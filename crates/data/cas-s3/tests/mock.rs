use std::{collections::HashMap, convert::Infallible, sync::Arc};

use axum::{
    Router,
    body::{Body, Bytes as AxumBytes},
    extract::{Path, State},
    http::{StatusCode, header},
    response::{IntoResponse, Response},
    routing::get,
};
use bytes::Bytes;
use covalence_data_cas::{AsyncCas, get_exact_fact};
use covalence_data_cas_s3::{S3Cas, S3CasConfig, S3CasError};
use covalence_lib_hash::O256;
use futures::stream;
use tokio::{net::TcpListener, sync::Mutex};

#[derive(Clone)]
enum Object {
    Bytes(AxumBytes),
    Declared { content_length: u64 },
    Streamed(Vec<AxumBytes>),
}

type Objects = Arc<Mutex<HashMap<String, Object>>>;

fn s3_error(status: StatusCode, code: &str) -> Response {
    (
        status,
        [(header::CONTENT_TYPE, "application/xml")],
        format!("<Error><Code>{code}</Code><Message>mock error</Message></Error>"),
    )
        .into_response()
}

async fn get_object(
    State(objects): State<Objects>,
    Path((bucket, key)): Path<(String, String)>,
) -> Response {
    if bucket == "missing-bucket" {
        return s3_error(StatusCode::NOT_FOUND, "NoSuchBucket");
    }
    let object = objects
        .lock()
        .await
        .get(&format!("{bucket}/{key}"))
        .cloned();
    match object {
        Some(Object::Bytes(bytes)) => bytes.into_response(),
        Some(Object::Declared { content_length }) => Response::builder()
            .header(header::CONTENT_LENGTH, content_length)
            .body(Body::from_stream(stream::pending::<
                Result<AxumBytes, Infallible>,
            >()))
            .expect("valid mock response"),
        Some(Object::Streamed(chunks)) => {
            let chunks = chunks.into_iter().map(Ok::<_, Infallible>);
            Response::new(Body::from_stream(stream::iter(chunks)))
        }
        None => s3_error(StatusCode::NOT_FOUND, "NoSuchKey"),
    }
}

async fn put_object(
    State(objects): State<Objects>,
    Path((bucket, key)): Path<(String, String)>,
    bytes: AxumBytes,
) {
    objects
        .lock()
        .await
        .insert(format!("{bucket}/{key}"), Object::Bytes(bytes));
}

async fn fixture_for_bucket(objects: Objects, bucket: &str, max_object_bytes: u64) -> S3Cas {
    let app = Router::new()
        .route("/{bucket}/{*key}", get(get_object).put(put_object))
        .with_state(objects);
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let address = listener.local_addr().unwrap();
    tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });
    S3Cas::new(
        S3CasConfig::new(bucket)
            .with_endpoint(format!("http://{address}"))
            .with_region("us-east-1")
            .with_path_style(true)
            .with_max_object_bytes(max_object_bytes)
            .with_credentials("test-access", "test-secret", None),
    )
    .await
}

async fn fixture(objects: Objects) -> S3Cas {
    fixture_for_bucket(objects, "test-bucket", 64 * 1024 * 1024).await
}

#[tokio::test]
async fn canonical_round_trip_and_missing_object() {
    let objects = Objects::default();
    let cas = fixture(Arc::clone(&objects)).await;
    let bytes = Bytes::from_static(b"portable S3 CAS");
    let address = O256::from_bytes(&bytes);

    assert_eq!(cas.key(address), format!("cas/{address}"));
    assert_eq!(cas.get_bytes(address).await.unwrap(), None);
    assert_eq!(cas.insert(bytes.clone()).await.unwrap(), address);
    assert_eq!(cas.get_bytes(address).await.unwrap(), Some(bytes.clone()));

    let fact = get_exact_fact(&cas, address).await.unwrap().unwrap();
    assert_eq!(fact.hash(), address);
    assert_eq!(fact.bytes(), &bytes);
    assert!(
        objects
            .lock()
            .await
            .contains_key(&format!("test-bucket/cas/{address}"))
    );

    let provider: &dyn AsyncCas = &cas;
    assert_eq!(
        provider.get_bytes(address).await.unwrap(),
        Some(bytes.clone())
    );
    let exact = get_exact_fact(provider, address).await.unwrap().unwrap();
    assert_eq!(exact.hash(), address);
    assert_eq!(exact.bytes(), &bytes);
}

#[tokio::test]
async fn checked_lookup_rejects_wrong_bytes() {
    let objects = Objects::default();
    let cas = fixture(Arc::clone(&objects)).await;
    let requested = O256::from_bytes(b"requested");
    objects.lock().await.insert(
        format!("test-bucket/cas/{requested}"),
        Object::Bytes(AxumBytes::from_static(b"different")),
    );

    assert_eq!(
        cas.get_bytes(requested).await.unwrap(),
        Some(Bytes::from_static(b"different"))
    );
    assert!(get_exact_fact(&cas, requested).await.is_err());
}

#[tokio::test]
async fn declared_oversize_is_rejected_before_reading() {
    let objects = Objects::default();
    let requested = O256::from_bytes(b"declared oversize");
    objects.lock().await.insert(
        format!("test-bucket/cas/{requested}"),
        Object::Declared { content_length: 5 },
    );
    let cas = fixture_for_bucket(objects, "test-bucket", 4).await;

    let result = cas.get_bytes(requested).await;
    assert!(
        matches!(
            result,
            Err(S3CasError::ObjectTooLarge {
                limit: 4,
                observed: 5
            })
        ),
        "unexpected result: {result:?}"
    );
}

#[tokio::test]
async fn streamed_oversize_is_rejected_without_a_declared_length() {
    let objects = Objects::default();
    let requested = O256::from_bytes(b"streamed oversize");
    objects.lock().await.insert(
        format!("test-bucket/cas/{requested}"),
        Object::Streamed(vec![
            AxumBytes::from_static(b"abc"),
            AxumBytes::from_static(b"def"),
        ]),
    );
    let cas = fixture_for_bucket(objects, "test-bucket", 4).await;

    assert!(matches!(
        cas.get_bytes(requested).await,
        Err(S3CasError::ObjectTooLarge {
            limit: 4,
            observed: 6
        })
    ));
}

#[tokio::test]
async fn no_such_bucket_is_not_object_absence() {
    let cas = fixture_for_bucket(Objects::default(), "missing-bucket", 1024).await;
    let requested = O256::from_bytes(b"requested");

    assert!(matches!(
        cas.get_bytes(requested).await,
        Err(S3CasError::Get { .. })
    ));
}

#[tokio::test]
async fn oversized_insert_is_rejected_without_uploading() {
    let objects = Objects::default();
    let cas = fixture_for_bucket(Arc::clone(&objects), "test-bucket", 4).await;

    assert!(matches!(
        cas.insert(Bytes::from_static(b"12345")).await,
        Err(S3CasError::ObjectTooLarge {
            limit: 4,
            observed: 5
        })
    ));
    assert!(objects.lock().await.is_empty());
}
