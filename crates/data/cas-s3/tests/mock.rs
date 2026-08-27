use std::{collections::HashMap, sync::Arc};

use axum::{
    Router,
    body::Bytes as AxumBytes,
    extract::{Path, State},
    http::StatusCode,
    routing::get,
};
use bytes::Bytes;
use covalence_data_cas_s3::{S3Cas, S3CasConfig};
use covalence_lib_hash::O256;
use tokio::{net::TcpListener, sync::Mutex};

type Objects = Arc<Mutex<HashMap<String, AxumBytes>>>;

async fn get_object(
    State(objects): State<Objects>,
    Path((bucket, key)): Path<(String, String)>,
) -> Result<AxumBytes, StatusCode> {
    objects
        .lock()
        .await
        .get(&format!("{bucket}/{key}"))
        .cloned()
        .ok_or(StatusCode::NOT_FOUND)
}

async fn put_object(
    State(objects): State<Objects>,
    Path((bucket, key)): Path<(String, String)>,
    bytes: AxumBytes,
) {
    objects
        .lock()
        .await
        .insert(format!("{bucket}/{key}"), bytes);
}

async fn fixture(objects: Objects) -> S3Cas {
    let app = Router::new()
        .route("/{bucket}/{*key}", get(get_object).put(put_object))
        .with_state(objects);
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let address = listener.local_addr().unwrap();
    tokio::spawn(async move { axum::serve(listener, app).await.unwrap() });
    S3Cas::new(
        S3CasConfig::new("test-bucket")
            .with_endpoint(format!("http://{address}"))
            .with_region("us-east-1")
            .with_path_style(true)
            .with_credentials("test-access", "test-secret", None),
    )
    .await
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

    let fact = cas.get_fact(address).await.unwrap().unwrap();
    assert_eq!(fact.hash(), address);
    assert_eq!(fact.bytes(), &bytes);
    assert!(
        objects
            .lock()
            .await
            .contains_key(&format!("test-bucket/cas/{address}"))
    );
}

#[tokio::test]
async fn checked_lookup_rejects_wrong_bytes() {
    let objects = Objects::default();
    let cas = fixture(Arc::clone(&objects)).await;
    let requested = O256::from_bytes(b"requested");
    objects.lock().await.insert(
        format!("test-bucket/cas/{requested}"),
        AxumBytes::from_static(b"different"),
    );

    assert_eq!(
        cas.get_bytes(requested).await.unwrap(),
        Some(Bytes::from_static(b"different"))
    );
    assert!(cas.get_fact(requested).await.is_err());
}
