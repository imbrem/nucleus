//! Opt-in conformance test for real S3-compatible providers.
//!
//! Run one provider at a time, for example:
//! `NUCLEUS_S3_PROVIDER=AWS cargo test -p covalence-data-cas-s3 --test provider -- --ignored`.
//! The selected prefix supplies `BUCKET`, and optionally `ENDPOINT`, `REGION`,
//! `ACCESS_KEY_ID`, and `SECRET_ACCESS_KEY` environment variables. If explicit
//! credentials are omitted, the standard AWS provider chain is used.

use std::env;

use bytes::Bytes;
use covalence_data_cas_s3::{S3Cas, S3CasConfig};

fn optional(name: &str) -> Option<String> {
    env::var(name).ok().filter(|value| !value.is_empty())
}

fn explicit_credentials(
    access: Option<String>,
    secret: Option<String>,
) -> Option<(String, String)> {
    match (access, secret) {
        (Some(access), Some(secret)) => Some((access, secret)),
        (None, None) => None,
        _ => panic!("selected provider must set both ACCESS_KEY_ID and SECRET_ACCESS_KEY"),
    }
}

#[test]
fn partial_explicit_credentials_are_rejected() {
    assert!(
        std::panic::catch_unwind(|| explicit_credentials(Some("access".to_owned()), None)).is_err()
    );
    assert!(
        std::panic::catch_unwind(|| explicit_credentials(None, Some("secret".to_owned()))).is_err()
    );
}

#[tokio::test]
#[ignore = "requires an explicitly selected real S3-compatible provider"]
async fn real_provider_round_trip() {
    let provider = env::var("NUCLEUS_S3_PROVIDER")
        .expect("set NUCLEUS_S3_PROVIDER to an environment-variable prefix such as AWS, R2, or B2");
    assert!(
        provider
            .bytes()
            .all(|byte| byte.is_ascii_uppercase() || byte == b'_'),
        "provider prefix must contain only ASCII uppercase letters and underscores"
    );
    let variable = |suffix: &str| format!("NUCLEUS_S3_{provider}_{suffix}");
    let bucket = env::var(variable("BUCKET")).expect("selected provider requires BUCKET");
    let mut config = S3CasConfig::new(bucket);
    if let Some(endpoint) = optional(&variable("ENDPOINT")) {
        config = config.with_endpoint(endpoint);
    }
    if let Some(region) = optional(&variable("REGION")) {
        config = config.with_region(region);
    }
    if optional(&variable("PATH_STYLE")).as_deref() == Some("1") {
        config = config.with_path_style(true);
    }
    if let Some((access, secret)) = explicit_credentials(
        optional(&variable("ACCESS_KEY_ID")),
        optional(&variable("SECRET_ACCESS_KEY")),
    ) {
        config = config.with_credentials(access, secret, optional(&variable("SESSION_TOKEN")));
    }

    let cas = S3Cas::new(config).await;
    let bytes = Bytes::from_static(b"nucleus S3 CAS provider conformance v1");
    let address = cas.insert(bytes.clone()).await.unwrap();
    assert_eq!(cas.get_bytes(address).await.unwrap(), Some(bytes.clone()));
    let fact = cas.get_fact(address).await.unwrap().unwrap();
    assert_eq!(fact.hash(), address);
    assert_eq!(fact.bytes(), &bytes);
}
