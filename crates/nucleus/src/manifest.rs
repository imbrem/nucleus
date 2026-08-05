//! Canonical physical-schema identity shared by kernel protocols.

use covalence_lib_hash::{O256, o256_path};
use covalence_lib_sqlite::Error;
use covalence_neutron::Connection;

/// Hashes the `sqlite_schema` manifest of `main` in canonical order.
///
/// Rows are `(type, name, tbl_name, sql)` ordered bytewise; each field is
/// length-prefixed (little-endian `u64`), with a presence byte before the
/// nullable `sql` field.
///
/// # Errors
///
/// Returns an error if the manifest cannot be read.
pub fn schema_manifest_id(connection: &Connection) -> Result<O256, Error> {
    let rows = connection.query_all(
        "SELECT type, name, tbl_name, sql FROM main.sqlite_schema
         ORDER BY type COLLATE BINARY, name COLLATE BINARY,
                  tbl_name COLLATE BINARY, sql COLLATE BINARY",
        &[],
        |row| Ok((row.text(0)?, row.text(1)?, row.text(2)?, row.text_opt(3)?)),
    )?;
    let mut bytes = Vec::new();
    for row in rows {
        let (kind, name, table, sql) = row;
        for field in [&kind, &name, &table] {
            bytes.extend_from_slice(&(field.len() as u64).to_le_bytes());
            bytes.extend_from_slice(field.as_bytes());
        }
        match sql {
            None => bytes.push(0),
            Some(sql) => {
                bytes.push(1);
                bytes.extend_from_slice(&(sql.len() as u64).to_le_bytes());
                bytes.extend_from_slice(sql.as_bytes());
            }
        }
    }
    Ok(o256_path!(::nucleus.sqlite.schema_manifest.v0).tag(bytes))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn manifest_identity_distinguishes_schemas() {
        let empty = Connection::open_in_memory().expect("open empty");
        let extended = Connection::open_in_memory().expect("open extended");
        extended
            .execute_batch("CREATE TABLE extra (value INTEGER) STRICT")
            .expect("extend");
        let empty_id = schema_manifest_id(&empty).expect("empty id");
        let extended_id = schema_manifest_id(&extended).expect("extended id");
        assert_ne!(empty_id, extended_id);
        assert_eq!(empty_id, schema_manifest_id(&empty).expect("stable"));
    }
}
