use std::{error::Error as StdError, fmt};

use serde::Deserialize;

use crate::{
    HolSchema, HolSchemaDescriptor, HolSchemaDescriptorError, MetadataSchemaError, MetadataTable,
    MetadataType,
};

const MAX_JSON_BYTES: usize = 1 << 20;
const MAX_DECLARATIONS: usize = 128;
const MAX_IDENTIFIER_BYTES: usize = u16::MAX as usize;
const MAX_INDEX_COLUMNS: usize = 16;
const MAX_INDEX_REFERENCES: usize = 512;

/// Declarative checked metadata schema shared by terminal and browser REPLs.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HolMetadataSchemaSpec {
    /// Authoring format version. Version one is currently required.
    pub version: u8,
    /// Nullable metadata columns in declaration order.
    #[serde(default)]
    pub columns: Vec<HolMetadataColumnSpec>,
    /// Ordinary or unique indexes over declared metadata columns.
    #[serde(default)]
    pub indexes: Vec<HolMetadataIndexSpec>,
}

/// One user-selected metadata column.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HolMetadataColumnSpec {
    /// Core table extended by this physical annotation.
    pub table: HolMetadataTableSpec,
    /// Exact `SQLite` identifier.
    pub name: String,
    /// `SQLite` storage class.
    pub storage: HolMetadataStorageSpec,
}

/// One user-selected index over declared metadata columns.
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct HolMetadataIndexSpec {
    /// Core table containing all indexed columns.
    pub table: HolMetadataTableSpec,
    /// Exact global `SQLite` index identifier.
    pub name: String,
    /// Ordered metadata column identifiers.
    pub columns: Vec<String>,
    /// Whether `SQLite` enforces uniqueness.
    #[serde(default)]
    pub unique: bool,
}

/// Core HOL table which may carry physical metadata.
#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum HolMetadataTableSpec {
    Node,
    Context,
    ContextMember,
    Judgement,
    ContextImplication,
    ContextUnion,
    Namespace,
    NamespaceExport,
    Import,
    TrustedImport,
}

/// `SQLite` storage class available to nullable metadata columns.
#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum HolMetadataStorageSpec {
    Integer,
    Real,
    Text,
    Blob,
    Any,
}

impl HolMetadataSchemaSpec {
    /// Parses one strict JSON schema declaration.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed JSON, unknown fields, or unknown enum values.
    pub fn from_json(json: &str) -> Result<Self, HolSchemaSpecError> {
        if json.len() > MAX_JSON_BYTES {
            return Err(HolSchemaSpecError::LimitExceeded);
        }
        let spec: Self = serde_json::from_str(json).map_err(HolSchemaSpecError::Json)?;
        if spec.version != 1 {
            return Err(HolSchemaSpecError::UnsupportedVersion(spec.version));
        }
        Ok(spec)
    }

    /// Reconstructs the declaration through the ordinary checked Nucleus builders.
    ///
    /// # Errors
    ///
    /// Returns an error for duplicate/reserved columns, invalid indexes, or portable descriptor
    /// bounds.
    pub fn descriptor(&self) -> Result<HolSchemaDescriptor, HolSchemaSpecError> {
        if self.version != 1 {
            return Err(HolSchemaSpecError::UnsupportedVersion(self.version));
        }
        if self.columns.len() > MAX_DECLARATIONS || self.indexes.len() > MAX_DECLARATIONS {
            return Err(HolSchemaSpecError::LimitExceeded);
        }
        let mut references = 0_usize;
        for column in &self.columns {
            if column.name.len() > MAX_IDENTIFIER_BYTES {
                return Err(HolSchemaSpecError::LimitExceeded);
            }
        }
        for index in &self.indexes {
            references = references
                .checked_add(index.columns.len())
                .ok_or(HolSchemaSpecError::LimitExceeded)?;
            if index.name.len() > MAX_IDENTIFIER_BYTES
                || index.columns.len() > MAX_INDEX_COLUMNS
                || references > MAX_INDEX_REFERENCES
                || index
                    .columns
                    .iter()
                    .any(|column| column.len() > MAX_IDENTIFIER_BYTES)
            {
                return Err(HolSchemaSpecError::LimitExceeded);
            }
        }
        let mut schema = HolSchema::new();
        for column in &self.columns {
            schema.add_column_to(column.table.into(), &column.name, column.storage.into())?;
        }
        for index in &self.indexes {
            schema.add_index_on(
                index.table.into(),
                &index.name,
                index.columns.iter().map(String::as_str),
                index.unique,
            )?;
        }
        HolSchemaDescriptor::from_schema(&schema).map_err(Into::into)
    }
}

/// Compiles strict user-authored JSON into the canonical checked portable descriptor.
///
/// # Errors
///
/// Returns an error for oversized/malformed JSON, an unsupported version, invalid checked schema
/// declarations, or descriptor limits.
pub fn compile_hol_schema_json(json: &str) -> Result<HolSchemaDescriptor, HolSchemaSpecError> {
    HolMetadataSchemaSpec::from_json(json)?.descriptor()
}

impl From<HolMetadataTableSpec> for MetadataTable {
    fn from(table: HolMetadataTableSpec) -> Self {
        match table {
            HolMetadataTableSpec::Node => Self::Node,
            HolMetadataTableSpec::Context => Self::Context,
            HolMetadataTableSpec::ContextMember => Self::ContextMember,
            HolMetadataTableSpec::Judgement => Self::Judgement,
            HolMetadataTableSpec::ContextImplication => Self::ContextImplication,
            HolMetadataTableSpec::ContextUnion => Self::ContextUnion,
            HolMetadataTableSpec::Namespace => Self::Namespace,
            HolMetadataTableSpec::NamespaceExport => Self::NamespaceExport,
            HolMetadataTableSpec::Import => Self::Import,
            HolMetadataTableSpec::TrustedImport => Self::TrustedImport,
        }
    }
}

impl From<HolMetadataStorageSpec> for MetadataType {
    fn from(storage: HolMetadataStorageSpec) -> Self {
        match storage {
            HolMetadataStorageSpec::Integer => Self::Integer,
            HolMetadataStorageSpec::Real => Self::Real,
            HolMetadataStorageSpec::Text => Self::Text,
            HolMetadataStorageSpec::Blob => Self::Blob,
            HolMetadataStorageSpec::Any => Self::Any,
        }
    }
}

/// Failure to parse or check a declarative REPL metadata schema.
#[derive(Debug)]
#[non_exhaustive]
pub enum HolSchemaSpecError {
    LimitExceeded,
    UnsupportedVersion(u8),
    Json(serde_json::Error),
    Schema(MetadataSchemaError),
    Descriptor(HolSchemaDescriptorError),
}

impl fmt::Display for HolSchemaSpecError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::LimitExceeded => {
                formatter.write_str("HOL metadata schema JSON exceeds a fixed authoring limit")
            }
            Self::UnsupportedVersion(version) => {
                write!(
                    formatter,
                    "unsupported HOL metadata schema JSON version {version}"
                )
            }
            Self::Json(error) => write!(formatter, "invalid HOL metadata schema JSON: {error}"),
            Self::Schema(error) => error.fmt(formatter),
            Self::Descriptor(error) => error.fmt(formatter),
        }
    }
}

impl StdError for HolSchemaSpecError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::LimitExceeded | Self::UnsupportedVersion(_) => None,
            Self::Json(error) => Some(error),
            Self::Schema(error) => Some(error),
            Self::Descriptor(error) => Some(error),
        }
    }
}

impl From<MetadataSchemaError> for HolSchemaSpecError {
    fn from(error: MetadataSchemaError) -> Self {
        Self::Schema(error)
    }
}

impl From<HolSchemaDescriptorError> for HolSchemaSpecError {
    fn from(error: HolSchemaDescriptorError) -> Self {
        Self::Descriptor(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn strict_json_builds_checked_columns_and_indexes() {
        let spec = HolMetadataSchemaSpec::from_json(
            r#"{
                "version": 1,
                "columns": [
                    {"table":"node", "name":"source label", "storage":"text"},
                    {"table":"judgement", "name":"cost", "storage":"integer"}
                ],
                "indexes": [
                    {"table":"node", "name":"by source", "columns":["source label"]},
                    {"table":"judgement", "name":"by_cost", "columns":["cost"], "unique":true}
                ]
            }"#,
        )
        .unwrap();
        let descriptor = spec.descriptor().unwrap();
        assert_eq!(
            descriptor.schema().metadata_type("source label"),
            Some(MetadataType::Text)
        );
        assert_eq!(
            descriptor
                .schema()
                .metadata_type_on(MetadataTable::Judgement, "cost"),
            Some(MetadataType::Integer)
        );
    }

    #[test]
    fn json_rejects_unknown_fields_and_checked_schema_errors() {
        assert!(HolMetadataSchemaSpec::from_json(r#"{"version":1,"columnz":[]}"#).is_err());
        let unknown = HolMetadataSchemaSpec::from_json(
            r#"{"version":1,"indexes":[{"table":"node","name":"bad","columns":["missing"]}]}"#,
        )
        .unwrap();
        assert!(matches!(
            unknown.descriptor(),
            Err(HolSchemaSpecError::Schema(
                MetadataSchemaError::UnknownColumn(_)
            ))
        ));
        assert!(matches!(
            HolMetadataSchemaSpec::from_json(r#"{"version":2}"#),
            Err(HolSchemaSpecError::UnsupportedVersion(2))
        ));
        assert!(matches!(
            HolMetadataSchemaSpec {
                version: 2,
                columns: Vec::new(),
                indexes: Vec::new(),
            }
            .descriptor(),
            Err(HolSchemaSpecError::UnsupportedVersion(2))
        ));
        assert!(matches!(
            HolMetadataSchemaSpec::from_json(&" ".repeat(MAX_JSON_BYTES + 1)),
            Err(HolSchemaSpecError::LimitExceeded)
        ));

        let too_many = HolMetadataSchemaSpec {
            version: 1,
            columns: (0..=MAX_DECLARATIONS)
                .map(|index| HolMetadataColumnSpec {
                    table: HolMetadataTableSpec::Node,
                    name: format!("column_{index}"),
                    storage: HolMetadataStorageSpec::Integer,
                })
                .collect(),
            indexes: Vec::new(),
        };
        assert!(matches!(
            too_many.descriptor(),
            Err(HolSchemaSpecError::LimitExceeded)
        ));
    }
}
