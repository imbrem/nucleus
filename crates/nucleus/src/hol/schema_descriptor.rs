use std::{collections::HashSet, error::Error as StdError, fmt};

use covalence_lib_hash::O256;

use super::{HolImageValidationError, HolSchema, MetadataSchemaError, MetadataTable, MetadataType};

const MAGIC: &[u8; 8] = b"COVHSD01";
const MAX_DESCRIPTOR_BYTES: usize = 1 << 20;
const MAX_ENTRIES: usize = 128;
const MAX_INDEX_COLUMNS: usize = 16;
const MAX_IDENTIFIER_BYTES: usize = u16::MAX as usize;
const MAX_INDEX_REFERENCES: usize = 512;
const CORE_INDEX_NAMES: &[&str] = &[
    "hol_proof_event_judgement",
    "hol_context_implication_event_edge",
    "hol_context_exact_union_event_key",
    "hol_namespace_named_child",
    "hol_namespace_export_name",
    "hol_kstar_unique",
    "hol_karr_unique",
    "hol_tbool_unique",
    "hol_tbase_unique",
    "hol_tarr_unique",
    "hol_mbool_unique",
    "hol_mfv_unique",
    "hol_mconst_unique",
    "hol_mbv_unique",
    "hol_mapp_unique",
    "hol_mlam_unique",
    "hol_meq_unique",
];

/// Canonical, bounded evidence for one portable checked HOL metadata schema.
#[derive(Clone, Debug)]
pub struct HolSchemaDescriptor {
    schema: HolSchema,
    bytes: Vec<u8>,
    schema_id: O256,
}

impl HolSchemaDescriptor {
    /// Canonicalizes a locally checked schema into the bounded portable format.
    ///
    /// # Errors
    ///
    /// Returns an error when the schema exceeds the format's fixed byte or declaration bounds.
    pub fn from_schema(schema: &HolSchema) -> Result<Self, HolSchemaDescriptorError> {
        let bytes = schema.encode_descriptor()?;
        Self::decode(&bytes)
    }

    /// Decodes canonical untrusted descriptor bytes using only checked schema builders.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed, non-canonical, oversized, or invalid declarations.
    pub fn decode(bytes: &[u8]) -> Result<Self, HolSchemaDescriptorError> {
        let schema = HolSchema::decode_descriptor(bytes)?;
        let schema_id = super::validate::expected_composite_schema_id(&schema)?;
        Ok(Self {
            schema,
            bytes: bytes.to_vec(),
            schema_id,
        })
    }

    /// Returns the canonical portable bytes.
    #[must_use]
    pub fn encode(&self) -> &[u8] {
        &self.bytes
    }

    /// Returns the checked canonical schema used for exact manifest validation.
    #[must_use]
    pub const fn schema(&self) -> &HolSchema {
        &self.schema
    }

    /// Returns the independently derived composite semantic and physical schema identity.
    #[must_use]
    pub const fn schema_id(&self) -> O256 {
        self.schema_id
    }

    /// Consumes the evidence and returns its checked canonical schema.
    #[must_use]
    pub fn into_schema(self) -> HolSchema {
        self.schema
    }
}

impl HolSchema {
    /// Encodes this checked metadata schema in the canonical portable version-one format.
    ///
    /// The descriptor contains declarations only, never SQL. It preserves declaration order
    /// within each table because that order contributes to the installed physical schema, while
    /// canonicalizing cross-table column interleaving and global index declaration order.
    ///
    /// # Errors
    ///
    /// Returns an error if this in-memory schema exceeds the portable format's fixed bounds.
    fn encode_descriptor(&self) -> Result<Vec<u8>, HolSchemaDescriptorError> {
        check_count(self.columns.len())?;
        check_count(self.indexes.len())?;
        let mut bytes = Vec::from(MAGIC.as_slice());
        put_u32(&mut bytes, self.columns.len())?;
        for tag in 0..=9 {
            for column in self
                .columns
                .iter()
                .filter(|column| table_tag(column.table) == tag)
            {
                bytes.push(tag);
                bytes.push(type_tag(column.storage));
                put_identifier(&mut bytes, &column.name)?;
            }
        }
        put_u32(&mut bytes, self.indexes.len())?;
        let mut indexes = self.indexes.iter().collect::<Vec<_>>();
        indexes.sort_by(|left, right| left.name.as_bytes().cmp(right.name.as_bytes()));
        let references = indexes.iter().try_fold(0_usize, |total, index| {
            total
                .checked_add(index.columns.len())
                .ok_or(HolSchemaDescriptorError::LimitExceeded)
        })?;
        if references > MAX_INDEX_REFERENCES {
            return Err(HolSchemaDescriptorError::LimitExceeded);
        }
        for index in indexes {
            if index.columns.len() > MAX_INDEX_COLUMNS {
                return Err(HolSchemaDescriptorError::LimitExceeded);
            }
            bytes.push(table_tag(index.table));
            bytes.push(u8::from(index.unique));
            if CORE_INDEX_NAMES
                .iter()
                .any(|core| core.eq_ignore_ascii_case(&index.name))
            {
                return Err(HolSchemaDescriptorError::ReservedIndex(index.name.clone()));
            }
            let mut seen = HashSet::new();
            if index
                .columns
                .iter()
                .any(|column| !seen.insert(column.to_ascii_lowercase()))
            {
                return Err(HolSchemaDescriptorError::RepeatedIndexColumn(
                    index.name.clone(),
                ));
            }
            put_identifier(&mut bytes, &index.name)?;
            put_u16(&mut bytes, index.columns.len())?;
            for column in &index.columns {
                put_identifier(&mut bytes, column)?;
            }
        }
        if bytes.len() > MAX_DESCRIPTOR_BYTES {
            return Err(HolSchemaDescriptorError::LimitExceeded);
        }
        Ok(bytes)
    }

    /// Reconstructs a checked metadata schema from its canonical portable descriptor.
    ///
    /// Decoding calls only the ordinary checked column/index builders. It cannot inject SQL.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed, non-canonical, oversized, unknown-version, or semantically
    /// invalid declarations.
    fn decode_descriptor(bytes: &[u8]) -> Result<Self, HolSchemaDescriptorError> {
        if bytes.len() > MAX_DESCRIPTOR_BYTES {
            return Err(HolSchemaDescriptorError::LimitExceeded);
        }
        let mut input = Input::new(bytes);
        if input.take(MAGIC.len())? != MAGIC {
            return Err(HolSchemaDescriptorError::WrongVersion);
        }
        let column_count = input.count()?;
        let mut schema = Self::new();
        for _ in 0..column_count {
            let table = decode_table(input.byte()?)?;
            let storage = decode_type(input.byte()?)?;
            let name = input.identifier()?;
            schema.add_column_to(table, name, storage)?;
        }
        let index_count = input.count()?;
        let mut references = 0_usize;
        for _ in 0..index_count {
            let table = decode_table(input.byte()?)?;
            let unique = match input.byte()? {
                0 => false,
                1 => true,
                _ => return Err(HolSchemaDescriptorError::Malformed),
            };
            let name = input.identifier()?;
            let count = usize::from(input.u16()?);
            if count > MAX_INDEX_COLUMNS {
                return Err(HolSchemaDescriptorError::LimitExceeded);
            }
            references = references
                .checked_add(count)
                .ok_or(HolSchemaDescriptorError::LimitExceeded)?;
            if references > MAX_INDEX_REFERENCES {
                return Err(HolSchemaDescriptorError::LimitExceeded);
            }
            let columns = (0..count)
                .map(|_| input.identifier())
                .collect::<Result<Vec<_>, _>>()?;
            schema.add_index_on(table, name, columns, unique)?;
        }
        if !input.is_empty() {
            return Err(HolSchemaDescriptorError::TrailingBytes);
        }
        if schema.encode_descriptor()?.as_slice() != bytes {
            return Err(HolSchemaDescriptorError::NonCanonical);
        }
        Ok(schema)
    }
}

fn table_tag(table: MetadataTable) -> u8 {
    match table {
        MetadataTable::Node => 0,
        MetadataTable::Context => 1,
        MetadataTable::ContextMember => 2,
        MetadataTable::Judgement => 3,
        MetadataTable::ContextImplication => 4,
        MetadataTable::ContextUnion => 5,
        MetadataTable::Namespace => 6,
        MetadataTable::NamespaceExport => 7,
        MetadataTable::Import => 8,
        MetadataTable::TrustedImport => 9,
    }
}

fn decode_table(tag: u8) -> Result<MetadataTable, HolSchemaDescriptorError> {
    match tag {
        0 => Ok(MetadataTable::Node),
        1 => Ok(MetadataTable::Context),
        2 => Ok(MetadataTable::ContextMember),
        3 => Ok(MetadataTable::Judgement),
        4 => Ok(MetadataTable::ContextImplication),
        5 => Ok(MetadataTable::ContextUnion),
        6 => Ok(MetadataTable::Namespace),
        7 => Ok(MetadataTable::NamespaceExport),
        8 => Ok(MetadataTable::Import),
        9 => Ok(MetadataTable::TrustedImport),
        _ => Err(HolSchemaDescriptorError::UnknownTable(tag)),
    }
}

fn type_tag(storage: MetadataType) -> u8 {
    match storage {
        MetadataType::Integer => 0,
        MetadataType::Real => 1,
        MetadataType::Text => 2,
        MetadataType::Blob => 3,
        MetadataType::Any => 4,
    }
}

fn decode_type(tag: u8) -> Result<MetadataType, HolSchemaDescriptorError> {
    match tag {
        0 => Ok(MetadataType::Integer),
        1 => Ok(MetadataType::Real),
        2 => Ok(MetadataType::Text),
        3 => Ok(MetadataType::Blob),
        4 => Ok(MetadataType::Any),
        _ => Err(HolSchemaDescriptorError::UnknownType(tag)),
    }
}

fn put_identifier(bytes: &mut Vec<u8>, value: &str) -> Result<(), HolSchemaDescriptorError> {
    if value.len() > MAX_IDENTIFIER_BYTES {
        return Err(HolSchemaDescriptorError::LimitExceeded);
    }
    put_u16(bytes, value.len())?;
    bytes.extend_from_slice(value.as_bytes());
    Ok(())
}

fn put_u16(bytes: &mut Vec<u8>, value: usize) -> Result<(), HolSchemaDescriptorError> {
    let value = u16::try_from(value).map_err(|_| HolSchemaDescriptorError::LimitExceeded)?;
    bytes.extend_from_slice(&value.to_le_bytes());
    Ok(())
}

fn put_u32(bytes: &mut Vec<u8>, value: usize) -> Result<(), HolSchemaDescriptorError> {
    check_count(value)?;
    let value = u32::try_from(value).map_err(|_| HolSchemaDescriptorError::LimitExceeded)?;
    bytes.extend_from_slice(&value.to_le_bytes());
    Ok(())
}

fn check_count(value: usize) -> Result<(), HolSchemaDescriptorError> {
    if value > MAX_ENTRIES {
        Err(HolSchemaDescriptorError::LimitExceeded)
    } else {
        Ok(())
    }
}

struct Input<'a> {
    remaining: &'a [u8],
}

impl<'a> Input<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { remaining: bytes }
    }

    fn take(&mut self, count: usize) -> Result<&'a [u8], HolSchemaDescriptorError> {
        let (value, remaining) = self
            .remaining
            .split_at_checked(count)
            .ok_or(HolSchemaDescriptorError::Truncated)?;
        self.remaining = remaining;
        Ok(value)
    }

    fn byte(&mut self) -> Result<u8, HolSchemaDescriptorError> {
        Ok(self.take(1)?[0])
    }

    fn u16(&mut self) -> Result<u16, HolSchemaDescriptorError> {
        let bytes = self.take(2)?;
        Ok(u16::from_le_bytes([bytes[0], bytes[1]]))
    }

    fn u32(&mut self) -> Result<u32, HolSchemaDescriptorError> {
        let bytes = self.take(4)?;
        Ok(u32::from_le_bytes([bytes[0], bytes[1], bytes[2], bytes[3]]))
    }

    fn count(&mut self) -> Result<usize, HolSchemaDescriptorError> {
        let count =
            usize::try_from(self.u32()?).map_err(|_| HolSchemaDescriptorError::LimitExceeded)?;
        check_count(count)?;
        Ok(count)
    }

    fn identifier(&mut self) -> Result<String, HolSchemaDescriptorError> {
        let length = usize::from(self.u16()?);
        if length > MAX_IDENTIFIER_BYTES {
            return Err(HolSchemaDescriptorError::LimitExceeded);
        }
        let bytes = self.take(length)?;
        std::str::from_utf8(bytes)
            .map(str::to_owned)
            .map_err(|_| HolSchemaDescriptorError::InvalidUtf8)
    }

    const fn is_empty(&self) -> bool {
        self.remaining.is_empty()
    }
}

/// Failure to encode or decode a portable checked HOL metadata schema descriptor.
#[derive(Debug)]
#[non_exhaustive]
pub enum HolSchemaDescriptorError {
    WrongVersion,
    Truncated,
    TrailingBytes,
    InvalidUtf8,
    UnknownTable(u8),
    UnknownType(u8),
    Malformed,
    NonCanonical,
    ReservedIndex(String),
    RepeatedIndexColumn(String),
    LimitExceeded,
    Schema(MetadataSchemaError),
    PhysicalSchema(HolImageValidationError),
}

impl fmt::Display for HolSchemaDescriptorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::WrongVersion => f.write_str("unknown HOL schema descriptor version"),
            Self::Truncated => f.write_str("truncated HOL schema descriptor"),
            Self::TrailingBytes => f.write_str("trailing HOL schema descriptor bytes"),
            Self::InvalidUtf8 => f.write_str("HOL schema descriptor identifier is not UTF-8"),
            Self::UnknownTable(tag) => write!(f, "unknown HOL metadata table tag {tag}"),
            Self::UnknownType(tag) => write!(f, "unknown HOL metadata type tag {tag}"),
            Self::Malformed => f.write_str("malformed HOL schema descriptor"),
            Self::NonCanonical => f.write_str("non-canonical HOL schema descriptor"),
            Self::ReservedIndex(name) => write!(f, "reserved HOL schema index {name:?}"),
            Self::RepeatedIndexColumn(name) => {
                write!(f, "portable HOL schema index {name:?} repeats a column")
            }
            Self::LimitExceeded => f.write_str("HOL schema descriptor exceeds a fixed limit"),
            Self::Schema(error) => error.fmt(f),
            Self::PhysicalSchema(error) => error.fmt(f),
        }
    }
}

impl StdError for HolSchemaDescriptorError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Schema(error) => Some(error),
            Self::PhysicalSchema(error) => Some(error),
            _ => None,
        }
    }
}

impl From<MetadataSchemaError> for HolSchemaDescriptorError {
    fn from(error: MetadataSchemaError) -> Self {
        Self::Schema(error)
    }
}

impl From<HolImageValidationError> for HolSchemaDescriptorError {
    fn from(error: HolImageValidationError) -> Self {
        Self::PhysicalSchema(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        AllowAll, AuthenticatedHolImageValidationError, AuthenticatedValidatedHolImage, Connection,
        Hol, Kernel, SignedSnapshotEnvelope,
    };

    #[test]
    fn empty_descriptor_has_a_fixed_wire_vector() {
        let descriptor = HolSchemaDescriptor::from_schema(&HolSchema::new()).unwrap();
        assert_eq!(descriptor.encode(), b"COVHSD01\0\0\0\0\0\0\0\0");
    }

    #[test]
    fn mixed_descriptor_has_fixed_wire_and_composite_vectors() {
        let mut schema = HolSchema::new();
        for (name, storage) in [
            ("alpha", MetadataType::Integer),
            ("beta", MetadataType::Real),
            ("gamma", MetadataType::Text),
        ] {
            schema
                .add_column_to(MetadataTable::Node, name, storage)
                .unwrap();
        }
        schema
            .add_column_to(MetadataTable::Judgement, "delta", MetadataType::Blob)
            .unwrap();
        schema
            .add_column_to(MetadataTable::Judgement, "epsilon", MetadataType::Any)
            .unwrap();
        schema
            .add_index_on(MetadataTable::Node, "node_combo", ["alpha", "beta"], false)
            .unwrap();
        schema
            .add_index_on(
                MetadataTable::Judgement,
                "judgement_unique",
                ["delta", "epsilon"],
                true,
            )
            .unwrap();
        let descriptor = HolSchemaDescriptor::from_schema(&schema).unwrap();

        let mut expected = Vec::from(MAGIC.as_slice());
        expected.extend_from_slice(&5_u32.to_le_bytes());
        for (table, storage, name) in [
            (0, 0, "alpha"),
            (0, 1, "beta"),
            (0, 2, "gamma"),
            (3, 3, "delta"),
            (3, 4, "epsilon"),
        ] {
            expected.extend_from_slice(&[table, storage]);
            expected.extend_from_slice(&u16::try_from(name.len()).unwrap().to_le_bytes());
            expected.extend_from_slice(name.as_bytes());
        }
        expected.extend_from_slice(&2_u32.to_le_bytes());
        for (table, unique, name, columns) in [
            (3, 1, "judgement_unique", &["delta", "epsilon"][..]),
            (0, 0, "node_combo", &["alpha", "beta"][..]),
        ] {
            expected.extend_from_slice(&[table, unique]);
            expected.extend_from_slice(&u16::try_from(name.len()).unwrap().to_le_bytes());
            expected.extend_from_slice(name.as_bytes());
            expected.extend_from_slice(&u16::try_from(columns.len()).unwrap().to_le_bytes());
            for column in columns {
                expected.extend_from_slice(&u16::try_from(column.len()).unwrap().to_le_bytes());
                expected.extend_from_slice(column.as_bytes());
            }
        }
        assert_eq!(descriptor.encode(), expected);
        assert_eq!(
            descriptor.schema_id().to_string(),
            "94ea2b678c70191ba52fe7b587bcf41e8e716b324578fa27234be58c68e27c77"
        );
    }

    #[test]
    fn canonical_descriptor_round_trips_checked_columns_and_indexes() {
        let mut schema = HolSchema::new();
        schema
            .add_column_to(MetadataTable::Node, "origin", MetadataType::Text)
            .unwrap();
        schema
            .add_column_to(MetadataTable::Judgement, "cost", MetadataType::Integer)
            .unwrap();
        schema
            .add_index_on(MetadataTable::Judgement, "by_cost", ["cost"], false)
            .unwrap();
        let descriptor = HolSchemaDescriptor::from_schema(&schema).unwrap();
        let decoded = HolSchemaDescriptor::decode(descriptor.encode()).unwrap();
        assert_eq!(decoded.encode(), descriptor.encode());
        assert_eq!(
            decoded
                .schema()
                .metadata_type_on(MetadataTable::Node, "origin"),
            Some(MetadataType::Text)
        );
        assert_eq!(
            decoded
                .schema()
                .metadata_type_on(MetadataTable::Judgement, "cost"),
            Some(MetadataType::Integer)
        );
    }

    #[test]
    fn exact_utf8_identifiers_round_trip_without_becoming_sql() {
        let mut schema = HolSchema::new();
        schema
            .add_column("Source Label λ", MetadataType::Text)
            .unwrap();
        schema
            .add_column("x); DROP TABLE hol_node; --", MetadataType::Text)
            .unwrap();
        schema
            .add_index("By Source Label λ", ["Source Label λ"], false)
            .unwrap();
        let descriptor = HolSchemaDescriptor::from_schema(&schema)
            .unwrap()
            .encode()
            .to_vec();
        let decoded = HolSchemaDescriptor::decode(&descriptor).unwrap();
        assert_eq!(
            decoded.schema().metadata_type("Source Label λ"),
            Some(MetadataType::Text)
        );
        assert_eq!(
            decoded
                .schema()
                .metadata_type("x); DROP TABLE hol_node; --"),
            Some(MetadataType::Text)
        );
    }

    #[test]
    fn decoder_rejects_unknown_tags_truncation_and_trailing_bytes() {
        let mut schema = HolSchema::new();
        schema.add_column("safe", MetadataType::Text).unwrap();
        let descriptor = HolSchemaDescriptor::from_schema(&schema)
            .unwrap()
            .encode()
            .to_vec();

        let mut unknown = descriptor.clone();
        unknown[MAGIC.len() + 4] = u8::MAX;
        assert!(matches!(
            HolSchemaDescriptor::decode(&unknown),
            Err(HolSchemaDescriptorError::UnknownTable(_))
        ));
        let mut unknown_type = descriptor.clone();
        unknown_type[MAGIC.len() + 5] = u8::MAX;
        assert!(matches!(
            HolSchemaDescriptor::decode(&unknown_type),
            Err(HolSchemaDescriptorError::UnknownType(_))
        ));
        for prefix in 0..descriptor.len() {
            assert!(HolSchemaDescriptor::decode(&descriptor[..prefix]).is_err());
        }
        let mut invalid_unique = Vec::from(MAGIC.as_slice());
        invalid_unique.extend_from_slice(&0_u32.to_le_bytes());
        invalid_unique.extend_from_slice(&1_u32.to_le_bytes());
        invalid_unique.extend_from_slice(&[0, 2]);
        assert!(matches!(
            HolSchemaDescriptor::decode(&invalid_unique),
            Err(HolSchemaDescriptorError::Malformed)
        ));
        let mut trailing = descriptor;
        trailing.push(0);
        assert!(matches!(
            HolSchemaDescriptor::decode(&trailing),
            Err(HolSchemaDescriptorError::TrailingBytes)
        ));
    }

    #[test]
    fn portable_indexes_reject_core_names_and_repeated_columns() {
        let mut reserved = HolSchema::new();
        reserved.add_column("origin", MetadataType::Text).unwrap();
        reserved
            .add_index("HOL_MBOOL_UNIQUE", ["origin"], false)
            .unwrap();
        assert!(matches!(
            HolSchemaDescriptor::from_schema(&reserved),
            Err(HolSchemaDescriptorError::ReservedIndex(name)) if name == "HOL_MBOOL_UNIQUE"
        ));

        let mut repeated = HolSchema::new();
        repeated.add_column("origin", MetadataType::Text).unwrap();
        repeated
            .add_index("by_origin_twice", ["origin", "ORIGIN"], false)
            .unwrap();
        assert!(matches!(
            HolSchemaDescriptor::from_schema(&repeated),
            Err(HolSchemaDescriptorError::RepeatedIndexColumn(name))
                if name == "by_origin_twice"
        ));

        let mut raw = Vec::from(MAGIC.as_slice());
        raw.extend_from_slice(&1_u32.to_le_bytes());
        raw.extend_from_slice(&[0, 2]);
        raw.extend_from_slice(&6_u16.to_le_bytes());
        raw.extend_from_slice(b"origin");
        raw.extend_from_slice(&1_u32.to_le_bytes());
        raw.extend_from_slice(&[0, 0]);
        raw.extend_from_slice(&4_u16.to_le_bytes());
        raw.extend_from_slice(b"dupe");
        raw.extend_from_slice(&2_u16.to_le_bytes());
        for column in [b"origin".as_slice(), b"ORIGIN".as_slice()] {
            raw.extend_from_slice(&6_u16.to_le_bytes());
            raw.extend_from_slice(column);
        }
        assert!(matches!(
            HolSchemaDescriptor::decode(&raw),
            Err(HolSchemaDescriptorError::RepeatedIndexColumn(name)) if name == "dupe"
        ));
    }

    #[test]
    fn descriptor_reconstructs_the_exact_authenticated_custom_schema() {
        let mut schema = HolSchema::new();
        schema
            .add_column_to(MetadataTable::Node, "origin", MetadataType::Text)
            .unwrap();
        schema
            .add_index_on(MetadataTable::Node, "by_origin", ["origin"], false)
            .unwrap();
        let descriptor = HolSchemaDescriptor::from_schema(&schema).unwrap();
        let kernel = Kernel::ephemeral();
        let mut connection = Connection::<Hol<AllowAll>>::open_hol_in_memory_with_schema(
            AllowAll,
            descriptor.schema().clone(),
        )
        .unwrap();
        connection.insert_bool_term(true).unwrap();
        let signed = kernel.export_hol(&mut connection).unwrap();
        let attestation = signed.attestation();
        let authenticate = || {
            SignedSnapshotEnvelope::new(
                signed.image().bytes(),
                attestation.schema(),
                attestation.image(),
                attestation.signer(),
                *attestation.public_key(),
                attestation.signature(),
            )
            .authenticate()
            .unwrap()
        };
        let validated =
            AuthenticatedValidatedHolImage::validate_with_descriptor(authenticate(), &descriptor)
                .unwrap();
        assert_eq!(validated.image().schema(), attestation.schema());

        let mut wrong_schema = HolSchema::new();
        wrong_schema
            .add_column_to(MetadataTable::Node, "origin", MetadataType::Text)
            .unwrap();
        wrong_schema
            .add_index_on(MetadataTable::Node, "by_origin", ["origin"], true)
            .unwrap();
        let wrong = HolSchemaDescriptor::from_schema(&wrong_schema).unwrap();
        assert!(matches!(
            AuthenticatedValidatedHolImage::validate_with_descriptor(authenticate(), &wrong),
            Err(AuthenticatedHolImageValidationError::SchemaMismatch { .. })
        ));
    }

    #[test]
    fn canonicalization_removes_only_physically_irrelevant_declaration_order() {
        let mut first = HolSchema::new();
        first
            .add_column_to(MetadataTable::Judgement, "cost", MetadataType::Integer)
            .unwrap();
        first
            .add_column_to(MetadataTable::Node, "origin", MetadataType::Text)
            .unwrap();
        first
            .add_index_on(MetadataTable::Judgement, "z_cost", ["cost"], false)
            .unwrap();
        first
            .add_index_on(MetadataTable::Node, "a_origin", ["origin"], false)
            .unwrap();

        let mut second = HolSchema::new();
        second
            .add_column_to(MetadataTable::Node, "origin", MetadataType::Text)
            .unwrap();
        second
            .add_column_to(MetadataTable::Judgement, "cost", MetadataType::Integer)
            .unwrap();
        second
            .add_index_on(MetadataTable::Node, "a_origin", ["origin"], false)
            .unwrap();
        second
            .add_index_on(MetadataTable::Judgement, "z_cost", ["cost"], false)
            .unwrap();

        let first = HolSchemaDescriptor::from_schema(&first).unwrap();
        let second = HolSchemaDescriptor::from_schema(&second).unwrap();
        assert_eq!(first.encode(), second.encode());
        assert_eq!(first.schema_id(), second.schema_id());

        let mut reordered = HolSchema::new();
        reordered.add_column("second", MetadataType::Text).unwrap();
        reordered.add_column("first", MetadataType::Text).unwrap();
        let mut opposite = HolSchema::new();
        opposite.add_column("first", MetadataType::Text).unwrap();
        opposite.add_column("second", MetadataType::Text).unwrap();
        let reordered = HolSchemaDescriptor::from_schema(&reordered).unwrap();
        let opposite = HolSchemaDescriptor::from_schema(&opposite).unwrap();
        assert_ne!(reordered.encode(), opposite.encode());
        assert_ne!(reordered.schema_id(), opposite.schema_id());
    }

    #[test]
    fn bounded_decoder_does_not_panic_on_arbitrary_bytes() {
        let mut state = 1_u64;
        for length in 0..512 {
            let mut bytes = vec![0; length];
            for byte in &mut bytes {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1);
                *byte = state.to_le_bytes()[4];
            }
            let _ = HolSchemaDescriptor::decode(&bytes);
        }
    }
}
