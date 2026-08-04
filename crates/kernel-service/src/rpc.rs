//! Canonical payloads for signed kernel-service operations.
//!
//! These payloads are independent of any HTTP, WebSocket, Worker, or in-process transport. Their
//! exact bytes are named with O256 and related by [`crate::operation_schema`].

use covalence_lib_hash::O256;

use crate::{
    ImageBytes, KernelIdentity, MAX_IMAGE_BYTES, MAX_LISTED_IMAGES, MAX_SQL_BYTES,
    MAX_SQL_OUTCOME_BYTES, Operation, OperationContract, ServiceError, SqlConnectionId, SqlOutcome,
    SqlOutcomeKind, SqlStatement, SqlValue,
};

const REQUEST_MAGIC: [u8; 8] = *b"COVKSRQI";
const RESPONSE_MAGIC: [u8; 8] = *b"COVKSRSP";
const VERSION: u8 = 0;
const RESERVED: [u8; 3] = [0; 3];
const MAX_DECODE_ALLOCATION_BYTES: usize = 64 << 20;

/// Canonical request supported by the initial signed SQL endpoint.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ServiceRequest {
    /// Read the observed kernel identity.
    Identity,
    /// Test operational image residency.
    HasImage {
        /// Operational image address.
        image: O256,
    },
    /// List bounded resident image addresses.
    ListImages,
    /// Admit one bounded complete image.
    PutImage {
        /// Exact uninterpreted image bytes.
        bytes: ImageBytes,
    },
    /// Open one in-memory `SQLite` connection.
    Open,
    /// Run one statement on a channel-owned connection.
    Run {
        /// Opaque channel-owned handle.
        connection: SqlConnectionId,
        /// Bounded UTF-8 statement.
        statement: SqlStatement,
    },
    /// Attach a resident image to a channel-owned connection.
    Attach {
        /// Opaque channel-owned handle.
        connection: SqlConnectionId,
        /// Operational image address.
        image: O256,
        /// Exact `SQLite` schema identifier.
        schema: String,
    },
    /// Close one channel-owned connection.
    Close {
        /// Opaque channel-owned handle.
        connection: SqlConnectionId,
    },
    /// Serialize a channel-owned connection's writable `main` database.
    Serialize {
        /// Opaque channel-owned handle.
        connection: SqlConnectionId,
    },
}

impl ServiceRequest {
    /// Operation whose semantic schema governs this request.
    #[must_use]
    pub const fn operation(&self) -> Operation {
        match self {
            Self::Identity => Operation::Identity,
            Self::HasImage { .. } => Operation::HasImage,
            Self::ListImages => Operation::ListImages,
            Self::PutImage { .. } => Operation::PutImage,
            Self::Open => Operation::OpenSql,
            Self::Run { .. } => Operation::RunSql,
            Self::Attach { .. } => Operation::AttachImage,
            Self::Close { .. } => Operation::CloseSql,
            Self::Serialize { .. } => Operation::SerializeSqlMain,
        }
    }

    /// Encodes the unique v0 request bytes.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        header(&mut bytes, REQUEST_MAGIC, self.operation());
        match self {
            Self::Identity | Self::ListImages | Self::Open => {}
            Self::HasImage { image } => bytes.extend_from_slice(image.as_ref()),
            Self::PutImage { bytes: image } => put_bytes(&mut bytes, image.as_slice()),
            Self::Run {
                connection,
                statement,
            } => {
                bytes.extend_from_slice(&connection.get().to_be_bytes());
                put_bytes(&mut bytes, statement.as_str().as_bytes());
            }
            Self::Close { connection } | Self::Serialize { connection } => {
                bytes.extend_from_slice(&connection.get().to_be_bytes());
            }
            Self::Attach {
                connection,
                image,
                schema,
            } => {
                bytes.extend_from_slice(&connection.get().to_be_bytes());
                bytes.extend_from_slice(image.as_ref());
                put_bytes(&mut bytes, schema.as_bytes());
            }
        }
        bytes
    }

    /// Decodes one exact canonical request.
    ///
    /// # Errors
    ///
    /// Rejects malformed, trailing, non-UTF-8, or over-limit request bytes.
    pub fn decode(bytes: &[u8]) -> Result<Self, RpcCodecError> {
        let mut cursor = Cursor::new(bytes);
        let operation = read_header(&mut cursor, REQUEST_MAGIC)?;
        let request = match operation {
            Operation::Identity => Self::Identity,
            Operation::HasImage => Self::HasImage {
                image: cursor.o256()?,
            },
            Operation::ListImages => Self::ListImages,
            Operation::PutImage => {
                let value = cursor.bytes()?;
                if value.len() > MAX_IMAGE_BYTES {
                    return Err(RpcCodecError::ResourceLimit);
                }
                Self::PutImage {
                    bytes: ImageBytes::new(value.to_vec())
                        .map_err(|_| RpcCodecError::ResourceLimit)?,
                }
            }
            Operation::OpenSql => Self::Open,
            Operation::RunSql => {
                let connection = SqlConnectionId::from_u64(cursor.u64()?);
                let statement = cursor.bytes()?;
                if statement.len() > MAX_SQL_BYTES {
                    return Err(RpcCodecError::ResourceLimit);
                }
                let statement = std::str::from_utf8(statement)
                    .map_err(|_| RpcCodecError::InvalidUtf8)?
                    .to_owned();
                Self::Run {
                    connection,
                    statement: SqlStatement::new(statement)
                        .map_err(|_| RpcCodecError::ResourceLimit)?,
                }
            }
            Operation::CloseSql => Self::Close {
                connection: SqlConnectionId::from_u64(cursor.u64()?),
            },
            Operation::AttachImage => {
                let connection = SqlConnectionId::from_u64(cursor.u64()?);
                let image = cursor.o256()?;
                let schema = cursor.bytes()?;
                if schema.len() > MAX_SQL_BYTES {
                    return Err(RpcCodecError::ResourceLimit);
                }
                Self::Attach {
                    connection,
                    image,
                    schema: std::str::from_utf8(schema)
                        .map_err(|_| RpcCodecError::InvalidUtf8)?
                        .to_owned(),
                }
            }
            Operation::SerializeSqlMain => Self::Serialize {
                connection: SqlConnectionId::from_u64(cursor.u64()?),
            },
        };
        cursor.finish()?;
        Ok(request)
    }

    /// O256 identity of the exact canonical request bytes.
    #[must_use]
    pub fn value_id(&self) -> O256 {
        value_id(self.operation(), b"input\0", &self.encode())
    }
}

/// Canonical signed-service result, including portable operation failures.
#[derive(Clone, Debug, PartialEq)]
pub enum ServiceResponse {
    /// Result of reading observed identity.
    Identity(Result<KernelIdentity, ServiceError>),
    /// Result of testing image residency.
    HasImage(Result<bool, ServiceError>),
    /// Result of listing image addresses.
    ListImages(Result<Vec<O256>, ServiceError>),
    /// Result of admitting an image.
    PutImage(Result<O256, ServiceError>),
    /// Result of opening a connection.
    Open(Result<SqlConnectionId, ServiceError>),
    /// Result of running a statement.
    Run(Result<SqlOutcome, ServiceError>),
    /// Result of attaching a resident image.
    Attach(Result<(), ServiceError>),
    /// Result of closing a connection.
    Close(Result<(), ServiceError>),
    /// Result of serializing writable `main`.
    Serialize(Result<ImageBytes, ServiceError>),
}

impl ServiceResponse {
    /// Operation whose semantic schema governs this response.
    #[must_use]
    pub const fn operation(&self) -> Operation {
        match self {
            Self::Identity(_) => Operation::Identity,
            Self::HasImage(_) => Operation::HasImage,
            Self::ListImages(_) => Operation::ListImages,
            Self::PutImage(_) => Operation::PutImage,
            Self::Open(_) => Operation::OpenSql,
            Self::Run(_) => Operation::RunSql,
            Self::Attach(_) => Operation::AttachImage,
            Self::Close(_) => Operation::CloseSql,
            Self::Serialize(_) => Operation::SerializeSqlMain,
        }
    }

    /// Encodes the unique v0 response bytes.
    #[must_use]
    pub fn encode(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        header(&mut bytes, RESPONSE_MAGIC, self.operation());
        match self {
            Self::Identity(result) => encode_result(&mut bytes, result, encode_identity),
            Self::HasImage(result) => {
                encode_result(&mut bytes, result, |bytes, value| {
                    bytes.push(u8::from(*value));
                });
            }
            Self::ListImages(result) => encode_result(&mut bytes, result, |bytes, images| {
                put_len(bytes, images.len());
                for image in images {
                    bytes.extend_from_slice(image.as_ref());
                }
            }),
            Self::PutImage(result) => encode_result(&mut bytes, result, |bytes, image| {
                bytes.extend_from_slice(image.as_ref());
            }),
            Self::Open(result) => encode_result(&mut bytes, result, |bytes, connection| {
                bytes.extend_from_slice(&connection.get().to_be_bytes());
            }),
            Self::Run(result) => encode_result(&mut bytes, result, encode_outcome),
            Self::Attach(result) => encode_result(&mut bytes, result, |_, ()| {}),
            Self::Close(result) => encode_result(&mut bytes, result, |_, ()| {}),
            Self::Serialize(result) => encode_result(&mut bytes, result, |bytes, image| {
                put_bytes(bytes, image.as_slice());
            }),
        }
        bytes
    }

    /// Decodes one exact canonical response.
    ///
    /// # Errors
    ///
    /// Rejects malformed, trailing, non-rectangular, or over-limit response bytes.
    pub fn decode(bytes: &[u8]) -> Result<Self, RpcCodecError> {
        let mut cursor = Cursor::new(bytes);
        let operation = read_header(&mut cursor, RESPONSE_MAGIC)?;
        let status = cursor.u8()?;
        if status == 1 {
            let error = decode_service_error(cursor.u8()?)?;
            cursor.finish()?;
            return Ok(match operation {
                Operation::Identity => Self::Identity(Err(error)),
                Operation::HasImage => Self::HasImage(Err(error)),
                Operation::ListImages => Self::ListImages(Err(error)),
                Operation::PutImage => Self::PutImage(Err(error)),
                Operation::OpenSql => Self::Open(Err(error)),
                Operation::RunSql => Self::Run(Err(error)),
                Operation::AttachImage => Self::Attach(Err(error)),
                Operation::CloseSql => Self::Close(Err(error)),
                Operation::SerializeSqlMain => Self::Serialize(Err(error)),
            });
        }
        if status != 0 {
            return Err(RpcCodecError::InvalidTag);
        }
        let response = match operation {
            Operation::Identity => Self::Identity(Ok(decode_identity(&mut cursor)?)),
            Operation::HasImage => Self::HasImage(Ok(match cursor.u8()? {
                0 => false,
                1 => true,
                _ => return Err(RpcCodecError::InvalidTag),
            })),
            Operation::ListImages => {
                let count = cursor.u32()? as usize;
                if count > MAX_LISTED_IMAGES {
                    return Err(RpcCodecError::ResourceLimit);
                }
                let mut images = Vec::new();
                images
                    .try_reserve_exact(count)
                    .map_err(|_| RpcCodecError::ResourceLimit)?;
                for _ in 0..count {
                    images.push(cursor.o256()?);
                }
                Self::ListImages(Ok(images))
            }
            Operation::PutImage => Self::PutImage(Ok(cursor.o256()?)),
            Operation::OpenSql => Self::Open(Ok(SqlConnectionId::from_u64(cursor.u64()?))),
            Operation::RunSql => Self::Run(Ok(decode_outcome(&mut cursor)?)),
            Operation::AttachImage => Self::Attach(Ok(())),
            Operation::CloseSql => Self::Close(Ok(())),
            Operation::SerializeSqlMain => {
                let value = cursor.bytes()?;
                if value.len() > MAX_IMAGE_BYTES {
                    return Err(RpcCodecError::ResourceLimit);
                }
                Self::Serialize(Ok(
                    ImageBytes::new(value.to_vec()).map_err(|_| RpcCodecError::ResourceLimit)?
                ))
            }
        };
        cursor.finish()?;
        Ok(response)
    }

    /// O256 identity of the exact canonical response bytes.
    #[must_use]
    pub fn value_id(&self) -> O256 {
        value_id(self.operation(), b"output\0", &self.encode())
    }
}

fn value_id(operation: Operation, direction: &[u8], payload: &[u8]) -> O256 {
    let mut value = Vec::with_capacity(direction.len() + 4 + payload.len());
    value.extend_from_slice(direction);
    value.extend_from_slice(
        &u32::try_from(payload.len())
            .expect("bounded canonical service payload")
            .to_be_bytes(),
    );
    value.extend_from_slice(payload);
    crate::operation_schema(operation).tag(value)
}

fn header(bytes: &mut Vec<u8>, magic: [u8; 8], operation: Operation) {
    bytes.extend_from_slice(&magic);
    bytes.push(VERSION);
    bytes.extend_from_slice(&RESERVED);
    bytes.push(operation.tag());
}

fn read_header(cursor: &mut Cursor<'_>, magic: [u8; 8]) -> Result<Operation, RpcCodecError> {
    if cursor.take(8)? != magic {
        return Err(RpcCodecError::InvalidMagic);
    }
    if cursor.u8()? != VERSION {
        return Err(RpcCodecError::UnsupportedVersion);
    }
    if cursor.take(3)? != RESERVED {
        return Err(RpcCodecError::NonzeroReserved);
    }
    operation_from_tag(cursor.u8()?)
}

fn operation_from_tag(tag: u8) -> Result<Operation, RpcCodecError> {
    Operation::ALL
        .into_iter()
        .find(|operation| operation.tag() == tag)
        .ok_or(RpcCodecError::InvalidTag)
}

fn put_bytes(output: &mut Vec<u8>, value: &[u8]) {
    let len = u32::try_from(value.len()).expect("bounded service value length");
    output.extend_from_slice(&len.to_be_bytes());
    output.extend_from_slice(value);
}

fn encode_result<T>(
    bytes: &mut Vec<u8>,
    result: &Result<T, ServiceError>,
    encode: impl FnOnce(&mut Vec<u8>, &T),
) {
    match result {
        Ok(value) => {
            bytes.push(0);
            encode(bytes, value);
        }
        Err(error) => {
            bytes.push(1);
            bytes.push(service_error_tag(*error));
        }
    }
}

fn service_error_tag(error: ServiceError) -> u8 {
    match error {
        ServiceError::InvalidRequest => 0,
        ServiceError::NotFound => 1,
        ServiceError::ResourceLimit => 2,
        ServiceError::Protocol => 3,
        ServiceError::Internal => 4,
    }
}

fn decode_service_error(tag: u8) -> Result<ServiceError, RpcCodecError> {
    match tag {
        0 => Ok(ServiceError::InvalidRequest),
        1 => Ok(ServiceError::NotFound),
        2 => Ok(ServiceError::ResourceLimit),
        3 => Ok(ServiceError::Protocol),
        4 => Ok(ServiceError::Internal),
        _ => Err(RpcCodecError::InvalidTag),
    }
}

fn encode_identity(bytes: &mut Vec<u8>, identity: &KernelIdentity) {
    bytes.extend_from_slice(&identity.public_key);
    put_len(bytes, identity.operations.len());
    for operation in &identity.operations {
        bytes.push(operation.operation.tag());
        bytes.extend_from_slice(operation.contract.as_ref());
    }
}

fn decode_identity(cursor: &mut Cursor<'_>) -> Result<KernelIdentity, RpcCodecError> {
    let public_key = cursor.array()?;
    let count = cursor.u32()? as usize;
    if count > Operation::ALL.len() {
        return Err(RpcCodecError::ResourceLimit);
    }
    let mut operations = Vec::new();
    operations
        .try_reserve_exact(count)
        .map_err(|_| RpcCodecError::ResourceLimit)?;
    let mut previous = None;
    for _ in 0..count {
        let operation = operation_from_tag(cursor.u8()?)?;
        if previous.is_some_and(|tag| tag >= operation.tag()) {
            return Err(RpcCodecError::NoncanonicalOrder);
        }
        previous = Some(operation.tag());
        operations.push(OperationContract {
            operation,
            contract: cursor.o256()?,
        });
    }
    Ok(KernelIdentity {
        public_key,
        operations,
    })
}

fn encode_outcome(bytes: &mut Vec<u8>, outcome: &SqlOutcome) {
    match outcome.kind() {
        SqlOutcomeKind::Changed(count) => {
            bytes.push(0);
            bytes.extend_from_slice(&count.to_be_bytes());
        }
        SqlOutcomeKind::Rows { columns, rows } => {
            bytes.push(1);
            put_len(bytes, columns.len());
            for column in columns {
                put_bytes(bytes, column.as_bytes());
            }
            put_len(bytes, rows.len());
            for row in rows {
                for value in row {
                    encode_value(bytes, value);
                }
            }
        }
    }
}

fn decode_outcome(cursor: &mut Cursor<'_>) -> Result<SqlOutcome, RpcCodecError> {
    match cursor.u8()? {
        0 => Ok(SqlOutcome::changed(cursor.u64()?)),
        1 => {
            let mut budget = LogicalBudget::new();
            budget.charge(1 + size_of::<u64>() * 2)?;
            let column_count = cursor.u32()? as usize;
            let column_prefix_bytes = column_count
                .checked_mul(size_of::<u32>())
                .ok_or(RpcCodecError::ResourceLimit)?;
            let minimum_prefix_bytes = column_prefix_bytes
                .checked_add(size_of::<u32>())
                .ok_or(RpcCodecError::ResourceLimit)?;
            if cursor.remaining_len() < minimum_prefix_bytes {
                return Err(RpcCodecError::Truncated);
            }
            budget.charge(
                column_count
                    .checked_mul(size_of::<u64>())
                    .ok_or(RpcCodecError::ResourceLimit)?,
            )?;
            if column_count
                .checked_mul(size_of::<String>())
                .is_none_or(|bytes| bytes > MAX_DECODE_ALLOCATION_BYTES)
            {
                return Err(RpcCodecError::ResourceLimit);
            }
            let mut columns = Vec::new();
            columns
                .try_reserve_exact(column_count)
                .map_err(|_| RpcCodecError::ResourceLimit)?;
            for _ in 0..column_count {
                let value = cursor.bytes()?;
                budget.charge(value.len())?;
                columns.push(
                    std::str::from_utf8(value)
                        .map_err(|_| RpcCodecError::InvalidUtf8)?
                        .to_owned(),
                );
            }
            let row_count = cursor.u32()? as usize;
            let cells = row_count.checked_mul(column_count);
            let container_bytes = row_count.checked_mul(size_of::<Vec<SqlValue>>());
            let value_bytes = cells.and_then(|cells| cells.checked_mul(size_of::<SqlValue>()));
            if cells.is_none_or(|cells| cursor.remaining_len() < cells) {
                return Err(RpcCodecError::Truncated);
            }
            if container_bytes
                .and_then(|rows| value_bytes.and_then(|values| rows.checked_add(values)))
                .is_none_or(|bytes| bytes > MAX_DECODE_ALLOCATION_BYTES)
            {
                return Err(RpcCodecError::ResourceLimit);
            }
            budget.charge(
                row_count
                    .checked_mul(size_of::<u64>())
                    .ok_or(RpcCodecError::ResourceLimit)?,
            )?;
            let mut rows = Vec::new();
            rows.try_reserve_exact(row_count)
                .map_err(|_| RpcCodecError::ResourceLimit)?;
            for _ in 0..row_count {
                let mut row = Vec::new();
                row.try_reserve_exact(column_count)
                    .map_err(|_| RpcCodecError::ResourceLimit)?;
                for _ in 0..column_count {
                    row.push(decode_value(cursor, &mut budget)?);
                }
                rows.push(row);
            }
            SqlOutcome::rows(columns, rows).map_err(|_| RpcCodecError::ResourceLimit)
        }
        _ => Err(RpcCodecError::InvalidTag),
    }
}

fn put_len(bytes: &mut Vec<u8>, len: usize) {
    bytes.extend_from_slice(
        &u32::try_from(len)
            .expect("bounded service sequence length")
            .to_be_bytes(),
    );
}

fn encode_value(bytes: &mut Vec<u8>, value: &SqlValue) {
    match value {
        SqlValue::Null => bytes.push(0),
        SqlValue::Integer(value) => {
            bytes.push(1);
            bytes.extend_from_slice(&value.to_be_bytes());
        }
        SqlValue::Real(value) => {
            bytes.push(2);
            bytes.extend_from_slice(&value.to_bits().to_be_bytes());
        }
        SqlValue::Text(value) => {
            bytes.push(3);
            put_bytes(bytes, value.as_bytes());
        }
        SqlValue::Blob(value) => {
            bytes.push(4);
            put_bytes(bytes, value);
        }
    }
}

fn decode_value(
    cursor: &mut Cursor<'_>,
    budget: &mut LogicalBudget,
) -> Result<SqlValue, RpcCodecError> {
    budget.charge(1)?;
    match cursor.u8()? {
        0 => Ok(SqlValue::Null),
        1 => {
            budget.charge(size_of::<u64>())?;
            Ok(SqlValue::Integer(i64::from_be_bytes(cursor.array()?)))
        }
        2 => {
            budget.charge(size_of::<u64>())?;
            Ok(SqlValue::Real(f64::from_bits(cursor.u64()?)))
        }
        3 => {
            let value = cursor.bytes()?;
            budget.charge(size_of::<u64>())?;
            budget.charge(value.len())?;
            Ok(SqlValue::Text(
                std::str::from_utf8(value)
                    .map_err(|_| RpcCodecError::InvalidUtf8)?
                    .to_owned(),
            ))
        }
        4 => {
            let value = cursor.bytes()?;
            budget.charge(size_of::<u64>())?;
            budget.charge(value.len())?;
            Ok(SqlValue::Blob(value.to_vec()))
        }
        _ => Err(RpcCodecError::InvalidTag),
    }
}

struct LogicalBudget {
    remaining: usize,
}

impl LogicalBudget {
    const fn new() -> Self {
        Self {
            remaining: MAX_SQL_OUTCOME_BYTES,
        }
    }

    fn charge(&mut self, bytes: usize) -> Result<(), RpcCodecError> {
        self.remaining = self
            .remaining
            .checked_sub(bytes)
            .ok_or(RpcCodecError::ResourceLimit)?;
        Ok(())
    }
}

struct Cursor<'a> {
    remaining: &'a [u8],
}

impl<'a> Cursor<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { remaining: bytes }
    }

    fn take(&mut self, len: usize) -> Result<&'a [u8], RpcCodecError> {
        let Some((value, remaining)) = self.remaining.split_at_checked(len) else {
            return Err(RpcCodecError::Truncated);
        };
        self.remaining = remaining;
        Ok(value)
    }

    fn array<const N: usize>(&mut self) -> Result<[u8; N], RpcCodecError> {
        self.take(N)?
            .try_into()
            .map_err(|_| RpcCodecError::Truncated)
    }

    fn u8(&mut self) -> Result<u8, RpcCodecError> {
        Ok(self.take(1)?[0])
    }

    fn u32(&mut self) -> Result<u32, RpcCodecError> {
        Ok(u32::from_be_bytes(self.array()?))
    }

    fn u64(&mut self) -> Result<u64, RpcCodecError> {
        Ok(u64::from_be_bytes(self.array()?))
    }

    fn o256(&mut self) -> Result<O256, RpcCodecError> {
        Ok(O256::from_array(self.array()?))
    }

    fn bytes(&mut self) -> Result<&'a [u8], RpcCodecError> {
        let len = self.u32()? as usize;
        self.take(len)
    }

    fn finish(self) -> Result<(), RpcCodecError> {
        if self.remaining.is_empty() {
            Ok(())
        } else {
            Err(RpcCodecError::TrailingBytes)
        }
    }

    const fn remaining_len(&self) -> usize {
        self.remaining.len()
    }
}

/// Rejected canonical SQL service payload.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum RpcCodecError {
    /// Input ended before a complete field.
    Truncated,
    /// Message-kind magic did not match.
    InvalidMagic,
    /// Message version is unsupported.
    UnsupportedVersion,
    /// Reserved bytes were not canonical zeroes.
    NonzeroReserved,
    /// Operation or value tag is unknown.
    InvalidTag,
    /// UTF-8 field is malformed.
    InvalidUtf8,
    /// Decoded value exceeds a service resource limit.
    ResourceLimit,
    /// Exact message contained unconsumed bytes.
    TrailingBytes,
    /// A set-like sequence was not in its unique canonical order.
    NoncanonicalOrder,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn requests_round_trip_and_ids_name_exact_bytes() {
        let requests = vec![
            ServiceRequest::Identity,
            ServiceRequest::HasImage {
                image: O256::from_bytes(b"image"),
            },
            ServiceRequest::ListImages,
            ServiceRequest::PutImage {
                bytes: ImageBytes::new(b"sqlite".to_vec()).unwrap(),
            },
            ServiceRequest::Open,
            ServiceRequest::Run {
                connection: SqlConnectionId::from_u64(7),
                statement: SqlStatement::new("SELECT 42".to_owned()).unwrap(),
            },
            ServiceRequest::Attach {
                connection: SqlConnectionId::from_u64(8),
                image: O256::from_bytes(b"image"),
                schema: "snapshot".to_owned(),
            },
            ServiceRequest::Close {
                connection: SqlConnectionId::from_u64(9),
            },
            ServiceRequest::Serialize {
                connection: SqlConnectionId::from_u64(10),
            },
        ];
        for request in requests {
            let bytes = request.encode();
            assert_eq!(ServiceRequest::decode(&bytes).unwrap(), request);
            assert_ne!(request.value_id(), O256::from_bytes(bytes));
        }
    }

    #[test]
    fn successes_and_service_errors_round_trip() {
        let rows =
            SqlOutcome::rows(vec!["answer".to_owned()], vec![vec![SqlValue::Integer(42)]]).unwrap();
        let responses = vec![
            ServiceResponse::Identity(Ok(KernelIdentity::complete([7; 32]))),
            ServiceResponse::HasImage(Ok(true)),
            ServiceResponse::ListImages(Ok(vec![O256::from_bytes(b"image")])),
            ServiceResponse::PutImage(Ok(O256::from_bytes(b"image"))),
            ServiceResponse::Open(Ok(SqlConnectionId::from_u64(1))),
            ServiceResponse::Run(Ok(rows)),
            ServiceResponse::Attach(Ok(())),
            ServiceResponse::Close(Ok(())),
            ServiceResponse::Serialize(Ok(ImageBytes::new(b"sqlite".to_vec()).unwrap())),
            ServiceResponse::Run(Err(ServiceError::NotFound)),
        ];
        for response in responses {
            let bytes = response.encode();
            assert_eq!(ServiceResponse::decode(&bytes).unwrap(), response);
            assert_ne!(response.value_id(), O256::from_bytes(bytes));
        }
    }

    #[test]
    fn operation_tag_and_trailing_bytes_are_rejected() {
        let mut unsupported = ServiceRequest::Open.encode();
        unsupported[12] = u8::MAX;
        assert_eq!(
            ServiceRequest::decode(&unsupported),
            Err(RpcCodecError::InvalidTag)
        );
        let mut trailing = ServiceRequest::Open.encode();
        trailing.push(0);
        assert_eq!(
            ServiceRequest::decode(&trailing),
            Err(RpcCodecError::TrailingBytes)
        );
    }

    #[test]
    fn decoder_rejects_expensive_shapes_before_cloning_or_reserving() {
        let mut oversized_statement = Vec::new();
        header(&mut oversized_statement, REQUEST_MAGIC, Operation::RunSql);
        oversized_statement.extend_from_slice(&1_u64.to_be_bytes());
        put_bytes(&mut oversized_statement, &vec![b'x'; MAX_SQL_BYTES + 1]);
        assert_eq!(
            ServiceRequest::decode(&oversized_statement),
            Err(RpcCodecError::ResourceLimit)
        );

        let mut too_many_empty_rows = Vec::new();
        header(&mut too_many_empty_rows, RESPONSE_MAGIC, Operation::RunSql);
        too_many_empty_rows.extend_from_slice(&[0, 1]);
        too_many_empty_rows.extend_from_slice(&0_u32.to_be_bytes());
        too_many_empty_rows.extend_from_slice(
            &u32::try_from(MAX_SQL_OUTCOME_BYTES / size_of::<u64>() + 1)
                .unwrap()
                .to_be_bytes(),
        );
        assert_eq!(
            ServiceResponse::decode(&too_many_empty_rows),
            Err(RpcCodecError::ResourceLimit)
        );

        let mut impossible_columns = Vec::new();
        header(&mut impossible_columns, RESPONSE_MAGIC, Operation::RunSql);
        impossible_columns.extend_from_slice(&[0, 1]);
        impossible_columns.extend_from_slice(&0x3fff_ffff_u32.to_be_bytes());
        assert!(matches!(
            ServiceResponse::decode(&impossible_columns),
            Err(RpcCodecError::Truncated | RpcCodecError::ResourceLimit)
        ));
    }

    #[test]
    fn signed_wire_bound_includes_maximum_image_rpc_framing() {
        let put = ServiceRequest::PutImage {
            bytes: ImageBytes::new(vec![0; MAX_IMAGE_BYTES]).unwrap(),
        }
        .encode();
        assert_eq!(put.len(), MAX_IMAGE_BYTES + 17);
        assert!(put.len() <= crate::wire::MAX_WIRE_PAYLOAD_BYTES);
        drop(put);

        let serialized =
            ServiceResponse::Serialize(Ok(ImageBytes::new(vec![0; MAX_IMAGE_BYTES]).unwrap()))
                .encode();
        assert_eq!(serialized.len(), MAX_IMAGE_BYTES + 18);
        assert!(serialized.len() <= crate::wire::MAX_WIRE_PAYLOAD_BYTES);
    }
}
