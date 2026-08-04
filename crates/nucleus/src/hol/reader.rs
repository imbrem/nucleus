use std::{error::Error as StdError, fmt, marker::PhantomData};

use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension as _;

use super::{
    Hol, ImportError, ImportId, MatchedTrustedHolImage, NamespaceId, NamespaceSource, Operation,
    Policy, TrustedImportId,
};
use crate::Connection;

const IMPORTED_SCHEMA: &str = "imported";

macro_rules! imported_id {
    ($name:ident, $doc:literal) => {
        #[doc = $doc]
        #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
        pub struct $name<'reader>(i64, PhantomData<fn(&'reader ()) -> &'reader ()>);

        impl $name<'_> {
            /// Returns the source database's inert integer coordinate.
            #[must_use]
            pub const fn get(self) -> i64 {
                self.0
            }
        }
    };
}

imported_id!(ImportedKindId, "A kind ID scoped to one imported reader.");
imported_id!(ImportedTypeId, "A type ID scoped to one imported reader.");
imported_id!(ImportedTermId, "A term ID scoped to one imported reader.");
imported_id!(
    ImportedContextId,
    "A context ID scoped to one imported reader."
);

/// One structural namespace export from the immutable imported image.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImportedExport<'reader> {
    /// Imported kind coordinate.
    Kind(ImportedKindId<'reader>),
    /// Imported type coordinate.
    Type(ImportedTypeId<'reader>),
    /// Imported term coordinate.
    Term(ImportedTermId<'reader>),
    /// Imported context coordinate.
    Context(ImportedContextId<'reader>),
}

/// Read-only structural view of an imported term.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ImportedTermView<'reader> {
    /// Boolean literal.
    Bool(bool),
    /// Typed free symbol.
    Free {
        symbol: u64,
        ty: ImportedTypeId<'reader>,
    },
    /// Closed opaque constant declaration.
    Constant {
        symbol: i64,
        ty: ImportedTypeId<'reader>,
    },
    /// Typed de Bruijn occurrence.
    Bound {
        index: u64,
        ty: ImportedTypeId<'reader>,
    },
    /// Typed application.
    Application {
        function: ImportedTermId<'reader>,
        argument: ImportedTermId<'reader>,
        ty: ImportedTypeId<'reader>,
    },
    /// Typed lambda.
    Lambda {
        parameter_type: ImportedTypeId<'reader>,
        body: ImportedTermId<'reader>,
        ty: ImportedTypeId<'reader>,
    },
    /// Same-typed equality.
    Equality {
        left: ImportedTermId<'reader>,
        right: ImportedTermId<'reader>,
        ty: ImportedTypeId<'reader>,
    },
    /// Hilbert choice applied to a Boolean-valued predicate.
    Epsilon {
        predicate: ImportedTermId<'reader>,
        ty: ImportedTypeId<'reader>,
    },
}

/// Evidence that one exact judgement row occurs in a verified imported image.
///
/// This capability is scoped to the imported reader that produced it. It is not a
/// local [`super::Theorem`] and cannot be used by the local proof rules.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ImportedTheorem<'reader> {
    context: ImportedContextId<'reader>,
    conclusion: ImportedTermId<'reader>,
}

impl<'reader> ImportedTheorem<'reader> {
    /// Returns the imported context coordinate of the persisted judgement.
    #[must_use]
    pub const fn context(self) -> ImportedContextId<'reader> {
        self.context
    }

    /// Returns the imported Boolean conclusion coordinate of the persisted judgement.
    #[must_use]
    pub const fn conclusion(self) -> ImportedTermId<'reader> {
        self.conclusion
    }
}

/// Scoped immutable structural reader for one exact trusted imported image.
///
/// It exposes no raw SQL, local judgement authority, local-ID conversion, or proof operation.
/// Persisted imported judgements can only be observed as reader-scoped [`ImportedTheorem`]
/// evidence.
pub struct ImportedHolReader<'reader, 'connection, P> {
    owner: &'connection mut Connection<Hol<P>>,
    sqlite: covalence_neutron::Connection,
    mounted: covalence_neutron::ImmutableImage,
    trusted_import: TrustedImportId,
    import: ImportId,
    namespace: NamespaceId,
    source_namespace: i64,
    _brand: PhantomData<fn(&'reader ()) -> &'reader ()>,
}

impl<'connection, P: Policy> MatchedTrustedHolImage<'connection, P> {
    /// Opens a scoped reader through one previously registered immutable image handle.
    ///
    /// The handle must serve bytes exactly equal to the independently authenticated and validated
    /// image. Matching trust, policy, and namespace provenance remain connection-local and are
    /// rechecked on every call. The actual post-attach VFS pointer is checked before `run` and
    /// before every structural read.
    ///
    /// # Errors
    ///
    /// Returns an error for policy denial, a local/wrong-import namespace, a byte mismatch,
    /// connection/attach failure, or an unexpected actual VFS pointer.
    pub fn with_mounted_reader<R>(
        self,
        namespace: NamespaceId,
        mounted: &covalence_neutron::ImmutableImage,
        run: impl for<'reader> FnOnce(ImportedHolReader<'reader, 'connection, P>) -> R,
    ) -> Result<R, ImportedReaderError> {
        let (owner, trusted_import, import, evidence) = self.into_parts();
        if !owner
            .parts_mut()
            .1
            .policy
            .allows(Operation::OpenTrustedImportReader)
        {
            return Err(ImportedReaderError::Denied(
                Operation::OpenTrustedImportReader,
            ));
        }
        let source_namespace = match owner.namespace_source(namespace)? {
            NamespaceSource::Local => {
                return Err(ImportError::LocalNamespace(namespace).into());
            }
            NamespaceSource::Imported {
                import: actual,
                source_namespace,
            } if actual == import => source_namespace,
            NamespaceSource::Imported { import: actual, .. } => {
                return Err(ImportedReaderError::NamespaceImportMismatch {
                    namespace,
                    expected: import,
                    actual,
                });
            }
        };
        let expected = evidence.image().hash();
        let actual = O256::from_bytes(evidence.image().bytes());
        if actual != expected {
            return Err(ImportedReaderError::ImageMismatch { expected, actual });
        }
        if mounted.bytes() != evidence.image().bytes() {
            return Err(ImportedReaderError::MountedBytesMismatch { image: expected });
        }
        let sqlite = covalence_neutron::Connection::open_in_memory()?;
        mounted.attach(&sqlite, IMPORTED_SCHEMA)?;
        Ok(run(ImportedHolReader {
            owner,
            sqlite,
            mounted: mounted.clone(),
            trusted_import,
            import,
            namespace,
            source_namespace,
            _brand: PhantomData,
        }))
    }
}

impl<'reader, P: Policy> ImportedHolReader<'reader, '_, P> {
    /// Returns the matched persistent trusted-import ID.
    #[must_use]
    pub const fn trusted_import(&self) -> TrustedImportId {
        self.trusted_import
    }

    /// Returns the matched inert import-directory ID.
    #[must_use]
    pub const fn import(&self) -> ImportId {
        self.import
    }

    /// Returns the destination-local imported namespace alias authorizing this reader.
    #[must_use]
    pub const fn namespace(&self) -> NamespaceId {
        self.namespace
    }

    /// Looks up one export in a complete imported namespace.
    ///
    /// # Errors
    ///
    /// Returns an error for policy denial, changed VFS identity, `SQLite` failure, or corruption.
    pub fn namespace_export(
        &mut self,
        export: i64,
    ) -> Result<Option<ImportedExport<'reader>>, ImportedReaderError> {
        self.authorize(Operation::ReadImportedImageNamespace)?;
        self.verify_vfs()?;
        let row = self
            .sqlite
            .sqlite()
            .query_row(
                "SELECT sort, local_id FROM imported.hol_namespace_export
             WHERE namespace_id = ?1 AND export_id = ?2",
                [self.source_namespace, export],
                |row| Ok((row.get::<_, String>(0)?, row.get::<_, i64>(1)?)),
            )
            .optional()?;
        row.map(|(sort, id)| match sort.as_str() {
            "kind" => Ok(ImportedExport::Kind(ImportedKindId(id, PhantomData))),
            "type" => Ok(ImportedExport::Type(ImportedTypeId(id, PhantomData))),
            "term" => Ok(ImportedExport::Term(ImportedTermId(id, PhantomData))),
            "context" => Ok(ImportedExport::Context(ImportedContextId(id, PhantomData))),
            _ => Err(ImportedReaderError::CorruptExport {
                namespace: self.source_namespace,
                export,
            }),
        })
        .transpose()
    }

    /// Reads one imported term's validated structural representation.
    ///
    /// # Errors
    ///
    /// Returns an error for policy denial, changed VFS identity, absence, or corruption.
    pub fn term(
        &mut self,
        id: ImportedTermId<'reader>,
    ) -> Result<ImportedTermView<'reader>, ImportedReaderError> {
        self.authorize(Operation::ReadImportedImageTerm)?;
        self.verify_vfs()?;
        let row = self
            .sqlite
            .sqlite()
            .query_row(
                "SELECT tag, lhs, rhs, ty FROM imported.hol_node WHERE node_id = ?1",
                [id.0],
                |row| Ok((row.get(0)?, row.get(1)?, row.get(2)?, row.get(3)?)),
            )
            .optional()?
            .ok_or(ImportedReaderError::UnknownTerm(id.0))?;
        decode_term(row, id.0)
    }

    /// Looks up one exact persisted judgement in the verified imported image.
    ///
    /// The returned capability witnesses only the imported row. It cannot be converted into a
    /// local theorem capability.
    ///
    /// # Errors
    ///
    /// Returns an error for policy denial, changed VFS identity, or `SQLite` failure.
    pub fn theorem(
        &mut self,
        context: ImportedContextId<'reader>,
        conclusion: ImportedTermId<'reader>,
    ) -> Result<Option<ImportedTheorem<'reader>>, ImportedReaderError> {
        self.authorize(Operation::ReadImportedImageTheorem)?;
        self.verify_vfs()?;
        let exists = self.sqlite.sqlite().query_row(
            "SELECT EXISTS(
                 SELECT 1 FROM imported.hol_judgement
                 WHERE ctx_id = ?1 AND term_id = ?2
             )",
            [context.0, conclusion.0],
            |row| row.get::<_, bool>(0),
        )?;
        Ok(exists.then_some(ImportedTheorem {
            context,
            conclusion,
        }))
    }

    fn authorize(&mut self, operation: Operation) -> Result<(), ImportedReaderError> {
        if self.owner.parts_mut().1.policy.allows(operation) {
            Ok(())
        } else {
            Err(ImportedReaderError::Denied(operation))
        }
    }

    fn verify_vfs(&self) -> Result<(), ImportedReaderError> {
        self.mounted
            .verify(&self.sqlite, IMPORTED_SCHEMA)
            .map_err(Into::into)
    }
}

type TermRow = (String, Option<i64>, Option<i64>, Option<i64>);

fn decode_term<'reader>(
    row: TermRow,
    id: i64,
) -> Result<ImportedTermView<'reader>, ImportedReaderError> {
    let (tag, lhs, rhs, ty) = row;
    let corrupt = || ImportedReaderError::CorruptTerm(id);
    match (tag.as_str(), lhs, rhs, ty) {
        ("MBOOL", Some(value @ 0..=1), None, Some(_)) => Ok(ImportedTermView::Bool(value != 0)),
        ("MFV", Some(symbol), None, Some(ty)) => Ok(ImportedTermView::Free {
            symbol: u64::try_from(symbol).map_err(|_| corrupt())?,
            ty: ImportedTypeId(ty, PhantomData),
        }),
        ("MCONST", Some(symbol), None, Some(ty)) => Ok(ImportedTermView::Constant {
            symbol,
            ty: ImportedTypeId(ty, PhantomData),
        }),
        ("MBV", Some(index), None, Some(ty)) => Ok(ImportedTermView::Bound {
            index: u64::try_from(index).map_err(|_| corrupt())?,
            ty: ImportedTypeId(ty, PhantomData),
        }),
        ("MAPP", Some(function), Some(argument), Some(ty)) => Ok(ImportedTermView::Application {
            function: ImportedTermId(function, PhantomData),
            argument: ImportedTermId(argument, PhantomData),
            ty: ImportedTypeId(ty, PhantomData),
        }),
        ("MLAM", Some(parameter_type), Some(body), Some(ty)) => Ok(ImportedTermView::Lambda {
            parameter_type: ImportedTypeId(parameter_type, PhantomData),
            body: ImportedTermId(body, PhantomData),
            ty: ImportedTypeId(ty, PhantomData),
        }),
        ("MEQ", Some(left), Some(right), Some(ty)) => Ok(ImportedTermView::Equality {
            left: ImportedTermId(left, PhantomData),
            right: ImportedTermId(right, PhantomData),
            ty: ImportedTypeId(ty, PhantomData),
        }),
        ("MEPS", Some(predicate), None, Some(ty)) => Ok(ImportedTermView::Epsilon {
            predicate: ImportedTermId(predicate, PhantomData),
            ty: ImportedTypeId(ty, PhantomData),
        }),
        _ => Err(corrupt()),
    }
}

/// Failure to open or use a scoped immutable imported-image reader.
#[derive(Debug)]
pub enum ImportedReaderError {
    Denied(Operation),
    Import(ImportError),
    NamespaceImportMismatch {
        namespace: NamespaceId,
        expected: ImportId,
        actual: ImportId,
    },
    ImageMismatch {
        expected: O256,
        actual: O256,
    },
    MountedBytesMismatch {
        image: O256,
    },
    Connection(covalence_neutron::ConnectionError),
    ImmutableImage(covalence_neutron::ImmutableImageError),
    Sqlite(sqlite::Error),
    Vfs(covalence_neutron::DatabaseVfsError),
    CorruptExport {
        namespace: i64,
        export: i64,
    },
    UnknownTerm(i64),
    CorruptTerm(i64),
}

impl fmt::Display for ImportedReaderError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Denied(op) => write!(f, "HOL policy denied {op:?}"),
            Self::Import(e) => e.fmt(f),
            Self::NamespaceImportMismatch {
                namespace,
                expected,
                actual,
            } => write!(
                f,
                "imported namespace {} names import {}, not matched import {}",
                namespace.get(),
                actual.get(),
                expected.get()
            ),
            Self::ImageMismatch { expected, actual } => {
                write!(f, "imported image {actual} differs from {expected}")
            }
            Self::MountedBytesMismatch { image } => {
                write!(
                    f,
                    "mounted bytes differ from validated imported image {image}"
                )
            }
            Self::Connection(e) => e.fmt(f),
            Self::ImmutableImage(e) => e.fmt(f),
            Self::Sqlite(e) => e.fmt(f),
            Self::Vfs(e) => e.fmt(f),
            Self::CorruptExport { namespace, export } => {
                write!(f, "imported export ({namespace}, {export}) is corrupt")
            }
            Self::UnknownTerm(id) => write!(f, "unknown imported term {id}"),
            Self::CorruptTerm(id) => write!(f, "imported term {id} is corrupt"),
        }
    }
}

impl StdError for ImportedReaderError {
    fn source(&self) -> Option<&(dyn StdError + 'static)> {
        match self {
            Self::Connection(e) => Some(e),
            Self::Import(e) => Some(e),
            Self::ImmutableImage(e) => Some(e),
            Self::Sqlite(e) => Some(e),
            Self::Vfs(e) => Some(e),
            _ => None,
        }
    }
}
impl From<ImportError> for ImportedReaderError {
    fn from(e: ImportError) -> Self {
        Self::Import(e)
    }
}

impl From<covalence_neutron::ConnectionError> for ImportedReaderError {
    fn from(e: covalence_neutron::ConnectionError) -> Self {
        Self::Connection(e)
    }
}
impl From<covalence_neutron::ImmutableImageError> for ImportedReaderError {
    fn from(e: covalence_neutron::ImmutableImageError) -> Self {
        Self::ImmutableImage(e)
    }
}
impl From<sqlite::Error> for ImportedReaderError {
    fn from(e: sqlite::Error) -> Self {
        Self::Sqlite(e)
    }
}
impl From<covalence_neutron::DatabaseVfsError> for ImportedReaderError {
    fn from(e: covalence_neutron::DatabaseVfsError) -> Self {
        Self::Vfs(e)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        AllowAll, AuthenticatedValidatedHolImage, ContextId, ExportId, HolDatabaseRef, Kernel,
        NamespaceError, NamespaceExport, SignedSnapshotEnvelope,
    };
    use std::{cell::Cell, rc::Rc, sync::Arc};

    #[derive(Clone)]
    struct SelectivePolicy {
        denied: Rc<Cell<Option<Operation>>>,
    }

    impl Policy for SelectivePolicy {
        fn allows(&mut self, operation: Operation) -> bool {
            self.denied.get() != Some(operation)
        }
    }

    #[test]
    fn imported_constant_preserves_its_closed_signature_symbol_and_type() {
        let view = decode_term(("MCONST".to_owned(), Some(-7), None, Some(42)), 9).unwrap();
        let ImportedTermView::Constant { symbol, ty } = view else {
            panic!("expected imported constant")
        };
        assert_eq!(symbol, -7);
        assert_eq!(ty.get(), 42);
    }

    #[test]
    fn imported_epsilon_preserves_its_predicate_and_result_type() {
        let view = decode_term(("MEPS".to_owned(), Some(17), None, Some(42)), 9).unwrap();
        let ImportedTermView::Epsilon { predicate, ty } = view else {
            panic!("expected imported epsilon")
        };
        assert_eq!(predicate.get(), 17);
        assert_eq!(ty.get(), 42);
        assert!(matches!(
            decode_term(("MEPS".to_owned(), Some(17), Some(18), Some(42)), 9),
            Err(ImportedReaderError::CorruptTerm(9))
        ));
    }

    #[test]
    #[allow(clippy::too_many_lines)]
    fn scoped_reader_uses_verified_vfs_and_exposes_only_scoped_evidence() {
        let source_kernel = Kernel::ephemeral();
        let mut source = source_kernel.open_hol(AllowAll).unwrap();
        let truth = source.insert_bool_term(true).unwrap();
        source
            .with_proof_session(|mut proof| {
                let theorem = proof.prove_truth(ContextId::empty())?;
                assert_eq!(theorem.conclusion(), truth);
                proof.persist_theorem(&theorem)
            })
            .unwrap();
        let falsehood = source.insert_bool_term(false).unwrap();
        let bool_type = source.insert_bool_type().unwrap();
        let bound = source.insert_bound_term(0, bool_type).unwrap();
        let predicate = source.insert_lambda(bool_type, bound).unwrap();
        let epsilon = source.insert_epsilon(predicate).unwrap();
        let namespace = source.create_namespace(None, Some("demo")).unwrap();
        source
            .export_value(
                namespace,
                ExportId::from_i64(7),
                NamespaceExport::Term(truth),
                Some("truth"),
            )
            .unwrap();
        source
            .export_value(
                namespace,
                ExportId::from_i64(10),
                NamespaceExport::Term(epsilon),
                Some("epsilon"),
            )
            .unwrap();
        source
            .export_value(
                namespace,
                ExportId::from_i64(8),
                NamespaceExport::Context(ContextId::empty()),
                Some("empty"),
            )
            .unwrap();
        source
            .export_value(
                namespace,
                ExportId::from_i64(9),
                NamespaceExport::Term(falsehood),
                Some("false"),
            )
            .unwrap();
        let signed = source_kernel.export_hol(&mut source).unwrap();
        let attestation = signed.attestation();
        let authenticated_image = || {
            let authenticated = SignedSnapshotEnvelope::new(
                signed.image().bytes(),
                attestation.schema(),
                attestation.image(),
                attestation.signer(),
                *attestation.public_key(),
                attestation.signature(),
            )
            .authenticate()
            .unwrap();
            AuthenticatedValidatedHolImage::validate_default(authenticated).unwrap()
        };
        let evidence = authenticated_image();
        let mounted =
            covalence_neutron::ImmutableImage::register(Arc::from(evidence.image().bytes()))
                .unwrap();
        drop(source);

        let denied = Rc::new(Cell::new(None));
        let mut target = source_kernel
            .open_hol(SelectivePolicy {
                denied: Rc::clone(&denied),
            })
            .unwrap();
        let claim = evidence.claim();
        target.trust_snapshot_signer(claim).unwrap();
        target.accept_authenticated_snapshot(claim).unwrap();
        let import = target
            .register_import(HolDatabaseRef::new(claim.schema(), claim.image()))
            .unwrap();
        let trusted = target.accept_trusted_import(import, claim).unwrap();
        let imported_namespace = target
            .create_imported_namespace(None, Some("downloaded"), import, namespace.get())
            .unwrap();
        let other_import = target
            .register_import(HolDatabaseRef::new(
                O256::from_bytes(b"other schema"),
                O256::from_bytes(b"other image"),
            ))
            .unwrap();
        let wrong_namespace = target
            .create_imported_namespace(None, Some("wrong"), other_import, namespace.get())
            .unwrap();
        assert!(matches!(
            target
                .match_trusted_import_image(trusted, authenticated_image())
                .unwrap()
                .with_mounted_reader(NamespaceId::root(), &mounted, |_| ()),
            Err(ImportedReaderError::Import(ImportError::LocalNamespace(_)))
        ));
        assert!(matches!(
            target
                .match_trusted_import_image(trusted, authenticated_image())
                .unwrap()
                .with_mounted_reader(NamespaceId::from_i64(999), &mounted, |_| ()),
            Err(ImportedReaderError::Import(ImportError::Namespace(
                NamespaceError::UnknownNamespace(_)
            )))
        ));
        assert!(matches!(
            target
                .match_trusted_import_image(trusted, authenticated_image())
                .unwrap()
                .with_mounted_reader(wrong_namespace, &mounted, |_| ()),
            Err(ImportedReaderError::NamespaceImportMismatch { .. })
        ));
        let wrong_mount = covalence_neutron::ImmutableImage::register(Arc::from(
            b"different resident bytes".as_slice(),
        ))
        .unwrap();
        assert!(matches!(
            target
                .match_trusted_import_image(trusted, authenticated_image())
                .unwrap()
                .with_mounted_reader(imported_namespace, &wrong_mount, |_| ()),
            Err(ImportedReaderError::MountedBytesMismatch { .. })
        ));
        let before = target.parts_mut().0.serialize().unwrap();
        let matched = target
            .match_trusted_import_image(trusted, evidence)
            .unwrap();

        matched
            .with_mounted_reader(imported_namespace, &mounted, |mut reader| {
                assert_eq!(reader.trusted_import(), trusted);
                assert_eq!(reader.import(), import);
                assert_eq!(reader.namespace(), imported_namespace);
                let exported = reader.namespace_export(7).unwrap().unwrap();
                let ImportedExport::Term(term) = exported else {
                    panic!("expected imported term export")
                };
                assert_eq!(term.get(), truth.get());
                assert_eq!(reader.term(term).unwrap(), ImportedTermView::Bool(true));
                let ImportedExport::Context(context) = reader.namespace_export(8).unwrap().unwrap()
                else {
                    panic!("expected imported context export")
                };
                let theorem = reader.theorem(context, term).unwrap().unwrap();
                assert_eq!(theorem.context(), context);
                assert_eq!(theorem.conclusion(), term);
                let ImportedExport::Term(falsehood) = reader.namespace_export(9).unwrap().unwrap()
                else {
                    panic!("expected imported term export")
                };
                assert!(reader.theorem(context, falsehood).unwrap().is_none());
                let ImportedExport::Term(imported_epsilon) =
                    reader.namespace_export(10).unwrap().unwrap()
                else {
                    panic!("expected imported epsilon export")
                };
                assert_eq!(imported_epsilon.get(), epsilon.get());
                assert_eq!(
                    reader.term(imported_epsilon).unwrap(),
                    ImportedTermView::Epsilon {
                        predicate: ImportedTermId(predicate.get(), PhantomData),
                        ty: ImportedTypeId(bool_type.get(), PhantomData),
                    }
                );
                denied.set(Some(Operation::ReadImportedImageTheorem));
                assert!(matches!(
                    reader.theorem(context, term),
                    Err(ImportedReaderError::Denied(
                        Operation::ReadImportedImageTheorem
                    ))
                ));
                reader
                    .mounted
                    .verify(&reader.sqlite, IMPORTED_SCHEMA)
                    .unwrap();
                assert!(
                    reader
                        .sqlite
                        .sqlite()
                        .execute("UPDATE imported.hol_node SET lhs = 0", [])
                        .is_err()
                );
            })
            .unwrap();

        assert_eq!(target.parts_mut().0.serialize().unwrap(), before);
        assert_eq!(
            target
                .parts_mut()
                .0
                .sqlite()
                .query_row(
                    "SELECT count(*) FROM pragma_database_list WHERE name = 'imported'",
                    [],
                    |row| row.get::<_, i64>(0),
                )
                .unwrap(),
            0
        );
    }
}
