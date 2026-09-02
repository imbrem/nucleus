//! Host implementation of the portable proof-component interface.

use bytes::Bytes;
use std::sync::Arc;

use covalence_data_cas::{AsyncCas, AsyncCasError, IndexCas, get_exact_fact};
use covalence_lib_error::snafu::Snafu;
use covalence_lib_hash::O256;
use covalence_lib_wasm::wasmtime;
use covalence_logic_cas::CasFact;
use covalence_logic_hol::{
    Arena, Import, Kernel as HolKernel, Link, LinkFormat, Ref, Resolver, Sort as HolSort,
    SynFactId, SynRel as HolSynRel, Table, wire,
};
use wasmtime::component::{Accessor, HasData, Resource, ResourceTable};

#[derive(Clone)]
pub struct HostBytes(Bytes);

#[derive(Clone)]
pub struct HostBlob(CasFact);

#[derive(Default)]
pub struct HostIndexCas(IndexCas);

#[derive(Clone, Default)]
pub struct HostArena(Arena);

#[derive(Clone)]
pub struct HostTable(Table);

#[derive(Default)]
pub struct HostKernel(HolKernel);

wasmtime::component::bindgen!({
    path: "../../wit/proof",
    world: "proof",
    wasmtime_crate: covalence_lib_wasm::wasmtime,
    with: {
        "nucleus:proof/host.bytes": HostBytes,
        "nucleus:proof/host.blob": HostBlob,
        "nucleus:proof/host.index-cas": HostIndexCas,
        "nucleus:proof/host.arena": HostArena,
        "nucleus:proof/host.table": HostTable,
        "nucleus:proof/host.kernel": HostKernel,
    },
    imports: { default: trappable },
});

struct ProofState {
    table: ResourceTable,
    cas: IndexCas,
    provider: Option<Arc<dyn AsyncCas>>,
}

impl Default for ProofState {
    fn default() -> Self {
        let mut cas = IndexCas::new();
        cas.insert(Bytes::from_static(b"nucleus proof demo"));
        Self {
            table: ResourceTable::new(),
            cas,
            provider: None,
        }
    }
}

impl ProofState {
    fn with_provider(provider: Arc<dyn AsyncCas>) -> Self {
        Self {
            provider: Some(provider),
            ..Self::default()
        }
    }
}

impl HasData for ProofState {
    type Data<'a> = &'a mut Self;
}

async fn yield_once() {
    let mut yielded = false;
    futures::future::poll_fn(|cx| {
        if yielded {
            std::task::Poll::Ready(())
        } else {
            yielded = true;
            cx.waker().wake_by_ref();
            std::task::Poll::Pending
        }
    })
    .await;
}

fn address(value: Vec<u8>) -> Result<O256, String> {
    let bytes: [u8; 32] = value
        .try_into()
        .map_err(|value: Vec<u8>| format!("CAS addresses contain 32 bytes, got {}", value.len()))?;
    Ok(O256::from_array(bytes))
}

fn usize_from_u64(value: u64, what: &str) -> Result<usize, String> {
    usize::try_from(value).map_err(|_| format!("{what} does not fit in host memory"))
}

fn u64_from_usize(value: usize, what: &str) -> wasmtime::Result<u64> {
    u64::try_from(value).map_err(|_| wasmtime::Error::msg(format!("{what} exceeds u64")))
}

/// Resolve the four references a binary connective takes, reporting the first
/// failure.
fn binary_logic(
    bool_type: u64,
    binder: u64,
    left: u64,
    right: u64,
) -> Result<(Ref, Ref, Ref, Ref), String> {
    Ok((
        reference(bool_type)?,
        reference(binder)?,
        reference(left)?,
        reference(right)?,
    ))
}

/// Marshal a concluded infinity axiom out to the component ABI.
fn infinity_axiom(
    axiom: covalence_logic_hol::InfinityAxiom,
) -> nucleus::proof::host::InfinityAxiom {
    nucleus::proof::host::InfinityAxiom {
        exists_type: u64_from_ref(axiom.exists_type),
        body: u64_from_ref(axiom.body),
        carrier_name: axiom.carrier_name,
        base_name: axiom.base_name,
        theorem: axiom.theorem.get().unsigned_abs().into(),
    }
}

/// Marshal a built subtype axiom out to the component ABI.
fn subtype_axiom(axiom: covalence_logic_hol::SubtypeAxiom) -> nucleus::proof::host::SubtypeAxiom {
    nucleus::proof::host::SubtypeAxiom {
        carrier: u64_from_ref(axiom.carrier),
        predicate: u64_from_ref(axiom.predicate),
        exists_type: u64_from_ref(axiom.exists_type),
        package_body: u64_from_ref(axiom.package_body),
        model_name: axiom.model_name,
        base_name: axiom.base_name,
        theorem: axiom.theorem.get().unsigned_abs().into(),
    }
}

fn u64_from_ref(reference: Ref) -> u64 {
    reference.get().unsigned_abs().into()
}

fn reference(value: u64) -> Result<Ref, String> {
    let value = i32::try_from(value).map_err(|_| "reference exceeds i32".to_owned())?;
    Ref::new(value).ok_or_else(|| "references are one-based".to_owned())
}

fn fact_id(value: u64) -> Result<SynFactId, String> {
    let value = i32::try_from(value).map_err(|_| "syntactic-fact slot exceeds i32".to_owned())?;
    SynFactId::new(value).ok_or_else(|| "syntactic-fact slots are one-based".to_owned())
}

fn theorem_id(value: u64) -> Result<covalence_logic_hol::ThmId, String> {
    let value = i32::try_from(value).map_err(|_| "theorem slot exceeds i32".to_owned())?;
    covalence_logic_hol::ThmId::new(value).ok_or_else(|| "theorem slots are one-based".to_owned())
}

fn import_id(value: u64) -> Result<covalence_logic_hol::ImportId, String> {
    let value = i32::try_from(value).map_err(|_| "import ID exceeds i32".to_owned())?;
    covalence_logic_hol::ImportId::new(value).ok_or_else(|| "import IDs are one-based".to_owned())
}

fn optional_fact_id(value: Option<u64>) -> Result<Option<SynFactId>, String> {
    value.map(fact_id).transpose()
}

fn pushed(value: Option<Ref>, what: &str) -> Result<u64, String> {
    value
        .map(ref_index)
        .ok_or_else(|| format!("{what} exceeds the arena's index space"))
}

fn pushed_import(value: Option<covalence_logic_hol::ImportId>) -> Result<u64, String> {
    value
        .map(import_index)
        .ok_or_else(|| "import exceeds the arena's index space".to_owned())
}

fn ref_index(value: Ref) -> u64 {
    u64::try_from(value.get()).expect("resident references are positive")
}

fn import_index(value: covalence_logic_hol::ImportId) -> u64 {
    u64::try_from(value.get()).expect("resident import IDs are positive")
}

fn fact_index(value: SynFactId) -> u64 {
    u64::try_from(value.get()).expect("resident syntactic-fact IDs are positive")
}

fn link(value: Vec<u8>) -> Result<Link, String> {
    Ok(Link {
        format: LinkFormat::Cbor,
        blake3: address(value)?,
    })
}

#[derive(Debug)]
struct ResolveFailure(String);

impl std::fmt::Display for ResolveFailure {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        output.write_str(&self.0)
    }
}

impl std::error::Error for ResolveFailure {}

struct CasResolver<'a>(&'a IndexCas);

impl Resolver for CasResolver<'_> {
    type Error = ResolveFailure;

    fn resolve(&mut self, link: &Link) -> Result<Table, Self::Error> {
        let fact = self
            .0
            .fact_at(link.blake3)
            .cloned()
            .ok_or_else(|| ResolveFailure(format!("CAS has no object at {}", link.blake3)))?;
        Table::try_from(fact).map_err(|error| ResolveFailure(error.to_string()))
    }
}

impl nucleus::proof::host::HostBytes for ProofState {
    fn new(&mut self, value: Vec<u8>) -> wasmtime::Result<Resource<HostBytes>> {
        Ok(self.table.push(HostBytes(Bytes::from(value)))?)
    }

    fn len(&mut self, value: Resource<HostBytes>) -> wasmtime::Result<u64> {
        u64_from_usize(self.table.get(&value)?.0.len(), "byte-buffer length")
    }

    fn to_list(&mut self, value: Resource<HostBytes>) -> wasmtime::Result<Vec<u8>> {
        Ok(self.table.get(&value)?.0.to_vec())
    }

    fn slice(
        &mut self,
        value: Resource<HostBytes>,
        start: u64,
        end: u64,
    ) -> wasmtime::Result<Result<Resource<HostBytes>, String>> {
        let result = (|| {
            let start = usize_from_u64(start, "slice start")?;
            let end = usize_from_u64(end, "slice end")?;
            let bytes = self
                .table
                .get(&value)
                .map_err(|error| error.to_string())?
                .0
                .clone();
            if start > end || end > bytes.len() {
                return Err("slice lies outside the byte buffer".to_owned());
            }
            let bytes = bytes.slice(start..end);
            self.table
                .push(HostBytes(bytes))
                .map_err(|error| error.to_string())
        })();
        Ok(result)
    }

    fn blob(&mut self, value: Resource<HostBytes>) -> wasmtime::Result<Resource<HostBlob>> {
        let bytes = self.table.get(&value)?.0.clone();
        Ok(self.table.push(HostBlob(CasFact::from_bytes(bytes)))?)
    }

    fn drop(&mut self, value: Resource<HostBytes>) -> wasmtime::Result<()> {
        self.table.delete(value)?;
        Ok(())
    }
}

impl nucleus::proof::host::HostBlob for ProofState {
    fn check(
        &mut self,
        claimed: Vec<u8>,
        value: Resource<HostBytes>,
    ) -> wasmtime::Result<Result<Resource<HostBlob>, String>> {
        let result = (|| {
            let claimed = address(claimed)?;
            let bytes = self
                .table
                .get(&value)
                .map_err(|error| error.to_string())?
                .0
                .clone();
            let fact = CasFact::new(claimed, bytes).map_err(|error| error.to_string())?;
            self.table
                .push(HostBlob(fact))
                .map_err(|error| error.to_string())
        })();
        Ok(result)
    }

    fn address(&mut self, value: Resource<HostBlob>) -> wasmtime::Result<Vec<u8>> {
        Ok(self.table.get(&value)?.0.hash().as_ref().to_vec())
    }

    fn bytes(&mut self, value: Resource<HostBlob>) -> wasmtime::Result<Resource<HostBytes>> {
        let bytes = self.table.get(&value)?.0.bytes().clone();
        Ok(self.table.push(HostBytes(bytes))?)
    }

    fn len(&mut self, value: Resource<HostBlob>) -> wasmtime::Result<u64> {
        u64_from_usize(self.table.get(&value)?.0.bytes().len(), "blob length")
    }

    fn drop(&mut self, value: Resource<HostBlob>) -> wasmtime::Result<()> {
        self.table.delete(value)?;
        Ok(())
    }
}

impl nucleus::proof::host::HostIndexCas for ProofState {
    fn new(&mut self) -> wasmtime::Result<Resource<HostIndexCas>> {
        Ok(self.table.push(HostIndexCas(IndexCas::new()))?)
    }

    fn insert(
        &mut self,
        cas: Resource<HostIndexCas>,
        value: Resource<HostBlob>,
    ) -> wasmtime::Result<u64> {
        let fact = self.table.get(&value)?.0.clone();
        Ok(self.table.get_mut(&cas)?.0.insert_fact(fact))
    }

    fn put(
        &mut self,
        cas: Resource<HostIndexCas>,
        value: Resource<HostBytes>,
    ) -> wasmtime::Result<u64> {
        let bytes = self.table.get(&value)?.0.clone();
        Ok(self.table.get_mut(&cas)?.0.insert(bytes))
    }

    fn get(
        &mut self,
        cas: Resource<HostIndexCas>,
        object: u64,
    ) -> wasmtime::Result<Option<Resource<HostBlob>>> {
        let fact = self.table.get(&cas)?.0.fact(object).cloned();
        fact.map(|fact| self.table.push(HostBlob(fact)))
            .transpose()
            .map_err(Into::into)
    }

    fn find(
        &mut self,
        cas: Resource<HostIndexCas>,
        value: Vec<u8>,
    ) -> wasmtime::Result<Result<Option<u64>, String>> {
        let address = match address(value) {
            Ok(address) => address,
            Err(error) => return Ok(Err(error)),
        };
        Ok(Ok(self.table.get(&cas)?.0.id(address)))
    }

    fn remove(
        &mut self,
        cas: Resource<HostIndexCas>,
        value: Vec<u8>,
    ) -> wasmtime::Result<Result<bool, String>> {
        let address = match address(value) {
            Ok(address) => address,
            Err(error) => return Ok(Err(error)),
        };
        Ok(Ok(self.table.get_mut(&cas)?.0.remove(address)))
    }

    fn len(&mut self, cas: Resource<HostIndexCas>) -> wasmtime::Result<u64> {
        u64_from_usize(self.table.get(&cas)?.0.fact_count(), "CAS object count")
    }

    fn drop(&mut self, cas: Resource<HostIndexCas>) -> wasmtime::Result<()> {
        self.table.delete(cas)?;
        Ok(())
    }
}

impl nucleus::proof::host::HostArena for ProofState {
    fn new(&mut self) -> wasmtime::Result<Resource<HostArena>> {
        Ok(self.table.push(HostArena(Arena::empty()))?)
    }

    fn from_cbor(
        &mut self,
        value: Resource<HostBytes>,
    ) -> wasmtime::Result<Result<Resource<HostArena>, String>> {
        let bytes = self.table.get(&value)?.0.clone();
        let result = wire::deserialize(bytes.as_ref())
            .map(HostArena)
            .map_err(|error| error.to_string())
            .and_then(|arena| self.table.push(arena).map_err(|error| error.to_string()));
        Ok(result)
    }

    fn to_cbor(
        &mut self,
        arena: Resource<HostArena>,
    ) -> wasmtime::Result<Result<Resource<HostBytes>, String>> {
        let result = (|| {
            let mut bytes = Vec::new();
            wire::serialize(
                &self.table.get(&arena).map_err(|error| error.to_string())?.0,
                &mut bytes,
            )
            .map_err(|error| error.to_string())?;
            self.table
                .push(HostBytes(Bytes::from(bytes)))
                .map_err(|error| error.to_string())
        })();
        Ok(result)
    }

    fn address(&mut self, arena: Resource<HostArena>) -> wasmtime::Result<Vec<u8>> {
        Ok(self.table.get(&arena)?.0.addr().as_ref().to_vec())
    }

    fn len(&mut self, arena: Resource<HostArena>) -> wasmtime::Result<u64> {
        u64_from_usize(self.table.get(&arena)?.0.len(), "arena length")
    }

    fn kind_star(&mut self, arena: Resource<HostArena>) -> wasmtime::Result<Result<u64, String>> {
        Ok(pushed(
            self.table.get_mut(&arena)?.0.push_kind_star(),
            "definition",
        ))
    }

    fn kind_arr(
        &mut self,
        arena: Resource<HostArena>,
        domain: u64,
        codomain: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(domain), reference(codomain)) {
            (Ok(domain), Ok(codomain)) => pushed(
                self.table
                    .get_mut(&arena)?
                    .0
                    .push_kind_arr(domain, codomain),
                "definition",
            ),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn bool_type(&mut self, arena: Resource<HostArena>) -> wasmtime::Result<Result<u64, String>> {
        Ok(pushed(
            self.table.get_mut(&arena)?.0.push_bool_ty(),
            "definition",
        ))
    }

    fn ty_arr(
        &mut self,
        arena: Resource<HostArena>,
        domain: u64,
        codomain: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(domain), reference(codomain)) {
            (Ok(domain), Ok(codomain)) => pushed(
                self.table.get_mut(&arena)?.0.push_ty_arr(domain, codomain),
                "definition",
            ),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn ty_app(
        &mut self,
        arena: Resource<HostArena>,
        function: u64,
        argument: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(function), reference(argument)) {
            (Ok(function), Ok(argument)) => pushed(
                self.table
                    .get_mut(&arena)?
                    .0
                    .push_ty_app(function, argument),
                "definition",
            ),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn ty_lam(
        &mut self,
        arena: Resource<HostArena>,
        binder: u64,
        body: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(binder), reference(body)) {
            (Ok(binder), Ok(body)) => pushed(
                self.table.get_mut(&arena)?.0.push_ty_lam(binder, body),
                "definition",
            ),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn ty_fv(
        &mut self,
        arena: Resource<HostArena>,
        name: u64,
        kind: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let kind = match reference(kind) {
            Ok(kind) => kind,
            Err(error) => return Ok(Err(error)),
        };
        Ok(pushed(
            self.table.get_mut(&arena)?.0.push_ty_fv(name, kind),
            "definition",
        ))
    }

    fn ty_exists(
        &mut self,
        arena: Resource<HostArena>,
        name: u64,
        predicate: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let predicate = match reference(predicate) {
            Ok(predicate) => predicate,
            Err(error) => return Ok(Err(error)),
        };
        Ok(pushed(
            self.table
                .get_mut(&arena)?
                .0
                .push_ty_exists(name, predicate),
            "definition",
        ))
    }

    fn ty_forall(
        &mut self,
        arena: Resource<HostArena>,
        name: u64,
        predicate: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let predicate = match reference(predicate) {
            Ok(predicate) => predicate,
            Err(error) => return Ok(Err(error)),
        };
        Ok(pushed(
            self.table
                .get_mut(&arena)?
                .0
                .push_ty_forall(name, predicate),
            "definition",
        ))
    }

    fn model(
        &mut self,
        arena: Resource<HostArena>,
        name: u64,
        predicate: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let predicate = match reference(predicate) {
            Ok(predicate) => predicate,
            Err(error) => return Ok(Err(error)),
        };
        Ok(pushed(
            self.table.get_mut(&arena)?.0.push_model(name, predicate),
            "definition",
        ))
    }

    fn tm_fv(
        &mut self,
        arena: Resource<HostArena>,
        name: u64,
        ty: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let ty = match reference(ty) {
            Ok(ty) => ty,
            Err(error) => return Ok(Err(error)),
        };
        Ok(pushed(
            self.table.get_mut(&arena)?.0.push_tm_fv(name, ty),
            "definition",
        ))
    }

    fn app(
        &mut self,
        arena: Resource<HostArena>,
        function: u64,
        argument: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(function), reference(argument)) {
            (Ok(function), Ok(argument)) => pushed(
                self.table.get_mut(&arena)?.0.push_app(function, argument),
                "definition",
            ),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn lam(
        &mut self,
        arena: Resource<HostArena>,
        binder: u64,
        body: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(binder), reference(body)) {
            (Ok(binder), Ok(body)) => pushed(
                self.table.get_mut(&arena)?.0.push_lam(binder, body),
                "definition",
            ),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn bool_lit(
        &mut self,
        arena: Resource<HostArena>,
        value: bool,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(pushed(
            self.table.get_mut(&arena)?.0.push_bool(value),
            "definition",
        ))
    }

    fn tm_eq(
        &mut self,
        arena: Resource<HostArena>,
        left: u64,
        right: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(left), reference(right)) {
            (Ok(left), Ok(right)) => pushed(
                self.table.get_mut(&arena)?.0.push_tm_eq(left, right),
                "definition",
            ),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn eps(
        &mut self,
        arena: Resource<HostArena>,
        ty: u64,
        predicate: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(ty), reference(predicate)) {
            (Ok(ty), Ok(predicate)) => pushed(
                self.table.get_mut(&arena)?.0.push_eps(ty, predicate),
                "definition",
            ),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn kind_ref(
        &mut self,
        arena: Resource<HostArena>,
        source: u64,
        foreign: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (import_id(source), reference(foreign)) {
            (Ok(source), Ok(foreign)) => pushed(
                self.table.get_mut(&arena)?.0.push_kind_ref(source, foreign),
                "definition",
            ),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn ty_ref(
        &mut self,
        arena: Resource<HostArena>,
        source: u64,
        foreign: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (import_id(source), reference(foreign)) {
            (Ok(source), Ok(foreign)) => pushed(
                self.table.get_mut(&arena)?.0.push_ty_ref(source, foreign),
                "definition",
            ),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn tm_ref(
        &mut self,
        arena: Resource<HostArena>,
        source: u64,
        foreign: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (import_id(source), reference(foreign)) {
            (Ok(source), Ok(foreign)) => pushed(
                self.table.get_mut(&arena)?.0.push_tm_ref(source, foreign),
                "definition",
            ),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn import_null(&mut self, arena: Resource<HostArena>) -> wasmtime::Result<Result<u64, String>> {
        Ok(pushed_import(
            self.table.get_mut(&arena)?.0.push_import(Import::Null),
        ))
    }

    fn import_arena(
        &mut self,
        arena: Resource<HostArena>,
        value: Resource<HostArena>,
    ) -> wasmtime::Result<Result<u64, String>> {
        let value = self.table.get(&value)?.0.clone();
        Ok(pushed_import(
            self.table
                .get_mut(&arena)?
                .0
                .push_import(Import::Literal(Box::new(value))),
        ))
    }

    fn import_link(
        &mut self,
        arena: Resource<HostArena>,
        value: Vec<u8>,
    ) -> wasmtime::Result<Result<u64, String>> {
        let value = match link(value) {
            Ok(value) => value,
            Err(error) => return Ok(Err(error)),
        };
        Ok(pushed_import(
            self.table
                .get_mut(&arena)?
                .0
                .push_import(Import::Link(value)),
        ))
    }

    fn add_context(
        &mut self,
        arena: Resource<HostArena>,
        proposition: u64,
    ) -> wasmtime::Result<Result<(), String>> {
        let proposition = match reference(proposition) {
            Ok(proposition) => proposition,
            Err(error) => return Ok(Err(error)),
        };
        self.table.get_mut(&arena)?.0.insert_context(proposition);
        Ok(Ok(()))
    }

    fn add_axiom(&mut self, arena: Resource<HostArena>, name: String) -> wasmtime::Result<()> {
        self.table.get_mut(&arena)?.0.insert_axiom(name);
        Ok(())
    }

    fn drop(&mut self, arena: Resource<HostArena>) -> wasmtime::Result<()> {
        self.table.delete(arena)?;
        Ok(())
    }
}

impl nucleus::proof::host::HostTable for ProofState {
    fn from_arena(
        &mut self,
        value: Resource<HostArena>,
    ) -> wasmtime::Result<Result<Resource<HostTable>, String>> {
        let arena = self.table.get(&value)?.0.clone();
        let result = Table::from_arena(arena)
            .map(HostTable)
            .map_err(|error| error.to_string())
            .and_then(|table| self.table.push(table).map_err(|error| error.to_string()));
        Ok(result)
    }

    fn from_blob(
        &mut self,
        value: Resource<HostBlob>,
    ) -> wasmtime::Result<Result<Resource<HostTable>, String>> {
        let fact = self.table.get(&value)?.0.clone();
        let result = Table::try_from(fact)
            .map(HostTable)
            .map_err(|error| error.to_string())
            .and_then(|table| self.table.push(table).map_err(|error| error.to_string()));
        Ok(result)
    }

    fn address(&mut self, table: Resource<HostTable>) -> wasmtime::Result<Vec<u8>> {
        Ok(self.table.get(&table)?.0.addr().as_ref().to_vec())
    }

    fn arena(&mut self, table: Resource<HostTable>) -> wasmtime::Result<Resource<HostArena>> {
        let arena = self.table.get(&table)?.0.as_ref().clone();
        Ok(self.table.push(HostArena(arena))?)
    }

    fn drop(&mut self, table: Resource<HostTable>) -> wasmtime::Result<()> {
        self.table.delete(table)?;
        Ok(())
    }
}
fn syn_relation(value: nucleus::proof::host::SynRel) -> HolSynRel {
    match value {
        nucleus::proof::host::SynRel::Syn => HolSynRel::Syn,
        nucleus::proof::host::SynRel::Alpha => HolSynRel::Alpha,
        nucleus::proof::host::SynRel::Conv => HolSynRel::Conv,
    }
}

fn wit_sort(value: HolSort) -> nucleus::proof::host::Sort {
    match value {
        HolSort::Kind => nucleus::proof::host::Sort::Kind,
        HolSort::Ty => nucleus::proof::host::Sort::Ty,
        HolSort::Tm => nucleus::proof::host::Sort::Tm,
    }
}

fn checked_ref(value: Result<Ref, covalence_logic_hol::KernelError>) -> Result<u64, String> {
    value.map(ref_index).map_err(|error| error.to_string())
}

fn checked_fact(value: Result<SynFactId, covalence_logic_hol::KernelError>) -> Result<u64, String> {
    value.map(fact_index).map_err(|error| error.to_string())
}

impl nucleus::proof::host::HostKernel for ProofState {
    fn new(&mut self) -> wasmtime::Result<Resource<HostKernel>> {
        Ok(self.table.push(HostKernel(HolKernel::new()))?)
    }

    fn arena(&mut self, kernel: Resource<HostKernel>) -> wasmtime::Result<Resource<HostArena>> {
        let arena = self.table.get(&kernel)?.0.arena().clone();
        Ok(self.table.push(HostArena(arena))?)
    }

    fn address(&mut self, kernel: Resource<HostKernel>) -> wasmtime::Result<Vec<u8>> {
        Ok(self.table.get(&kernel)?.0.addr().as_ref().to_vec())
    }

    fn len(&mut self, kernel: Resource<HostKernel>) -> wasmtime::Result<u64> {
        u64_from_usize(self.table.get(&kernel)?.0.len(), "kernel length")
    }

    fn category(
        &mut self,
        kernel: Resource<HostKernel>,
        value: u64,
    ) -> wasmtime::Result<Result<nucleus::proof::host::Sort, String>> {
        Ok(reference(value).and_then(|value| {
            self.table
                .get(&kernel)
                .map_err(|error| error.to_string())?
                .0
                .category(value)
                .map(wit_sort)
                .map_err(|error| error.to_string())
        }))
    }

    fn classifier(
        &mut self,
        kernel: Resource<HostKernel>,
        value: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(reference(value).and_then(|value| {
            checked_ref(
                self.table
                    .get(&kernel)
                    .map_err(|error| error.to_string())?
                    .0
                    .classifier(value),
            )
        }))
    }

    fn find(
        &mut self,
        kernel: Resource<HostKernel>,
        value: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(reference(value).and_then(|value| {
            checked_ref(
                self.table
                    .get(&kernel)
                    .map_err(|error| error.to_string())?
                    .0
                    .find(value),
            )
        }))
    }

    fn find_mut(
        &mut self,
        kernel: Resource<HostKernel>,
        value: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(reference(value).and_then(|value| {
            checked_ref(
                self.table
                    .get_mut(&kernel)
                    .map_err(|error| error.to_string())?
                    .0
                    .find_mut(value),
            )
        }))
    }

    fn equivalent(
        &mut self,
        kernel: Resource<HostKernel>,
        left: u64,
        right: u64,
    ) -> wasmtime::Result<Result<bool, String>> {
        Ok(match (reference(left), reference(right)) {
            (Ok(left), Ok(right)) => self
                .table
                .get(&kernel)?
                .0
                .equivalent(left, right)
                .map_err(|error| error.to_string()),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn equivalent_mut(
        &mut self,
        kernel: Resource<HostKernel>,
        left: u64,
        right: u64,
    ) -> wasmtime::Result<Result<bool, String>> {
        Ok(match (reference(left), reference(right)) {
            (Ok(left), Ok(right)) => self
                .table
                .get_mut(&kernel)?
                .0
                .equivalent_mut(left, right)
                .map_err(|error| error.to_string()),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn kind_star(&mut self, kernel: Resource<HostKernel>) -> wasmtime::Result<Result<u64, String>> {
        Ok(checked_ref(self.table.get_mut(&kernel)?.0.star()))
    }

    fn kind_arr(
        &mut self,
        kernel: Resource<HostKernel>,
        domain: u64,
        codomain: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(domain), reference(codomain)) {
            (Ok(domain), Ok(codomain)) => {
                checked_ref(self.table.get_mut(&kernel)?.0.kind_arr(domain, codomain))
            }
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn bool_type(
        &mut self,
        kernel: Resource<HostKernel>,
        star: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let star = match reference(star) {
            Ok(star) => star,
            Err(error) => return Ok(Err(error)),
        };
        Ok(checked_ref(self.table.get_mut(&kernel)?.0.bool_ty(star)))
    }

    fn ty_arr(
        &mut self,
        kernel: Resource<HostKernel>,
        domain: u64,
        codomain: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(domain), reference(codomain)) {
            (Ok(domain), Ok(codomain)) => {
                checked_ref(self.table.get_mut(&kernel)?.0.ty_arr(domain, codomain))
            }
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn ty_app(
        &mut self,
        kernel: Resource<HostKernel>,
        function: u64,
        argument: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(function), reference(argument)) {
            (Ok(function), Ok(argument)) => {
                checked_ref(self.table.get_mut(&kernel)?.0.ty_app(function, argument))
            }
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn ty_lam(
        &mut self,
        kernel: Resource<HostKernel>,
        binder: u64,
        body: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(binder), reference(body)) {
            (Ok(binder), Ok(body)) => {
                checked_ref(self.table.get_mut(&kernel)?.0.ty_lam(binder, body))
            }
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn ty_fv(
        &mut self,
        kernel: Resource<HostKernel>,
        name: u64,
        kind: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let kind = match reference(kind) {
            Ok(kind) => kind,
            Err(error) => return Ok(Err(error)),
        };
        Ok(checked_ref(
            self.table.get_mut(&kernel)?.0.ty_fv(name, kind),
        ))
    }

    fn ty_exists(
        &mut self,
        kernel: Resource<HostKernel>,
        name: u64,
        predicate: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let predicate = match reference(predicate) {
            Ok(predicate) => predicate,
            Err(error) => return Ok(Err(error)),
        };
        Ok(checked_ref(
            self.table.get_mut(&kernel)?.0.ty_exists(name, predicate),
        ))
    }

    fn ty_forall(
        &mut self,
        kernel: Resource<HostKernel>,
        name: u64,
        predicate: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let predicate = match reference(predicate) {
            Ok(predicate) => predicate,
            Err(error) => return Ok(Err(error)),
        };
        Ok(checked_ref(
            self.table.get_mut(&kernel)?.0.ty_forall(name, predicate),
        ))
    }

    fn model(
        &mut self,
        kernel: Resource<HostKernel>,
        name: u64,
        predicate: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let predicate = match reference(predicate) {
            Ok(predicate) => predicate,
            Err(error) => return Ok(Err(error)),
        };
        Ok(checked_ref(
            self.table.get_mut(&kernel)?.0.model(name, predicate),
        ))
    }

    fn tm_fv(
        &mut self,
        kernel: Resource<HostKernel>,
        name: u64,
        ty: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let ty = match reference(ty) {
            Ok(ty) => ty,
            Err(error) => return Ok(Err(error)),
        };
        Ok(checked_ref(self.table.get_mut(&kernel)?.0.tm_fv(name, ty)))
    }

    fn app(
        &mut self,
        kernel: Resource<HostKernel>,
        function: u64,
        argument: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(function), reference(argument)) {
            (Ok(function), Ok(argument)) => {
                checked_ref(self.table.get_mut(&kernel)?.0.app(function, argument))
            }
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn lam(
        &mut self,
        kernel: Resource<HostKernel>,
        binder: u64,
        body: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(binder), reference(body)) {
            (Ok(binder), Ok(body)) => checked_ref(self.table.get_mut(&kernel)?.0.lam(binder, body)),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn bool_lit(
        &mut self,
        kernel: Resource<HostKernel>,
        bool_type: u64,
        value: bool,
    ) -> wasmtime::Result<Result<u64, String>> {
        let bool_type = match reference(bool_type) {
            Ok(bool_type) => bool_type,
            Err(error) => return Ok(Err(error)),
        };
        Ok(checked_ref(
            self.table.get_mut(&kernel)?.0.bool(bool_type, value),
        ))
    }

    fn tm_eq(
        &mut self,
        kernel: Resource<HostKernel>,
        bool_type: u64,
        left: u64,
        right: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(
            match (reference(bool_type), reference(left), reference(right)) {
                (Ok(bool_type), Ok(left), Ok(right)) => {
                    checked_ref(self.table.get_mut(&kernel)?.0.eq(bool_type, left, right))
                }
                (Err(error), _, _) | (_, Err(error), _) | (_, _, Err(error)) => Err(error),
            },
        )
    }

    fn eps(
        &mut self,
        kernel: Resource<HostKernel>,
        ty: u64,
        predicate: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(ty), reference(predicate)) {
            (Ok(ty), Ok(predicate)) => {
                checked_ref(self.table.get_mut(&kernel)?.0.eps(ty, predicate))
            }
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn import_arena(
        &mut self,
        kernel: Resource<HostKernel>,
        value: Resource<HostArena>,
    ) -> wasmtime::Result<Result<u64, String>> {
        let arena = self.table.get(&value)?.0.clone();
        Ok(self
            .table
            .get_mut(&kernel)?
            .0
            .import_literal(arena)
            .map(import_index)
            .map_err(|error| error.to_string()))
    }

    fn import_table(
        &mut self,
        kernel: Resource<HostKernel>,
        value: Resource<HostTable>,
    ) -> wasmtime::Result<Result<u64, String>> {
        let arena = self.table.get(&value)?.0.as_ref().clone();
        Ok(self
            .table
            .get_mut(&kernel)?
            .0
            .import_literal(arena)
            .map(import_index)
            .map_err(|error| error.to_string()))
    }

    fn import_link(
        &mut self,
        kernel: Resource<HostKernel>,
        value: Vec<u8>,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(link(value).and_then(|value| {
            self.table
                .get_mut(&kernel)
                .map_err(|error| error.to_string())?
                .0
                .import_link(value)
                .map(import_index)
                .map_err(|error| error.to_string())
        }))
    }

    fn kind_ref(
        &mut self,
        kernel: Resource<HostKernel>,
        source: u64,
        foreign: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let parsed = import_id(source).and_then(|source| Ok((source, reference(foreign)?)));
        let (table, cas) = (&mut self.table, &self.cas);
        Ok(match parsed {
            Ok((source, foreign)) => {
                let mut resolver = CasResolver(cas);
                table
                    .get_mut(&kernel)?
                    .0
                    .kind_ref(&mut resolver, source, foreign)
                    .map(ref_index)
                    .map_err(|error| error.to_string())
            }
            Err(error) => Err(error),
        })
    }

    fn ty_ref(
        &mut self,
        kernel: Resource<HostKernel>,
        source: u64,
        foreign: u64,
        kind: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let parsed = (|| Ok((import_id(source)?, reference(foreign)?, reference(kind)?)))();
        let (table, cas) = (&mut self.table, &self.cas);
        Ok(match parsed {
            Ok((source, foreign, kind)) => {
                let mut resolver = CasResolver(cas);
                table
                    .get_mut(&kernel)?
                    .0
                    .ty_ref(&mut resolver, source, foreign, kind)
                    .map(ref_index)
                    .map_err(|error| error.to_string())
            }
            Err(error) => Err(error),
        })
    }

    fn tm_ref(
        &mut self,
        kernel: Resource<HostKernel>,
        source: u64,
        foreign: u64,
        ty: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let parsed = (|| Ok((import_id(source)?, reference(foreign)?, reference(ty)?)))();
        let (table, cas) = (&mut self.table, &self.cas);
        Ok(match parsed {
            Ok((source, foreign, ty)) => {
                let mut resolver = CasResolver(cas);
                table
                    .get_mut(&kernel)?
                    .0
                    .tm_ref(&mut resolver, source, foreign, ty)
                    .map(ref_index)
                    .map_err(|error| error.to_string())
            }
            Err(error) => Err(error),
        })
    }

    fn add_context(
        &mut self,
        kernel: Resource<HostKernel>,
        proposition: u64,
    ) -> wasmtime::Result<Result<(), String>> {
        Ok(reference(proposition).and_then(|proposition| {
            self.table
                .get_mut(&kernel)
                .map_err(|error| error.to_string())?
                .0
                .add_context(proposition)
                .map_err(|error| error.to_string())
        }))
    }

    fn add_axiom(
        &mut self,
        kernel: Resource<HostKernel>,
        name: String,
    ) -> wasmtime::Result<Result<(), String>> {
        Ok(self
            .table
            .get_mut(&kernel)?
            .0
            .add_axiom(&name)
            .map_err(|error| error.to_string()))
    }

    fn not_tm(
        &mut self,
        kernel: Resource<HostKernel>,
        bool_type: u64,
        proposition: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(bool_type), reference(proposition)) {
            (Ok(bool_type), Ok(proposition)) => checked_ref(
                self.table
                    .get_mut(&kernel)?
                    .0
                    .not_tm(bool_type, proposition),
            ),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn forall_tm(
        &mut self,
        kernel: Resource<HostKernel>,
        bool_type: u64,
        binder: u64,
        body: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(
            match (reference(bool_type), reference(binder), reference(body)) {
                (Ok(bool_type), Ok(binder), Ok(body)) => checked_ref(
                    self.table
                        .get_mut(&kernel)?
                        .0
                        .forall_tm(bool_type, binder, body),
                ),
                (Err(error), _, _) | (_, Err(error), _) | (_, _, Err(error)) => Err(error),
            },
        )
    }

    fn exists_tm(
        &mut self,
        kernel: Resource<HostKernel>,
        binder: u64,
        body: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(binder), reference(body)) {
            (Ok(binder), Ok(body)) => {
                checked_ref(self.table.get_mut(&kernel)?.0.exists_tm(binder, body))
            }
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn and_tm(
        &mut self,
        kernel: Resource<HostKernel>,
        bool_type: u64,
        binder: u64,
        left: u64,
        right: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match binary_logic(bool_type, binder, left, right) {
            Ok((bool_type, binder, left, right)) => checked_ref(
                self.table
                    .get_mut(&kernel)?
                    .0
                    .and_tm(bool_type, binder, left, right),
            ),
            Err(error) => Err(error),
        })
    }

    fn or_tm(
        &mut self,
        kernel: Resource<HostKernel>,
        bool_type: u64,
        binder: u64,
        left: u64,
        right: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match binary_logic(bool_type, binder, left, right) {
            Ok((bool_type, binder, left, right)) => checked_ref(
                self.table
                    .get_mut(&kernel)?
                    .0
                    .or_tm(bool_type, binder, left, right),
            ),
            Err(error) => Err(error),
        })
    }

    fn imp_tm(
        &mut self,
        kernel: Resource<HostKernel>,
        bool_type: u64,
        binder: u64,
        left: u64,
        right: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match binary_logic(bool_type, binder, left, right) {
            Ok((bool_type, binder, left, right)) => checked_ref(
                self.table
                    .get_mut(&kernel)?
                    .0
                    .imp_tm(bool_type, binder, left, right),
            ),
            Err(error) => Err(error),
        })
    }

    fn fresh_name(
        &mut self,
        kernel: Resource<HostKernel>,
        roots: Vec<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        let mut resolved = Vec::with_capacity(roots.len());
        for root in roots {
            match reference(root) {
                Ok(root) => resolved.push(root),
                Err(error) => return Ok(Err(error)),
            }
        }
        Ok(self
            .table
            .get(&kernel)?
            .0
            .fresh_name(&resolved)
            .map_err(|error| error.to_string()))
    }

    fn model_spec(
        &mut self,
        kernel: Resource<HostKernel>,
        theorem: u64,
        substitution: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (theorem_id(theorem), fact_id(substitution)) {
            (Ok(theorem), Ok(substitution)) => self
                .table
                .get_mut(&kernel)?
                .0
                .model_spec(theorem, substitution)
                .map(|id| id.get().unsigned_abs().into())
                .map_err(|error| error.to_string()),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn refl(
        &mut self,
        kernel: Resource<HostKernel>,
        bool_ty: u64,
        term: u64,
    ) -> wasmtime::Result<Result<nucleus::proof::host::ReflThm, String>> {
        Ok(match (reference(bool_ty), reference(term)) {
            (Ok(bool_ty), Ok(term)) => self
                .table
                .get_mut(&kernel)?
                .0
                .refl(bool_ty, term)
                .map(|result| nucleus::proof::host::ReflThm {
                    equality: u64::from(result.equality.get().unsigned_abs()),
                    theorem: u64::from(result.theorem.get().unsigned_abs()),
                })
                .map_err(|error| error.to_string()),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn ap_thm(
        &mut self,
        kernel: Resource<HostKernel>,
        theorem: u64,
        argument: u64,
    ) -> wasmtime::Result<Result<nucleus::proof::host::ApThm, String>> {
        Ok(match (theorem_id(theorem), reference(argument)) {
            (Ok(theorem), Ok(argument)) => self
                .table
                .get_mut(&kernel)?
                .0
                .ap_thm(theorem, argument)
                .map(|result| nucleus::proof::host::ApThm {
                    left: u64::from(result.left.get().unsigned_abs()),
                    right: u64::from(result.right.get().unsigned_abs()),
                    equality: u64::from(result.equality.get().unsigned_abs()),
                    theorem: u64::from(result.theorem.get().unsigned_abs()),
                })
                .map_err(|error| error.to_string()),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn ap_term(
        &mut self,
        kernel: Resource<HostKernel>,
        theorem: u64,
        function: u64,
    ) -> wasmtime::Result<Result<nucleus::proof::host::ApThm, String>> {
        Ok(match (theorem_id(theorem), reference(function)) {
            (Ok(theorem), Ok(function)) => self
                .table
                .get_mut(&kernel)?
                .0
                .ap_term(theorem, function)
                .map(|result| nucleus::proof::host::ApThm {
                    left: u64::from(result.left.get().unsigned_abs()),
                    right: u64::from(result.right.get().unsigned_abs()),
                    equality: u64::from(result.equality.get().unsigned_abs()),
                    theorem: u64::from(result.theorem.get().unsigned_abs()),
                })
                .map_err(|error| error.to_string()),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn eq_mp(
        &mut self,
        kernel: Resource<HostKernel>,
        equality: u64,
        premise: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (theorem_id(equality), theorem_id(premise)) {
            (Ok(equality), Ok(premise)) => self
                .table
                .get_mut(&kernel)?
                .0
                .eq_mp(equality, premise)
                .map(|id| u64::from(id.get().unsigned_abs()))
                .map_err(|error| error.to_string()),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn forall_intro(
        &mut self,
        kernel: Resource<HostKernel>,
        theorem: u64,
        binder: u64,
    ) -> wasmtime::Result<Result<nucleus::proof::host::ForallThm, String>> {
        Ok(match (theorem_id(theorem), reference(binder)) {
            (Ok(theorem), Ok(binder)) => self
                .table
                .get_mut(&kernel)?
                .0
                .forall_intro(theorem, binder)
                .map(|result| nucleus::proof::host::ForallThm {
                    universal: u64::from(result.universal.get().unsigned_abs()),
                    theorem: u64::from(result.theorem.get().unsigned_abs()),
                })
                .map_err(|error| error.to_string()),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn forall_intro_at(
        &mut self,
        kernel: Resource<HostKernel>,
        theorem: u64,
        binder: u64,
        universal: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        let (theorem, binder, universal) =
            match (theorem_id(theorem), reference(binder), reference(universal)) {
                (Ok(theorem), Ok(binder), Ok(universal)) => (theorem, binder, universal),
                (Err(error), _, _) | (_, Err(error), _) | (_, _, Err(error)) => {
                    return Ok(Err(error));
                }
            };
        Ok(self
            .table
            .get_mut(&kernel)?
            .0
            .forall_intro_at(theorem, binder, universal)
            .map(|id| u64::from(id.get().unsigned_abs()))
            .map_err(|error| error.to_string()))
    }

    fn choice_intro(
        &mut self,
        kernel: Resource<HostKernel>,
        theorem: u64,
    ) -> wasmtime::Result<Result<nucleus::proof::host::ChoiceThm, String>> {
        Ok(match theorem_id(theorem) {
            Ok(theorem) => self
                .table
                .get_mut(&kernel)?
                .0
                .choice_intro(theorem)
                .map(|result| nucleus::proof::host::ChoiceThm {
                    witness: u64::from(result.witness.get().unsigned_abs()),
                    proposition: u64::from(result.proposition.get().unsigned_abs()),
                    theorem: u64::from(result.theorem.get().unsigned_abs()),
                })
                .map_err(|error| error.to_string()),
            Err(error) => Err(error),
        })
    }

    fn choice_intro_at(
        &mut self,
        kernel: Resource<HostKernel>,
        theorem: u64,
        target: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (theorem_id(theorem), reference(target)) {
            (Ok(theorem), Ok(target)) => self
                .table
                .get_mut(&kernel)?
                .0
                .choice_intro_at(theorem, target)
                .map(|id| u64::from(id.get().unsigned_abs()))
                .map_err(|error| error.to_string()),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn convert_theorem(
        &mut self,
        kernel: Resource<HostKernel>,
        theorem: u64,
        source: u64,
        target: u64,
    ) -> wasmtime::Result<Result<(), String>> {
        let (theorem, source, target) =
            match (theorem_id(theorem), reference(source), reference(target)) {
                (Ok(theorem), Ok(source), Ok(target)) => (theorem, source, target),
                (Err(error), _, _) | (_, Err(error), _) | (_, _, Err(error)) => {
                    return Ok(Err(error));
                }
            };
        Ok(self
            .table
            .get_mut(&kernel)?
            .0
            .convert_theorem(theorem, source, target)
            .map_err(|error| error.to_string()))
    }

    fn convert_conclusions(
        &mut self,
        kernel: Resource<HostKernel>,
        theorem: u64,
        source: u64,
        target: u64,
    ) -> wasmtime::Result<Result<(), String>> {
        let (theorem, source, target) =
            match (theorem_id(theorem), reference(source), reference(target)) {
                (Ok(theorem), Ok(source), Ok(target)) => (theorem, source, target),
                (Err(error), _, _) | (_, Err(error), _) | (_, _, Err(error)) => {
                    return Ok(Err(error));
                }
            };
        Ok(self
            .table
            .get_mut(&kernel)?
            .0
            .convert_conclusions(theorem, source, target)
            .map_err(|error| error.to_string()))
    }

    fn contract_theorem(
        &mut self,
        kernel: Resource<HostKernel>,
        theorem: u64,
    ) -> wasmtime::Result<Result<(), String>> {
        Ok(match theorem_id(theorem) {
            Ok(theorem) => self
                .table
                .get_mut(&kernel)?
                .0
                .contract_theorem(theorem)
                .map_err(|error| error.to_string()),
            Err(error) => Err(error),
        })
    }

    fn eqt_elim(
        &mut self,
        kernel: Resource<HostKernel>,
        theorem: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match theorem_id(theorem) {
            Ok(theorem) => self
                .table
                .get_mut(&kernel)?
                .0
                .eqt_elim(theorem)
                .map(|id| u64::from(id.get().unsigned_abs()))
                .map_err(|error| error.to_string()),
            Err(error) => Err(error),
        })
    }

    fn deduct_antisym(
        &mut self,
        kernel: Resource<HostKernel>,
        bool_type: u64,
        p: u64,
        q: u64,
        left: u64,
        right: u64,
    ) -> wasmtime::Result<Result<nucleus::proof::host::AntisymmThm, String>> {
        let (bool_type, p, q, left, right) = match (
            reference(bool_type),
            reference(p),
            reference(q),
            theorem_id(left),
            theorem_id(right),
        ) {
            (Ok(bool_type), Ok(p), Ok(q), Ok(left), Ok(right)) => (bool_type, p, q, left, right),
            (Err(error), _, _, _, _)
            | (_, Err(error), _, _, _)
            | (_, _, Err(error), _, _)
            | (_, _, _, Err(error), _)
            | (_, _, _, _, Err(error)) => {
                return Ok(Err(error));
            }
        };
        Ok(self
            .table
            .get_mut(&kernel)?
            .0
            .deduct_antisym(bool_type, p, q, left, right)
            .map(|result| nucleus::proof::host::AntisymmThm {
                equality: u64_from_ref(result.equality),
                theorem: u64::from(result.theorem.get().unsigned_abs()),
            })
            .map_err(|error| error.to_string()))
    }

    fn inf_exists(
        &mut self,
        kernel: Resource<HostKernel>,
        bool_type: u64,
    ) -> wasmtime::Result<Result<nucleus::proof::host::InfinityAxiom, String>> {
        let bool_type = match reference(bool_type) {
            Ok(bool_type) => bool_type,
            Err(error) => return Ok(Err(error)),
        };
        Ok(self
            .table
            .get_mut(&kernel)?
            .0
            .inf_exists(bool_type)
            .map_err(|error| error.to_string())
            .map(infinity_axiom))
    }

    fn sub_exists(
        &mut self,
        kernel: Resource<HostKernel>,
        bool_type: u64,
        carrier: u64,
        predicate: u64,
    ) -> wasmtime::Result<Result<nucleus::proof::host::SubtypeAxiom, String>> {
        let (bool_type, carrier, predicate) = match (
            reference(bool_type),
            reference(carrier),
            reference(predicate),
        ) {
            (Ok(bool_type), Ok(carrier), Ok(predicate)) => (bool_type, carrier, predicate),
            (Err(error), _, _) | (_, Err(error), _) | (_, _, Err(error)) => {
                return Ok(Err(error));
            }
        };
        Ok(self
            .table
            .get_mut(&kernel)?
            .0
            .sub_exists(bool_type, carrier, predicate)
            .map_err(|error| error.to_string())
            .map(subtype_axiom))
    }

    fn syn_fact_count(&mut self, kernel: Resource<HostKernel>) -> wasmtime::Result<u64> {
        u64_from_usize(
            self.table.get(&kernel)?.0.syn_fact_len(),
            "syntactic-fact count",
        )
    }

    fn remove_syn_fact(
        &mut self,
        kernel: Resource<HostKernel>,
        fact: u64,
    ) -> wasmtime::Result<bool> {
        let Ok(fact) = fact_id(fact) else {
            return Ok(false);
        };
        Ok(self.table.get_mut(&kernel)?.0.remove_syn_fact(fact))
    }

    fn truncate_syn_facts(
        &mut self,
        kernel: Resource<HostKernel>,
        len: u64,
    ) -> wasmtime::Result<Result<(), String>> {
        let len = match usize_from_u64(len, "syntactic-fact count") {
            Ok(len) => len,
            Err(error) => return Ok(Err(error)),
        };
        self.table.get_mut(&kernel)?.0.truncate_syn_facts(len);
        Ok(Ok(()))
    }

    fn syn_refl(
        &mut self,
        kernel: Resource<HostKernel>,
        relation: nucleus::proof::host::SynRel,
        input: u64,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(input), optional_fact_id(target)) {
            (Ok(input), Ok(target)) => checked_fact(self.table.get_mut(&kernel)?.0.syn_refl(
                target,
                syn_relation(relation),
                input,
            )),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn syn_refine(
        &mut self,
        kernel: Resource<HostKernel>,
        fact: u64,
        relation: nucleus::proof::host::SynRel,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (fact_id(fact), optional_fact_id(target)) {
            (Ok(fact), Ok(target)) => checked_fact(self.table.get_mut(&kernel)?.0.syn_refine(
                target,
                fact,
                syn_relation(relation),
            )),
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn syn_symm(
        &mut self,
        kernel: Resource<HostKernel>,
        fact: u64,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (fact_id(fact), optional_fact_id(target)) {
            (Ok(fact), Ok(target)) => {
                checked_fact(self.table.get_mut(&kernel)?.0.syn_symm(target, fact))
            }
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn syn_trans(
        &mut self,
        kernel: Resource<HostKernel>,
        left: u64,
        right: u64,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(
            match (fact_id(left), fact_id(right), optional_fact_id(target)) {
                (Ok(left), Ok(right), Ok(target)) => checked_fact(
                    self.table
                        .get_mut(&kernel)?
                        .0
                        .syn_trans(target, left, right),
                ),
                (Err(error), _, _) | (_, Err(error), _) | (_, _, Err(error)) => Err(error),
            },
        )
    }

    fn syn_sub_var(
        &mut self,
        kernel: Resource<HostKernel>,
        var: u64,
        val: u64,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(
            match (reference(var), reference(val), optional_fact_id(target)) {
                (Ok(var), Ok(val), Ok(target)) => {
                    checked_fact(self.table.get_mut(&kernel)?.0.syn_sub_var(target, var, val))
                }
                (Err(error), _, _) | (_, Err(error), _) | (_, _, Err(error)) => Err(error),
            },
        )
    }

    fn syn_sub_leaf(
        &mut self,
        kernel: Resource<HostKernel>,
        var: u64,
        val: u64,
        input: u64,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(
            match (
                reference(var),
                reference(val),
                reference(input),
                optional_fact_id(target),
            ) {
                (Ok(var), Ok(val), Ok(input), Ok(target)) => checked_fact(
                    self.table
                        .get_mut(&kernel)?
                        .0
                        .syn_sub_leaf(target, var, val, input),
                ),
                (Err(error), _, _, _)
                | (_, Err(error), _, _)
                | (_, _, Err(error), _)
                | (_, _, _, Err(error)) => Err(error),
            },
        )
    }

    fn syn_sub_leaf_forall(
        &mut self,
        kernel: Resource<HostKernel>,
        var: u64,
        input: u64,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(
            match (reference(var), reference(input), optional_fact_id(target)) {
                (Ok(var), Ok(input), Ok(target)) => checked_fact(
                    self.table
                        .get_mut(&kernel)?
                        .0
                        .syn_sub_leaf_forall(target, var, input),
                ),
                (Err(error), _, _) | (_, Err(error), _) | (_, _, Err(error)) => Err(error),
            },
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn syn_sub_identity(
        &mut self,
        kernel: Resource<HostKernel>,
        var: u64,
        val: u64,
        input: u64,
        output: u64,
        variable_equality: u64,
        body_equality: u64,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        let parsed = (|| {
            Ok((
                reference(var)?,
                reference(val)?,
                reference(input)?,
                reference(output)?,
                fact_id(variable_equality)?,
                fact_id(body_equality)?,
                optional_fact_id(target)?,
            ))
        })();
        Ok(match parsed {
            Ok((var, val, input, output, variable_equality, body_equality, target)) => {
                checked_fact(self.table.get_mut(&kernel)?.0.syn_sub_identity(
                    target,
                    var,
                    val,
                    input,
                    output,
                    variable_equality,
                    body_equality,
                ))
            }
            Err(error) => Err(error),
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn syn_congr(
        &mut self,
        kernel: Resource<HostKernel>,
        relation: nucleus::proof::host::SynRel,
        var: Option<u64>,
        val: Option<u64>,
        input: u64,
        output: u64,
        children: Vec<u64>,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        let parsed = (|| {
            let var = var.map(reference).transpose()?;
            let val = val.map(reference).transpose()?;
            let input = reference(input)?;
            let output = reference(output)?;
            let children = children
                .into_iter()
                .map(fact_id)
                .collect::<Result<Vec<_>, _>>()?;
            let target = optional_fact_id(target)?;
            Ok((var, val, input, output, children, target))
        })();
        Ok(match parsed {
            Ok((var, val, input, output, children, target)) => {
                checked_fact(self.table.get_mut(&kernel)?.0.syn_congr(
                    target,
                    syn_relation(relation),
                    var,
                    val,
                    input,
                    output,
                    &children,
                ))
            }
            Err(error) => Err(error),
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn syn_binder_congr(
        &mut self,
        kernel: Resource<HostKernel>,
        relation: nucleus::proof::host::SynRel,
        var: Option<u64>,
        val: Option<u64>,
        input: u64,
        output: u64,
        binder: u64,
        body: u64,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        let parsed = (|| {
            Ok((
                var.map(reference).transpose()?,
                val.map(reference).transpose()?,
                reference(input)?,
                reference(output)?,
                fact_id(binder)?,
                fact_id(body)?,
                optional_fact_id(target)?,
            ))
        })();
        Ok(match parsed {
            Ok((var, val, input, output, binder, body, target)) => {
                checked_fact(self.table.get_mut(&kernel)?.0.syn_binder_congr(
                    target,
                    syn_relation(relation),
                    var,
                    val,
                    input,
                    output,
                    binder,
                    body,
                ))
            }
            Err(error) => Err(error),
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn syn_implicit_binder_congr(
        &mut self,
        kernel: Resource<HostKernel>,
        relation: nucleus::proof::host::SynRel,
        var: Option<u64>,
        val: Option<u64>,
        input: u64,
        output: u64,
        binder: u64,
        body: u64,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        let parsed = (|| {
            Ok((
                var.map(reference).transpose()?,
                val.map(reference).transpose()?,
                reference(input)?,
                reference(output)?,
                reference(binder)?,
                fact_id(body)?,
                optional_fact_id(target)?,
            ))
        })();
        Ok(match parsed {
            Ok((var, val, input, output, binder, body, target)) => {
                checked_fact(self.table.get_mut(&kernel)?.0.syn_implicit_binder_congr(
                    target,
                    syn_relation(relation),
                    var,
                    val,
                    input,
                    output,
                    binder,
                    body,
                ))
            }
            Err(error) => Err(error),
        })
    }

    fn syn_alpha_binder(
        &mut self,
        kernel: Resource<HostKernel>,
        input: u64,
        output: u64,
        binder_classifier: u64,
        body_substitution: u64,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        let parsed = (|| {
            Ok((
                reference(input)?,
                reference(output)?,
                fact_id(binder_classifier)?,
                fact_id(body_substitution)?,
                optional_fact_id(target)?,
            ))
        })();
        Ok(match parsed {
            Ok((input, output, binder_classifier, body_substitution, target)) => {
                checked_fact(self.table.get_mut(&kernel)?.0.syn_alpha_binder(
                    target,
                    input,
                    output,
                    binder_classifier,
                    body_substitution,
                ))
            }
            Err(error) => Err(error),
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn syn_alpha_implicit_binder(
        &mut self,
        kernel: Resource<HostKernel>,
        input: u64,
        output: u64,
        input_binder: u64,
        output_binder: u64,
        body_substitution: u64,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        let parsed = (|| {
            Ok((
                reference(input)?,
                reference(output)?,
                reference(input_binder)?,
                reference(output_binder)?,
                fact_id(body_substitution)?,
                optional_fact_id(target)?,
            ))
        })();
        Ok(match parsed {
            Ok((input, output, input_binder, output_binder, body_substitution, target)) => {
                checked_fact(self.table.get_mut(&kernel)?.0.syn_alpha_implicit_binder(
                    target,
                    input,
                    output,
                    input_binder,
                    output_binder,
                    body_substitution,
                ))
            }
            Err(error) => Err(error),
        })
    }

    fn tm_beta(
        &mut self,
        kernel: Resource<HostKernel>,
        source: u64,
        substitution: u64,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(
            match (
                reference(source),
                fact_id(substitution),
                optional_fact_id(target),
            ) {
                (Ok(source), Ok(substitution), Ok(target)) => checked_fact(
                    self.table
                        .get_mut(&kernel)?
                        .0
                        .tm_beta_fact(target, source, substitution),
                ),
                (Err(error), _, _) | (_, Err(error), _) | (_, _, Err(error)) => Err(error),
            },
        )
    }

    fn ty_beta(
        &mut self,
        kernel: Resource<HostKernel>,
        source: u64,
        substitution: u64,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(
            match (
                reference(source),
                fact_id(substitution),
                optional_fact_id(target),
            ) {
                (Ok(source), Ok(substitution), Ok(target)) => checked_fact(
                    self.table
                        .get_mut(&kernel)?
                        .0
                        .ty_beta_fact(target, source, substitution),
                ),
                (Err(error), _, _) | (_, Err(error), _) | (_, _, Err(error)) => Err(error),
            },
        )
    }

    fn tm_eta(
        &mut self,
        kernel: Resource<HostKernel>,
        source: u64,
        target: Option<u64>,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok(match (reference(source), optional_fact_id(target)) {
            (Ok(source), Ok(target)) => {
                checked_fact(self.table.get_mut(&kernel)?.0.tm_eta_fact(target, source))
            }
            (Err(error), _) | (_, Err(error)) => Err(error),
        })
    }

    fn union_syn_fact(
        &mut self,
        kernel: Resource<HostKernel>,
        fact: u64,
    ) -> wasmtime::Result<Result<(), String>> {
        Ok(fact_id(fact).and_then(|fact| {
            self.table
                .get_mut(&kernel)
                .map_err(|error| error.to_string())?
                .0
                .union_syn_fact(fact)
                .map_err(|error| error.to_string())
        }))
    }

    fn drop(&mut self, kernel: Resource<HostKernel>) -> wasmtime::Result<()> {
        self.table.delete(kernel)?;
        Ok(())
    }
}

impl nucleus::proof::host::Host for ProofState {
    fn cas_insert(&mut self, value: Resource<HostBlob>) -> wasmtime::Result<u64> {
        let fact = self.table.get(&value)?.0.clone();
        Ok(self.cas.insert_fact(fact))
    }

    fn cas_put(&mut self, value: Resource<HostBytes>) -> wasmtime::Result<u64> {
        let bytes = self.table.get(&value)?.0.clone();
        Ok(self.cas.insert(bytes))
    }

    fn cas_get(&mut self, object: u64) -> wasmtime::Result<Option<Resource<HostBlob>>> {
        let fact = self.cas.fact(object).cloned();
        fact.map(|fact| self.table.push(HostBlob(fact)))
            .transpose()
            .map_err(Into::into)
    }

    fn cas_find(&mut self, value: Vec<u8>) -> wasmtime::Result<Result<Option<u64>, String>> {
        Ok(address(value).map(|address| self.cas.id(address)))
    }
}

impl nucleus::proof::host::HostWithStore<ProofState> for ProofState {
    async fn cas_get_bytes(
        accessor: &Accessor<ProofState, Self>,
        value: Vec<u8>,
    ) -> wasmtime::Result<Result<Option<Resource<HostBytes>>, String>> {
        let address = match address(value) {
            Ok(address) => address,
            Err(error) => return Ok(Err(error)),
        };
        let (resident, provider) = accessor.with(|mut access| {
            let state = access.get();
            (
                state.cas.fact_at(address).map(|fact| fact.bytes().clone()),
                state.provider.clone(),
            )
        });
        let bytes = if resident.is_some() {
            resident
        } else if let Some(provider) = provider {
            match provider.get_bytes(address).await {
                Ok(bytes) => bytes,
                Err(error) => return Ok(Err(error.to_string())),
            }
        } else {
            yield_once().await;
            None
        };
        accessor.with(|mut access| {
            let state = access.get();
            Ok(match bytes {
                Some(bytes) => state
                    .table
                    .push(HostBytes(bytes))
                    .map(Some)
                    .map_err(|error| error.to_string()),
                None => Ok(None),
            })
        })
    }

    async fn cas_get_fact(
        accessor: &Accessor<ProofState, Self>,
        value: Vec<u8>,
    ) -> wasmtime::Result<Result<Option<Resource<HostBlob>>, String>> {
        let address = match address(value) {
            Ok(address) => address,
            Err(error) => return Ok(Err(error)),
        };
        let (resident, provider) = accessor.with(|mut access| {
            let state = access.get();
            (state.cas.fact_at(address).cloned(), state.provider.clone())
        });
        let fact = if resident.is_some() {
            resident
        } else if let Some(provider) = provider {
            match get_exact_fact(provider.as_ref(), address).await {
                Ok(fact) => fact,
                Err(error) => return Ok(Err(error.to_string())),
            }
        } else {
            yield_once().await;
            None
        };
        accessor.with(|mut access| {
            let state = access.get();
            Ok(match fact {
                Some(fact) => state
                    .table
                    .push(HostBlob(fact))
                    .map(Some)
                    .map_err(|error| error.to_string()),
                None => Ok(None),
            })
        })
    }
}

impl nucleus::proof::capabilities::Host for ProofState {
    fn random_bytes(&mut self, len: u64) -> wasmtime::Result<Result<Resource<HostBytes>, String>> {
        const MAX_RANDOM_BYTES: usize = 1 << 20;
        let Ok(len) = usize::try_from(len) else {
            return Ok(Err(
                "random byte length does not fit in host memory".to_owned()
            ));
        };
        if len > MAX_RANDOM_BYTES {
            return Ok(Err(format!(
                "random byte request exceeds the {MAX_RANDOM_BYTES}-byte runtime limit"
            )));
        }
        let mut bytes = Vec::new();
        if bytes.try_reserve_exact(len).is_err() {
            return Ok(Err("random byte allocation failed".to_owned()));
        }
        bytes.resize(len, 0);
        covalence_lib_rand::fill(bytes.as_mut_slice());
        Ok(self
            .table
            .push(HostBytes(Bytes::from(bytes)))
            .map_err(|error| error.to_string()))
    }
}

impl nucleus::proof::tactics::Host for ProofState {
    fn iterate_unary(
        &mut self,
        kernel: Resource<HostKernel>,
        zero: u64,
        successor: u64,
        count: u64,
    ) -> wasmtime::Result<Result<u64, String>> {
        Ok((|| {
            let result = crate::tactics::iterate_unary(
                &mut self
                    .table
                    .get_mut(&kernel)
                    .map_err(|error| error.to_string())?
                    .0,
                reference(zero)?,
                reference(successor)?,
                count,
            )
            .map_err(|error| error.to_string())?;
            Ok(u64_from_ref(result))
        })())
    }

    fn rewrite_proposition(
        &mut self,
        kernel: Resource<HostKernel>,
        bool_type: u64,
        equality: u64,
        premise: u64,
        direction: nucleus::proof::tactics::RewriteDirection,
    ) -> wasmtime::Result<Result<nucleus::proof::tactics::RewriteResult, String>> {
        let direction = match direction {
            nucleus::proof::tactics::RewriteDirection::Forward => {
                crate::tactics::RewriteDirection::Forward
            }
            nucleus::proof::tactics::RewriteDirection::Backward => {
                crate::tactics::RewriteDirection::Backward
            }
        };
        Ok((|| {
            let result = crate::tactics::rewrite_proposition(
                &mut self
                    .table
                    .get_mut(&kernel)
                    .map_err(|error| error.to_string())?
                    .0,
                reference(bool_type)?,
                theorem_id(equality)?,
                theorem_id(premise)?,
                direction,
            )
            .map_err(|error| error.to_string())?;
            Ok(nucleus::proof::tactics::RewriteResult {
                source: u64_from_ref(result.source()),
                target: u64_from_ref(result.target()),
                theorem: u64::from(result.theorem().get().unsigned_abs()),
            })
        })())
    }
}

/// Failure to load or execute a standard proof component.
#[derive(Debug, Snafu)]
#[snafu(crate_root(covalence_lib_error::snafu))]
pub enum ProofError {
    /// The component could not be compiled, linked, instantiated, or called.
    #[snafu(display("proof component failed: {source}"))]
    Component {
        /// Wasmtime failure.
        source: wasmtime::Error,
    },
    /// The component ran successfully but rejected its own proof.
    #[snafu(display("proof component returned an error: {message}"))]
    Guest {
        /// Component-provided diagnostic.
        message: String,
    },
    /// A CAS failed while loading a content-addressed proof component.
    #[snafu(display("could not load proof component from CAS: {source}"))]
    Cas {
        /// Provider or content-validation failure.
        source: AsyncCasError,
    },
    /// The requested proof component address was absent from its CAS.
    #[snafu(display("proof component {address} is absent from the CAS"))]
    MissingComponent {
        /// Requested component address.
        address: O256,
    },
}

/// A live, reusable instance of the portable `nucleus:proof/proof` world.
pub struct Strategy {
    store: wasmtime::Store<ProofState>,
    proof: Proof,
}

impl Strategy {
    /// Compiles and instantiates component bytes without an external CAS.
    ///
    /// # Errors
    ///
    /// Returns [`ProofError::Component`] if compilation, linking, or
    /// instantiation fails.
    pub fn from_bytes(component: &[u8]) -> Result<Self, ProofError> {
        futures::executor::block_on(Self::from_bytes_async(component, None))
    }

    /// Compiles and instantiates component bytes with a runtime CAS provider.
    ///
    /// # Errors
    ///
    /// Returns [`ProofError::Component`] if compilation, linking, or
    /// instantiation fails.
    pub fn from_bytes_with_cas(
        component: &[u8],
        provider: Arc<dyn AsyncCas>,
    ) -> Result<Self, ProofError> {
        futures::executor::block_on(Self::from_bytes_async(component, Some(provider)))
    }

    /// Compiles and instantiates component bytes with an optional runtime CAS.
    ///
    /// # Errors
    ///
    /// Returns [`ProofError::Component`] if compilation, linking, or
    /// instantiation fails.
    pub async fn from_bytes_async(
        component: &[u8],
        provider: Option<Arc<dyn AsyncCas>>,
    ) -> Result<Self, ProofError> {
        let state = provider.map_or_else(ProofState::default, ProofState::with_provider);
        let mut config = wasmtime::Config::new();
        config.wasm_component_model(true);
        config.wasm_component_model_async(true);
        config.concurrency_support(true);
        let engine =
            wasmtime::Engine::new(&config).map_err(|source| ProofError::Component { source })?;
        let component = wasmtime::component::Component::new(&engine, component)
            .map_err(|source| ProofError::Component { source })?;
        let mut linker = wasmtime::component::Linker::new(&engine);
        Proof::add_to_linker::<ProofState, ProofState>(&mut linker, |state| state)
            .map_err(|source| ProofError::Component { source })?;
        let mut store = wasmtime::Store::new(&engine, state);
        let proof = Proof::instantiate_async(&mut store, &component, &linker)
            .await
            .map_err(|source| ProofError::Component { source })?;
        Ok(Self { store, proof })
    }

    /// Loads, validates, compiles, and instantiates a component from `provider`.
    ///
    /// # Errors
    ///
    /// Returns [`ProofError::Cas`] for provider or address-validation failures,
    /// [`ProofError::MissingComponent`] when absent, and
    /// [`ProofError::Component`] for component failures.
    pub async fn from_address_async(
        address: O256,
        provider: Arc<dyn AsyncCas>,
    ) -> Result<Self, ProofError> {
        let fact = get_exact_fact(provider.as_ref(), address)
            .await
            .map_err(|source| ProofError::Cas { source })?
            .ok_or(ProofError::MissingComponent { address })?;
        Self::from_bytes_async(fact.bytes(), Some(provider)).await
    }

    /// Loads and instantiates a content-addressed component from `provider`.
    ///
    /// # Errors
    ///
    /// Returns the same failures as [`Self::from_address_async`].
    pub fn from_address(address: O256, provider: Arc<dyn AsyncCas>) -> Result<Self, ProofError> {
        futures::executor::block_on(Self::from_address_async(address, provider))
    }

    fn insert_kernel(
        &mut self,
        kernel: Option<HolKernel>,
    ) -> Result<Option<Resource<HostKernel>>, ProofError> {
        kernel
            .map(|kernel| self.store.data_mut().table.push(HostKernel(kernel)))
            .transpose()
            .map_err(|source| ProofError::Component {
                source: source.into(),
            })
    }

    fn remove_kernel(
        &mut self,
        kernel: Result<Resource<HostKernel>, String>,
    ) -> Result<HolKernel, ProofError> {
        let kernel = kernel.map_err(|message| ProofError::Guest { message })?;
        self.store
            .data_mut()
            .table
            .delete(kernel)
            .map(|kernel: HostKernel| kernel.0)
            .map_err(|source| ProofError::Component {
                source: source.into(),
            })
    }

    /// Applies a compact strategy-local tactic to a supplied or fresh kernel.
    ///
    /// # Errors
    ///
    /// Returns [`ProofError::Component`] for runtime/resource failures and
    /// [`ProofError::Guest`] when the strategy rejects the request.
    pub fn apply_tactic(
        &mut self,
        tactic_id: u64,
        arguments: Vec<u8>,
        kernel: Option<HolKernel>,
    ) -> Result<HolKernel, ProofError> {
        futures::executor::block_on(self.apply_tactic_async(tactic_id, arguments, kernel))
    }

    /// Asynchronously applies a compact strategy-local tactic.
    ///
    /// # Errors
    ///
    /// Returns the same failures as [`Self::apply_tactic`].
    pub async fn apply_tactic_async(
        &mut self,
        tactic_id: u64,
        arguments: Vec<u8>,
        kernel: Option<HolKernel>,
    ) -> Result<HolKernel, ProofError> {
        let kernel = self.insert_kernel(kernel)?;
        let result = self
            .store
            .run_concurrent(async |accessor| {
                self.proof
                    .nucleus_proof_strategy()
                    .call_apply_tactic(accessor, tactic_id, arguments, kernel)
                    .await
            })
            .await
            .map_err(|source| ProofError::Component { source })?
            .map_err(|source| ProofError::Component { source })?;
        self.remove_kernel(result)
    }

    /// Applies a human-readable strategy-local tactic.
    ///
    /// # Errors
    ///
    /// Returns the same failures as [`Self::apply_tactic`].
    pub fn apply_tactic_name(
        &mut self,
        name: String,
        kernel: Option<HolKernel>,
    ) -> Result<HolKernel, ProofError> {
        futures::executor::block_on(self.apply_tactic_name_async(name, kernel))
    }

    /// Asynchronously applies a human-readable strategy-local tactic.
    ///
    /// # Errors
    ///
    /// Returns the same failures as [`Self::apply_tactic`].
    pub async fn apply_tactic_name_async(
        &mut self,
        name: String,
        kernel: Option<HolKernel>,
    ) -> Result<HolKernel, ProofError> {
        self.apply_tactic_async(1, name.into_bytes(), kernel).await
    }

    /// Constructs a checked kernel for an addressed proof request.
    ///
    /// # Errors
    ///
    /// Returns the same failures as [`Self::apply_tactic`].
    pub fn prove_addr(&mut self, addr: O256) -> Result<HolKernel, ProofError> {
        self.apply_tactic(0, addr.as_bytes().to_vec(), None)
    }

    /// Asynchronously constructs a checked kernel for an addressed proof request.
    ///
    /// # Errors
    ///
    /// Returns the same failures as [`Self::apply_tactic`].
    pub async fn prove_addr_async(&mut self, addr: O256) -> Result<HolKernel, ProofError> {
        self.apply_tactic_async(0, addr.as_bytes().to_vec(), None)
            .await
    }
}

/// Runs the default request for a component implementing
/// `nucleus:proof/proof`, blocking the current thread until its
/// native-async execution completes.
///
/// This is a Rust compatibility convenience, not a second component ABI. New
/// async callers should use [`load_proof_async`].
///
/// # Errors
///
/// Returns [`ProofError::Component`] for malformed components, missing imports
/// or exports, traps, and resource failures. Returns [`ProofError::Guest`] when
/// the component's tactic-zero default request returns an error.
pub fn load_proof(component: &[u8]) -> Result<HolKernel, ProofError> {
    Strategy::from_bytes(component)?.apply_tactic(0, Vec::new(), None)
}

/// Runs one prover-local `o256` request through a native-async proof component.
///
/// The request is an opaque selector interpreted by the prover. It is not
/// compared with the returned kernel's independently computed address.
///
/// # Errors
///
/// Returns [`ProofError::Component`] for malformed components, missing imports
/// or exports, traps, and resource failures. Returns [`ProofError::Guest`] when
/// the component's tactic-zero addressed request rejects the request.
pub async fn load_proof_async(component: &[u8], target: O256) -> Result<HolKernel, ProofError> {
    Strategy::from_bytes_async(component, None)
        .await?
        .prove_addr_async(target)
        .await
}

/// Runs one prover-local request with an injected asynchronous CAS provider.
///
/// The component's private insertion-ordered CAS remains available as a
/// runtime-local overlay. Async lookups consult that overlay first and then
/// `provider`. Raw provider bytes remain untrusted; optimized facts are checked
/// to ensure they answer the exact requested address.
///
/// # Errors
///
/// Returns [`ProofError::Component`] for malformed components, missing imports
/// or exports, traps, and resource failures. Returns [`ProofError::Guest`] when
/// the component rejects the request, including a provider lookup failure.
pub async fn load_proof_with_cas_async(
    component: &[u8],
    target: O256,
    provider: Arc<dyn AsyncCas>,
) -> Result<HolKernel, ProofError> {
    Strategy::from_bytes_async(component, Some(provider))
        .await?
        .prove_addr_async(target)
        .await
}

#[cfg(test)]
mod tests {
    use super::*;
    use nucleus::proof::host::{
        Host, HostBlob, HostBytes, HostIndexCas, HostKernel as HostKernelApi,
    };

    #[test]
    fn bytes_and_blobs_round_trip_through_both_cas_views() {
        let mut state = ProofState::default();
        let bytes = HostBytes::new(&mut state, b"portable proof".to_vec()).unwrap();
        let blob = HostBytes::blob(&mut state, bytes).unwrap();
        let round_trip = HostBlob::bytes(&mut state, Resource::new_borrow(blob.rep())).unwrap();
        assert_eq!(
            HostBytes::to_list(&mut state, round_trip).unwrap(),
            b"portable proof"
        );

        let private = HostIndexCas::new(&mut state).unwrap();
        let private_id = HostIndexCas::insert(
            &mut state,
            Resource::new_borrow(private.rep()),
            Resource::new_borrow(blob.rep()),
        )
        .unwrap();
        assert!(
            HostIndexCas::get(&mut state, Resource::new_borrow(private.rep()), private_id)
                .unwrap()
                .is_some()
        );

        let default_id = Host::cas_insert(&mut state, Resource::new_borrow(blob.rep())).unwrap();
        assert!(Host::cas_get(&mut state, default_id).unwrap().is_some());
    }

    #[test]
    fn wit_rewrite_accelerator_returns_a_checked_theorem() {
        let mut kernel = HolKernel::new();
        let star = kernel.star().expect("star");
        let bool_ty = kernel.bool_ty(star).expect("bool");
        let truth = kernel.bool(bool_ty, true).expect("truth");
        let proposition = kernel.refl(bool_ty, truth).expect("truth equality");
        let equality = kernel
            .refl(bool_ty, proposition.equality)
            .expect("proposition equality");

        let mut state = ProofState::default();
        let resource = state
            .table
            .push(HostKernel(kernel))
            .expect("kernel resource");
        let result = <ProofState as nucleus::proof::tactics::Host>::rewrite_proposition(
            &mut state,
            Resource::new_borrow(resource.rep()),
            u64_from_ref(bool_ty),
            u64::from(equality.theorem.get().unsigned_abs()),
            u64::from(proposition.theorem.get().unsigned_abs()),
            nucleus::proof::tactics::RewriteDirection::Forward,
        )
        .expect("host call")
        .expect("rewrite");
        let kernel = &state.table.get(&resource).expect("kernel resource").0;
        assert!(
            kernel
                .thm()
                .get(theorem_id(result.theorem).expect("theorem ID"))
                .is_some()
        );
        assert_eq!(result.source, result.target);
    }

    #[test]
    fn wit_deduction_antisymmetry_returns_a_checked_equality() {
        let mut state = ProofState::default();
        let resource = HostKernelApi::new(&mut state).expect("kernel resource");
        let star = HostKernelApi::kind_star(&mut state, Resource::new_borrow(resource.rep()))
            .expect("host call")
            .expect("star");
        let bool_ty =
            HostKernelApi::bool_type(&mut state, Resource::new_borrow(resource.rep()), star)
                .expect("host call")
                .expect("bool type");
        let truth = HostKernelApi::bool_lit(
            &mut state,
            Resource::new_borrow(resource.rep()),
            bool_ty,
            true,
        )
        .expect("host call")
        .expect("truth");
        let identity = state
            .table
            .get_mut(&resource)
            .expect("kernel resource")
            .0
            .identity(covalence_logic_hol::Lit::positive(
                i32::try_from(truth).expect("reference fits i32"),
            ))
            .expect("identity");
        let result = HostKernelApi::deduct_antisym(
            &mut state,
            Resource::new_borrow(resource.rep()),
            bool_ty,
            truth,
            truth,
            u64::from(identity.get().unsigned_abs()),
            u64::from(identity.get().unsigned_abs()),
        )
        .expect("host call")
        .expect("deduction antisymmetry");
        let kernel = &state.table.get(&resource).expect("kernel resource").0;
        assert!(
            kernel
                .thm()
                .get(theorem_id(result.theorem).expect("theorem ID"))
                .is_some()
        );
        assert_eq!(
            kernel
                .arena()
                .bool_value(reference(result.equality).expect("equality")),
            None
        );
    }

    #[test]
    fn wit_unary_iteration_checks_classifiers_and_is_atomic() {
        let mut kernel = HolKernel::new();
        let star = kernel.star().expect("star");
        let ty = kernel.bool_ty(star).expect("type");
        let zero = kernel.bool(ty, false).expect("zero");
        let binder = kernel.tm_fv(0, ty).expect("binder");
        let successor = kernel.lam(binder, binder).expect("successor");
        let malformed = kernel.bool(ty, true).expect("malformed successor");
        let mut state = ProofState::default();
        let resource = state
            .table
            .push(HostKernel(kernel))
            .expect("kernel resource");

        let result = <ProofState as nucleus::proof::tactics::Host>::iterate_unary(
            &mut state,
            Resource::new_borrow(resource.rep()),
            u64_from_ref(zero),
            u64_from_ref(successor),
            3,
        )
        .expect("host call")
        .expect("iteration");
        let kernel = &state.table.get(&resource).expect("kernel resource").0;
        assert_eq!(
            kernel
                .classifier(reference(result).expect("result reference"))
                .expect("result classifier"),
            ty
        );

        let before = kernel.arena().clone();
        let rejected = <ProofState as nucleus::proof::tactics::Host>::iterate_unary(
            &mut state,
            Resource::new_borrow(resource.rep()),
            u64_from_ref(zero),
            u64_from_ref(malformed),
            0,
        )
        .expect("host call");
        assert!(rejected.is_err());
        assert_eq!(
            state
                .table
                .get(&resource)
                .expect("kernel resource")
                .0
                .arena(),
            &before
        );
    }
}
