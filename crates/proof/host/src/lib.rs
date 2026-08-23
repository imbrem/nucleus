//! Portable implementation of the Nucleus proof host interface.

#![cfg(target_os = "wasi")]

use std::cell::RefCell;

use bytes::Bytes as SharedBytes;
use covalence_data_cas::IndexCas as InnerIndexCas;
use covalence_lib_hash::O256;
use covalence_logic_cas::CasFact;
use covalence_logic_hol::{
    Arena as InnerArena, Import, ImportId, Kernel as InnerKernel, Link, LinkFormat, Ref, Resolver,
    Sort as InnerSort, SynFactId, SynRel, Table as InnerTable, wire,
};

#[allow(
    unsafe_code,
    warnings,
    clippy::all,
    clippy::pedantic,
    clippy::nursery,
    clippy::restriction
)]
mod bindings;

use bindings::exports::nucleus::proof::host::{
    self as wit, Arena, ArenaBorrow, Blob, BlobBorrow, Bytes, BytesBorrow, Guest, GuestArena,
    GuestBlob, GuestBytes, GuestIndexCas, GuestKernel, GuestTable, Sort, SynRel as WitSynRel,
    Table,
};

#[derive(Clone)]
struct HostBytes(SharedBytes);

#[derive(Clone)]
struct HostBlob(CasFact);

#[derive(Default)]
struct HostIndexCas(RefCell<InnerIndexCas>);

#[derive(Clone, Default)]
struct HostArena(RefCell<InnerArena>);

#[derive(Clone)]
struct HostTable(InnerTable);

#[derive(Default)]
struct HostKernel(RefCell<InnerKernel>);

struct Component;

thread_local! {
    static DEFAULT_CAS: RefCell<InnerIndexCas> = const { RefCell::new(InnerIndexCas::new()) };
}

impl Guest for Component {
    type Bytes = HostBytes;
    type Blob = HostBlob;
    type IndexCas = HostIndexCas;
    type Arena = HostArena;
    type Table = HostTable;
    type Kernel = HostKernel;

    fn cas_insert(value: BlobBorrow<'_>) -> u64 {
        DEFAULT_CAS.with_borrow_mut(|cas| cas.insert_fact(value.get::<HostBlob>().0.clone()))
    }

    fn cas_put(value: BytesBorrow<'_>) -> u64 {
        DEFAULT_CAS.with_borrow_mut(|cas| cas.insert(value.get::<HostBytes>().0.clone()))
    }

    fn cas_get(object: u64) -> Option<Blob> {
        DEFAULT_CAS.with_borrow(|cas| {
            cas.fact(object)
                .cloned()
                .map(|fact| Blob::new(HostBlob(fact)))
        })
    }

    fn cas_find(address: Vec<u8>) -> Result<Option<u64>, String> {
        let address = address_from_bytes(address)?;
        Ok(DEFAULT_CAS.with_borrow(|cas| cas.id(address)))
    }
}

impl GuestBytes for HostBytes {
    fn new(value: Vec<u8>) -> Self {
        Self(SharedBytes::from(value))
    }

    fn len(&self) -> u64 {
        u64::try_from(self.0.len()).unwrap_or(u64::MAX)
    }

    fn to_list(&self) -> Vec<u8> {
        self.0.to_vec()
    }

    fn slice(&self, start: u64, end: u64) -> Result<Bytes, String> {
        let start = usize_from_u64(start, "slice start")?;
        let end = usize_from_u64(end, "slice end")?;
        if start > end || end > self.0.len() {
            return Err("slice lies outside the byte buffer".to_owned());
        }
        Ok(Bytes::new(Self(self.0.slice(start..end))))
    }

    fn blob(&self) -> Blob {
        Blob::new(HostBlob(CasFact::from_bytes(self.0.clone())))
    }
}

impl GuestBlob for HostBlob {
    fn check(address: Vec<u8>, value: BytesBorrow<'_>) -> Result<Blob, String> {
        let address = address_from_bytes(address)?;
        let bytes = value.get::<HostBytes>().0.clone();
        let fact = CasFact::new(address, bytes).map_err(|error| error.to_string())?;
        Ok(Blob::new(Self(fact)))
    }

    fn address(&self) -> Vec<u8> {
        self.0.hash().as_ref().to_vec()
    }

    fn bytes(&self) -> Bytes {
        Bytes::new(HostBytes(self.0.bytes().clone()))
    }

    fn len(&self) -> u64 {
        u64::try_from(self.0.bytes().len()).unwrap_or(u64::MAX)
    }
}

impl GuestIndexCas for HostIndexCas {
    fn new() -> Self {
        Self::default()
    }

    fn insert(&self, value: BlobBorrow<'_>) -> u64 {
        self.0
            .borrow_mut()
            .insert_fact(value.get::<HostBlob>().0.clone())
    }

    fn put(&self, value: BytesBorrow<'_>) -> u64 {
        self.0
            .borrow_mut()
            .insert(value.get::<HostBytes>().0.clone())
    }

    fn get(&self, object: u64) -> Option<Blob> {
        self.0
            .borrow()
            .fact(object)
            .cloned()
            .map(|fact| Blob::new(HostBlob(fact)))
    }

    fn find(&self, address: Vec<u8>) -> Result<Option<u64>, String> {
        Ok(self.0.borrow().id(address_from_bytes(address)?))
    }

    fn remove(&self, address: Vec<u8>) -> Result<bool, String> {
        Ok(self.0.borrow_mut().remove(address_from_bytes(address)?))
    }

    fn len(&self) -> u64 {
        u64::try_from(self.0.borrow().fact_count()).unwrap_or(u64::MAX)
    }
}

impl GuestArena for HostArena {
    fn new() -> Self {
        Self::default()
    }

    fn from_cbor(value: BytesBorrow<'_>) -> Result<Arena, String> {
        let arena = wire::deserialize(value.get::<HostBytes>().0.as_ref())
            .map_err(|error| error.to_string())?;
        Ok(Arena::new(Self(RefCell::new(arena))))
    }

    fn to_cbor(&self) -> Result<Bytes, String> {
        let mut bytes = Vec::new();
        wire::serialize(&self.0.borrow(), &mut bytes).map_err(|error| error.to_string())?;
        Ok(Bytes::new(HostBytes(SharedBytes::from(bytes))))
    }

    fn address(&self) -> Vec<u8> {
        self.0.borrow().addr().as_ref().to_vec()
    }

    fn len(&self) -> u64 {
        u64::try_from(self.0.borrow().len()).unwrap_or(u64::MAX)
    }

    fn kind_star(&self) -> Result<u64, String> {
        pushed(self.0.borrow_mut().push_kind_star(), "definition")
    }

    fn kind_arr(&self, domain: u64, codomain: u64) -> Result<u64, String> {
        pushed(
            self.0
                .borrow_mut()
                .push_kind_arr(reference(domain)?, reference(codomain)?),
            "definition",
        )
    }

    fn bool_type(&self) -> Result<u64, String> {
        pushed(self.0.borrow_mut().push_bool_ty(), "definition")
    }

    fn ty_arr(&self, domain: u64, codomain: u64) -> Result<u64, String> {
        pushed(
            self.0
                .borrow_mut()
                .push_ty_arr(reference(domain)?, reference(codomain)?),
            "definition",
        )
    }

    fn ty_app(&self, function: u64, argument: u64) -> Result<u64, String> {
        pushed(
            self.0
                .borrow_mut()
                .push_ty_app(reference(function)?, reference(argument)?),
            "definition",
        )
    }

    fn ty_lam(&self, binder: u64, body: u64) -> Result<u64, String> {
        pushed(
            self.0
                .borrow_mut()
                .push_ty_lam(reference(binder)?, reference(body)?),
            "definition",
        )
    }

    fn ty_fv(&self, name: u64, kind: u64) -> Result<u64, String> {
        pushed(
            self.0.borrow_mut().push_ty_fv(name, reference(kind)?),
            "definition",
        )
    }

    fn ty_exists(&self, name: u64, predicate: u64) -> Result<u64, String> {
        pushed(
            self.0
                .borrow_mut()
                .push_ty_exists(name, reference(predicate)?),
            "definition",
        )
    }

    fn model(&self, name: u64, predicate: u64) -> Result<u64, String> {
        pushed(
            self.0.borrow_mut().push_model(name, reference(predicate)?),
            "definition",
        )
    }

    fn tm_fv(&self, name: u64, ty: u64) -> Result<u64, String> {
        pushed(
            self.0.borrow_mut().push_tm_fv(name, reference(ty)?),
            "definition",
        )
    }

    fn app(&self, function: u64, argument: u64) -> Result<u64, String> {
        pushed(
            self.0
                .borrow_mut()
                .push_app(reference(function)?, reference(argument)?),
            "definition",
        )
    }

    fn lam(&self, binder: u64, body: u64) -> Result<u64, String> {
        pushed(
            self.0
                .borrow_mut()
                .push_lam(reference(binder)?, reference(body)?),
            "definition",
        )
    }

    fn bool_lit(&self, value: bool) -> Result<u64, String> {
        pushed(self.0.borrow_mut().push_bool(value), "definition")
    }

    fn tm_eq(&self, left: u64, right: u64) -> Result<u64, String> {
        pushed(
            self.0
                .borrow_mut()
                .push_tm_eq(reference(left)?, reference(right)?),
            "definition",
        )
    }

    fn eps(&self, ty: u64, predicate: u64) -> Result<u64, String> {
        pushed(
            self.0
                .borrow_mut()
                .push_eps(reference(ty)?, reference(predicate)?),
            "definition",
        )
    }

    fn kind_ref(&self, source: u64, foreign: u64) -> Result<u64, String> {
        pushed(
            self.0
                .borrow_mut()
                .push_kind_ref(import_id(source)?, reference(foreign)?),
            "definition",
        )
    }

    fn ty_ref(&self, source: u64, foreign: u64) -> Result<u64, String> {
        pushed(
            self.0
                .borrow_mut()
                .push_ty_ref(import_id(source)?, reference(foreign)?),
            "definition",
        )
    }

    fn tm_ref(&self, source: u64, foreign: u64) -> Result<u64, String> {
        pushed(
            self.0
                .borrow_mut()
                .push_tm_ref(import_id(source)?, reference(foreign)?),
            "definition",
        )
    }

    fn import_null(&self) -> Result<u64, String> {
        pushed_import(self.0.borrow_mut().push_import(Import::Null))
    }

    fn import_arena(&self, value: ArenaBorrow<'_>) -> Result<u64, String> {
        let arena = value.get::<HostArena>().0.borrow().clone();
        pushed_import(
            self.0
                .borrow_mut()
                .push_import(Import::Literal(Box::new(arena))),
        )
    }

    fn import_link(&self, address: Vec<u8>) -> Result<u64, String> {
        pushed_import(
            self.0
                .borrow_mut()
                .push_import(Import::Link(link(address)?)),
        )
    }

    fn add_context(&self, proposition: u64) -> Result<(), String> {
        self.0.borrow_mut().insert_context(reference(proposition)?);
        Ok(())
    }

    fn add_axiom(&self, name: String) {
        self.0.borrow_mut().insert_axiom(name);
    }
}

impl GuestTable for HostTable {
    fn from_arena(value: ArenaBorrow<'_>) -> Result<Table, String> {
        let arena = value.get::<HostArena>().0.borrow().clone();
        let table = InnerTable::from_arena(arena).map_err(|error| error.to_string())?;
        Ok(Table::new(Self(table)))
    }

    fn from_blob(value: BlobBorrow<'_>) -> Result<Table, String> {
        let table = InnerTable::try_from(value.get::<HostBlob>().0.clone())
            .map_err(|error| error.to_string())?;
        Ok(Table::new(Self(table)))
    }

    fn address(&self) -> Vec<u8> {
        self.0.addr().as_ref().to_vec()
    }

    fn arena(&self) -> Arena {
        Arena::new(HostArena(RefCell::new(self.0.as_ref().clone())))
    }
}

impl GuestKernel for HostKernel {
    fn new() -> Self {
        Self::default()
    }

    fn arena(&self) -> Arena {
        Arena::new(HostArena(RefCell::new(self.0.borrow().arena().clone())))
    }

    fn address(&self) -> Vec<u8> {
        self.0.borrow().addr().as_ref().to_vec()
    }

    fn len(&self) -> u64 {
        u64::try_from(self.0.borrow().len()).unwrap_or(u64::MAX)
    }

    fn category(&self, reference_value: u64) -> Result<Sort, String> {
        self.0
            .borrow()
            .category(reference(reference_value)?)
            .map(wit_sort)
            .map_err(|error| error.to_string())
    }

    fn classifier(&self, reference_value: u64) -> Result<u64, String> {
        checked_ref(self.0.borrow().classifier(reference(reference_value)?))
    }

    fn find(&self, reference_value: u64) -> Result<u64, String> {
        checked_ref(self.0.borrow().find(reference(reference_value)?))
    }

    fn find_mut(&self, reference_value: u64) -> Result<u64, String> {
        checked_ref(self.0.borrow_mut().find_mut(reference(reference_value)?))
    }

    fn equivalent(&self, left: u64, right: u64) -> Result<bool, String> {
        self.0
            .borrow()
            .equivalent(reference(left)?, reference(right)?)
            .map_err(|error| error.to_string())
    }

    fn equivalent_mut(&self, left: u64, right: u64) -> Result<bool, String> {
        self.0
            .borrow_mut()
            .equivalent_mut(reference(left)?, reference(right)?)
            .map_err(|error| error.to_string())
    }

    fn kind_star(&self) -> Result<u64, String> {
        checked_ref(self.0.borrow_mut().star())
    }

    fn kind_arr(&self, domain: u64, codomain: u64) -> Result<u64, String> {
        checked_ref(
            self.0
                .borrow_mut()
                .kind_arr(reference(domain)?, reference(codomain)?),
        )
    }

    fn bool_type(&self, star: u64) -> Result<u64, String> {
        checked_ref(self.0.borrow_mut().bool_ty(reference(star)?))
    }

    fn ty_arr(&self, domain: u64, codomain: u64) -> Result<u64, String> {
        checked_ref(
            self.0
                .borrow_mut()
                .ty_arr(reference(domain)?, reference(codomain)?),
        )
    }

    fn ty_app(&self, function: u64, argument: u64) -> Result<u64, String> {
        checked_ref(
            self.0
                .borrow_mut()
                .ty_app(reference(function)?, reference(argument)?),
        )
    }

    fn ty_lam(&self, binder: u64, body: u64) -> Result<u64, String> {
        checked_ref(
            self.0
                .borrow_mut()
                .ty_lam(reference(binder)?, reference(body)?),
        )
    }

    fn ty_fv(&self, name: u64, kind: u64) -> Result<u64, String> {
        checked_ref(self.0.borrow_mut().ty_fv(name, reference(kind)?))
    }

    fn ty_exists(&self, name: u64, predicate: u64) -> Result<u64, String> {
        checked_ref(self.0.borrow_mut().ty_exists(name, reference(predicate)?))
    }

    fn model(&self, name: u64, predicate: u64) -> Result<u64, String> {
        checked_ref(self.0.borrow_mut().model(name, reference(predicate)?))
    }

    fn tm_fv(&self, name: u64, ty: u64) -> Result<u64, String> {
        checked_ref(self.0.borrow_mut().tm_fv(name, reference(ty)?))
    }

    fn app(&self, function: u64, argument: u64) -> Result<u64, String> {
        checked_ref(
            self.0
                .borrow_mut()
                .app(reference(function)?, reference(argument)?),
        )
    }

    fn lam(&self, binder: u64, body: u64) -> Result<u64, String> {
        checked_ref(
            self.0
                .borrow_mut()
                .lam(reference(binder)?, reference(body)?),
        )
    }

    fn bool_lit(&self, bool_type: u64, value: bool) -> Result<u64, String> {
        checked_ref(self.0.borrow_mut().bool(reference(bool_type)?, value))
    }

    fn tm_eq(&self, bool_type: u64, left: u64, right: u64) -> Result<u64, String> {
        checked_ref(self.0.borrow_mut().eq(
            reference(bool_type)?,
            reference(left)?,
            reference(right)?,
        ))
    }

    fn eps(&self, ty: u64, predicate: u64) -> Result<u64, String> {
        checked_ref(
            self.0
                .borrow_mut()
                .eps(reference(ty)?, reference(predicate)?),
        )
    }

    fn import_arena(&self, value: ArenaBorrow<'_>) -> Result<u64, String> {
        let arena = value.get::<HostArena>().0.borrow().clone();
        self.0
            .borrow_mut()
            .import_literal(arena)
            .map(ImportId::get)
            .map_err(|error| error.to_string())
    }

    fn import_table(&self, value: wit::TableBorrow<'_>) -> Result<u64, String> {
        let arena = value.get::<HostTable>().0.as_ref().clone();
        self.0
            .borrow_mut()
            .import_literal(arena)
            .map(ImportId::get)
            .map_err(|error| error.to_string())
    }

    fn import_link(&self, address: Vec<u8>) -> Result<u64, String> {
        self.0
            .borrow_mut()
            .import_link(link(address)?)
            .map(ImportId::get)
            .map_err(|error| error.to_string())
    }

    fn kind_ref(&self, source: u64, foreign: u64) -> Result<u64, String> {
        DEFAULT_CAS.with_borrow(|cas| {
            let mut resolver = CasResolver(cas);
            self.0
                .borrow_mut()
                .kind_ref(&mut resolver, import_id(source)?, reference(foreign)?)
                .map(Ref::get)
                .map_err(|error| error.to_string())
        })
    }

    fn ty_ref(&self, source: u64, foreign: u64, kind: u64) -> Result<u64, String> {
        DEFAULT_CAS.with_borrow(|cas| {
            let mut resolver = CasResolver(cas);
            self.0
                .borrow_mut()
                .ty_ref(
                    &mut resolver,
                    import_id(source)?,
                    reference(foreign)?,
                    reference(kind)?,
                )
                .map(Ref::get)
                .map_err(|error| error.to_string())
        })
    }

    fn tm_ref(&self, source: u64, foreign: u64, ty: u64) -> Result<u64, String> {
        DEFAULT_CAS.with_borrow(|cas| {
            let mut resolver = CasResolver(cas);
            self.0
                .borrow_mut()
                .tm_ref(
                    &mut resolver,
                    import_id(source)?,
                    reference(foreign)?,
                    reference(ty)?,
                )
                .map(Ref::get)
                .map_err(|error| error.to_string())
        })
    }

    fn add_context(&self, proposition: u64) -> Result<(), String> {
        self.0
            .borrow_mut()
            .add_context(reference(proposition)?)
            .map_err(|error| error.to_string())
    }

    fn add_axiom(&self, name: String) -> Result<(), String> {
        self.0
            .borrow_mut()
            .add_axiom(&name)
            .map_err(|error| error.to_string())
    }

    fn syn_fact_count(&self) -> u64 {
        u64::try_from(self.0.borrow().syn_fact_len()).unwrap_or(u64::MAX)
    }

    fn remove_syn_fact(&self, fact: u64) -> bool {
        SynFactId::new(fact).is_some_and(|fact| self.0.borrow_mut().remove_syn_fact(fact))
    }

    fn truncate_syn_facts(&self, len: u64) -> Result<(), String> {
        self.0
            .borrow_mut()
            .truncate_syn_facts(usize_from_u64(len, "syntactic-fact count")?);
        Ok(())
    }

    fn syn_refl(
        &self,
        relation: WitSynRel,
        input: u64,
        target: Option<u64>,
    ) -> Result<u64, String> {
        checked_fact(self.0.borrow_mut().syn_refl(
            optional_fact_id(target)?,
            syn_relation(relation),
            reference(input)?,
        ))
    }

    fn syn_refine(
        &self,
        fact: u64,
        relation: WitSynRel,
        target: Option<u64>,
    ) -> Result<u64, String> {
        checked_fact(self.0.borrow_mut().syn_refine(
            optional_fact_id(target)?,
            fact_id(fact)?,
            syn_relation(relation),
        ))
    }

    fn syn_symm(&self, fact: u64, target: Option<u64>) -> Result<u64, String> {
        checked_fact(
            self.0
                .borrow_mut()
                .syn_symm(optional_fact_id(target)?, fact_id(fact)?),
        )
    }

    fn syn_trans(&self, left: u64, right: u64, target: Option<u64>) -> Result<u64, String> {
        checked_fact(self.0.borrow_mut().syn_trans(
            optional_fact_id(target)?,
            fact_id(left)?,
            fact_id(right)?,
        ))
    }

    fn syn_sub_var(&self, var: u64, val: u64, target: Option<u64>) -> Result<u64, String> {
        checked_fact(self.0.borrow_mut().syn_sub_var(
            optional_fact_id(target)?,
            reference(var)?,
            reference(val)?,
        ))
    }

    fn syn_sub_leaf(
        &self,
        var: u64,
        val: u64,
        input: u64,
        target: Option<u64>,
    ) -> Result<u64, String> {
        checked_fact(self.0.borrow_mut().syn_sub_leaf(
            optional_fact_id(target)?,
            reference(var)?,
            reference(val)?,
            reference(input)?,
        ))
    }

    fn syn_sub_leaf_forall(
        &self,
        var: u64,
        input: u64,
        target: Option<u64>,
    ) -> Result<u64, String> {
        checked_fact(self.0.borrow_mut().syn_sub_leaf_forall(
            optional_fact_id(target)?,
            reference(var)?,
            reference(input)?,
        ))
    }

    fn syn_sub_identity(
        &self,
        var: u64,
        val: u64,
        input: u64,
        output: u64,
        variable_equality: u64,
        body_equality: u64,
        target: Option<u64>,
    ) -> Result<u64, String> {
        checked_fact(self.0.borrow_mut().syn_sub_identity(
            optional_fact_id(target)?,
            reference(var)?,
            reference(val)?,
            reference(input)?,
            reference(output)?,
            fact_id(variable_equality)?,
            fact_id(body_equality)?,
        ))
    }

    fn syn_congr(
        &self,
        relation: WitSynRel,
        var: Option<u64>,
        val: Option<u64>,
        input: u64,
        output: u64,
        children: Vec<u64>,
        target: Option<u64>,
    ) -> Result<u64, String> {
        let children = children
            .into_iter()
            .map(fact_id)
            .collect::<Result<Vec<_>, _>>()?;
        checked_fact(self.0.borrow_mut().syn_congr(
            optional_fact_id(target)?,
            syn_relation(relation),
            var.map(reference).transpose()?,
            val.map(reference).transpose()?,
            reference(input)?,
            reference(output)?,
            &children,
        ))
    }

    fn syn_binder_congr(
        &self,
        relation: WitSynRel,
        var: Option<u64>,
        val: Option<u64>,
        input: u64,
        output: u64,
        binder: u64,
        body: u64,
        target: Option<u64>,
    ) -> Result<u64, String> {
        checked_fact(self.0.borrow_mut().syn_binder_congr(
            optional_fact_id(target)?,
            syn_relation(relation),
            var.map(reference).transpose()?,
            val.map(reference).transpose()?,
            reference(input)?,
            reference(output)?,
            fact_id(binder)?,
            fact_id(body)?,
        ))
    }

    fn syn_implicit_binder_congr(
        &self,
        relation: WitSynRel,
        var: Option<u64>,
        val: Option<u64>,
        input: u64,
        output: u64,
        binder: u64,
        body: u64,
        target: Option<u64>,
    ) -> Result<u64, String> {
        checked_fact(self.0.borrow_mut().syn_implicit_binder_congr(
            optional_fact_id(target)?,
            syn_relation(relation),
            var.map(reference).transpose()?,
            val.map(reference).transpose()?,
            reference(input)?,
            reference(output)?,
            reference(binder)?,
            fact_id(body)?,
        ))
    }

    fn syn_alpha_binder(
        &self,
        input: u64,
        output: u64,
        binder_classifier: u64,
        body_substitution: u64,
        target: Option<u64>,
    ) -> Result<u64, String> {
        checked_fact(self.0.borrow_mut().syn_alpha_binder(
            optional_fact_id(target)?,
            reference(input)?,
            reference(output)?,
            fact_id(binder_classifier)?,
            fact_id(body_substitution)?,
        ))
    }

    fn syn_alpha_implicit_binder(
        &self,
        input: u64,
        output: u64,
        input_binder: u64,
        output_binder: u64,
        body_substitution: u64,
        target: Option<u64>,
    ) -> Result<u64, String> {
        checked_fact(self.0.borrow_mut().syn_alpha_implicit_binder(
            optional_fact_id(target)?,
            reference(input)?,
            reference(output)?,
            reference(input_binder)?,
            reference(output_binder)?,
            fact_id(body_substitution)?,
        ))
    }

    fn tm_beta(&self, source: u64, substitution: u64, target: Option<u64>) -> Result<u64, String> {
        checked_fact(self.0.borrow_mut().tm_beta_fact(
            optional_fact_id(target)?,
            reference(source)?,
            fact_id(substitution)?,
        ))
    }

    fn ty_beta(&self, source: u64, substitution: u64, target: Option<u64>) -> Result<u64, String> {
        checked_fact(self.0.borrow_mut().ty_beta_fact(
            optional_fact_id(target)?,
            reference(source)?,
            fact_id(substitution)?,
        ))
    }

    fn tm_eta(&self, source: u64, target: Option<u64>) -> Result<u64, String> {
        checked_fact(
            self.0
                .borrow_mut()
                .tm_eta_fact(optional_fact_id(target)?, reference(source)?),
        )
    }

    fn union_syn_fact(&self, fact: u64) -> Result<(), String> {
        self.0
            .borrow_mut()
            .union_syn_fact(fact_id(fact)?)
            .map_err(|error| error.to_string())
    }
}

fn address_from_bytes(value: Vec<u8>) -> Result<O256, String> {
    let bytes: [u8; 32] = value
        .try_into()
        .map_err(|value: Vec<u8>| format!("CAS addresses contain 32 bytes, got {}", value.len()))?;
    Ok(O256::from_array(bytes))
}

fn usize_from_u64(value: u64, what: &str) -> Result<usize, String> {
    usize::try_from(value).map_err(|_| format!("{what} does not fit in component memory"))
}

fn reference(value: u64) -> Result<Ref, String> {
    Ref::new(value).ok_or_else(|| "arena references are one-based".to_owned())
}

fn import_id(value: u64) -> Result<ImportId, String> {
    ImportId::new(value).ok_or_else(|| "import IDs are one-based".to_owned())
}

fn fact_id(value: u64) -> Result<SynFactId, String> {
    SynFactId::new(value).ok_or_else(|| "syntactic-fact slots are one-based".to_owned())
}

fn optional_fact_id(value: Option<u64>) -> Result<Option<SynFactId>, String> {
    value.map(fact_id).transpose()
}

fn pushed(value: Option<Ref>, what: &str) -> Result<u64, String> {
    value
        .map(Ref::get)
        .ok_or_else(|| format!("{what} exceeds the arena's index space"))
}

fn pushed_import(value: Option<ImportId>) -> Result<u64, String> {
    value
        .map(ImportId::get)
        .ok_or_else(|| "import exceeds the arena's index space".to_owned())
}

fn link(value: Vec<u8>) -> Result<Link, String> {
    Ok(Link {
        format: LinkFormat::Cbor,
        blake3: address_from_bytes(value)?,
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

struct CasResolver<'a>(&'a InnerIndexCas);

impl Resolver for CasResolver<'_> {
    type Error = ResolveFailure;

    fn resolve(&mut self, link: &Link) -> Result<InnerTable, Self::Error> {
        let fact = self
            .0
            .fact_at(link.blake3)
            .cloned()
            .ok_or_else(|| ResolveFailure(format!("CAS has no object at {}", link.blake3)))?;
        InnerTable::try_from(fact).map_err(|error| ResolveFailure(error.to_string()))
    }
}

fn checked_ref(value: Result<Ref, covalence_logic_hol::KernelError>) -> Result<u64, String> {
    value.map(Ref::get).map_err(|error| error.to_string())
}

fn checked_fact(value: Result<SynFactId, covalence_logic_hol::KernelError>) -> Result<u64, String> {
    value.map(SynFactId::get).map_err(|error| error.to_string())
}

fn syn_relation(value: WitSynRel) -> SynRel {
    match value {
        WitSynRel::Syn => SynRel::Syn,
        WitSynRel::Alpha => SynRel::Alpha,
        WitSynRel::Conv => SynRel::Conv,
    }
}

fn wit_sort(value: InnerSort) -> Sort {
    match value {
        InnerSort::Kind => Sort::Kind,
        InnerSort::Ty => Sort::Ty,
        InnerSort::Tm => Sort::Tm,
    }
}

#[allow(unsafe_code, clippy::used_underscore_items)]
mod component_export {
    use super::{Component, bindings};

    bindings::export!(Component with_types_in bindings);
}
