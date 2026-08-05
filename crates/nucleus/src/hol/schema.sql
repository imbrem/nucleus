CREATE TABLE hol_schema (
    representation TEXT PRIMARY KEY CHECK (representation = 'tagged-node')
) STRICT;

-- One algebraic node stream for kinds, types, and terms.  The tag determines
-- the sort, constructor, and meaning of lhs/rhs/ty.  Nucleus validates those
-- invariants before admission; SQL provides storage and canonical indexes.
CREATE TABLE hol_node (
    node_id INTEGER PRIMARY KEY,
    tag TEXT NOT NULL,
    lhs INTEGER,
    rhs INTEGER,
    ty INTEGER,
    CHECK (COALESCE((
        (tag = 'KSTAR' AND node_id = 1 AND lhs IS NULL AND rhs IS NULL AND ty IS NULL)
        OR (tag = 'KARR' AND lhs IS NOT NULL AND rhs IS NOT NULL AND ty IS NULL)
        OR (tag = 'TBOOL' AND node_id = 2 AND lhs IS NULL AND rhs IS NULL AND ty = 1)
        OR (tag = 'TBASE' AND lhs IS NOT NULL AND rhs IS NULL AND ty = 1)
        OR (tag = 'TFV' AND lhs IS NOT NULL AND rhs IS NULL AND ty = 1)
        OR (tag = 'TARR' AND lhs IS NOT NULL AND rhs IS NOT NULL AND ty = 1)
        OR (
            tag = 'MBOOL'
            AND lhs IS NOT NULL
            AND lhs IN (0, 1)
            AND rhs IS NULL
            AND ty = 2
        )
        OR (tag = 'MFV' AND lhs IS NOT NULL AND rhs IS NULL AND ty IS NOT NULL)
        OR (tag = 'MCONST' AND lhs IS NOT NULL AND rhs IS NULL AND ty IS NOT NULL)
        OR (
            tag = 'MBV'
            AND lhs BETWEEN 0 AND 4294967295
            AND rhs IS NULL
            AND ty IS NOT NULL
        )
        OR (tag = 'MAPP' AND lhs IS NOT NULL AND rhs IS NOT NULL AND ty IS NOT NULL)
        OR (tag = 'MLAM' AND lhs IS NOT NULL AND rhs IS NOT NULL AND ty IS NOT NULL)
        OR (tag = 'MEQ' AND lhs IS NOT NULL AND rhs IS NOT NULL AND ty = 2)
        OR (tag = 'MEPS' AND lhs IS NOT NULL AND rhs IS NULL AND ty IS NOT NULL)
    ), 0))
) STRICT;

CREATE TABLE hol_context (
    ctx_id INTEGER PRIMARY KEY
) STRICT;

CREATE TABLE hol_context_member (
    ctx_id INTEGER NOT NULL,
    term_id INTEGER NOT NULL,
    PRIMARY KEY (ctx_id, term_id)
) STRICT, WITHOUT ROWID;

CREATE TABLE hol_judgement (
    ctx_id INTEGER NOT NULL,
    term_id INTEGER NOT NULL,
    PRIMARY KEY (ctx_id, term_id)
) STRICT, WITHOUT ROWID;

-- Γ implies Δ when every member of Δ has been proved under Γ.
CREATE TABLE hol_context_implication (
    antecedent_ctx_id INTEGER NOT NULL,
    consequent_ctx_id INTEGER NOT NULL,
    PRIMARY KEY (antecedent_ctx_id, consequent_ctx_id)
) STRICT, WITHOUT ROWID;

-- A decidable structural fact: result is exactly the finite member-set union.
-- This is deliberately distinct from future opaque/equivalence-backed unions.
CREATE TABLE hol_context_exact_union (
    left_ctx_id INTEGER NOT NULL,
    right_ctx_id INTEGER NOT NULL,
    result_ctx_id INTEGER NOT NULL,
    PRIMARY KEY (left_ctx_id, right_ctx_id)
) STRICT, WITHOUT ROWID;

-- Hierarchical local names. Namespace zero is the anonymous root.
CREATE TABLE hol_namespace (
    namespace_id INTEGER PRIMARY KEY CHECK (namespace_id >= 0),
    parent_namespace_id INTEGER,
    name TEXT,
    source_import_id INTEGER,
    source_namespace_id INTEGER,
    CHECK (
        parent_namespace_id IS NULL
        OR (parent_namespace_id >= 0 AND parent_namespace_id != namespace_id)
    ),
    CHECK (name IS NULL OR length(name) > 0),
    CHECK (
        (source_import_id IS NULL AND source_namespace_id IS NULL)
        OR (
            source_import_id IS NOT NULL
            AND source_import_id >= 0
            AND source_namespace_id IS NOT NULL
            AND source_namespace_id >= 0
        )
    )
) STRICT;

CREATE UNIQUE INDEX hol_namespace_named_child
    ON hol_namespace(COALESCE(parent_namespace_id, -1), name)
    WHERE name IS NOT NULL;

-- One namespace-wide export-ID space shared by all HOL sorts.
CREATE TABLE hol_namespace_export (
    namespace_id INTEGER NOT NULL CHECK (namespace_id >= 0),
    export_id INTEGER NOT NULL CHECK (export_id >= 0),
    sort TEXT NOT NULL CHECK (sort IN ('kind', 'type', 'term', 'context')),
    local_id INTEGER NOT NULL CHECK (local_id >= 0),
    name TEXT,
    CHECK (name IS NULL OR length(name) > 0),
    PRIMARY KEY (namespace_id, export_id)
) STRICT, WITHOUT ROWID;

CREATE UNIQUE INDEX hol_namespace_export_name
    ON hol_namespace_export(namespace_id, name)
    WHERE name IS NOT NULL;

-- Hash-first references only. Registration does not fetch, validate, attach,
-- authenticate, or trust the named database.
CREATE TABLE hol_import (
    import_id INTEGER PRIMARY KEY CHECK (import_id >= 0),
    schema_hash BLOB NOT NULL,
    image_hash BLOB NOT NULL,
    CHECK (typeof(schema_hash) = 'blob' AND length(schema_hash) = 32),
    CHECK (typeof(image_hash) = 'blob' AND length(image_hash) = 32),
    UNIQUE (schema_hash, image_hash)
) STRICT;

-- Persistent audit evidence that the creating connection explicitly accepted
-- one registered import assertion.  Receiving this table does not make its
-- rows trusted on another connection.
CREATE TABLE hol_trusted_import (
    trusted_import_id INTEGER PRIMARY KEY CHECK (trusted_import_id >= 0),
    import_id INTEGER NOT NULL CHECK (import_id >= 0),
    signer_hash BLOB NOT NULL,
    public_key BLOB NOT NULL,
    signature BLOB NOT NULL,
    CHECK (typeof(signer_hash) = 'blob' AND length(signer_hash) = 32),
    CHECK (typeof(public_key) = 'blob' AND length(public_key) = 32),
    CHECK (typeof(signature) = 'blob' AND length(signature) = 64),
    UNIQUE (import_id, signer_hash)
) STRICT;

CREATE UNIQUE INDEX hol_kstar_unique
    ON hol_node((1)) WHERE tag = 'KSTAR';

CREATE UNIQUE INDEX hol_karr_unique
    ON hol_node(lhs, rhs) WHERE tag = 'KARR';

CREATE UNIQUE INDEX hol_tbool_unique
    ON hol_node((1)) WHERE tag = 'TBOOL';

CREATE UNIQUE INDEX hol_tbase_unique
    ON hol_node(lhs) WHERE tag = 'TBASE';

CREATE UNIQUE INDEX hol_tfv_unique
    ON hol_node(lhs, ty) WHERE tag = 'TFV';

CREATE UNIQUE INDEX hol_tarr_unique
    ON hol_node(lhs, rhs) WHERE tag = 'TARR';

CREATE UNIQUE INDEX hol_mbool_unique
    ON hol_node(lhs) WHERE tag = 'MBOOL';

CREATE UNIQUE INDEX hol_mfv_unique
    ON hol_node(lhs, ty) WHERE tag = 'MFV';

CREATE UNIQUE INDEX hol_mconst_unique
    ON hol_node(lhs) WHERE tag = 'MCONST';

CREATE UNIQUE INDEX hol_mbv_unique
    ON hol_node(lhs, ty) WHERE tag = 'MBV';

CREATE UNIQUE INDEX hol_mapp_unique
    ON hol_node(lhs, rhs) WHERE tag = 'MAPP';

CREATE UNIQUE INDEX hol_mlam_unique
    ON hol_node(lhs, rhs) WHERE tag = 'MLAM';

CREATE UNIQUE INDEX hol_meq_unique
    ON hol_node(lhs, rhs) WHERE tag = 'MEQ';

CREATE UNIQUE INDEX hol_meps_unique
    ON hol_node(lhs) WHERE tag = 'MEPS';

INSERT INTO hol_schema(representation) VALUES ('tagged-node');
INSERT INTO hol_node(node_id, tag) VALUES (1, 'KSTAR');
INSERT INTO hol_node(node_id, tag, ty) VALUES (2, 'TBOOL', 1);
INSERT INTO hol_context(ctx_id) VALUES (0);
INSERT INTO hol_namespace(namespace_id) VALUES (0);
