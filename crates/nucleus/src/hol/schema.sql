-- HOL-omega kernel-state schema, version 1.
--
-- Two authoritative tables. `hol_object` is one tagged-node stream for
-- kinds, types, terms, and context spines; the tag fixes the sort and the
-- meaning of (lhs, rhs, ty). `hol_theorem` records established judgements
-- (kinds; vars; hyps |- concl) by spine and term ids; `theorem_id` is an
-- external handle and never authority. The remaining tables are the
-- namespace/export layer. Coordinate 0 means "empty/absent"; local object
-- ids are positive; negative coordinates are reserved for source-namespace
-- positions and are invalid in this version.
--
-- The kernel checks well-formedness before insertion; the UNIQUE indexes
-- provide local hash-consing as an optimization, never as a semantic
-- invariant. See semantics.txt for the normative tag vocabulary, formation
-- rules, and rule set.

CREATE TABLE hol_object (
    id  INTEGER PRIMARY KEY,
    tag INTEGER NOT NULL,
    lhs INTEGER NOT NULL DEFAULT 0,
    rhs INTEGER NOT NULL DEFAULT 0,
    ty  INTEGER NOT NULL DEFAULT 0,
    UNIQUE (tag, lhs, rhs, ty)
) STRICT;

CREATE TABLE hol_theorem (
    theorem_id INTEGER PRIMARY KEY,
    kinds INTEGER NOT NULL,
    vars  INTEGER NOT NULL,
    hyps  INTEGER NOT NULL,
    concl INTEGER NOT NULL,
    UNIQUE (kinds, vars, hyps, concl)
) STRICT;

CREATE TABLE hol_source (
    source_id   INTEGER PRIMARY KEY,
    schema_o256 BLOB NOT NULL
        CHECK (typeof(schema_o256) = 'blob' AND length(schema_o256) = 32),
    image_o256  BLOB NOT NULL
        CHECK (typeof(image_o256) = 'blob' AND length(image_o256) = 32),
    namespace   TEXT NOT NULL,
    UNIQUE (schema_o256, image_o256, namespace)
) STRICT;

CREATE TABLE hol_namespace (
    ns_id INTEGER PRIMARY KEY,
    name  TEXT NOT NULL UNIQUE CHECK (length(name) > 0)
) STRICT;

CREATE TABLE hol_export (
    ns_id  INTEGER NOT NULL,
    pos    INTEGER NOT NULL CHECK (pos >= 0),
    sort   INTEGER NOT NULL,
    target INTEGER NOT NULL,
    name   TEXT CHECK (name IS NULL OR length(name) > 0),
    PRIMARY KEY (ns_id, pos)
) STRICT, WITHOUT ROWID;

CREATE UNIQUE INDEX hol_export_name
    ON hol_export(ns_id, name) WHERE name IS NOT NULL;
