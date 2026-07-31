PRAGMA foreign_keys = ON;

-- Baseline: one SQLite JSONB tagged expression per definition.
CREATE TABLE json_def (
    id INTEGER PRIMARY KEY,
    body BLOB NOT NULL CHECK (json_valid(body, 8)),
    tag INTEGER GENERATED ALWAYS AS (json_extract(body, '$[0]')) STORED,
    CHECK (json_type(body) = 'array'),
    CHECK (json_type(body, '$[0]') = 'integer')
) STRICT;

-- A rebuildable dependency index. The JSONB body remains the source of truth.
CREATE TABLE json_dep (
    owner_id INTEGER NOT NULL REFERENCES json_def(id) ON DELETE CASCADE,
    position INTEGER NOT NULL CHECK (position > 0),
    source_id INTEGER,
    target_id INTEGER NOT NULL,
    PRIMARY KEY (owner_id, position),
    FOREIGN KEY (source_id) REFERENCES ast_source(id)
) STRICT, WITHOUT ROWID;

CREATE INDEX json_dep_target
    ON json_dep(source_id, target_id, owner_id);

-- Persistent imports use snapshot identities, never connection-local schema names.
CREATE TABLE ast_source (
    id INTEGER PRIMARY KEY,
    snapshot_hash BLOB NOT NULL UNIQUE CHECK (length(snapshot_hash) = 32),
    format TEXT NOT NULL
) STRICT;

-- Actual byte strings remain SQL BLOBs. JSONB contains only the local blob ID.
CREATE TABLE ast_blob (
    id INTEGER PRIMARY KEY,
    hash BLOB NOT NULL UNIQUE CHECK (length(hash) = 32),
    data BLOB NOT NULL
) STRICT;

-- Competing normalized tagged-DAG layout.
CREATE TABLE dag_node (
    id INTEGER PRIMARY KEY,
    tag INTEGER NOT NULL,
    atom BLOB,
    blob_id INTEGER REFERENCES ast_blob(id)
) STRICT;

CREATE TABLE dag_edge (
    owner_id INTEGER NOT NULL REFERENCES dag_node(id) ON DELETE CASCADE,
    position INTEGER NOT NULL CHECK (position >= 0),
    target_id INTEGER NOT NULL REFERENCES dag_node(id),
    PRIMARY KEY (owner_id, position)
) STRICT, WITHOUT ROWID;

CREATE INDEX dag_edge_target
    ON dag_edge(target_id, owner_id);

CREATE TABLE dag_import (
    node_id INTEGER PRIMARY KEY REFERENCES dag_node(id) ON DELETE CASCADE,
    source_id INTEGER NOT NULL REFERENCES ast_source(id),
    target_id INTEGER NOT NULL
) STRICT;

-- Lean NDJSON baseline: preserve each record as JSONB, then project the hot graph.
CREATE TABLE lean_record (
    ordinal INTEGER PRIMARY KEY,
    raw BLOB NOT NULL CHECK (json_valid(raw, 8)),
    kind TEXT GENERATED ALWAYS AS (json_extract(raw, '$.kind')) STORED,
    source_id INTEGER REFERENCES ast_source(id)
) STRICT;

CREATE INDEX lean_record_kind ON lean_record(kind, ordinal);

CREATE TABLE lean_expr (
    expr_id INTEGER PRIMARY KEY,
    tag TEXT NOT NULL,
    arg0 INTEGER,
    arg1 INTEGER,
    payload BLOB
) STRICT;
