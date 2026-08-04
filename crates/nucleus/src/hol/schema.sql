CREATE TABLE hol_schema (
    version INTEGER PRIMARY KEY CHECK (version = 0),
    representation TEXT NOT NULL CHECK (representation = 'tagged-node')
) STRICT;

-- One algebraic node stream for kinds, types, and terms.  The tag determines
-- the sort, constructor, and meaning of lhs/rhs/ty.  Nucleus validates those
-- invariants before admission; SQL provides storage and canonical indexes.
CREATE TABLE hol_node (
    node_id INTEGER PRIMARY KEY,
    tag TEXT NOT NULL,
    lhs INTEGER,
    rhs INTEGER,
    ty INTEGER
) STRICT;

CREATE TABLE hol_context (
    ctx_id INTEGER PRIMARY KEY
) STRICT;

CREATE TABLE hol_context_member (
    ctx_id INTEGER NOT NULL,
    term_id INTEGER NOT NULL,
    PRIMARY KEY (ctx_id, term_id)
) STRICT, WITHOUT ROWID;

CREATE TABLE hol_theorem (
    ctx_id INTEGER NOT NULL,
    term_id INTEGER NOT NULL,
    rule TEXT NOT NULL,
    PRIMARY KEY (ctx_id, term_id)
) STRICT, WITHOUT ROWID;

CREATE UNIQUE INDEX hol_kstar_unique
    ON hol_node((1)) WHERE tag = 'KSTAR';

CREATE UNIQUE INDEX hol_karr_unique
    ON hol_node(lhs, rhs) WHERE tag = 'KARR';

CREATE UNIQUE INDEX hol_tbool_unique
    ON hol_node((1)) WHERE tag = 'TBOOL';

CREATE UNIQUE INDEX hol_tarr_unique
    ON hol_node(lhs, rhs) WHERE tag = 'TARR';

CREATE UNIQUE INDEX hol_mbool_unique
    ON hol_node(lhs) WHERE tag = 'MBOOL';

CREATE UNIQUE INDEX hol_mfv_unique
    ON hol_node(lhs, ty) WHERE tag = 'MFV';

CREATE UNIQUE INDEX hol_mapp_unique
    ON hol_node(lhs, rhs) WHERE tag = 'MAPP';

INSERT INTO hol_schema(version, representation) VALUES (0, 'tagged-node');
INSERT INTO hol_node(node_id, tag) VALUES (1, 'KSTAR');
INSERT INTO hol_node(node_id, tag, ty) VALUES (2, 'TBOOL', 1);
INSERT INTO hol_context(ctx_id) VALUES (0);
