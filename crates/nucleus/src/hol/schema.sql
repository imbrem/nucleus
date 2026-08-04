PRAGMA foreign_keys = ON;

CREATE TABLE hol_schema (
    version INTEGER PRIMARY KEY CHECK (version = 0)
) STRICT;

CREATE TABLE hol_kind (
    kind_id INTEGER PRIMARY KEY,
    rank INTEGER NOT NULL CHECK (rank >= 0)
) STRICT;

CREATE TABLE hol_kind_star (
    kind_id INTEGER PRIMARY KEY REFERENCES hol_kind(kind_id)
) STRICT;

CREATE TABLE hol_kind_arrow (
    kind_id INTEGER PRIMARY KEY REFERENCES hol_kind(kind_id),
    domain_id INTEGER NOT NULL REFERENCES hol_kind(kind_id),
    codomain_id INTEGER NOT NULL REFERENCES hol_kind(kind_id),
    UNIQUE (domain_id, codomain_id)
) STRICT;

INSERT INTO hol_schema(version) VALUES (0);
INSERT INTO hol_kind(kind_id, rank) VALUES (1, 0);
INSERT INTO hol_kind_star(kind_id) VALUES (1);
