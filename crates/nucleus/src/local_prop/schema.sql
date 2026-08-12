PRAGMA foreign_keys = ON;

CREATE TABLE prop_row (
    premise INTEGER NOT NULL CHECK (
        premise BETWEEN -4294967295 AND 4294967295 AND premise != 0
    ),
    source INTEGER NOT NULL CHECK (source = 0),
    conclusion INTEGER NOT NULL CHECK (
        conclusion BETWEEN -4294967295 AND 4294967295 AND conclusion != 0
    ),
    reason INTEGER NOT NULL CHECK (reason >= 0),
    PRIMARY KEY (premise, source, conclusion)
) STRICT, WITHOUT ROWID;

CREATE TABLE prop_metadata (
    premise INTEGER NOT NULL,
    source INTEGER NOT NULL,
    conclusion INTEGER NOT NULL,
    kind TEXT NOT NULL CHECK (length(kind) BETWEEN 1 AND 128),
    payload BLOB NOT NULL,
    PRIMARY KEY (premise, source, conclusion, kind),
    FOREIGN KEY (premise, source, conclusion)
      REFERENCES prop_row (premise, source, conclusion) ON DELETE CASCADE
) STRICT;
