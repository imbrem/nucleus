CREATE TABLE {table} (
    tm INTEGER NOT NULL,
    lhs INTEGER NOT NULL,
    rhs INTEGER NOT NULL,
    PRIMARY KEY (tm, lhs, rhs),
    CHECK (typeof(lhs + rhs) = 'integer' AND tm = lhs + rhs)
) STRICT, WITHOUT ROWID;
