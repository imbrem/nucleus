-- Propositional kernel-state schema, version 1.
--
-- One implication table over SAT-style literals plus a registry of
-- positive model numbers (worlds). A row asserts `lhs => rhs` where a
-- negative id denotes the negation of its absolute value and 0 is the
-- truthy constant. The `model` column is the possible-world index: 0 is
-- the definitional layer, negative rows are universal consequences, and
-- positive rows hold in one registered world. See prop/semantics.txt for
-- the normative commitment; the kernel enforces the define-once (level
-- uniqueness), positivity, and acyclicity disciplines before insertion,
-- and they double as validity assertions over untrusted images.

-- One row per implication: a pair is true for exactly one reason, and the
-- model column records it. The DEFAULT is a plain universal implication
-- (-1); definitions mark themselves explicitly with model 0.
CREATE TABLE prop_row (
    lhs   INTEGER NOT NULL CHECK (lhs != -9223372036854775808),
    rhs   INTEGER NOT NULL CHECK (rhs != -9223372036854775808),
    model INTEGER NOT NULL DEFAULT -1,
    PRIMARY KEY (lhs, rhs)
) STRICT, WITHOUT ROWID;

CREATE TABLE prop_world (
    world_id INTEGER PRIMARY KEY CHECK (world_id > 0),
    meaning  TEXT CHECK (meaning IS NULL OR length(meaning) > 0)
) STRICT;
