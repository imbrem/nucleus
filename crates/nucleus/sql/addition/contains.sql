SELECT EXISTS(
    SELECT 1 FROM {table}
    WHERE tm = ?1 AND lhs = ?2 AND rhs = ?3
)
