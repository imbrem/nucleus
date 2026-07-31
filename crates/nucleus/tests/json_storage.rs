use covalence_lib_hash::O256;
use covalence_lib_sqlite as sqlite;
use sqlite::OptionalExtension;

const SCHEMA: &str = include_str!("../sql/experimental/json_storage.sql");

const REF: i64 = 16;
const IMPORT: i64 = 17;
const BYTES: i64 = 18;

#[derive(Debug, Eq, PartialEq)]
struct Node {
    tag: i64,
    children: Vec<i64>,
    atom: Option<Vec<u8>>,
}

trait Ast {
    fn node(&self, id: i64) -> sqlite::Result<Node>;
    fn bytes(&self, id: i64) -> sqlite::Result<Option<Vec<u8>>>;
    fn import(&self, id: i64) -> sqlite::Result<Option<(Vec<u8>, i64)>>;
}

struct JsonbAst<'connection>(&'connection sqlite::Connection);
struct DagAst<'connection>(&'connection sqlite::Connection);

impl Ast for JsonbAst<'_> {
    fn node(&self, id: i64) -> sqlite::Result<Node> {
        let (tag, atom) = self.0.query_row(
            "SELECT tag,
                    CASE WHEN tag = 1
                         THEN CAST(json_extract(body, '$[1]') AS BLOB)
                    END
             FROM json_def WHERE id = ?1",
            [id],
            |row| Ok((row.get(0)?, row.get(1)?)),
        )?;
        let mut statement = self.0.prepare(
            "SELECT target_id FROM json_dep
             WHERE owner_id = ?1 AND source_id IS NULL
             ORDER BY position",
        )?;
        let children = statement
            .query_map([id], |row| row.get(0))?
            .collect::<sqlite::Result<Vec<_>>>()?;
        Ok(Node {
            tag,
            children,
            atom,
        })
    }

    fn bytes(&self, id: i64) -> sqlite::Result<Option<Vec<u8>>> {
        self.0
            .query_row(
                "SELECT b.data
                 FROM json_def AS d
                 JOIN ast_blob AS b ON b.id = json_extract(d.body, '$[1]')
                 WHERE d.id = ?1 AND d.tag = ?2",
                (id, BYTES),
                |row| row.get(0),
            )
            .optional()
    }

    fn import(&self, id: i64) -> sqlite::Result<Option<(Vec<u8>, i64)>> {
        self.0
            .query_row(
                "SELECT s.snapshot_hash, json_extract(d.body, '$[2]')
                 FROM json_def AS d
                 JOIN ast_source AS s ON s.id = json_extract(d.body, '$[1]')
                 WHERE d.id = ?1 AND d.tag = ?2",
                (id, IMPORT),
                |row| Ok((row.get(0)?, row.get(1)?)),
            )
            .optional()
    }
}

impl Ast for DagAst<'_> {
    fn node(&self, id: i64) -> sqlite::Result<Node> {
        let (tag, atom) = self.0.query_row(
            "SELECT tag, atom FROM dag_node WHERE id = ?1",
            [id],
            |row| Ok((row.get(0)?, row.get(1)?)),
        )?;
        let mut statement = self
            .0
            .prepare("SELECT target_id FROM dag_edge WHERE owner_id = ?1 ORDER BY position")?;
        let children = statement
            .query_map([id], |row| row.get(0))?
            .collect::<sqlite::Result<Vec<_>>>()?;
        Ok(Node {
            tag,
            children,
            atom,
        })
    }

    fn bytes(&self, id: i64) -> sqlite::Result<Option<Vec<u8>>> {
        self.0
            .query_row(
                "SELECT b.data
                 FROM dag_node AS n JOIN ast_blob AS b ON b.id = n.blob_id
                 WHERE n.id = ?1 AND n.tag = ?2",
                (id, BYTES),
                |row| row.get(0),
            )
            .optional()
    }

    fn import(&self, id: i64) -> sqlite::Result<Option<(Vec<u8>, i64)>> {
        self.0
            .query_row(
                "SELECT s.snapshot_hash, i.target_id
                 FROM dag_import AS i
                 JOIN ast_source AS s ON s.id = i.source_id
                 WHERE i.node_id = ?1",
                [id],
                |row| Ok((row.get(0)?, row.get(1)?)),
            )
            .optional()
    }
}

fn database() -> sqlite::Result<sqlite::Connection> {
    let connection = sqlite::Connection::open_in_memory()?;
    connection.execute_batch(SCHEMA)?;
    Ok(connection)
}

fn insert_fixtures(connection: &sqlite::Connection) -> sqlite::Result<()> {
    let source_hash = O256::from_bytes(b"foreign snapshot");
    let blob = b"\0binary\xff";
    let blob_hash = O256::from_bytes(blob);
    connection.execute(
        "INSERT INTO ast_source VALUES (1, ?1, 'fixture/v0')",
        [source_hash.as_ref()],
    )?;
    connection.execute(
        "INSERT INTO ast_blob VALUES (1, ?1, ?2)",
        (blob_hash.as_ref(), blob.as_slice()),
    )?;

    for (id, body) in [
        (1, "[0]"),
        (2, "[1,\"x\"]"),
        (3, "[2,[16,2],[16,1]]"),
        (4, "[2,[16,2],[16,2]]"),
        (5, "[18,1]"),
        (6, "[17,1,57]"),
    ] {
        connection.execute(
            "INSERT INTO json_def(id, body) VALUES (?1, jsonb(?2))",
            (id, body),
        )?;
    }
    connection.execute(
        "INSERT INTO json_dep(owner_id, position, source_id, target_id)
         SELECT d.id,
                CAST(j.key AS INTEGER),
                CASE json_extract(j.value, '$[0]')
                    WHEN ?2 THEN json_extract(j.value, '$[1]')
                END,
                CASE json_extract(j.value, '$[0]')
                    WHEN ?1 THEN json_extract(j.value, '$[1]')
                    WHEN ?2 THEN json_extract(j.value, '$[2]')
                END
         FROM json_def AS d, json_each(d.body) AS j
         WHERE j.type = 'array'
           AND json_extract(j.value, '$[0]') IN (?1, ?2)",
        (REF, IMPORT),
    )?;

    connection.execute_batch(
        "INSERT INTO dag_node(id, tag, atom, blob_id) VALUES
            (1, 0, NULL, NULL),
            (2, 1, x'78', NULL),
            (3, 2, NULL, NULL),
            (4, 2, NULL, NULL),
            (5, 18, NULL, 1),
            (6, 17, NULL, NULL);
         INSERT INTO dag_edge VALUES
            (3, 0, 2), (3, 1, 1),
            (4, 0, 2), (4, 1, 2);
         INSERT INTO dag_import VALUES (6, 1, 57);",
    )
}

#[test]
fn tagged_jsonb_and_normalized_dag_expose_the_same_nodes() {
    let connection = database().unwrap();
    insert_fixtures(&connection).unwrap();
    let json = JsonbAst(&connection);
    let dag = DagAst(&connection);

    for id in 1..=4 {
        assert_eq!(json.node(id).unwrap(), dag.node(id).unwrap());
    }
    assert_ne!(json.node(3).unwrap(), json.node(4).unwrap());
    assert_eq!(json.bytes(5).unwrap(), dag.bytes(5).unwrap());
    assert_eq!(json.import(6).unwrap(), dag.import(6).unwrap());
}

#[test]
fn jsonb_validity_is_only_structural_validity() {
    let connection = database().unwrap();
    insert_fixtures(&connection).unwrap();

    // A well-formed tagged value may still contain a dangling logical REF.
    connection
        .execute(
            "INSERT INTO json_def(id, body) VALUES (99, jsonb('[2,[16,999],[16,1]]'))",
            [],
        )
        .unwrap();
    let dangling = connection
        .query_row(
            "SELECT count(*)
             FROM json_tree((SELECT body FROM json_def WHERE id = 99)) AS j
             WHERE j.type = 'array'
               AND json_extract(j.value, '$[0]') = ?1
               AND NOT EXISTS (
                   SELECT 1 FROM json_def
                   WHERE id = json_extract(j.value, '$[1]')
               )",
            [REF],
            |row| row.get::<_, i64>(0),
        )
        .unwrap();
    assert_eq!(dangling, 1);

    assert!(
        connection
            .execute("INSERT INTO json_def(id, body) VALUES (100, x'00ff')", [])
            .is_err()
    );
}

#[test]
fn lean_ndjson_keeps_source_bytes_and_projects_hot_fields() {
    let connection = database().unwrap();
    let line = br#"{"kind":"expr","id":12,"tag":"app","fn":4,"arg":9}"#;
    let source_hash = O256::from_bytes(line);
    connection
        .execute(
            "INSERT INTO ast_source VALUES (1, ?1, 'lean-ndjson/v0')",
            [source_hash.as_ref()],
        )
        .unwrap();
    connection
        .execute(
            "INSERT INTO ast_blob VALUES (1, ?1, ?2)",
            (source_hash.as_ref(), line.as_slice()),
        )
        .unwrap();
    connection
        .execute(
            "INSERT INTO lean_record(ordinal, raw, source_id)
             VALUES (1, jsonb(?1), 1)",
            [line.as_slice()],
        )
        .unwrap();
    connection
        .execute(
            "INSERT INTO lean_expr(expr_id, tag, arg0, arg1)
             SELECT json_extract(raw, '$.id'),
                    json_extract(raw, '$.tag'),
                    json_extract(raw, '$.fn'),
                    json_extract(raw, '$.arg')
             FROM lean_record WHERE ordinal = 1",
            [],
        )
        .unwrap();

    let projected = connection
        .query_row(
            "SELECT tag, arg0, arg1 FROM lean_expr WHERE expr_id = 12",
            [],
            |row| {
                Ok((
                    row.get::<_, String>(0)?,
                    row.get::<_, i64>(1)?,
                    row.get::<_, i64>(2)?,
                ))
            },
        )
        .unwrap();
    assert_eq!(projected, (String::from("app"), 4, 9));
    let exact_source = connection
        .query_row("SELECT data FROM ast_blob WHERE id = 1", [], |row| {
            row.get::<_, Vec<u8>>(0)
        })
        .unwrap();
    assert_eq!(exact_source, line);
}
