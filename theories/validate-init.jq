def declarations: .declarations;
def semantic: declarations | map(select(.[0] != "section"));
def names: semantic | map(.[1]);
def requiredInventory: [
  "true", "false", "not", "and", "or", "imp", "iff", "exists", "forall",
  "function.id", "function.comp", "set.empty", "set.univ", "set.mem",
  "set.subset", "set.inter", "set.union", "set.compl",
  "unit", "unit.star", "product", "coproduct", "option", "finSucc",
  "tuple2", "tuple3", "ind", "nat", "nat.rec", "nat.add", "nat.mul",
  "nat.pow", "nat.sub", "nat.le", "nat.lt", "nat.min", "nat.max",
  "list", "list.append", "list.map", "list.foldr", "list.length",
  "list.reverse", "list.mem", "list.all", "list.any", "list.head?",
  "list.tail?", "list.take", "list.drop", "nonemptyList", "vector", "tree",
  "int", "rat", "real", "number.natToInt", "number.intToRat",
  "number.ratToReal", "real.supremum"
];

if .format != "nucleus.hol.init.array-v0" then
  error("unexpected init format")
elif .status as $status |
    (["design-sketch", "checked", "complete"] | index($status)) == null then
  error("unexpected init status")
elif (declarations | all(type == "array" and length == 6)) | not then
  error("every declaration must be a six-field array")
elif (declarations | all(.[0] as $class |
    ["type-family", "constant", "definition", "theorem", "section"] |
    index($class) != null)) | not then
  error("unknown declaration class")
elif (declarations | all(.[1] | type == "string" and
    test("^[A-Za-z][A-Za-z0-9_.?-]*$"))) | not then
  error("declaration names must use the portable v0 name grammar")
elif ((names | length) != (names | unique | length)) then
  error("semantic declaration names must be unique")
elif (declarations | all(.[2] | type == "array" and
    all(type == "array" and length == 2 and (.[0] | type == "string" and
      test("^[A-Za-z][A-Za-z0-9_.?-]*$"))))) | not then
  error("parameters must be name/type pairs")
elif (declarations | all(.[2] | map(.[0]) as $parameters |
    ($parameters | length) == ($parameters | unique | length))) | not then
  error("parameter names must be locally unique")
elif (declarations | all(.[5] | type == "array" and all(. | type == "string"))) | not then
  error("properties must be arrays of names")
elif (declarations | all(if .[0] == "section" then
    (.[2] | length == 0) and .[3] == null and .[4] == null
  else .[3] != null end)) | not then
  error("section and non-section declaration fields are inconsistent")
elif (declarations | all(if .[0] == "constant" then .[4] == null else true end)) | not then
  error("primitive constants must have null bodies")
elif (requiredInventory - names | length) != 0 then
  error("required bootstrap inventory is missing: \((requiredInventory - names) | join(", "))")
elif (.status != "design-sketch" and
    (semantic | any((.[0] == "definition" or .[0] == "theorem") and .[4] == null))) then
  error("checked and complete manifests may not contain deferred definitions or theorems")
elif (.status == "complete" and
    ((semantic | map(select(.[0] == "theorem") | .[1])) as $theorems |
      (semantic | map(.[5][]?) | unique) - $theorems | length) != 0) then
  error("a complete manifest must declare every promised property as a theorem")
else
  {format, status, declarations: (declarations | length),
    semanticDeclarations: (semantic | length), namesUnique: true,
    requiredInventoryComplete: true}
end
