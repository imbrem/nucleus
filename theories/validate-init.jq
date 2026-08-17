def declarations: .declarations;
def names: declarations | map(.[1]);

if .format != "nucleus.hol.init.array-v0" then
  error("unexpected init format")
elif (declarations | all(type == "array" and length == 6)) | not then
  error("every declaration must be a six-field array")
elif (declarations | all(.[0] as $class |
    ["type-family", "constant", "definition", "theorem", "section"] |
    index($class) != null)) | not then
  error("unknown declaration class")
elif (declarations | all(.[1] | type == "string" and length > 0)) | not then
  error("declaration names must be nonempty strings")
elif ((names | length) != (names | unique | length)) then
  error("declaration names must be unique")
elif (declarations | all(.[2] | type == "array" and
    all(type == "array" and length == 2 and (.[0] | type == "string")))) | not then
  error("parameters must be name/type pairs")
elif (declarations | all(.[5] | type == "array" and all(. | type == "string"))) | not then
  error("properties must be arrays of names")
elif (declarations | all(if .[0] == "section" then
    (.[2] | length == 0) and .[3] == null and .[4] == null
  else .[3] != null end)) | not then
  error("section and non-section declaration fields are inconsistent")
else
  {format, declarations: (declarations | length), namesUnique: true}
end
