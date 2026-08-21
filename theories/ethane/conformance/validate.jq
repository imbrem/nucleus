def ids($xs): $xs | map(.id);
def unique_ids($xs): (ids($xs) | length) == (ids($xs) | unique | length);
def operation($registry; $id):
  $registry.operations[] | select(.id == $id);

$registry[0] as $registry
| $traces[0] as $traces
| if $registry.format != "nucleus.ethane.kernel-operations.v0" then
    error("unexpected operation registry format")
  elif $traces.format != "nucleus.ethane.kernel-traces.v0" then
    error("unexpected trace format")
  elif unique_ids($registry.operations) | not then
    error("operation ids must be unique")
  elif unique_ids($traces.traces) | not then
    error("trace ids must be unique")
  elif ($registry.operations | all(
      (.kind == "constructor" and (.oldArenas | length) == 0) or
      (.kind == "transition" and (.oldArenas | length) == 1) or
      (.kind == "multi-arena-transition" and (.oldArenas | length) > 1))) | not then
    error("operation kind and old arena count disagree")
  elif ($registry.operations | all(
      if .kind == "constructor" then .rust.receiver == "constructor"
      else .rust.receiver == "mutable"
      end)) | not then
    error("operation kind and Rust receiver disagree")
  elif ($registry.operations | all(
      if .kind == "constructor" then .lean.stateModel == "pure-arena-constructor"
      else .lean.stateModel == "pure-arena-transition"
      end)) | not then
    error("operation kind and Lean state model disagree")
  elif ($registry.operations | all(.fixtures as $fixtures |
      $fixtures | all(. as $fixture | ids($traces.traces) | index($fixture) != null))) | not then
    error("registry refers to a missing fixture")
  elif ($traces.traces | all(.operation as $id |
      ids($registry.operations) | index($id) != null)) | not then
    error("trace refers to an unknown operation")
  elif ($traces.traces | all(. as $trace |
      operation($registry; $trace.operation) as $operation |
      (($trace.oldArenas | length) == ($operation.oldArenas | length)) and
      ($trace.casUse == $operation.casUse) and
      ($operation.fixtures | index($trace.id) != null))) | not then
    error("trace does not match its operation contract")
  elif ($traces.traces | all(.expected.newArena.assumptions as $new |
      if (.oldArenas | length) == 0 then $new == []
      else all(.oldArenas[]; .assumptions == $new)
      end)) | not then
    error("initial fixtures must preserve their tracked assumptions")
  else
    {
      registry: $registry.format,
      traces: $traces.format,
      operations: ($registry.operations | length),
      fixtures: ($traces.traces | length),
      crossReferencesValid: true
    }
  end
