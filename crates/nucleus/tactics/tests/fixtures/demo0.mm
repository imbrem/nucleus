$( demo0.mm — the introductory theory from the Metamath book.            $)
$( Exercises the uncompressed .mm subset: $c $v $f $e $a $p, ${ $},       $)
$( comments, and a normal RPN proof.                                      $)

$c 0 + = -> ( ) term wff |- $.
$v t r s P Q $.

$( Floating (typing) hypotheses. $)
tt $f term t $.
tr $f term r $.
ts $f term s $.
wp $f wff P $.
wq $f wff Q $.

$( Term and wff formation axioms. $)
tze $a term 0 $.
tpl $a term ( t + r ) $.
weq $a wff t = r $.
wim $a wff ( P -> Q ) $.

$( Logical axioms. $)
a1 $a |- ( t = r -> ( t = s -> r = s ) ) $.
a2 $a |- ( t + 0 ) = t $.

$( Modus ponens, scoped with its essential hypotheses. $)
${
  min $e |- P $.
  maj $e |- ( P -> Q ) $.
  mp $a |- Q $.
$}

$( The theorem: reflexivity of equality, |- t = t. $)
th1 $p |- t = t $=
  tt tze tpl tt weq tt tt weq tt a2 tt tze tpl
  tt weq tt tze tpl tt weq tt tt weq wim tt a2 tt tze tpl
  tt tt a1 mp mp $.
