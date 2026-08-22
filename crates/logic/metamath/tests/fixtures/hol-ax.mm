$( hol-ax.mm -- the axioms of hol.mm, and nothing else.

   WHAT THIS IS.  A standalone Metamath database holding every axiomatic
   statement of hol.mm and the minimum scaffolding that makes those statements
   well-formed.  It has no proofs, so a verifier reports zero theorems; what it
   does report is that all 71 axioms parse and that every symbol, typecode and
   hypothesis they mention is declared.  Nucleus keeps it next to the Lean
   interpretation in lean/Nucleus/Nucleus/Metamath/HolMM/Axioms.lean: that
   interpretation is a reading of these axioms, and this is the artefact it is
   a reading of, checkable on its own terms by any Metamath verifier.

   DERIVED FROM.  hol.mm at revision b263d6e45b460ace961dea8839c953be7034adb4
   of https://github.com/metamath/set.mm (2356 lines, 96976 bytes).  hol.mm is
   Mario Carneiro's Metamath formalisation of higher-order logic, created
   7-Oct-2014; the accompanying paper is "Conversion of HOL Light proofs into
   Metamath", Journal of Formalized Reasoning 9(1), 2016, arXiv:1412.8091.
   Everything below this header -- the title comment, the section headers, and
   the documentation on every retained statement -- is upstream's text,
   unaltered.  Like hol.mm itself, this file is CC0 / public domain.

   WHAT COUNTS AS AN AXIOM.  All 71 of hol.mm's $a statements are kept.  In
   Metamath a $a *is* an axiom: it is asserted without proof, and the database
   has no other primitive way to say something is assumed.  Keeping only the
   ax-* family would be following a naming convention rather than a semantic
   one, and would go wrong twice.  The 21 syntax constructors (tv, ht, hb, hi,
   kc, kl, ke, kt, kbr, kct, tfal, tan, tne, tim, tal, tex, tor, teu, tf11,
   tfo, tat) are unproved assertions that the whole grammar rests on; without
   them no logical axiom has a well-formed statement.  The 11 df-* statements
   are unproved assertions that a newly declared constant equals a particular
   lambda term -- Metamath has no definitional mechanism that would make them
   conservative by construction, so they are extra axioms in exactly the sense
   the other $a statements are.  They also cannot be dropped without emptying
   out the rest: the statement of ax-inf mentions the constants introduced by
   df-ex, df-f11, df-fo, df-an and df-not, and that of ax-ac the ones
   introduced by df-al and df-im, so deleting the definitions would turn the
   axioms of infinity and choice into claims about uninterpreted constants.
   The three wff statements (wffMMJ2, wffMMJ2t, wffMMJ2d, which upstream calls
   "internal axiom for mmj2 use") are $a statements too and are kept for the
   same reason, though they are the one group a consumer can drop without
   changing what the |- typecode asserts -- drop the wff typecode declaration
   along with them if you do.

   The 71 in full, in source order:

     syntax (21)  tv ht hb hi kc kl ke kt kbr kct tfal tan tne tim tal tex tor
                  teu tf11 tfo tat
     mmj2 (3)     wffMMJ2 wffMMJ2t wffMMJ2d
     ax-* (36)    ax-syl ax-jca ax-simpl ax-simpr ax-id ax-trud ax-cb1 ax-cb2
                  ax-wctl ax-wctr ax-weq ax-refl ax-eqmp ax-ded ax-wct ax-wc
                  ax-ceq ax-wv ax-wl ax-beta ax-distrc ax-leq ax-distrl ax-wov
                  ax-eqtypi ax-eqtypri ax-hbl1 ax-17 ax-inst ax-wabs ax-wrep
                  ax-tdef ax-eta ax-wat ax-ac ax-inf
     df-* (11)    df-ov df-al df-fal df-an df-im df-not df-ex df-or df-eu
                  df-f11 df-fo

   WHAT ELSE IS KEPT, AND WHY IT HAS TO BE.  A .mm file does not parse unless
   every symbol and every typecode it uses has been declared, and an assertion
   mentioning a variable needs an active floating hypothesis for it.  So "just
   the axioms" necessarily drags in scaffolding: all 31 $c declarations, all 6
   $v declarations and all 18 $f floating hypotheses are kept, unchanged and in
   upstream order.  Kept too are the 52 $e essential hypotheses and 13 $d
   distinct-variable statements that are active where some retained axiom is
   stated, inside the 27 ${ ... $} blocks that hold them.  The $d conditions in
   particular are part of what an axiom asserts, not decoration: ax-17 without
   $d x A, or ax-inst without $d x y / $d y B / $d y S, is a different and
   unsound claim.

   WHAT WAS REMOVED.  All 151 $p theorems, with their proofs -- this file is
   the axiom set, not the development built on it.  With them goes the
   scaffolding that existed only for their sake: 219 of the 271 $e hypotheses,
   129 of the 142 $d statements, and 102 of the 129 ${ ... $} blocks.  None of
   that is reachable from a retained axiom.  A Metamath assertion's mandatory
   frame is fixed by the hypotheses and disjoint conditions active *at its own
   position*, so a block holding no $a, or any statement following the last $a
   in its block, cannot contribute to any axiom kept here.  Also removed is
   hol.mm's opening "what is Metamath" boilerplate, replaced by this header;
   its final "Rederive the Metamath axioms" section, which is $p only; and its
   trailing typesetting comment, 214 lines of HTML and LaTeX rendering
   definitions for the metamath.exe web-page generator, which say nothing
   about what the axioms mean.

   TWO CONSEQUENCES WORTH KNOWING.  First, retained comments still cross-refer
   to theorems that are gone -- the documentation of ax-trud points at tru, of
   ax-cb1 at wct, wctl and wctr, of ax-inst at ax17m.  The prose is upstream's
   and is left as it stands; it reads as a pointer back into hol.mm, which is
   what it is.  A markup checker will flag those five as unknown labels.
   Second, with the typesetting comment gone such a checker will also report a
   missing htmldef for every constant.  Neither affects structural
   verification: metamath-knife's --verify --grammar --parse-stmt reports no
   diagnostics on this file, which is to say the grammar it derives from these
   axioms parses all of them.

   HOW TO REGENERATE.  Against a fresh hol.mm, walk the token stream and:

     1. discard every $p statement;
     2. discard every ${ ... $} block that does not transitively contain a $a;
     3. in every surviving block, and at file scope, discard everything after
        the last surviving $a or surviving nested block;
     4. keep every $c, $v, $f, and every $e and $d that survives 2 and 3;
     5. carry each surviving statement's documentation comment with it, keep a
        section header if its section still holds anything, and replace the
        opening boilerplate with a header like this one.

   Steps 1 to 3 are what make the result faithful; steps 4 and 5 are what make
   it readable.  Check the result with

     cargo run -p covalence-logic-metamath --release --example validate -- \
       crates/logic/metamath/tests/fixtures/hol-ax.mm

   and, with a checkout of metamath/set.mm to hand,

     NUCLEUS_METAMATH_CORPUS=/path/to/set.mm-checkout cargo test \
       -p covalence-logic-metamath --test hol_ax -- --include-ignored

   which parses this file and upstream hol.mm side by side and asserts that
   every $a here has a conclusion, an essential-hypothesis list and a
   disjoint-variable set identical to its namesake there, and that no $a of
   hol.mm is missing.  That test is the real specification of this file; the
   five steps above are how it was produced.  For a second opinion from an
   implementation that is not ours,

     cargo install --git https://github.com/metamath/metamath-knife
     metamath-knife --verify --grammar --parse-stmt hol-ax.mm
$)

$( !
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Metamath source file for higher-order logic
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#

                           ~~ PUBLIC DOMAIN ~~
This work is waived of all rights, including copyright, according to the CC0
Public Domain Dedication.  https://creativecommons.org/publicdomain/zero/1.0/

Mario Carneiro - email: di.gama at gmail.com

$)

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Foundations
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $( Declare the primitive constant symbols for lambda calculus. $)
  $c var $.   $( Typecode for variables (syntax) $)
  $c type $.  $( Typecode for types (syntax) $)
  $c term $.  $( Typecode for terms (syntax) $)
  $c |- $.    $( Typecode for theorems (logical) $)
  $c : $.     $( Typehood indicator $)
  $c . $.     $( Separator $)
  $c |= $.    $( Context separator $)
  $c bool $.  $( Boolean type $)
  $c ind $.   $( 'Individual' type $)
  $c -> $.    $( Function type $)
  $c ( $.     $( Open parenthesis $)
  $c ) $.     $( Close parenthesis $)
  $c , $.     $( Context comma $)
  $c \ $.     $( Lambda expression $)
  $c = $.     $( Equality term $)
  $c T. $.    $( Truth term $)
  $c [ $.     $( Infix operator $)
  $c ] $.     $( Infix operator $)

  $v al $.  $( Greek alpha $)
  $v be $.  $( Greek beta $)
  $v ga $.  $( Greek gamma $)
  $v de $.  $( Greek delta $)

  $v x y z f g p q $.  $( Bound variables $)
  $v A B C F R S T $.  $( Term variables $)

  $( $j syntax 'var' 'type' 'term'; bound 'var'; $)

  $( Let variable ` al ` be a type. $)
  hal $f type al $.
  $( Let variable ` be ` be a type. $)
  hbe $f type be $.
  $( Let variable ` ga ` be a type. $)
  hga $f type ga $.
  $( Let variable ` de ` be a type. $)
  hde $f type de $.

  $( Let variable ` x ` be a var. $)
  vx $f var x $.
  $( Let variable ` y ` be a var. $)
  vy $f var y $.
  $( Let variable ` z ` be a var. $)
  vz $f var z $.
  $( Let variable ` f ` be a var. $)
  vf $f var f $.
  $( Let variable ` g ` be a var. $)
  vg $f var g $.
  $( Let variable ` p ` be a var. $)
  vp $f var p $.
  $( Let variable ` q ` be a var. $)
  vq $f var q $.

  $( Let variable ` A ` be a term. $)
  ta $f term A $.
  $( Let variable ` B ` be a term. $)
  tb $f term B $.
  $( Let variable ` C ` be a term. $)
  tc $f term C $.
  $( Let variable ` F ` be a term. $)
  tf $f term F $.
  $( Let variable ` R ` be a term. $)
  tr $f term R $.
  $( Let variable ` S ` be a term. $)
  ts $f term S $.
  $( Let variable ` T ` be a term. $)
  tt $f term T $.

  $( A var is a term. $)
  tv $a term x : al $.

  $( The type of all functions from type ` al ` to type ` be ` . $)
  ht $a type ( al -> be ) $.
  $( The type of booleans (true and false). $)
  hb $a type bool $.
  $( The type of individuals. $)
  hi $a type ind $.

  $( A combination (function application). $)
  kc $a term ( F T ) $.
  $( A lambda abstraction. $)
  kl $a term \ x : al . T $.
  $( The equality term. $)
  ke $a term = $.
  $( Truth term. $)
  kt $a term T. $.
  $( Infix operator. $)
  kbr $a term [ A F B ] $.
  $( Context operator. $)
  kct $a term ( A , B ) $.

  $c wff $.  $( Not used; for mmj2 compatibility $)

  $( $j syntax 'wff'; syntax '|-' as 'wff'; $)

  $( Internal axiom for mmj2 use. $)
  wffMMJ2 $a wff A |= B $.

  $( Internal axiom for mmj2 use. $)
  wffMMJ2t $a wff A : al $.

  ${
    ax-syl.1 $e |- R |= S $.
    ax-syl.2 $e |- S |= T $.
    $( Syllogism inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-syl $a |- R |= T $.
  $}

  ${
    ax-jca.1 $e |- R |= S $.
    ax-jca.2 $e |- R |= T $.
    $( Join common antecedents.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-jca $a |- R |= ( S , T ) $.
  $}

  ${
    ax-simpl.1 $e |- R : bool $.
    ax-simpl.2 $e |- S : bool $.
    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-simpl $a |- ( R , S ) |= R $.

    $( Extract an assumption from the context.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-simpr $a |- ( R , S ) |= S $.
  $}

  ${
    ax-id.1 $e |- R : bool $.
    $( The identity inference.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-id $a |- R |= R $.
  $}

  ${
    ax-trud.1 $e |- R : bool $.
    $( Deduction form of ~ tru .  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-trud $a |- R |= T. $.
  $}

  ${
    ax-cb.1 $e |- R |= A $.
    $( A context has type boolean.

       This and the next few axioms are not strictly necessary, and are
       conservative on any theorem for which every variable has a specified
       type, but by adding this axiom we can save some typehood hypotheses in
       many theorems.  The easy way to see that this axiom is conservative is
       to note that every axiom and inference rule that constructs a theorem of
       the form ` R |= A ` where ` R ` and ` A ` are type variables, also
       ensures that ` R : bool ` and ` A : bool ` .  Thus it is impossible to
       prove any theorem ` |- R |= A ` unless both ` |- R : bool ` and
       ` |- A : bool ` had been previously derived, so it is conservative to
       deduce ` |- R : bool ` from ` |- R |= A ` .  The same remark applies to
       the construction of the theorem ` ( A , B ) : bool ` - there is only one
       rule that creates a formula of this type, namely ~ wct , and it requires
       that ` A : bool ` and ` B : bool ` be previously established, so it is
       safe to reverse the process in ~ wctl and ~ wctr .  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    ax-cb1 $a |- R : bool $.

    $( A theorem has type boolean.  (This axiom is unnecessary; see ~ ax-cb1 .)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-cb2 $a |- A : bool $.
  $}

  ${
    wctl.1 $e |- ( S , T ) : bool $.
    $( Reverse closure for the type of a context.  (This axiom is unnecessary;
       see ~ ax-cb1 .)  Prefer ~ wctl .  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wctl $a |- S : bool $.

    $( Reverse closure for the type of a context.  (This axiom is unnecessary;
       see ~ ax-cb1 .)  Prefer ~ wctr .  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wctr $a |- T : bool $.
  $}

  $( The equality function has type ` al -> al -> bool ` , i.e. it is
     polymorphic over all types, but the left and right type must agree.
     (New usage is discouraged.)  (Contributed by Mario Carneiro,
     7-Oct-2014.) $)
  ax-weq $a |- = : ( al -> ( al -> bool ) ) $.

  ${
    ax-refl.1 $e |- A : al $.
    $( Reflexivity of equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-refl $a |- T. |= ( ( = A ) A ) $.
  $}

  ${
    ax-eqmp.1 $e |- R |= A $.
    ax-eqmp.2 $e |- R |= ( ( = A ) B ) $.
    $( Modus ponens for equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-eqmp $a |- R |= B $.
  $}

  ${
    ax-ded.1 $e |- ( R , S ) |= T $.
    ax-ded.2 $e |- ( R , T ) |= S $.
    $( Deduction theorem for equality.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-ded $a |- R |= ( ( = S ) T ) $.
  $}

  ${
    wct.1 $e |- S : bool $.
    wct.2 $e |- T : bool $.
    $( The type of a context.  (Contributed by Mario Carneiro, 7-Oct-2014.)
       (New usage is discouraged.) $)
    ax-wct $a |- ( S , T ) : bool $.
  $}

  ${
    wc.1 $e |- F : ( al -> be ) $.
    wc.2 $e |- T : al $.
    $( The type of a combination.  (Contributed by Mario Carneiro, 7-Oct-2014.)
       (New usage is discouraged.) $)
    ax-wc $a |- ( F T ) : be $.
  $}

  ${
    ax-ceq.1 $e |- F : ( al -> be ) $.
    ax-ceq.2 $e |- T : ( al -> be ) $.
    ax-ceq.3 $e |- A : al $.
    ax-ceq.4 $e |- B : al $.
    $( Equality theorem for combination.  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-ceq $a |- ( ( ( = F ) T ) , ( ( = A ) B ) ) |=
      ( ( = ( F A ) ) ( T B ) ) $.
  $}

  $( The type of a typed variable.  (New usage is discouraged.)  (Contributed
     by Mario Carneiro, 8-Oct-2014.) $)
  ax-wv $a |- x : al : al $.

  ${
    wl.1 $e |- T : be $.
    $( The type of a lambda abstraction.  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wl $a |- \ x : al . T : ( al -> be ) $.
  $}

  ${
    ax-beta.1 $e |- A : be $.
    $( Axiom of beta-substitution.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-beta $a |- T. |= ( ( = ( \ x : al . A x : al ) ) A ) $.

    ax-distrc.2 $e |- B : al $.
    ax-distrc.3 $e |- F : ( be -> ga ) $.
    $( Distribution of combination over substitution.  (Contributed by Mario
       Carneiro, 8-Oct-2014.) $)
    ax-distrc $a |- T. |= ( ( = ( \ x : al . ( F A ) B ) )
      ( ( \ x : al . F B ) ( \ x : al . A B ) ) ) $.
  $}

  ${
    $d x R $.
    ax-leq.1 $e |- A : be $.
    ax-leq.2 $e |- B : be $.
    ax-leq.3 $e |- R |= ( ( = A ) B ) $.
    $( Equality theorem for abstraction.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-leq $a |- R |= ( ( = \ x : al . A ) \ x : al . B ) $.
  $}

  ${
    $d x y $.  $d y B $.
    ax-distrl.1 $e |- A : ga $.
    ax-distrl.2 $e |- B : al $.
    $( Distribution of lambda abstraction over substitution.  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    ax-distrl $a |- T. |=
      ( ( = ( \ x : al . \ y : be . A B ) ) \ y : be . ( \ x : al . A B ) ) $.
  $}

  ${
    wov.1 $e |- F : ( al -> ( be -> ga ) ) $.
    wov.2 $e |- A : al $.
    wov.3 $e |- B : be $.
    $( Type of an infix operator.  (New usage is discouraged.)  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    ax-wov $a |- [ A F B ] : ga $.

    $( Infix operator.  This is a simple metamath way of cleaning up the syntax
       of all these infix operators to make them a bit more readable than the
       curried representation.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    df-ov $a |- T. |= ( ( = [ A F B ] ) ( ( F A ) B ) ) $.
  $}

  ${
    eqcomi.1 $e |- A : al $.
    eqcomi.2 $e |- R |= [ A = B ] $.
    $( Deduce equality of types from equality of expressions.  (This is
       unnecessary but eliminates a lot of hypotheses.)
       (New usage is discouraged.)  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-eqtypi $a |- B : al $.
  $}

  ${
    eqtypri.1 $e |- A : al $.
    eqtypri.2 $e |- R |= [ B = A ] $.
    $( Deduce equality of types from equality of expressions.  (This is
       unnecessary but eliminates a lot of hypotheses.)
       (New usage is discouraged.)  (Contributed by Mario Carneiro,
       7-Oct-2014.) $)
    ax-eqtypri $a |- B : al $.
  $}

  ${
    ax-hbl1.1 $e |- A : ga $.
    ax-hbl1.2 $e |- B : al $.
    $( ` x ` is bound in ` \ x A ` .  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-hbl1 $a |- T. |= [ ( \ x : al . \ x : be . A B ) = \ x : be . A ] $.
  $}

  ${
    $d x A $.
    ax-17.1 $e |- A : be $.
    ax-17.2 $e |- B : al $.
    $( If ` x ` does not appear in ` A ` , then any substitution to ` A `
       yields ` A ` again, i.e. ` \ x A ` is a constant function.  (Contributed
       by Mario Carneiro, 8-Oct-2014.) $)
    ax-17 $a |- T. |= [ ( \ x : al . A B ) = A ] $.
  $}

  ${
    $d x y $.  $d y B $.  $d y S $.
    ax-inst.1 $e |- R |= A $.
    ax-inst.2 $e |- T. |= [ ( \ x : al . B y : al ) = B ] $.
    ax-inst.3 $e |- T. |= [ ( \ x : al . S y : al ) = S ] $.
    ax-inst.4 $e |- [ x : al = C ] |= [ A = B ] $.
    ax-inst.5 $e |- [ x : al = C ] |= [ R = S ] $.
    $( Instantiate a theorem with a new term.  The second and third hypotheses
       are the HOL equivalent of set.mm "effectively not free in" predicate
       (see set.mm's ax-17, or ~ ax17m ).  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    ax-inst $a |- S |= B $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Add propositional calculus definitions
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c F. $.   $( Contradiction term $)
  $c /\ $.   $( Conjunction term $)
  $c ~ $.    $( Negation term $)
  $c ==> $.  $( Implication term $)
  $c ! $.    $( For all term $)
  $c ? $.    $( There exists term $)
  $c \/ $.   $( Disjunction term $)
  $c ?! $.   $( There exists unique term $)

  $( Contradiction term. $)
  tfal $a term F. $.
  $( Conjunction term. $)
  tan $a term /\ $.
  $( Negation term. $)
  tne $a term ~ $.
  $( Implication term. $)
  tim $a term ==> $.
  $( For all term. $)
  tal $a term ! $.
  $( There exists term. $)
  tex $a term ? $.
  $( Disjunction term. $)
  tor $a term \/ $.
  $( There exists unique term. $)
  teu $a term ?! $.

  ${
    $d f p q x y $.
    $( Define the for all operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-al $a |- T. |=
      [ ! = \ p : ( al -> bool ) . [ p : ( al -> bool ) = \ x : al . T. ] ] $.

    $( Define the constant false.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-fal $a |- T. |= [ F. = ( ! \ p : bool . p : bool ) ] $.

    $( Define the 'and' operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-an $a |- T. |=
        [ /\ = \ p : bool . \ q : bool . [ \ f : ( bool -> ( bool -> bool ) ) .
        [ p : bool f : ( bool -> ( bool -> bool ) ) q : bool ] =
          \ f : ( bool -> ( bool -> bool ) ) .
            [ T. f : ( bool -> ( bool -> bool ) ) T. ] ] ] $.

    $( Define the implication operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-im $a |- T. |= [ ==> =
      \ p : bool . \ q : bool . [ [ p : bool /\ q : bool ] = p : bool ] ] $.

    $( Define the negation operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-not $a |- T. |= [ ~ = \ p : bool . [ p : bool ==> F. ] ] $.

    $( Define the existence operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-ex $a |- T. |= [ ? = \ p : ( al -> bool ) .
      ( ! \ q : bool . [ ( ! \ x : al .
        [ ( p : ( al -> bool ) x : al ) ==> q : bool ] ) ==> q : bool ] ) ] $.

    $( Define the 'or' operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-or $a |- T. |= [ \/ = \ p : bool . \ q : bool . ( ! \ x : bool .
        [ [ p : bool ==> x : bool ] ==>
          [ [ q : bool ==> x : bool ] ==> x : bool ] ] ) ] $.

    $( Define the 'exists unique' operator.  (Contributed by Mario Carneiro,
       8-Oct-2014.) $)
    df-eu $a |- T. |= [ ?! = \ p : ( al -> bool ) .
      ( ? \ y : al . ( ! \ x : al .
        [ ( p : ( al -> bool ) x : al ) = [ x : al = y : al ] ] ) ) ] $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Type definition mechanism
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c typedef $.

  $( Internal axiom for mmj2 use. $)
  wffMMJ2d $a wff typedef al ( A , B ) C $.

  ${
    $d x A $.  $d x R $.  $d x F $.
    ax-tdef.1 $e |- B : al $.
    ax-tdef.2 $e |- F : ( al -> bool ) $.
    ax-tdef.3 $e |- T. |= ( F B ) $.
    ax-tdef.4 $e |- typedef be ( A , R ) F $.
    $( Type of the abstraction function.  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wabs $a |- A : ( al -> be ) $.

    $( Type of the representation function.  (New usage is discouraged.)
       (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-wrep $a |- R : ( be -> al ) $.

    $( The type definition axiom.  The last hypothesis corresponds to the
       actual definition one wants to make; here we are defining a new type
       ` be ` and the definition will provide us with pair of bijections
       ` A , R ` mapping the new type ` be ` to the subset of the old type
       ` al ` such that ` F x ` is true.  In order for this to be a valid
       (conservative) extension, we must ensure that the new type is nonempty,
       and for that purpose we need a witness ` B ` that ` F ` is not always
       false.  (Contributed by Mario Carneiro, 8-Oct-2014.) $)
    ax-tdef $a |- T. |= ( ( ! \ x : be . [ ( A ( R x : be ) ) = x : be ] ) ,
      ( ! \ x : al . [ ( F x : al ) = [ ( R ( A x : al ) ) = x : al ] ] ) ) $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Extensionality
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  ${
    $d f x $.
    $( The eta-axiom: a function is determined by its values.  (Contributed by
       Mario Carneiro, 8-Oct-2014.) $)
    ax-eta $a |- T. |= ( ! \ f : ( al -> be ) .
      [ \ x : al . ( f : ( al -> be ) x : al ) = f : ( al -> be ) ] ) $.
  $}

$(
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
  Axioms of infinity and choice
#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#*#
$)

  $c 1-1 $.   $( One-to-one function $)
  $c onto $.  $( Onto function $)
  $c @ $.     $( Indefinite descriptor $)

  $( One-to-one function. $)
  tf11 $a term 1-1 $.
  $( Onto function. $)
  tfo $a term onto $.
  $( Indefinite descriptor. $)
  tat $a term @ $.

  $( The type of the indefinite descriptor.  (New usage is discouraged.)
     (Contributed by Mario Carneiro, 10-Oct-2014.) $)
  ax-wat $a |- @ : ( ( al -> bool ) -> al ) $.

  ${
    $d f p x y $.
    $( Define a one-to-one function.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    df-f11 $a |- T. |= [ 1-1 = \ f : ( al -> be ) .
      ( ! \ x : al . ( ! \ y : al .
        [ [ ( f : ( al -> be ) x : al ) = ( f : ( al -> be ) y : al ) ] ==>
          [ x : al = y : al ] ] ) ) ] $.

    $( Define an onto function.  (Contributed by Mario Carneiro,
       10-Oct-2014.) $)
    df-fo $a |- T. |= [ onto = \ f : ( al -> be ) . ( ! \ y : be .
      ( ? \ x : al . [ y : be = ( f : ( al -> be ) x : al ) ] ) ) ] $.

    $( Defining property of the indefinite descriptor: it selects an element
       from any type.  This is equivalent to global choice in ZF. (Contributed
       by Mario Carneiro, 10-Oct-2014.) $)
    ax-ac $a |- T. |= ( ! \ p : ( al -> bool ) .
      ( ! \ x : al . [ ( p : ( al -> bool ) x : al ) ==>
        ( p : ( al -> bool ) ( @ p : ( al -> bool ) ) ) ] ) ) $.
  $}

  $( The axiom of infinity: the set of "individuals" is not Dedekind-finite.
     Using the axiom of choice, we can show that this is equivalent to an
     embedding of the natural numbers in ` ind ` .  (Contributed by Mario
     Carneiro, 10-Oct-2014.) $)
  ax-inf $a |- T. |= ( ? \ f : ( ind -> ind ) .
    [ ( 1-1 f : ( ind -> ind ) ) /\ ( ~ ( onto f : ( ind -> ind ) ) ) ] ) $.
