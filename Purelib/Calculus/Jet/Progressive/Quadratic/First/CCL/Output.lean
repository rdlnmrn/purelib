module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Calculus.Jet.Progressive.Quadratic.First
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.CCL.Request

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.First
namespace FirstJet

open Purelib.Calculus.Jet.Progressive.Quadratic.First in
open Purelib.Data in
/-- A first jet satisfies the finite common-index request contract of its trace.

For a positive target and requested bit count, all five trace channels meet the shared radius bounds, retain the exact
quadratic law and extend their initialized emitted words by that count. -/
theorem bitstream_and_quadratic_law {increment : Nat →
  Gaussian.Basic.Canonical}
    (jet : FirstJet increment) (current : Nat) (target : Rat.Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    Trace.RequestContract jet.trace current target positive count :=
  jet.trace.bitstream_and_quadratic_law current target positive count

end FirstJet

end Purelib.Calculus.Jet.Progressive.Quadratic.First

end
