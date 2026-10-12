module
public import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

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

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace
section Trace

/-! ## A genuinely changing progressive witness -/

open Purelib.Calculus.Jet.Quadratic.Basic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Certify the identity expansion at one displayed increment.

The base, remainder and factor are zero, the slope is one, and the output field is exactly the supplied increment. -/
def identityCertificate (increment :
  Basic.Canonical) : Certificate increment :=
  { base := 0
    slope := 1
    output := increment
    remainder := 0
    expansion := by
      apply Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.zero_re, Basic.zero_im,
          Basic.one_re, Basic.one_im] <;> ring1
    factor := 0
    factor_nonneg := le_rfl
    remainder_le := by
      rw [Basic.Canonical.normSq_zero, Fraction.Field.zero_mul_direct] }
end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace

end
