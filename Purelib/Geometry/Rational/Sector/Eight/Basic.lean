module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Completed-block contraction for redundant CCL choices

The canonical contraction theorem stores annulus and disjoint-sector proofs.
For arithmetic output those hypotheses are unnecessarily strong.  A block is
sound and has the same contraction factor whenever its displayed value has
norm at least one and its chosen representative has residual quadrance below
one half.

This parallel structure deliberately leaves the canonical theorem and parser
unchanged.  `ofCanonical` embeds every old compatible block into this wider
arithmetic layer.
-/

namespace Purelib.Geometry.Rational.Sector.Eight.Basic

/-! ## Projective terminal tails -/

/-- Every displayed sector representative has squared norm at least one. -/
theorem rep_norm_lower (sector :
  Data.ComplexContinuedFraction.Encoding.Sector) :
    (1 : Fraction.Rational) ≤ Data.Gaussian.Norm.Basic.normSq sector.rep := by
  cases sector <;> decide

end Purelib.Geometry.Rational.Sector.Eight.Basic

end
