module
import Purelib.Data.Rat.Fraction
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Rational.Sector.Eight.Safe

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry.Rational.Sector.Eight

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

namespace Purelib.Geometry.Projective.SectorBlock.Safe.Basic

/-- The exact hypotheses consumed by the block-contraction calculation. -/
structure CompatibleTail (sector :
  Sector) (tail
  value : Data.Gaussian.Basic.Canonical) : Prop where
  /-- The exact cleared equation relating the tail, value, and sector representative. -/ equation :
    Canonical.gamma * tail * value = Canonical.gamma * tail * sector.rep + 1
  /-- The source value has squared norm at least one. -/ normLower : 1 ≤ Data.Gaussian.Norm.Basic.normSq value
  /-- The residual from the selected representative has squared norm below one half. -/
  safe : Geometry.Rational.Sector.Eight.Safe sector value

namespace CompatibleTail

/-- A safe compatible affine tail is nonzero. -/
theorem tail_nonzero {sector :
  Sector} {tail value : Data.Gaussian.Basic.Canonical}
    (compatible : CompatibleTail sector tail value) : tail ≠ 0 := by
  intro tailZero
  have equation := compatible.equation
  simp only [tailZero,
    Data.Gaussian.Basic.mul_zero,
    Data.Gaussian.Basic.zero_mul,
    Data.Gaussian.Basic.zero_add] at equation
  exact one_ne_zero equation.symm

/-- Safe compatibility gives the cleared residual identity `gamma*tail*(value-sector.rep)=1`. -/
theorem residual_equation {sector :
  Sector} {tail value : Data.Gaussian.Basic.Canonical}
    (compatible : CompatibleTail sector tail value) :
    Canonical.gamma * tail * (value - sector.rep) = 1 := by
  calc
    Canonical.gamma * tail * (value - sector.rep) =
        Canonical.gamma * tail * value - Canonical.gamma * tail * sector.rep :=
          by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
    _ = 1 := by
      rw [compatible.equation]
      apply Data.Gaussian.Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.one_re, Basic.one_im] <;>
          ring1

/-- The tail squared norm times twice the residual squared norm equals one. -/
theorem norm_equation {sector :
  Sector} {tail value : Data.Gaussian.Basic.Canonical}
    (compatible : CompatibleTail sector tail value) :
    (2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep)) * Data.Gaussian.Norm.Basic.normSq tail
      = 1 := by
  have normEquation := congrArg Data.Gaussian.Norm.Basic.normSq compatible.residual_equation
  rw [Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul, Constants.normSq_gamma,
    Data.Gaussian.Norm.Basic.normSq_one] at normEquation
  calc
    (2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep)) * Data.Gaussian.Norm.Basic.normSq tail
      =
        2 * Data.Gaussian.Norm.Basic.normSq tail * Data.Gaussian.Norm.Basic.normSq (value -
          sector.rep) := by ring1
    _ = 1 := normEquation

/-- A safe compatible tail has squared norm strictly greater than one.

The strict residual bound and the retained norm identity give the strict inequality. -/
theorem tail_norm_gt_one {sector :
  Sector} {tail value : Data.Gaussian.Basic.Canonical}
    (compatible : CompatibleTail sector tail value) :
    1 < Data.Gaussian.Norm.Basic.normSq tail := by
  have factorLess : 2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep) < (1 : Fraction.Rational) := by
    calc
      2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep) < 2 * (1 / 2 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (by decide) compatible.safe
      _ = 1 := by decide
  by_cases greater : 1 < Data.Gaussian.Norm.Basic.normSq tail
  · exact greater
  · have tailLe : Data.Gaussian.Norm.Basic.normSq tail ≤ 1 := le_of_not_gt greater
    have factorNonnegative : 0 ≤ 2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep) :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    have productLe :
        (2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep)) * Data.Gaussian.Norm.Basic.normSq
          tail ≤
          (2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep)) * 1 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct tailLe
        factorNonnegative
    have oneLtOne : (1 : Fraction.Rational) < 1 := by
      calc
        1 = (2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep)) *
          Data.Gaussian.Norm.Basic.normSq tail :=
          compatible.norm_equation.symm
        _ ≤ (2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep)) * 1 := productLe
        _ = 2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep) := by ring1
        _ < 1 := factorLess
    exact (lt_irrefl 1 oneLtOne).elim
end CompatibleTail

end Purelib.Geometry.Projective.SectorBlock.Safe.Basic

end
