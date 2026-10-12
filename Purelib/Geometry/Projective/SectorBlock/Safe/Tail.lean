module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation

import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Data.Rat.Fraction
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Rat.BalancedRatio
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
public import Purelib.Geometry.Projective.Line.Matrix
public import Purelib.Geometry.Projective.SectorBlock.Basic
public import Purelib.Geometry.Projective.SectorBlock.Safe.Basic
import Purelib.Geometry.Projective.SectorBlock.Safe.Contraction
import Purelib.Geometry.Rational.Sector.Eight.Safe
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.Rat

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.SectorBlock

open Purelib.Geometry.Projective.SectorBlock.Safe

open Purelib.Geometry.Rational.Sector.Eight

section
public section

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

namespace Purelib.Geometry.Projective.SectorBlock.Safe

set_option genInjectivity false in
/-- A redundant compatible tail is either affine or the formal projective terminal. The latter is the finite semantics
of an indefinitely padded exact residual. -/
inductive Tail (sector : Data.ComplexContinuedFraction.Encoding.Sector) where
  /-- The exact projective terminal continuation. -/ | omega
  /-- Retain an affine tail, its source value, and their safe compatibility certificate. -/ | affine (tail value :
    Data.Gaussian.Basic.Canonical) (compatible : Safe.Basic.CompatibleTail sector tail value)

constructive_injectivity Tail

namespace Tail.affine

end Tail.affine

namespace Tail

/-- Read the homogeneous point of the affine continuation or formal terminal. -/
@[expose] def point {sector : Data.ComplexContinuedFraction.Encoding.Sector} :
  Tail sector → GaussianLine
  | .omega => Proj.omega
  | .affine tail _ _ => Proj.affine tail

/-- A redundant safe value has a total projective continuation: exact sector representatives use `ω`, while every
nonzero residual uses its displayed affine reciprocal. The branch is a rational equality test on the supplied finite
value, not an equality test on a completed name. -/
@[expose] def ofSafe (sector : Data.ComplexContinuedFraction.Encoding.Sector) (value
  : Data.Gaussian.Basic.Canonical)
    (normLower : 1 ≤ Data.Gaussian.Norm.Basic.normSq value)
    (safe : Rational.Sector.Eight.Safe sector value) : Tail sector := by
  let residual := value - sector.rep
  if residualZero : residual = 0 then
    exact .omega
  else
    let tail := (Data.Gaussian.Basic.Canonical.gamma * residual)⁻¹
    have productNonzero : Data.Gaussian.Basic.Canonical.gamma * residual ≠ 0 :=
      Data.Gaussian.Field.mul_ne_zero_direct (by decide) residualZero
    have cancellation : Data.Gaussian.Basic.Canonical.gamma * tail * residual = 1 := by
      calc
        Data.Gaussian.Basic.Canonical.gamma * tail * residual = (Data.Gaussian.Basic.Canonical.gamma * residual) *
          (Data.Gaussian.Basic.Canonical.gamma * residual)⁻¹ := by
          apply Data.Gaussian.Basic.ext <;>
            simp only [-eq_self, -iff_self, tail, Purelib.Data.Gaussian.Basic.mul_re,
              Purelib.Data.Gaussian.Basic.mul_im] <;> ring1
        _ = 1 :=
          Data.Gaussian.Basic.Canonical.mul_inv_cancel _ productNonzero
    exact .affine tail value
      { equation := by
          have decomposition : value = sector.rep + residual := by
            apply Data.Gaussian.Basic.ext <;>
              simp only [-eq_self, -iff_self, residual, Purelib.Data.Gaussian.Basic.sub_re,
                Purelib.Data.Gaussian.Basic.sub_im, Purelib.Data.Gaussian.Basic.add_re,
                Purelib.Data.Gaussian.Basic.add_im] <;> ring1
          calc
            Data.Gaussian.Basic.Canonical.gamma * tail * value =
                Data.Gaussian.Basic.Canonical.gamma * tail * (sector.rep + residual) := by rw [decomposition]
            _ = Data.Gaussian.Basic.Canonical.gamma * tail * sector.rep + Data.Gaussian.Basic.Canonical.gamma * tail *
              residual := by
              apply Data.Gaussian.Basic.ext <;>
                simp only [-eq_self, -iff_self, Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im,
                  Purelib.Data.Gaussian.Basic.mul_re, Purelib.Data.Gaussian.Basic.mul_im] <;> ring1
            _ = Data.Gaussian.Basic.Canonical.gamma * tail * sector.rep + 1 := by rw [cancellation]
        normLower := normLower
        safe := safe }

/-- The projective continuation models exactly the displayed normalized value in both its affine and terminal branches.
-/
@[expose] def ModelsValue {sector : Data.ComplexContinuedFraction.Encoding.Sector}
  (tail : Tail sector)
    (value : Data.Gaussian.Basic.Canonical) : Prop :=
  match tail with
  | .omega => value = sector.rep
  | .affine _ storedValue _ => storedValue = value

/-- The continuation constructed from a safe value models that exact retained value. -/
theorem ofSafe_models (sector : Data.ComplexContinuedFraction.Encoding.Sector)
  (value : Data.Gaussian.Basic.Canonical)
    (normLower : 1 ≤ Data.Gaussian.Norm.Basic.normSq value)
    (safe : Rational.Sector.Eight.Safe sector value) :
    (ofSafe sector value normLower safe).ModelsValue value := by
  unfold ofSafe
  dsimp only
  split
  · rename_i residualZero
    simpa only [ModelsValue] using Group.eq_of_sub_eq_zero residualZero
  · simp only [-eq_self, -iff_self, ModelsValue]
    rfl

/-- The total tail has the single homogeneous formula `[1 : γ(value-s)]`. This avoids branching on residual equality
when a progressive cursor carries the projective tail through unary padding. -/
theorem ofSafe_point_equivalent_homogeneous
    (sector : Data.ComplexContinuedFraction.Encoding.Sector) (value : Data.Gaussian.Basic.Canonical)
    (normLower : 1 ≤ Data.Gaussian.Norm.Basic.normSq value)
    (safe : Rational.Sector.Eight.Safe sector value) :
    (ofSafe sector value normLower safe).point.Equivalent
      ⟨1, Data.Gaussian.Basic.Canonical.gamma * (value - sector.rep)⟩ := by
  unfold ofSafe
  dsimp only
  split
  · rename_i residualZero
    simp only [-eq_self, -iff_self, point, Proj.Equivalent, Proj.omega]
    rw [residualZero, Data.Gaussian.Basic.mul_zero]
  · rename_i residualNonzero
    let residual := value - sector.rep
    let product := Data.Gaussian.Basic.Canonical.gamma * residual
    have productNonzero : product ≠ 0 :=
      Data.Gaussian.Field.mul_ne_zero_direct (by decide) residualNonzero
    change product⁻¹ * product = 1 * 1
    rw [Data.Gaussian.Basic.mul_one]
    exact Data.Gaussian.Basic.Canonical.inv_mul_cancel
      product productNonzero

/-- Every redundant tail has a nonzero homogeneous coordinate. -/
theorem point_valid {sector : Data.ComplexContinuedFraction.Encoding.Sector} (tail :
  Tail sector) :
    Proj.HasNonzeroCoordinate tail.point := by
  cases tail with
  | omega => exact Proj.omega_hasNonzeroCoordinate
  | affine value source compatible =>
      exact Proj.affine_hasNonzeroCoordinate value

/-- Full redundant contraction, including all affine/projective terminal pairs. -/
theorem contraction {sector : Data.ComplexContinuedFraction.Encoding.Sector} (scale
  : Data.Gaussian.Basic.Canonical) (scaleNonzero : scale ≠ 0)
    (left right : Tail sector) :
    Chordal.Basic.chordalSq (Line.Matrix.act (SectorBlock.Basic.block scale sector) left.point)
        (Line.Matrix.act (SectorBlock.Basic.block scale sector) right.point) ≤
      BalancedRatio.factor scale * Chordal.Basic.chordalSq left.point right.point := by
  cases left with
  | omega =>
      cases right with
      | omega =>
          simp only [-eq_self, -iff_self, point]
          rw [Chordal.Basic.chordalSq_eq_zero_of_equivalent rfl,
            Chordal.Basic.chordalSq_eq_zero_of_equivalent rfl,
            Fraction.Field.mul_zero_direct]
      | affine tail value compatible =>
          simp only [-eq_self, -iff_self, point]
          rw [Chordal.Basic.chordalSq_comm
            (Line.Matrix.act (SectorBlock.Basic.block scale sector) Proj.omega)
            (Line.Matrix.act (SectorBlock.Basic.block scale sector) (Proj.affine tail)),
            Chordal.Basic.chordalSq_comm Proj.omega (Proj.affine tail)]
          exact Contraction.affine_omega_contraction scaleNonzero compatible
  | affine tail value compatible =>
      cases right with
      | omega =>
          simp only [-eq_self, -iff_self, point]
          exact Contraction.affine_omega_contraction scaleNonzero compatible
      | affine rightTail rightValue rightCompatible =>
          simp only [-eq_self, -iff_self, point]
          exact Contraction.affine_contraction scaleNonzero compatible rightCompatible

/-- A nonzero scaled block contracts squared-chordal distance between redundant compatible tails by at most one half. -/
theorem contraction_half {sector : Data.ComplexContinuedFraction.Encoding.Sector}
  (scale : Data.Gaussian.Basic.Canonical)
    (scaleNonzero : scale ≠ 0) (left right : Tail sector) :
    Chordal.Basic.chordalSq (Line.Matrix.act (SectorBlock.Basic.block scale sector) left.point)
        (Line.Matrix.act (SectorBlock.Basic.block scale sector) right.point) ≤
      (1 / 2 : Fraction.Rational) * Chordal.Basic.chordalSq left.point right.point := by
  exact (contraction scale scaleNonzero left right).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (BalancedRatio.factor_le_half scale)
      (Chordal.Basic.chordalSq_nonneg _ _))

end Tail

end Purelib.Geometry.Projective.SectorBlock.Safe

end

end
