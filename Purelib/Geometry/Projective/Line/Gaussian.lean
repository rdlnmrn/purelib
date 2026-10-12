module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
public import Purelib.Geometry.Projective.Line.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

section
@[expose] public section

/-!
# Choice-free projective quadrance over constructive Gaussian fractions

This is the finite projective geometry used by the constructive CCL layer.  It
is deliberately separate from `Purelib.CCL.Geometry.Chordal`, whose coordinates are Mathlib's
`Rat`.  Every coordinate here is an explicit quotient of an integer numerator
and a positive integer denominator.
-/

section

section

namespace Purelib.Geometry.Projective.Line.Gaussian.Proj

/-- Multiply both homogeneous coordinates by a constructive Gaussian scalar. -/
def scale (scalar : Data.Gaussian.Basic.Canonical) (x :
  GaussianLine) : GaussianLine :=
  ⟨scalar * x.p, scalar * x.q⟩

/-- Finite validity predicate for a homogeneous coordinate pair. -/
def HasNonzeroCoordinate (x : GaussianLine)
  : Prop :=
  x.p ≠ 0 ∨ x.q ≠ 0

/-- Decide projective validity by testing the two Gaussian coordinates for zero. -/
instance hasNonzeroCoordinateDecidable (x :
  GaussianLine) :
    Decidable (HasNonzeroCoordinate x) := by
  unfold HasNonzeroCoordinate
  infer_instance

/-- Every affine homogeneous pair is valid because its denominator is one. -/
theorem affine_hasNonzeroCoordinate (z :
  Data.Gaussian.Basic.Canonical) :
    HasNonzeroCoordinate (Proj.affine z : GaussianLine) :=
  Or.inr one_ne_zero

/-- The terminal homogeneous pair is valid because its numerator is one. -/
theorem omega_hasNonzeroCoordinate :
    HasNonzeroCoordinate (Proj.omega : GaussianLine) :=
  Or.inl one_ne_zero

end Purelib.Geometry.Projective.Line.Gaussian.Proj

end

namespace Purelib.Geometry.Projective.Line.Gaussian.Proj

/-- Two valid equivalent homogeneous pairs differ by one explicit nonzero scalar. The proof splits on a displayed
coordinate; it performs no choice. -/
theorem exists_nonzero_scale_of_equivalent {x y :
  GaussianLine}
    (xValid : (HasNonzeroCoordinate x)) (yValid :
      (HasNonzeroCoordinate y))
    (equivalent : x.Equivalent y) :
    ∃ scalar : Data.Gaussian.Basic.Canonical, scalar ≠ 0 ∧ x = scale scalar y :=
      by
  by_cases yDenominatorZero : y.q = 0
  · have yNumeratorNonzero : y.p ≠ 0 := by
      rcases yValid with numeratorNonzero | denominatorNonzero
      · exact numeratorNonzero
      · exact (denominatorNonzero yDenominatorZero).elim
    have xDenominatorZero : x.q = 0 := by
      have crossIdentity := equivalent
      dsimp only [Proj.Equivalent] at crossIdentity
      have productZero : y.p * x.q = 0 := by
        rw [yDenominatorZero,
          Data.Gaussian.Basic.mul_zero] at crossIdentity
        exact crossIdentity.symm
      apply Data.Gaussian.Field.mul_right_cancel_of_ne
        yNumeratorNonzero
      rw [Data.Gaussian.Basic.mul_comm x.q y.p,
        productZero, Data.Gaussian.Basic.zero_mul]
    have xNumeratorNonzero : x.p ≠ 0 := by
      rcases xValid with numeratorNonzero | denominatorNonzero
      · exact numeratorNonzero
      · exact (denominatorNonzero xDenominatorZero).elim
    let scalar := x.p * y.p⁻¹
    have scalarNonzero : scalar ≠ 0 :=
      Data.Gaussian.Field.mul_ne_zero_direct
        xNumeratorNonzero
        (Data.Gaussian.Field.inv_ne_zero_direct
          yNumeratorNonzero)
    have numeratorIdentity : scalar * y.p = x.p := by
      dsimp only [scalar]
      rw [Data.Gaussian.Basic.mul_assoc,
        Data.Gaussian.Field.inv_eq,
        Data.Gaussian.Field.inv_mul _ yNumeratorNonzero,
        _root_.mul_one]
    exact ⟨scalar, scalarNonzero, by
      apply Proj.ext
      · exact numeratorIdentity.symm
      · rw [scale, yDenominatorZero, xDenominatorZero,
          Data.Gaussian.Basic.mul_zero]⟩
  · have yDenominatorNonzero : y.q ≠ 0 := yDenominatorZero
    have xDenominatorNonzero : x.q ≠ 0 := by
      intro xDenominatorZero
      have crossIdentity := equivalent
      dsimp only [Proj.Equivalent] at crossIdentity
      have productZero : x.p * y.q = 0 := by
        rw [xDenominatorZero,
          Data.Gaussian.Basic.mul_zero] at crossIdentity
        exact crossIdentity
      have xNumeratorZero : x.p = 0 := by
        apply Data.Gaussian.Field.mul_right_cancel_of_ne
          yDenominatorNonzero
        rw [productZero,
          Data.Gaussian.Basic.zero_mul]
      rcases xValid with numeratorNonzero | denominatorNonzero
      · exact numeratorNonzero xNumeratorZero
      · exact denominatorNonzero xDenominatorZero
    let scalar := x.q * y.q⁻¹
    have scalarNonzero : scalar ≠ 0 :=
      Data.Gaussian.Field.mul_ne_zero_direct
        xDenominatorNonzero
        (Data.Gaussian.Field.inv_ne_zero_direct
          yDenominatorNonzero)
    have denominatorIdentity : scalar * y.q = x.q := by
      dsimp only [scalar]
      rw [Data.Gaussian.Basic.mul_assoc,
        Data.Gaussian.Field.inv_eq,
        Data.Gaussian.Field.inv_mul _ yDenominatorNonzero,
        _root_.mul_one]
    have numeratorIdentity : scalar * y.p = x.p := by
      apply Data.Gaussian.Field.mul_right_cancel_of_ne
        yDenominatorNonzero
      calc
        (scalar * y.p) * y.q = scalar * (y.p * y.q) :=
          Data.Gaussian.Basic.mul_assoc _ _ _
        _ = scalar * (y.q * y.p) := by
          rw [Data.Gaussian.Basic.mul_comm y.p y.q]
        _ = (scalar * y.q) * y.p :=
          (Data.Gaussian.Basic.mul_assoc _ _ _).symm
        _ = y.p * (scalar * y.q) :=
          Data.Gaussian.Basic.mul_comm _ _
        _ = y.p * x.q := by rw [denominatorIdentity]
        _ = x.p * y.q := equivalent.symm
    exact ⟨scalar, scalarNonzero, by
      apply Proj.ext
      · exact numeratorIdentity.symm
      · exact denominatorIdentity.symm⟩

/-- Transitivity of projective equivalence through a valid middle/right pair, proved by exposing their finite nonzero
scale. -/
theorem equivalent_trans {x y z :
  GaussianLine}
    (xy : x.Equivalent y) (yz : y.Equivalent z)
    (yValid : (HasNonzeroCoordinate y)) (zValid :
      (HasNonzeroCoordinate z)) :
    x.Equivalent z := by
  rcases exists_nonzero_scale_of_equivalent yValid zValid yz with
    ⟨scalar, scalarNonzero, yIdentity⟩
  rw [yIdentity] at xy
  dsimp only [Proj.Equivalent, scale] at xy ⊢
  apply Data.Gaussian.Field.mul_right_cancel_of_ne scalarNonzero
  calc
    (x.p * z.q) * scalar = x.p * (scalar * z.q) := by
      rw [Data.Gaussian.Basic.mul_comm scalar z.q,
        Data.Gaussian.Basic.mul_assoc]
    _ = (scalar * z.p) * x.q := xy
    _ = (z.p * scalar) * x.q := by
      rw [Data.Gaussian.Basic.mul_comm scalar z.p]
    _ = z.p * (scalar * x.q) :=
      Data.Gaussian.Basic.mul_assoc _ _ _
    _ = z.p * (x.q * scalar) := by
      rw [Data.Gaussian.Basic.mul_comm scalar x.q]
    _ = (z.p * x.q) * scalar :=
      (Data.Gaussian.Basic.mul_assoc _ _ _).symm

end Purelib.Geometry.Projective.Line.Gaussian.Proj

end

end

section
/-!
# Projective coordinates over constructive Gaussian fractions

The generic finite projective records are specialized here without importing the old `Rat`
coordinate model.  Transitivity is proved with the explicit Gaussian cancellation theorem, so it
does not synthesize a generic domain instance through a choice-bearing compatibility constructor.
-/

@[expose] public section

section

namespace Purelib.Geometry.Projective.Line.Gaussian

/-- Cross-multiplication equivalence is transitive through a nonzero middle denominator.

The proof uses explicit Gaussian cancellation for the three displayed homogeneous pairs. -/
theorem equivalent_trans_of_mid_q {x y z :
  GaussianLine}
    (hxy : Proj.Equivalent x y) (hyz : Proj.Equivalent y z)
    (hyq : y.q ≠ 0) : Proj.Equivalent x z := by
  dsimp [Proj.Equivalent] at hxy hyz ⊢
  apply Data.Gaussian.Field.mul_right_cancel_of_ne hyq
  calc
    (x.p * z.q) * y.q = z.q * (x.p * y.q) := by ring1
    _ = z.q * (y.p * x.q) := by rw [hxy]
    _ = x.q * (y.p * z.q) := by ring1
    _ = x.q * (z.p * y.q) := by rw [hyz]
    _ = (z.p * x.q) * y.q := by ring1

end Purelib.Geometry.Projective.Line.Gaussian

end

end

end
