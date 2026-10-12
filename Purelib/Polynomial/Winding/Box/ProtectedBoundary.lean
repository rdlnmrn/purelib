module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary.Strip
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
public import Purelib.Polynomial.Clearance.Box.ProtectedRadius
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
public import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Residual
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

open Purelib.Geometry.Rational.Box.Boundary.Strip (BoundaryStripSide BoundaryStripWitness)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free protected boundary strips

A finite boundary-clearance certificate and the Horner Lipschitz bound define
an explicit rational strip.  Any sufficiently small nonzero-winding subbox
must avoid that strip.  The proof projects one supplied corner to one parent
edge and uses only finite squared-norm inequalities.
-/

namespace Purelib.Polynomial.Winding.Box.ProtectedBoundary

/-- Meeting the protected strip forces raw winding zero. -/
theorem quadrupledBoxWinding_eq_zero_of_boundaryStripWitness
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) {ambient small : Box}
    (degreePositive : 0 < p.natDegree)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p ambient)
    (ambientProper : ambient.Proper) (smallProper : small.Proper)
    (refines : small.Refines ambient)
    (diagonal : small.diagonalSq ≤
      Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance ^ 2)
    (witness : BoundaryStripWitness ambient small
      (4 * Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance)) :
    Winding.Box.Basic.quadrupledBoxWinding p small = 0 := by
  let rho := Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance
  have rhoPositive := Clearance.Box.ProtectedRadius.protectedBoundaryRadius_pos p clearance ambientProper
  have nearby : Box.Boundary.Strip.NearbyBoundaryPoint ambient small rho :=
    Box.Boundary.Strip.nearbyBoundaryPoint (ambient := ambient) (small := small)
      (rho := rho) refines diagonal witness
  have anchorInside : ambient.Contains small.anchor :=
    refines.contains small.contains_anchor
  have variationRaw := Dense.Gaussian.Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound
    p nearby.boundary.1 anchorInside
  have variation : Data.Gaussian.Norm.Basic.normSq (p.eval nearby.point - p.eval small.anchor) ≤
      Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient *
        (Box.Boundary.Strip.protectedBoundaryDistanceScale * rho ^ 2) :=
    variationRaw.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        nearby.distance (Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p ambient).le)
  have valueIdentity : p.eval nearby.point = p.eval small.anchor +
      (p.eval nearby.point - p.eval small.anchor) := by
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;>
      ring1
  have valueUpper := Gaussian.Norm.Bounds.normSq_add_le_two (p.eval small.anchor)
    (p.eval nearby.point - p.eval small.anchor)
  rw [← valueIdentity] at valueUpper
  have dominance := Clearance.Box.ProtectedRadius.protectedBoundaryRadius_dominates
    p clearance ambientProper diagonal
  have chain :
      2 * (Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small +
          Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient *
            (Box.Boundary.Strip.protectedBoundaryDistanceScale * rho ^ 2)) <
        2 * (Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) +
          Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient *
            (Box.Boundary.Strip.protectedBoundaryDistanceScale * rho ^ 2)) := by
    have twoNonnegative : (0 : Fraction.Rational) ≤ 2 :=
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 2) (by decide)).le
    calc
      2 * (Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small +
          Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient *
            (Box.Boundary.Strip.protectedBoundaryDistanceScale * rho ^ 2)) <
          clearance.bound := dominance
      _ ≤ Data.Gaussian.Norm.Basic.normSq (p.eval nearby.point) :=
        by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using
          clearance.lower nearby.point nearby.boundary
      _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) +
          Data.Gaussian.Norm.Basic.normSq (p.eval nearby.point - p.eval small.anchor)) := valueUpper
      _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) +
          Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient *
            (Box.Boundary.Strip.protectedBoundaryDistanceScale * rho ^ 2)) := by
        have added : Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) +
              Data.Gaussian.Norm.Basic.normSq (p.eval nearby.point - p.eval small.anchor) ≤
            Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) +
              Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient *
                (Box.Boundary.Strip.protectedBoundaryDistanceScale * rho ^ 2) :=
          add_le_add (le_refl _) variation
        exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          added twoNonnegative
  have cancelledScale :
      Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small +
          Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient *
            (Box.Boundary.Strip.protectedBoundaryDistanceScale * rho ^ 2) <
        Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) +
          Dense.Gaussian.Bounds.Box.denseLipschitzBound p ambient *
            (Box.Boundary.Strip.protectedBoundaryDistanceScale * rho ^ 2) := by
    have twoPositive : (0 : Fraction.Rational) < 2 :=
      Fraction.Cast.Order.natCast_pos_direct (n := 2) (by decide)
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := 2) ?_ twoPositive
    simpa only [Fraction.Field.mul_comm] using chain
  have large : Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p ambient small <
      Data.Gaussian.Norm.Basic.normSq (p.eval small.anchor) :=
    Fraction.Order.Arithmetic.lt_of_add_lt_add_right_direct cancelledScale
  exact Winding.Box.Residual.quadrupledBoxWinding_eq_zero_of_anchorResidualBound_lt
    p degreePositive refines smallProper large

/-- A sufficiently small nonzero-winding source lies beyond all four
protected strips. -/
theorem strictly_inside_protectedBoundary
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient small : Box}
    (degreePositive : 0 < p.natDegree)
    (clearance : Clearance.Box.Boundary.Basic.BoundaryClearance p ambient)
    (ambientProper : ambient.Proper) (smallProper : small.Proper)
    (refines : small.Refines ambient)
    (rawNonzero : Winding.Box.Basic.quadrupledBoxWinding p small ≠ 0)
    (diagonal : small.diagonalSq ≤
      Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance ^ 2) :
    let rho := Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance
    ambient.xLower + 4 * rho < small.xLower ∧
      small.xUpper < ambient.xUpper - 4 * rho ∧
      ambient.yLower + 4 * rho < small.yLower ∧
      small.yUpper < ambient.yUpper - 4 * rho := by
  let rho := Clearance.Box.ProtectedRadius.protectedBoundaryRadius p ambient clearance
  have left : ambient.xLower + 4 * rho < small.xLower := by
    by_cases strict : ambient.xLower + 4 * rho < small.xLower
    · exact strict
    · have side : small.xLower ≤ ambient.xLower + 4 * rho :=
        le_of_not_gt strict
      let witness : BoundaryStripWitness ambient small (4 * rho) :=
        ⟨small.anchor, small.contains_anchor, BoundaryStripSide.left side⟩
      exact (rawNonzero
        (quadrupledBoxWinding_eq_zero_of_boundaryStripWitness
          p degreePositive clearance ambientProper smallProper refines
          diagonal witness)).elim
  have right : small.xUpper < ambient.xUpper - 4 * rho := by
    by_cases strict : small.xUpper < ambient.xUpper - 4 * rho
    · exact strict
    · have side : ambient.xUpper - 4 * rho ≤ small.xUpper :=
        le_of_not_gt strict
      let point : Gaussian.Basic.Canonical := ⟨small.xUpper, small.yLower⟩
      let witness : BoundaryStripWitness ambient small (4 * rho) :=
        ⟨point, ⟨small.x_valid, le_rfl, le_rfl, small.y_valid⟩,
          BoundaryStripSide.right side⟩
      exact (rawNonzero
        (quadrupledBoxWinding_eq_zero_of_boundaryStripWitness
          p degreePositive clearance ambientProper smallProper refines
          diagonal witness)).elim
  have bottom : ambient.yLower + 4 * rho < small.yLower := by
    by_cases strict : ambient.yLower + 4 * rho < small.yLower
    · exact strict
    · have side : small.yLower ≤ ambient.yLower + 4 * rho :=
        le_of_not_gt strict
      let witness : BoundaryStripWitness ambient small (4 * rho) :=
        ⟨small.anchor, small.contains_anchor, BoundaryStripSide.bottom side⟩
      exact (rawNonzero
        (quadrupledBoxWinding_eq_zero_of_boundaryStripWitness
          p degreePositive clearance ambientProper smallProper refines
          diagonal witness)).elim
  have top : small.yUpper < ambient.yUpper - 4 * rho := by
    by_cases strict : small.yUpper < ambient.yUpper - 4 * rho
    · exact strict
    · have side : ambient.yUpper - 4 * rho ≤ small.yUpper :=
        le_of_not_gt strict
      let point : Gaussian.Basic.Canonical := ⟨small.xLower, small.yUpper⟩
      let witness : BoundaryStripWitness ambient small (4 * rho) :=
        ⟨point, ⟨le_rfl, small.x_valid, small.y_valid, le_rfl⟩,
          BoundaryStripSide.top side⟩
      exact (rawNonzero
        (quadrupledBoxWinding_eq_zero_of_boundaryStripWitness
          p degreePositive clearance ambientProper smallProper refines
          diagonal witness)).elim
  exact ⟨left, right, bottom, top⟩

end Purelib.Polynomial.Winding.Box.ProtectedBoundary

end
