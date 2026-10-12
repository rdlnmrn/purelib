module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Integration.Path.Dyadic.DyadicAreaRefinement
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBoundary
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

@[expose] public section

/-!
# Refinement error for the retained reciprocal cap polynomial

The existing energy cache supplies the polynomial and its finite coefficient
and Taylor bounds. These control every actual inverse source arc, and hence
the area difference between any coarse depth and any further finite depth.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- The squared-increment ceiling computed from the retained polynomial derivative and Taylor bounds on the reciprocal
disk. -/
def lipschitz (bounds : EnergyBounds sample) : Fraction.Rational := 2 *
  (bounds.coefficient + 4 * bounds.remainder)

/-- The retained polynomial squared-increment ceiling is nonnegative. -/
theorem lipschitz_nonnegative (bounds : EnergyBounds sample) : 0 ≤
  Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.lipschitz bounds :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg bounds.coefficient_nonnegative
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) bounds.remainder_nonnegative))

/-- Two points in the original reciprocal disk satisfy the polynomial squared-increment bound from the retained energy
cache. -/
theorem polynomial_increment_le (bounds : EnergyBounds sample) {first
  last : Gaussian.Basic.Canonical}
    (firstInside : Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial first)
    (lastInside : Dense.Gaussian.Reciprocal.Bounds.InDisk curve.polynomial last) :
    Data.Gaussian.Norm.Basic.normSq (sample.primitive.value.eval last - sample.primitive.value.eval first) ≤
      Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.lipschitz bounds * Data.Gaussian.Norm.Basic.normSq (last -
      first) := by
  have distance : Data.Gaussian.Norm.Basic.normSq (last - first) ≤ 4 :=
    (Gaussian.Norm.Bounds.normSq_sub_le_two last first).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (Dense.Gaussian.Reciprocal.Bounds.disk_unit_bound lastInside)
        (Dense.Gaussian.Reciprocal.Bounds.disk_unit_bound firstInside))
      (by decide)).trans_eq (by decide : (2 : Fraction.Rational) * (1 + 1) = 4))
  have squared : Data.Gaussian.Norm.Basic.normSq (last - first) ^ 2 ≤ 4 * Data.Gaussian.Norm.Basic.normSq (last
    - first) := by
    simpa only [pow_two] using Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct distance
      (Gaussian.Norm.Basic.normSq_nonneg (last - first))
  have remainder := (bounds.increment_le firstInside lastInside).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squared bounds.remainder_nonnegative)
  have affine : Data.Gaussian.Norm.Basic.normSq (sample.coefficient.eval first * (last - first)) ≤
    bounds.coefficient * Data.Gaussian.Norm.Basic.normSq (last - first) := by
    rw [Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (bounds.coefficient_le firstInside)
      (Gaussian.Norm.Basic.normSq_nonneg _)
  have identity : sample.primitive.value.eval last - sample.primitive.value.eval first =
      (sample.primitive.value.eval last - sample.primitive.value.eval first - sample.coefficient.eval first * (last -
        first)) +
        sample.coefficient.eval first * (last - first) := by ring1
  rw [identity]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add remainder affine) (by decide)).trans_eq (by
        unfold Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.lipschitz;
        ring1))

/-- The retained inverse-arc slope ceiling, including the original reciprocal distance factor eight. -/
def arcSlope (bounds : EnergyBounds sample) : Fraction.Rational := 8 *
  Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.lipschitz bounds

/-- The retained inverse-arc slope ceiling is nonnegative. -/
theorem arcSlope_nonnegative (bounds : EnergyBounds sample) : 0 ≤
  Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.arcSlope bounds :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.lipschitz_nonnegative bounds)

/-- The finite dyadic area-refinement scale computed from the original inverse-arc slope. -/
def areaScale (bounds : EnergyBounds sample) : Fraction.Rational := 4 *
  Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.arcSlope bounds ^ 2

/-- The retained area-refinement scale is nonnegative. -/
theorem areaScale_nonnegative (bounds : EnergyBounds sample) : 0 ≤
  Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale bounds :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct _)

/-- The actual inverse source arc satisfies the retained slope bound between two unit-interval parameters on one
original ambient side. -/
theorem inverse_arc_increment_le (bounds : EnergyBounds sample) {first
  last : Gaussian.Basic.Canonical}
    (firstInside : (Hyperelliptic.Branches.Cuts.Ambient curve).Contains first) (lastInside :
      (Hyperelliptic.Branches.Cuts.Ambient curve).Contains last)
    (side : Paths.PreparedBoundarySegments.SameSide (Hyperelliptic.Branches.Cuts.Ambient curve) first last)
    {left right : Fraction.Rational} (leftUnit : 0 ≤ left ∧ left ≤ 1) (rightUnit : 0 ≤ right ∧ right ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (sample.primitive.value.eval
      ((Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source first last right)⁻¹) -
      sample.primitive.value.eval ((Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source first last left)⁻¹))
        ≤ Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.arcSlope bounds * (right - left) ^ 2 := by
  have leftDisk := Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.inverse_inDisk curve
    (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source_boundary firstInside lastInside side leftUnit)
  have rightDisk := Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.inverse_inDisk curve
    (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source_boundary firstInside lastInside side rightUnit)
  exact (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.polynomial_increment_le bounds leftDisk rightDisk).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.inverse_distance firstInside lastInside side rightUnit
        leftUnit)
      (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.lipschitz_nonnegative bounds)).trans_eq (by
          unfold Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.arcSlope;
          ring1))

/-- Any further finite inverse-arc refinement differs from the coarse dyadic area by at most the retained
quarter-geometric bound. -/
theorem arc_refinement_bound (bounds : EnergyBounds sample) {first last
  : Gaussian.Basic.Canonical}
    (firstInside : (Hyperelliptic.Branches.Cuts.Ambient curve).Contains first) (lastInside :
      (Hyperelliptic.Branches.Cuts.Ambient curve).Contains last)
    (side : Paths.PreparedBoundarySegments.SameSide (Hyperelliptic.Branches.Cuts.Ambient curve) first last) (coarse fine
      : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea
      sample.primitive.value.eval (coarse + fine) first last -
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.arcArea sample.primitive.value.eval coarse first last) ≤
        Rational.Geometric.Basic.quarterRadius (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale bounds)
        coarse := by
  have estimate := Path.Dyadic.DyadicAreaRefinement.dyadicArea_refinement_bound
    (fun parameter => sample.primitive.value.eval ((Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source
      first last parameter)⁻¹))
    (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.arcSlope_nonnegative bounds) (fun _ _ leftUnit rightUnit =>
      Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.inverse_arc_increment_le bounds firstInside lastInside side
      leftUnit rightUnit)
    coarse fine (first := 0) (last := 1) (by decide) (by decide) (by decide)
  exact estimate.trans_eq (by unfold Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale; rw [show ((1 :
    Fraction.Rational) - 0) ^ 4 = 1 by decide]; ring1)

/-- The affine source segment between an original centered parent's endpoints is exactly its retained point map. -/
private theorem parent_source (parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)
  (parameter : Fraction.Rational) :
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source (parent.edge.point 0) (parent.edge.point 1)
      parameter = parent.edge.point parameter := by
  change parent.edge.localSegment.pointAt 0 + Gaussian.Scale.scale parameter
    (parent.edge.localSegment.pointAt 1 - parent.edge.localSegment.pointAt 0) = parent.edge.localSegment.pointAt
      parameter
  rw [Geometry.ClearPath.ClearSegment.pointAt_zero, Geometry.ClearPath.ClearSegment.pointAt_one]
  rfl

/-- An original parent on the ambient boundary satisfies the same retained inverse-arc increment ceiling. -/
theorem parent_increment_le (bounds : EnergyBounds sample) {parent :
  Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
    (boundary : Paths.PreparedBoundarySegments.ParentOnBoundary parent (Hyperelliptic.Branches.Cuts.Ambient curve))
    {left right : Fraction.Rational} (leftUnit : 0 ≤ left ∧ left ≤ 1) (rightUnit : 0 ≤ right ∧ right ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (sample.primitive.value.eval ((parent.edge.point right)⁻¹) -
      sample.primitive.value.eval ((parent.edge.point left)⁻¹)) ≤
      Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.arcSlope bounds * (right - left) ^ 2 := by
  have estimate := Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.inverse_arc_increment_le bounds
    boundary.startInside boundary.finishInside boundary.side leftUnit rightUnit
  rw [Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.parent_source,
    Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.parent_source] at estimate
  exact estimate

/-- The same estimate applies to the anchored path used by the retained
regular parent comparison. Its primitive origin cancels exactly. -/
theorem parent_refinement_bound (bounds : EnergyBounds sample) {parent
  : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
    (boundary : Paths.PreparedBoundarySegments.ParentOnBoundary parent (Hyperelliptic.Branches.Cuts.Ambient curve))
      (coarse fine : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Path.Dyadic.DyadicBoundaryRibbon.dyadicArea
        (fun parameter => sample.primitive.value.eval ((parent.edge.point parameter)⁻¹) - sample.primitive.value.eval
          ((parent.edge.point 0)⁻¹))
        (coarse + fine) 0 1 -
      Path.Dyadic.DyadicBoundaryRibbon.dyadicArea
        (fun parameter => sample.primitive.value.eval ((parent.edge.point parameter)⁻¹) - sample.primitive.value.eval
          ((parent.edge.point 0)⁻¹))
        coarse 0 1) ≤ Rational.Geometric.Basic.quarterRadius
          (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale bounds) coarse := by
  have bounded (left right : Fraction.Rational) (leftUnit : 0 ≤ left ∧ left ≤ 1) (rightUnit : 0 ≤ right ∧ right ≤ 1) :
      Data.Gaussian.Norm.Basic.normSq ((sample.primitive.value.eval ((parent.edge.point right)⁻¹) -
        sample.primitive.value.eval ((parent.edge.point 0)⁻¹)) -
        (sample.primitive.value.eval ((parent.edge.point left)⁻¹) - sample.primitive.value.eval ((parent.edge.point
          0)⁻¹))) ≤
          Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.arcSlope bounds * (right - left) ^ 2 := by
    rw [show (sample.primitive.value.eval ((parent.edge.point right)⁻¹) - sample.primitive.value.eval
      ((parent.edge.point 0)⁻¹)) -
        (sample.primitive.value.eval ((parent.edge.point left)⁻¹) - sample.primitive.value.eval ((parent.edge.point
          0)⁻¹)) =
        sample.primitive.value.eval ((parent.edge.point right)⁻¹) - sample.primitive.value.eval ((parent.edge.point
          left)⁻¹) by ring1]
    exact Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.parent_increment_le bounds boundary leftUnit rightUnit
  have estimate := Path.Dyadic.DyadicAreaRefinement.dyadicArea_refinement_bound _
    (Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.arcSlope_nonnegative bounds) bounded
    coarse fine (first := 0) (last := 1) (by decide) (by decide) (by decide)
  exact estimate.trans_eq (by unfold Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea.areaScale; rw [show ((1 :
    Fraction.Rational) - 0) ^ 4 = 1 by decide]; ring1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RefinementArea
