module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Boundary.BoundaryDefectReadings
import Purelib.Tactic.Ring

public section

/-!
# Finite area bounds for cached primitive-pair defects

The general estimate allows two different primitive components. Conjugate
energy readings supply the left-component bound from the right one. The
primitive value multiplying the defect is retained explicitly.
-/

namespace Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Data
open Purelib.Riemann
open Purelib.Topology

open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair (Sample)

open Purelib.Data.Gaussian.Basic.Canonical
/-- The rational scalar type for primitive area bounds. -/
abbrev AreaCoordinate := Rat.Fraction.Rational

namespace PrimitivePoint

/-- Both Gaussian coordinates of a primitive point have quadrance at most the same bound. -/
@[expose] def Bounded (point : PrimitivePoint) (bound : Readings.PrimitiveAreaBounds.AreaCoordinate) : Prop :=
  Gaussian.Basic.Canonical.normSq point.left ≤ bound ∧ Gaussian.Basic.Canonical.normSq point.right ≤ bound

/-- The primitive point's left coordinate is the conjugate of its right coordinate. -/
@[expose] def Conjugate (point : PrimitivePoint) : Prop := point.left = Gaussian.Basic.Canonical.conj point.right

/-- The difference of two conjugate primitive points remains conjugate. -/
theorem sub_conjugate {first last : PrimitivePoint} (left : (PrimitivePoint.Conjugate first)) (right :
  (PrimitivePoint.Conjugate last)) :
    (PrimitivePoint.Conjugate ((Polygon.Stokes.PrimitivePoint.sub first) last)) := by
  change first.left - last.left = Gaussian.Basic.Canonical.conj (first.right - last.right)
  rw [left, right]
  apply Gaussian.Basic.ext
  · rfl
  · simp only [Gaussian.Basic.Canonical.conj, Gaussian.Basic.sub_im]; ring1

/-- A right-coordinate quadrance bound controls both coordinates of a conjugate primitive point.

Conjugation retains the real coordinate and negates the imaginary coordinate.
Their two squared contributions therefore give the same retained quadrance bound. -/
theorem bounded_of_conjugate {point : PrimitivePoint} (conjugate : (PrimitivePoint.Conjugate point)) {bound :
  Readings.PrimitiveAreaBounds.AreaCoordinate}
    (right : Gaussian.Basic.Canonical.normSq point.right ≤ bound) : (PrimitivePoint.Bounded point) bound :=
  ⟨by
    rw [conjugate]
    change point.right.re * point.right.re + (-point.right.im) * (-point.right.im) ≤ bound
    have square : (-point.right.im) * (-point.right.im) = point.right.im * point.right.im := by ring1
    rewrite [square]
    exact right, right⟩

/-- The primitive area pairing has quadrance at most four times the two point bounds.

Each point retains a common bound on its left and right coordinates; the product bound pays both terms in the
antisymmetric pairing. -/
theorem area_bound {first last : PrimitivePoint} {firstBound lastBound : Readings.PrimitiveAreaBounds.AreaCoordinate}
    (left : (PrimitivePoint.Bounded first) firstBound) (right : (PrimitivePoint.Bounded last) lastBound) :
    Gaussian.Basic.Canonical.normSq (edgeArea first last) ≤ 4 * firstBound * lastBound := by
  have firstProduct := Rat.Fraction.Order.Arithmetic.mul_le_mul_direct left.1 right.2
    (Gaussian.Basic.Canonical.normSq_nonneg _) ((Gaussian.Basic.Canonical.normSq_nonneg _).trans left.1)
  have lastProduct := Rat.Fraction.Order.Arithmetic.mul_le_mul_direct right.1 left.2
    (Gaussian.Basic.Canonical.normSq_nonneg _) ((Gaussian.Basic.Canonical.normSq_nonneg _).trans right.1)
  have estimate := Gaussian.Norm.Bounds.normSq_sub_le_two (first.left * last.right) (last.left * first.right)
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  rw [Gaussian.Basic.Canonical.normSq_mul, Gaussian.Basic.Canonical.normSq_mul] at estimate
  exact estimate.trans ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add firstProduct lastProduct) (by decide)).trans_eq (by ring1))

/-- Adding primitive points costs twice the sum of their component norm bounds.

Both retained coordinates satisfy their supplied Gaussian norm bounds. The
quadrance bound for each coordinate sum pays the exact factor two. -/
theorem bounded_add {first last : Polygon.Stokes.PrimitivePoint} {leftBound rightBound :
  PrimitiveAreaBounds.AreaCoordinate}
    (left : (PrimitivePoint.Bounded first) leftBound) (right : (PrimitivePoint.Bounded last) rightBound) :
    (PrimitivePoint.Bounded (first.add last)) (2 * (leftBound + rightBound)) := by
  change Gaussian.Basic.Canonical.normSq (first.left + last.left) ≤ _ ∧ Gaussian.Basic.Canonical.normSq (first.right +
    last.right) ≤ _
  constructor
  · rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Rat.Fraction.Order.Arithmetic.add_le_add_direct
        (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using left.1) (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using right.1)) (by decide))
  · rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Rat.Fraction.Order.Arithmetic.add_le_add_direct
        (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using left.2) (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using right.2)) (by decide))

end PrimitivePoint

namespace ProjectedEdgePair.Sample

variable {source target : Nat} {labels : Fin source → Fin target} {primitive : Fin source → PrimitivePoint}

/-- Conjugate primitive endpoint readings give a conjugate edge defect. -/
theorem defect_conjugate (sample : Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample (labels := labels) primitive)
  (conjugate : ∀ vertex, (PrimitivePoint.Conjugate (primitive vertex))) :
    (PrimitivePoint.Conjugate sample.defect) := by
  rw [sample.defect_eq, sample.finishJump_eq, sample.startJump_eq]
  exact PrimitivePoint.sub_conjugate (PrimitivePoint.sub_conjugate (conjugate _) (conjugate _))
    (PrimitivePoint.sub_conjugate (conjugate _) (conjugate _))

/-- The endpoint defect term has quadrance at most four times error times magnitude.

The defect is bounded by the supplied error and the actual second sample's finishing point by the supplied magnitude. -/
theorem defectTerm_bound (sample : Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample (labels := labels) primitive)
  {error magnitude : Readings.PrimitiveAreaBounds.AreaCoordinate}
    (defect : (PrimitivePoint.Bounded sample.defect) error) (endpoint : (PrimitivePoint.Bounded (primitive
      sample.pair.second.finish)) magnitude) :
    Gaussian.Basic.Canonical.normSq sample.defectTerm ≤ 4 * error * magnitude := by
  rw [sample.defectTerm_eq]
  exact PrimitivePoint.area_bound defect endpoint

end ProjectedEdgePair.Sample
end Purelib.Riemann.Readings.PrimitiveAreaBounds

end
