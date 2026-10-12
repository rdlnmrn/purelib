module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedPrimitives
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

@[expose] public section

/-! Existing geometric references bound every normalized corner pair. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)

namespace FaceMagnitudeBank
variable {faces : List (Meshes.PuncturedGridFaces.RegularFace bank)} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus} {stage : Nat}

/-- Every original normalized corner reading satisfies the retained geometric magnitude bound at any sufficiently late
stage. -/
theorem normalized_corner_bound (fixed : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential)
    (later : fixed.index ≤ stage) (cached : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank
      differential stage domains)
    (position : Fin faces.length) (sheet : Fin 2) (corner : Fin 4) :
    Data.Gaussian.Norm.Basic.normSq (((cached.normalize.get position).atSheet sheet).corners.values corner) ≤
      fixed.bound := by
  rw [cached.normalize_get,
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitives.normalize_atSheet,
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.normalize_corner, fixed.bound_eq]
  exact fixed.entries.bounded (fixed.index_eq ▸ later) cached position sheet corner

end FaceMagnitudeBank
namespace RegularMeshes.Numerics
variable {faces : List (Meshes.PuncturedGridFaces.RegularFace bank)} {domains :
  Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces} {stage : Nat}
  {i j : Fin genus}

/-- Read the two selected original differential values at one retained face, sheet and corner. -/
def cornerPair (cached : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage) (i
  j : Fin genus)
    (position : Fin faces.length) (sheet : Fin 2) (corner : Fin 4) : PrimitivePoint :=
  ⟨(cached.atDomain position sheet i).corners.values corner,
    (cached.atDomain position sheet j).corners.values corner⟩

/-- Both components of an original normalized corner pair are bounded by the sum of their retained reference bounds. -/
theorem normalized_corner_pair_bound
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential i))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential j))
    (firstLater : first.index ≤ stage) (secondLater : second.index ≤ stage)
    (cached : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage) (position :
      Fin faces.length) (sheet : Fin 2) (corner : Fin 4) :
    (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached.normalize i
      j position sheet corner)) (first.bound + second.bound) := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair
  change Gaussian.Basic.Canonical.normSq _ ≤ _ ∧ Gaussian.Basic.Canonical.normSq _ ≤ _
  rw [cached.normalize_atDomain, cached.normalize_atDomain,
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.normalize_corner,
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.normalize_corner]
  have left := first.entries.bounded (first.index_eq ▸ firstLater) (cached.get i) position sheet corner
  have right := second.entries.bounded (second.index_eq ▸ secondLater) (cached.get j) position sheet corner
  rw [← first.bound_eq] at left
  rw [← second.bound_eq] at right
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at left right
  exact ⟨left.trans (le_add_of_nonneg_right second.nonnegative),
    right.trans (le_add_of_nonneg_left first.nonnegative)⟩

/-- The difference of two original normalized corner pairs is bounded by four times the retained reference-bound sum. -/
theorem normalized_corner_difference_bound
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential i))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential j))
    (firstLater : first.index ≤ stage) (secondLater : second.index ≤ stage)
    (cached : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
    (leftPosition rightPosition : Fin faces.length) (leftSheet rightSheet : Fin 2) (leftCorner rightCorner : Fin 4) :
    (Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached.normalize
      i j leftPosition leftSheet leftCorner).sub
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached.normalize i
        j rightPosition rightSheet rightCorner))) (4 * (first.bound + second.bound)) := by
  have left :=
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.normalized_corner_pair_bound
    first second firstLater secondLater cached leftPosition leftSheet leftCorner
  have right :=
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.normalized_corner_pair_bound
    first second firstLater secondLater cached rightPosition rightSheet rightCorner
  have firstScalar := Gaussian.Norm.Bounds.normSq_sub_le_two
    (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached.normalize i j
      leftPosition leftSheet leftCorner).left
    (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached.normalize i j
      rightPosition rightSheet rightCorner).left
  have secondScalar := Gaussian.Norm.Bounds.normSq_sub_le_two
    (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached.normalize i j
      leftPosition leftSheet leftCorner).right
    (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached.normalize i j
      rightPosition rightSheet rightCorner).right
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at firstScalar secondScalar
  constructor
  · exact firstScalar.trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct left.1
        right.1) (by decide)).trans_eq (by ring1))
  · exact secondScalar.trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct left.2
        right.2) (by decide)).trans_eq (by ring1))

/-- Read the exact cross-area of the original corner-to-origin jump and retained within-face increment. -/
def cornerJump (cached : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage) (i
  j : Fin genus)
    (leftPosition rightPosition : Fin faces.length) (leftSheet rightSheet : Fin 2)
    (origin terminal : Fin 4) : Gaussian.Basic.Canonical :=
  Topology.Polygon.Stokes.edgeArea
    ((Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached i j
    leftPosition leftSheet origin).sub
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached i j
        rightPosition rightSheet 0))
    ((Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached i j
      leftPosition leftSheet terminal).sub
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached i j
        leftPosition leftSheet origin))

/-- The original normalized corner jump has squared norm at most sixty-four times the squared reference-bound sum. -/
theorem normalized_corner_jump_bound
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential i))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential j))
    (firstLater : first.index ≤ stage) (secondLater : second.index ≤ stage)
    (cached : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
    (leftPosition rightPosition : Fin faces.length) (leftSheet rightSheet : Fin 2) (origin terminal : Fin 4) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerJump cached.normalize i
      j leftPosition rightPosition leftSheet rightSheet origin terminal) ≤
      64 * (first.bound + second.bound)^2 := by
  rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact (Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound

      (normalized_corner_difference_bound
      first second firstLater secondLater cached leftPosition rightPosition leftSheet rightSheet origin 0)

      (normalized_corner_difference_bound
      first second firstLater secondLater cached leftPosition leftPosition leftSheet leftSheet terminal
      origin)).trans_eq (by ring1)

/-- Perturbing both original corner-jump arguments within the retained small error gives the explicit linear area-error
allowance. -/
theorem normalized_corner_jump_perturbation
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential i))
    (second : Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
      (Periods.PeriodMatrix.standardDifferential j))
    (firstLater : first.index ≤ stage) (secondLater : second.index ≤ stage)
    (cached : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
    (leftPosition rightPosition : Fin faces.length) (leftSheet rightSheet : Fin 2) (origin terminal : Fin 4)
    (jump increment : Topology.Polygon.Stokes.PrimitivePoint) {error : Fraction.Rational} (errorNonnegative : 0 ≤ error)
      (small : error ≤ 1)
    (jumpError : Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (jump.sub
      ((Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached.normalize
      i j leftPosition leftSheet origin).sub
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached.normalize i
        j rightPosition rightSheet 0))) error)
    (incrementError : Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (increment.sub
      ((Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached.normalize
      i j leftPosition leftSheet terminal).sub
      (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cached.normalize i
        j leftPosition leftSheet origin))) error) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Polygon.Stokes.edgeArea jump increment -
      Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerJump cached.normalize i
      j leftPosition rightPosition leftSheet rightSheet origin terminal) ≤
      32 * (4 * (first.bound + second.bound) + 1) * error :=
  Topology.Surface.Boundary.HandleAreaBounds.PrimitivePoint.area_difference_bound
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg first.nonnegative second.nonnegative))
      errorNonnegative small

      (normalized_corner_difference_bound
      first second firstLater secondLater cached leftPosition rightPosition leftSheet rightSheet origin 0)

      (normalized_corner_difference_bound
      first second firstLater secondLater cached leftPosition leftPosition leftSheet leftSheet terminal origin)
    jumpError incrementError

end RegularMeshes.Numerics
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude
