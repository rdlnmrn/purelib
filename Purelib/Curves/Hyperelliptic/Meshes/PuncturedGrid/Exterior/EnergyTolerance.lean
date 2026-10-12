module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyGaps
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.Request

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.Request

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Riemann

public section

/-!
# A requested tolerance for the actual odd exterior energy

Counts and source bounds belong to the original prepared occurrences. They
choose one allowance before any target-dependent chart or root acquisition.
The resulting estimate preserves the original internal-area correction.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

/-- The rational coordinate cast of a natural finite count is nonnegative. -/
private theorem cast_nonnegative (n : Nat) : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ n :=
  Fraction.Cast.Order.natCast_le_direct (Nat.zero_le n)

/-- The fixed gap-correction coefficient computed from the original occurrence count and source slope. -/
@[expose] def correctionCoefficient (count : Nat) (slope : Normalization.InverseRootPolynomial.Coordinate) : Coordinate
  :=
  2 * (16 * (count : Normalization.InverseRootPolynomial.Coordinate) ^ 4 * (2 * (2 * (slope + 1) + 1)) +
    (count : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (4 * (2 * (slope + 1))))

/-- The fixed whole-surface comparison coefficient from the original parent count, occurrence count and slope. -/
@[expose] def surfaceCoefficient (parents count : Nat) (slope : Normalization.InverseRootPolynomial.Coordinate) :
  Coordinate :=
  2 * (2568 + 2 * (164 * ((parents : Normalization.InverseRootPolynomial.Coordinate) ^ 2 + 1) +
    correctionCoefficient
    count slope))

/-- The original gap-correction coefficient is nonnegative for a nonnegative source slope. -/
theorem correction_nonnegative (count : Nat) {slope : Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤
  slope) :
    0 ≤ correctionCoefficient
      count slope := by
  have twice : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2 * (slope + 1) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg nonnegative (by decide +kernel))
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
          (Fraction.Order.Arithmetic.pow_nonneg_direct
            (cast_nonnegative
            count) 4))
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg twice (by decide +kernel))))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) twice)))

/-- The original whole-surface coefficient is nonnegative for a nonnegative source slope. -/
theorem surface_nonnegative (parents count : Nat) {slope : Normalization.InverseRootPolynomial.Coordinate} (nonnegative
  : 0 ≤ slope) :
    0 ≤ surfaceCoefficient
      parents count slope :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg (by decide +kernel)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
        (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _) (by decide +kernel)))
      (correction_nonnegative
        count nonnegative))))

/-- A nonnegative gap allowance bounded by one and the common target is paid by the original fixed correction
coefficient. -/
theorem correction_paid (count : Nat) {slope allowance delta : Normalization.InverseRootPolynomial.Coordinate}
    (slopeNonnegative : 0 ≤ slope) (allowanceNonnegative : 0 ≤ allowance)
    (deltaNonnegative : 0 ≤ delta) (small : allowance ≤ 1) (paid : allowance ≤ delta) :
    2 * (16 * (count : Normalization.InverseRootPolynomial.Coordinate) ^ 4 * allowance * (2 * (2 * (slope + 1) +
      allowance)) +
      (count : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (4 * (2 * (slope + 1)) * allowance)) ≤

          correctionCoefficient
          count slope * delta := by
  have twice : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2 * (slope + 1) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg slopeNonnegative (by decide +kernel))
  have widened := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (le_refl (2 * (slope + 1))) small) (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct paid widened
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg twice allowanceNonnegative))
      deltaNonnegative
  have polygon := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 16)
      (Fraction.Order.Arithmetic.pow_nonneg_direct
        (cast_nonnegative
        count) 4))
  have triangles := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct (count :
      Normalization.InverseRootPolynomial.Coordinate))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4) twice))
  have combined := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct polygon triangles) (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  calc
    _ = 2 * ((16 * (count : Normalization.InverseRootPolynomial.Coordinate) ^ 4) * (allowance * (2 * (2 * (slope + 1) +
      allowance))) +
      ((count : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (4 * (2 * (slope + 1)))) * allowance) := by ring1
    _ ≤ _ := combined
    _ = _ := by
      unfold correctionCoefficient
      ring1

/-- The original retained parent residual is bounded by its fixed count coefficient times the common chart-and-join
allowance. -/
theorem residual_paid (parents : Nat) {localChart allowance delta : Normalization.InverseRootPolynomial.Coordinate}
    (chartPaid : localChart ≤ delta) (joinPaid : allowance ≤ delta) :
    2 * ((parents : Normalization.InverseRootPolynomial.Coordinate) * ((parents :
      Normalization.InverseRootPolynomial.Coordinate) * (80 * localChart + 2 * allowance)) +
      (80 * localChart + 2 * allowance)) ≤ 164 * ((parents : Normalization.InverseRootPolynomial.Coordinate) ^ 2 + 1) *
        delta := by
  have pair := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct chartPaid (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 80))
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct joinPaid (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct pair
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
      (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct (parents :
        Normalization.InverseRootPolynomial.Coordinate)) (by
            decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1)))
  calc
    _ = (2 * ((parents : Normalization.InverseRootPolynomial.Coordinate) ^ 2 + 1)) * (80 * localChart + 2 * allowance)
      := by
      ring1
    _ ≤ _ := scaled
    _ = _ := by ring1

set_option genInjectivity false in
/-- The coefficient and chosen allowance are cached before acquiring samples. -/
structure Budget (parents count : Nat) (slope target : Normalization.InverseRootPolynomial.Coordinate) where
  /-- The cached whole-surface coefficient determined by the original finite counts and slope. -/ coefficient :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The coefficient cache equals the exact original whole-surface coefficient expression. -/ coefficient_eq :
    coefficient =
    surfaceCoefficient
    parents count slope
  /-- The cached common positive allowance used by all retained exterior requests. -/ allowance :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The common allowance is the minimum of one and the original target divided by the cached coefficient plus one. -/
    allowance_eq : allowance = min (target / (coefficient + 1)) 1
  /-- The cached actual common allowance is strictly positive. -/ positive : 0 < allowance
  /-- The cached actual common allowance is at most one. -/ small : allowance ≤ 1
  /-- The complete cached coefficient times its original allowance is strictly below the requested target. -/ paid :
    coefficient * allowance < target

constructive_injectivity Budget

/-- Compute the original fixed surface coefficient and a positive common allowance paying the complete requested target.
-/
@[expose] def Budget.build (parents count : Nat) (slope target : Normalization.InverseRootPolynomial.Coordinate)
    (slopeNonnegative : 0 ≤ slope) (positive : 0 < target) :
      Budget parents count
      slope target := by
  let coefficient :=
    surfaceCoefficient
    parents count slope
  have nonnegative : 0 ≤ coefficient :=
    surface_nonnegative
    parents count slopeNonnegative
  have denominatorPositive : (0 : Normalization.InverseRootPolynomial.Coordinate) < coefficient + 1 :=
    Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative (by decide +kernel)
  let allowance := min (target / (coefficient + 1)) 1
  have allowancePositive : 0 < allowance := Fraction.Order.Basic.lt_min (Fraction.Order.Field.div_pos_direct positive
    denominatorPositive) (by decide +kernel)
  have coefficientLess : coefficient < coefficient + 1 :=
    (show coefficient = coefficient + 0 by ring1).trans_lt
      (Fraction.Order.Arithmetic.add_lt_add_left_direct (by
          decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) < 1) coefficient)
  have enlarged := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct coefficientLess allowancePositive
  have bounded := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Basic.min_le_left (target / (coefficient + 1)) 1) denominatorPositive.le
  have cancel : (coefficient + 1) * (target / (coefficient + 1)) = target := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
  exact ⟨coefficient, rfl, allowance, rfl, allowancePositive, Fraction.Order.Basic.min_le_right _ _, enlarged.trans_le
    (bounded.trans_eq cancel)⟩

/-- The actual retained common allowance is strictly below the original whole target. -/
theorem Budget.allowance_lt {parents count : Nat} {slope target : Normalization.InverseRootPolynomial.Coordinate}
    (budget : Budget parents
      count slope target) (nonnegative : 0 ≤ slope) : budget.allowance < target := by
  have inner : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 164 * ((parents :
    Normalization.InverseRootPolynomial.Coordinate) ^ 2 + 1) +
    correctionCoefficient
    count slope :=
    add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 164)
      (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _) (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1)))
      (correction_nonnegative
        count nonnegative)
  have oneLe : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ budget.coefficient := by
    rw [budget.coefficient_eq]
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    exact (add_nonneg (by decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 5135)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4) inner)).trans_eq (by
        unfold
          surfaceCoefficient
        ring1)
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct oneLe budget.positive.le
  exact (show budget.allowance = 1 * budget.allowance by ring1).trans_le scaled |>.trans_lt budget.paid

/-- The positive aggregate per-term allowance is at most its original target for every finite count. -/
private theorem perTerm_le {target : Normalization.InverseRootPolynomial.Coordinate} (positive : 0 < target) (count :
  Nat) : Aggregate.perTerm target count ≤ target := by
  let n : Coordinate := (count : Normalization.InverseRootPolynomial.Coordinate)
  have nonnegative : 0 ≤ n := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  have denominatorPositive : (0 : Normalization.InverseRootPolynomial.Coordinate) < 2 * (n + 1) ^ 2 :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Fraction.Order.Arithmetic.pow_pos_direct (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative (by
      decide)) 2)
  have coefficient : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2 * (n + 1) ^ 2 := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    exact (add_nonneg (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤
        2) (Fraction.Order.Arithmetic.sq_nonneg_direct n))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤
        4) nonnegative)) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 1)).trans_eq (by ring1)
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient (Aggregate.perTerm_positive
    positive count).le
  have paid : (2 * (n + 1) ^ 2) * Aggregate.perTerm target count = target := by
    rw [Aggregate.perTerm, Aggregate.countCoordinate_eq, Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'
  exact (show Aggregate.perTerm target count = 1 * Aggregate.perTerm target count by ring1).trans_le (scaled.trans_eq
    paid)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceComponent)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation (Request
  sourceMaximum sourceMaximum_nonnegative)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.Request.ChartRequest
  (RootEnergyAcquisition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy.Request.ChartRequest (acquireRootEnergy)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy (singleComponent
  build_odd_component_count)
open Purelib.Riemann.Normalization
open Purelib.Integration.Path.IncrementArea (Summary)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {localTarget localArea chartTarget : Coordinate} {floor index
    depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    FacePrimitiveBank differential index domains}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)

namespace OddRootEnergy.Request.ChartRequest.RootEnergyAcquisition

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {delta : Coordinate}
  {request : Request
    prepared delta delta floor} {charts :
    SurfaceRequests.AllSurfacePreparation.Request.ChartRequest
    request delta}
  {component :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
    regular domains differential} {energyTarget : Coordinate}
    {depthFloor energyFloor : Nat}

/-- With one common allowance, the physical estimate is linear in that allowance and uses only the original cached
counts and source bound. -/
theorem
  uniform_bound
  (acquired : ChartRequest.RootEnergyAcquisition charts component delta energyTarget depthFloor energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (positive : 0 < delta) :
    Data.Gaussian.Norm.Basic.normSq (acquired.energy.energy + (acquired.evaluated.original.surface.area +
      acquired.evaluated.original.internalArea)) <

        EnergyTolerance.ExteriorEnergyAllowance.surfaceCoefficient
        component.program.cache.parents.length request.count request.slope * delta := by
  have chartPaid : charts.localChart ≤ delta := by
    rw [charts.localChart_eq]
    exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance.perTerm_le positive
      _
  have joinPaid : acquired.roots.allowance ≤ delta := by
    rw [acquired.roots.allowance_eq]
    exact Fraction.Order.Basic.min_le_left _ _
  have residual :=
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance.residual_paid
    component.program.cache.parents.length chartPaid joinPaid
  have correction : acquired.correctionBound ≤
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance.correctionCoefficient
    request.count request.slope * delta :=
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance.correction_paid
      request.count
      (request.slope_eq ▸ AllSurfacePreparation.sourceMaximum_nonnegative prepared.occurrences)
      acquired.roots.positive.le positive.le acquired.roots.small joinPaid
  have boundary := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct residual correction) (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  have combined := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct
      (le_refl (2 * (256 * (4 * delta + delta) + 2 * (delta + delta)))) boundary) (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  exact (acquired.surface_energy_bound branch).trans_le
    (combined.trans_eq (by
      unfold EnergyTolerance.ExteriorEnergyAllowance.surfaceCoefficient
      ring1))

end OddRootEnergy.Request.ChartRequest.RootEnergyAcquisition

set_option genInjectivity false in
/-- An actual acquired exterior, with every numerical budget chosen from the requested tolerance and the original finite
preparation. -/
structure EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy (prepared : ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (component : ExteriorProgram.SurfaceComponent regular domains differential) (target energyTarget :
      Normalization.InverseRootPolynomial.Coordinate)
    (floor depthFloor energyFloor : Nat) where
  /-- The original prepared exterior component list is exactly this retained singleton component. -/ single :
    prepared.components = [component]
  /-- The retained tolerance budget computed from the actual original component, occurrence count and source slope. -/
    budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance.Budget
    component.program.cache.parents.length prepared.occurrences.length
    (AllSurfacePreparation.sourceMaximum prepared.occurrences) target
  /-- The original complete exterior request using the same retained allowance for integration and area. -/ request :
    AllSurfacePreparation.Request prepared budget.allowance budget.allowance floor
  /-- The original chart request using that same cached common allowance. -/ charts :
    AllSurfacePreparation.Request.ChartRequest request budget.allowance
  /-- The actual retained root-energy acquisition on the original component and chart request. -/ acquired :
    ChartRequest.RootEnergyAcquisition charts component budget.allowance energyTarget depthFloor energyFloor
  /-- The actual acquired energy satisfies the requested strict lower bound. -/ lower : -energyTarget <
    acquired.energy.energy.im / 4
  /-- The actual acquired energy and original corrected surface area satisfy the requested strict
squared-error bound. -/
  close : Data.Gaussian.Norm.Basic.normSq (acquired.energy.energy +
    (acquired.evaluated.original.surface.area + acquired.evaluated.original.internalArea)) < target

constructive_injectivity EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy

namespace EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy

set_option genInjectivity false in
/-- Retain all exterior accuracy requirements before choosing the common bank. -/
structure Preparation (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential)
    (component : ExteriorProgram.SurfaceComponent regular domains differential) (target :
      Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original prepared exterior component list is exactly this retained singleton component. -/ single :
    prepared.components = [component]
  /-- The retained tolerance budget computed from the actual original component, occurrence count and source slope. -/
    budget : Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance.Budget
    component.program.cache.parents.length prepared.occurrences.length
    (AllSurfacePreparation.sourceMaximum prepared.occurrences) target
  /-- The original complete exterior request using the same retained allowance for integration and area. -/ request :
    AllSurfacePreparation.Request prepared budget.allowance budget.allowance floor
  /-- The original chart request using that same cached common allowance. -/ charts :
    AllSurfacePreparation.Request.ChartRequest request budget.allowance

constructive_injectivity Preparation

namespace Preparation

/-- Prepare the complete original exterior and chart requests after caching their shared tolerance budget. -/
@[expose] def build (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential)
    (component : ExteriorProgram.SurfaceComponent regular domains differential) (single : prepared.components =
      [component])
    (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      RequestedOddEnergy.Preparation
      prepared component target floor := by
  let budget := Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance.Budget.build
    component.program.cache.parents.length prepared.occurrences.length
    (AllSurfacePreparation.sourceMaximum prepared.occurrences) target (AllSurfacePreparation.sourceMaximum_nonnegative
      _) positive
  let request := AllSurfacePreparation.Request.build prepared budget.allowance budget.allowance budget.positive
    budget.positive floor
  let charts := ChartRequest.build request budget.allowance budget.positive
  exact ⟨single, budget, request, charts⟩

/-- Evaluate on the caller's already shared numerical bank, with no repeated surface preparation or intermediate
allowance calculation. -/
@[expose] def evaluate {prepared : ExteriorProgram.AllSurfacePreparation regular domains differential}
    {component : ExteriorProgram.SurfaceComponent regular domains differential} {target :
      Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
    (ready :
      RequestedOddEnergy.Preparation
      prepared component target floor)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (energyPositive : 0 < energyTarget) (depthFloor
      energyFloor : Nat)
    {index : Nat} (sample : Primitives.Sample cap differential index collar.box)
    (shared : PrimitiveData.FacePrimitiveBank differential index domains) (later : ready.charts.index ≤ index) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy prepared
      component target energyTarget floor depthFloor energyFloor := by
  let acquired := ChartRequest.acquireRootEnergy ready.charts component ready.single branch ready.budget.allowance
    energyTarget
    ready.budget.positive energyPositive depthFloor energyFloor sample shared later
  have close := acquired.uniform_bound branch ready.budget.positive
  have coefficientEq :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.ExteriorEnergyAllowance.surfaceCoefficient
    component.program.cache.parents.length ready.request.count ready.request.slope = ready.budget.coefficient := by
    rw [ready.request.count_eq, ready.request.slope_eq, ready.budget.coefficient_eq]
  have paid := close.trans_eq (congrArg (· * ready.budget.allowance) coefficientEq)
  exact ⟨ready.single, ready.budget, ready.request, ready.charts, acquired, acquired.energy.lower, paid.trans
    ready.budget.paid⟩

end Preparation

/-- Canonical standalone acquisition uses the same preparation/evaluation path. -/
@[expose] def build (prepared : ExteriorProgram.AllSurfacePreparation regular domains differential)
    (component : ExteriorProgram.SurfaceComponent regular domains differential) (single : prepared.components =
      [component])
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (target energyTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (energyPositive : 0 <
      energyTarget)
    (floor depthFloor energyFloor : Nat) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy
      prepared component target energyTarget floor depthFloor energyFloor :=
  let ready :=
    Preparation.build
    prepared component single target positive floor
  ready.evaluate branch energyTarget energyPositive depthFloor energyFloor
    (Primitives.Sample.build cap differential ready.charts.index collar.box)
    (FacePrimitiveBank.build differential ready.charts.index domains) (Nat.le_refl _)

variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {component :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceComponent
  regular domains differential}
  {target energyTarget : Coordinate} {depthFloor energyFloor : Nat}

/-- The original acquired integral and retained cap increment total differ by squared norm strictly below the whole
requested target. -/
theorem integral_close (result :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy prepared
  component target energyTarget floor depthFloor energyFloor) :
    Data.Gaussian.Norm.Basic.normSq (result.acquired.evaluated.original.integral -
      result.acquired.evaluated.original.cap.total) < target :=
  result.acquired.evaluated.original.integral_close.trans (result.budget.allowance_lt
    (AllSurfacePreparation.sourceMaximum_nonnegative _))

/-- The original acquired source area and retained cap area differ by squared norm strictly below the whole requested
target. -/
theorem source_area_close (result :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy prepared
  component target energyTarget floor depthFloor energyFloor) :
    Data.Gaussian.Norm.Basic.normSq (result.acquired.evaluated.original.source.area -
      result.acquired.evaluated.original.cap.area) < target :=
  result.acquired.evaluated.original.area_close.trans (result.budget.allowance_lt
    (AllSurfacePreparation.sourceMaximum_nonnegative _))

/-- The physical polygon uses the very same shared triangle increments. -/
theorem triangle_close (result :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy prepared
  component target energyTarget floor depthFloor energyFloor)
    (readings : TrianglePrimitiveReadings.TriangleReadings result.acquired.shared lifted.mesh) :
    Data.Gaussian.Norm.Basic.normSq (result.acquired.energy.energy + (IncrementArea.pathArea
      (result.request.entries.map
      (fun entry => entry.occurrence.placement.location.sourceEdge.increment readings.values)) +
        result.acquired.evaluated.original.internalArea)) < target := by
  rw [← result.acquired.evaluated.original.triangle_area readings]
  exact result.close

end EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy

/-- Canonical construction needs no caller component, stage, or intermediate allowance. The odd component is selected
from this same preparation. -/
@[expose] def EnergyTolerance.AllSurfacePreparation.acquireOddEnergy (regular : RegularBounds.Data cap)
    (domains : DomainBanks.FaceDomainBank lifted.frames base.faces.regulars) (differential :
      Differentials.Basic.Differential genus)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (target energyTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (energyPositive : 0 <
      energyTarget)
    (floor depthFloor energyFloor : Nat) :
    let prepared := AllSurfacePreparation.build regular domains differential
    let component := OddRootEnergy.singleComponent prepared (OddRootEnergy.build_odd_component_count regular domains
      differential branch)
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy prepared
      component.val target energyTarget floor depthFloor energyFloor :=
  let prepared := AllSurfacePreparation.build regular domains differential
  let component := OddRootEnergy.singleComponent prepared (OddRootEnergy.build_odd_component_count regular domains
    differential branch)
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyTolerance.AllSurfacePreparation.RequestedOddEnergy.build
    prepared component.val component.property branch target energyTarget positive energyPositive floor depthFloor
    energyFloor

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
