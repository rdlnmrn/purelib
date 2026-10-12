module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Topology.Surface.Cut.IntegralPairing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
public import Purelib.Riemann.Integration.PreparedRefinementPrograms
public import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutIntersection
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.SewingTree

public section

/-!
# Standard period names on the retained grid-intersection rows

The topology bank consumes the original canonical root-closed period rows.
These readbacks identify its programs, names and all finite integration
models with the existing standard period data. Primitive tail estimates
therefore target those exact programs. Comparing original parent primitives
to the split grid path remains a separate analytic obligation.
-/

section

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.LinearAlgebra.Alternating
open Purelib.Riemann

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Meshes.FramedPuncturedGrid curve (Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve
    branches).branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {integral :
    Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionBank

/-- The geometry table keeps the supplied numerical row, not its recomputed specification. -/
theorem ofPeriods_period (lifted : Meshes.LiftedPuncturedGrid base)
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
    (normal : LinearAlgebra.Alternating.NormalForm integral.paired raw)
    (periods : Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank curve)
    (canonical : ∀ index, periods.rows index =
      (Periods.PreparedRootClosedPeriodBank.PreparedCycleModels.RootClosedPeriodBank.ofData curve branches).rows index)
    (index : Fin genus) :
    ((Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.ofPeriods lifted integral normal
      periods canonical).rows.get index).period = periods.rows index := by
  simp only [Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.ofPeriods,
    Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionBank.ofRows,
    Data.Vector.DependentVector.ofFn_get, -eq_self, -iff_self]
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionBank

variable {index : Fin genus} (row : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow lifted
  integral index)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow

/-- The retained geometric A tour is exactly the original period row's A tour. -/
theorem source_aTour : row.pair.source.aTour = row.period.tours.aTour := congrArg (·.aTour) row.source_eq
/-- The retained geometric B tour is exactly the original period row's B tour. -/
theorem source_bTour : row.pair.source.bTour = row.period.tours.bTour := congrArg (·.bTour) row.source_eq

/-- No operational equivalence or new integration stream is needed: these
are exactly the named matrix entries of the retained standard bank. -/
theorem a_output (differential : Fin genus) :
    (row.period.aProgram differential).output = (Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve
      branches).aMatrix differential index := by
  rw [Periods.PeriodMatrix.PeriodData.aMatrix_apply, row.period_eq]
  rfl

/-- The retained original B program outputs the exact named entry of the standard raw period matrix. -/
theorem b_output (differential : Fin genus) :
    (row.period.bProgram differential).output = (Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve
      branches).bMatrix differential index := by
  rw [Periods.PeriodMatrix.PeriodData.bMatrix_apply, row.period_eq]
  rfl

/-- Each retained original A integration model equals the corresponding standard raw-period model. -/
theorem a_model (differential : Fin genus) (stage : Nat) :
    (row.period.aProgram differential).integral.model stage =
      ((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential
        index).integral.model stage := by
  rw [row.period_eq]
  rfl

/-- Each retained original B integration model equals the corresponding standard raw-period model. -/
theorem b_model (differential : Fin genus) (stage : Nat) :
    (row.period.bProgram differential).integral.model stage =
      ((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential
        index).integral.model stage := by
  rw [row.period_eq]
  rfl

/-- With canonical branch isolation, the retained A output is the original automatic raw-period matrix entry. -/
theorem a_output_automatic (canonical : branches = Hyperelliptic.Branches.BranchIsolation.data curve) (differential :
  Fin genus) :
    (row.period.aProgram differential).output = (Integration.PreparedRefinementPrograms.automaticRawPeriodData
      curve).aMatrix differential index := by
  subst branches
  cases genus with
  | zero => exact Fin.elim0 index
  | succ genus =>
    exact Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow.a_output row differential

/-- With canonical branch isolation, the retained B output is the original automatic raw-period matrix entry. -/
theorem b_output_automatic (canonical : branches = Hyperelliptic.Branches.BranchIsolation.data curve) (differential :
  Fin genus) :
    (row.period.bProgram differential).output = (Integration.PreparedRefinementPrograms.automaticRawPeriodData
      curve).bMatrix differential index := by
  subst branches
  cases genus with
  | zero => exact Fin.elim0 index
  | succ genus =>
    exact Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow.b_output row differential

set_option genInjectivity false in
/-- Both original standard programs receive automatic primitive comparisons.
The common tail is selected before evaluating either period sample. -/
structure PrimitiveComparison (differential : Fin genus) (minimum : Nat) (target : Fraction.Rational) where
  /-- The actual primitive comparison request on the retained original A initial state. -/ a :
    Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds.CoveredPeriodRequest row.period.aInitial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential) genus minimum target
  /-- The actual primitive comparison request on the retained original B initial state. -/ b :
    Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds.CoveredPeriodRequest row.period.bInitial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential) genus minimum target
  /-- The common stage for both original period tails. -/ stage : Nat
  /-- The retained stage is exactly the maximum of the two original comparison stages. -/ stage_eq : stage = max a.stage
    b.stage

constructive_injectivity PrimitiveComparison

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow

variable {row : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow lifted integral index}
  {differential : Fin genus}
  {minimum : Nat} {target : Fraction.Rational}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow.PrimitiveComparison

/-- Coverage, root agreement and both error budgets are acquired internally
on the same original A/B programs retained by the intersection bank. -/
@[expose] def acquire (row : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow lifted
  integral index) (differential : Fin genus)
    (minimum : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow.PrimitiveComparison row differential
      minimum target :=
  let a := Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds.CoveredPeriodRequest.acquire
    row.period.aInitial (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential) genus minimum target positive
  let b := Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds.CoveredPeriodRequest.acquire
    row.period.bInitial (Integration.PreparedRefinementProgramCore.standardDifferentials genus)
    (Periods.PeriodMatrix.standardDifferential differential) genus minimum target positive
  ⟨a, b, max a.stage b.stage, rfl⟩

/-- The retained common period-comparison stage meets the original requested floor. -/
theorem stage_ge (comparison :
  Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow.PrimitiveComparison row differential
  minimum target) : minimum ≤ comparison.stage := by
  rw [comparison.stage_eq]
  exact comparison.a.stage_ge.trans (Data.Nat.Order.le_max_left _ _)

/-- Every sufficiently late original A-program sample is within the target of its retained original primitive sum. -/
theorem a_accurate (comparison :
  Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow.PrimitiveComparison row differential
  minimum target)
    (stage : Nat) (later : comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (comparison.a.request.primitiveSum -
      (((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve branches).aProgram differential
        index).integral.model stage).integralSample) < target := by
  rw [← Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow.a_model row differential stage,
    row.period.aProgram_model]
  exact comparison.a.accurate (Integration.PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials
    differential) stage
    ((Data.Nat.Order.le_max_left _ _).trans (comparison.stage_eq ▸ later))

/-- Every sufficiently late original B-program sample is within the target of its retained original primitive sum. -/
theorem b_accurate (comparison :
  Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow.PrimitiveComparison row differential
  minimum target)
    (stage : Nat) (later : comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (comparison.b.request.primitiveSum -
      (((Integration.PreparedRefinementPrograms.rawPeriodDataOfData curve branches).bProgram differential
        index).integral.model stage).integralSample) < target := by
  rw [← Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow.b_model row differential stage,
    row.period.bProgram_model]
  exact comparison.b.accurate (Integration.PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials
    differential) stage
    ((Data.Nat.Order.le_max_right _ _).trans (comparison.stage_eq ▸ later))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback.IntersectionRow.PrimitiveComparison

end
