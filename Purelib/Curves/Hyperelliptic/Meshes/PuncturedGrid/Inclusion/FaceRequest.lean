module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedCoveredPeriodComparison
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FacePeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodCanonical
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarSums
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

public section

/-! Requested original regular-cell readings on the enlarged shared mesh.
The scalar floor is chosen before acquiring the original parent primitives. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FaceRequest

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks.RegularPrimitiveSplits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PeriodFragments
open Purelib.Data.Rat
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Integration
open Purelib.Riemann.Meshes
open Purelib.Riemann.Periods
open Purelib.Riemann.Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FacePeriods
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank (FaceScalarBudgets)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceSharedMeshes)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment renaming SplitSheets -> SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceDomainBank (stepsBound)
open Purelib.Riemann.Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds (CoveredPeriodRequest)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (IndicesAbove)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover (CoveredPeriodStage)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries
  (SharedSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {face : RegularFace bank} {base : FramedPuncturedGrid
    curve branches higher}
  {included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion bank.grid base.bank.grid}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {sheet : Fin 2} {source :
    Differential genus}
  {differential : Fin genus} {minimum : Nat} {target : Rational}

set_option genInjectivity false in
/-- The retained primitive, fragment and scalar requests for an included original regular face.

The scalar floor is fixed before acquiring the original parent primitives, and the retained fragment count pays every
shared-mesh piece. -/
structure IncludedRequest (face : PuncturedGridFaces.RegularFace bank)
    (included : Extension.CoordinateInclusion bank.grid base.bank.grid) (frames :
        RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid)
    (sheet : Fin 2) (source : Differentials.Basic.Differential genus) (differential : Fin genus) (minimum : Nat) (target
      : Fraction.Rational)
    (domains : DomainBanks.FaceDomainBank frames base.faces.regulars) : Type 2 where
  /-- The retained upper bound on the complete number of scalar mesh pieces. -/ pieces : Nat
  /-- The face scalar budgets paying one quarter of the requested target. -/ scalars : BranchCellBank.FaceScalarBudgets
    (PeriodMatrix.standardDifferential differential) pieces (target / 4) domains
  /-- The actual included period fragments and their retained comparison request. -/ fragments :
    PeriodFragments.IncludedFragments (base := base)
    (face.includedPeriod included frames sheet source).period differential minimum (target / 4)
  /-- The assignment of the original primitive requests to the actual shared face domains. -/ entries :
    Fragment.SplitSheets domains fragments.cells fragments.comparison.request.requests
  /-- Every retained primitive request lies above the chosen scalar floor. -/ indices :
    PreparedControlledPrimitiveRequests.IndicesAbove (FaceScalarBudgets.index scalars)
    fragments.comparison.request.requests
  /-- The actual split and analytic mesh count is at most the retained piece allowance. -/ count :
    fragments.fragments.splits.count * (2 * FaceDomainBank.stepsBound domains + 5) ≤ pieces

constructive_injectivity IncludedRequest

namespace IncludedRequest

variable {domains : FaceDomainBank frames
  base.faces.regulars}

/-- Prepare an included original-face request with positive scalar and period budgets.

The retained cover fixes the piece count before its scalar floor is imposed on the acquired primitive requests. -/
@[expose] def build (face : PuncturedGridFaces.RegularFace bank) (included : Extension.CoordinateInclusion bank.grid
  base.bank.grid)
    (frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid) (sheet : Fin 2) (source :
        Differentials.Basic.Differential genus)
    (differential : Fin genus) (minimum : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (domains : DomainBanks.FaceDomainBank frames base.faces.regulars) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FaceRequest.IncludedRequest face included frames sheet source
      differential minimum target domains := by
  let period := (face.includedPeriod included frames sheet source).period
  let cover := CoveredPeriodStage.acquire period.initial (PreparedRefinementProgramCore.standardDifferentials genus)
    genus minimum
  let gridCount := base.bank.grid.vertical.length + base.bank.grid.horizontal.length + 1
  let analyticCount := 2 * FaceDomainBank.stepsBound domains + 5
  let pieces := cover.retained.current.state.parents.length * gridCount * analyticCount
  have smallPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let scalars := FaceScalarBudgets.build (PeriodMatrix.standardDifferential differential) pieces (target / 4)
    smallPositive domains
  let floor := FaceScalarBudgets.index scalars
  let comparison := CoveredPeriodRequest.ofCover cover (PeriodMatrix.standardDifferential differential)
    (target / 4) smallPositive floor
  let fragments := IncludedFragments.ofRequest period (face.cell.anchor_mem face.member) included comparison
  have count : fragments.fragments.splits.count * analyticCount ≤ pieces := by
    have bound := fragments.fragments.splits.count_le
    simp only [-eq_self, -iff_self, fragments.axes.vertical_eq, fragments.axes.horizontal_eq, Data.List.Map.length_map]
      at bound
    exact Nat.mul_le_mul_right analyticCount bound
  have indices : PreparedControlledPrimitiveRequests.IndicesAbove floor comparison.request.requests := by
    have equal : comparison.request.minimumIndex = floor := ControlledSumRequest.acquire_minimumIndex ..
    exact equal ▸ comparison.request.indices_ge
  exact ⟨pieces, scalars, fragments, fragments.assign domains, indices, count⟩

/-- The original sheet-entry observation points followed by the supplied extra points. -/
@[expose] def points (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FaceRequest.IncludedRequest face
  included frames sheet source differential minimum target domains)
    (extra : List Data.Gaussian.Basic.Canonical) : List Gaussian :=
  SheetEntries.points request.entries ++ extra

/-- The retained scalar mesh budgets on the original and extra observation points. -/
@[expose] def budgets (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FaceRequest.IncludedRequest face
  included frames sheet source differential minimum target domains)
    (extra : List Data.Gaussian.Basic.Canonical) := FaceScalarBudgets.meshes (request.points extra) request.scalars

set_option genInjectivity false in
/-- The shared meshes and actual retained primitive sum for an included original face.

All meshes consume the supplied numerical bank, and the cached sum carries its paid scalar error bound. -/
structure Readings (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FaceRequest.IncludedRequest face
  included frames sheet source differential minimum target domains)
    (extra : List Data.Gaussian.Basic.Canonical) {numericalIndex : Nat}
    (numerics : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) numericalIndex domains)
      where
  /-- The actual shared meshes consuming the retained budgets and supplied primitive bank. -/ meshes :
    CommonMeshes.FaceSharedMeshes (request.budgets extra) numerics
  /-- The cached actual sum on the original retained sheet entries. -/ sum : SheetEntries.SharedSum meshes
    request.entries
  /-- The retained shared-sum bound is strictly below one quarter of the target. -/ small : sum.bound < target / 4

constructive_injectivity Readings

/-- Build shared meshes and their cached original-entry sum from the supplied paid numerical bank. -/
@[expose] def readWith (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FaceRequest.IncludedRequest face
  included frames sheet source differential minimum target domains)
    (positive : 0 < target) (extra : List Data.Gaussian.Basic.Canonical) {numericalIndex : Nat}
    (numerics : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) numericalIndex domains)
    (later : FaceScalarBudgets.index request.scalars ≤ numericalIndex) : request.Readings extra numerics := by
  let meshes := FaceSharedMeshes.build (request.budgets extra) numerics
    ((FaceScalarBudgets.meshes_index request.scalars (request.points extra)).le.trans later)
  let sum := SharedSum.build meshes request.entries (fun _ member => List.mem_append_left _ member)
  exact ⟨meshes, sum, sum.bound_lt
    (Fraction.Order.Field.div_pos_direct positive (by decide)) later request.indices request.count⟩

/-- The actual shared reading approximates the original included-face period program at every later paid stage. -/
theorem Readings.accurate
    {request : Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FaceRequest.IncludedRequest face included frames
      sheet source differential minimum target domains}
    {extra : List Data.Gaussian.Basic.Canonical} {numericalIndex : Nat}
    {numerics : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential differential) numericalIndex domains}
    (readings : request.Readings extra numerics) (stage : Nat) (later : request.fragments.comparison.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (readings.sum.value -
      (((face.includedPeriod included frames sheet source).period.program differential).integral.model
        stage).integralSample) < target := by
  have mesh := readings.sum.accurate
  rw [← request.fragments.comparison.request.increments_eq,
    ← request.fragments.comparison.request.primitiveSum_eq] at mesh
  have first := mesh.trans_lt readings.small
  have last := request.fragments.comparison.accurate
    (PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials differential) stage later
  have bound := (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct first last))
  rw [sub_add_sub_cancel] at bound
  have equal : 2 * (target / 4 + target / 4) = target := by
    rw [show 2 * (target / 4 + target / 4) = target / 4 * 4 by ring1]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  exact bound.trans_eq equal

end IncludedRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.FaceRequest

end
