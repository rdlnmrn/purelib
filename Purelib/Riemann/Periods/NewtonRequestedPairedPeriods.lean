module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Periods.NewtonPairedPeriodFragments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ScalarSums
import Purelib.Tactic.Ring

public section

/-! Requested shared-face readings of the fixed original corrected periods.
Scalar budgets precede the original polynomial requests. Both sums read one
supplied Newton-grid primitive bank; no new period family is prepared. -/

namespace Purelib.Riemann.Periods.NewtonRequestedPairedPeriods

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank (FaceScalarBudgets)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceSharedMeshes)
open Purelib.Riemann.Periods.PreparedCoveredPeriodComparison.PreparedPrimitiveChargeBounds (CoveredPeriodRequest)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (IndicesAbove)
open Purelib.Riemann.Periods.PreparedPeriodPrimitiveCover (CoveredPeriodStage)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials
  standardDifferential_mem_standardDifferentials)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment renaming SplitSheets -> SheetEntries
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries
  (SharedSum)
open Purelib.Riemann.Periods.NewtonPairedPeriodFragments (NewtonFragments)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {bandTarget radius : Rational}
  {prepared : Prepared paired} {grid :
    NewtonGrid preparation bandTarget radius}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid.punctured.bank.grid}
  {differential index : Fin genus} {minimum : Nat} {target : Rational}

open Purelib.Curves in
open Purelib.Data in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- Retain scalar budgets and shared-face fragments for the original corrected A and B periods.

The scalar floor precedes both original polynomial requests. Sheet assignments, index bounds and complete split counts
remain tied to their original prepared periods and Newton grid. -/
structure NewtonPeriodRequest (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  (grid : NewtonGrid preparation bandTarget radius)
    (differential index : Fin genus) (minimum : Nat) (target : Rat.Fraction.Rational)
    {frames : RootIsolation.SquareRoot.Grid.RootFrames grid.punctured.bank.grid}
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.punctured.faces.regulars)
      : Type 2 where
  /-- The retained common upper bound on all analytic fragment pieces. -/ pieces : Nat
  /-- The original face-domain scalar budgets at one quarter of the target. -/ scalars :
    Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets (standardDifferential
    differential) pieces (target / 4) domains
  /-- The original A and B period fragments on the retained Newton grid. -/ fragments : NewtonFragments prepared grid
    differential index minimum (target / 4)
  /-- The actual A-fragment sheet assignments and requests in the original face domains. -/ aEntries :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets domains
    fragments.a.cells fragments.a.comparison.request.requests
  /-- The actual B-fragment sheet assignments and requests in the original face domains. -/ bEntries :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SplitSheets domains
    fragments.b.cells fragments.b.comparison.request.requests
  /-- Every original A-fragment request respects the scalar floor. -/ a_indices : IndicesAbove
    (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.index scalars)
    fragments.a.comparison.request.requests
  /-- Every original B-fragment request respects the scalar floor. -/ b_indices : IndicesAbove
    (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.index scalars)
    fragments.b.comparison.request.requests
  /-- The complete A split count with analytic expansion fits the retained piece bound. -/ a_count :
    fragments.a.fragments.splits.count * (2 *
    (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceDomainBank.stepsBound domains) + 5) ≤
    pieces
  /-- The complete B split count with analytic expansion fits the retained piece bound. -/ b_count :
    fragments.b.fragments.splits.count * (2 *
    (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceDomainBank.stepsBound domains) + 5) ≤
    pieces

constructive_injectivity NewtonPeriodRequest

namespace NewtonPeriodRequest

variable {domains : FaceDomainBank frames
  grid.punctured.faces.regulars}

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Approximation in
open Purelib.Data in
/-- Acquiring a covered period request preserves the supplied minimum polynomial index. -/
theorem ofCover_indices {source : Hyperelliptic.Differentials.Basic.Differential genus}
    {root : Gaussian.Name.Basic.Named}
    {initial : Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState curve source root}
    {targets : List (Hyperelliptic.Differentials.Basic.Differential genus)} {count minimum : Nat}
    (cover : CoveredPeriodStage initial targets count minimum) (differential :
      Hyperelliptic.Differentials.Basic.Differential genus)
    (target : Rat.Fraction.Rational) (positive : 0 < target) (floor : Nat) :
    IndicesAbove floor (CoveredPeriodRequest.ofCover cover differential target positive floor).request.requests := by
  let requested := CoveredPeriodRequest.ofCover cover differential target positive floor
  have equal : requested.request.minimumIndex = floor := ControlledSumRequest.acquire_minimumIndex ..
  exact equal ▸ requested.request.indices_ge

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Approximation in
open Purelib.Data in

open Purelib.Curves in
open Purelib.Data in
open Purelib.RootIsolation in
/-- Prepare shared-face requests for both original corrected periods.

The original covers determine a common piece count, which selects the scalar floor before either polynomial request is
acquired. Both assignments retain their original owners and count evidence. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (grid :
  NewtonGrid preparation bandTarget radius)
    (differential index : Fin genus) (minimum : Nat) (target : Rat.Fraction.Rational) (positive : 0 < target)
    {frames : RootIsolation.SquareRoot.Grid.RootFrames grid.punctured.bank.grid}
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.punctured.faces.regulars)
      :
    NewtonPeriodRequest prepared grid differential index minimum target domains := by
  let aCover := CoveredPeriodStage.acquire (prepared.aWalk index).initial (standardDifferentials genus) genus minimum
  let bCover := CoveredPeriodStage.acquire (prepared.bWalk index).initial (standardDifferentials genus) genus minimum
  let parents := aCover.retained.current.state.parents.length + bCover.retained.current.state.parents.length
  let gridCount := grid.punctured.bank.grid.vertical.length + grid.punctured.bank.grid.horizontal.length + 1
  let analyticCount := 2 *
    (Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceDomainBank.stepsBound domains) + 5
  let pieces := parents * gridCount * analyticCount
  have smallPositive : 0 < target / 4 := Rat.Fraction.Order.Field.div_pos_direct positive (by decide)
  let scalars := Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.build
    (standardDifferential differential) pieces (target / 4) smallPositive domains
  let floor := Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.index scalars
  let a := CoveredPeriodRequest.ofCover aCover (standardDifferential differential) (target / 4) smallPositive floor
  let b := CoveredPeriodRequest.ofCover bCover (standardDifferential differential) (target / 4) smallPositive floor
  let fragments := NewtonFragments.ofRequests prepared grid a b
  have aCount : fragments.a.fragments.splits.count * analyticCount ≤ pieces := by
    have bound := fragments.a.fragments.splits.count_le
    simp only [fragments.a.axes.vertical_eq, fragments.a.axes.horizontal_eq, Data.List.Map.length_map] at bound
    exact Nat.mul_le_mul_right analyticCount (bound.trans (Nat.mul_le_mul_right gridCount (Nat.le_add_right _ _)))
  have bCount : fragments.b.fragments.splits.count * analyticCount ≤ pieces := by
    have bound := fragments.b.fragments.splits.count_le
    simp only [fragments.b.axes.vertical_eq, fragments.b.axes.horizontal_eq, Data.List.Map.length_map] at bound
    exact Nat.mul_le_mul_right analyticCount (bound.trans (Nat.mul_le_mul_right gridCount (Nat.le_add_left _ _)))
  exact ⟨pieces, scalars, fragments, fragments.a.assign domains, fragments.b.assign domains,
    ofCover_indices .., ofCover_indices .., aCount, bCount⟩

section
open Purelib.Curves
open Purelib.Data
/-- The ordered A and B entry points followed by the supplied additional points. -/
@[expose] def points (request : NewtonPeriodRequest prepared grid differential index minimum target domains)
    (extra : List Gaussian.Basic.Canonical) : List Gaussian :=
      ((Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points
      request.aEntries) ++
      (Hyperelliptic.Meshes.PuncturedGrid.Fragment.PointBanks.RegularPrimitiveSplits.SheetEntries.points
      request.bEntries)) ++ extra

/-- The retained face scalar budgets specialized to the combined point list. -/
@[expose] def budgets (request : NewtonPeriodRequest prepared grid differential index minimum target domains)
    (extra : List Gaussian.Basic.Canonical) :=
      Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.meshes (request.points
      extra) request.scalars

end

open Purelib.Curves in
open Purelib.Data in
set_option genInjectivity false in
/-- Retain both period sums on one supplied numerical bank and shared point mesh.

Each sum retains its actual sheet entries and a strict quarter-target bound; both refer to the same original face-domain
owners. -/
structure Readings (request : NewtonPeriodRequest prepared grid differential index minimum target domains)
    (extra : List Gaussian.Basic.Canonical) {numericalIndex : Nat}
    (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (standardDifferential
      differential) numericalIndex domains) where
  /-- The shared point meshes on the exact supplied face-primitive bank. -/ meshes :
    Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes (request.budgets extra) numerics
  /-- The retained A-fragment sum on the shared mesh. -/ a :
    Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.SharedSum meshes
    request.aEntries
  /-- The retained B-fragment sum on the shared mesh. -/ b :
    Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.SharedSum meshes
    request.bEntries
  /-- The A-fragment comparison bound is strictly below one quarter of the target. -/ a_small : a.bound < target / 4
  /-- The B-fragment comparison bound is strictly below one quarter of the target. -/ b_small : b.bound < target / 4

constructive_injectivity Readings

open Purelib.Curves in
open Purelib.Data in
/-- Read both requested sums from the supplied later numerical bank.

One shared point mesh supplies both retained sums, and the original index and count payments certify their strict
quarter-target bounds. -/
@[expose] def readWith (request : NewtonPeriodRequest prepared grid differential index minimum target domains)
    (positive : 0 < target) (extra : List Gaussian.Basic.Canonical) {numericalIndex : Nat}
    (numerics : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank (standardDifferential
      differential) numericalIndex domains)
    (later : Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.index
      request.scalars ≤ numericalIndex) : request.Readings extra numerics := by
  let meshes := Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes.FaceSharedMeshes.build (request.budgets extra)
    numerics
    ((Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets.BranchCellBank.FaceScalarBudgets.meshes_index
      request.scalars (request.points extra)).le.trans later)
  let a := Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.SharedSum.build
    meshes request.aEntries
    (fun _ member => List.mem_append_left _ (List.mem_append_left _ member))
  let b := Hyperelliptic.Meshes.PuncturedGrid.Fragment.SharedSums.RegularPrimitiveSplits.SheetEntries.SharedSum.build
    meshes request.bEntries
    (fun _ member => List.mem_append_left _ (List.mem_append_right _ member))
  have smallPositive : 0 < target / 4 := Rat.Fraction.Order.Field.div_pos_direct positive (by decide)
  exact ⟨meshes, a, b, a.bound_lt smallPositive later request.a_indices request.a_count,
    b.bound_lt smallPositive later request.b_indices request.b_count⟩

open Purelib.Data in
/-- Two successive squared-error comparisons below quarter-target allowances pay the full target. -/
private theorem pay {x y z : Gaussian.Basic.Canonical} {target bound : Rat.Fraction.Rational}
    (mesh : Data.Gaussian.Norm.Basic.normSq (x - y) ≤ bound) (small : bound < target / 4)
    (period : Data.Gaussian.Norm.Basic.normSq (y - z) < target / 4) : Data.Gaussian.Norm.Basic.normSq (x - z) <
      target := by
  rw [show x - z = (x - y) + (y - z) by ring1]
  have first := mesh.trans_lt small
  have sum := (Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct first (Data.Gaussian.Norm.Basic.normSq (y -
    z))).trans
    (Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct period (target / 4))
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rat.Fraction.Rational) < 2)
      sum).trans_eq (by
      rw [show 2 * (target / 4 + target / 4) = (target / 4) * 4 by ring1]
      exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

namespace Readings

variable {request : NewtonPeriodRequest prepared grid differential index minimum target domains}
  {extra : List Purelib.Data.Gaussian.Basic.Canonical} {numericalIndex : Nat}
  {numerics : FacePrimitiveBank
    (standardDifferential differential) numericalIndex domains}

open Purelib.Data
/-- The retained A sum approximates the original prepared A-period sample within the target at every permitted later
stage. -/
theorem a_accurate (readings : request.Readings extra numerics)
    (stage : Nat) (later : request.fragments.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (readings.a.value -
      ((prepared.periodData.aProgram differential index).integral.model stage).integralSample) < target := by
  have mesh := readings.a.accurate
  rw [← request.fragments.a.comparison.request.increments_eq,
    ← request.fragments.a.comparison.request.primitiveSum_eq] at mesh
  exact pay mesh readings.a_small (request.fragments.a.comparison.accurate
    (standardDifferential_mem_standardDifferentials differential) stage
    ((Data.Nat.Order.le_max_left _ _).trans (request.fragments.stage_eq ▸ later)))

/-- The retained B sum approximates the original prepared B-period sample within the target at every permitted later
stage. -/
theorem b_accurate (readings : request.Readings extra numerics)
    (stage : Nat) (later : request.fragments.stage ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (readings.b.value -
      ((prepared.periodData.bProgram differential index).integral.model stage).integralSample) < target := by
  have mesh := readings.b.accurate
  rw [← request.fragments.b.comparison.request.increments_eq,
    ← request.fragments.b.comparison.request.primitiveSum_eq] at mesh
  exact pay mesh readings.b_small (request.fragments.b.comparison.accurate
    (standardDifferential_mem_standardDifferentials differential) stage
    ((Data.Nat.Order.le_max_right _ _).trans (request.fragments.stage_eq ▸ later)))

end Readings
end NewtonPeriodRequest
end Purelib.Riemann.Periods.NewtonRequestedPairedPeriods
