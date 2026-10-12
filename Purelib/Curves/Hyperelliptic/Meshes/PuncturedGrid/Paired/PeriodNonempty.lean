module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathWinding

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.PreparedRootSafeCycleStates

open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints

@[expose] public section

open Purelib.Riemann.Paths.PreparedClearPathModels (CompleteSegment PreparedPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState (Step)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (Coordinate)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Pair
  Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea (PairedRow)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea (CommonLoop)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank (PairedPeriodBank)

/-!
# Nonempty integration cells on the corrected period family

A complete prepared segment must advance from parameter zero to one. Its
accepted steps therefore supply at least one parent. The actual root-safe
refinement multiplies the parent count by a positive dyadic factor, so a
nonempty grid walk remains nonempty at every period stage. The branch-pair
application reads the retained winding-one circuit in each outward leg.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.PreparedClearPathModels

namespace CompleteSegment

/-- A complete accepted segment from parameter zero to one contains at least one actual subdivision step. -/
theorem stepCount_positive {polynomial : ClearPath.GaussianPolynomial} {ambient :
  Rational.Box}
    {start finish : Data.Gaussian.Basic.Canonical} {segment : ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient} {owner : SquareRootContinuationChain.Owner (polynomial.eval start)}
    (prepared : PreparedClearPathModels.CompleteSegment segment within owner) : 0 < prepared.subdivision.stepCount := by
  rcases prepared with ⟨subdivision, endpoint⟩
  cases subdivision with
  | stop => exact (show (0 : Fraction.Rational) ≠ 1 by decide) endpoint |>.elim
  | next => exact Nat.zero_lt_succ _

end CompleteSegment

namespace PreparedPath

/-- The complete prepared path has at least as many actual subdivision steps as original segments. -/
theorem segmentCount_le_stepCount {polynomial : ClearPath.GaussianPolynomial} {ambient :
  Rational.Box}
    {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath polynomial ambient start
      finish}
    {owner : SquareRootContinuationChain.Owner (polynomial.eval start)} (prepared : PreparedClearPathModels.PreparedPath
      path owner) :
    path.segmentCount ≤ prepared.stepCount := by
  induction prepared with
  | nil => exact Nat.le_refl 0
  | cons head tail owner headWithin preparedHead preparedTail ih =>
      have positive :=
        CompleteSegment.stepCount_positive
        preparedHead
      change tail.segmentCount + 1 ≤ preparedHead.subdivision.stepCount + preparedTail.stepCount
      omega

end PreparedPath

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.PreparedClearPathModels

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.RootClosedState

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus} {root :
  Named}

namespace Step

/-- Root-safe refinement preserves positivity of the actual retained parent count. -/
theorem parents_positive {current : PreparedRefinementRootEndpoints.RootClosedState curve source root}
    {targets : List (Differentials.Basic.Differential genus)} {target : PreparedPrimitiveRequests.Coordinate} (step :
      RootClosedState.Step current targets target)
    (positive : 0 < current.state.parents.length) : 0 < step.next.state.parents.length := by
  rw [step.parents_eq, SynchronizedDirectBlockRefinement.children_length]
  exact Nat.mul_pos positive (Nat.pow_pos (by decide))

end Step

/-- Every retained refinement stage has positive parent count when the original stage does. -/
theorem states_parents_positive (initial : PreparedRefinementRootEndpoints.RootClosedState curve source root)
    (targets : List (Differentials.Basic.Differential genus)) (positive : 0 < initial.state.parents.length) :
    ∀ stage, 0 < (initial.states targets stage).state.parents.length
  | 0 => positive
  | stage + 1 => Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.RootClosedState.Step.parents_positive
    (initial.scheduledStep targets stage)
      (states_parents_positive
        initial targets positive stage)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.RootClosedState

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.Grid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)

variable {polynomial : GaussianPolynomial} {ambient :
  Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient}

namespace Walk

/-- Concatenating actual grid walks adds their edge counts. -/
theorem edgeCount_append : ∀ {start middle finish : Data.Gaussian.Basic.Canonical}
    (left : Walks.Walk grid start middle) (right : Walks.Walk grid middle finish),
    (left.append right).edgeCount = left.edgeCount + right.edgeCount
  | _, _, _, .nil _, _ => (Nat.zero_add _).symm
  | _, _, _, .cons _ tail, right => by
      change (tail.append right).edgeCount + 1 = (tail.edgeCount + 1) + right.edgeCount
      rw [edgeCount_append tail right]
      omega

/-- Transporting the endpoint indices preserves the actual grid walk edge count. -/
theorem edgeCount_castEndpoints {start finish first last : Data.Gaussian.Basic.Canonical}
    (walk : Walks.Walk grid start finish) (startEq : start = first) (finishEq : finish = last) :
    (walk.castEndpoints startEq finishEq).edgeCount = walk.edgeCount := by
  cases startEq
  cases finishEq
  rfl

/-- A grid walk with nonzero retained winding contains at least one actual edge. -/
theorem edgeCount_positive_of_winding : ∀ {start finish : Data.Gaussian.Basic.Canonical}
    (walk : Walks.Walk grid start finish), ClearPath.rawWinding walk.path ≠ 0 → 0 < walk.edgeCount
  | _, _, .nil _, nonzero => (nonzero rfl).elim
  | _, _, .cons _ _, _ => Nat.zero_lt_succ _

end Walk

namespace PeriodWalk

/-- Every model stage of the retained period program has positive cell count when its original walk is nonempty. -/
theorem program_cells_positive {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient} {base : Data.Gaussian.Basic.Canonical}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval base)} {source : Differentials.Basic.Differential
      genus}
    (prepared : PreparedGridPeriodPrograms.PeriodWalk grid base owner source) (nonempty : 0 <
      prepared.closed.walk.edgeCount)
    (differential : Fin genus) (stage : Nat) :
    0 < ((prepared.program differential).integral.model stage).cells.length := by
  rw [prepared.program_cellCount]
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.RootClosedState.states_parents_positive
    prepared.initial
  rw [prepared.initial_parentCount]
  apply Nat.lt_of_lt_of_le nonempty
  rw [← prepared.closed.walk.path_segmentCount]
  exact
    PreparedClearPathModels.PreparedPath.segmentCount_le_stepCount
    prepared.closed.traced.prepared

end PeriodWalk

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.Grid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}

namespace BasedBranchBank

/-- The actual lifted branch loop has the same edge count as its retained reference walk. -/
theorem liftedLoop_edgeCount (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (index : BranchIsolation.Data.Index
  branches) (sheet : Fin 2) :
    (bank.liftedLoop index sheet).walk.edgeCount = (bank.rows.get index).reference.walk.edgeCount :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.Grid.Walk.edgeCount_castEndpoints _ _ _

end BasedBranchBank

namespace BasedBranchBank.Pair

/-- The original closed branch-pair walk is nonempty because its winding-one excursion contains an edge. -/
theorem closed_edgeCount_positive {first last : BranchIsolation.Data.Index branches}
    (pair : BasedBranchBank.Pair bank first last sheet) : 0 < pair.closed.walk.edgeCount := by
  rw [pair.closed_eq]
  change 0 < (pair.outward.walk.append pair.returning.walk).edgeCount
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.Grid.Walk.edgeCount_append, pair.outward_eq,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.BasedBranchBank.liftedLoop_edgeCount]
  have positive :=
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.Grid.Walk.edgeCount_positive_of_winding
    (bank.rows.get first).reference.walk (by
    rw [(bank.rows.get first).reference.winding]
    decide)
  omega

end BasedBranchBank.Pair

namespace BasedBranchBank.PairedRow

/-- The actual corrected B walk remains nonempty after adjoining its retained preceding correction walks. -/
theorem corrected_edgeCount_positive {reference : BranchIsolation.Data.Index branches}
    {labels : BranchIsolation.Data.Index branches × BranchIsolation.Data.Index branches} {prior : BranchArea.CommonLoop
      lifted sheet}
    (row : BranchArea.PairedRow bank reference sheet labels prior) : 0 < row.corrected.walk.edgeCount := by
  rw [row.corrected_eq]
  change 0 < (row.b.closed.walk.append prior.walk).edgeCount
  rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.Grid.Walk.edgeCount_append]
  exact Nat.lt_of_lt_of_le
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.BasedBranchBank.Pair.closed_edgeCount_positive
      row.b)
    (Nat.le_add_right _ _)

end BasedBranchBank.PairedRow

namespace Prepared

variable {ordered :
  Ordered bank
  sheet} {paired : Paired ordered}
  (prepared : Prepared paired)

/-- Every genus-indexed retained A period program has positive cell count at every model stage. -/
theorem aProgram_cells_positive (differential index : Fin genus) (stage : Nat) :
    0 < ((prepared.periodData.aProgram differential index).integral.model stage).cells.length := by
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.Grid.PeriodWalk.program_cells_positive
    (prepared.aWalk index)
  rw [prepared.a_walk_eq]
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.BasedBranchBank.Pair.closed_edgeCount_positive
    (paired.row index).row.a

/-- Every genus-indexed retained B period program has positive cell count at every model stage. -/
theorem bProgram_cells_positive (differential index : Fin genus) (stage : Nat) :
    0 < ((prepared.periodData.bProgram differential index).integral.model stage).cells.length := by
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.Grid.PeriodWalk.program_cells_positive
    (prepared.bWalk index)
  rw [prepared.b_walk_eq]
  exact
    BasedBranchBank.PairedRow.corrected_edgeCount_positive
    (paired.row index).row

end Prepared
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.PairedPeriodBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

variable {genus : Nat} {curve : HyperellipticCurve genus}

/-- Every genus-indexed retained A period program has positive cell count at every model stage. -/
theorem aProgram_cells_positive (bank : PeriodBank.PairedPeriodBank curve) (differential index : Fin genus) (stage :
  Nat) :
    0 < ((bank.periodData.aProgram differential index).integral.model stage).cells.length := by
  cases bank with
  | empty zero => exact Fin.elim0 (Fin.cast zero index)
  | retained prepared =>
      exact Prepared.aProgram_cells_positive
        prepared differential index stage

/-- Every genus-indexed retained B period program has positive cell count at every model stage. -/
theorem bProgram_cells_positive (bank : PeriodBank.PairedPeriodBank curve) (differential index : Fin genus) (stage :
  Nat) :
    0 < ((bank.periodData.bProgram differential index).integral.model stage).cells.length := by
  cases bank with
  | empty zero => exact Fin.elim0 (Fin.cast zero index)
  | retained prepared =>
      exact Prepared.bProgram_cells_positive
        prepared differential index stage

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodNonempty.PairedPeriodBank
