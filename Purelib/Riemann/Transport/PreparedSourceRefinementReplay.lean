module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

public import Purelib.Riemann.Transport.PreparedDirectRefinementReplay
public import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Arithmetic

@[expose] public section

namespace Purelib.Riemann.Transport.PreparedSourceRefinementReplay

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements

open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Coordinate)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

section
open Purelib.Curves.Hyperelliptic
open Purelib.Riemann.Integration
/-- Build a differential-accurate refinement from the selected retained blocks.

Keeps the original selector's diameter, depth, meshes and allowances, with the supplied blocks' exact identity to the
mesh readback. -/
def fromBlocks (parents : List (CenteredEdge curve source))
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate)
    (selected : CheckedSelection parents targets target)
    (blocks : PreparedSwitchedRefinements.SynchronizedDirectBlockRefinement selected.depth selected.rootDiameter
      parents)
    (equal : blocks = selected.meshes.toBlocks) :
    DifferentialAccurateDirectRefinement parents targets target :=
  ⟨selected.rootDiameter, selected.positive, selected.depth, selected.meshes,
    selected.allowances, blocks, equal⟩

/-- Replaying the exact observed selection reproduces the original differential refinement.

Eliminates the retained selection and block identities without rebuilding the original executable meshes. -/
theorem fromBlocks_eq (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (targets : List (Differentials.Basic.Differential genus)) (target : Coordinate) (positive : 0 < target)
    (selected : CheckedSelection parents targets target)
    (observed : selected = checkedDirectSelection parents proper targets target positive)
    (blocks : PreparedSwitchedRefinements.SynchronizedDirectBlockRefinement selected.depth selected.rootDiameter
      parents)
    (equal : blocks = selected.meshes.toBlocks) :
    fromBlocks parents targets target selected blocks equal =
      differentialAccurateDirectRefinement parents proper targets target positive := by
  cases equal
  cases observed
  rfl

end

/-- Replay a source-accurate refinement from retained mesh-center witnesses.

Uses the selected meshes and their exact block readback for the singleton source differential. -/
def fromCenters (parents : List (CenteredEdge curve source)) (target : Coordinate)
    (selected : CheckedSelection parents [source] target)
    (centers : PreparedDirectRefinementReplay.BankCenters selected.meshes) : AccurateDirectRefinement parents target :=
  ⟨fromBlocks parents [source] target selected (PreparedDirectRefinementReplay.blocks selected.meshes centers)
    (PreparedDirectRefinementReplay.blocks_eq selected.meshes centers)⟩

/-- Retained centers reproduce the original source-accurate refinement.

Requires the observed selection to be the actual checked selector output at the positive target. -/
theorem fromCenters_eq (parents : List (CenteredEdge curve source)) (proper : AllParentsProper parents)
    (target : Coordinate) (positive : 0 < target)
    (selected : CheckedSelection parents [source] target)
    (observed : selected = checkedDirectSelection parents proper [source] target positive)
    (centers : PreparedDirectRefinementReplay.BankCenters selected.meshes) :
    fromCenters parents target selected centers = accurateDirectRefinement parents proper target positive :=
  congrArg AccurateDirectRefinement.mk (fromBlocks_eq parents proper [source] target positive selected observed _ _)

open Purelib.Riemann.Integration.PreparedSwitchedRefinements (DirectSwitchedState)

/-- Refine the original switched state using the retained source selection and centers.

Keeps its original parent bank and applies the exact source refinement reconstructed from the selected meshes. -/
def step (current : DirectSwitchedState curve source) (target : Coordinate)
    (selected : CheckedSelection current.parents [source] target)
    (centers : PreparedDirectRefinementReplay.BankCenters selected.meshes) :
    DirectSwitchedState curve source :=
  current.refineSource (fromCenters current.parents target selected centers)

/-- The retained source-replay step equals the original accurate refinement step.

Uses the exact observed selector output for the state's proper parent bank at a positive target. -/
theorem step_eq (current : DirectSwitchedState curve source) (target : Coordinate) (positive : 0 < target)
    (selected : CheckedSelection current.parents [source] target)
    (observed : selected = checkedDirectSelection current.parents current.proper [source] target positive)
    (centers : PreparedDirectRefinementReplay.BankCenters selected.meshes) :
    step current target selected centers =
      current.refineSource (accurateDirectRefinement current.parents current.proper target positive) := by
  unfold step
  rw [fromCenters_eq current.parents current.proper target positive selected observed centers]

/-- A source-replay step preserves readiness of the retained parent bank.

The original parent readiness and checked mesh-center witnesses supply readiness for every resulting child. -/
theorem step_ready (current : DirectSwitchedState curve source)
    (ready : PreparedDirectRefinementReplay.AllReady current.parents) (target : Coordinate)
    (selected : CheckedSelection current.parents [source] target)
    (centers : PreparedDirectRefinementReplay.BankCenters selected.meshes) :
    PreparedDirectRefinementReplay.AllReady (step current target selected centers).parents :=
  PreparedDirectRefinementReplay.blocks_ready selected.meshes centers ready

end Purelib.Riemann.Transport.PreparedSourceRefinementReplay
