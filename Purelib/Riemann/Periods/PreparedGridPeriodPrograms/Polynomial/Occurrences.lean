module

public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms.Polynomial
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet.Occurrences.Preparations
import Purelib.Riemann.Topology.PreparedRecastRootChains.Parents
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Data.List.Map

/-! # Positional six-channel attachment on the same canonical polynomial spine

The original root-closed state supplies actual operational root links. Their
existing differential recast and the retained spine's whole parent-factory
law identify the same physical occurrences, including repeated visits.
The supplied preparation family is consumed unchanged. New endpoint
refinements complete the original source bank without requiring old Ready.
-/

public section

namespace Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.PreparedBankRootChains (ownerName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {ambient : Box}
    {grid : ClearGrid (Fibre.frameCurve frame).polynomial ambient} {base : Canonical}
    {owner : Owner ((Fibre.frameCurve frame).polynomial.eval base)} {source : Differential 1}
    {walk : PeriodWalk grid base owner source}

/-- Recover actual operational root closure on the same cached recast parents of the original canonical spine.

The existing cached recast consumes the actual supplied parents. Their map
law is used only by erased root-name proofs; no parent, owner, root reading
or coefficient model is acquired or reconstructed by this operation.
-/
def roots (spine : PolynomialSpine (parameter := parameter) (frame := frame) walk) :
    RootChain spine.parents (ownerName owner) (ownerName owner) :=
  PreparedRecastRootChains.RootChain.recastOn (PeriodMatrix.standardDifferential (0 : Fin 1))
    walk.initial.roots spine.parents spine.parents_eq

/-- The recovered root chain is the original complete recast value after the exact cached-parent index transport. -/
private theorem packaged_roots_factory (spine : PolynomialSpine (parameter := parameter) (frame := frame) walk) :
    PreparedBankRootChains.RootChain.castChildren spine.parents_eq spine.roots =
      PreparedRecastRootChains.RootChain.recast
        (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.initial.roots :=
  PreparedRecastRootChains.RootChain.recastOn_eq (PeriodMatrix.standardDifferential (0 : Fin 1))
    walk.initial.roots spine.parents spine.parents_eq

/-- The recovered root chain is the original complete recast value after the exact cached-parent index transport. -/
theorem roots_factory (spine : PolynomialSpine (parameter := parameter) (frame := frame) walk) :
    PreparedBankRootChains.RootChain.castChildren spine.parents_eq spine.roots =
      PreparedRecastRootChains.RootChain.recast
        (PeriodMatrix.standardDifferential (0 : Fin 1)) walk.initial.roots :=
  packaged_roots_factory spine

/-- The cached polynomial spine retains exactly the accepted step count of the original prepared walk. -/
theorem parentCount (spine : PolynomialSpine (parameter := parameter) (frame := frame) walk) :
    spine.parents.length = walk.closed.traced.prepared.stepCount :=
  (congrArg List.length spine.parents_eq).trans
    ((Data.List.Map.length_map (recastCenteredEdge (PeriodMatrix.standardDifferential (0 : Fin 1)))
      walk.initial.state.parents).trans walk.initial_parentCount)

/-- The original zero-stage holomorphic model and the same retained polynomial spine have identical cell counts. -/
theorem initial_cellCount (spine : PolynomialSpine (parameter := parameter) (frame := frame) walk) :
    ((walk.program 0).integral.model 0).cells.length = spine.parents.length :=
  (congrArg List.length (walk.program_initial_cells 0)).trans
    ((Data.List.Map.length_map _ _).trans (congrArg List.length spine.parents_eq).symm)

/-- Positivity of the original retained zero-stage model proves nonemptiness of its same cached polynomial spine. -/
theorem nonempty_of_initial_cells_positive (spine : PolynomialSpine (parameter := parameter) (frame := frame) walk)
    (positive : 0 < ((walk.program 0).integral.model 0).cells.length) : spine.parents ≠ [] := by
  intro empty
  have countEq := spine.initial_cellCount.trans (congrArg List.length empty)
  exact Nat.lt_irrefl 0 (Eq.mp (congrArg (fun count => 0 < count) countEq) positive)

/-- A genuine positive accepted-step count proves that the same retained canonical spine has a source-bank entry. -/
theorem nonempty_of_stepCount_pos (spine : PolynomialSpine (parameter := parameter) (frame := frame) walk)
    (positive : 0 < walk.closed.traced.prepared.stepCount) : spine.parents ≠ [] := by
  intro empty
  have countEq : 0 = walk.closed.traced.prepared.stepCount :=
    (congrArg List.length empty).symm.trans spine.parentCount
  exact Nat.lt_irrefl 0 (Eq.mp (congrArg (fun count => 0 < count) countEq.symm) positive)

/-- Construct the positional source jet on the same canonical parents and supplied whole preparation family.

The original closed root links derive every endpoint comparison. The
constructor retains the original per-stage bank/check attempt, including
both old outcomes, and adds genuine endpoint refinements and admissions.
Its one jet supplies all six channels and both internally derived relation
certificates. Empty spines require their separate zero-cycle construction.
-/
def occurrenceJet (spine : PolynomialSpine (parameter := parameter) (frame := frame) walk) (floor rootStage : Nat)
    (prepared : (index : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      spine.covered floor (CellEndpoints.Targets.build spine.chain.path index))
    (nonempty : spine.parents ≠ []) :
    (actual : SynchronizedPeriodJet frame) ×
      Jets.Connection.ConnectionCertificate actual × Jets.PicardFuchs.PicardFuchsCertificate actual :=
  PreparedParents.StageAttempt.OccurrenceCompletion.ofPreparations (parameter := parameter) (frame := frame)
    (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor)
    spine.covered spine.chain prepared rootStage spine.roots nonempty

/-- The canonical constructor consumes the same cached cover, chain, supplied preparations and derived root closure. -/
private theorem packaged_occurrenceJet_factory
    (spine : PolynomialSpine (parameter := parameter) (frame := frame) walk) (floor rootStage : Nat)
    (prepared : (index : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      spine.covered floor (CellEndpoints.Targets.build spine.chain.path index))
    (nonempty : spine.parents ≠ []) :
    spine.occurrenceJet floor rootStage prepared nonempty =
      PreparedParents.StageAttempt.OccurrenceCompletion.ofPreparations (parameter := parameter) (frame := frame)
        (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor)
        spine.covered spine.chain prepared rootStage spine.roots nonempty := by rfl

/-- The canonical constructor consumes the same cached cover, chain, supplied preparations and derived root closure. -/
theorem occurrenceJet_factory
    (spine : PolynomialSpine (parameter := parameter) (frame := frame) walk) (floor rootStage : Nat)
    (prepared : (index : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      spine.covered floor (CellEndpoints.Targets.build spine.chain.path index))
    (nonempty : spine.parents ≠ []) :
    spine.occurrenceJet floor rootStage prepared nonempty =
      PreparedParents.StageAttempt.OccurrenceCompletion.ofPreparations (parameter := parameter) (frame := frame)
        (basis := PeriodMatrix.standardDifferential (0 : Fin 1)) (count := 1) (floor := floor)
        spine.covered spine.chain prepared rootStage spine.roots nonempty :=
  packaged_occurrenceJet_factory spine floor rootStage prepared nonempty

/-- The same retained canonical lifted cycle is the actual cycle of all six constructed source programmes. -/
theorem occurrenceJet_cycle
    (spine : PolynomialSpine (parameter := parameter) (frame := frame) walk) (floor rootStage : Nat)
    (prepared : (index : Nat) → PreparedParents (parameter := parameter) (frame := frame)
      spine.covered floor (CellEndpoints.Targets.build spine.chain.path index))
    (nonempty : spine.parents ≠ []) :
    (spine.occurrenceJet floor rootStage prepared nonempty).1.cycle = PreparedParents.constantCycle spine.chain := by
  rewrite [occurrenceJet_factory]
  exact PreparedParents.StageAttempt.OccurrenceCompletion.ofPreparations_cycle
    (parameter := parameter) (frame := frame) (basis := PeriodMatrix.standardDifferential (0 : Fin 1))
    (count := 1) (floor := floor) spine.covered spine.chain prepared rootStage spine.roots nonempty

end Purelib.Riemann.Periods.PreparedGridPeriodPrograms.PeriodWalk.PolynomialSpine

end
