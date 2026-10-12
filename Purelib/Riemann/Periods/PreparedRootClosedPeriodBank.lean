module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Riemann.Integration.PreparedOwnerClosedSchedules
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Topology.PreparedCycleModels

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
public import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
public import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-!
# Retained root-closed A/B period banks

Each row retains its two prepared tours and their actual initial integration
states.  The A and reference-bridge B programs refine these cached states,
with one common operational base root and all finite root joins preserved.
The finite row vector is materialized once rather than rebuilding tours for
each differential entry.  Geometric symplectic realization remains separate.
-/

namespace Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.RootClosedState

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named)
open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState (period)

open Purelib.Curves.Hyperelliptic
/-- Transport the retained closed state along an exact equality of its root name. -/
def castRoot {genus : Nat} {curve : Basic.HyperellipticCurve genus} {source : Differentials.Basic.Differential genus}
    {first second : Named} (initial : RootClosedState curve source first) (equal : first = second) :
    RootClosedState curve source second := by
  cases equal
  exact initial

/-- Transporting the root-name index preserves the exact switched state. -/
theorem castRoot_state {genus : Nat} {curve : Basic.HyperellipticCurve genus} {source : Differentials.Basic.Differential
  genus}
    {first second : Named} (initial : RootClosedState curve source first) (equal : first = second) :
    (castRoot initial equal).state = initial.state := by
  cases equal
  rfl

/-- Transporting the root-name index preserves the exact period refinement program. -/
theorem castRoot_period {genus : Nat} {curve : Basic.HyperellipticCurve genus} {source :
  Differentials.Basic.Differential genus}
    {first second : Named} (initial : RootClosedState curve source first) (equal : first = second)
    (targets : List (Differentials.Basic.Differential genus)) (differential : Differentials.Basic.Differential genus)
      (member : differential ∈ targets) :
    period (castRoot initial equal) targets differential member = period initial targets differential member := by
  cases equal
  rfl

/-- Every root-safe refinement stage preserves the initial lifted starting point. -/
theorem states_start_eq {genus : Nat} {curve : Basic.HyperellipticCurve genus} {source :
  Differentials.Basic.Differential genus}
    {root : Named} (initial : RootClosedState curve source root) (targets : List (Differentials.Basic.Differential
      genus)) :
    ∀ stage, (initial.states targets stage).state.start = initial.state.start
  | 0 => rfl
  | stage + 1 => (initial.scheduledStep targets stage).start_eq.trans (states_start_eq initial targets stage)

end Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.RootClosedState

namespace Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Basis (CertifiedPeriodProgram)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Integration.PreparedOwnerClosedBridges (OwnerClosedCyclePair)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState (period)
open Purelib.Riemann.Integration.PreparedRefinementProgramCore (standardDifferentials
  standardDifferential_mem_standardDifferentials)

namespace OwnerClosedCyclePair

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

section
open Purelib.Curves.Hyperelliptic
open Purelib.Riemann.Periods
open Purelib.Riemann.Topology
/-- Read the original A tour's initial closed state indexed by the pair's retained shared root name. -/
def aInitial (pair : OwnerClosedCyclePair curve) (source : Differentials.Basic.Differential genus) :
    RootClosedState curve source pair.root :=
  PreparedRootClosedPeriodBank.RootClosedState.castRoot
    (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial pair.aTour source)
    pair.aRoot_eq

/-- Read the original B tour's initial closed state indexed by the pair's retained shared root name. -/
def bInitial (pair : OwnerClosedCyclePair curve) (source : Differentials.Basic.Differential genus) :
    RootClosedState curve source pair.root :=
  PreparedRootClosedPeriodBank.RootClosedState.castRoot
    (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial pair.bTour source)
    pair.bRoot_eq

/-- Reading the A initial state preserves the original tour's exact switched state. -/
theorem aInitial_state (pair : OwnerClosedCyclePair curve) (source : Differentials.Basic.Differential genus) :
    (aInitial pair source).state =
      (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial pair.aTour source).state :=
  PreparedRootClosedPeriodBank.RootClosedState.castRoot_state _ _

/-- Reading the B initial state preserves the original tour's exact switched state. -/
theorem bInitial_state (pair : OwnerClosedCyclePair curve) (source : Differentials.Basic.Differential genus) :
    (bInitial pair source).state =
      (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial pair.bTour source).state :=
  PreparedRootClosedPeriodBank.RootClosedState.castRoot_state _ _

/-- The retained A initial state gives the original tour's exact period program. -/
theorem aInitial_period (pair : OwnerClosedCyclePair curve) (source : Differentials.Basic.Differential genus)
    (targets : List (Differentials.Basic.Differential genus)) (differential : Differentials.Basic.Differential genus)
      (member : differential ∈ targets) :
    period (aInitial pair source) targets differential member =
      period (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial pair.aTour source)
        targets differential member :=
  PreparedRootClosedPeriodBank.RootClosedState.castRoot_period _ _ _ _ _

/-- The retained B initial state gives the original tour's exact period program. -/
theorem bInitial_period (pair : OwnerClosedCyclePair curve) (source : Differentials.Basic.Differential genus)
    (targets : List (Differentials.Basic.Differential genus)) (differential : Differentials.Basic.Differential genus)
      (member : differential ∈ targets) :
    period (bInitial pair source) targets differential member =
      period (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial pair.bTour source)
        targets differential member :=
  PreparedRootClosedPeriodBank.RootClosedState.castRoot_period _ _ _ _ _

end

end OwnerClosedCyclePair

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
set_option genInjectivity false in
/-- A retained tour pair with exact initial A and B root-closed states.

Both original initial states are indexed by the same stored root name and source differential, with equalities tying
them to their respective tours. -/
structure RootClosedPeriodRow {genus : Nat} (curve : Basic.HyperellipticCurve genus) where
  /-- The original owner-closed A and B tour pair sharing a root name. -/ tours : OwnerClosedCyclePair curve
  /-- The retained source differential used by both initial states. -/ source : Differentials.Basic.Differential genus
  /-- The exact retained A root-closed initial state. -/ aInitial : RootClosedState curve source tours.root
  /-- The exact retained B root-closed initial state. -/ bInitial : RootClosedState curve source tours.root
  /-- The retained A initial state equals construction from the original A tour. -/ aInitial_eq : aInitial =
    PreparedRootClosedPeriodBank.PreparedCycleModels.OwnerClosedCyclePair.aInitial tours source
  /-- The retained B initial state equals construction from the original B tour. -/ bInitial_eq : bInitial =
    PreparedRootClosedPeriodBank.PreparedCycleModels.OwnerClosedCyclePair.bInitial tours source

constructive_injectivity RootClosedPeriodRow

namespace RootClosedPeriodRow

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
/-- Cache the exact A and B root-closed initial states of the supplied tour pair. -/
def ofTours (tours : OwnerClosedCyclePair curve) (source : Differentials.Basic.Differential genus) : RootClosedPeriodRow
  curve :=
  let aInitial := PreparedRootClosedPeriodBank.PreparedCycleModels.OwnerClosedCyclePair.aInitial tours source
  let bInitial := PreparedRootClosedPeriodBank.PreparedCycleModels.OwnerClosedCyclePair.bInitial tours source
  ⟨tours, source, aInitial, bInitial, rfl, rfl⟩

/-- Read the retained A initial state's root-safe stage for the standard differential family. -/
def aState (row : RootClosedPeriodRow curve) (stage : Nat) : RootClosedState curve row.source row.tours.root :=
  row.aInitial.states (standardDifferentials genus) stage

/-- Read the retained B initial state's root-safe stage for the standard differential family. -/
def bState (row : RootClosedPeriodRow curve) (stage : Nat) : RootClosedState curve row.source row.tours.root :=
  row.bInitial.states (standardDifferentials genus) stage

section
open Purelib.Curves.Hyperelliptic
open Purelib.Riemann.Integration
open Purelib.Riemann.Topology
/-- Recast the retained A-stage root chain to the requested differential with the same shared endpoint name. -/
def aRoots (row : RootClosedPeriodRow curve) (differential : Differentials.Basic.Differential genus) (stage : Nat) :
    RootChain
      ((row.aState stage).state.parents.map (PreparedEdgeRecasting.recastCenteredEdge differential))
      row.tours.root row.tours.root :=
  PreparedRecastRootChains.RootChain.recast differential (row.aState stage).roots

/-- Recast the retained B-stage root chain to the requested differential with the same shared endpoint name. -/
def bRoots (row : RootClosedPeriodRow curve) (differential : Differentials.Basic.Differential genus) (stage : Nat) :
    RootChain
      ((row.bState stage).state.parents.map (PreparedEdgeRecasting.recastCenteredEdge differential))
      row.tours.root row.tours.root :=
  PreparedRecastRootChains.RootChain.recast differential (row.bState stage).roots

end

section
open Purelib.Geometry.Path.Gaussian
open Purelib.Riemann.Periods
/-- The retained A and B states share the same lifted starting point at independently chosen stages. -/
theorem states_base_eq (row : RootClosedPeriodRow curve) (aStage bStage : Nat) :
    (row.aState aStage).state.start = (row.bState bStage).state.start := by
  unfold aState bState
  rw [PreparedRootClosedPeriodBank.RootClosedState.states_start_eq,
    PreparedRootClosedPeriodBank.RootClosedState.states_start_eq, row.aInitial_eq, row.bInitial_eq,
    PreparedRootClosedPeriodBank.PreparedCycleModels.OwnerClosedCyclePair.aInitial_state,
      PreparedRootClosedPeriodBank.PreparedCycleModels.OwnerClosedCyclePair.bInitial_state]
  exact congrArg (fun coordinate => (⟨coordinate, 0⟩ : Lifted.Basic.LiftedPoint 2)) row.tours.base_eq

/-- The closed A-cycle refinement sequence from the retained A initial state. -/
def aCycle (row : RootClosedPeriodRow curve) : Lifted.Refinement.LiftedCycleRefinement 2 :=
  PreparedRootSafePeriodPrograms.RootClosedState.cycle row.aInitial (standardDifferentials genus)

/-- The closed B-cycle refinement sequence from the retained B initial state. -/
def bCycle (row : RootClosedPeriodRow curve) : Lifted.Refinement.LiftedCycleRefinement 2 :=
  PreparedRootSafePeriodPrograms.RootClosedState.cycle row.bInitial (standardDifferentials genus)

end

section
open Purelib.Curves.Hyperelliptic.Integration
open Purelib.Riemann.Periods
/-- The requested standard differential's certified period on the retained A-cycle sequence. -/
def aProgram (row : RootClosedPeriodRow curve) (differential : Fin genus) :
    Algebraic.Period.Basis.CertifiedPeriodProgram curve (PeriodMatrix.standardDifferential differential) row.aCycle :=
  PreparedRootSafePeriodPrograms.RootClosedState.certifiedPeriodProgram row.aInitial (standardDifferentials genus)
    (PeriodMatrix.standardDifferential differential)
    (standardDifferential_mem_standardDifferentials differential)

/-- The requested standard differential's certified period on the retained B-cycle sequence. -/
def bProgram (row : RootClosedPeriodRow curve) (differential : Fin genus) :
    Algebraic.Period.Basis.CertifiedPeriodProgram curve (PeriodMatrix.standardDifferential differential) row.bCycle :=
  PreparedRootSafePeriodPrograms.RootClosedState.certifiedPeriodProgram row.bInitial (standardDifferentials genus)
    (PeriodMatrix.standardDifferential differential)
    (standardDifferential_mem_standardDifferentials differential)

end

section
open Purelib.Curves.Hyperelliptic
open Purelib.Riemann.Periods
open Purelib.Riemann.Topology
/-- The cached A entry's integral is the exact original tour's period program. -/
theorem ofTours_aProgram_integral (tours : OwnerClosedCyclePair curve) (source : Differentials.Basic.Differential genus)
    (differential : Fin genus) :
    ((ofTours tours source).aProgram differential).integral =
      period (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial tours.aTour source)
        (standardDifferentials genus)
        (PeriodMatrix.standardDifferential differential)
        (standardDifferential_mem_standardDifferentials differential) :=
  PreparedRootClosedPeriodBank.PreparedCycleModels.OwnerClosedCyclePair.aInitial_period tours source _ _ _

/-- The cached B entry's integral is the exact original tour's period program. -/
theorem ofTours_bProgram_integral (tours : OwnerClosedCyclePair curve) (source : Differentials.Basic.Differential genus)
    (differential : Fin genus) :
    ((ofTours tours source).bProgram differential).integral =
      period (PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial tours.bTour source)
        (standardDifferentials genus)
        (PeriodMatrix.standardDifferential differential)
        (standardDifferential_mem_standardDifferentials differential) :=
  PreparedRootClosedPeriodBank.PreparedCycleModels.OwnerClosedCyclePair.bInitial_period tours source _ _ _

end

/-- The A program reads exactly the retained A-stage model for the requested standard differential. -/
theorem aProgram_model (row : RootClosedPeriodRow curve) (differential : Fin genus) (stage : Nat) :
    ((row.aProgram differential).integral.model stage) = (row.aState stage).state.model
      (PeriodMatrix.standardDifferential differential) := rfl

/-- The B program reads exactly the retained B-stage model for the requested standard differential. -/
theorem bProgram_model (row : RootClosedPeriodRow curve) (differential : Fin genus) (stage : Nat) :
    ((row.bProgram differential).integral.model stage) = (row.bState stage).state.model
      (PeriodMatrix.standardDifferential differential) := rfl

section
open Purelib.Riemann.Integration
open Purelib.Riemann.Periods
/-- The retained A initial state has exactly two stationary switches. -/
theorem aInitial_switchCount (row : RootClosedPeriodRow curve) : row.aInitial.state.chain.switchCount = 2 := by
  rw [row.aInitial_eq, PreparedRootClosedPeriodBank.PreparedCycleModels.OwnerClosedCyclePair.aInitial_state]
  exact PreparedSwitchedRefinements.compactCycleState_switchCount _ _ _

/-- The retained B initial state has exactly two stationary switches. -/
theorem bInitial_switchCount (row : RootClosedPeriodRow curve) : row.bInitial.state.chain.switchCount = 2 := by
  rw [row.bInitial_eq, PreparedRootClosedPeriodBank.PreparedCycleModels.OwnerClosedCyclePair.bInitial_state]
  exact PreparedSwitchedRefinements.compactCycleState_switchCount _ _ _

end

open Purelib.Riemann.Integration
/-- Every retained A-period model has a nonempty cell list. -/
theorem aProgram_cells_positive (row : RootClosedPeriodRow curve) (differential : Fin genus) (stage : Nat) :
    0 < ((row.aProgram differential).integral.model stage).cells.length := by
  rw [row.aProgram_model, PreparedSwitchedRefinements.DirectSwitchedState.model_cells_length]
  have switches := row.aInitial.states_switchCount (standardDifferentials genus) stage
  rw [row.aInitial_switchCount] at switches
  change 0 < _ + (row.aInitial.states (standardDifferentials genus) stage).state.chain.switchCount
  rw [switches]
  omega

/-- Every retained B-period model has a nonempty cell list. -/
theorem bProgram_cells_positive (row : RootClosedPeriodRow curve) (differential : Fin genus) (stage : Nat) :
    0 < ((row.bProgram differential).integral.model stage).cells.length := by
  rw [row.bProgram_model, PreparedSwitchedRefinements.DirectSwitchedState.model_cells_length]
  have switches := row.bInitial.states_switchCount (standardDifferentials genus) stage
  rw [row.bInitial_switchCount] at switches
  change 0 < _ + (row.bInitial.states (standardDifferentials genus) stage).state.chain.switchCount
  rw [switches]
  omega

end RootClosedPeriodRow

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
set_option genInjectivity false in
/-- A finite vector of retained root-closed period rows indexed by the curve's genus.

Each row owns its original tour pair and cached initial states; the vector preserves their finite cycle order. -/
structure RootClosedPeriodBank {genus : Nat} (curve : Basic.HyperellipticCurve genus) where
  /-- The retained finite vector of root-closed period rows in cycle-index order. -/ rows : Data.Vector
    (RootClosedPeriodRow curve) genus

constructive_injectivity RootClosedPeriodBank

namespace RootClosedPeriodBank

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

open Purelib.Geometry.Path.Gaussian in
/-- Read the original paired A and B cycle families from the retained row vector. -/
def cycles (bank : RootClosedPeriodBank curve) : Lifted.Family.PairedCycleRefinements 2 genus where
  aCycle := fun index => (bank.rows index).aCycle
  bCycle := fun index => (bank.rows index).bCycle

/-- Read the paired cycles and standard-differential period programs from the same retained rows. -/
def periodData (bank : RootClosedPeriodBank curve) : PeriodMatrix.PeriodData curve where
  cycles := bank.cycles
  aProgram := fun differential cycle => (bank.rows cycle).aProgram differential
  bProgram := fun differential cycle => (bank.rows cycle).bProgram differential

section
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Branches
section
open Purelib.Data
/-- Construct the finite row bank from the exact supplied branch-isolation data.

Each cycle index retains its corresponding owner-closed tour pair and standard source differential in the resulting
vector. -/
def ofData (curve : Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve) : RootClosedPeriodBank curve
  :=
  ⟨Vector.Basic.vectorOfFn fun index =>
    RootClosedPeriodRow.ofTours (OwnerClosedCyclePair.ofData curve branches index) (PeriodMatrix.standardDifferential
      index)⟩

/-- The indexed row is exactly the retained tour-pair construction for that original branch-data index. -/
theorem ofData_row (curve : Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve) (index : Fin genus)
  :
    (ofData curve branches).rows index =
      RootClosedPeriodRow.ofTours (OwnerClosedCyclePair.ofData curve branches index)
        (PeriodMatrix.standardDifferential index) :=
  Vector.Basic.vectorOfFn_apply _ _

end

open Purelib.Riemann.Integration in
/-- The indexed A tour equals the original owner-closed A seed for the same branch data. -/
theorem ofData_aTour (curve : Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve) (index : Fin
  genus) :
    ((ofData curve branches).rows index).tours.aTour =
      PreparedOwnerClosedSchedules.PreparedRefinementPrograms.ownerClosedASeedOfData curve branches index := by
  rw [ofData_row]
  exact OwnerClosedCyclePair.ofData_aTour curve branches index

open Purelib.Riemann.Topology in
/-- The indexed B tour explicitly realizes the same original stage-zero reference bridge. -/
theorem ofData_bTour_realizesRaw (curve : Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (index : Fin genus) :
    PreparedCycleModels.PreparedCycleData.RealizesRaw (.finiteCut ((ofData curve branches).rows
      index).tours.bTour.joined.data)
      (OwnerClosedCyclePair.rawBridgeOfData curve branches index 0) := by
  rw [ofData_row]
  exact OwnerClosedCyclePair.ofData_bTour_realizesRaw curve branches index

/-- Construct the canonical root-closed bank, returning the empty vector for genus zero. -/
def ofCurve : {genus : Nat} → (curve : Basic.HyperellipticCurve genus) → RootClosedPeriodBank curve
  | 0, _ => ⟨.nil⟩
  | _ + 1, curve => ofData curve (BranchIsolation.data curve)

end

end RootClosedPeriodBank

end Purelib.Riemann.Periods.PreparedRootClosedPeriodBank.PreparedCycleModels
