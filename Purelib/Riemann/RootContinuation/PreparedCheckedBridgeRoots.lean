module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Transport.PreparedOwnerHandoffChecks
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Topology.PreparedBankRootChains

public import Purelib.RootIsolation.SquareRoot.Preparation.Handoff.Refinement
public import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Geometry.Rational.Box.Separation.Certificate

@[expose] public section

/-!
# Checked root closure of the original two-bank period state

Successful handoff checks supply the two missing root joins of an existing
prepared bridge. Assemble the root chain of that very initial period state,
retaining its original banks, centers, parent order, and stationary label
cells. No replacement owner or branch-boundary tour is inserted.

This is a conditional certificate consumer, not an automatic symplectic
realization. In particular, root closure of a connector-only retrace does
not make it a nontrivial B cycle. The later root-safe states use their own
checked depth choices; equality to the legacy scheduler's later samples is
not asserted here.
-/

namespace Purelib.Riemann.RootContinuation.PreparedCheckedBridgeRoots.HandoffOutcome

open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Transport.PreparedOwnerHandoffChecks.SquareRootTrace (HandoffOutcome)

open Purelib.Approximation.Gaussian
open Purelib.Geometry.Rational
/-- Whether a handoff outcome certifies containment in one of the two owners.

Both containment outcomes are accepted; distinct and inconclusive outcomes provide no root agreement. -/
def Accepted {first last : Name.Basic.Named} {left right : Box} : HandoffOutcome first last left right →
  Prop
  | .leftInside _ _ => True
  | .rightInside _ _ => True
  | .distinct _ _ => False
  | .inconclusive _ => False

/-- Decide acceptance from the retained handoff outcome constructor. -/
instance acceptedDecidable {first last : Name.Basic.Named} {left right : Box}
    (outcome : HandoffOutcome first last left right) : Decidable (Accepted outcome) := by
  cases outcome <;> unfold Accepted <;> infer_instance

/-- Read root-name equivalence from an accepted handoff outcome.

Uses the actual containment certificate and eliminates the impossible accepted distinct or inconclusive cases. -/
def agreement {first last : Name.Basic.Named} {left right : Box} :
    (outcome : HandoffOutcome first last left right) → Accepted outcome → Equivalence.NamedEquivalent first last
  | .leftInside _ equivalent, _ => equivalent ()
  | .rightInside _ equivalent, _ => equivalent ()
  | .distinct _ _, accepted => accepted.elim
  | .inconclusive _, accepted => accepted.elim

end Purelib.Riemann.RootContinuation.PreparedCheckedBridgeRoots.HandoffOutcome

namespace Purelib.Riemann.RootContinuation.PreparedCheckedBridgeRoots.PreparedDoublePath

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints (RootClosedState)
open Purelib.Riemann.Topology.PreparedCycleModels (PreparedDoublePath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Topology.PreparedBankRootChains (dyadicBankRootChain)
open Purelib.Riemann.Transport.PreparedOwnerHandoffChecks.PreparedCycleModels.PreparedDoublePath (Handoffs)
open Purelib.Riemann.Integration.PreparedSwitchedRefinements
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.RootIsolation.SquareRoot.Preparation.Handoff.Refinement (OwnerHandoffAttempt)
open Purelib.Riemann.RootContinuation.PreparedCheckedBridgeRoots.HandoffOutcome (Accepted agreement)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

open Purelib.Approximation.Gaussian in
set_option genInjectivity false in
/-- Root-name agreements at the turn and return of a doubled path.

Keeps the forward-finish/backward-start and backward-finish/forward-start comparisons separate. -/
structure TwoRootJoins (forwardFinish backwardStart backwardFinish forwardStart : Name.Basic.Named) where
  /-- Agreement between the forward finish and backward start root names. -/ atTurn : Equivalence.NamedEquivalent
    forwardFinish backwardStart
  /-- Agreement between the backward finish and forward start root names. -/ atReturn : Equivalence.NamedEquivalent
    backwardFinish forwardStart

constructive_injectivity TwoRootJoins

open Purelib.Riemann.Paths in
/-- Endpoint root agreements for the actual forward and backward path owners. -/
abbrev RootJoins (data : PreparedDoublePath curve) :=
  TwoRootJoins (ownerName (PreparedPathGluing.finishOwner data.forward)) (ownerName data.backwardOwner)
    (ownerName (PreparedPathGluing.finishOwner data.backward)) (ownerName data.forwardOwner)

open Purelib.Approximation.Gaussian in
/-- Transport accepted checked handoffs to the original doubled-path owners.

Uses the stored finish-owner equalities to retain the exact turn and return comparisons supplied by the checks. -/
def rootJoinsOfChecks (data : PreparedDoublePath curve) (checked : Handoffs data)
    (turnAccepted : Accepted checked.atFinish.report.outcome)
    (returnAccepted : Accepted checked.atStart.report.outcome) : RootJoins data :=
  ⟨cast (congrArg (fun first => Equivalence.NamedEquivalent first (ownerName data.backwardOwner))
      (congrArg ownerName checked.atFinish.finishOwner_eq))
      (agreement checked.atFinish.report.outcome turnAccepted),
    cast (congrArg (fun first => Equivalence.NamedEquivalent first (ownerName data.forwardOwner))
      (congrArg ownerName checked.atStart.finishOwner_eq))
      (agreement checked.atStart.report.outcome returnAccepted)⟩

open Purelib.Riemann.Paths in
open Purelib.RootIsolation in
/-- Read both root joins from accepted original owner handoff attempts.

The attempts are already indexed by the actual path endpoint owners, so their retained agreement witnesses are used
directly. -/
def rootJoinsOfAttempts (data : PreparedDoublePath curve)
    (turn : SquareRoot.Preparation.Handoff.Refinement.OwnerHandoffAttempt (PreparedPathGluing.finishOwner data.forward)
      data.backwardOwner)
    (back : SquareRoot.Preparation.Handoff.Refinement.OwnerHandoffAttempt (PreparedPathGluing.finishOwner data.backward)
      data.forwardOwner)
    (turnAccepted : Accepted turn.outcome) (returnAccepted : Accepted back.outcome) : RootJoins data :=
  ⟨agreement turn.outcome turnAccepted, agreement back.outcome returnAccepted⟩

section
open Purelib.Curves.Hyperelliptic
open Purelib.Riemann.Topology
/-- Build the closed root chain of a prepared bridge from its two joins.

Appends the actual forward and backward dyadic-bank chains, transports the turn and return names, and casts only the
exact bridge parent-list identity. -/
def initialRootChain (data : PreparedDoublePath curve) (differential : Differentials.Basic.Differential genus)
    (joins : RootJoins data) :
    RootChain (bridgeState curve differential data).parents
      (ownerName data.forwardOwner) (ownerName data.forwardOwner) :=
  let forward := dyadicBankRootChain curve differential 0 data.forwardChecked
  let backward := (dyadicBankRootChain curve differential 1 data.backwardChecked).changeStart joins.atTurn
  PreparedBankRootChains.RootChain.castChildren
    (bridgeState_parents curve differential data).symm
    (PreparedBankRootChains.RootChain.changeFinish
      (forward.append backward) joins.atReturn)

/-- Retain a root-closed initial bridge state with its original parents.

Keeps the compact cycle state and transports the constructed root chain through its exact parent readback. -/
def rootClosedInitial (data : PreparedDoublePath curve) (differential : Differentials.Basic.Differential genus)
    (joins : RootJoins data) : RootClosedState curve differential (ownerName data.forwardOwner) where
  state := compactCycleState curve differential (.bridge data)
  closed := rfl
  roots := PreparedBankRootChains.RootChain.castChildren
    (compactCycleState_parents curve differential (.bridge data)).symm
    (initialRootChain data differential joins)

end

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
/-- The retained root-closed bridge state is the original schedule's initial state. -/
theorem rootClosedInitial_state (data : PreparedDoublePath curve) (differential : Differentials.Basic.Differential
  genus)
    (joins : RootJoins data) :
    (rootClosedInitial data differential joins).state =
      (⟨differential, .bridge data⟩ : PreparedRefinementProgramCore.StandardSwitchedClosedSchedule
        curve).toDifferential.initial := rfl

end Purelib.Riemann.RootContinuation.PreparedCheckedBridgeRoots.PreparedDoublePath
