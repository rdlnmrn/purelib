module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.RootContinuation.SquareRootContinuation
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
public import Purelib.RootIsolation.SquareRoot.Replay.PreparedRootStateReplay

import Purelib.Elab.Deriving.Repr
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.Owner.Local.Basic
import Purelib.RootIsolation.SquareRoot.Replay.PreparedBoundaryReplay
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

@[expose] public section

/-!
# Restoring nonstationary owner transport from its finite source state

A genuine parameter move forgets the incoming refinement function.  Every
branch of reserved transport constructs a fresh owner using only the finite
initial state.  A stationary move deliberately retains the original owner,
so this exact dependency boundary must not be extended to that case.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.PreparedOwnerTransportReplay

open Purelib.Riemann
open Purelib.Riemann.RootContinuation Purelib.Riemann.Integration

/-- The rational coordinate field of the retained replay measurements. -/
abbrev Coordinate := Fraction.Rational
/-- The exact Gaussian parameter type of the quadratic source. -/
abbrev Gaussian := Gaussian.Basic.Canonical
/-- The rational rectangular box used by the retained quadratic state. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original quadratic owner, including its actual track and refinement function. -/
abbrev Owner := Riemann.Topology.SquareRootContinuationChain.Owner
/-- The original winding-one state for the quadratic parameter and its retained ambient box. -/
abbrev State := SquareRoot.Replay.PreparedRootStateReplay.State

open Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance (reservedTransport ownerOfState)

/-- Nonstationary reserved transport depends on the complete finite initial
state, but not the incoming track's refinement function.  This covers the
same-box and fallback branches of the original total constructor alike. -/
theorem reservedTransport_eq_of_initial_eq
    {source target : SquareRoot.Replay.PreparedOwnerTransportReplay.Gaussian} (different : source ≠ target)
    (first second : SquareRoot.Replay.PreparedOwnerTransportReplay.Owner source) (ambient : first.ambient =
      second.ambient)
    (initial : ambient ▸ first.track.initial = second.track.initial)
    (targetNonzero : target ≠ 0)
    (firstSmall : Data.Gaussian.Norm.Basic.normSq (source - target) < first.track.initial.clearance.bound)
    (secondSmall : Data.Gaussian.Norm.Basic.normSq (source - target) < second.track.initial.clearance.bound)
    (reserve : SquareRoot.Replay.PreparedOwnerTransportReplay.Coordinate) :
    reservedTransport first targetNonzero firstSmall reserve =
      reservedTransport second targetNonzero secondSmall reserve := by
  cases first with
  | mk firstNonzero firstAmbient firstTrack =>
    cases second with
    | mk secondNonzero secondAmbient secondTrack =>
      cases ambient
      cases firstTrack
      cases secondTrack
      cases initial
      unfold reservedTransport
      rw [dif_neg different, dif_neg different]
      rfl

/-- A finite source-state checkpoint is enough to reproduce a nonstationary
transport exactly.  The arbitrary deferred representative is only an internal
input to the move, not a claim about the original source owner's history. -/
theorem reservedTransport_from_restored_state
    {source target : SquareRoot.Replay.PreparedOwnerTransportReplay.Gaussian} (original :
      SquareRoot.Replay.PreparedOwnerTransportReplay.Owner source)
    (different : source ≠ target) (targetNonzero : target ≠ 0)
    (restored : SquareRoot.Replay.PreparedRootStateReplay.Checked source original.ambient
      (SquareRoot.Replay.PreparedRootStateReplay.capture original.track.initial))
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < restored.state.clearance.bound)
    (originalSmall : Data.Gaussian.Norm.Basic.normSq (source - target) < original.track.initial.clearance.bound)
    (reserve : SquareRoot.Replay.PreparedOwnerTransportReplay.Coordinate) :
    reservedTransport (ownerOfState original.parameterNonzero restored.state)
        targetNonzero small reserve =
      reservedTransport original targetNonzero originalSmall reserve := by
  apply SquareRoot.Replay.PreparedOwnerTransportReplay.reservedTransport_eq_of_initial_eq different
    (ownerOfState original.parameterNonzero restored.state) original rfl _
    targetNonzero small originalSmall reserve
  exact restored.eq_original original.track.initial

/-- One of the retained state's boundary or four ambient-line clearance fields. -/
inductive Field where
  /-- The original box-boundary clearance field. -/ | boundary /-- The original left ambient-line clearance field. -/ |
    left /-- The original right ambient-line clearance field. -/ | right /-- The original bottom ambient-line clearance
    field. -/ | bottom /-- The original top ambient-line clearance field. -/ | top
deriving DecidableEq
derive_exposed_repr Purelib.RootIsolation.SquareRoot.Replay.PreparedOwnerTransportReplay.Field

/-- Read the original bound at the selected state-clearance field. -/
def Field.bound {source : SquareRoot.Replay.PreparedOwnerTransportReplay.Gaussian} {ambient :
  SquareRoot.Replay.PreparedOwnerTransportReplay.Box} (state : SquareRoot.Replay.PreparedOwnerTransportReplay.State
  source ambient) : SquareRoot.Replay.PreparedOwnerTransportReplay.Field →
  SquareRoot.Replay.PreparedOwnerTransportReplay.Coordinate
  | .boundary => state.clearance.bound
  | .left => state.ambientLeftClearance.bound
  | .right => state.ambientRightClearance.bound
  | .bottom => state.ambientBottomClearance.bound
  | .top => state.ambientTopClearance.bound

set_option genInjectivity false in
/-- A retained failure of the finite nonstationary ambient-transport replay checks.

Zero or stationary parameters, failed clearance and missed reserve identify this attempted reconstruction, without
asserting failure of the original total transport procedure. -/
inductive Failure {source : SquareRoot.Replay.PreparedOwnerTransportReplay.Gaussian} {ambient :
  SquareRoot.Replay.PreparedOwnerTransportReplay.Box}
    (state : SquareRoot.Replay.PreparedOwnerTransportReplay.State source ambient) (target :
      SquareRoot.Replay.PreparedOwnerTransportReplay.Gaussian) (reserve :
      SquareRoot.Replay.PreparedOwnerTransportReplay.Coordinate) where
  /-- The supplied source parameter is zero. -/ | sourceZero (zero : source = 0)
  /-- The supplied target parameter is zero. -/ | targetZero (zero : target = 0)
  /-- The source and target parameters coincide, so this state-only nonstationary replay is inapplicable. -/ |
    stationary (same : source = target)
  /-- Retain the failing original clearance field and the exact displacement reading. -/ | clearance (field :
    SquareRoot.Replay.PreparedOwnerTransportReplay.Field) (displacement :
    SquareRoot.Replay.PreparedOwnerTransportReplay.Coordinate)
      (displacement_eq : displacement = Data.Gaussian.Norm.Basic.normSq (source - target))
      (failed : ¬ displacement < field.bound state)
  /-- Retain the exact transported clearance and the failed strict reserve comparison. -/ | reserve (displacement :
    SquareRoot.Replay.PreparedOwnerTransportReplay.Coordinate)
      (displacement_eq : displacement = Data.Gaussian.Norm.Basic.normSq (source - target))
      (small : Data.Gaussian.Norm.Basic.normSq (source - target) < state.clearance.bound)
      (carried : SquareRoot.Replay.PreparedOwnerTransportReplay.Coordinate)
      (carried_eq : carried = (Riemann.RootContinuation.SquareRootContinuation.transportedOwner state
        small).clearance.bound)
      (failed : ¬ reserve < carried)

constructive_injectivity Failure

/-- Assemble only the accepted ambient-Rouché branch.  The four transported
side calculations are shared by the new state's boundary and ambient fields.
No initial isolation, Newton search, midpoint reset or shrinking runs here. -/
def carriedState {source target : SquareRoot.Replay.PreparedOwnerTransportReplay.Gaussian} {ambient :
  SquareRoot.Replay.PreparedOwnerTransportReplay.Box}
    (state : SquareRoot.Replay.PreparedOwnerTransportReplay.State source ambient) (sourceNonzero : source ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < state.clearance.bound)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) < state.ambientLeftClearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) < state.ambientRightClearance.bound)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) < state.ambientBottomClearance.bound)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) < state.ambientTopClearance.bound) :
      SquareRoot.Replay.PreparedOwnerTransportReplay.State target ambient :=
  let representative := ownerOfState sourceNonzero state
  let left := SquareRoot.Clearance.ExactQuadraticOwnerClearance.ambientLeftAfterMove representative leftSmall
  let right := SquareRoot.Clearance.ExactQuadraticOwnerClearance.ambientRightAfterMove representative rightSmall
  let bottom := SquareRoot.Clearance.ExactQuadraticOwnerClearance.ambientBottomAfterMove representative bottomSmall
  let top := SquareRoot.Clearance.ExactQuadraticOwnerClearance.ambientTopAfterMove representative topSmall
  { box := state.box
    refinesAmbient := state.refinesAmbient
    proper := state.proper
    clearance := Clearance.Box.Boundary.Lines.boundaryOfLines
      (left.restrict state.refinesAmbient) (right.restrict state.refinesAmbient)
      (bottom.restrict state.refinesAmbient) (top.restrict state.refinesAmbient)
    rawWindingFour := (Riemann.RootContinuation.SquareRootContinuation.transportedOwner state small).rawWindingFour
    ambientLeftClearance := left
    ambientRightClearance := right
    ambientBottomClearance := bottom
    ambientTopClearance := top }

/-- The owner assembled from the certified carried state equals the original reserved-transport fast branch. -/
theorem carriedState_owner_eq_reservedTransport {source target :
  SquareRoot.Replay.PreparedOwnerTransportReplay.Gaussian} {ambient :
  SquareRoot.Replay.PreparedOwnerTransportReplay.Box}
    (state : SquareRoot.Replay.PreparedOwnerTransportReplay.State source ambient) (sourceNonzero : source ≠ 0)
      (targetNonzero : target ≠ 0)
    (different : source ≠ target)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < state.clearance.bound)
    (leftSmall : Data.Gaussian.Norm.Basic.normSq (source - target) < state.ambientLeftClearance.bound)
    (rightSmall : Data.Gaussian.Norm.Basic.normSq (source - target) < state.ambientRightClearance.bound)
    (bottomSmall : Data.Gaussian.Norm.Basic.normSq (source - target) < state.ambientBottomClearance.bound)
    (topSmall : Data.Gaussian.Norm.Basic.normSq (source - target) < state.ambientTopClearance.bound)
    (reserve : SquareRoot.Replay.PreparedOwnerTransportReplay.Coordinate)
    (reserveSmall : reserve < (Riemann.RootContinuation.SquareRootContinuation.transportedOwner state
      small).clearance.bound) :
    ownerOfState targetNonzero
        (SquareRoot.Replay.PreparedOwnerTransportReplay.carriedState state sourceNonzero small leftSmall rightSmall
          bottomSmall topSmall) =
      reservedTransport (ownerOfState sourceNonzero state) targetNonzero small reserve := by
  unfold reservedTransport
  rw [dif_neg different]
  change Data.Gaussian.Norm.Basic.normSq (source - target) <
    (ownerOfState sourceNonzero state).track.initial.ambientLeftClearance.bound at leftSmall
  change Data.Gaussian.Norm.Basic.normSq (source - target) <
    (ownerOfState sourceNonzero state).track.initial.ambientRightClearance.bound at rightSmall
  change Data.Gaussian.Norm.Basic.normSq (source - target) <
    (ownerOfState sourceNonzero state).track.initial.ambientBottomClearance.bound at bottomSmall
  change Data.Gaussian.Norm.Basic.normSq (source - target) <
    (ownerOfState sourceNonzero state).track.initial.ambientTopClearance.bound at topSmall
  change reserve < (Riemann.RootContinuation.SquareRootContinuation.transportedOwner
    (ownerOfState sourceNonzero state).track.initial small).clearance.bound at reserveSmall
  rw [dif_pos leftSmall, dif_pos rightSmall, dif_pos bottomSmall, dif_pos topSmall,
    dif_pos reserveSmall]
  rfl

set_option genInjectivity false in
/-- The exact successful ambient transport with all retained checks and owner identity.

The certificate binds the displacement, five original bounds, transported reserve and output to the same original state
and target. -/
structure Checked {source : SquareRoot.Replay.PreparedOwnerTransportReplay.Gaussian} {ambient :
  SquareRoot.Replay.PreparedOwnerTransportReplay.Box}
    (state : SquareRoot.Replay.PreparedOwnerTransportReplay.State source ambient) (target :
      SquareRoot.Replay.PreparedOwnerTransportReplay.Gaussian) (reserve :
      SquareRoot.Replay.PreparedOwnerTransportReplay.Coordinate) where
  /-- The retained source parameter is nonzero. -/ sourceNonzero : source ≠ 0
  /-- The retained target parameter is nonzero. -/ targetNonzero : target ≠ 0
  /-- The source and target parameters are distinct. -/ different : source ≠ target
  /-- The actual squared source-to-target displacement used by the comparisons. -/ displacement :
    SquareRoot.Replay.PreparedOwnerTransportReplay.Coordinate
  /-- The retained displacement equals the squared Gaussian difference of the original parameters. -/ displacement_eq :
    displacement = Data.Gaussian.Norm.Basic.normSq (source - target)
  /-- The source-to-target displacement is smaller than the original boundary bound. -/ small :
    Data.Gaussian.Norm.Basic.normSq (source - target) < state.clearance.bound
  /-- The retained displacement is smaller than the original left ambient-line bound. -/ leftSmall : displacement <
    state.ambientLeftClearance.bound
  /-- The retained displacement is smaller than the original right ambient-line bound. -/ rightSmall : displacement <
    state.ambientRightClearance.bound
  /-- The retained displacement is smaller than the original bottom ambient-line bound. -/ bottomSmall : displacement <
    state.ambientBottomClearance.bound
  /-- The retained displacement is smaller than the original top ambient-line bound. -/ topSmall : displacement <
    state.ambientTopClearance.bound
  /-- The retained clearance of the original transported state. -/ carried :
    SquareRoot.Replay.PreparedOwnerTransportReplay.Coordinate
  /-- The retained transported clearance equals the original transport computation. -/ carried_eq : carried =
    (Riemann.RootContinuation.SquareRootContinuation.transportedOwner state small).clearance.bound
  /-- The requested reserve is strictly below the retained transported clearance. -/ reserveSmall : reserve < carried
  /-- The actual reconstructed owner at the original target parameter. -/ value :
    SquareRoot.Replay.PreparedOwnerTransportReplay.Owner target
  /-- The reconstructed owner equals the original reserved transport from the same restored state. -/ value_eq : value =
    reservedTransport (ownerOfState sourceNonzero state) targetNonzero small reserve

constructive_injectivity Checked

/-- Check the actual fast-branch comparisons before constructing its result.
Failure certifies just this reconstruction attempt.  In particular, a
stationary request needs the original owner's history, and a missed reserve
does not claim that the original total transport constructor fails. -/
def check {source : SquareRoot.Replay.PreparedOwnerTransportReplay.Gaussian} {ambient :
  SquareRoot.Replay.PreparedOwnerTransportReplay.Box}
    (state : SquareRoot.Replay.PreparedOwnerTransportReplay.State source ambient) (target :
      SquareRoot.Replay.PreparedOwnerTransportReplay.Gaussian) (reserve :
      SquareRoot.Replay.PreparedOwnerTransportReplay.Coordinate) :
    Except (SquareRoot.Replay.PreparedOwnerTransportReplay.Failure state target reserve)
      (SquareRoot.Replay.PreparedOwnerTransportReplay.Checked state target reserve) :=
  if sourceZero : source = 0 then .error (.sourceZero sourceZero)
  else
    if targetZero : target = 0 then .error (.targetZero targetZero)
    else
      if same : source = target then .error (.stationary same)
      else
        let displacement := Data.Gaussian.Norm.Basic.normSq (source - target)
        if small : displacement < state.clearance.bound then
          if leftSmall : displacement < state.ambientLeftClearance.bound then
            if rightSmall : displacement < state.ambientRightClearance.bound then
              if bottomSmall : displacement < state.ambientBottomClearance.bound then
                if topSmall : displacement < state.ambientTopClearance.bound then
                  let carried := (Riemann.RootContinuation.SquareRootContinuation.transportedOwner state
                    small).clearance.bound
                  if reserveSmall : reserve < carried then
                    let value := ownerOfState targetZero
                      (SquareRoot.Replay.PreparedOwnerTransportReplay.carriedState state sourceZero small leftSmall
                        rightSmall bottomSmall topSmall)
                    .ok
                      { sourceNonzero := sourceZero, targetNonzero := targetZero,
                        different := same, displacement := displacement, displacement_eq := rfl,
                        leftSmall := leftSmall, rightSmall := rightSmall,
                        bottomSmall := bottomSmall, topSmall := topSmall,
                        carried := carried, carried_eq := rfl, reserveSmall := reserveSmall,
                        small := small, value := value,
                        value_eq :=
                          SquareRoot.Replay.PreparedOwnerTransportReplay.carriedState_owner_eq_reservedTransport state
                          sourceZero targetZero
                          same small leftSmall rightSmall bottomSmall topSmall reserve reserveSmall }
                  else .error (.reserve displacement rfl small carried rfl reserveSmall)
                else .error (.clearance .top displacement rfl topSmall)
              else .error (.clearance .bottom displacement rfl bottomSmall)
            else .error (.clearance .right displacement rfl rightSmall)
          else .error (.clearance .left displacement rfl leftSmall)
        else .error (.clearance .boundary displacement rfl small)

/-- A successful check on the restored state supplies the original owner's small-displacement certificate. -/
theorem Checked.originalSmall {source target : SquareRoot.Replay.PreparedOwnerTransportReplay.Gaussian} (original :
  SquareRoot.Replay.PreparedOwnerTransportReplay.Owner source)
    (restored : SquareRoot.Replay.PreparedRootStateReplay.Checked source original.ambient
      (SquareRoot.Replay.PreparedRootStateReplay.capture original.track.initial))
    {reserve : SquareRoot.Replay.PreparedOwnerTransportReplay.Coordinate} (result :
      SquareRoot.Replay.PreparedOwnerTransportReplay.Checked restored.state target reserve) :
    Data.Gaussian.Norm.Basic.normSq (source - target) < original.track.initial.clearance.bound := by
  rw [← restored.eq_original original.track.initial]
  exact result.small

/-- The loader need not reconstruct the incoming refinement history or ask
for a separate small-move certificate: success already supplies that proof. -/
theorem Checked.eq_original {source target : SquareRoot.Replay.PreparedOwnerTransportReplay.Gaussian} (original :
  SquareRoot.Replay.PreparedOwnerTransportReplay.Owner source)
    (restored : SquareRoot.Replay.PreparedRootStateReplay.Checked source original.ambient
      (SquareRoot.Replay.PreparedRootStateReplay.capture original.track.initial))
    {reserve : SquareRoot.Replay.PreparedOwnerTransportReplay.Coordinate} (result :
      SquareRoot.Replay.PreparedOwnerTransportReplay.Checked restored.state target reserve) :
    result.value = reservedTransport original result.targetNonzero
      (result.originalSmall original restored) reserve := by
  rw [result.value_eq]
  exact SquareRoot.Replay.PreparedOwnerTransportReplay.reservedTransport_from_restored_state original result.different
    result.targetNonzero
    restored result.small (result.originalSmall original restored) reserve

end Purelib.RootIsolation.SquareRoot.Replay.PreparedOwnerTransportReplay
