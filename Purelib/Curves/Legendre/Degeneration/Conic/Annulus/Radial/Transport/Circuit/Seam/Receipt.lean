module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit.Seam.Reading
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Retained full-cubic seams on actual original quarter endpoint caches

The handoff takes the actual old endpoint Readings and actual terminal
Owner of a paid producer. Its already proved local endpoint comparison
is retained alongside the two original-budget comparisons and the exact
signed Leg seam. No target-list representation or dyadic count occurs.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport

namespace Seam

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {site : Fin 2} {parameter : Canonical} {leftQuarter rightQuarter : UnitCircuitQuarter}
variable {left : Leg site parameter leftQuarter} {right : Leg site parameter rightQuarter}
variable {finishTime sourceTime : Fraction.Rational}
variable {finishInside : FixedRootBoxPath.Inside finishTime} {sourceInside : FixedRootBoxPath.Inside sourceTime}
variable (finishReading : Reading left.actual finishTime finishInside)
variable (sourceReading : Reading right.actual sourceTime sourceInside)
variable (finishOwner : Owner ((Paths.polynomial parameter).eval
  (Spatial.coordinate site parameter 2 leftQuarter (of_decide_eq_true rfl) finishTime)))
variable (previousAgreement : NamedEquivalent (ownerRootName finishOwner.parameterNonzero finishOwner)
  finishReading.lift.value.name)
variable (atFinish : finishTime = 1) (atSource : sourceTime = 0)
variable (directions : Waist.direction leftQuarter 1 = Waist.direction rightQuarter 0)
variable (stored : Seam left right)

attribute [local irreducible] Spatial.coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The retained local endpoint witness is exactly the already completed producer's supplied witness. -/
@[irreducible, expose] def PreviousCache
    (retained : NamedEquivalent (ownerRootName finishOwner.parameterNonzero finishOwner)
      finishReading.lift.value.name) : Prop := retained = previousAgreement

/-- The retained local finish witness is the original same-quarter budget comparison on the identical old Readings. -/
@[irreducible, expose] def FinishCache
    (retained : NamedEquivalent finishReading.lift.value.name left.target.lift.value.name) : Prop :=
  retained = finishComparison (left := left) finishReading atFinish

/-- The retained local source witness is the original same-quarter budget comparison on the identical old Readings. -/
@[irreducible, expose] def SourceCache
    (retained : NamedEquivalent right.source.lift.value.name sourceReading.lift.value.name) : Prop :=
  retained = sourceComparison (right := right) sourceReading atSource

/-- The retained next Owner is the exact geometric reindexing of the supplied actual terminal Owner. -/
@[irreducible, expose] def OwnerCache
    (retained : Owner ((Paths.polynomial parameter).eval
      (Spatial.coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) sourceTime))) : Prop :=
  retained = castOwner (site := site) (parameter := parameter)
    (leftQuarter := leftQuarter) (rightQuarter := rightQuarter) atFinish atSource directions finishOwner

/-- Read the exact geometric-owner factory equality without exposing any original Owner construction. -/
theorem OwnerCache.readback
    {retained : Owner ((Paths.polynomial parameter).eval
      (Spatial.coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) sourceTime))}
    (cache : OwnerCache finishOwner atFinish atSource directions retained) :
    retained = castOwner (site := site) (parameter := parameter)
      (leftQuarter := leftQuarter) (rightQuarter := rightQuarter) atFinish atSource directions finishOwner := by
  unfold OwnerCache at cache
  exact cache

/-- A full-cubic handoff retains the same six actual caches on arbitrary paid endpoint inputs.

The supplied preceding relation is the producer's local endpoint theorem.
The next source relation is derived by the original full-cubic signed seam,
both original quarter-budget comparisons and the exact same Owner cast.
No new Reading, Source attachment or desired next agreement is supplied.
-/
@[expose] def Receipt :=
  Σ owner : { retained : Owner ((Paths.polynomial parameter).eval
        (Spatial.coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) sourceTime)) //
      OwnerCache finishOwner atFinish atSource directions retained },
    Σ previous : { retained : NamedEquivalent
          (ownerRootName finishOwner.parameterNonzero finishOwner) finishReading.lift.value.name //
        PreviousCache finishReading finishOwner previousAgreement retained },
      Σ finish : { retained : NamedEquivalent finishReading.lift.value.name left.target.lift.value.name //
          FinishCache (left := left) finishReading atFinish retained },
        Σ source : { retained : NamedEquivalent right.source.lift.value.name sourceReading.lift.value.name //
            SourceCache (right := right) sourceReading atSource retained },
          Σ joined : { retained : NamedEquivalent
                (ownerRootName finishOwner.parameterNonzero finishOwner) sourceReading.lift.value.name //
              retained = previous.val.trans
                (finish.val.trans ((originalComparison stored).trans source.val)) },
            { following : NamedEquivalent sourceReading.lift.value.name
                (ownerRootName owner.val.parameterNonzero owner.val) //
              following = NamedEquivalent.transport rfl
                ((congrArg (fun value : Owner ((Paths.polynomial parameter).eval
                    (Spatial.coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) sourceTime)) =>
                  ownerRootName value.parameterNonzero value)
                    (OwnerCache.readback finishOwner atFinish atSource directions owner.property)).trans
                  (castOwner_name (site := site) (parameter := parameter)
                    (leftQuarter := leftQuarter) (rightQuarter := rightQuarter)
                    atFinish atSource directions finishOwner)).symm joined.val.symm }

namespace Receipt

/-- Construct each handoff cache once, preserving the original six-cache factory order. -/
def build : Receipt (left := left) (right := right)
    finishReading sourceReading finishOwner previousAgreement atFinish atSource directions stored :=
  let owner : { retained : Owner ((Paths.polynomial parameter).eval
        (Spatial.coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) sourceTime)) //
      OwnerCache finishOwner atFinish atSource directions retained } :=
    ⟨castOwner (site := site) (parameter := parameter)
      (leftQuarter := leftQuarter) (rightQuarter := rightQuarter) atFinish atSource directions finishOwner,
      by unfold OwnerCache; rfl⟩
  let previous := previousAgreement
  let finish := finishComparison (left := left) finishReading atFinish
  let source := sourceComparison (right := right) sourceReading atSource
  let joined := previous.trans (finish.trans ((originalComparison stored).trans source))
  let following := NamedEquivalent.transport rfl
    ((congrArg (fun value : Owner ((Paths.polynomial parameter).eval
        (Spatial.coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) sourceTime)) =>
      ownerRootName value.parameterNonzero value)
        (OwnerCache.readback finishOwner atFinish atSource directions owner.property)).trans
      (castOwner_name (site := site) (parameter := parameter)
        (leftQuarter := leftQuarter) (rightQuarter := rightQuarter)
        atFinish atSource directions finishOwner)).symm joined.symm
  ⟨owner, ⟨previous, by unfold PreviousCache; rfl⟩,
    ⟨finish, by unfold FinishCache; rfl⟩, ⟨source, by unfold SourceCache; rfl⟩,
    ⟨joined, rfl⟩, ⟨following, rfl⟩⟩

variable (receipt : Receipt (left := left) (right := right)
  finishReading sourceReading finishOwner previousAgreement atFinish atSource directions stored)

/-- Read the identical actual terminal Owner with only its proved next-quarter parameter index changed. -/
@[expose] def owner : Owner ((Paths.polynomial parameter).eval
    (Spatial.coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) sourceTime)) := receipt.1.val

/-- Read the exact old producer's retained local endpoint witness without rebuilding it. -/
@[expose] def preceding : NamedEquivalent
    (ownerRootName finishOwner.parameterNonzero finishOwner) finishReading.lift.value.name := receipt.2.1.val

/-- Read the same retained original-budget comparison at the preceding old finish Reading. -/
@[expose] def finish : NamedEquivalent finishReading.lift.value.name left.target.lift.value.name :=
  receipt.2.2.1.val

/-- Read the same retained original-budget comparison at the following old source Reading. -/
@[expose] def source : NamedEquivalent right.source.lift.value.name sourceReading.lift.value.name :=
  receipt.2.2.2.1.val

/-- Read the actual ordered composition on the supplied original full-cubic endpoint inputs. -/
@[expose] def joined : NamedEquivalent
    (ownerRootName finishOwner.parameterNonzero finishOwner) sourceReading.lift.value.name :=
  receipt.2.2.2.2.1.val

/-- Read the derived next-source witness on the literal stored Owner and unchanged original source Reading. -/
@[expose] def nextAgreement : NamedEquivalent sourceReading.lift.value.name
    (ownerRootName receipt.owner.parameterNonzero receipt.owner) := receipt.2.2.2.2.2.val

/-- The stored handoff Owner is exactly the original geometric cast of the supplied terminal Owner. -/
theorem owner_eq : receipt.owner = castOwner (site := site) (parameter := parameter)
    (leftQuarter := leftQuarter) (rightQuarter := rightQuarter) atFinish atSource directions finishOwner :=
  OwnerCache.readback finishOwner atFinish atSource directions receipt.1.property

/-- The handoff preserves the whole actual terminal Owner, including its track and original clearance caches. -/
theorem owner_heq : HEq receipt.owner finishOwner :=
  (heq_of_eq receipt.owner_eq).trans
    (castOwner_heq (site := site) (parameter := parameter)
      (leftQuarter := leftQuarter) (rightQuarter := rightQuarter) atFinish atSource directions finishOwner)

/-- The stored next Owner retains the exact actual terminal Owner's complete root name. -/
theorem name_eq : ownerRootName receipt.owner.parameterNonzero receipt.owner =
    ownerRootName finishOwner.parameterNonzero finishOwner :=
  (congrArg (fun value : Owner ((Paths.polynomial parameter).eval
      (Spatial.coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) sourceTime)) =>
    ownerRootName value.parameterNonzero value) receipt.owner_eq).trans
    (castOwner_name (site := site) (parameter := parameter)
      (leftQuarter := leftQuarter) (rightQuarter := rightQuarter) atFinish atSource directions finishOwner)

/-- The retained preceding witness is exactly the supplied already constructed local endpoint certificate. -/
theorem preceding_eq : receipt.preceding = previousAgreement := by
  have retained := receipt.2.1.property
  unfold PreviousCache at retained
  exact retained

/-- The retained finish witness is the original local budget factory on the identical old endpoint Reading. -/
theorem finish_eq : receipt.finish = finishComparison (left := left) finishReading atFinish := by
  have retained := receipt.2.2.1.property
  unfold FinishCache at retained
  exact retained

/-- The retained source witness is the original local budget factory on the identical old initial Reading. -/
theorem source_eq : receipt.source = sourceComparison (right := right) sourceReading atSource := by
  have retained := receipt.2.2.2.1.property
  unfold SourceCache at retained
  exact retained

/-- The joined witness is exactly the ordered composition of the same retained comparisons and original signed seam. -/
theorem joined_eq : receipt.joined = receipt.preceding.trans
    (receipt.finish.trans ((originalComparison stored).trans receipt.source)) := receipt.2.2.2.2.1.property

/-- The next witness preserves the same actual comparison schedule under reversal and exact Owner-name transport. -/
theorem nextAgreement_eq : receipt.nextAgreement =
    NamedEquivalent.transport rfl receipt.name_eq.symm receipt.joined.symm := receipt.2.2.2.2.2.property

end Receipt

end Seam

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport

end
