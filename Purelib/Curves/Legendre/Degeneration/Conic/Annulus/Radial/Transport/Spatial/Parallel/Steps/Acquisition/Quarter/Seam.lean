module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit.Seam.Receipt

/-! # Actual full-cubic handoff between retained paid quarters

The existing Circuit.Seam is full-cubic operational data, including both
original cofactor Owners. It joins the original endpoint Leg Readings.
The previous paid quarter's stored endpoint and the next original source
Reading are compared to those identical Leg Readings internally. The same
actual paid finishOwner is reindexed only along the proved physical seam.
No independent attachment, replacement query or normalized-only sheet
closure is used.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Seam

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Meshes
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)

variable {site : Fin 2} {parameter : Canonical}
variable {leftQuarter rightQuarter : UnitCircuitQuarter}
variable {left : Transport.Leg site parameter leftQuarter} {right : Transport.Leg site parameter rightQuarter}
variable {current : Endpoint} {reading : ReadingAt left.actual current}
variable {originalOwner : OwnerAt site parameter leftQuarter (of_decide_eq_true rfl) current}
variable {original : Steps.Quarter left.actual left.regular current reading originalOwner}
variable {sourceOwner : OwnerAt site parameter leftQuarter (of_decide_eq_true rfl) current}
variable {agreement : InitialAgreement current reading sourceOwner}
variable (previous : Quarter original sourceOwner agreement)
variable (previousInitial : current = UniformPrimitiveMesh.firstEndpoint)
variable {nextCurrent : Endpoint} (nextReading : ReadingAt right.actual nextCurrent)
variable (nextInitial : nextCurrent = UniformPrimitiveMesh.firstEndpoint)
variable (directions : Waist.direction leftQuarter 1 = Waist.direction rightQuarter 0)
variable (stored : Transport.Seam left right)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

include previousInitial in
/-- The unchanged final Reading of the previous paid quarter has the original left Leg's physical endpoint. -/
theorem finish_base_eq :
    (point site parameter 2
      (Waist.direction leftQuarter (finalTarget current previous.originalQuarter.cache.val).parameter)
      (of_decide_eq_true rfl)).base =
    (point site parameter 2 (Waist.direction leftQuarter 1) (of_decide_eq_true rfl)).base := by
  have endpoint := previous.finalEndpoint_eq previousInitial
  have bases := congrArg (fun endpoint : Endpoint =>
    (point site parameter 2 (Waist.direction leftQuarter endpoint.parameter) (of_decide_eq_true rfl)).base)
    endpoint
  exact bases

include nextInitial in
/-- The identical next source Reading has the original right Leg's initial physical point. -/
theorem source_base_eq :
    (point site parameter 2 (Waist.direction rightQuarter 0) (of_decide_eq_true rfl)).base =
    (point site parameter 2 (Waist.direction rightQuarter nextCurrent.parameter) (of_decide_eq_true rfl)).base :=
  (congrArg (fun endpoint : Endpoint =>
    (point site parameter 2 (Waist.direction rightQuarter endpoint.parameter) (of_decide_eq_true rfl)).base)
    nextInitial).symm

include previousInitial nextInitial directions in
/-- The actual previous finish and actual next source have the same physical cubic-polynomial parameter. -/
theorem point_eq :
    coordinate site parameter 2 leftQuarter (of_decide_eq_true rfl)
      (finalTarget current previous.originalQuarter.cache.val).parameter =
    coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) nextCurrent.parameter :=
  (finish_base_eq (left := left) previous previousInitial).trans
    ((congrArg (fun direction => (point site parameter 2 direction (of_decide_eq_true rfl)).base)
      directions).trans (source_base_eq (rightQuarter := rightQuarter) nextInitial))

/-- Reindex the identical stored paid finishOwner along the exact geometric seam, without acquiring another Owner. -/
@[expose] def reindexOwner : OwnerAt site parameter rightQuarter (of_decide_eq_true rfl) nextCurrent :=
  Transport.Seam.castOwner (site := site) (parameter := parameter)
    (leftQuarter := leftQuarter) (rightQuarter := rightQuarter)
    (congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (congrArg Endpoint.parameter nextInitial) directions previous.finishOwner

/-- The exact geometric reindexing retains the whole actual previous Owner, including its track and clearance caches. -/
theorem reindexOwner_heq :
    HEq (reindexOwner (left := left) previous previousInitial nextInitial directions) previous.finishOwner :=
  Transport.Seam.castOwner_heq (site := site) (parameter := parameter)
    (leftQuarter := leftQuarter) (rightQuarter := rightQuarter)
    (congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (congrArg Endpoint.parameter nextInitial) directions previous.finishOwner

/-- Geometric endpoint reindexing preserves the original actual paid Owner's complete root name. -/
theorem reindexName_eq :
    ownerRootName (reindexOwner (left := left) previous previousInitial nextInitial directions).parameterNonzero
      (reindexOwner (left := left) previous previousInitial nextInitial directions) =
      ownerRootName previous.finishOwner.parameterNonzero previous.finishOwner :=
  Transport.Seam.castOwner_name (site := site) (parameter := parameter)
    (leftQuarter := leftQuarter) (rightQuarter := rightQuarter)
    (congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (congrArg Endpoint.parameter nextInitial) directions previous.finishOwner

/-- Compare the two retained left-quarter Readings using the shared original endpoint operation. -/
def finishComparison : NamedEquivalent previous.finishReading.lift.value.name left.target.lift.value.name :=
  Transport.Seam.finishComparison (left := left) previous.finishReading
    (congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))

/-- Compare the two retained right-quarter Readings using the shared original source operation. -/
def sourceComparison : NamedEquivalent right.source.lift.value.name nextReading.lift.value.name :=
  Transport.Seam.sourceComparison (right := right) nextReading (congrArg Endpoint.parameter nextInitial)

/-- One full-cubic quarter seam retains each actual comparison and the identical reindexed paid Owner.

The existing full-cubic original seam is an input, not a newly requested
final relation. Both local endpoint comparisons and the previous paid
endpoint witness are constructed once and stored with their factory
identities. The next source agreement uses exactly those stored values.
-/
@[expose] def Receipt :=
  Transport.Seam.Receipt (left := left) (right := right) previous.finishReading nextReading
    previous.finishOwner previous.finishEquivalent
    (congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (congrArg Endpoint.parameter nextInitial) directions stored

namespace Receipt

/-- Construct the paid handoff once from the original full-cubic seam and the actual retained endpoint inputs. -/
def build : Receipt (left := left) (right := right)
    previous previousInitial nextReading nextInitial directions stored :=
  Transport.Seam.Receipt.build (left := left) (right := right) previous.finishReading nextReading
    previous.finishOwner previous.finishEquivalent
    (congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (congrArg Endpoint.parameter nextInitial) directions stored

/-- The old Quarter entry is the exact shared six-cache factory on its SAME retained endpoint inputs. -/
theorem build_eq : build (left := left) (right := right)
    previous previousInitial nextReading nextInitial directions stored =
    Transport.Seam.Receipt.build (left := left) (right := right) previous.finishReading nextReading
      previous.finishOwner previous.finishEquivalent
      (congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
      (congrArg Endpoint.parameter nextInitial) directions stored := by
  unfold build
  rfl

variable (receipt : Receipt (left := left) (right := right)
  previous previousInitial nextReading nextInitial directions stored)

/-- Read the identical physical reindexing of the actual previous paid finishOwner. -/
@[expose] def owner : OwnerAt site parameter rightQuarter (of_decide_eq_true rfl) nextCurrent := receipt.1.val

/-- Read the same retained full-cubic paid endpoint comparison without replaying its factory. -/
@[expose] def preceding : NamedEquivalent
    (ownerRootName previous.finishOwner.parameterNonzero previous.finishOwner)
    previous.finishReading.lift.value.name := receipt.2.1.val

/-- Read the same retained original-budget comparison at the previous quarter's final physical point. -/
@[expose] def finish : NamedEquivalent previous.finishReading.lift.value.name left.target.lift.value.name :=
  receipt.2.2.1.val

/-- Read the same retained original-budget comparison at the next quarter's initial physical point. -/
@[expose] def source : NamedEquivalent right.source.lift.value.name nextReading.lift.value.name :=
  receipt.2.2.2.1.val

/-- Read the actual composed full-cubic endpoint witness using the identical stored original seam. -/
@[expose] def joined : NamedEquivalent
    (ownerRootName previous.finishOwner.parameterNonzero previous.finishOwner) nextReading.lift.value.name :=
  receipt.2.2.2.2.1.val

/-- Read the retained next-source agreement on the exact stored physical Owner and unchanged next Reading. -/
@[expose] def nextAgreement : InitialAgreement nextCurrent nextReading receipt.owner :=
  receipt.2.2.2.2.2.val

/-- The retained handoff Owner is precisely the original geometric endpoint-index transport. -/
theorem owner_eq : receipt.owner = reindexOwner (left := left) previous previousInitial nextInitial directions := by
  have retained := Transport.Seam.Receipt.owner_eq
    (left := left) (right := right) (finishReading := previous.finishReading) (sourceReading := nextReading)
    (finishOwner := previous.finishOwner) (previousAgreement := previous.finishEquivalent)
    (atFinish := congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (atSource := congrArg Endpoint.parameter nextInitial) (directions := directions) (stored := stored) receipt
  exact retained

/-- The retained physical handoff Owner has the exact original paid Owner's root name. -/
theorem name_eq :
    ownerRootName receipt.owner.parameterNonzero receipt.owner =
      ownerRootName previous.finishOwner.parameterNonzero previous.finishOwner :=
  Transport.Seam.Receipt.name_eq (left := left) (right := right)
    (finishReading := previous.finishReading) (sourceReading := nextReading)
    (finishOwner := previous.finishOwner) (previousAgreement := previous.finishEquivalent)
    (atFinish := congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (atSource := congrArg Endpoint.parameter nextInitial) (directions := directions) (stored := stored) receipt

/-- The handoff preserves the exact complete previous paid Owner, track and clearance caches. -/
theorem owner_heq : HEq receipt.owner previous.finishOwner :=
  Transport.Seam.Receipt.owner_heq (left := left) (right := right)
    (finishReading := previous.finishReading) (sourceReading := nextReading)
    (finishOwner := previous.finishOwner) (previousAgreement := previous.finishEquivalent)
    (atFinish := congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (atSource := congrArg Endpoint.parameter nextInitial) (directions := directions) (stored := stored) receipt

/-- The retained previous endpoint witness is the same operation on the completed previous paid quarter. -/
theorem preceding_eq : receipt.preceding = previous.finishEquivalent :=
  Transport.Seam.Receipt.preceding_eq (left := left) (right := right)
    (finishReading := previous.finishReading) (sourceReading := nextReading)
    (finishOwner := previous.finishOwner) (previousAgreement := previous.finishEquivalent)
    (atFinish := congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (atSource := congrArg Endpoint.parameter nextInitial) (directions := directions) (stored := stored) receipt

/-- The retained local finish witness uses the shared original same-quarter comparison factory. -/
theorem finish_eq : receipt.finish = finishComparison (left := left) previous previousInitial :=
  Transport.Seam.Receipt.finish_eq (left := left) (right := right)
    (finishReading := previous.finishReading) (sourceReading := nextReading)
    (finishOwner := previous.finishOwner) (previousAgreement := previous.finishEquivalent)
    (atFinish := congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (atSource := congrArg Endpoint.parameter nextInitial) (directions := directions) (stored := stored) receipt

/-- The retained local source witness uses the shared original same-quarter comparison factory. -/
theorem source_eq : receipt.source = sourceComparison (right := right) nextReading nextInitial :=
  Transport.Seam.Receipt.source_eq (left := left) (right := right)
    (finishReading := previous.finishReading) (sourceReading := nextReading)
    (finishOwner := previous.finishOwner) (previousAgreement := previous.finishEquivalent)
    (atFinish := congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (atSource := congrArg Endpoint.parameter nextInitial) (directions := directions) (stored := stored) receipt

/-- The joined relation is exactly the ordered composition of the same retained original witnesses. -/
theorem joined_eq : receipt.joined = receipt.preceding.trans
    (receipt.finish.trans ((Transport.Seam.originalComparison stored).trans receipt.source)) :=
  Transport.Seam.Receipt.joined_eq (left := left) (right := right)
    (finishReading := previous.finishReading) (sourceReading := nextReading)
    (finishOwner := previous.finishOwner) (previousAgreement := previous.finishEquivalent)
    (atFinish := congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (atSource := congrArg Endpoint.parameter nextInitial) (directions := directions) (stored := stored) receipt

/-- The next source witness retains the same reversal, operational composition and geometric index transport. -/
theorem nextAgreement_eq : receipt.nextAgreement = NamedEquivalent.transport rfl receipt.name_eq.symm
    receipt.joined.symm :=
  Transport.Seam.Receipt.nextAgreement_eq (left := left) (right := right)
    (finishReading := previous.finishReading) (sourceReading := nextReading)
    (finishOwner := previous.finishOwner) (previousAgreement := previous.finishEquivalent)
    (atFinish := congrArg Endpoint.parameter (previous.finalEndpoint_eq previousInitial))
    (atSource := congrArg Endpoint.parameter nextInitial) (directions := directions) (stored := stored) receipt

end Receipt

end Steps.Acquisition.Quarter.Seam

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
