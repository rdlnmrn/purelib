module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Circuit
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Comparison
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Full-cubic seams at arbitrary retained original quarter endpoint readings

The original seam joins both actual original Leg cubic channels. Original
quarter budgets compare arbitrary retained readings at the exact same
endpoint times. Actual direction equality also transports a supplied
terminal Owner without changing its track or source comparison schedule.
No dyadic depth, target count or particular paid-quarter representation
is needed by these original signed endpoint operations.
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
variable (finish : Reading left.actual finishTime finishInside) (source : Reading right.actual sourceTime sourceInside)
variable (atFinish : finishTime = 1) (atSource : sourceTime = 0)

include atFinish in
/-- The same old left-quarter Reading lies at its exact original Leg endpoint by its retained chart-time identity. -/
theorem finish_base_eq :
    (point site parameter 2 (Waist.direction leftQuarter finishTime) (of_decide_eq_true rfl)).base =
      (point site parameter 2 (Waist.direction leftQuarter 1) (of_decide_eq_true rfl)).base :=
  congrArg (fun time => (point site parameter 2 (Waist.direction leftQuarter time)
    (of_decide_eq_true rfl)).base) atFinish

include atSource in
/-- The original right Leg source and the same old right-quarter Reading have the exact source physical point. -/
theorem source_base_eq :
    (point site parameter 2 (Waist.direction rightQuarter 0) (of_decide_eq_true rfl)).base =
      (point site parameter 2 (Waist.direction rightQuarter sourceTime) (of_decide_eq_true rfl)).base :=
  (congrArg (fun time => (point site parameter 2 (Waist.direction rightQuarter time)
    (of_decide_eq_true rfl)).base) atSource).symm

/-- Read the exact stored original full-cubic seam without reconstructing either quarter or root comparison.

The witness keeps both original endpoint channel owners and its original
operational comparison schedule; only the named seam type is read back.
-/
def originalComparison (stored : Seam left right) :
    NamedEquivalent left.target.lift.value.name right.source.lift.value.name := by
  unfold Transport.Seam at stored
  exact stored

/-- Compare the actual old finish Reading to the same original Leg target using its original quarter budget. -/
def finishComparison : NamedEquivalent finish.lift.value.name left.target.lift.value.name :=
  Reading.agrees_of_base_eq finish left.target left.regular
    (finish_base_eq (site := site) (parameter := parameter) (leftQuarter := leftQuarter) atFinish)

/-- Compare the original Leg source to the actual old source Reading using its original quarter budget. -/
def sourceComparison : NamedEquivalent right.source.lift.value.name source.lift.value.name :=
  Reading.agrees_of_base_eq right.source source right.regular
    (source_base_eq (site := site) (parameter := parameter) (rightQuarter := rightQuarter) atSource)

/-- The original full-cubic seam and both original quarter budgets compare these SAME arbitrary old endpoint Readings.

The two local comparisons retain each input cofactor Owner and its actual
quarter budget. Their signed normalized factors and the original full-cubic
Leg seam are composed without acquiring another Reading, root Owner,
polynomial preparation, coefficient sample or replacement common channel.
-/
def agrees_at_times (stored : Seam left right) : NamedEquivalent finish.lift.value.name source.lift.value.name :=
  (finishComparison (left := left) finish atFinish).trans
    ((originalComparison stored).trans (sourceComparison (right := right) source atSource))

variable (directions : Waist.direction leftQuarter 1 = Waist.direction rightQuarter 0)

include atFinish atSource directions in
/-- Exact original oriented endpoint directions identify these actual old endpoint physical coordinates. -/
theorem point_eq :
    Spatial.coordinate site parameter 2 leftQuarter (of_decide_eq_true rfl) finishTime =
      Spatial.coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) sourceTime := by
  have finishBase := finish_base_eq (site := site) (parameter := parameter)
    (leftQuarter := leftQuarter) atFinish
  have directionBase := congrArg (fun direction =>
    (point site parameter 2 direction (of_decide_eq_true rfl)).base) directions
  have sourceBase := source_base_eq (site := site) (parameter := parameter)
    (rightQuarter := rightQuarter) atSource
  exact finishBase.trans (directionBase.trans sourceBase)

variable (owner : Owner ((Paths.polynomial parameter).eval
  (Spatial.coordinate site parameter 2 leftQuarter (of_decide_eq_true rfl) finishTime)))

/-- Reindex the SAME supplied actual terminal Owner across the original oriented geometric seam. -/
@[expose] def castOwner : Owner ((Paths.polynomial parameter).eval
    (Spatial.coordinate site parameter 2 rightQuarter (of_decide_eq_true rfl) sourceTime)) :=
  RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter
    (congrArg (fun value : Canonical => (Paths.polynomial parameter).eval value)
      (point_eq (site := site) (parameter := parameter)
        (leftQuarter := leftQuarter) (rightQuarter := rightQuarter) atFinish atSource directions)) owner

/-- The actual geometric seam transport retains the complete same original terminal Owner and every track cache. -/
theorem castOwner_heq : HEq (castOwner atFinish atSource directions owner) owner :=
  RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter_heq _ owner

/-- Exact original seam transport preserves the actual same terminal Owner's root name. -/
theorem castOwner_name :
    ownerRootName (castOwner atFinish atSource directions owner).parameterNonzero
      (castOwner atFinish atSource directions owner) = ownerRootName owner.parameterNonzero owner :=
  SquareRootTrackEquivalence.ownerRootName_castOwnerParameter _ owner

/-- An actual paid endpoint certificate and original full-cubic seam derive the next old Reading's source compatibility.

The incoming relation is the already constructed endpoint witness of the
literal supplied Owner and finish Reading. The original seam constructs
its old-Reading comparison internally. Equality transport retains the SAME
operational schedules while changing only the exact geometric Owner index.
No desired next compatibility or whole-circuit return witness is supplied.
-/
def following (stored : Seam left right)
    (preceding : NamedEquivalent (ownerRootName owner.parameterNonzero owner) finish.lift.value.name) :
    NamedEquivalent source.lift.value.name
      (ownerRootName (castOwner atFinish atSource directions owner).parameterNonzero
        (castOwner atFinish atSource directions owner)) :=
  NamedEquivalent.transport rfl (castOwner_name atFinish atSource directions owner).symm
    (preceding.trans (agrees_at_times (left := left) (right := right) finish source atFinish atSource stored)).symm

end Seam

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport

end
