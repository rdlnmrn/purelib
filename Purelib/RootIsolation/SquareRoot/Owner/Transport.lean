module
public import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance

public import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

public section

namespace Purelib.RootIsolation.SquareRoot.Owner.Transport

open Purelib.Riemann.Topology.SquareRootContinuationChain (Gaussian Owner)

/-- Reindex an owner along an equality of its base parameter.

Retains the complete original owner, track and dependent certificates while changing only the displayed parameter index.
-/
@[expose] def castOwnerParameter {source target : Gaussian} (equal : source = target)
    (owner : Owner source) : Owner target :=
  equal ▸ owner

/-- Parameter reindexing does not change the owner data. -/
theorem castOwnerParameter_heq {source target : Gaussian}
    (equal : source = target) (owner : Owner source) :
    HEq (castOwnerParameter equal owner) owner := by
  cases equal
  rfl

/-- Reindexing the base parameter preserves the owner's original initial box. -/
@[simp] theorem castOwnerParameter_initial_box {source target : Gaussian}
    (equal : source = target) (owner : Owner source) :
    (castOwnerParameter equal owner).track.initial.box =
      owner.track.initial.box := by
  cases equal
  rfl

/-- Reindexing the base parameter preserves the owner's retained initial clearance bound. -/
@[simp] theorem castOwnerParameter_clearance_bound {source target : Gaussian}
    (equal : source = target) (owner : Owner source) :
    (castOwnerParameter equal owner).track.initial.clearance.bound =
      owner.track.initial.clearance.bound := by
  cases equal
  rfl

/-- Reindexing the base parameter preserves the owner's original ambient box. -/
@[simp] theorem castOwnerParameter_ambient {source target : Gaussian}
    (equal : source = target) (owner : Owner source) :
    (castOwnerParameter equal owner).ambient = owner.ambient := by
  cases equal
  rfl

open Purelib.RootIsolation.SquareRoot.Clearance

/-- Parameter reindexing preserves the retained ambient-left clearance bound.

The equality changes only the owner index; its original initial track and clearance certificate remain the same data. -/
@[simp] theorem castOwnerParameter_ambientLeftClearance_bound
    {source target : Gaussian} (equal : source = target)
    (owner : Owner source) :
    (castOwnerParameter equal owner).track.initial.ambientLeftClearance.bound =
      owner.track.initial.ambientLeftClearance.bound := by
  cases equal
  rfl

/-- Parameter reindexing preserves ambient-clearance dominance.

Transports the original certificate for the same retained owner and its four ambient-line clearance bounds. -/
theorem castOwnerParameter_dominance
    {source target : Gaussian} (equal : source = target)
    (owner : Owner source)
    (dominance : ExactQuadraticOwnerClearance.AmbientClearanceDominance owner) :
    ExactQuadraticOwnerClearance.AmbientClearanceDominance
      (castOwnerParameter equal owner) := by
  cases equal
  exact dominance

/-- Parameter reindexing preserves the quadratic ambient budget.

Transports the original budget certificate along the parameter equality without changing the retained owner, track or
ambient bounds. -/
theorem castOwnerParameter_budget
    {source target : Gaussian} (equal : source = target)
    (owner : Owner source)
    (budget : ExactQuadraticOwnerClearance.QuadraticAmbientBudget owner) :
    ExactQuadraticOwnerClearance.QuadraticAmbientBudget
      (castOwnerParameter equal owner) := by
  cases equal
  exact budget

end Purelib.RootIsolation.SquareRoot.Owner.Transport
