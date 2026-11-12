module
public import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance

public import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
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

section

open Purelib.Data.Gaussian

/-- Exact source and target parameter transports commute with the SAME original Owner.advance operation.

Both nonzero and clearance proofs are retained at their actual indices.
The equality compares the entire original Owner records; it does not
identify independently constructed roots from coordinates or boxes.
-/
theorem castOwnerParameter_advance {source target nextSource nextTarget : Gaussian}
    (sourceEq : source = nextSource) (targetEq : target = nextTarget) (owner : Owner source)
    (nonzero : target ≠ 0)
    (small : Norm.Basic.normSq (source - target) <
      owner.track.initial.clearance.bound)
    (nextNonzero : nextTarget ≠ 0)
    (nextSmall : Norm.Basic.normSq (nextSource - nextTarget) <
      (castOwnerParameter sourceEq owner).track.initial.clearance.bound) :
    castOwnerParameter targetEq (owner.advance nonzero small) =
      (castOwnerParameter sourceEq owner).advance nextNonzero nextSmall := by
  cases sourceEq
  cases targetEq
  rfl

end

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
