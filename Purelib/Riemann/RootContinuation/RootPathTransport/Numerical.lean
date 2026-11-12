module

public import Purelib.Riemann.RootContinuation.RootPathTransport
public import Purelib.Riemann.Paths.PreparedPathParentCaches
public import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.RootOwnerFrames

/-! # Distinct numerical preparations retaining an original framed transport row

The original row remains a complete input cache. A new covered preparation
on its exact path and starting Owner supplies proper numerical parents and
one retained request bank. Its independently acquired finish Owner is not
identified with the original row's finish by this producer.
-/

public section

namespace Purelib.Riemann.RootContinuation.RootPathTransport.TransportRow

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)

variable {genus : Nat} {curve : HyperellipticCurve genus} {ambient : Box} {start finish : Canonical}
variable {path : ClearPath curve.polynomial ambient start finish}
variable {first : OwnerFrame (curve.polynomial.eval start)} {last : OwnerFrame (curve.polynomial.eval finish)}
variable {index : Fin 2}

/-- Retain the old whole row and four complete results of a distinct covered numerical execution.

The original ParentCache fixes the numerical count to genus. Each exact
factory equality belongs to the same cached preparation, parent list,
endpoint frame selection and request bank. No final root relation is a
premise, and the incoming original row is not run again.
-/
@[expose] def Numerical (original : TransportRow path first last index) (within : path.WithinAmbient)
    (differential : Differential genus) (parentSheet : Fin 2) (target : Rational) (positive : 0 < target)
    (minimum : Nat) :=
  {value : TransportRow path first last index // value = original} ×
  Σ covered : {value : CoveredTracedPath path (first.owners index) //
    value = CoveredTracedPath.build path within (first.owners index)},
  Σ parents : {value : ParentCache covered.val differential parentSheet //
    value = ParentCache.build covered.val differential parentSheet},
  {value : OwnerSelection last.owners covered.val.traced.finishOwner //
    value = last.select covered.val.traced.finishOwner} ×
  {value : ControlledSumRequest parents.val.parents genus target //
    value = ControlledSumRequest.acquire parents.val.covered parents.val.proper target positive minimum}

namespace Numerical

variable {original : TransportRow path first last index} {within : path.WithinAmbient}
variable {differential : Differential genus} {parentSheet : Fin 2} {target : Rational}
variable {positive : 0 < target} {minimum : Nat}

/-- Acquire only the numerical requests after retaining the exact new preparation, parents and finish selection.

The supplied whole factory equations retain actual completed work. This
constructor allows a common split mesh to determine minimum before the
new primitive requests are acquired, without repeating root preparation.
-/
def ofPrepared (original : TransportRow path first last index) (within : path.WithinAmbient)
    (differential : Differential genus) (parentSheet : Fin 2)
    (covered : CoveredTracedPath path (first.owners index))
    (covered_eq : covered = CoveredTracedPath.build path within (first.owners index))
    (parents : ParentCache covered differential parentSheet)
    (parents_eq : parents = ParentCache.build covered differential parentSheet)
    (selected : OwnerSelection last.owners covered.traced.finishOwner)
    (selected_eq : selected = last.select covered.traced.finishOwner)
    (target : Rational) (positive : 0 < target) (minimum : Nat) :
    Numerical original within differential parentSheet target positive minimum :=
  let requested := ControlledSumRequest.acquire parents.covered parents.proper target positive minimum
  ⟨⟨original, rfl⟩, ⟨covered, covered_eq⟩, ⟨parents, parents_eq⟩, ⟨selected, selected_eq⟩, ⟨requested, rfl⟩⟩

/-- Acquire a new covered path, parent cache, finish selection and numerical request bank in that order. -/
def build (original : TransportRow path first last index) (within : path.WithinAmbient)
    (differential : Differential genus) (parentSheet : Fin 2) (target : Rational) (positive : 0 < target)
    (minimum : Nat) : Numerical original within differential parentSheet target positive minimum :=
  let covered := CoveredTracedPath.build path within (first.owners index)
  let parents := ParentCache.build covered differential parentSheet
  let selected := last.select covered.traced.finishOwner
  ofPrepared original within differential parentSheet covered rfl parents rfl selected rfl
    target positive minimum

variable (numerics : Numerical original within differential parentSheet target positive minimum)

/-- Read the complete original input row without another transport or selection. -/
def previous : TransportRow path first last index := numerics.1.val

/-- Read the entire independently acquired covered preparation on this same path and starting Owner. -/
def covered : CoveredTracedPath path (first.owners index) := numerics.2.1.val

/-- Read the complete new centered-parent cache and its exact primitive coverage. -/
def parents : ParentCache numerics.covered differential parentSheet := numerics.2.2.1.val

/-- Read the retained selection of the new actual finish Owner in the unchanged target frame. -/
def selected : OwnerSelection last.owners numerics.covered.traced.finishOwner := numerics.2.2.2.1.val

/-- Read the one controlled numerical request bank on the new cached parents. -/
def requested : ControlledSumRequest numerics.parents.parents genus target := numerics.2.2.2.2.val

/-- The complete old row is exactly the original supplied cache. -/
theorem previous_eq : numerics.previous = original := numerics.1.property

/-- The complete new covered preparation is its original automatic factory on the same route and source Owner. -/
theorem covered_eq : numerics.covered = CoveredTracedPath.build path within (first.owners index) :=
  numerics.2.1.property

/-- The complete new parent cache is the original factory on the retained numerical preparation. -/
theorem parents_eq : numerics.parents = ParentCache.build numerics.covered differential parentSheet :=
  numerics.2.2.1.property

/-- The entire new finish selection is its original frame-selection factory result. -/
theorem selected_eq : numerics.selected = last.select numerics.covered.traced.finishOwner :=
  numerics.2.2.2.1.property

/-- The whole retained controlled bank is its original acquisition on those same covered proper parents. -/
theorem requested_eq : numerics.requested = ControlledSumRequest.acquire numerics.parents.covered
    numerics.parents.proper target positive minimum := numerics.2.2.2.2.property

/-- The same retained controlled request pays the requested minimum numerical stage exactly. -/
theorem minimumIndex_eq : numerics.requested.minimumIndex = minimum :=
  (congrArg (fun value : ControlledSumRequest numerics.parents.parents genus target => value.minimumIndex)
    numerics.requested_eq).trans
    (ControlledSumRequest.acquire_minimumIndex numerics.parents.covered numerics.parents.proper
      target positive minimum)

/-- Whole parent-factory identities identify the cached numerical list with the supplied actual parent cache. -/
private theorem parents_list_eq
    (supplied : CoveredTracedPath path (first.owners index))
    (supplied_eq : supplied = CoveredTracedPath.build path within (first.owners index))
    (parents : ParentCache supplied differential parentSheet)
    (parents_eq : parents = ParentCache.build supplied differential parentSheet) :
    numerics.parents.parents = parents.parents := by
  have cached := congrArg (fun value : ParentCache numerics.covered differential parentSheet => value.parents)
    (Numerical.parents_eq numerics)
  have prepared := congrArg (fun value : CoveredTracedPath path (first.owners index) =>
    (ParentCache.build value differential parentSheet).parents) ((Numerical.covered_eq numerics).trans supplied_eq.symm)
  have retained := congrArg (fun value : ParentCache supplied differential parentSheet => value.parents) parents_eq
  exact cached.trans (prepared.trans retained.symm)

/-- Read the same whole controlled request on the supplied original parent-cache index.

Only its parent-list type is transported through complete factory identities.
No request, parent, preparation or previous row is constructed again.
-/
def requestedOn (supplied : CoveredTracedPath path (first.owners index))
    (supplied_eq : supplied = CoveredTracedPath.build path within (first.owners index))
    (parents : ParentCache supplied differential parentSheet)
    (parents_eq : parents = ParentCache.build supplied differential parentSheet) :
    ControlledSumRequest parents.parents genus target :=
  Eq.mp (congrArg (fun entries => ControlledSumRequest entries genus target)
    (numerics.parents_list_eq supplied supplied_eq parents parents_eq)) numerics.requested

/-- Reindexing retains the entire original controlled request value, including every cached field. -/
theorem requestedOn_heq (supplied : CoveredTracedPath path (first.owners index))
    (supplied_eq : supplied = CoveredTracedPath.build path within (first.owners index))
    (parents : ParentCache supplied differential parentSheet)
    (parents_eq : parents = ParentCache.build supplied differential parentSheet) :
    HEq (numerics.requestedOn supplied supplied_eq parents parents_eq) numerics.requested := by
  have retained : ∀ {firstParents lastParents : List (CenteredEdge curve differential)}
      (same : firstParents = lastParents) (value : ControlledSumRequest firstParents genus target),
      HEq (Eq.mp (congrArg (fun entries => ControlledSumRequest entries genus target) same) value) value := by
    intro firstParents lastParents same value
    cases same
    rfl
  exact retained (numerics.parents_list_eq supplied supplied_eq parents parents_eq) numerics.requested

/-- The same reindexed request retains the numerical execution's exact requested minimum stage. -/
theorem requestedOn_minimumIndex (supplied : CoveredTracedPath path (first.owners index))
    (supplied_eq : supplied = CoveredTracedPath.build path within (first.owners index))
    (parents : ParentCache supplied differential parentSheet)
    (parents_eq : parents = ParentCache.build supplied differential parentSheet) :
    (numerics.requestedOn supplied supplied_eq parents parents_eq).minimumIndex = minimum := by
  have readback : ∀ {firstParents lastParents : List (CenteredEdge curve differential)}
      (same : firstParents = lastParents) (value : ControlledSumRequest firstParents genus target),
      (Eq.mp (congrArg (fun entries => ControlledSumRequest entries genus target) same) value).minimumIndex =
        value.minimumIndex := by
    intro firstParents lastParents same value
    cases same
    rfl
  exact (readback (numerics.parents_list_eq supplied supplied_eq parents parents_eq) numerics.requested).trans
    (Numerical.minimumIndex_eq numerics)

end Numerical

end Purelib.Riemann.RootContinuation.RootPathTransport.TransportRow

end
