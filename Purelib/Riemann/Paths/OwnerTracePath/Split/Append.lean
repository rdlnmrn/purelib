module

public import Purelib.Riemann.Paths.OwnerTracePath.Split
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTracePath.Suffix
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Retained OwnerPath splits under exact transports and concatenation

Whole path/suffix equalities transport actual split data. Appending a
prefix or suffix retains the selected original middle point and Owner;
no link, root comparison or trace factory is reconstructed.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {polynomial : GaussianPolynomial}

namespace Split

/-- The selected whole point/Owner pair of a retained original split. -/
@[expose] def vertex {start finish : Canonical} {first : Owner (polynomial.eval start)}
    {last : Owner (polynomial.eval finish)} {path : OwnerPath polynomial start first finish last}
    (divided : Split path) : Σ point : Canonical, Owner (polynomial.eval point) :=
  ⟨divided.suffix.point, divided.suffix.owner⟩

/-- Transport the SAME split through exact outer endpoint and whole-Owner reindices of its original path. -/
def castEndpoints {start finish nextStart nextFinish : Canonical}
    {first : Owner (polynomial.eval start)} {last : Owner (polynomial.eval finish)}
    {nextFirst : Owner (polynomial.eval nextStart)} {nextLast : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (firstEq : HEq first nextFirst) (lastEq : HEq last nextLast)
    {path : OwnerPath polynomial start first finish last} (divided : Split path) :
    Split (path.castEndpoints startEq finishEq firstEq lastEq) := by
  cases startEq
  cases finishEq
  cases eq_of_heq firstEq
  cases eq_of_heq lastEq
  exact divided

/-- Exact outer endpoint transport preserves the selected whole original middle vertex. -/
theorem castEndpoints_vertex {start finish nextStart nextFinish : Canonical}
    {first : Owner (polynomial.eval start)} {last : Owner (polynomial.eval finish)}
    {nextFirst : Owner (polynomial.eval nextStart)} {nextLast : Owner (polynomial.eval nextFinish)}
    (startEq : start = nextStart) (finishEq : finish = nextFinish)
    (firstEq : HEq first nextFirst) (lastEq : HEq last nextLast)
    {path : OwnerPath polynomial start first finish last} (divided : Split path) :
    (castEndpoints startEq finishEq firstEq lastEq divided).vertex = divided.vertex := by
  cases startEq
  cases finishEq
  cases eq_of_heq firstEq
  cases eq_of_heq lastEq
  rfl

/-- Reindex a split through a whole equality of the original materialized paths. -/
def castPath {start finish : Canonical} {first : Owner (polynomial.eval start)}
    {last : Owner (polynomial.eval finish)} {before after : OwnerPath polynomial start first finish last}
    (same : before = after) (divided : Split before) : Split after :=
  Eq.mp (congrArg Split same) divided

/-- Whole-path transport retains the entire original selected suffix. -/
theorem castPath_suffix {start finish : Canonical} {first : Owner (polynomial.eval start)}
    {last : Owner (polynomial.eval finish)} {before after : OwnerPath polynomial start first finish last}
    (same : before = after) (divided : Split before) : (castPath same divided).suffix = divided.suffix := by
  cases same
  rfl

/-- Whole-path transport preserves the selected original point and complete Owner. -/
theorem castPath_vertex {start finish : Canonical} {first : Owner (polynomial.eval start)}
    {last : Owner (polynomial.eval finish)} {before after : OwnerPath polynomial start first finish last}
    (same : before = after) (divided : Split before) : (castPath same divided).vertex = divided.vertex := by
  cases same
  rfl

/-- Reindex a split through a whole original source-point/Owner/tail tuple equality. -/
def castSuffix {finish : Canonical} {last : Owner (polynomial.eval finish)} {before after : Suffix last}
    (same : before = after) (divided : Split before.path) : Split after.path :=
  Eq.mp (congrArg (fun suffix : Suffix last => Split suffix.path) same) divided

/-- Whole-suffix transport preserves the complete selected original following path and its Owner. -/
theorem castSuffix_suffix {finish : Canonical} {last : Owner (polynomial.eval finish)}
    {before after : Suffix last} (same : before = after) (divided : Split before.path) :
    (castSuffix same divided).suffix = divided.suffix := by
  cases same
  rfl

/-- Whole-suffix transport preserves the same selected point and complete Owner. -/
theorem castSuffix_vertex {finish : Canonical} {last : Owner (polynomial.eval finish)}
    {before after : Suffix last} (same : before = after) (divided : Split before.path) :
    (castSuffix same divided).vertex = divided.vertex := by
  cases same
  rfl

/-- Prepend one GIVEN whole path to a retained split without changing the selected original suffix. -/
def prependPath {start middle finish : Canonical} {first : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {last : Owner (polynomial.eval finish)}
    (front : OwnerPath polynomial start first middle center) (path : OwnerPath polynomial middle center finish last)
    (divided : Split path) : Split (front.append path) :=
  ⟨divided.point, divided.owner, front.append divided.initial,
    ⟨divided.remaining, (OwnerPath.append_assoc front divided.initial divided.remaining).trans
      (congrArg (fun tail => front.append tail) divided.append_eq)⟩⟩

/-- Prefix concatenation retains the entire SAME original suffix, including every stored Owner and link. -/
theorem prependPath_suffix {start middle finish : Canonical} {first : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {last : Owner (polynomial.eval finish)}
    (front : OwnerPath polynomial start first middle center) (path : OwnerPath polynomial middle center finish last)
    (divided : Split path) : (prependPath front path divided).suffix = divided.suffix := by
  unfold prependPath
  rfl

/-- Prefix concatenation preserves the selected whole original middle vertex. -/
theorem prependPath_vertex {start middle finish : Canonical} {first : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {last : Owner (polynomial.eval finish)}
    (front : OwnerPath polynomial start first middle center) (path : OwnerPath polynomial middle center finish last)
    (divided : Split path) : (prependPath front path divided).vertex = divided.vertex := by
  unfold prependPath
  rfl

end Split

/-- Splitting after a GIVEN actual prefix reads the SAME original suffix split and preserves its whole ownership.

The structural proof traverses only the supplied prefix. The original
splitAt and append operations retain every link, including stationary
ones, and no concatenated path is recomputed to perform this readback.
-/
theorem splitAt_afterPrefix :
    ∀ {start middle finish : Canonical} {first : Owner (polynomial.eval start)}
      {center : Owner (polynomial.eval middle)} {last : Owner (polynomial.eval finish)}
      (front : OwnerPath polynomial start first middle center)
      (after : OwnerPath polynomial middle center finish last) (count : Nat),
    splitAt (front.vertices.length + count) (front.append after) =
      Split.prependPath front after (splitAt count after)
  | _, _, _, _, _, _, .nil _ _, after, count => by
      change splitAt (0 + count) after = Split.prependPath (.nil _ _) after (splitAt count after)
      rewrite [Nat.zero_add]
      unfold Split.prependPath
      rcases splitAt count after with ⟨suffix, front⟩
      rfl
  | _, _, _, _, _, _, .cons link tail, after, count => by
      have offset : (tail.vertices.length + 1) + count = (tail.vertices.length + count) + 1 :=
        Nat.succ_add tail.vertices.length count
      change splitAt ((tail.vertices.length + 1) + count) (.cons link (tail.append after)) = _
      rewrite [offset]
      change Split.prepend link (tail.append after) (splitAt (tail.vertices.length + count)
        (tail.append after)) = _
      exact (congrArg (Split.prepend link (tail.append after)) (splitAt_afterPrefix tail after count)).trans
        (by unfold Split.prependPath Split.prepend; rfl)
termination_by structural _ _ _ _ _ _ front _ _ => front

/-- Prepending one actual retained link preserves the complete selected suffix. -/
theorem split_prepend_vertex {start middle finish : Canonical} {first : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {last : Owner (polynomial.eval finish)}
    (link : OwnerLink polynomial start middle first center) (after : OwnerPath polynomial middle center finish last)
    (divided : Split after) : (Split.prepend link after divided).vertex = divided.vertex := by
  unfold Split.prepend
  rfl

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

end
