module

public import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.RootIsolation.SquareRoot.Owner.Transport

/-! # Literal suffixes of a retained original OwnerPath

A single direct constructor elimination reads the actual middle point,
whole middle Owner and original tail. Exact suffix/index transports retain
those same objects; no link, source query or continuation is produced.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter)

variable {polynomial : GaussianPolynomial} {finish : Canonical}
    {last : Owner (polynomial.eval finish)}

/-- A literal original tail, with its actual source point and complete stored source Owner. -/
@[expose] def Suffix (last : Owner (polynomial.eval finish)) :=
  (point : Canonical) × (owner : Owner (polynomial.eval point)) × OwnerPath polynomial point owner finish last

namespace Suffix

/-- Read the exact retained source point of the original tail. -/
@[expose] def point (suffix : Suffix last) : Canonical := suffix.1

/-- Read the complete actual source Owner, without reconstructing its source factory. -/
@[expose] def owner (suffix : Suffix last) : Owner (polynomial.eval suffix.point) := suffix.2.1

/-- Read the identical stored tail at its same nominal source point and Owner. -/
@[expose] def path (suffix : Suffix last) : OwnerPath polynomial suffix.point suffix.owner finish last := suffix.2.2

/-- Reindex only the actual retained Owner along an exact equality of complete suffixes. -/
@[expose] def ownerCast {first second : Suffix last} (same : first = second) : Owner (polynomial.eval second.point) :=
  castOwnerParameter (congrArg polynomial.eval (congrArg Suffix.point same)) first.owner

/-- The transported whole Owner equals the exact source Owner of the equal suffix. -/
theorem ownerCast_eq {first second : Suffix last} (same : first = second) :
    ownerCast same = second.owner := by
  cases same
  rfl

/-- Reindex the same original tail using an exact equality of complete suffixes. -/
@[expose, macro_inline] def pathCast {first second : Suffix last} (same : first = second) :
    OwnerPath polynomial second.point second.owner finish last :=
  Eq.mp (congrArg (fun suffix : Suffix last =>
    OwnerPath polynomial suffix.point suffix.owner finish last) same) first.path

/-- Exact suffix transport preserves the entire original tail heterogeneously. -/
theorem pathCast_heq {first second : Suffix last} (same : first = second) : HEq (pathCast same) first.path := by
  cases same
  rfl

/-- The transported original tail equals the entire tail of the equal suffix. -/
theorem pathCast_eq {first second : Suffix last} (same : first = second) : pathCast same = second.path := by
  cases same
  rfl

/-- Repacking an exactly reindexed tail retains the whole original suffix, including its source Owner.

The equality concerns the complete point/Owner/path tuple. It permits
transport of a dependent observation cache without recovering a source
Owner from coordinates or from a heterogeneous path equality alone.
-/
theorem pathCast_suffix {first second : Suffix last} (same : first = second) :
    (⟨second.point, second.owner, pathCast same⟩ : Suffix last) = first := by
  cases same
  rfl

end Suffix

/-- Drop one actual retained link and read its literal middle Owner and unchanged tail.

The direct constructor eliminator reads the original hidden middle fields.
The empty path has no following link; the nonempty path returns its actual
middle and tail data, without evaluating any owner-path factory.
-/
@[expose] def dropLink {start : Canonical} {first : Owner (polynomial.eval start)}
    (path : OwnerPath polynomial start first finish last) : Option (Suffix last) :=
  OwnerPath.casesOn
    (motive := fun _ _ finish last _ => Option (Suffix (finish := finish) last)) path
    (fun _ _ => none)
    (fun {_start middle _finish _left center _right} _ tail => some ⟨middle, center, tail⟩)

/-- The exact original empty path has no following source Owner or tail. -/
theorem dropLink_nil (point : Canonical) (owner : Owner (polynomial.eval point)) :
    (OwnerPath.nil point owner).dropLink = none := by rfl

/-- One actual constructor exposes its same original middle, source Owner and tail, with complete equality. -/
theorem dropLink_cons {start middle : Canonical} {first : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)}
    (link : OwnerLink polynomial start middle first center) (tail : OwnerPath polynomial middle center finish last) :
    (OwnerPath.cons link tail).dropLink = some ⟨middle, center, tail⟩ := by rfl

/-- Read the actual original head link and its whole constructor equation from a retained suffix occurrence.

The supplied dropLink equation fixes the complete middle Owner and tail.
Direct elimination reads the original link; it constructs no root,
continuation, comparison or alternative path. An empty head is excluded
by that same actual Option equation.
-/
def headLink {start : Canonical} {first : Owner (polynomial.eval start)}
    (path : OwnerPath polynomial start first finish last) (suffix : Suffix last)
    (present : path.dropLink = some suffix) :
    {link : OwnerLink polynomial start suffix.point first suffix.owner // path = .cons link suffix.path} :=
  OwnerPath.casesOn
    (motive := fun start first finish last path =>
      (suffix : Suffix (finish := finish) last) → path.dropLink = some suffix →
      {link : OwnerLink polynomial start suffix.point first suffix.owner // path = .cons link suffix.path}) path
    (fun _ _ _ present => False.elim (by cases present))
    (fun {_start middle _finish _first center last} link tail suffix present => by
      have same : (⟨middle, center, tail⟩ : Suffix last) = suffix := Option.some.inj present
      cases same
      exact ⟨link, rfl⟩)
    suffix present

/-- Exact endpoint transport preserves the entire input OwnerPath heterogeneously. -/
theorem castEndpoints_heq {start nextStart nextFinish : Canonical}
    {first : Owner (polynomial.eval start)} {nextFirst : Owner (polynomial.eval nextStart)}
    {nextLast : Owner (polynomial.eval nextFinish)}
    (start_eq : start = nextStart) (finish_eq : finish = nextFinish)
    (first_eq : HEq first nextFirst) (last_eq : HEq last nextLast)
    (path : OwnerPath polynomial start first finish last) :
    HEq (path.castEndpoints start_eq finish_eq first_eq last_eq) path := by
  cases start_eq
  cases finish_eq
  cases eq_of_heq first_eq
  cases eq_of_heq last_eq
  rfl

/-- Reversing the same exact endpoint transports recovers the entire original OwnerPath. -/
theorem castEndpoints_inverse {start nextStart nextFinish : Canonical}
    {first : Owner (polynomial.eval start)} {nextFirst : Owner (polynomial.eval nextStart)}
    {nextLast : Owner (polynomial.eval nextFinish)}
    (start_eq : start = nextStart) (finish_eq : finish = nextFinish)
    (first_eq : HEq first nextFirst) (last_eq : HEq last nextLast)
    (path : OwnerPath polynomial start first finish last) :
    (path.castEndpoints start_eq finish_eq first_eq last_eq).castEndpoints
      start_eq.symm finish_eq.symm first_eq.symm last_eq.symm = path := by
  cases start_eq
  cases finish_eq
  cases eq_of_heq first_eq
  cases eq_of_heq last_eq
  rfl

/-- Reversing exact endpoint-Owner reindexing preserves the original complete path. -/
theorem reindexOwners_inverse {start : Canonical}
    {first nextFirst : Owner (polynomial.eval start)} {nextLast : Owner (polynomial.eval finish)}
    (first_eq : first = nextFirst) (last_eq : last = nextLast)
    (path : OwnerPath polynomial start first finish last) :
    (path.reindexOwners first_eq last_eq).reindexOwners first_eq.symm last_eq.symm = path := by
  cases first_eq
  cases last_eq
  rfl

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

end
