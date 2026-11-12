module

public import Purelib.Riemann.Paths.OwnerTracePath.Suffix

/-! # Finite splits of the actual materialized owner path

The count selects an actual retained constructor boundary. Both pieces,
the complete middle Owner and every original link come from the supplied
path. A canonical append equation is used only to certify the chosen
boundary; no expected prefix or trace factory is executed to recover data.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)

variable {polynomial : GaussianPolynomial}

namespace Split

/-- Read the complete original suffix from the retained split's point, owner and following path. -/
@[expose] def suffix {start finish : Canonical} {first : Owner (polynomial.eval start)}
    {last : Owner (polynomial.eval finish)} {path : OwnerPath polynomial start first finish last}
    (divided : Split path) : Suffix last :=
  ⟨divided.point, divided.owner, divided.remaining⟩

/-- Prepend one actual retained head link to a split of its identical tail. -/
@[expose] def prepend {start middle finish : Canonical} {first : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {last : Owner (polynomial.eval finish)}
    (link : OwnerLink polynomial start middle first center) (tail : OwnerPath polynomial middle center finish last)
    (divided : Split tail) : Split (.cons link tail) :=
  ⟨divided.point, divided.owner, .cons link divided.initial,
    ⟨divided.remaining, congrArg (OwnerPath.cons link) divided.append_eq⟩⟩

/-- Transport the SAME actual prefix along equality of its complete retained suffix tuple. -/
@[expose] def prefixCast {start finish : Canonical} {first : Owner (polynomial.eval start)}
    {last : Owner (polynomial.eval finish)} {path : OwnerPath polynomial start first finish last}
    (divided : Split path) {expected : Suffix last} (same : divided.suffix = expected) :
    OwnerPath polynomial start first expected.point expected.owner :=
  Eq.mp (congrArg (fun suffix : Suffix last =>
    OwnerPath polynomial start first suffix.point suffix.owner) same) divided.initial

/-- Complete-suffix reindexing preserves the entire supplied prefix heterogeneously. -/
theorem prefixCast_heq {start finish : Canonical} {first : Owner (polynomial.eval start)}
    {last : Owner (polynomial.eval finish)} {path : OwnerPath polynomial start first finish last}
    (divided : Split path) {expected : Suffix last} (same : divided.suffix = expected) :
    HEq (prefixCast divided same) divided.initial := by
  cases same
  rfl

/-- A complete exact split identifies its transported prefix without inspecting either path. -/
private theorem prefixCast_of_eq {start middle finish : Canonical}
    {first : Owner (polynomial.eval start)} {center : Owner (polynomial.eval middle)}
    {last : Owner (polynomial.eval finish)} (front : OwnerPath polynomial start first middle center)
    (following : OwnerPath polynomial middle center finish last) (divided : Split (front.append following))
    (factory : divided = ⟨middle, center, front, ⟨following, rfl⟩⟩)
    (same : divided.suffix = (⟨middle, center, following⟩ : Suffix last)) :
    prefixCast divided same = front := by
  cases factory
  rfl

end Split

/-- The zero boundary preserves the complete supplied path as its literal suffix. -/
theorem splitAt_zero {start finish : Canonical} {first : Owner (polynomial.eval start)}
    {last : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start first finish last) :
    splitAt 0 path = ⟨start, first, .nil start first, ⟨path, rfl⟩⟩ := rfl

/-- Every positive boundary on the empty path retains the same original empty prefix and suffix. -/
theorem splitAt_nil (count : Nat) (point : Canonical) (owner : Owner (polynomial.eval point)) :
    splitAt count (.nil point owner) = ⟨point, owner, .nil point owner, ⟨.nil point owner, rfl⟩⟩ := by
  cases count <;> rfl

/-- One split step consumes exactly the actual original head and the same retained tail. -/
theorem splitAt_cons (count : Nat) {start middle finish : Canonical}
    {first : Owner (polynomial.eval start)} {center : Owner (polynomial.eval middle)}
    {last : Owner (polynomial.eval finish)} (link : OwnerLink polynomial start middle first center)
    (tail : OwnerPath polynomial middle center finish last) :
    splitAt (count + 1) (.cons link tail) = Split.prepend link tail (splitAt count tail) := rfl

/-- Splitting an actual append at its original prefix length recovers both complete input pieces.

The equality includes the middle point, whole middle Owner, entire suffix,
entire prefix and append certificate. It does not identify any Owner from
coordinate equality or from equality of a numerical reading.
-/
theorem splitAt_append :
    ∀ {start middle finish : Canonical} {first : Owner (polynomial.eval start)}
      {center : Owner (polynomial.eval middle)} {last : Owner (polynomial.eval finish)}
      (front : OwnerPath polynomial start first middle center)
      (following : OwnerPath polynomial middle center finish last),
      splitAt front.vertices.length (front.append following) =
        ⟨middle, center, front, ⟨following, rfl⟩⟩
  | _, _, _, _, _, _, .nil _ _, _ => rfl
  | _, _, _, _, _, _, .cons link tail, following => by
      change Split.prepend link (tail.append following)
        (splitAt tail.vertices.length (tail.append following)) = _
      exact congrArg (fun divided : Split (tail.append following) =>
        Split.prepend link (tail.append following) divided) (splitAt_append tail following)
termination_by structural _ _ _ _ _ _ front _ => front

/-- The complete actual suffix, including its whole Owner and path, matches the original append boundary. -/
theorem splitAt_suffix {start middle finish : Canonical} {first : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {last : Owner (polynomial.eval finish)}
    (count : Nat) (materialized : OwnerPath polynomial start first finish last)
    (front : OwnerPath polynomial start first middle center)
    (following : OwnerPath polynomial middle center finish last)
    (countEq : count = front.vertices.length) (factory : materialized = front.append following) :
    (splitAt count materialized).suffix = (⟨middle, center, following⟩ : Suffix last) := by
  cases countEq
  cases factory
  exact congrArg (fun divided : Split (front.append following) => divided.suffix) (splitAt_append front following)

/-- The actual prefix reindexed by its whole-suffix identity equals the original append prefix. -/
theorem splitAt_prefix {start middle finish : Canonical} {first : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {last : Owner (polynomial.eval finish)}
    (count : Nat) (materialized : OwnerPath polynomial start first finish last)
    (front : OwnerPath polynomial start first middle center)
    (following : OwnerPath polynomial middle center finish last)
    (countEq : count = front.vertices.length) (factory : materialized = front.append following)
    (same : (splitAt count materialized).suffix = (⟨middle, center, following⟩ : Suffix last)) :
    Split.prefixCast (splitAt count materialized) same = front := by
  cases countEq
  cases factory
  exact Split.prefixCast_of_eq front following _ (splitAt_append front following) same

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

end
