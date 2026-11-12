module

public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Approximation.AccuracyRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Paths.OwnerTraceReadings

/-! # Complete old primitive caches across an original path append

The same original OwnerPath append determines the indices. Splitting an old
spine retains every old vertex, stationary decision and actual comparison.
Appending accepts the identical shared vertex cache; equality of coordinates
or root Owners alone is insufficient. No primitive observation is selected.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)

variable {polynomial : Coefficients} {expression : Expression polynomial} {accuracy : AccuracyRequest}

namespace Tail

/-- Append two complete old tails whose shared source is the SAME literal preceding final vertex.

Every original target vertex and stationary Step in the prefix is reused.
The suffix is handed over unchanged at the original nil boundary. Neither
an observation request nor a stationary comparison producer is executed.
-/
@[expose] def append :
    {start middle finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {center : Owner (polynomial.eval middle)} → {right : Owner (polynomial.eval finish)} →
    (front : OwnerPath polynomial start left middle center) →
    (suffix : OwnerPath polynomial middle center finish right) →
    (first : Vertex expression start left accuracy) →
    (before : Tail expression accuracy front first) →
    Tail expression accuracy suffix (last front first before) →
      Tail expression accuracy (front.append suffix) first
  | _, _, _, _, _, _, .nil _ _, _, _, _, after => after
  | _, _, _, _, _, _, .cons _link remaining, suffix, _first, before, after =>
      ⟨before.1, before.2.1, append remaining suffix before.1 before.2.2 after⟩
termination_by structural _ _ _ _ _ _ front _ _ _ _ => front

/-- Both old tails retain their exact final vertex after the original path append. -/
theorem append_last : ∀ {start middle finish : Canonical} {left : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {right : Owner (polynomial.eval finish)}
    (front : OwnerPath polynomial start left middle center)
    (suffix : OwnerPath polynomial middle center finish right)
    (first : Vertex expression start left accuracy) (before : Tail expression accuracy front first)
    (after : Tail expression accuracy suffix (last front first before)),
    last (front.append suffix) first (append front suffix first before after) =
      last suffix (last front first before) after
  | _, _, _, _, _, _, .nil _ _, _, _, _, _ => rfl
  | _, _, _, _, _, _, .cons _ remaining, suffix, _first, before, after =>
      append_last remaining suffix before.1 before.2.2 after
termination_by structural _ _ _ _ _ _ front _ _ _ _ => front

/-- Exact source-cache transport preserves the SAME original final vertex of an old tail. -/
theorem last_of_source_eq {start finish : Canonical} {left : Owner (polynomial.eval start)}
    {right : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start left finish right)
    {first next : Vertex expression start left accuracy} (same : first = next)
    (observed : Tail expression accuracy path first) :
    last path next ((congrArg (Tail expression accuracy path) same).mp observed) = last path first observed := by
  cases same
  rfl

/-- Both complete old tails at an original append boundary retain their identical shared vertex cache. -/
@[expose] def Split {start middle finish : Canonical} {left : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {right : Owner (polynomial.eval finish)}
    (front : OwnerPath polynomial start left middle center)
    (suffix : OwnerPath polynomial middle center finish right)
    (first : Vertex expression start left accuracy) :=
  Σ before : Tail expression accuracy front first,
    Tail expression accuracy suffix (last front first before)

/-- Split a complete old tail through the SAME original prefix constructors without observing any vertex again. -/
@[expose] def split :
    {start middle finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {center : Owner (polynomial.eval middle)} → {right : Owner (polynomial.eval finish)} →
    (front : OwnerPath polynomial start left middle center) →
    (suffix : OwnerPath polynomial middle center finish right) →
    (first : Vertex expression start left accuracy) →
    Tail expression accuracy (front.append suffix) first → Split front suffix first
  | _, _, _, _, _, _, .nil _ _, _, _, observed => ⟨PUnit.unit, observed⟩
  | _, _, _, _, _, _, .cons _link remaining, suffix, _first, observed =>
      let divided := split remaining suffix observed.1 observed.2.2
      ⟨⟨observed.1, observed.2.1, divided.1⟩, divided.2⟩
termination_by structural _ _ _ _ _ _ front _ _ _ => front

/-- Reappending the split recovers the WHOLE old tail, including every retained actual comparison cache. -/
theorem append_split : ∀ {start middle finish : Canonical} {left : Owner (polynomial.eval start)}
    {center : Owner (polynomial.eval middle)} {right : Owner (polynomial.eval finish)}
    (front : OwnerPath polynomial start left middle center)
    (suffix : OwnerPath polynomial middle center finish right)
    (first : Vertex expression start left accuracy)
    (observed : Tail expression accuracy (front.append suffix) first),
    append front suffix first (split front suffix first observed).1 (split front suffix first observed).2 =
      observed
  | _, _, _, _, _, _, .nil _ _, _, _, _ => rfl
  | _, _, _, _, _, _, .cons link remaining, suffix, first, observed => by
      have tail := append_split remaining suffix observed.1 observed.2.2
      exact congrArg (fun following : Tail expression accuracy (remaining.append suffix) observed.1 =>
        (⟨observed.1, observed.2.1, following⟩ :
          Tail expression accuracy ((OwnerPath.cons link remaining).append suffix) first)) tail
termination_by structural _ _ _ _ _ _ front _ _ _ => front

end Tail

namespace Spine

variable {start middle finish : Canonical} {left : Owner (polynomial.eval start)}
variable {center : Owner (polynomial.eval middle)} {right : Owner (polynomial.eval finish)}
variable {front : OwnerPath polynomial start left middle center}
variable {suffix : OwnerPath polynomial middle center finish right}

/-- Append complete old spines using an exact identity of the shared vertex cache.

The entire old inputs remain available. The supplied identity transports
only the suffix tail's source index. A pair of independently observed seam
values is not identified merely because its coordinate and Owner coincide.
-/
@[expose] def append (before : Spine expression accuracy front) (after : Spine expression accuracy suffix)
    (same : after.first = before.last) : Spine expression accuracy (front.append suffix) :=
  ⟨before.first, Tail.append front suffix before.first before.2
    ((congrArg (Tail expression accuracy suffix) same).mp after.2)⟩

/-- The actual appended spine begins with the SAME entire original prefix source vertex cache. -/
theorem append_first (before : Spine expression accuracy front) (after : Spine expression accuracy suffix)
    (same : after.first = before.last) : (append before after same).first = before.first := rfl

/-- The complete suffix final vertex cache remains the appended spine's literal final vertex. -/
theorem append_last (before : Spine expression accuracy front) (after : Spine expression accuracy suffix)
    (same : after.first = before.last) : (append before after same).last = after.last := by
  have retained := Tail.append_last front suffix before.first before.2
    ((congrArg (Tail expression accuracy suffix) same).mp after.2)
  exact retained.trans (Tail.last_of_source_eq suffix same after.2)

/-- Equal complete input spines give the SAME append cache, independently of their proof-only shared-index witnesses. -/
theorem append_congr {before nextBefore : Spine expression accuracy front}
    {after nextAfter : Spine expression accuracy suffix} (beforeEq : before = nextBefore)
    (afterEq : after = nextAfter) (same : after.first = before.last)
    (nextSame : nextAfter.first = nextBefore.last) :
    append before after same = append nextBefore nextAfter nextSame := by
  cases beforeEq
  cases afterEq
  rfl

/-- A full split retains the two complete old spines and their exact shared vertex identity. -/
@[expose] def Split (front : OwnerPath polynomial start left middle center)
    (suffix : OwnerPath polynomial middle center finish right) :=
  Σ before : Spine expression accuracy front,
    { after : Spine expression accuracy suffix // after.first = before.last }

/-- Split the SAME old spine into complete original prefix and suffix caches, with no observation replay. -/
@[expose] def split (front : OwnerPath polynomial start left middle center)
    (suffix : OwnerPath polynomial middle center finish right)
    (observed : Spine expression accuracy (front.append suffix)) :
    Split (expression := expression) (accuracy := accuracy) front suffix :=
  let divided := Tail.split front suffix observed.first observed.2
  ⟨⟨observed.first, divided.1⟩, ⟨⟨Tail.last front observed.first divided.1, divided.2⟩, rfl⟩⟩

namespace Split

variable (divided : Split (expression := expression) (accuracy := accuracy) front suffix)

/-- Read the complete old prefix spine from the original split cache. -/
@[expose] def before : Spine expression accuracy front := divided.1

/-- Read the complete old suffix spine whose source is the identical retained prefix endpoint. -/
@[expose] def after : Spine expression accuracy suffix := divided.2.val

/-- The two complete old views retain one literal shared source/target vertex cache. -/
theorem shared : divided.after.first = divided.before.last := divided.2.property

end Split

/-- The split prefix keeps the entire old source vertex, including its original state and request. -/
theorem split_first (observed : Spine expression accuracy (front.append suffix)) :
    (split front suffix observed).before.first = observed.first := rfl

/-- Appending the two split views recovers the WHOLE original spine, not only its endpoint values or vertex list. -/
theorem append_split (observed : Spine expression accuracy (front.append suffix)) :
    append (split front suffix observed).before (split front suffix observed).after
      (split front suffix observed).shared = observed := by
  exact congrArg (fun following : Tail expression accuracy (front.append suffix) observed.first =>
    (⟨observed.first, following⟩ : Spine expression accuracy (front.append suffix)))
      (Tail.append_split front suffix observed.first observed.2)

/-- The split suffix keeps the complete old final vertex cache unchanged. -/
theorem split_last (observed : Spine expression accuracy (front.append suffix)) :
    (split front suffix observed).after.last = observed.last := by
  have final := append_last (split front suffix observed).before (split front suffix observed).after
    (split front suffix observed).shared
  exact final.symm.trans (congrArg (fun retained : Spine expression accuracy (front.append suffix) => retained.last)
    (append_split observed))

/-- Append three actual old Spines through exact identities of both retained shared Vertices.

The same two original append constructors execute once each. The returned
path remains actual data, so a caller need not infer the dependent path
index of either intermediate Spine through a large retained crop cache.
-/
def appendThree {firstMiddle secondMiddle : Canonical}
    {firstOwner : Owner (polynomial.eval firstMiddle)} {secondOwner : Owner (polynomial.eval secondMiddle)}
    {firstPath : OwnerPath polynomial start left firstMiddle firstOwner}
    {betweenPath : OwnerPath polynomial firstMiddle firstOwner secondMiddle secondOwner}
    {lastPath : OwnerPath polynomial secondMiddle secondOwner finish right}
    (before : Spine expression accuracy firstPath) (between : Spine expression accuracy betweenPath)
    (after : Spine expression accuracy lastPath)
    (source : between.first = before.last) (target : between.last = after.first) :
    Σ actual : OwnerPath polynomial start left finish right, Spine expression accuracy actual :=
  let front := append (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
    before between source
  let final := append (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
    front after ((append_last (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
      before between source).trans target).symm
  ⟨_, final⟩

/-- Three-Spine composition retains the complete original two-append result and all actual input caches. -/
theorem appendThree_eq {firstMiddle secondMiddle : Canonical}
    {firstOwner : Owner (polynomial.eval firstMiddle)} {secondOwner : Owner (polynomial.eval secondMiddle)}
    {firstPath : OwnerPath polynomial start left firstMiddle firstOwner}
    {betweenPath : OwnerPath polynomial firstMiddle firstOwner secondMiddle secondOwner}
    {lastPath : OwnerPath polynomial secondMiddle secondOwner finish right}
    (before : Spine expression accuracy firstPath) (between : Spine expression accuracy betweenPath)
    (after : Spine expression accuracy lastPath)
    (source : between.first = before.last) (target : between.last = after.first) :
    appendThree (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
      before between after source target =
      let front := append (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
        before between source
      let final := append (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
        front after ((append_last (polynomial := polynomial) (expression := expression) (accuracy := accuracy)
          before between source).trans target).symm
      (⟨(firstPath.append betweenPath).append lastPath, final⟩ :
        Σ actual : OwnerPath polynomial start left finish right, Spine expression accuracy actual) := by
  unfold appendThree
  rfl

end Spine

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive

end
