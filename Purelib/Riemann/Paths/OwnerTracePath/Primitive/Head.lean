module

public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Append
public import Purelib.Riemann.Paths.OwnerTracePath.Suffix
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Approximation.AccuracyRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Paths.OwnerTraceReadings

/-! # Original primitive observations at a literal retained head

An actual dropLink occurrence selects the original head link. Exact path
transport and the original Spine.split expose its complete old observation
and unchanged suffix with their literal shared Vertex. No vertex,
stationary decision, comparison or observation request is constructed.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Spine

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)

variable {polynomial : Coefficients} {expression : Expression polynomial} {accuracy : AccuracyRequest}
variable {start finish : Canonical} {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}
variable {path : OwnerPath polynomial start left finish right}

/-- The original head, exact path-index transport and complete old split at one actual suffix occurrence.

Both fields retain their whole original factory equations. The split
contains the old head's source/target Vertices and Stationary.Step, plus
the unchanged suffix with the identical shared Vertex; its accuracy and
expression remain the original input indices.
-/
@[expose] def Head (observed : Spine expression accuracy path) (suffix : Suffix right)
    (present : path.dropLink = some suffix) :=
  Σ head : {value : {link : OwnerLink polynomial start suffix.point left suffix.owner //
      path = .cons link suffix.path} // value = path.headLink suffix present},
  {value : Split (.cons head.val.val (.nil suffix.point suffix.owner)) suffix.path //
    value = split (.cons head.val.val (.nil suffix.point suffix.owner)) suffix.path
      (castPath head.val.property observed)}

/-- Extract the old head observation and literal suffix by the actual original constructor equation. -/
def atHead (observed : Spine expression accuracy path) (suffix : Suffix right)
    (present : path.dropLink = some suffix) : Head observed suffix present :=
  let head := path.headLink suffix present
  let aligned := castPath head.property observed
  let divided := split (.cons head.val (.nil suffix.point suffix.owner)) suffix.path aligned
  ⟨⟨head, rfl⟩, ⟨divided, rfl⟩⟩

namespace Head

variable {observed : Spine expression accuracy path} {suffix : Suffix right}
variable {present : path.dropLink = some suffix} (kept : Head observed suffix present)

/-- Read the actual complete original link before this supplied literal suffix. -/
abbrev link : OwnerLink polynomial start suffix.point left suffix.owner := kept.1.val.val

/-- The old whole path is its SAME head link followed by the identical original suffix. -/
theorem path_eq : path = .cons kept.link suffix.path := kept.1.val.property

/-- The complete retained head certificate is its original literal-head reader. -/
theorem head_eq : kept.1.val = path.headLink suffix present := kept.1.property

/-- Read the whole original split cache, retaining both old spines and their actual shared Vertex. -/
abbrev divided : Split (expression := expression) (accuracy := accuracy)
    (.cons kept.link (.nil suffix.point suffix.owner)) suffix.path := kept.2.val

/-- Read the complete old one-link observation, including its original Stationary.Step. -/
abbrev before : Spine expression accuracy (.cons kept.link (.nil suffix.point suffix.owner)) :=
  kept.divided.before

/-- Read the unchanged old following spine at this actual suffix's complete source Owner. -/
abbrev after : Spine expression accuracy suffix.path := kept.divided.after

/-- The two old spines retain one literal original target/source Vertex cache. -/
theorem shared : kept.after.first = kept.before.last := kept.divided.shared

/-- The whole split cache is its original factory on the unchanged path-transported observation. -/
theorem divided_eq : kept.divided = split (.cons kept.link (.nil suffix.point suffix.owner)) suffix.path
    (castPath kept.path_eq observed) := kept.2.property

/-- Rejoining the two views recovers the complete original old observation under its exact path index. -/
theorem rejoin_eq : append kept.before kept.after kept.shared = castPath kept.path_eq observed := by
  have same := congrArg
    (fun value : Split (.cons kept.link (.nil suffix.point suffix.owner)) suffix.path =>
      append value.before value.after value.shared) kept.divided_eq
  exact same.trans (append_split (castPath kept.path_eq observed))

/-- The head keeps the literal old source Vertex and its original observation request. -/
theorem first_eq : kept.before.first = observed.first := by
  have same := congrArg
    (fun value : Split (.cons kept.link (.nil suffix.point suffix.owner)) suffix.path => value.before.first)
    kept.divided_eq
  exact same.trans ((split_first (castPath kept.path_eq observed)).trans (castPath_first kept.path_eq observed))

/-- The following view keeps the literal old final Vertex without re-observing it. -/
theorem last_eq : kept.after.last = observed.last := by
  have same := congrArg
    (fun value : Split (.cons kept.link (.nil suffix.point suffix.owner)) suffix.path => value.after.last)
    kept.divided_eq
  exact same.trans ((split_last (castPath kept.path_eq observed)).trans (castPath_last kept.path_eq observed))

end Head

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Spine

end
