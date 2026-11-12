module

public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine

/-! # Original primitive tails with two retained endpoint observations

A nonempty original OwnerPath can retain both supplied endpoint Vertex
caches. Only genuine internal vertices are observed. The original links
compare their actual adjacent observations, including stationary/repeated
occurrences; an empty path does not identify independent endpoint caches.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner)

variable {polynomial : Coefficients}

namespace Defined

/-- The original formal root expression is defined at every actual vertex of the SAME retained path. -/
theorem generator : {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} → (path : OwnerPath polynomial start left finish right) →
    Defined (Expression.generator (radicand := polynomial)) path
  | _, _, _, _, .nil point _ => Expression.defined_generator point
  | first, _, _, _, .cons _ tail => ⟨Expression.defined_generator first, generator tail⟩

end Defined

namespace Tail

/-- Construct a nonempty original tail while retaining both supplied endpoint Vertex caches.

The final link stores the supplied final cache verbatim. Every preceding
link builds its own intermediate Vertex once, passes that identical cache
as the following source, and retains its actual original Stationary.Step.
No endpoint Vertex, root Owner or OwnerJoin is acquired by this operation.
-/
def betweenCons (expression : Expression polynomial) (accuracy : AccuracyRequest) :
    {start middle finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {center : Owner (polynomial.eval middle)} → {right : Owner (polynomial.eval finish)} →
    (link : OwnerLink polynomial start middle left center) →
    (tail : OwnerPath polynomial middle center finish right) →
    (first : Vertex expression start left accuracy) → (last : Vertex expression finish right accuracy) →
    Defined expression tail → Tail expression accuracy (.cons link tail) first
  | _, _, _, _, _, _, link, .nil _ _, first, last, _ =>
      ⟨last, Stationary.Step.build link first last, PUnit.unit⟩
  | _, middle, _, _, center, _, link, .cons following remaining, first, last, defined =>
      let next := Vertex.build expression middle center accuracy defined.1
      let compared := Stationary.Step.build link first next
      let after := betweenCons expression accuracy following remaining next last defined.2
      ⟨next, compared, after⟩
termination_by structural _ _ _ _ _ _ _ tail _ _ _ => tail

/-- The entire supplied terminal Vertex, including its original request and reading state, is retained literally. -/
theorem betweenCons_last (expression : Expression polynomial) (accuracy : AccuracyRequest) :
    {start middle finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {center : Owner (polynomial.eval middle)} → {right : Owner (polynomial.eval finish)} →
    (link : OwnerLink polynomial start middle left center) →
    (tail : OwnerPath polynomial middle center finish right) →
    (first : Vertex expression start left accuracy) → (last : Vertex expression finish right accuracy) →
    (defined : Defined expression tail) →
    Tail.last (.cons link tail) first (betweenCons expression accuracy link tail first last defined) = last
  | _, _, _, _, _, _, _, .nil _ _, _, _, _ => rfl
  | _, middle, _, _, center, _, _, .cons following remaining, _, last, defined =>
      betweenCons_last expression accuracy following remaining
        (Vertex.build expression middle center accuracy defined.1) last defined.2
termination_by structural _ _ _ _ _ _ _ tail _ _ _ => tail

end Tail

namespace Spine

variable {expression : Expression polynomial} {accuracy : AccuracyRequest}
variable {start finish : Canonical} {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}

/-- Observe only the interior of an actual nonempty original path, retaining both old endpoint Vertex caches.

Nonemptiness is geometric incidence on this same data path. An actual
nil constructor is rejected by that negative certificate; no equality of
independent observations is inferred from its common point or Owner.
-/
def between (path : OwnerPath polynomial start left finish right)
    (nonempty : path.vertices ≠ []) (first : Vertex expression start left accuracy)
    (last : Vertex expression finish right accuracy) (defined : Defined expression path) :
    Spine expression accuracy path :=
  match path with
  | .nil _ _ => False.elim (nonempty rfl)
  | .cons link tail => ⟨first, Tail.betweenCons expression accuracy link tail first last defined.2⟩

/-- The source is the SAME entire supplied old Vertex; no source observation factory runs. -/
theorem between_first (path : OwnerPath polynomial start left finish right)
    (nonempty : path.vertices ≠ []) (first : Vertex expression start left accuracy)
    (last : Vertex expression finish right accuracy) (defined : Defined expression path) :
    (between path nonempty first last defined).first = first := by
  cases path with
  | nil => exact False.elim (nonempty rfl)
  | cons => rfl

/-- The final Vertex is likewise the unchanged actual old cache, not a new reading on the same Owner. -/
theorem between_last (path : OwnerPath polynomial start left finish right)
    (nonempty : path.vertices ≠ []) (first : Vertex expression start left accuracy)
    (last : Vertex expression finish right accuracy) (defined : Defined expression path) :
    (between path nonempty first last defined).last = last := by
  cases path with
  | nil => exact False.elim (nonempty rfl)
  | cons link tail => exact Tail.betweenCons_last expression accuracy link tail first last defined.2

end Spine

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive

end
