module

public import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Append
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Approximation.AccuracyRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTracePath.Primitive
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Spine
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Original moving observations with both actual endpoint joins

One new observation at each outer Point Owner is attached to the exact
retained moving Spine. Both stationary comparisons use their actual supplied
OwnerJoins, and the resulting complete Spine retains its append factory.
The two new handoffs have separate finite payments.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Paths.OwnerTraceReadings (Owner OwnerJoin)

/-- Attach both actual endpoint OwnerJoins around the unchanged original moving path. -/
@[expose] def withJoins {polynomial : Coefficients} {start finish : Canonical}
    {left outerLeft : Owner (polynomial.eval start)} {right outerRight : Owner (polynomial.eval finish)}
    (path : OwnerPath polynomial start left finish right)
    (source : OwnerJoin outerLeft left) (target : OwnerJoin right outerRight) :
    OwnerPath polynomial start outerLeft finish outerRight :=
  .cons (OwnerLink.stationary polynomial start source)
    (path.append (.cons (OwnerLink.stationary polynomial finish target) (.nil finish outerRight)))

/-- Both endpoint joins add their actual occurrences around the unchanged ordered moving vertices. -/
theorem withJoins_vertices {polynomial : Coefficients} {start finish : Canonical}
    {left outerLeft : Owner (polynomial.eval start)} {right outerRight : Owner (polynomial.eval finish)}
    (path : OwnerPath polynomial start left finish right)
    (source : OwnerJoin outerLeft left) (target : OwnerJoin right outerRight) :
    (path.withJoins source target).vertices = start :: (path.vertices ++ [finish]) := by
  unfold withJoins
  change start ::
    (path.append (.cons (OwnerLink.stationary polynomial finish target) (.nil finish outerRight))).vertices = _
  rewrite [append_vertices]
  rfl

namespace Primitive

namespace Stationary

/-- Keep both supplied observations and the exact actual comparison on one genuine coincident-endpoint link. -/
def spine {polynomial : Coefficients} {expression : Expression polynomial} {start finish : Canonical}
    {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)} {accuracy : AccuracyRequest}
    (link : OwnerLink polynomial start finish left right) (same : start = finish)
    (first : Vertex expression start left accuracy) (last : Vertex expression finish right accuracy)
    (compared : Compared link first last (.isTrue same)) :
    Spine expression accuracy (.cons link (.nil finish right)) :=
  ⟨first, last, ⟨.isTrue same, compared⟩, PUnit.unit⟩

/-- The stationary constructor retains the identical whole supplied source Vertex without another observation. -/
theorem spine_first {polynomial : Coefficients} {expression : Expression polynomial} {start finish : Canonical}
    {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)} {accuracy : AccuracyRequest}
    (link : OwnerLink polynomial start finish left right) (same : start = finish)
    (first : Vertex expression start left accuracy) (last : Vertex expression finish right accuracy)
    (compared : Compared link first last (.isTrue same)) :
    (spine link same first last compared).first = first := by
  unfold spine
  rfl

/-- The stationary constructor retains the identical whole supplied target Vertex without another observation. -/
theorem spine_last {polynomial : Coefficients} {expression : Expression polynomial} {start finish : Canonical}
    {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)} {accuracy : AccuracyRequest}
    (link : OwnerLink polynomial start finish left right) (same : start = finish)
    (first : Vertex expression start left accuracy) (last : Vertex expression finish right accuracy)
    (compared : Compared link first last (.isTrue same)) :
    (spine link same first last compared).last = last := by
  unfold spine
  rfl

end Stationary

namespace Spine

variable {polynomial : Coefficients} {expression : Expression polynomial} {accuracy : AccuracyRequest}
variable {start finish : Canonical}
variable {left outerLeft : Owner (polynomial.eval start)} {right outerRight : Owner (polynomial.eval finish)}
variable {path : OwnerPath polynomial start left finish right}
variable (moving : Spine expression accuracy path) (source : OwnerJoin outerLeft left)
variable (target : OwnerJoin right outerRight)

/-- Both stationary comparison caches refer to the two original joins and retained moving endpoint Vertices. -/
@[expose] def JoinComparisons
    (first : Vertex expression start outerLeft accuracy) (last : Vertex expression finish outerRight accuracy) :=
  Stationary.Compared (OwnerLink.stationary polynomial start source) first moving.first (.isTrue rfl) ×
    Stationary.Compared (OwnerLink.stationary polynomial finish target) moving.last last (.isTrue rfl)

/-- Assemble both exact stationary spines and the unchanged moving cache through the original append operation. -/
def attachSpines (first : Vertex expression start outerLeft accuracy)
    (last : Vertex expression finish outerRight accuracy) (compared : JoinComparisons moving source target first last) :
    Spine expression accuracy (path.withJoins source target) :=
  let before := Stationary.spine (OwnerLink.stationary polynomial start source) rfl first moving.first compared.1
  let after := Stationary.spine (OwnerLink.stationary polynomial finish target) rfl moving.last last compared.2
  let front := append before moving rfl
  append front after (append_last before moving rfl).symm

/-- Actual append construction preserves the entire outer source observation. -/
private theorem packaged_attachSpines_first (first : Vertex expression start outerLeft accuracy)
    (last : Vertex expression finish outerRight accuracy) (compared : JoinComparisons moving source target first last) :
    (attachSpines moving source target first last compared).first = first := rfl

/-- Actual append construction preserves the entire outer target observation. -/
private theorem packaged_attachSpines_last (first : Vertex expression start outerLeft accuracy)
    (last : Vertex expression finish outerRight accuracy) (compared : JoinComparisons moving source target first last) :
    (attachSpines moving source target first last compared).last = last := by
  unfold attachSpines
  exact append_last _ _ _

/-- Two new outer observations, their genuine join comparisons and the complete original append execution. -/
@[expose] def WithJoins :=
  Σ first : Vertex expression start outerLeft accuracy,
  Σ last : Vertex expression finish outerRight accuracy,
  Σ compared : JoinComparisons moving source target first last,
    {observed : Spine expression accuracy (path.withJoins source target) //
      observed = attachSpines moving source target first last compared}

/-- Observe both outer owners once and retain their actual join comparisons around the unchanged moving Spine. -/
def withJoins (firstDefined : expression.Defined start) (lastDefined : expression.Defined finish) :
    WithJoins moving source target :=
  let first := Vertex.build expression start outerLeft accuracy firstDefined
  let last := Vertex.build expression finish outerRight accuracy lastDefined
  let firstCompared := Stationary.compare (OwnerLink.stationary polynomial start source) rfl first moving.first
  let lastCompared := Stationary.compare (OwnerLink.stationary polynomial finish target) rfl moving.last last
  let compared : JoinComparisons moving source target first last :=
    ⟨⟨firstCompared, rfl⟩, ⟨lastCompared, rfl⟩⟩
  let observed := attachSpines moving source target first last compared
  ⟨first, last, compared, ⟨observed, rfl⟩⟩

namespace WithJoins

variable {moving source target}
variable (kept : WithJoins moving source target)

/-- Read the independent new outer source observation at its original Point Owner. -/
abbrev first := kept.1

/-- Read the separate new outer target observation unchanged. -/
abbrev last := kept.2.1

/-- Read both actual original stationary comparison caches and their exact factories. -/
abbrev comparisons := kept.2.2.1

/-- Read the complete actual appended observation cache without observing any moving vertex again. -/
abbrev observed := kept.2.2.2.val

/-- The complete appended execution uses these same outer observations, actual comparisons and original moving cache. -/
theorem observed_eq : kept.observed = attachSpines moving source target kept.first kept.last kept.comparisons :=
  kept.2.2.2.property

/-- The appended execution starts at the entire retained outer source Vertex. -/
theorem observed_first : kept.observed.first = kept.first :=
  (congrArg (fun spine : Spine expression accuracy (path.withJoins source target) => spine.first)
    kept.observed_eq).trans (packaged_attachSpines_first moving source target kept.first kept.last kept.comparisons)

/-- The appended execution finishes at the entire independent retained outer target Vertex. -/
theorem observed_last : kept.observed.last = kept.last :=
  (congrArg (fun spine : Spine expression accuracy (path.withJoins source target) => spine.last)
    kept.observed_eq).trans (packaged_attachSpines_last moving source target kept.first kept.last kept.comparisons)

/-- Both new join payments bound the actual change in the retained oriented primitive increment. -/
theorem increment_error_le : Norm.Basic.normSq
    ((kept.observed.last.value - kept.observed.first.value) - (moving.last.value - moving.first.value)) ≤
    4 * accuracy.tolerance := by
  have firstBound := (Stationary.jump_lt kept.first moving.first kept.comparisons.1.val).le
  have lastBound := (Stationary.jump_lt moving.last kept.last kept.comparisons.2.val).le
  rewrite [kept.observed_first, kept.observed_last]
  have decomposition : (kept.last.value - kept.first.value) - (moving.last.value - moving.first.value) =
      (kept.last.value - moving.last.value) + (moving.first.value - kept.first.value) := by ring1
  rewrite [decomposition]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct lastBound firstBound)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2)).trans_eq (by ring1))

end WithJoins

end Spine

end Primitive

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

end
