module

public import Purelib.Riemann.Paths.OwnerTracePath.Between
public import Purelib.Riemann.Paths.OwnerTraceReadings.Reverse
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.RootContinuation.SquareRootTrace
import Purelib.Data.List.Append
import Purelib.Data.List.Reverse
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Polynomial.Dense.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Tactic.Ring
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Paths.OwnerTraceReadings

/-! # Reversing actual retained native reading spines

A reverse realizer is indexed by each original ordered link occurrence.
It must supply its own reverse edge certificate on the GIVEN readings and
GIVEN checked forward edge. Neither forward Small nor endpoint names alone
provide this data. The actual reverse fold uses the original complete
interior/end readings and each original checked forward distance cache.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Paths.OwnerTraceReadings
open Purelib.Riemann.RootContinuation.SquareRootTrace (EdgeData Edge Chain)
open Purelib.Data.List

namespace OwnerLink

variable {polynomial : CoefficientPolynomial} {start finish : Canonical}
    {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}

/-- An actual reverse edge operation on the SAME complete readings and checked original forward edge.

Its cache equations retain the given displacement and the original final
reading's norm and residual. The reverse quantitative proof is additional
mathematical data, not inferred from the forward edge's Small certificate.
-/
@[expose] def ReverseData (link : OwnerLink polynomial start finish left right) :=
  ∀ (first : OwnerReading left) (last : OwnerReading right),
    link.leftIndex ≤ first.index → link.rightIndex ≤ last.index →
    (forward : Edge polynomial first.value last.value start finish) →
      { backward : Edge polynomial last.value first.value finish start //
        backward.data.distance = forward.data.distance ∧
        backward.data.rootNorm = last.reading.norm ∧ backward.data.residual = last.reading.residualNorm }

/-- Reverse an original link's roles, retaining both exact tails and selected floors.

A later independent realization may call the original link's arithmetic
realizer. The retained-spine reverse fold below instead passes its GIVEN
checked forward edge directly and performs no forward realization replay.
-/
def reverse (link : OwnerLink polynomial start finish left right) (paid : ReverseData link) :
    OwnerLink polynomial finish start right left where
  leftTail := link.rightTail
  rightTail := link.leftTail
  leftIndex := link.rightIndex
  rightIndex := link.leftIndex
  left_ge := link.right_ge
  right_ge := link.left_ge
  realize := fun last first lastLater firstLater =>
    let forward := link.realize first last firstLater lastLater
    (paid ⟨link.leftTail, first⟩ ⟨link.rightTail, last⟩ firstLater lastLater forward).val

/-- Reverse a stationary link on the GIVEN cached symmetric join and reuse its checked forward displacement.

Both native reading objects and the actual comparison floors remain fixed.
Only zero base variation is constructed; no selector or reading runs.
-/
def stationaryReverseData (point : Canonical) {left right : Owner (polynomial.eval point)}
    (join : OwnerJoin left right) (sameLower : join.leftTail.lower = join.rightTail.lower)
    (swapped : { value : OwnerJoin right left // value = join.symm sameLower }) :
    ReverseData (OwnerLink.stationary polynomial point join) := by
  intro first last firstLater lastLater forward
  have leftFloor : swapped.val.comparison.leftIndex = join.comparison.rightIndex :=
    (congrArg (fun value : OwnerJoin right left => value.comparison.leftIndex) swapped.property).trans
      (join.symm_leftIndex sameLower)
  have rightFloor : swapped.val.comparison.rightIndex = join.comparison.leftIndex :=
    (congrArg (fun value : OwnerJoin right left => value.comparison.rightIndex) swapped.property).trans
      (join.symm_rightIndex sameLower)
  have leftTail : swapped.val.leftTail = join.rightTail :=
    (congrArg (fun value : OwnerJoin right left => value.leftTail) swapped.property).trans
      (join.symm_leftTail sameLower)
  have rightTail : swapped.val.rightTail = join.leftTail :=
    (congrArg (fun value : OwnerJoin right left => value.rightTail) swapped.property).trans
      (join.symm_rightTail sameLower)
  let incoming := last.inTail swapped.val.leftTail
    (Eq.mpr (congrArg (fun tail : OwnerTail right => tail.first ≤ last.index) leftTail)
      (join.comparison.right_ge.trans lastLater))
  let outgoing := first.inTail swapped.val.rightTail
    (Eq.mpr (congrArg (fun tail : OwnerTail left => tail.first ≤ first.index) rightTail)
      (join.comparison.left_ge.trans firstLater))
  have distance := swapped.val.distance incoming outgoing
    (leftFloor.trans_le lastLater) (rightFloor.trans_le firstLater)
  have symmetry : Canonical.normSq (last.value - first.value) =
      Canonical.normSq (first.value - last.value) := by
    rewrite [← Canonical.normSq_neg (first.value - last.value)]
    congr 1
    ring1
  have distanceEq := forward.data.distance_eq.trans symmetry
  let data : EdgeData polynomial last.value first.value point point :=
    { rootNorm := last.reading.norm
      rootNorm_eq := last.reading.norm_eq
      distance := forward.data.distance
      distance_eq := distanceEq
      residual := last.reading.residualNorm
      residual_eq := last.reading.residualNorm_eq
      variation := 0
      variation_eq := by
        intro time
        rewrite [Polynomial.Dense.Basic.DensePolynomial.eval_zero]
        have same : Geometry.Rational.Affine.line point (point - point) time = point := by
          unfold Geometry.Rational.Affine.line
          ring1
        rewrite [same, Basic.sub_self]
        rfl
      movementBound := 0
      movementBound_valid := by
        intro time _inside
        rewrite [Polynomial.Dense.Basic.DensePolynomial.eval_zero, Canonical.normSq_zero]
        exact Order.Basic.le_refl _ }
  let backward : Edge polynomial last.value first.value point point :=
    ⟨data, last.tail.lower_positive.trans_le last.reading.lower,
      distanceEq.trans_le distance, last.reading.residual_small,
      Order.Field.div_nonneg_direct
        (Order.Arithmetic.sq_nonneg_direct _)
        (Data.Rat.Fraction.Cast.Order.natCast_pos_direct (n := 1024) (by decide +kernel)).le⟩
  exact ⟨backward, rfl, rfl, rfl⟩

end OwnerLink

namespace OwnerPath

variable {polynomial : CoefficientPolynomial}

/-- Reverse operations on the actual ordered original link occurrences, including stationary links. -/
@[expose] def Reversals : {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} → OwnerPath polynomial start left finish right → Type
  | _, _, _, _, .nil _ _ => PUnit
  | _, _, _, _, .cons link tail => OwnerLink.ReverseData link × Reversals tail

/-- Join the two GIVEN reverse-operation spines without rebuilding either original path or link. -/
def Reversals.append : {start middle finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {center : Owner (polynomial.eval middle)} → {right : Owner (polynomial.eval finish)} →
    (front : OwnerPath polynomial start left middle center) →
    (back : OwnerPath polynomial middle center finish right) →
    Reversals front → Reversals back → Reversals (front.append back)
  | _, _, _, _, _, _, .nil _ _, _, _, after => after
  | _, _, _, _, _, _, .cons _ tail, back, before, after =>
      ⟨before.1, Reversals.append tail back before.2 after⟩

/-- Reverse all original link occurrences and their exact Owner roles, retaining stationary links separately. -/
def reversePath : {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} → (path : OwnerPath polynomial start left finish right) →
    Reversals path → OwnerPath polynomial finish right start left
  | _, _, _, _, .nil point owner, _ => .nil point owner
  | start, _, left, _, .cons link tail, paid =>
      (reversePath tail paid.2).append (.cons (link.reverse paid.1) (.nil start left))

/-- The entire ordered base word reverses, preserving repeated and stationary occurrences. -/
theorem reversePath_vertices : {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} → (path : OwnerPath polynomial start left finish right) →
    (paid : Reversals path) → finish :: (reversePath path paid).vertices = (start :: path.vertices).reverse
  | _, _, _, _, .nil _ _, _ => rfl
  | start, finish, _, _, .cons (middle := middle) link tail, paid => by
      have after := reversePath_vertices tail paid.2
      change finish :: ((reversePath tail paid.2).append _).vertices = _
      rewrite [OwnerPath.append_vertices]
      change (finish :: (reversePath tail paid.2).vertices) ++ [start] = _
      exact (congrArg (fun values => values ++ [start]) after).trans
        (Reverse.reverse_cons start (middle :: tail.vertices)).symm

/-- An original reverse realization with literal supplied endpoint objects and the complete reversed root word. -/
@[expose] def ReverseResult {start finish : Canonical} {left : Owner (polynomial.eval start)}
    {right : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start left finish right)
    (paid : Reversals path) (first : OwnerReading left) (last : OwnerReading right)
    (roots : List Canonical) :=
  { result : Realization (reversePath path paid) last.index first.index //
    result.first = last ∧ result.last = first ∧
      last.value :: result.roots = (first.value :: roots).reverse }

/-- Reverse a nonempty original path on its GIVEN complete native reading spine and checked forward edges. -/
private def reverseCons : {start middle finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {center : Owner (polynomial.eval middle)} → {right : Owner (polynomial.eval finish)} →
    (link : OwnerLink polynomial start middle left center) →
    (tail : OwnerPath polynomial middle center finish right) →
    (paid : Reversals (.cons link tail)) → (first : OwnerReading left) → (last : OwnerReading right) →
    link.leftIndex ≤ first.index → targetMinimum (.cons link tail) ≤ last.index →
    (interiors : InteriorReadings (.cons link tail)) →
    Chain polynomial first.value (InteriorReadings.values (.cons link tail) interiors ++ [last.value])
      start (OwnerPath.cons link tail).vertices →
    ReverseResult (.cons link tail) paid first last
      (InteriorReadings.values (.cons link tail) interiors ++ [last.value])
  | start, middle, _, _left, _, _, link, .nil _ _, paid, first, last,
      firstLater, lastLater, _interiors, chain => by
      change Chain polynomial first.value [last.value] start [middle] at chain
      cases chain with
      | cons forward _tailChain =>
          let backward := paid.1 first last firstLater lastLater forward
          let result : Realization (reversePath (.cons link (.nil _ _)) paid) last.index first.index :=
            { first := last
              last := first
              first_ge := Nat.le_refl _
              last_ge := Nat.le_refl _
              roots := [first.value]
              chain := .cons backward.val (.nil first.value start)
              terminal_root := rfl }
          exact ⟨result, rfl, rfl, rfl⟩
  | start, middle, _, left, _, _, link, .cons following remaining, paid, first, last,
      firstLater, lastLater, interiors, chain => by
      change Chain polynomial first.value
        (interiors.1.val.value :: InteriorReadings.values (OwnerPath.cons following remaining) interiors.2 ++
          [last.value]) start (middle :: (OwnerPath.cons following remaining).vertices) at chain
      cases chain with
      | cons forward tailChain =>
          let next := interiors.1.val
          have incoming : link.rightIndex ≤ next.index :=
            (Data.Nat.Order.le_max_left _ _).trans_eq interiors.1.property.2.symm
          have outgoing : following.leftIndex ≤ next.index :=
            (Data.Nat.Order.le_max_right _ _).trans_eq interiors.1.property.2.symm
          let after := reverseCons following remaining paid.2 next last outgoing lastLater interiors.2 tailChain
          let backward := paid.1 first next firstLater incoming forward
          let reversed := reversePath (.cons following remaining) paid.2
          let final : Chain polynomial
              (Geometry.Rational.Polygon.Chain.terminal after.val.first.value after.val.roots) [first.value]
              (Geometry.Rational.Polygon.Chain.terminal _ reversed.vertices) [start] :=
            Eq.mpr (congrArg₂ (fun root base => Chain polynomial root [first.value] base [start])
              (after.val.terminal_root.trans (congrArg OwnerReading.value after.property.2.1))
              reversed.vertices_terminal) (.cons backward.val (.nil first.value start))
          let chained := Chain.append after.val.chain final
          let result : Realization (reversePath (.cons link (.cons following remaining)) paid)
              last.index first.index :=
            { first := last
              last := first
              first_ge := Nat.le_refl _
              last_ge := Nat.le_refl _
              roots := after.val.roots ++ [first.value]
              chain := Eq.mp (congrArg₂ (fun root bases =>
                  Chain polynomial root (after.val.roots ++ [first.value]) _ bases)
                (congrArg OwnerReading.value after.property.1)
                (OwnerPath.append_vertices reversed (.cons (link.reverse paid.1) (.nil start left))).symm) chained
              terminal_root := Geometry.Rational.Polygon.Chain.terminal_append_singleton _ _ _ }
          have rootWord : last.value :: result.roots =
              (first.value :: (next.value :: InteriorReadings.values (.cons following remaining) interiors.2 ++
                [last.value])).reverse :=
            (congrArg (fun roots => roots ++ [first.value]) after.property.2.2).trans
              (Reverse.reverse_cons first.value _).symm
          exact ⟨result, rfl, rfl, rootWord⟩
termination_by structural _ _ _ _ _ _ _ tail _ _ _ _ _ _ _ => tail

/-- Reverse the SAME supplied-endpoint realization, reusing every native reading and checked forward edge.

The actual reverse data comes from the original quantitative/link caches.
No Owner, tail, request, comparison or observation is acquired here.
The first and last reverse reading objects are the literal old last and
first objects; the complete original root word reverses in order.
-/
def reverseBetween : {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} → (path : OwnerPath polynomial start left finish right) →
    (nonempty : path.vertices ≠ []) → (paid : Reversals path) →
    (first : OwnerReading left) → (last : OwnerReading right) →
    (firstLater : sourceMinimum path ≤ first.index) → (lastLater : targetMinimum path ≤ last.index) →
    (observed : Between path first last) → ReverseResult path paid first last observed.realization.roots
  | _, _, _, _, .nil _ _, nonempty, _, _, _, _, _, _ => False.elim (nonempty rfl)
  | start, _, _, _, .cons link tail, _, paid, first, last, firstLater, lastLater, observed => by
      let roots := InteriorReadings.values (OwnerPath.cons link tail) observed.interiors ++ [last.value]
      let forward : Chain polynomial first.value roots start (OwnerPath.cons link tail).vertices :=
        Eq.mp (congrArg₂ (fun root values =>
          Chain polynomial root values start (OwnerPath.cons link tail).vertices)
          (congrArg OwnerReading.value observed.first_eq) observed.roots_eq) observed.realization.chain
      let result := reverseCons link tail paid first last firstLater lastLater observed.interiors forward
      exact Eq.mpr (congrArg (ReverseResult (OwnerPath.cons link tail) paid first last) observed.roots_eq) result

namespace ReverseResult

variable {start finish : Canonical} {left : Owner (polynomial.eval start)} {right : Owner (polynomial.eval finish)}
    {path : OwnerPath polynomial start left finish right} {paid : Reversals path}
    {first : OwnerReading left} {last : OwnerReading right} {roots : List Canonical}
    (cached : ReverseResult path paid first last roots)

/-- Read the SAME actual reverse realization without sampling. -/
@[expose] def realization : Realization (reversePath path paid) last.index first.index := cached.val

/-- The complete original last reading is the reverse trace's first reading. -/
theorem first_eq : cached.realization.first = last := cached.property.1

/-- The complete original first reading is the reverse trace's last reading. -/
theorem last_eq : cached.realization.last = first := cached.property.2.1

/-- Every original root occurrence reverses, including the separate stationary handoff reading. -/
theorem root_word : last.value :: cached.realization.roots = (first.value :: roots).reverse := cached.property.2.2

end ReverseResult

end OwnerPath

end Purelib.Riemann.Paths.OwnerTracePath

end
