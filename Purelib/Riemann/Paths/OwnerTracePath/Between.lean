module

meta import Purelib.Elab.ConstructiveInjectivity

public import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Data.Nat.Order
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Polygon.Chain
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.SquareRootTrace

/-! # Native root traces with two retained endpoint readings

Every nonempty original OwnerPath can consume two GIVEN complete endpoint
OwnerReadings after its actual endpoint link floors have been paid. Only
interior vertices are sampled. The constructor retains the original
links, tails, Owners and actual EdgeData realizations; independent readings
on a nil path are not identified.
-/

public section

namespace Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Riemann.Paths.OwnerTraceReadings
open Purelib.Riemann.RootContinuation.SquareRootTrace (Chain)

variable {polynomial : CoefficientPolynomial}

/-- The actual first-link native reading threshold, or zero for the original nil path. -/
@[expose] def sourceMinimum : {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} → OwnerPath polynomial start left finish right → Nat
  | _, _, _, _, .nil _ _ => 0
  | _, _, _, _, .cons link _ => link.leftIndex

/-- The actual last-link native reading threshold, retaining every original stationary link. -/
@[expose] def targetMinimum : {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} → OwnerPath polynomial start left finish right → Nat
  | _, _, _, _, .nil _ _ => 0
  | _, _, _, _, .cons link (.nil _ _) => link.rightIndex
  | _, _, _, _, .cons _ (.cons following remaining) => targetMinimum (.cons following remaining)
termination_by structural _ _ _ _ path => path

/-- The actual two endpoint requirements of one GIVEN path, cached with their original scalar factories. -/
@[expose] def ReadingFloors {start finish : Canonical} {left : Owner (polynomial.eval start)}
    {right : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start left finish right) :=
  (_source : { value : Nat // value = sourceMinimum path }) ×
    { target : Nat // target = targetMinimum path }

/-- Compute each original endpoint requirement once, before any reading or corner-maximum lookup. -/
def readingFloors {start finish : Canonical} {left : Owner (polynomial.eval start)}
    {right : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start left finish right) :
    ReadingFloors path :=
  let source := sourceMinimum path
  let target := targetMinimum path
  ⟨⟨source, rfl⟩, ⟨target, rfl⟩⟩

namespace ReadingFloors

variable {start finish : Canonical} {left : Owner (polynomial.eval start)}
    {right : Owner (polynomial.eval finish)} {path : OwnerPath polynomial start left finish right}
    (floors : ReadingFloors path)

/-- Read the SAME cached first-link requirement. -/
@[expose] def source : Nat := floors.1.val

/-- The cached source requirement is the original path's first-link floor. -/
theorem source_eq : floors.source = sourceMinimum path := floors.1.property

/-- Read the SAME cached last-link requirement. -/
@[expose] def target : Nat := floors.2.val

/-- The cached target requirement is the original path's final-link floor, including a stationary handoff. -/
theorem target_eq : floors.target = targetMinimum path := floors.2.property

end ReadingFloors

/-- The complete native interior reading objects indexed by the SAME literal original path.

Only a genuine interior vertex contributes an entry. Each stored entry is
an original OwnerReading at that path's actual middle Owner; no new point,
Owner or observation record is introduced.
-/
@[expose] def InteriorReadings : {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} → OwnerPath polynomial start left finish right → Type
  | _, _, _, _, .nil _ _ => PUnit
  | _, _, _, _, .cons _ (.nil _ _) => PUnit
  | _, _, _, _, .cons (center := center) link (.cons following remaining) =>
      { sample : OwnerReading center // sample.tail = following.leftTail ∧
        sample.index = Nat.max link.rightIndex following.leftIndex } × InteriorReadings (.cons following remaining)
termination_by structural _ _ _ _ path => path

namespace InteriorReadings

/-- The ordered original values of the SAME complete native interior reading objects. -/
@[expose] def values : {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} → (path : OwnerPath polynomial start left finish right) →
    InteriorReadings path → List Canonical
  | _, _, _, _, .nil _ _, _ => []
  | _, _, _, _, .cons _ (.nil _ _), _ => []
  | _, _, _, _, .cons _ (.cons following remaining), observed =>
      observed.1.val.value :: values (.cons following remaining) observed.2
termination_by structural _ _ _ _ path _ => path

end InteriorReadings

namespace Between

/-- The exact original realization and its coupled interior-root readback on the two GIVEN endpoint objects. -/
@[expose] def Execution {start finish : Canonical} {left : Owner (polynomial.eval start)}
    {right : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start left finish right)
    (first : OwnerReading left) (last : OwnerReading right) (interiors : InteriorReadings path) : Type :=
  { result : Realization path first.index last.index // result.first = first ∧ result.last = last ∧
    result.roots = InteriorReadings.values path interiors ++ [last.value] }

end Between

attribute [local irreducible] InteriorReadings Between.Execution in
set_option genInjectivity false in
/-- A retained original realization whose complete endpoint reading objects are the two supplied inputs.

The original interior reading spine and certified realization remain two
coupled caches. This nominal boundary preserves their exact types and
root-word relation while keeping client code emission from expanding the
recursive reading type.
-/
structure Between {start finish : Canonical} {left : Owner (polynomial.eval start)}
    {right : Owner (polynomial.eval finish)} (path : OwnerPath polynomial start left finish right)
    (first : OwnerReading left) (last : OwnerReading right) where
  /-- The complete original interior reading objects on this actual path. -/
  interiorCache : InteriorReadings path
  /-- The same certified original realization and its exact input/root readbacks. -/
  execution : Between.Execution path first last interiorCache

attribute [local irreducible] InteriorReadings Between.Execution in
constructive_injectivity Between

/-- Realize a nonempty original path on two GIVEN complete endpoint readings, sampling only genuine interior Owners.

At each interior vertex the maximum of the two incident retained link
thresholds is computed before one native reading. That SAME complete
reading is used in both original link tails. The terminal link consumes
the supplied last reading verbatim.
-/
private def betweenCons : {start middle finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {center : Owner (polynomial.eval middle)} → {right : Owner (polynomial.eval finish)} →
    (link : OwnerLink polynomial start middle left center) →
    (tail : OwnerPath polynomial middle center finish right) →
    (first : OwnerReading left) → (last : OwnerReading right) →
    link.leftIndex ≤ first.index → targetMinimum (.cons link tail) ≤ last.index →
      Between (.cons link tail) first last
  | _, middle, _, _, _, _, link, .nil _ _, first, last, firstLater, lastLater =>
      let leftReading := first.inTail link.leftTail (link.left_ge.trans firstLater)
      let rightReading := last.inTail link.rightTail (link.right_ge.trans lastLater)
      let edge := link.realize leftReading rightReading firstLater lastLater
      let result : Realization (.cons link (.nil middle _)) first.index last.index :=
        { first := first
          last := last
          first_ge := Nat.le_refl _
          last_ge := Nat.le_refl _
          roots := [last.value]
          chain := .cons edge (.nil last.value middle)
          terminal_root := rfl }
      ⟨PUnit.unit, ⟨result, rfl, rfl, rfl⟩⟩
  | _, middle, _, _, center, _, link, .cons following remaining, first, last, firstLater, lastLater =>
      let index := Nat.max link.rightIndex following.leftIndex
      have incoming : link.rightIndex ≤ index := Data.Nat.Order.le_max_left _ _
      have outgoing : following.leftIndex ≤ index := Data.Nat.Order.le_max_right _ _
      let reading := OwnerTail.Reading.acquire following.leftTail index (following.left_ge.trans outgoing)
      let next : OwnerReading center := ⟨following.leftTail, reading⟩
      let after := betweenCons following remaining next last outgoing lastLater
      let leftReading := first.inTail link.leftTail (link.left_ge.trans firstLater)
      let rightReading := next.inTail link.rightTail (link.right_ge.trans incoming)
      let edge := link.realize leftReading rightReading firstLater incoming
      have firstValue : after.execution.val.first.value = next.value :=
        congrArg OwnerReading.value after.execution.property.1
      let tailChain : Chain polynomial next.value after.execution.val.roots middle
          (OwnerPath.cons following remaining).vertices :=
        Eq.mp (congrArg (fun root => Chain polynomial root after.execution.val.roots middle
          (OwnerPath.cons following remaining).vertices) firstValue) after.execution.val.chain
      let result : Realization (.cons link (.cons following remaining)) first.index last.index :=
        { first := first
          last := last
          first_ge := Nat.le_refl _
          last_ge := Nat.le_refl _
          roots := next.value :: after.execution.val.roots
          chain := .cons edge tailChain
          terminal_root := (congrArg (fun root =>
            Geometry.Rational.Polygon.Chain.terminal root after.execution.val.roots) firstValue.symm).trans
              (after.execution.val.terminal_root.trans (congrArg OwnerReading.value after.execution.property.2.1)) }
      ⟨⟨⟨next, rfl, rfl⟩, after.interiorCache⟩,
        ⟨result, rfl, rfl, congrArg (List.cons next.value) after.execution.property.2.2⟩⟩
termination_by structural _ _ _ _ _ _ _ tail _ _ _ _ => tail

/-- Consume the SAME actual nonempty path and two supplied endpoint readings after its actual native floors.

The original nil constructor is excluded by this same path's nonempty
vertex certificate. No equality of independent readings, no root source
reconstruction and no endpoint observation occurs in this operation.
-/
def between : {start finish : Canonical} → {left : Owner (polynomial.eval start)} →
    {right : Owner (polynomial.eval finish)} → (path : OwnerPath polynomial start left finish right) →
    (nonempty : path.vertices ≠ []) → (first : OwnerReading left) → (last : OwnerReading right) →
    (firstLater : sourceMinimum path ≤ first.index) → (lastLater : targetMinimum path ≤ last.index) →
      Between path first last
  | _, _, _, _, .nil _ _, nonempty, _, _, _, _ => False.elim (nonempty rfl)
  | _, _, _, _, .cons link tail, _, first, last, firstLater, lastLater =>
      betweenCons link tail first last firstLater lastLater

namespace Between

variable {start finish : Canonical} {left : Owner (polynomial.eval start)}
    {right : Owner (polynomial.eval finish)} {path : OwnerPath polynomial start left finish right}
    {first : OwnerReading left} {last : OwnerReading right} (cached : Between path first last)

/-- Read the SAME complete native interior reading spine, including its actual indices and tail states. -/
@[expose] def interiors : InteriorReadings path := cached.interiorCache

/-- Read the SAME original realized trace built from the given endpoints and these actual interiors. -/
@[expose] def realization : Realization path first.index last.index := cached.execution.val

/-- The actual complete original first endpoint reading is the supplied object. -/
theorem first_eq : cached.realization.first = first := cached.execution.property.1

/-- The actual complete original last endpoint reading is the supplied object. -/
theorem last_eq : cached.realization.last = last := cached.execution.property.2.1

/-- The actual trace root list is exactly these SAME interior values followed by the supplied terminal value. -/
theorem roots_eq : cached.realization.roots = InteriorReadings.values path cached.interiors ++ [last.value] :=
  cached.execution.property.2.2

end Between

end Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

end
