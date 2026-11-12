module

import Purelib.Data.List.Membership
import Purelib.Data.List.Map
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Compile
public import Purelib.Approximation.Gaussian.Acquisition.Expression.Bindings
public import Purelib.Approximation.Gaussian.Provenance.Algebraic
public import Purelib.Polynomial.Multivariate.Gaussian.Division
import Purelib.Polynomial.Multivariate.Gaussian.Denotation
public import Purelib.Polynomial.Multivariate.Gaussian.Algebraic
public import Purelib.Polynomial.Multivariate.Gaussian.Inverse
public import Purelib.Computation.Query.History
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Arithmetic
import Purelib.Data.List.DependentProduct
import Purelib.Polynomial.Multivariate.PowerReduction
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Gaussian.Arithmetic.Neg
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Algebraic admissions at actual retained total-expression bindings

Tables refer to the original compiled binding records and bounded positions.
Each root admission retains its original mathematical owner and channel link;
reading the table never calls the original root producer again.
-/

public section
namespace Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Base

open Purelib.Data.List.Membership (mem_append)
open Purelib.Data.List.Map (mem_map)

open Purelib.Approximation.Gaussian.Acquisition (Annotated)
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Provenance
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Polynomial.Multivariate
open Purelib.Polynomial.Approximation.Gaussian (Residual)
open Purelib.Data.List (DependentProduct)
open Purelib.Computation
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Coefficient

variable {arity : Nat} {environment : Fin arity → Annotated}

/-- One stored optional algebraic admission at each original binding occurrence and actual channel index.

The default channel function is the original annotation readback. A supplied
interpretation can retain genuine conjugated channels without changing the
original binding records or identifying independently supplied sidecars.
-/
@[expose] def Slots (bindings : List (Basic.Binding environment))
    (channels : Fin bindings.length → CoherentNamed := Basic.Binding.channels bindings) : Type 1 :=
  DependentProduct bindings (fun index => Option (Algebraic.Sidecar (channels index)))

/-- A complete executable admission table over the exact original binding spine. -/
@[expose] def Admissions (bindings : List (Basic.Binding environment)) : Type 1 :=
  DependentProduct bindings (fun index => Algebraic.Sidecar (Basic.Binding.read bindings index).annotation.channel)

namespace Slots

/-- Read the same cached optional admission at its original bounded table position. -/
@[expose] def get (bindings : List (Basic.Binding environment)) (slots : Slots bindings)
    (index : Fin bindings.length) : Option (Algebraic.Sidecar (Basic.Binding.read bindings index).annotation.channel) :=
  DependentProduct.get bindings slots index

/-- Append the same two original slot caches over their literal binding concatenation.

The original dependent-product operation retains every stored optional sidecar
and the complete supplied right tail. No annotation or admission is rebuilt. -/
@[expose] def append (first second : List (Basic.Binding environment))
    (left : Slots first) (right : Slots second) : Slots (first ++ second) :=
  let family := fun binding : Basic.Binding environment => Option (Algebraic.Sidecar binding.annotation.channel)
  let actual := DependentProduct.append family first second (Basic.Binding.read first) (Basic.Binding.read second)
    left right
  DependentProduct.transport (first ++ second)
    (fun index => congrArg family (Basic.Binding.read_appendFn first second index)) actual

/-- An empty left slot table returns the identical supplied right cache. -/
theorem append_nil (second : List (Basic.Binding environment))
    (left : Slots (environment := environment) []) (right : Slots second) :
    append [] second left right = right := rfl

/-- A nonempty slot append retains the literal original head and recursively attached actual tail. -/
theorem append_cons (first : Basic.Binding environment) (remaining second : List (Basic.Binding environment))
    (left : Slots (first :: remaining)) (right : Slots second) :
    append (first :: remaining) second left right = (left.1, append remaining second left.2 right) := by
  unfold append
  change DependentProduct.transport (first :: (remaining ++ second)) _ _ = _
  rewrite [DependentProduct.transport_cons]
  rfl

/-- Appended left lookup retains its entire original optional sidecar under the exact original channel equality. -/
theorem get_append_left (first second : List (Basic.Binding environment))
    (left : Slots first) (right : Slots second) (index : Fin first.length) :
    get (first ++ second) (append first second left right) (DependentProduct.leftIndex first second index) =
      cast (congrArg (fun channel : CoherentNamed => Option (Algebraic.Sidecar channel))
        (Basic.Binding.channels_append_left first second index).symm) (get first left index) := by
  let family := fun binding : Basic.Binding environment => Option (Algebraic.Sidecar binding.annotation.channel)
  let actual := DependentProduct.append family first second (Basic.Binding.read first) (Basic.Binding.read second)
    left right
  have transported := DependentProduct.get_transport (first ++ second)
    (fun index => congrArg family (Basic.Binding.read_appendFn first second index)) actual
    (DependentProduct.leftIndex first second index)
  have original := DependentProduct.get_append_left family first second
    (Basic.Binding.read first) (Basic.Binding.read second) left right index
  exact eq_of_heq ((transported.trans original).trans (cast_heq _ (get first left index)).symm)

/-- Appended right lookup retains its entire original optional sidecar under the exact original channel equality. -/
theorem get_append_right (first second : List (Basic.Binding environment))
    (left : Slots first) (right : Slots second) (index : Fin second.length) :
    get (first ++ second) (append first second left right) (DependentProduct.rightIndex first second index) =
      cast (congrArg (fun channel : CoherentNamed => Option (Algebraic.Sidecar channel))
        (Basic.Binding.channels_append_right first second index).symm) (get second right index) := by
  let family := fun binding : Basic.Binding environment => Option (Algebraic.Sidecar binding.annotation.channel)
  let actual := DependentProduct.append family first second (Basic.Binding.read first) (Basic.Binding.read second)
    left right
  have transported := DependentProduct.get_transport (first ++ second)
    (fun index => congrArg family (Basic.Binding.read_appendFn first second index)) actual
    (DependentProduct.rightIndex first second index)
  have original := DependentProduct.get_append_right family first second
    (Basic.Binding.read first) (Basic.Binding.read second) left right index
  exact eq_of_heq ((transported.trans original).trans (cast_heq _ (get second right index)).symm)

/-- Transport the same whole original slot product through pointwise identities of its actual channel indices. -/
@[expose] def transport (bindings : List (Basic.Binding environment))
    {first second : Fin bindings.length → CoherentNamed} (same : ∀ index, first index = second index)
    (slots : Slots bindings first) : Slots bindings second :=
  DependentProduct.transport bindings (fun index => congrArg (fun channel => Option (Algebraic.Sidecar channel))
    (same index)) slots

/-- Conjugate each supplied actual sidecar once at its actual conjugated channel, retaining the original binding spine.

The target channel bank is supplied outside entry construction. Its pointwise
construction equations transport each original Sidecar.conj to the literal
cached target channel; the old sidecar remains its actual conjugation parent.
-/
@[expose] def conj : (bindings : List (Basic.Binding environment)) →
    {first second : Fin bindings.length → CoherentNamed} →
    (∀ index, second index = CoherentNamed.conj (first index)) → Slots bindings first → Slots bindings second
  | [], _, _, _, _ => PUnit.unit
  | _head :: remaining, _first, _second, same, slots =>
      (match slots.1 with
       | none => none
       | some original => some ((same 0).symm ▸ original.conj),
       conj remaining (fun index => same index.succ) slots.2)
termination_by structural bindings _ _ _ _ => bindings

/-- Interpreted slot transport reads the same complete original entry under its exact channel type transport. -/
theorem get_transport (bindings : List (Basic.Binding environment))
    {first second : Fin bindings.length → CoherentNamed} (same : ∀ index, first index = second index)
    (slots : Slots bindings first) (index : Fin bindings.length) :
    HEq (DependentProduct.get bindings (transport bindings same slots) index)
      (DependentProduct.get bindings slots index) :=
  DependentProduct.get_transport bindings _ slots index

/-- Conjugated slot lookup is exactly the original supplied sidecar's conjugation at the retained target channel. -/
theorem get_conj : (bindings : List (Basic.Binding environment)) →
    {first second : Fin bindings.length → CoherentNamed} →
    (same : ∀ index, second index = CoherentNamed.conj (first index)) → (slots : Slots bindings first) →
    (index : Fin bindings.length) →
    DependentProduct.get bindings (conj bindings same slots) index =
      match DependentProduct.get bindings slots index with
      | none => none
      | some original => some ((same index).symm ▸ original.conj)
  | [], _, _, _, _, index => Fin.elim0 index
  | _head :: remaining, _, _, same, slots, index => by
      cases slots with
      | mk entry remainingSlots =>
          unfold conj DependentProduct.get
          refine Fin.cases ?_ ?_ index
          · rewrite [_root_.Fin.cases_zero, _root_.Fin.cases_zero]
            cases entry <;> rfl
          · intro tail
            rewrite [_root_.Fin.cases_succ, _root_.Fin.cases_succ]
            have agreement := get_conj remaining (fun index => same index.succ) remainingSlots tail
            cases selected : DependentProduct.get remaining remainingSlots tail with
            | none =>
                rewrite [selected] at agreement
                exact agreement
            | some original =>
                rewrite [selected] at agreement
                exact agreement

/-- Replace one original slot with supplied intrinsic data at that exact original channel. -/
@[expose] def supply (bindings : List (Basic.Binding environment)) (slots : Slots bindings)
    (index : Fin bindings.length)
    (evidence : Algebraic.Sidecar (Basic.Binding.read bindings index).annotation.channel) : Slots bindings :=
  DependentProduct.replace bindings slots index (some evidence)

/-- Retain every absent required original position, preserving the original bounded occurrence order. -/
@[expose] def missing : (bindings : List (Basic.Binding environment)) → Slots bindings →
    (required : Fin bindings.length → Bool) → List (Fin bindings.length)
  | [], _, _ => []
  | _first :: remaining, slots, required =>
      let later := (missing remaining slots.2 (fun index => required index.succ)).map Fin.succ
      match slots.1 with
      | some _ => later
      | none => if required 0 then ⟨0, Nat.zero_lt_succ remaining.length⟩ :: later else later

/-- Every required original bounded position has retained same-channel intrinsic evidence. -/
@[expose] def Ready (bindings : List (Basic.Binding environment)) (slots : Slots bindings)
    (required : Fin bindings.length → Bool) : Prop :=
  ∀ index, required index = true → (get bindings slots index).isSome = true

end Slots

namespace Admissions

/-- Read the same original admitted sidecar at its retained bounded occurrence. -/
@[expose] def get (bindings : List (Basic.Binding environment)) (admissions : Admissions bindings)
    (index : Fin bindings.length) : Algebraic.Sidecar (Basic.Binding.read bindings index).annotation.channel :=
  DependentProduct.get bindings admissions index

/-- Append both complete original admission caches without equating or rebuilding their retained sidecars. -/
@[expose] def append (first second : List (Basic.Binding environment))
    (left : Admissions first) (right : Admissions second) : Admissions (first ++ second) :=
  let family := fun binding : Basic.Binding environment => Algebraic.Sidecar binding.annotation.channel
  let actual := DependentProduct.append family first second (Basic.Binding.read first) (Basic.Binding.read second)
    left right
  DependentProduct.transport (first ++ second)
    (fun index => congrArg family (Basic.Binding.read_appendFn first second index)) actual

/-- An empty left admission table returns the same supplied right parent cache. -/
theorem append_nil (second : List (Basic.Binding environment))
    (left : Admissions (environment := environment) []) (right : Admissions second) :
    append [] second left right = right := rfl

/-- A nonempty admission append retains the literal original head and supplied recursive tail. -/
theorem append_cons (first : Basic.Binding environment) (remaining second : List (Basic.Binding environment))
    (left : Admissions (first :: remaining)) (right : Admissions second) :
    append (first :: remaining) second left right = (left.1, append remaining second left.2 right) := by
  unfold append
  change DependentProduct.transport (first :: (remaining ++ second)) _ _ = _
  rewrite [DependentProduct.transport_cons]
  rfl

/-- Appended left lookup retains the whole original admission under its exact original channel equality. -/
theorem get_append_left (first second : List (Basic.Binding environment))
    (left : Admissions first) (right : Admissions second) (index : Fin first.length) :
    get (first ++ second) (append first second left right) (DependentProduct.leftIndex first second index) =
      cast (congrArg (fun channel : CoherentNamed => Algebraic.Sidecar channel)
        (Basic.Binding.channels_append_left first second index).symm) (get first left index) := by
  let family := fun binding : Basic.Binding environment => Algebraic.Sidecar binding.annotation.channel
  let actual := DependentProduct.append family first second (Basic.Binding.read first) (Basic.Binding.read second)
    left right
  have transported := DependentProduct.get_transport (first ++ second)
    (fun index => congrArg family (Basic.Binding.read_appendFn first second index)) actual
    (DependentProduct.leftIndex first second index)
  have original := DependentProduct.get_append_left family first second
    (Basic.Binding.read first) (Basic.Binding.read second) left right index
  exact eq_of_heq ((transported.trans original).trans (cast_heq _ (get first left index)).symm)

/-- Appended right lookup retains the whole original admission under its exact original channel equality. -/
theorem get_append_right (first second : List (Basic.Binding environment))
    (left : Admissions first) (right : Admissions second) (index : Fin second.length) :
    get (first ++ second) (append first second left right) (DependentProduct.rightIndex first second index) =
      cast (congrArg (fun channel : CoherentNamed => Algebraic.Sidecar channel)
        (Basic.Binding.channels_append_right first second index).symm) (get second right index) := by
  let family := fun binding : Basic.Binding environment => Algebraic.Sidecar binding.annotation.channel
  let actual := DependentProduct.append family first second (Basic.Binding.read first) (Basic.Binding.read second)
    left right
  have transported := DependentProduct.get_transport (first ++ second)
    (fun index => congrArg family (Basic.Binding.read_appendFn first second index)) actual
    (DependentProduct.rightIndex first second index)
  have original := DependentProduct.get_append_right family first second
    (Basic.Binding.read first) (Basic.Binding.read second) left right index
  exact eq_of_heq ((transported.trans original).trans (cast_heq _ (get second right index)).symm)

/-- Retain a complete table as the same optional slots, without recomputing any original admission. -/
@[expose] def slots : (bindings : List (Basic.Binding environment)) → Admissions bindings → Slots bindings
  | [], _ => PUnit.unit
  | _first :: remaining, admissions => (some admissions.1, slots remaining admissions.2)

/-- Optional readback of appended admissions preserves both complete original slot caches.

The original `some` wrappers retain their actual sidecars. Structural recursion
shares the same original head and the literal supplied right admission tail. -/
theorem slots_append : (first second : List (Basic.Binding environment)) →
    (left : Admissions first) → (right : Admissions second) →
    slots (first ++ second) (append first second left right) =
      Slots.append first second (slots first left) (slots second right)
  | [], _, _, _ => rfl
  | first :: remaining, second, left, right => by
      rewrite [append_cons, Slots.append_cons]
      exact congrArg (fun tail => (some left.1, tail)) (slots_append remaining second left.2 right)

/-- Optional admission readback retains the same complete original sidecar at every bounded occurrence. -/
theorem get_slots : (bindings : List (Basic.Binding environment)) →
    (admissions : Admissions bindings) → (index : Fin bindings.length) →
      Slots.get bindings (slots bindings admissions) index = some (get bindings admissions index)
  | [], _, index => Fin.elim0 index
  | _first :: remaining, admissions, index => by
      cases admissions with
      | mk entry remainingAdmissions =>
          unfold Slots.get get slots DependentProduct.get
          refine Fin.cases ?_ ?_ index
          · rewrite [_root_.Fin.cases_zero, _root_.Fin.cases_zero]
            rfl
          · intro tail
            rewrite [_root_.Fin.cases_succ, _root_.Fin.cases_succ]
            exact get_slots remaining remainingAdmissions tail

/-- Store supplied intrinsic data over the exact finite original bounded table, without calling a leaf producer. -/
@[expose] def ofFunction (bindings : List (Basic.Binding environment))
    (evidence : (index : Fin bindings.length) →
      Algebraic.Sidecar (Basic.Binding.read bindings index).annotation.channel) : Admissions bindings :=
  DependentProduct.ofFn bindings evidence

/-- Reading materialized admissions returns the exact supplied certificate at its original bounded occurrence. -/
theorem get_ofFunction (bindings : List (Basic.Binding environment))
    (evidence : (index : Fin bindings.length) →
      Algebraic.Sidecar (Basic.Binding.read bindings index).annotation.channel) (index : Fin bindings.length) :
    get bindings (ofFunction bindings evidence) index = evidence index :=
  DependentProduct.get_ofFn bindings evidence index

end Admissions

set_option genInjectivity false in
/-- The exact first absent required original slot, retaining the unchanged source index and relevant prefix. -/
structure Missing (bindings : List (Basic.Binding environment)) (slots : Slots bindings)
    (required : Fin bindings.length → Bool) where
  /-- The first unresolved required original bounded table position. -/
  index : Fin bindings.length
  /-- This same variable remains in the actual current coefficient support. -/
  needed : required index = true
  /-- This exact original slot has no retained algebraic admission. -/
  absent : Slots.get bindings slots index = none
  /-- Every earlier required original occurrence already has its intrinsic admission. -/
  before : ∀ earlier : Fin bindings.length, earlier.val < index.val → required earlier = true →
    (Slots.get bindings slots earlier).isSome = true

constructive_injectivity Missing

/-- Check only the currently required original slots, retaining their exact first missing occurrence. -/
@[expose] def checkSlots : (bindings : List (Basic.Binding environment)) → (slots : Slots bindings) →
    (required : Fin bindings.length → Bool) →
    Except (Missing bindings slots required) (PLift (Slots.Ready bindings slots required))
  | [], _, _ => .ok ⟨fun index => Fin.elim0 index⟩
  | _first :: remaining, slots, required =>
      match selected : slots.1 with
      | some _ => match checkSlots remaining slots.2 (fun index => required index.succ) with
        | .ok ready => .ok ⟨by
            intro index
            refine Fin.cases ?_ ?_ index
            · intro _; change slots.1.isSome = true; rewrite [selected]; rfl
            · intro tail needed; exact ready.down tail needed⟩
        | .error missing => .error ⟨missing.index.succ, missing.needed, missing.absent, by
            intro earlier
            refine Fin.cases ?_ ?_ earlier
            · intro _ _; change slots.1.isSome = true; rewrite [selected]; rfl
            · intro tail order needed
              exact missing.before tail (Nat.lt_of_succ_lt_succ order) needed⟩
      | none => if needed : required 0 = true then
          .error ⟨⟨0, Nat.zero_lt_succ remaining.length⟩, needed, selected,
            fun _ order _ => False.elim (Nat.not_lt_zero _ order)⟩
        else match checkSlots remaining slots.2 (fun index => required index.succ) with
          | .ok ready => .ok ⟨by
              intro index
              refine Fin.cases ?_ ?_ index
              · intro used; exact False.elim (needed used)
              · intro tail used; exact ready.down tail used⟩
          | .error missing => .error ⟨missing.index.succ, missing.needed, missing.absent, by
              intro earlier
              refine Fin.cases ?_ ?_ earlier
              · intro _ used; exact False.elim (needed used)
              · intro tail order used
                exact missing.before tail (Nat.lt_of_succ_lt_succ order) used⟩

/-- Read existing generic evidence, preserving scalar coordinate and zero-root fast paths when available. -/
@[expose] def fromAnnotation (annotation : Annotated) : Option (Algebraic.Sidecar annotation.channel) :=
  match annotation.provenance with
  | none => none
  | some provenance => match provenance.algebraic? with
    | some sidecar => some sidecar
    | none => provenance.rationalReading.map Algebraic.Sidecar.ofRational

/-- Materialize one admission view from each actual stored original annotation. -/
@[expose] def materialize : (bindings : List (Basic.Binding environment)) → Slots bindings
  | [] => PUnit.unit
  | first :: remaining => (fromAnnotation first.annotation, materialize remaining)

/-- Reuse an actual original output sidecar before constructing a missing fallback certificate. -/
@[expose] def withExisting (annotation : Annotated)
    (fallback : Unit → Algebraic.Sidecar annotation.channel) : Algebraic.Sidecar annotation.channel :=
  match fromAnnotation annotation with
  | some retained => retained
  | none => fallback ()

/-- Read an actual admitted original leaf using the compiler's original occurrence lookup and channel identity. -/
@[expose] def leaf (bindings : List (Basic.Binding environment)) (admissions : Admissions bindings)
    (key : Basic.Leaf arity) (annotation : Annotated)
    (source : annotation = key.annotation environment) (present : Basic.Binding.Present key bindings) :
    Algebraic.Sidecar annotation.channel :=
  let position := Basic.Binding.locate key bindings present
  let retained := Admissions.get bindings admissions position.val
  have same : (Basic.Binding.read bindings position.val).annotation = annotation :=
    (Basic.Binding.Lookup.annotation_eq position.val position.property).trans source.symm
  (congrArg Annotated.channel same) ▸ retained

/-- Construct general algebraic evidence through the actual original total-expression construction.

Existing output evidence is reused first. Missing arithmetic evidence consumes
these same admitted leaf caches and the original retained child annotations.
-/
@[expose] def construction (bindings : List (Basic.Binding environment)) (admissions : Admissions bindings) :
    {expression : Basic.Expr arity} → (annotation : Annotated) →
    (built : Basic.Construction environment expression annotation) → built.Supported bindings →
      Algebraic.Sidecar annotation.channel
  | _, annotation, .atom index _ source, present => leaf bindings admissions (.atom index) annotation source present
  | _, _annotation, .rational value _ source, _ =>
      (congrArg Annotated.channel source).symm ▸ Algebraic.Sidecar.ofRational (RationalSidecar.exact value)
  | _, annotation, .root parameter sheet _ source, present =>
      leaf bindings admissions (.root parameter sheet) annotation source present
  | _, annotation, .neg child built source, supported => withExisting annotation fun _ =>
      let retained := construction bindings admissions child built supported
      (congrArg Annotated.channel source).symm ▸ retained.neg
  | _, annotation, .add _ first second builtFirst builtSecond _ source, supported => withExisting annotation fun _ =>
      let left := construction bindings admissions first builtFirst supported.1
      let right := construction bindings admissions second builtSecond supported.2
      (congrArg Annotated.channel source).symm ▸ left.add right
  | _, annotation, .addNeg child _ source, _ => withExisting annotation fun _ =>
      let zero := RationalSidecar.zero
        (channel := CoherentNamed.add child.channel (CoherentNamed.neg child.channel))
        (Purelib.Approximation.Gaussian.Arithmetic.Neg.coherentAdd_neg_right child.channel)
      (congrArg Annotated.channel source).symm ▸ Algebraic.Sidecar.ofRational zero
  | _, annotation, .sub _ first second builtFirst builtSecond _ source, supported => withExisting annotation fun _ =>
      let left := construction bindings admissions first builtFirst supported.1
      let right := construction bindings admissions second builtSecond supported.2
      (congrArg Annotated.channel source).symm ▸ left.sub right
  | _, annotation, .subSelf child _ source, _ => withExisting annotation fun _ =>
      let zero := RationalSidecar.zero
        (channel := CoherentNamed.add child.channel (CoherentNamed.neg child.channel))
        (Purelib.Approximation.Gaussian.Arithmetic.Neg.coherentAdd_neg_right child.channel)
      (congrArg Annotated.channel source).symm ▸ Algebraic.Sidecar.ofRational zero
  | _, annotation, .mul _ first second builtFirst builtSecond _ source, supported => withExisting annotation fun _ =>
      let left := construction bindings admissions first builtFirst supported.1
      let right := construction bindings admissions second builtSecond supported.2
      (congrArg Annotated.channel source).symm ▸ left.mul right
  | _, annotation, .square child built _ source, supported => withExisting annotation fun _ =>
      let retained := construction bindings admissions child built supported
      (congrArg Annotated.channel source).symm ▸ retained.mul retained

set_option genInjectivity false in
/-- The once inspected pure-power form of an actual original admitted sidecar. -/
structure PowerInspection {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel) where
  /-- The actual recognized original-channel equation or typed coefficient mismatch. -/
  form : Residual.PowerForm sidecar.residual
  /-- This form was inspected from this same retained original residual. -/
  form_eq : form = sidecar.residual.inspectPower

constructive_injectivity PowerInspection

/-- Actual original sidecars and their once inspected equations at partial bounded binding positions. -/
@[expose] def Powers (bindings : List (Basic.Binding environment)) : Type 1 :=
  DependentProduct bindings (fun index =>
    Option (Sigma fun sidecar : Algebraic.Sidecar (Basic.Binding.read bindings index).annotation.channel =>
      PowerInspection sidecar))

namespace PowerInspection

/-- Inspect the same retained original residual once. -/
@[expose] def prepare {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel) : PowerInspection sidecar :=
  ⟨sidecar.residual.inspectPower, rfl⟩

end PowerInspection

namespace Powers

/-- Materialize equation inspections only where the actual original slots already retain evidence. -/
@[expose] def prepare : (bindings : List (Basic.Binding environment)) → Slots bindings → Powers bindings
  | [], _ => PUnit.unit
  | _first :: remaining, slots =>
      (slots.1.map (fun sidecar => ⟨sidecar, PowerInspection.prepare sidecar⟩), prepare remaining slots.2)

/-- Read one literal retained original sidecar and its original-channel equation inspection. -/
@[expose] def get (bindings : List (Basic.Binding environment)) (powers : Powers bindings)
    (index : Fin bindings.length) :
    Option (Sigma fun sidecar : Algebraic.Sidecar (Basic.Binding.read bindings index).annotation.channel =>
      PowerInspection sidecar) := DependentProduct.get bindings powers index

/-- Forget only inspections, retaining the exact original sidecar at every original slot. -/
@[expose] def slots : (bindings : List (Basic.Binding environment)) → Powers bindings → Slots bindings
  | [], _ => PUnit.unit
  | _first :: remaining, powers => (powers.1.map Sigma.fst, slots remaining powers.2)

/-- Inspection materialization retains the complete original slot table. -/
theorem prepare_slots : (bindings : List (Basic.Binding environment)) → (supplied : Slots bindings) →
    slots bindings (prepare bindings supplied) = supplied
  | [], _ => rfl
  | _first :: remaining, supplied => by
      rcases supplied with ⟨entry, tail⟩
      cases entry with
      | none => exact congrArg (fun later => (none, later)) (prepare_slots remaining tail)
      | some sidecar => exact congrArg (fun later => (some sidecar, later)) (prepare_slots remaining tail)

/-- Replace one bounded inspection, reusing every other original sidecar, inspection and retained product tail. -/
@[expose] def supply (bindings : List (Basic.Binding environment)) (powers : Powers bindings)
    (index : Fin bindings.length)
    (sidecar : Algebraic.Sidecar (Basic.Binding.read bindings index).annotation.channel)
    (inspection : PowerInspection sidecar) : Powers bindings :=
  DependentProduct.replace bindings powers index (some ⟨sidecar, inspection⟩)

/-- Supplying one equation changes exactly the same original optional slot as supplying its sidecar. -/
theorem supply_slots : (bindings : List (Basic.Binding environment)) → (powers : Powers bindings) →
    (index : Fin bindings.length) →
    (sidecar : Algebraic.Sidecar (Basic.Binding.read bindings index).annotation.channel) →
    (inspection : PowerInspection sidecar) →
    slots bindings (supply bindings powers index sidecar inspection) =
      Slots.supply bindings (slots bindings powers) index sidecar
  | [], _, index, _, _ => Fin.elim0 index
  | _first :: remaining, powers, index, sidecar, inspection => by
      revert sidecar inspection
      refine Fin.cases (fun _ _ => rfl) ?_ index
      intro tail sidecar inspection
      exact congrArg (fun later => (powers.1.map Sigma.fst, later))
        (supply_slots remaining powers.2 tail sidecar inspection)

end Powers

set_option genInjectivity false in
/-- One retained normalization and its once computed inferred annotation on the exact same original compilation. -/
structure Normalization {expression : Basic.Expr arity} (compiled : Basic.Compiled environment expression) where
  /-- The actual original polynomial normalization and cached leaf inspections. -/
  value : Basic.Normalized environment expression
  /-- This normalization retains the same original compilation, including root and child caches. -/
  compiled_eq : value.compiled = compiled
  /-- The retained variables are the exact original compiled bounded binding table. -/
  bindings_eq : value.bindings = compiled.bindings
  /-- The actual once computed original-channel annotation after retained power reduction and inference. -/
  annotation : Annotated
  /-- The annotation was computed from this same retained normalization. -/
  annotation_eq : annotation = value.infer

constructive_injectivity Normalization

/-- The stored normalized inference preserves the exact original output numerical channel. -/
theorem Normalization.channel_eq {expression : Basic.Expr arity} {compiled : Basic.Compiled environment expression}
    (retained : Normalization compiled) : retained.annotation.channel = compiled.annotation.channel :=
  (congrArg Annotated.channel retained.annotation_eq).trans
    (retained.value.infer_channel.trans (congrArg (fun output => output.annotation.channel) retained.compiled_eq))

/-- Read the retained normalization on its exact original compiled channel and bounded variable table. -/
@[expose] def Normalization.polynomial {expression : Basic.Expr arity}
    {compiled : Basic.Compiled environment expression} (retained : Normalization compiled) :
    Gaussian.Normalized (Basic.Binding.channels compiled.bindings) compiled.annotation.channel :=
  let original := retained.value.polynomial.transport
    (congrArg (fun output => output.annotation.channel) retained.compiled_eq)
  Eq.mp (congrArg (fun bindings => Gaussian.Normalized (Basic.Binding.channels bindings)
    compiled.annotation.channel) retained.bindings_eq) original

/-- The retained original pure-power coefficient form or the completed general basis division.

Both branches consume the same original predecessor and equation inspection.
The recognized branch stores its exact sparse form and computation equality;
exponent selection and output construction consume that same value.
-/
@[expose] def PowerInspection.Coefficients {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel)
    (inspection : PowerInspection sidecar) {size : Nat} {bindings : Fin size → CoherentNamed}
    {original : CoherentNamed} (input : Gaussian.Normalized bindings original) (index : Fin size) : Type :=
  match inspection.form with
  | .recognized _ _ => {form : Sparse Coefficient size //
      form = input.form.reduceAt index sidecar.polynomial.natDegree (-sidecar.polynomial.eval 0)}
  | .other _ => Sparse.DivisionAt input.form index sidecar.polynomial

/-- Compute the original pure-power form or each required basis division once and retain the complete result. -/
@[expose] def PowerInspection.divide {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel)
    (inspection : PowerInspection sidecar) {size : Nat} {bindings : Fin size → CoherentNamed}
    {original : CoherentNamed} (input : Gaussian.Normalized bindings original) (index : Fin size) :
    PowerInspection.Coefficients sidecar inspection input index := by
  unfold Coefficients
  cases inspection.form with
  | recognized _ _ =>
      exact ⟨input.form.reduceAt index sidecar.polynomial.natDegree (-sidecar.polynomial.eval 0), rfl⟩
  | other _ => exact Sparse.DivisionAt.prepare input.form index sidecar.polynomial

/-- Read the actual selected-coordinate remainder form supplied by this same equation inspection and division cache. -/
@[expose] def PowerInspection.reducedForm {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel)
    (inspection : PowerInspection sidecar) {size : Nat} {bindings : Fin size → CoherentNamed}
    {original : CoherentNamed} (input : Gaussian.Normalized bindings original) (index : Fin size)
    (coefficients : PowerInspection.Coefficients sidecar inspection input index) : Sparse Coefficient size := by
  unfold Coefficients at coefficients
  cases selected : inspection.form with
  | recognized _ _ =>
      rewrite [selected] at coefficients
      exact coefficients.val
  | other _ =>
      rewrite [selected] at coefficients
      exact coefficients.remainder

/-- The exact selected-coordinate exponents needed by the same retained quotient and remainder. -/
@[expose] def PowerInspection.exponents {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel)
    (inspection : PowerInspection sidecar) {size : Nat} {bindings : Fin size → CoherentNamed}
    {original : CoherentNamed} (input : Gaussian.Normalized bindings original) (index : Fin size)
    (coefficients : PowerInspection.Coefficients sidecar inspection input index) : List Nat := by
  unfold Coefficients at coefficients
  cases selected : inspection.form with
  | recognized _ _ =>
      rewrite [selected] at coefficients
      exact coefficients.val.terms.map (fun term => term.monomial.exponentAt index)
  | other _ =>
      rewrite [selected] at coefficients
      exact (coefficients.remainder.terms ++ coefficients.quotient.terms).map
        (fun term => term.monomial.exponentAt index)

/-- Every actual remainder monomial is found in this inspection's retained original product and power caches.

The certificate composes producer completeness with the exact once-extended
power bank. It covers both the pure-power branch and arbitrary original
annihilators after canonical coefficient combination and cancellation.
-/
theorem PowerInspection.replacementComplete {channel : CoherentNamed} (sidecar : Algebraic.Sidecar channel)
    (inspection : PowerInspection sidecar) {size : Nat} {bindings : Fin size → CoherentNamed}
    {original : CoherentNamed} (input : Gaussian.Normalized bindings original) (index : Fin size)
    (coefficients : PowerInspection.Coefficients sidecar inspection input index)
    (powers : List (Monomial.PowerEntry (bindings index)))
    (same : powers = input.denotation.retainPowersAt index
      (PowerInspection.exponents sidecar inspection input index coefficients)) :
    Terms.CacheComplete bindings (input.denotation.replacementLookup index powers)
      (PowerInspection.reducedForm sidecar inspection input index coefficients).terms := by
  subst powers
  cases inspection with
  | mk form _ =>
      unfold PowerInspection.Coefficients at coefficients
      cases form with
      | recognized _ _ =>
          have computedOrigins := Sparse.reduceAt_replacementOrigins input.form index sidecar.polynomial.natDegree
            (-sidecar.polynomial.eval 0)
          have origins : Terms.MonomialsSatisfy (Terms.ReplacementOrigin index input.form.terms)
              coefficients.val.terms :=
            Eq.mp (congrArg (fun form : Sparse Coefficient size =>
              Terms.MonomialsSatisfy (Terms.ReplacementOrigin index input.form.terms) form.terms)
                coefficients.property.symm) computedOrigins
          exact input.denotation.replacementLookup_complete index _ _ origins
            (Terms.selectedExponents_complete index coefficients.val.terms)
      | other different =>
          apply input.denotation.replacementLookup_complete index _ _ coefficients.remainder_replacementOrigins
          apply Terms.monomialsSatisfy_of_forall_mem
          intro term present
          exact mem_map.mpr ⟨term, mem_append.mpr (Or.inl present), rfl⟩

set_option genInjectivity false in
/-- One retained coefficient reduction through an actual original bounded generator and its original equation.

Its exact predecessor, coefficient attempt and selected-coordinate power cache
are retained as executable data. A reconstruction mismatch preserves that same
attempt; it supplies no conclusion that a root or expression is nonzero.
-/
structure Reduction {size : Nat} (bindings : Fin size → CoherentNamed) (original : CoherentNamed) where
  /-- The original bounded generator coordinate. -/
  index : Fin size
  /-- The same original admitted sidecar at this actual generator channel. -/
  sidecar : Algebraic.Sidecar (bindings index)
  /-- The once computed equation inspection of this same original sidecar. -/
  inspection : PowerInspection sidecar
  /-- The complete cached normalization actually preceding this operation. -/
  input : Gaussian.Normalized bindings original
  /-- The retained original pure-power coefficient form or completed general coefficient division. -/
  coefficients : PowerInspection.Coefficients sidecar inspection input index
  /-- This attempt consumes that same predecessor and original equation. -/
  coefficients_eq : coefficients = PowerInspection.divide sidecar inspection input index
  /-- The actual original selected-coordinate powers and once computed missing powers. -/
  powers : List (Monomial.PowerEntry (bindings index))
  /-- This power table extends the actual original predecessor's cached powers. -/
  powers_eq : powers = input.denotation.retainPowersAt index
    (PowerInspection.exponents sidecar inspection input index coefficients)

constructive_injectivity Reduction

namespace Reduction

/-- Retain one original equation reduction and every actual quotient, remainder and reused power cache. -/
@[expose] def prepare {size : Nat} {bindings : Fin size → CoherentNamed} {original : CoherentNamed}
    (index : Fin size) (sidecar : Algebraic.Sidecar (bindings index)) (inspection : PowerInspection sidecar)
    (input : Gaussian.Normalized bindings original) : Reduction bindings original :=
  let coefficients := PowerInspection.divide sidecar inspection input index
  let exponents := PowerInspection.exponents sidecar inspection input index coefficients
  let powers := input.denotation.retainPowersAt index exponents
  ⟨index, sidecar, inspection, input, coefficients, rfl, powers, rfl⟩

/-- Consume the same retained coefficient attempt and power table on the unchanged original source channel. -/
@[expose] def output {size : Nat} {bindings : Fin size → CoherentNamed} {original : CoherentNamed}
    (request : Reduction bindings original) : Gaussian.Normalized bindings original := by
  cases request with
  | mk index sidecar inspection input coefficients _ powers powers_eq =>
      let cached := input.denotation.replacementLookup index powers
      have complete := PowerInspection.replacementComplete sidecar inspection input index coefficients powers powers_eq
      cases inspection with
      | mk form _ =>
          unfold PowerInspection.Coefficients at coefficients
          cases form with
          | recognized _ identity =>
              have specified : Terms.CacheComplete bindings cached
                  (input.form.reduceAt index sidecar.polynomial.natDegree (-sidecar.polynomial.eval 0)).terms :=
                Eq.mp (congrArg (fun form : Sparse Coefficient size => Terms.CacheComplete bindings cached form.terms)
                  coefficients.property) complete
              exact input.reduceAtCached index sidecar.polynomial.natDegree (-sidecar.polynomial.eval 0)
                identity cached specified coefficients
          | other _ =>
              exact input.reduceBy index sidecar.polynomial coefficients sidecar.residual.source
                sidecar.residual.equivalent sidecar.equation cached complete

/-- The original reduction's output reads the same retained coefficient form without inspecting its numerical caches. -/
theorem output_form {size : Nat} {bindings : Fin size → CoherentNamed} {original : CoherentNamed}
    (request : Reduction bindings original) : request.output.form =
      PowerInspection.reducedForm request.sidecar request.inspection request.input request.index
        request.coefficients := by
  cases request with
  | mk index sidecar inspection input coefficients _ powers powersEq =>
      cases inspection with
      | mk form _ =>
          unfold PowerInspection.Coefficients at coefficients
          cases form with
          | recognized _ _ => rfl
          | other _ => rfl

/-- A prepared reduction computes its coefficients from any exact readback of the original input form. -/
theorem prepare_form {size : Nat} {bindings : Fin size → CoherentNamed} {original : CoherentNamed}
    (index : Fin size) (sidecar : Algebraic.Sidecar (bindings index)) (inspection : PowerInspection sidecar)
    (input : Gaussian.Normalized bindings original) (form : Sparse Coefficient size) (same : input.form = form) :
    (prepare index sidecar inspection input).output.form =
      match inspection.form with
      | .recognized _ _ => form.reduceAt index sidecar.polynomial.natDegree (-sidecar.polynomial.eval 0)
      | .other _ => (Sparse.DivisionAt.prepare form index sidecar.polynomial).remainder := by
  have actual := output_form (prepare index sidecar inspection input)
  cases same
  apply actual.trans
  cases inspection with
  | mk inspected _ => cases inspected <;> rfl

/-- A saved reduction consumes its exact original predecessor and retains its complete computed next state. -/
@[expose] def Valid {size : Nat} {bindings : Fin size → CoherentNamed} {original : CoherentNamed}
    (earlier : Gaussian.Normalized bindings original)
    (step : Query.History.Step (Reduction bindings original) (Gaussian.Normalized bindings original)) : Prop :=
  step.request.input = earlier ∧ step.next = step.request.output

end Reduction

set_option genInjectivity false in
/-- The current partial equation bank, chronological coefficient attempts and exact retained final reading. -/
structure Reduced {expression : Basic.Expr arity} {compiled : Basic.Compiled environment expression}
    (retained : Normalization compiled) (slots : Slots compiled.bindings) where
  /-- The actual optional original sidecars and their stored original equation inspections. -/
  powers : Powers compiled.bindings
  /-- The inspection bank retains precisely these same original optional slots. -/
  slots_eq : Powers.slots compiled.bindings powers = slots
  /-- Actual chronological reductions and their complete cached next normalizations. -/
  history : Query.History (Reduction (Basic.Binding.channels compiled.bindings) compiled.annotation.channel)
    (Gaussian.Normalized (Basic.Binding.channels compiled.bindings) compiled.annotation.channel)
  /-- The original normalization is the unchanged initial code. -/
  initial_eq : history.initial = retained.polynomial
  /-- Every retained attempt consumed the actual preceding cached normalization. -/
  chain : Query.History.Chain Reduction.Valid history.initial history.steps
  /-- The actual retained final normalization at the unchanged original numerical channel. -/
  polynomial : Gaussian.Normalized (Basic.Binding.channels compiled.bindings) compiled.annotation.channel
  /-- This same complete state is the endpoint of the original retained attempts. -/
  polynomial_eq : polynomial = Query.History.finish history.initial history.steps
  /-- The cached exact coefficient reading or all surviving nonconstant terms. -/
  reading : Sparse.ConstantView polynomial.form
  /-- The reading was computed from this same actual final coefficient form. -/
  reading_eq : reading = polynomial.form.constantView

constructive_injectivity Reduced

namespace Reduced

/-- Append one retained attempt without executing any preceding equation inspection or coefficient division again. -/
@[expose] def advance {expression : Basic.Expr arity} {compiled : Basic.Compiled environment expression}
    {retained : Normalization compiled} {slots nextSlots : Slots compiled.bindings}
    (reduced : Reduced retained slots) (powers : Powers compiled.bindings)
    (slots_eq : Powers.slots compiled.bindings powers = nextSlots)
    (index : Fin compiled.bindings.length)
    (sidecar : Algebraic.Sidecar (Basic.Binding.read compiled.bindings index).annotation.channel)
    (inspection : PowerInspection sidecar) : Reduced retained nextSlots := by
  let request := Reduction.prepare index sidecar inspection reduced.polynomial
  let next := request.output
  let step : Query.History.Step _ _ := ⟨request, next⟩
  let history := Query.History.mk reduced.history.initial (reduced.history.steps ++ [step])
  have after : Query.History.Chain Reduction.Valid
      (Query.History.finish reduced.history.initial reduced.history.steps) [step] :=
    .cons step ⟨reduced.polynomial_eq, rfl⟩ (.nil next)
  have endpoint : next = Query.History.finish history.initial history.steps := by
    change next = Query.History.finish reduced.history.initial (reduced.history.steps ++ [step])
    rewrite [Query.History.finish_append]
    rfl
  exact ⟨powers, slots_eq, history, reduced.initial_eq, reduced.chain.append after,
    next, endpoint, next.form.constantView, rfl⟩

/-- Apply each already available original equation once, retaining every actual intermediate state. -/
@[expose] def applyKnown {expression : Basic.Expr arity} {compiled : Basic.Compiled environment expression}
    {retained : Normalization compiled} {slots : Slots compiled.bindings} (reduced : Reduced retained slots) :
    (count : Nat) → count ≤ compiled.bindings.length → Reduced retained slots
  | 0, _ => reduced
  | count + 1, bound =>
      let previous := applyKnown reduced count (Nat.le_of_succ_le bound)
      let index : Fin compiled.bindings.length := ⟨count, Nat.lt_of_lt_of_le (Nat.lt_succ_self count) bound⟩
      match Powers.get compiled.bindings previous.powers index with
      | none => previous
      | some entry => previous.advance previous.powers previous.slots_eq index entry.1 entry.2

/-- Prepare original equations before asking for variables surviving their exact coefficient reductions. -/
@[expose] def prepare {expression : Basic.Expr arity} {compiled : Basic.Compiled environment expression}
    (retained : Normalization compiled) (slots : Slots compiled.bindings) : Reduced retained slots :=
  let powers := Powers.prepare compiled.bindings slots
  let polynomial := retained.polynomial
  let initial : Reduced retained slots :=
    ⟨powers, Powers.prepare_slots compiled.bindings slots, ⟨polynomial, []⟩,
      rfl, .nil polynomial, polynomial, rfl, polynomial.form.constantView, rfl⟩
  initial.applyKnown compiled.bindings.length (Nat.le_refl _)

/-- Supply one original equation and continue at the same literal retained coefficient state. -/
@[expose] def supply {expression : Basic.Expr arity} {compiled : Basic.Compiled environment expression}
    {retained : Normalization compiled} {slots : Slots compiled.bindings} (reduced : Reduced retained slots)
    (index : Fin compiled.bindings.length)
    (sidecar : Algebraic.Sidecar (Basic.Binding.read compiled.bindings index).annotation.channel) :
    Reduced retained (Slots.supply compiled.bindings slots index sidecar) :=
  let inspection := PowerInspection.prepare sidecar
  let powers := Powers.supply compiled.bindings reduced.powers index sidecar inspection
  have linked := Powers.supply_slots compiled.bindings reduced.powers index sidecar inspection
  have same : Powers.slots compiled.bindings powers = Slots.supply compiled.bindings slots index sidecar := by
    exact linked.trans (congrArg (fun slots => Slots.supply compiled.bindings slots index sidecar) reduced.slots_eq)
  reduced.advance powers same index sidecar inspection

/-- Read a constant before any generic arithmetic, consuming the actual retained final coefficient view. -/
@[expose] def result {expression : Basic.Expr arity} {compiled : Basic.Compiled environment expression}
    {retained : Normalization compiled} {slots : Slots compiled.bindings} (reduced : Reduced retained slots)
    (fallback : Unit → Algebraic.Sidecar compiled.annotation.channel) : Algebraic.Sidecar compiled.annotation.channel :=
  match reduced.reading with
  | .exact value same => Algebraic.Sidecar.ofRational (reduced.polynomial.rational value same)
  | .variable _ _ _ | .multiple _ _ _ _ => fallback ()

end Reduced

/-- The exact retained partial reduction, or no reduction when normalization was deliberately omitted. -/
@[expose] def ReductionCache {expression : Basic.Expr arity} (compiled : Basic.Compiled environment expression)
    (normalized : Option (Normalization compiled)) (slots : Slots compiled.bindings) : Type 1 :=
  match normalized with
  | none => PUnit
  | some retained => Reduced retained slots

set_option genInjectivity false in
/-- An original total-expression compilation and its actual materialized partial admission views. -/
structure Cached (environment : Fin arity → Annotated) (expression : Basic.Expr arity) where
  /-- The actual original total compilation, retaining its child annotations and source root caches. -/
  compiled : Basic.Compiled environment expression
  /-- The stored optional admissions at those same actual original binding occurrences. -/
  slots : Slots compiled.bindings
  /-- One retained normalization of this same compilation, computed only when existing evidence is absent. -/
  normalized : Option (Normalization compiled)
  /-- Current partial coefficient reductions and all actual chronological attempt caches. -/
  reduced : ReductionCache compiled normalized slots

constructive_injectivity Cached

namespace Cached

/-- Read the exact numerical channel of the retained original total compilation. -/
@[expose] def channel {environment : Fin arity → Annotated} {expression : Basic.Expr arity}
    (cached : Cached environment expression) : CoherentNamed := cached.compiled.annotation.channel

/-- Derive evidence from complete original admissions, reusing their same stored sidecars. -/
@[expose] def admitted {environment : Fin arity → Annotated} {expression : Basic.Expr arity}
    (cached : Cached environment expression) (admissions : Admissions cached.compiled.bindings) :
    Algebraic.Sidecar cached.channel :=
  let fallback : Unit → Algebraic.Sidecar cached.channel := fun _ =>
    withExisting cached.compiled.annotation fun _ =>
      construction cached.compiled.bindings admissions cached.compiled.annotation
        cached.compiled.construction cached.compiled.construction.supported_bindings
  match cached.normalized with
  | none => fallback ()
  | some retained => match fromAnnotation retained.annotation with
    | some sidecar =>
        show Algebraic.Sidecar cached.compiled.annotation.channel from retained.channel_eq ▸ sidecar
    | none => fallback ()

/-- Read the stored partial reduction through an exact identity of its original optional normalization. -/
@[expose] def reduction {expression : Basic.Expr arity} (cached : Cached environment expression)
    (retained : Normalization cached.compiled) (selected : cached.normalized = some retained) :
    Reduced retained cached.slots :=
  Eq.mp (congrArg (fun normalized => ReductionCache cached.compiled normalized cached.slots) selected) cached.reduced

/-- Read the exact currently needed original variables after all retained partial equation reductions. -/
@[expose] def required {expression : Basic.Expr arity} (cached : Cached environment expression) :
    Fin cached.compiled.bindings.length → Bool :=
  match selected : cached.normalized with
  | none => fun _ => true
  | some retained =>
      let reduced : Reduced retained cached.slots := cached.reduction retained selected
      fun index => decide (Terms.Required reduced.polynomial.form.terms index)

/-- Without normalization, the required-support check requests every original bounded binding. -/
theorem required_none {expression : Basic.Expr arity} (cached : Cached environment expression)
    (selected : cached.normalized = none) (index : Fin cached.compiled.bindings.length) :
    cached.required index = true := by
  cases cached with
  | mk compiled slots normalized reduced =>
      change normalized = none at selected
      subst normalized
      rfl

/-- With normalization, the required-support check reads precisely the stored reduced coefficient form. -/
theorem required_some {expression : Basic.Expr arity} (cached : Cached environment expression)
    (retained : Normalization cached.compiled) (selected : cached.normalized = some retained)
    (index : Fin cached.compiled.bindings.length) :
    cached.required index =
      decide (Terms.Required (cached.reduction retained selected).polynomial.form.terms index) := by
  cases cached with
  | mk compiled slots normalized reduced =>
      change Normalization compiled at retained
      change Fin compiled.bindings.length at index
      change normalized = some retained at selected
      subst normalized
      rfl

end Cached

set_option genInjectivity false in
/-- Original, normalized or exact reduced output evidence at the unchanged original compiled channel. -/
inductive Certificate {expression : Basic.Expr arity} (cached : Cached environment expression) : Type 1 where
  /-- Reuse an actual original output sidecar. -/
  | original (sidecar : Algebraic.Sidecar cached.compiled.annotation.channel)
      (selected : fromAnnotation cached.compiled.annotation = some sidecar)
  /-- Reuse the once computed normalized annotation. -/
  | normalized (retained : Normalization cached.compiled) (retained_eq : cached.normalized = some retained)
      (sidecar : Algebraic.Sidecar retained.annotation.channel)
      (selected : fromAnnotation retained.annotation = some sidecar)
  /-- Retain complete original admissions and their actual original construction. -/
  | admitted (admissions : Admissions cached.compiled.bindings)
      (result : Option {result : Algebraic.Sidecar cached.compiled.annotation.channel //
        result = cached.admitted admissions})
  /-- Read the exact constant from the actual once retained partial reduction. -/
  | exact (retained : Normalization cached.compiled) (retained_eq : cached.normalized = some retained)
      (reduced : Reduced retained cached.slots) (reduced_eq : reduced = cached.reduction retained retained_eq)
      (value : Coefficient) (same : reduced.polynomial.form.terms = (Sparse.constant value).terms)
  /-- Generic fallback consumes precisely the supported actual reduced caches and original surviving sidecars. -/
  | supported (retained : Normalization cached.compiled) (retained_eq : cached.normalized = some retained)
      (reduced : Reduced retained cached.slots) (reduced_eq : reduced = cached.reduction retained retained_eq)
      (support : Terms.Supported
        (fun index => (Slots.get cached.compiled.bindings cached.slots index).isSome = true)
        reduced.polynomial.form.terms)
      (result : Option {result : Algebraic.Sidecar cached.compiled.annotation.channel //
        result = reduced.result (fun _ => reduced.polynomial.algebraic
          (Slots.get cached.compiled.bindings cached.slots) support)})

constructive_injectivity Certificate

namespace Certificate

/-- Materialize this same original certificate, reusing an already retained actual result when supplied.

Admitted and supported certificates defer generic elimination until this named
full Sidecar boundary. Their original parent, coefficient caches and admissions
remain the actual inputs of the same existing materialization operation.
-/
@[expose] def buildSidecar {expression : Basic.Expr arity} {cached : Cached environment expression} :
    Certificate cached → Algebraic.Sidecar cached.compiled.annotation.channel
  | .original result _ => result
  | .normalized retained _ result _ => retained.channel_eq ▸ result
  | .admitted admissions result => match result with
    | some retained => retained.val
    | none => cached.admitted admissions
  | .exact _ _ reduced _ value same => Algebraic.Sidecar.ofRational (reduced.polynomial.rational value same)
  | .supported _ _ reduced _ support result => match result with
    | some retained => retained.val
    | none => reduced.result (fun _ => reduced.polynomial.algebraic
        (Slots.get cached.compiled.bindings cached.slots) support)

/-- Materialize and retain the actual output of this same original certificate at an explicit Sidecar boundary. -/
@[expose] def materialize {expression : Basic.Expr arity} {cached : Cached environment expression}
    (certificate : Certificate cached) :
    {result : Algebraic.Sidecar cached.channel // result = certificate.buildSidecar} :=
  let result := certificate.buildSidecar
  ⟨result, rfl⟩

/-- Read an already retained Sidecar without triggering generic materialization. -/
@[expose] def cached {expression : Basic.Expr arity} {cached : Cached environment expression} :
    Certificate cached → Option (Algebraic.Sidecar cached.channel)
  | .original result _ => some result
  | .normalized retained _ result _ =>
      let transported : Algebraic.Sidecar cached.compiled.annotation.channel := retained.channel_eq ▸ result
      some transported
  | .admitted _ result => result.map Subtype.val
  | .exact _ _ reduced _ value same => some (Algebraic.Sidecar.ofRational (reduced.polynomial.rational value same))
  | .supported _ _ _ _ _ result => result.map Subtype.val

/-- Any already retained output is the actual materialization of this same certificate. -/
theorem cached_eq {expression : Basic.Expr arity} {cached : Cached environment expression}
    (certificate : Certificate cached) (result : Algebraic.Sidecar cached.channel)
    (selected : certificate.cached = some result) : result = certificate.buildSidecar := by
  cases certificate with
  | original _ _ => exact Option.some.inj selected.symm
  | normalized _ _ _ _ => exact Option.some.inj selected.symm
  | exact _ _ _ _ _ _ => exact Option.some.inj selected.symm
  | admitted admissions retained =>
      cases retained with
      | none => cases selected
      | some retained => exact Option.some.inj selected.symm
  | supported _ _ _ _ _ retained =>
      cases retained with
      | none => cases selected
      | some retained => exact Option.some.inj selected.symm

/-- Read the same selected original generator evidence, including explicitly supplied full admissions. -/
@[expose] def generator {expression : Basic.Expr arity} {cached : Cached environment expression}
    (certificate : Certificate cached) (index : Fin cached.compiled.bindings.length) :
    Option (Algebraic.Sidecar (Basic.Binding.channels cached.compiled.bindings index)) :=
  match certificate with
  | .admitted admissions _ => some (Admissions.get cached.compiled.bindings admissions index)
  | .original _ _ | .normalized _ _ _ _ | .exact _ _ _ _ _ _ | .supported _ _ _ _ _ _ =>
      Slots.get cached.compiled.bindings cached.slots index

/-- Read the actual original optional generator table, retaining complete supplied admissions when present. -/
@[expose] def generatorSlots {expression : Basic.Expr arity} {cached : Cached environment expression} :
    Certificate cached → Slots cached.compiled.bindings
  | .admitted admissions _ => Admissions.slots cached.compiled.bindings admissions
  | .original _ _ | .normalized _ _ _ _ | .exact _ _ _ _ _ _ | .supported _ _ _ _ _ _ => cached.slots

/-- Reading the retained generator table is the original selected-generator operation's complete output. -/
theorem get_generatorSlots {expression : Basic.Expr arity} {cached : Cached environment expression}
    (certificate : Certificate cached) (index : Fin cached.compiled.bindings.length) :
    Slots.get cached.compiled.bindings certificate.generatorSlots index = certificate.generator index := by
  cases certificate with
  | admitted admissions _ => exact Admissions.get_slots cached.compiled.bindings admissions index
  | original _ _ | normalized _ _ _ _ | exact _ _ _ _ _ _ | supported _ _ _ _ _ _ => rfl

/-- Inspect retained coefficient constants before requesting admissions or constructing generic eliminants. -/
@[expose] def existing {expression : Basic.Expr arity} (cached : Cached environment expression) :
    Option (Certificate cached) :=
  let original : Unit → Option (Certificate cached) := fun _ =>
    match selected : fromAnnotation cached.compiled.annotation with
    | some result => some (.original result selected)
    | none => none
  match retained_eq : cached.normalized with
  | none => original ()
  | some retained =>
      let reduced : Reduced retained cached.slots := cached.reduction retained retained_eq
      match reduced.reading with
      | .exact value same => some (.exact retained retained_eq reduced rfl value same)
      | .variable _ _ _ | .multiple _ _ _ _ =>
          match inferred : fromAnnotation retained.annotation with
          | none => original ()
          | some result => some (.normalized retained retained_eq result inferred)

/-- The actual retained normalization of this certificate's original compilation. -/
abbrev InverseSource {expression : Basic.Expr arity} {cached : Cached environment expression}
    (_certificate : Certificate cached) :=
  {retained : Normalization cached.compiled // cached.normalized = some retained}

namespace InverseSource

/-- Read the literal current partial polynomial and all of its original denotation caches. -/
@[expose] def polynomial {expression : Basic.Expr arity} {cached : Cached environment expression}
    {certificate : Certificate cached} (source : InverseSource certificate) :
    Gaussian.Normalized (Basic.Binding.channels cached.compiled.bindings) cached.channel :=
  let reduced : Reduced source.val cached.slots := cached.reduction source.val source.property
  reduced.polynomial

end InverseSource

/-- The exact selected-generator check cache is indexed by this original certificate and actual source normalization. -/
abbrev InverseCheck {expression : Basic.Expr arity} {cached : Cached environment expression}
    (certificate : Certificate cached) :=
  (source : InverseSource certificate) ×
    Gaussian.Normalized.InverseCheck source.polynomial certificate.generator

/-- Compute and retain one exact-generator attempt, preserving all original visited coordinates and gcd results. -/
@[expose] def inverseCheck {expression : Basic.Expr arity} {cached : Cached environment expression}
    (certificate : Certificate cached) (supplied : Option (Division.Prepared cached.channel) := none) :
    Option (InverseCheck certificate) :=
  match selected : cached.normalized with
  | none => none
  | some retained =>
      let source : InverseSource certificate := ⟨retained, selected⟩
      some ⟨source, source.polynomial.inverseCheck certificate.generator supplied⟩

end Certificate

namespace Cached

/-- Retain compilation, original leaf views and partial equation reductions once, with deferred generic arithmetic. -/
@[expose] def ofExpression (environment : Fin arity → Annotated) (expression : Basic.Expr arity) :
    Cached environment expression :=
  let compiled := expression.retain environment false
  let slots := materialize compiled.bindings
  let normalize : Unit → Option (Normalization compiled) := fun _ =>
    let value := compiled.normalize
    some ⟨value, rfl, rfl, value.infer, rfl⟩
  let normalized := match compiled.annotation.provenance with
    | none => normalize ()
    | some retained => match retained.rationalReading with
      | some _ => none
      | none => normalize ()
  let reduced : ReductionCache compiled normalized slots := match normalized with
    | none => PUnit.unit
    | some retained => Reduced.prepare retained slots
  ⟨compiled, slots, normalized, reduced⟩

/-- Supply one original leaf while retaining the compilation, every old equation and every prior coefficient attempt. -/
@[expose] def supply {environment : Fin arity → Annotated} {expression : Basic.Expr arity}
    (cached : Cached environment expression) (index : Fin cached.compiled.bindings.length)
    (sidecar : Algebraic.Sidecar (Basic.Binding.read cached.compiled.bindings index).annotation.channel) :
    Cached environment expression :=
  let slots := Slots.supply cached.compiled.bindings cached.slots index sidecar
  let reduced : ReductionCache cached.compiled cached.normalized slots :=
    match selected : cached.normalized with
    | none => PUnit.unit
    | some retained =>
        let previous : Reduced retained cached.slots := cached.reduction retained selected
        previous.supply index sidecar
  ⟨cached.compiled, slots, cached.normalized, reduced⟩

/-- Supplying an admission preserves the literal original compilation and its complete retained child owners. -/
theorem supply_compiled {expression : Basic.Expr arity} (cached : Cached environment expression)
    (index : Fin cached.compiled.bindings.length)
    (sidecar : Algebraic.Sidecar (Basic.Binding.read cached.compiled.bindings index).annotation.channel) :
    (cached.supply index sidecar).compiled = cached.compiled := rfl

/-- Supplying an admission preserves the once computed original normalization and inferred annotation. -/
theorem supply_normalized {expression : Basic.Expr arity} (cached : Cached environment expression)
    (index : Fin cached.compiled.bindings.length)
    (sidecar : Algebraic.Sidecar (Basic.Binding.read cached.compiled.bindings index).annotation.channel) :
    (cached.supply index sidecar).normalized = cached.normalized := rfl

/-- Complete supported reduced work once, without requesting an absent variable that the exact equations eliminated. -/
@[expose] def certificateReady {expression : Basic.Expr arity} (cached : Cached environment expression)
    (ready : Slots.Ready cached.compiled.bindings cached.slots cached.required) : Certificate cached := by
  match selected : cached.normalized with
  | none =>
      let admissions := Admissions.ofFunction cached.compiled.bindings fun index =>
        (Slots.get cached.compiled.bindings cached.slots index).get (ready index (by
          exact required_none cached selected index))
      exact .admitted admissions none
  | some retained =>
      let reduced : Reduced retained cached.slots := cached.reduction retained selected
      have available : ∀ index, Terms.Required reduced.polynomial.form.terms index →
          (Slots.get cached.compiled.bindings cached.slots index).isSome = true := by
        intro index needed
        apply ready index
        exact (required_some cached retained selected index).trans (decide_eq_true needed)
      let support := Terms.supported_of_required
        (fun index => (Slots.get cached.compiled.bindings cached.slots index).isSome = true)
        reduced.polynomial.form.terms available
      exact .supported retained selected reduced rfl support none

/-- Retain complete supplied original admissions and materialize their original construction once. -/
@[expose] def certificate {expression : Basic.Expr arity} (cached : Cached environment expression)
    (admissions : Admissions cached.compiled.bindings) : Certificate cached :=
  match Certificate.existing cached with
  | some retained => retained
  | none => .admitted admissions none

end Cached

end Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Base
end
