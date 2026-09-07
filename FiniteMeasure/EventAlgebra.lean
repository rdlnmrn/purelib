import FiniteMeasure.Stochastic
import FiniteMeasure.Valuation
import FiniteMeasure.Consolidation

/-!
# Explicit finite event algebras

An event algebra here is finite presented data: an explicitly enumerated code
type, an executable interpretation of each code as a Boolean event, and
certified Boolean operations.  No powerset, sigma-algebra, generated closure,
or enumeration of an ambient carrier is formed.
-/

namespace FiniteMeasure

/-- A finitely enumerated Boolean algebra of executable events. -/
structure FiniteEventAlgebra (α : Type) where
  Code : Type
  codes : List Code
  listed : ∀ code, code ∈ codes
  codeEq : (left right : Code) → Decidable (left = right)
  evaluate : Code → α → Bool
  empty : Code
  univ : Code
  complement : Code → Code
  union : Code → Code → Code
  intersection : Code → Code → Code
  evaluate_empty : ∀ item, evaluate empty item = false
  evaluate_univ : ∀ item, evaluate univ item = true
  evaluate_complement : ∀ event item,
    evaluate (complement event) item = !(evaluate event item)
  evaluate_union : ∀ left right item,
    evaluate (union left right) item =
      (evaluate left item || evaluate right item)
  evaluate_intersection : ∀ left right item,
    evaluate (intersection left right) item =
      (evaluate left item && evaluate right item)

namespace FiniteEventAlgebra

/-- Pull a finite event algebra back along an explicit function.  Codes and
Boolean operations are unchanged; only their executable interpretation is
precomposed. -/
def comap {α β : Type} (algebra : FiniteEventAlgebra β)
    (function : α → β) : FiniteEventAlgebra α where
  Code := algebra.Code
  codes := algebra.codes
  listed := algebra.listed
  codeEq := algebra.codeEq
  evaluate event item := algebra.evaluate event (function item)
  empty := algebra.empty
  univ := algebra.univ
  complement := algebra.complement
  union := algebra.union
  intersection := algebra.intersection
  evaluate_empty item := algebra.evaluate_empty (function item)
  evaluate_univ item := algebra.evaluate_univ (function item)
  evaluate_complement event item :=
    algebra.evaluate_complement event (function item)
  evaluate_union left right item :=
    algebra.evaluate_union left right (function item)
  evaluate_intersection left right item :=
    algebra.evaluate_intersection left right (function item)

@[simp] theorem comap_evaluate {α β : Type}
    (algebra : FiniteEventAlgebra β) (function : α → β)
    (event : algebra.Code) (item : α) :
    (algebra.comap function).evaluate event item =
      algebra.evaluate event (function item) := rfl

/-- The complete finite truth signature of one payload against the displayed
event catalogue.  Equal signatures are the algebra's finite atoms. -/
def signature {α : Type} (algebra : FiniteEventAlgebra α)
    (item : α) : List Bool :=
  algebra.codes.map fun event => algebra.evaluate event item

private def selectCode {Code : Type}
    (equal : (left right : Code) → Decidable (left = right))
    (target : Code) : List Code → List Bool → Bool
  | [], _ => false
  | _ :: _, [] => false
  | event :: remaining, selected :: selections =>
      match equal target event with
      | .isTrue _ => selected
      | .isFalse _ => selectCode equal target remaining selections

private theorem selectCode_map {Code α : Type}
    (equal : (left right : Code) → Decidable (left = right))
    (evaluate : Code → α → Bool) (target : Code) (item : α) :
    ∀ events : List Code, target ∈ events →
      selectCode equal target events
          (events.map fun event => evaluate event item) =
        evaluate target item
  | [], member => by
      simp only [List.not_mem_nil] at member
  | event :: remaining, member => by
      cases decision : equal target event with
      | isTrue same =>
          subst event
          simp only [List.map_cons, selectCode, decision]
      | isFalse different =>
          have tail : target ∈ remaining := by
            simpa only [List.mem_cons, different, false_or] using member
          simp only [List.map_cons, selectCode, decision]
          exact selectCode_map equal evaluate target item remaining tail

/-- Read the truth value of one algebra event from a supplied signature. -/
def signatureEvent {α : Type} (algebra : FiniteEventAlgebra α)
    (event : algebra.Code) : List Bool → Bool :=
  selectCode algebra.codeEq event algebra.codes

theorem signatureEvent_signature {α : Type}
    (algebra : FiniteEventAlgebra α) (event : algebra.Code) (item : α) :
    algebra.signatureEvent event (algebra.signature item) =
      algebra.evaluate event item :=
  selectCode_map algebra.codeEq algebra.evaluate event item algebra.codes
    (algebra.listed event)

/-- Payloads with the same finite truth signature cannot be distinguished by
any event in the displayed algebra. -/
theorem evaluate_eq_of_signature_eq {α : Type}
    (algebra : FiniteEventAlgebra α) {left right : α}
    (same : algebra.signature left = algebra.signature right)
    (event : algebra.Code) :
    algebra.evaluate event left = algebra.evaluate event right := by
  rw [← algebra.signatureEvent_signature event left,
    ← algebra.signatureEvent_signature event right, same]

/-- Push a finite distribution onto the finite truth signatures of an event
algebra.  Repeated signatures may remain as repeated rows; consolidation is
an independent finite operation. -/
def signatureDistribution {α : Type}
    (algebra : FiniteEventAlgebra α) (distribution : Distribution α) :
    Distribution (List Bool) :=
  distribution.map algebra.signature

/-- Every algebra-event probability is recovered exactly from its finite
signature distribution.  Thus the rational weights of the signature atoms
determine the measure on the complete displayed algebra. -/
theorem probability_eq_signatureDistribution_probability {α : Type}
    (algebra : FiniteEventAlgebra α) (distribution : Distribution α)
    (event : algebra.Code) :
    distribution.probability (algebra.evaluate event) =
      (algebra.signatureDistribution distribution).probability
        (algebra.signatureEvent event) := by
  symm
  calc
    (algebra.signatureDistribution distribution).probability
          (algebra.signatureEvent event) =
        distribution.probability (fun item =>
          algebra.signatureEvent event (algebra.signature item)) :=
      distribution.map_probability algebra.signature
        (algebra.signatureEvent event)
    _ = distribution.probability (algebra.evaluate event) := by
      exact distribution.probability_congr _ _ (fun item =>
        algebra.signatureEvent_signature event item)

/-- Merge repeated truth signatures to obtain the actual displayed algebra
atoms and their rational weights. -/
def atomDistribution {α : Type} (algebra : FiniteEventAlgebra α)
    (distribution : Distribution α) : Distribution (List Bool) :=
  (algebra.signatureDistribution distribution).consolidate

theorem atomDistribution_noRepeatedSignatures {α : Type}
    (algebra : FiniteEventAlgebra α) (distribution : Distribution α) :
    NoRepeatedPayloads (algebra.atomDistribution distribution).atoms :=
  (algebra.signatureDistribution distribution).consolidate_noRepeatedPayloads

theorem atomDistribution_atoms_length_le {α : Type}
    (algebra : FiniteEventAlgebra α) (distribution : Distribution α) :
    (algebra.atomDistribution distribution).atoms.length ≤
      distribution.atoms.length := by
  exact (algebra.signatureDistribution distribution).consolidate_atoms_length_le
    |>.trans_eq (distribution.map_atoms_length algebra.signature)

/-- The consolidated finite signature atoms still determine every coded
event probability exactly. -/
theorem probability_eq_atomDistribution_probability {α : Type}
    (algebra : FiniteEventAlgebra α) (distribution : Distribution α)
    (event : algebra.Code) :
    distribution.probability (algebra.evaluate event) =
      (algebra.atomDistribution distribution).probability
        (algebra.signatureEvent event) := by
  calc
    distribution.probability (algebra.evaluate event) =
        (algebra.signatureDistribution distribution).probability
          (algebra.signatureEvent event) :=
      algebra.probability_eq_signatureDistribution_probability
        distribution event
    _ = (algebra.atomDistribution distribution).probability
          (algebra.signatureEvent event) :=
      ((algebra.signatureDistribution distribution)
        |>.consolidate_evaluationEquivalent.probability_eq
          (algebra.signatureEvent event)).symm

/-- Restrict a finite content to one code of a displayed finite event
algebra. -/
def measure {α : Type} (algebra : FiniteEventAlgebra α)
    (content : FiniteContent α) (event : algebra.Code) : Coordinate :=
  content.measure (algebra.evaluate event)

@[simp] theorem measure_empty {α : Type}
    (algebra : FiniteEventAlgebra α) (content : FiniteContent α) :
    algebra.measure content algebra.empty = 0 := by
  unfold measure
  calc
    content.measure (algebra.evaluate algebra.empty) =
        content.measure (fun _ => false) :=
      content.measure_congr _ _ algebra.evaluate_empty
    _ = 0 := content.measure_empty

@[simp] theorem measure_univ {α : Type}
    (algebra : FiniteEventAlgebra α) (content : FiniteContent α) :
    algebra.measure content algebra.univ = content.total := by
  unfold measure
  calc
    content.measure (algebra.evaluate algebra.univ) =
        content.measure (fun _ => true) :=
      content.measure_congr _ _ algebra.evaluate_univ
    _ = content.total := content.measure_univ

theorem measure_add_complement {α : Type}
    (algebra : FiniteEventAlgebra α) (content : FiniteContent α)
    (event : algebra.Code) :
    algebra.measure content event +
        algebra.measure content (algebra.complement event) = content.total := by
  unfold measure
  calc
    content.measure (algebra.evaluate event) +
          content.measure (algebra.evaluate (algebra.complement event)) =
        content.measure (algebra.evaluate event) +
          content.measure (complementEvent (algebra.evaluate event)) := by
      apply congrArg (content.measure (algebra.evaluate event) + ·)
      exact content.measure_congr _ _ (fun item =>
        algebra.evaluate_complement event item)
    _ = content.total := content.add_complement (algebra.evaluate event)

theorem measure_valuation {α : Type}
    (algebra : FiniteEventAlgebra α) (content : FiniteContent α)
    (left right : algebra.Code) :
    algebra.measure content left + algebra.measure content right =
      algebra.measure content (algebra.union left right) +
      algebra.measure content (algebra.intersection left right) := by
  unfold measure
  have unionSame :
      content.measure (algebra.evaluate (algebra.union left right)) =
        content.measure
          (unionEvent (algebra.evaluate left) (algebra.evaluate right)) :=
    content.measure_congr _ _ (fun item =>
      algebra.evaluate_union left right item)
  have intersectionSame :
      content.measure (algebra.evaluate (algebra.intersection left right)) =
        content.measure
          (intersectionEvent (algebra.evaluate left)
            (algebra.evaluate right)) :=
    content.measure_congr _ _ (fun item =>
      algebra.evaluate_intersection left right item)
  rw [unionSame, intersectionSame]
  exact content.valuation (algebra.evaluate left) (algebra.evaluate right)

end FiniteEventAlgebra

/-! ## A concrete four-event algebra on `Bool` -/

/-- Codes select independently whether `false` and `true` belong to the
event.  The four displayed codes are the complete Boolean event algebra. -/
def boolEventAlgebra : FiniteEventAlgebra Bool where
  Code := Bool × Bool
  codes := [(false, false), (false, true), (true, false), (true, true)]
  listed code := by
    rcases code with ⟨first, second⟩
    cases first <;> cases second <;> simp
  codeEq left right := inferInstance
  evaluate code item := if item then code.2 else code.1
  empty := (false, false)
  univ := (true, true)
  complement code := (!code.1, !code.2)
  union left right := (left.1 || right.1, left.2 || right.2)
  intersection left right := (left.1 && right.1, left.2 && right.2)
  evaluate_empty item := by cases item <;> rfl
  evaluate_univ item := by cases item <;> rfl
  evaluate_complement event item := by cases item <;> rfl
  evaluate_union left right item := by cases item <;> rfl
  evaluate_intersection left right item := by cases item <;> rfl

end FiniteMeasure
