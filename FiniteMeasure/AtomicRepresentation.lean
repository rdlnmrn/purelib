import FiniteMeasure.EventAlgebra
import FiniteMeasure.ContentIntegral
import FiniteMeasure.SimpleObservable

/-!
# Atomic representation of finite event-algebra contents

Finite content is already arithmetic data: a displayed list of nonnegative
rational weights.  Relative to a finitely presented event algebra, pushing
that table to complete truth signatures and consolidating equal signatures
produces the unique displayed algebra atoms relevant to every coded event and
simple observable.

No abstract measure is postulated and no carrier powerset is enumerated.
-/

namespace FiniteMeasure

namespace FiniteEventAlgebra

/-- Push arbitrary finite content onto the complete truth signatures of a
presented finite event algebra. -/
def signatureContent {α : Type} (algebra : FiniteEventAlgebra α)
    (content : FiniteContent α) : FiniteContent (List Bool) :=
  content.map algebra.signature

theorem signatureContent_total {α : Type}
    (algebra : FiniteEventAlgebra α) (content : FiniteContent α) :
    (algebra.signatureContent content).total = content.total :=
  content.map_total algebra.signature

/-- Every coded event measure is exactly recovered from the pushed truth
signatures. -/
theorem measure_eq_signatureContent_measure {α : Type}
    (algebra : FiniteEventAlgebra α) (content : FiniteContent α)
    (event : algebra.Code) :
    algebra.measure content event =
      (algebra.signatureContent content).measure
        (algebra.signatureEvent event) := by
  unfold measure signatureContent
  rw [content.map_measure]
  exact content.measure_congr _ _ (fun item =>
    (algebra.signatureEvent_signature event item).symm)

/-- Every rational observable of a truth signature obeys exact finite change
of variables. -/
theorem signatureContent_integral {α : Type}
    (algebra : FiniteEventAlgebra α) (content : FiniteContent α)
    (value : List Bool → Coordinate) :
    (algebra.signatureContent content).integral value =
      content.integral (fun item => value (algebra.signature item)) :=
  content.map_integral algebra.signature value

/-- Consolidate repeated signatures into the actual displayed atoms of the
finite event algebra. -/
def atomContent {α : Type} (algebra : FiniteEventAlgebra α)
    (content : FiniteContent α) : FiniteContent (List Bool) :=
  ⟨consolidateAtoms (algebra.signatureContent content).atoms⟩

theorem atomContent_noRepeatedSignatures {α : Type}
    (algebra : FiniteEventAlgebra α) (content : FiniteContent α) :
    NoRepeatedPayloads (algebra.atomContent content).atoms :=
  consolidateAtoms_noRepeatedPayloads
    (algebra.signatureContent content).atoms

theorem atomContent_total {α : Type}
    (algebra : FiniteEventAlgebra α) (content : FiniteContent α) :
    (algebra.atomContent content).total = content.total := by
  change totalWeight
      (consolidateAtoms (algebra.signatureContent content).atoms) =
    content.total
  rw [totalWeight_consolidateAtoms]
  exact algebra.signatureContent_total content

theorem atomContent_atoms_length_le {α : Type}
    (algebra : FiniteEventAlgebra α) (content : FiniteContent α) :
    (algebra.atomContent content).atoms.length ≤ content.atoms.length := by
  calc
    (algebra.atomContent content).atoms.length ≤
        (algebra.signatureContent content).atoms.length :=
      consolidateAtoms_length_le _
    _ = content.atoms.length := by
      unfold signatureContent FiniteContent.map
      induction content.atoms with
      | nil => rfl
      | cons atom remaining inductionHypothesis =>
          simp only [mapAtoms, List.length_cons, inductionHypothesis]

/-- The consolidated algebra atoms recover every coded event measure. -/
theorem measure_eq_atomContent_measure {α : Type}
    (algebra : FiniteEventAlgebra α) (content : FiniteContent α)
    (event : algebra.Code) :
    algebra.measure content event =
      (algebra.atomContent content).measure
        (algebra.signatureEvent event) := by
  calc
    algebra.measure content event =
        (algebra.signatureContent content).measure
          (algebra.signatureEvent event) :=
      algebra.measure_eq_signatureContent_measure content event
    _ = (algebra.atomContent content).measure
          (algebra.signatureEvent event) := by
      unfold atomContent FiniteContent.measure
      exact (eventWeight_consolidateAtoms
        (algebra.signatureEvent event)
        (algebra.signatureContent content).atoms).symm

/-- The atom table recovers the integral of every rational observable that
is explicitly evaluated on truth signatures. -/
theorem integral_eq_atomContent_integral {α : Type}
    (algebra : FiniteEventAlgebra α) (content : FiniteContent α)
    (value : List Bool → Coordinate) :
    content.integral (fun item => value (algebra.signature item)) =
      (algebra.atomContent content).integral value := by
  calc
    content.integral (fun item => value (algebra.signature item)) =
        (algebra.signatureContent content).integral value :=
      (algebra.signatureContent_integral content value).symm
    _ = (algebra.atomContent content).integral value := by
      unfold atomContent FiniteContent.integral
      exact (expectationWeight_consolidateAtoms value
        (algebra.signatureContent content).atoms).symm

/-- In particular, the unique displayed truth atoms determine every coded
simple-observable integral. -/
theorem simpleObservable_integral_eq_atomContent_integral {α : Type}
    (algebra : FiniteEventAlgebra α) (content : FiniteContent α)
    (observable : SimpleObservable algebra) :
    content.integral observable.evaluate =
      (algebra.atomContent content).integral observable.signatureValue := by
  calc
    content.integral observable.evaluate =
        content.integral (fun item =>
          observable.signatureValue (algebra.signature item)) := by
      exact content.integral_congr _ _ (fun item =>
        (observable.signatureValue_signature item).symm)
    _ = (algebra.atomContent content).integral observable.signatureValue :=
      algebra.integral_eq_atomContent_integral content
        observable.signatureValue

end FiniteEventAlgebra

end FiniteMeasure
