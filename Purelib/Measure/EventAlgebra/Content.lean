module
import Purelib.Data.Rat.Fraction

import Purelib.Measure.Content.Basic
public import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Operations
public import Purelib.Measure.Weighted.Consolidation
import Purelib.Measure.Weighted.Transform
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.EventAlgebra.Simple.Basic
import Purelib.Measure.Weighted.Event
public import Purelib.Measure.EventAlgebra.Basic
import Purelib.Measure.Distribution.Mixture.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Explicit finite event algebras

An event algebra here is finite presented data: an explicitly enumerated code
type, an executable interpretation of each code as a Boolean event, and
certified Boolean operations.  No powerset, sigma-algebra, generated closure,
or enumeration of an ambient carrier is formed.
-/

namespace Purelib.Measure
namespace EventAlgebra

open Purelib.Data.Rat in
/-- Measure the Boolean event obtained by evaluating the retained algebra code in the exact input content. -/
def measure {α : Type} (algebra : EventAlgebra α)
    (content : Content α) (event : algebra.Code) : Fraction.Rational :=
  content.measure (algebra.evaluate event)

/-- The algebra's empty code has zero content measurement. -/
@[simp] theorem measure_empty {α : Type}
    (algebra : EventAlgebra α) (content : Content α) :
    algebra.measure content algebra.empty = 0 := by
  unfold measure
  calc
    content.measure (algebra.evaluate algebra.empty) =
        content.measure (fun _ => false) :=
      content.measure_congr _ _ algebra.evaluate_empty
    _ = 0 := content.measure_empty

/-- The algebra's universal code has measurement equal to the original total content mass. -/
@[simp] theorem measure_univ {α : Type}
    (algebra : EventAlgebra α) (content : Content α) :
    algebra.measure content algebra.univ = content.total := by
  unfold measure
  calc
    content.measure (algebra.evaluate algebra.univ) =
        content.measure (fun _ => true) :=
      content.measure_congr _ _ algebra.evaluate_univ
    _ = content.total := content.measure_univ

/-- A retained event code and its complement have measurements summing to original total mass. -/
theorem measure_add_complement {α : Type}
    (algebra : EventAlgebra α) (content : Content α)
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

/-- The two code measurements sum to the measurements of their retained union and intersection. -/
theorem measure_valuation {α : Type}
    (algebra : EventAlgebra α) (content : Content α)
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

end EventAlgebra
end Purelib.Measure

end

section
section
@[expose] public section

/-!
# Atomic representation of finite event-algebra contents

Finite content is already arithmetic data: a displayed list of nonnegative
rational weights.  Relative to a finitely presented event algebra, pushing
that table to complete truth signatures and consolidating equal signatures
produces the unique displayed algebra atoms relevant to every coded event and
simple observable.

No abstract measure is postulated and no carrier powerset is enumerated.
-/

namespace Purelib.Measure

namespace EventAlgebra

/-- Push the exact content occurrences onto their complete retained event-algebra signatures. -/
def signatureContent {α : Type} (algebra : EventAlgebra α)
    (content : Content α) : Content (List Bool) :=
  content.map algebra.signature

/-- Signature pushforward preserves the original content total. -/
theorem signatureContent_total {α : Type}
    (algebra : EventAlgebra α) (content : Content α) :
    (algebra.signatureContent content).total = content.total :=
  content.map_total algebra.signature

/-- A coded event's original measurement equals its signature-event measurement under the exact signature content. -/
theorem measure_eq_signatureContent_measure {α : Type}
    (algebra : EventAlgebra α) (content : Content α)
    (event : algebra.Code) :
    algebra.measure content event =
      (algebra.signatureContent content).measure
        (algebra.signatureEvent event) := by
  unfold measure signatureContent
  rw [content.map_measure]
  exact content.measure_congr _ _ (fun item =>
    (algebra.signatureEvent_signature event item).symm)

open Purelib.Data.Rat in
/-- Integrating a signature observable equals integrating its pullback under the exact original content. -/
theorem signatureContent_integral {α : Type}
    (algebra : EventAlgebra α) (content : Content α)
    (value : List Bool → Fraction.Rational) :
    (algebra.signatureContent content).integral value =
      content.integral (fun item => value (algebra.signature item)) :=
  content.map_integral algebra.signature value

/-- Consolidate equal event-algebra signatures in the exact signature pushforward content.

The executable finite consolidation combines the original weights into one row per retained signature without choosing
new payload representatives. -/
def atomContent {α : Type} (algebra : EventAlgebra α)
    (content : Content α) : Content (List Bool) :=
  ⟨consolidateAtoms (algebra.signatureContent content).atoms⟩

/-- The consolidated algebra atom content contains no repeated signatures. -/
theorem atomContent_noRepeatedSignatures {α : Type}
    (algebra : EventAlgebra α) (content : Content α) :
    NoRepeatedPayloads (algebra.atomContent content).atoms :=
  consolidateAtoms_noRepeatedPayloads
    (algebra.signatureContent content).atoms

/-- Consolidated algebra atom content preserves the original total mass. -/
theorem atomContent_total {α : Type}
    (algebra : EventAlgebra α) (content : Content α) :
    (algebra.atomContent content).total = content.total := by
  change totalWeight
      (consolidateAtoms (algebra.signatureContent content).atoms) =
    content.total
  rw [totalWeight_consolidateAtoms]
  exact algebra.signatureContent_total content

/-- Consolidated algebra atom content has no more rows than the original content. -/
theorem atomContent_atoms_length_le {α : Type}
    (algebra : EventAlgebra α) (content : Content α) :
    (algebra.atomContent content).atoms.length ≤ content.atoms.length := by
  calc
    (algebra.atomContent content).atoms.length ≤
        (algebra.signatureContent content).atoms.length :=
      consolidateAtoms_length_le _
    _ = content.atoms.length := by
      unfold signatureContent Content.map
      induction content.atoms with
      | nil => rfl
      | cons atom remaining inductionHypothesis =>
          simp only [mapAtoms, List.length_cons, inductionHypothesis, -eq_self, -iff_self]
          rfl

/-- The consolidated algebra atom content preserves every original coded-event measurement. -/
theorem measure_eq_atomContent_measure {α : Type}
    (algebra : EventAlgebra α) (content : Content α)
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
      unfold atomContent Content.measure
      exact (eventWeight_consolidateAtoms
        (algebra.signatureEvent event)
        (algebra.signatureContent content).atoms).symm

open Purelib.Data.Rat in
/-- The consolidated algebra atom content preserves every original signature-observable integral. -/
theorem integral_eq_atomContent_integral {α : Type}
    (algebra : EventAlgebra α) (content : Content α)
    (value : List Bool → Fraction.Rational) :
    content.integral (fun item => value (algebra.signature item)) =
      (algebra.atomContent content).integral value := by
  calc
    content.integral (fun item => value (algebra.signature item)) =
        (algebra.signatureContent content).integral value :=
      (algebra.signatureContent_integral content value).symm
    _ = (algebra.atomContent content).integral value := by
      unfold atomContent Content.integral
      exact (expectationWeight_consolidateAtoms value
        (algebra.signatureContent content).atoms).symm
end EventAlgebra

end Purelib.Measure

end

end
