import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.ContentIntegral

/-!
# Finite expectation stability

These estimates turn supplied pointwise rational error budgets into exact
finite expectation bounds.  A second form permits a larger error on one
displayed exceptional event and charges exactly its finite probability.
-/

namespace FiniteMeasure

/-- A two-sided pointwise error bound on the displayed weighted atoms. -/
def SymmetricErrorOn {α : Type} (atoms : List (Weighted α))
    (allowance left right : α → Coordinate) : Prop :=
  ∀ atom, atom ∈ atoms →
    right atom.item - left atom.item ≤ allowance atom.item ∧
      left atom.item - right atom.item ≤ allowance atom.item

namespace Distribution

theorem expectationWeight_sub {α : Type}
    (atoms : List (Weighted α)) (left right : α → Coordinate) :
    expectationWeight atoms (fun item => left item - right item) =
      expectationWeight atoms left - expectationWeight atoms right := by
  induction atoms with
  | nil =>
      simp only [expectationWeight]
      ring1
  | cons atom remaining inductionHypothesis =>
      simp only [expectationWeight, inductionHypothesis]
      ring1

end Distribution

namespace FiniteContent

theorem integral_sub {α : Type} (content : FiniteContent α)
    (left right : α → Coordinate) :
    content.integral (fun item => left item - right item) =
      content.integral left - content.integral right :=
  Distribution.expectationWeight_sub content.atoms left right

/-- A pointwise two-sided rational envelope bounds the difference of exact
finite-content integrals. -/
theorem integral_symmetricError {α : Type} (content : FiniteContent α)
    (allowance left right : α → Coordinate)
    (bounded : SymmetricErrorOn content.atoms allowance left right) :
    content.integral right - content.integral left ≤
        content.integral allowance ∧
      content.integral left - content.integral right ≤
        content.integral allowance := by
  constructor
  · have averaged := content.integral_mono
      (fun item => right item - left item) allowance
      (fun atom member => (bounded atom member).1)
    rw [content.integral_sub] at averaged
    exact averaged
  · have averaged := content.integral_mono
      (fun item => left item - right item) allowance
      (fun atom member => (bounded atom member).2)
    rw [content.integral_sub] at averaged
    exact averaged

/-- Uniform finite-content error scales by the exact displayed total mass. -/
theorem integral_close_of_uniform {α : Type} (content : FiniteContent α)
    (epsilon : Coordinate) (left right : α → Coordinate)
    (bounded : SymmetricErrorOn content.atoms
      (fun _ => epsilon) left right) :
    content.integral right - content.integral left ≤
        content.total * epsilon ∧
      content.integral left - content.integral right ≤
        content.total * epsilon := by
  have averaged := content.integral_symmetricError
    (fun _ => epsilon) left right bounded
  rw [content.integral_constant] at averaged
  exact averaged

end FiniteContent

namespace Distribution

theorem expectation_sub {α : Type} (distribution : Distribution α)
    (left right : α → Coordinate) :
    distribution.expectation (fun item => left item - right item) =
      distribution.expectation left - distribution.expectation right :=
  expectationWeight_sub distribution.atoms left right

/-- A pointwise two-sided rational envelope also encloses the difference of
the two exact finite expectations. -/
theorem expectation_symmetricError {α : Type}
    (distribution : Distribution α)
    (allowance left right : α → Coordinate)
    (bounded : SymmetricErrorOn distribution.atoms allowance left right) :
    distribution.expectation right - distribution.expectation left ≤
        distribution.expectation allowance ∧
      distribution.expectation left - distribution.expectation right ≤
        distribution.expectation allowance := by
  constructor
  · have averaged := distribution.expectation_mono
      (fun item => right item - left item) allowance
      (fun atom member => (bounded atom member).1)
    rw [distribution.expectation_sub] at averaged
    exact averaged
  · have averaged := distribution.expectation_mono
      (fun item => left item - right item) allowance
      (fun atom member => (bounded atom member).2)
    rw [distribution.expectation_sub] at averaged
    exact averaged

/-- Uniform finite error passes unchanged through a probability-weighted
expectation. -/
theorem expectation_close_of_uniform {α : Type}
    (distribution : Distribution α) (epsilon : Coordinate)
    (left right : α → Coordinate)
    (bounded : SymmetricErrorOn distribution.atoms
      (fun _ => epsilon) left right) :
    distribution.expectation right - distribution.expectation left ≤ epsilon ∧
      distribution.expectation left - distribution.expectation right ≤ epsilon := by
  have averaged := distribution.expectation_symmetricError
    (fun _ => epsilon) left right bounded
  rw [distribution.expectation_constant] at averaged
  exact averaged

/-- Finite exceptional-event stability.  Away from the displayed event the
error is at most `ordinary`; on it, the additional allowance `extra` is
charged in proportion to its exact rational probability. -/
theorem expectation_close_outside_event {α : Type}
    (distribution : Distribution α) (exceptional : α → Bool)
    (ordinary extra : Coordinate) (left right : α → Coordinate)
    (outside : ∀ atom, atom ∈ distribution.atoms →
      exceptional atom.item = false →
        right atom.item - left atom.item ≤ ordinary ∧
          left atom.item - right atom.item ≤ ordinary)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      exceptional atom.item = true →
        right atom.item - left atom.item ≤ ordinary + extra ∧
          left atom.item - right atom.item ≤ ordinary + extra) :
    distribution.expectation right - distribution.expectation left ≤
        ordinary + extra * distribution.probability exceptional ∧
      distribution.expectation left - distribution.expectation right ≤
        ordinary + extra * distribution.probability exceptional := by
  let allowance : α → Coordinate := fun item =>
    ordinary + extra * indicator exceptional item
  have bounded : SymmetricErrorOn distribution.atoms allowance left right := by
    intro atom member
    cases selected : exceptional atom.item
    · simpa only [allowance, indicator, selected, mul_zero, add_zero] using
        outside atom member selected
    · simpa only [allowance, indicator, selected, mul_one] using
        inside atom member selected
  have averaged := distribution.expectation_symmetricError
    allowance left right bounded
  have allowanceExpectation : distribution.expectation allowance =
      ordinary + extra * distribution.probability exceptional := by
    calc
      distribution.expectation allowance =
          distribution.expectation (fun _ => ordinary) +
            distribution.expectation
              (fun item => extra * indicator exceptional item) :=
        distribution.expectation_add _ _
      _ = ordinary + extra * distribution.probability exceptional := by
        rw [distribution.expectation_constant,
          distribution.expectation_scale,
          distribution.expectation_indicator]
  rw [allowanceExpectation] at averaged
  exact averaged

end Distribution

end FiniteMeasure
