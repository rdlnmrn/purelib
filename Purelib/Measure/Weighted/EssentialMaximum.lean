module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Weighted.Density
public import Purelib.Measure.Weighted.EssentialBound
import Purelib.Measure.Weighted.Operations
public import Purelib.Measure.Weighted.Transform
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Executable finite essential maxima

The scan retains the original weighted occurrence list, skips exactly the
zero-weight rows and takes the rational maximum of the remaining observable
magnitudes. Its bound and transport certificates concern that same scan,
including the original maps, nonnegative weight factors and density witnesses.
-/

namespace Purelib.Measure

open Purelib.Data.Rat
open Fraction.Order

/-- Compute the maximum observable magnitude over nonzero-weight retained occurrences, starting from zero.

The recursive scan skips exactly zero weights and takes rational maxima at
all other original occurrences. An empty or entirely zero-weight list returns zero. -/
@[expose] public def essentialMaximumMagnitudeOn {α : Type}
    (value : α → Fraction.Rational) : List (Weighted α) → Fraction.Rational
  | [] => 0
  | atom :: remaining =>
      if atom.weight = 0 then essentialMaximumMagnitudeOn value remaining
      else max (Distance.rationalSeparation (value atom.item) 0)
        (essentialMaximumMagnitudeOn value remaining)

/-- Pointwise equal observables have equal essential maximum magnitude on the same retained list.

At each occurrence the supplied scalar equality identifies the observable
magnitudes. The original zero-weight branch and unchanged tail are retained. -/
public theorem essentialMaximumMagnitudeOn_congr {α : Type}
    (atoms : List (Weighted α)) (left right : α → Fraction.Rational)
    (pointwise : ∀ item, left item = right item) :
    essentialMaximumMagnitudeOn left atoms =
      essentialMaximumMagnitudeOn right atoms := by
  induction atoms with
  | nil => rfl
  | cons atom remaining ih =>
      change (if atom.weight = 0 then essentialMaximumMagnitudeOn left remaining
          else max (Distance.rationalSeparation (left atom.item) 0)
            (essentialMaximumMagnitudeOn left remaining)) =
        (if atom.weight = 0 then essentialMaximumMagnitudeOn right remaining
          else max (Distance.rationalSeparation (right atom.item) 0)
            (essentialMaximumMagnitudeOn right remaining))
      by_cases zero : atom.weight = 0
      · exact (if_pos zero).trans (ih.trans (if_pos zero).symm)
      · have headEqual := congrArg (fun value => Distance.rationalSeparation value 0)
          (pointwise atom.item)
        exact (if_neg zero).trans
          ((congrArg (fun head => max head (essentialMaximumMagnitudeOn left remaining))
            headEqual).trans
            ((congrArg (fun tail => max (Distance.rationalSeparation (right atom.item) 0)
              tail) ih).trans (if_neg zero).symm))

/-- The computed essential maximum magnitude is nonnegative.

The empty scan returns zero. A nonzero-weight head contributes a maximum
whose retained tail already has a nonnegative bound. -/
public theorem essentialMaximumMagnitudeOn_nonnegative {α : Type}
    (value : α → Fraction.Rational) :
    ∀ atoms : List (Weighted α), 0 ≤ essentialMaximumMagnitudeOn value atoms
  | [] => Basic.le_refl 0
  | atom :: remaining => by
      by_cases zero : atom.weight = 0
      · rw [essentialMaximumMagnitudeOn, if_pos zero]
        exact essentialMaximumMagnitudeOn_nonnegative value remaining
      · rw [essentialMaximumMagnitudeOn, if_neg zero]
        exact Basic.Compatibility.le_trans _ _ _
          (essentialMaximumMagnitudeOn_nonnegative value remaining)
          (Basic.le_max_right _ _)

/-- The computed essential maximum bounds every nonzero-weight retained occurrence's observable magnitude.

Membership supplies the actual head or tail occurrence. A retained maximum
bounds the head directly and transports the recursive bound on tail occurrences. -/
public theorem essentiallyBoundedByOn_essentialMaximumMagnitudeOn {α : Type}
    (value : α → Fraction.Rational) :
    ∀ atoms : List (Weighted α),
      EssentiallyBoundedByOn atoms value (essentialMaximumMagnitudeOn value atoms)
  | [] => by
      intro atom member
      nomatch member
  | atom :: remaining => by
      intro candidate member
      cases member with
      | head =>
          by_cases zero : atom.weight = 0
          · exact Or.inl zero
          · apply Or.inr
            rw [essentialMaximumMagnitudeOn, if_neg zero]
            exact Basic.le_max_left _ _
      | tail _ tailMember =>
          cases essentiallyBoundedByOn_essentialMaximumMagnitudeOn value
              remaining candidate tailMember with
          | inl zero => exact Or.inl zero
          | inr bound =>
              apply Or.inr
              by_cases headZero : atom.weight = 0
              · rw [essentialMaximumMagnitudeOn, if_pos headZero]
                exact bound
              · rw [essentialMaximumMagnitudeOn, if_neg headZero]
                exact Basic.Compatibility.le_trans _ _ _ bound (Basic.le_max_right _ _)

/-- Any nonnegative essential magnitude ceiling bounds the computed maximum on the retained list.

The ceiling bounds each retained nonzero-weight head and recursively bounds
the original tail. Both scalar bounds bound their retained rational maximum. -/
public theorem essentialMaximumMagnitudeOn_le {α : Type}
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational)
    (ceilingNonnegative : 0 ≤ ceiling) :
    ∀ atoms : List (Weighted α), EssentiallyBoundedByOn atoms value ceiling →
      essentialMaximumMagnitudeOn value atoms ≤ ceiling
  | [], _ => ceilingNonnegative
  | atom :: remaining, bounded => by
      have tailBounded : EssentiallyBoundedByOn remaining value ceiling :=
        fun candidate member => bounded candidate (List.Mem.tail atom member)
      have tailLe := essentialMaximumMagnitudeOn_le value ceiling
        ceilingNonnegative remaining tailBounded
      by_cases zero : atom.weight = 0
      · rw [essentialMaximumMagnitudeOn, if_pos zero]
        exact tailLe
      · have headLe : Distance.rationalSeparation (value atom.item) 0 ≤ ceiling := by
          cases bounded atom (List.Mem.head remaining) with
          | inl impossible => exact (zero impossible).elim
          | inr bound => exact bound
        rw [essentialMaximumMagnitudeOn, if_neg zero]
        exact Basic.max_le headLe tailLe

/-- Nonnegative density weighting preserves an essential magnitude bound on the same retained payloads.

Each output occurrence retains its source payload and multiplies the original
weight by the supplied density. A zero source weight remains zero; every other
source bound is unchanged. -/
public theorem essentiallyBoundedByOn_densityAtoms {α : Type}
    (density : α → Fraction.Rational) (densityNonnegative : ∀ item, 0 ≤ density item)
    (value : α → Fraction.Rational) (ceiling : Fraction.Rational) :
    ∀ atoms : List (Weighted α), EssentiallyBoundedByOn atoms value ceiling →
      EssentiallyBoundedByOn (densityAtoms density densityNonnegative atoms) value ceiling
  | [], _ => by
      intro atom member
      nomatch member
  | source :: remaining, bounded => by
      have tailBounded : EssentiallyBoundedByOn remaining value ceiling :=
        fun atom member => bounded atom (List.Mem.tail source member)
      have tailResult := essentiallyBoundedByOn_densityAtoms
        density densityNonnegative value ceiling remaining tailBounded
      intro candidate member
      change candidate ∈ (⟨source.item, source.weight * density source.item,
          Arithmetic.mul_nonneg_direct source.nonnegative
            (densityNonnegative source.item)⟩ : Weighted α) ::
        densityAtoms density densityNonnegative remaining at member
      cases member with
      | head =>
          cases bounded source (List.Mem.head remaining) with
          | inl sourceZero =>
              apply Or.inl
              change source.weight * density source.item = 0
              rw [sourceZero, zero_mul]
          | inr valueBound => exact Or.inr valueBound
      | tail _ tailMember => exact tailResult candidate tailMember

/-- The essential maximum of appended occurrence lists is the maximum of their individual essential maxima.

The scan retains the exact appended lists. Its zero-weight branch passes to
the original tail; its other branch reassociates the same rational maxima. -/
public theorem essentialMaximumMagnitudeOn_append {α : Type}
    (value : α → Fraction.Rational) : ∀ left right : List (Weighted α),
    essentialMaximumMagnitudeOn value (left ++ right) =
      max (essentialMaximumMagnitudeOn value left) (essentialMaximumMagnitudeOn value right)
  | [], right => (Basic.max_eq_right
      (essentialMaximumMagnitudeOn_nonnegative value right)).symm
  | atom :: remaining, right => by
      change (if atom.weight = 0 then essentialMaximumMagnitudeOn value (remaining ++ right)
          else max (Distance.rationalSeparation (value atom.item) 0)
            (essentialMaximumMagnitudeOn value (remaining ++ right))) =
        max (if atom.weight = 0 then essentialMaximumMagnitudeOn value remaining
          else max (Distance.rationalSeparation (value atom.item) 0)
            (essentialMaximumMagnitudeOn value remaining))
          (essentialMaximumMagnitudeOn value right)
      have tailEqual := essentialMaximumMagnitudeOn_append value remaining right
      by_cases zero : atom.weight = 0
      · exact (if_pos zero).trans
          (tailEqual.trans (congrArg (fun left => max left
            (essentialMaximumMagnitudeOn value right)) (if_pos zero)).symm)
      · exact (if_neg zero).trans
          ((congrArg (fun tail => max (Distance.rationalSeparation (value atom.item) 0)
            tail) tailEqual).trans
            ((Basic.max_assoc _ _ _).symm.trans
              (congrArg (fun left => max left (essentialMaximumMagnitudeOn value right))
                (if_neg zero)).symm))

/-- Mapping payloads pulls the observable back along the same retained map.

The map preserves each original weight and nonnegativity witness, so both
scans take identical zero-weight branches and retain the same tail comparison. -/
public theorem essentialMaximumMagnitudeOn_mapAtoms {α β : Type}
    (function : α → β) (value : β → Fraction.Rational) :
    ∀ atoms : List (Weighted α),
      essentialMaximumMagnitudeOn value (mapAtoms function atoms) =
        essentialMaximumMagnitudeOn (fun item => value (function item)) atoms
  | [] => rfl
  | atom :: remaining => by
      change (if atom.weight = 0 then essentialMaximumMagnitudeOn value (mapAtoms function remaining)
          else max (Distance.rationalSeparation (value (function atom.item)) 0)
            (essentialMaximumMagnitudeOn value (mapAtoms function remaining))) =
        (if atom.weight = 0 then
          essentialMaximumMagnitudeOn (fun item => value (function item)) remaining
          else max (Distance.rationalSeparation (value (function atom.item)) 0)
            (essentialMaximumMagnitudeOn (fun item => value (function item)) remaining))
      have tailEqual := essentialMaximumMagnitudeOn_mapAtoms function value remaining
      by_cases zero : atom.weight = 0
      · exact (if_pos zero).trans (tailEqual.trans (if_pos zero).symm)
      · exact (if_neg zero).trans
          ((congrArg (fun tail => max (Distance.rationalSeparation (value (function atom.item)) 0)
            tail) tailEqual).trans (if_neg zero).symm)

/-- A factor equal to zero makes the scaled list's essential maximum magnitude zero.

The scaling operation retains the original occurrences and factor witness.
Every computed weight is zero, so the same scan skips each retained row. -/
public theorem essentialMaximumMagnitudeOn_scaleAtoms_of_eq_zero {α : Type}
    (value : α → Fraction.Rational) (factor : Fraction.Rational)
    (nonnegative : 0 ≤ factor) (factorZero : factor = 0) :
    ∀ atoms : List (Weighted α),
      essentialMaximumMagnitudeOn value (scaleAtoms factor nonnegative atoms) = 0
  | [] => rfl
  | atom :: remaining => by
      have scaledZero : factor * atom.weight = 0 := by rw [factorZero, zero_mul]
      change (if factor * atom.weight = 0 then
          essentialMaximumMagnitudeOn value (scaleAtoms factor nonnegative remaining)
          else max (Distance.rationalSeparation (value atom.item) 0)
            (essentialMaximumMagnitudeOn value (scaleAtoms factor nonnegative remaining))) = 0
      exact (if_pos scaledZero).trans
        (essentialMaximumMagnitudeOn_scaleAtoms_of_eq_zero value factor nonnegative factorZero remaining)

/-- A nonzero nonnegative weight factor preserves the exact essential maximum magnitude.

A zero original weight remains zero and a nonzero one stays nonzero under
multiplication by the supplied factor. The original occurrence magnitudes and
the recursively retained scaled tail therefore give the same maximum. -/
public theorem essentialMaximumMagnitudeOn_scaleAtoms_of_ne {α : Type}
    (value : α → Fraction.Rational) (factor : Fraction.Rational)
    (nonnegative : 0 ≤ factor) (factorNonzero : factor ≠ 0) :
    ∀ atoms : List (Weighted α),
      essentialMaximumMagnitudeOn value (scaleAtoms factor nonnegative atoms) =
        essentialMaximumMagnitudeOn value atoms
  | [] => rfl
  | atom :: remaining => by
      change (if factor * atom.weight = 0 then
          essentialMaximumMagnitudeOn value (scaleAtoms factor nonnegative remaining)
          else max (Distance.rationalSeparation (value atom.item) 0)
            (essentialMaximumMagnitudeOn value (scaleAtoms factor nonnegative remaining))) =
        (if atom.weight = 0 then essentialMaximumMagnitudeOn value remaining
          else max (Distance.rationalSeparation (value atom.item) 0)
            (essentialMaximumMagnitudeOn value remaining))
      have tailEqual := essentialMaximumMagnitudeOn_scaleAtoms_of_ne value factor
        nonnegative factorNonzero remaining
      by_cases atomZero : atom.weight = 0
      · have scaledZero : factor * atom.weight = 0 := by rw [atomZero, mul_zero]
        exact (if_pos scaledZero).trans (tailEqual.trans (if_pos atomZero).symm)
      · have productNonzero := Fraction.Field.mul_ne_zero_direct factorNonzero atomZero
        exact (if_neg productNonzero).trans
          ((congrArg (fun tail => max (Distance.rationalSeparation (value atom.item) 0)
            tail) tailEqual).trans (if_neg atomZero).symm)

/-- Taking pointwise magnitude first leaves the computed essential maximum magnitude unchanged.

Each original magnitude is nonnegative, so taking its separation from zero
again returns that same scalar. The original weights and recursive tails are retained. -/
public theorem essentialMaximumMagnitudeOn_magnitude {α : Type}
    (value : α → Fraction.Rational) : ∀ atoms : List (Weighted α),
    essentialMaximumMagnitudeOn (fun item => Distance.rationalSeparation (value item) 0) atoms =
      essentialMaximumMagnitudeOn value atoms
  | [] => rfl
  | atom :: remaining => by
      change (if atom.weight = 0 then
          essentialMaximumMagnitudeOn (fun item => Distance.rationalSeparation (value item) 0) remaining
          else max (Distance.rationalSeparation (Distance.rationalSeparation (value atom.item) 0) 0)
            (essentialMaximumMagnitudeOn (fun item => Distance.rationalSeparation (value item) 0) remaining)) =
        (if atom.weight = 0 then essentialMaximumMagnitudeOn value remaining
          else max (Distance.rationalSeparation (value atom.item) 0)
            (essentialMaximumMagnitudeOn value remaining))
      have tailEqual := essentialMaximumMagnitudeOn_magnitude value remaining
      by_cases zero : atom.weight = 0
      · exact (if_pos zero).trans (tailEqual.trans (if_pos zero).symm)
      · have headEqual := Distance.rationalSeparation_zero_of_nonneg
          (Distance.rationalSeparation_nonneg (value atom.item) 0)
        exact (if_neg zero).trans
          ((congrArg (fun head => max head
            (essentialMaximumMagnitudeOn (fun item => Distance.rationalSeparation (value item) 0) remaining))
            headEqual).trans
            ((congrArg (fun tail => max (Distance.rationalSeparation (value atom.item) 0) tail)
              tailEqual).trans (if_neg zero).symm))

end Purelib.Measure
