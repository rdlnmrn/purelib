module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.Rat.Bounds.Half
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Group.Negation
import Purelib.Tactic.Ring
import Mathlib.Order.Basic

/-!
# Quarter-turn covariance of Gaussian sectors

Two Boolean bits retain one of the four Gaussian quarter-turn units. Inverse
rotation by that unit transports its axial or diagonal sector to east or
northeast with the original strict and weak half-coordinate boundaries.
-/

namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Unit

open Purelib.Data
open ComplexContinuedFraction.Encoding
open Rat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

/-- Decode two bits as the successive quarter-turn units one, i, minus one and minus i.

The four entries retain the original real and imaginary rational coordinates.
The first bit chooses a half-turn and the second chooses a further quarter-turn. -/
@[expose] public def quarterUnit : Bool → Bool → Gaussian.Basic.Canonical
  | false, false => ⟨1, 0⟩
  | false, true => ⟨0, 1⟩
  | true, false => ⟨-1, 0⟩
  | true, true => ⟨0, -1⟩

/-- Read the exact inverse of the quarter-turn unit encoded by two bits.

The lookup retains the original real coordinate and reverses the imaginary
coordinate. Each entry is the original unit's total Gaussian reciprocal. -/
@[expose] public def inverseQuarterUnit : Bool → Bool → Gaussian.Basic.Canonical
  | false, false => ⟨1, 0⟩
  | false, true => ⟨0, -1⟩
  | true, false => ⟨-1, 0⟩
  | true, true => ⟨0, 1⟩

/-- The canonical Gaussian inverse of a quarter-turn unit is the retained inverse lookup.

The two Boolean inputs determine four exact Gaussian records. Their original
reciprocal operation agrees with the displayed lookup in every case. -/
@[simp] public theorem quarterUnit_inv (first second : Bool) :
    (quarterUnit first second)⁻¹ = inverseQuarterUnit first second := by
  cases first <;> cases second <;> decide

/-- Choose east for an axial code and northeast for a diagonal code.

These are the two sector predicates after removing the encoded quarter-turn.
The lookup preserves the original axial-versus-diagonal Boolean convention. -/
@[expose] public def canonicalSector : Bool → Sector
  | false => .east
  | true => .northEast

/-- Rotating by the inverse encoded quarter-turn unit reduces sector membership to east or northeast.

The first two code bits determine the retained unit and the third selects the
axial or diagonal predicate. Direct coordinate equalities and half-bound
implications preserve every strict and weak boundary in both directions. -/
public theorem holds_covariant (first second diagonal : Bool)
    (value : Gaussian.Basic.Canonical) :
    (Sector.Code.sectorOfBits first second diagonal).Holds value ↔
      (canonicalSector diagonal).Holds ((quarterUnit first second)⁻¹ * value) := by
  rw [quarterUnit_inv]
  have eastRotation : inverseQuarterUnit false false * value = value := by
    apply Gaussian.Basic.Canonical.ext
    · change 1 * value.re - 0 * value.im = value.re
      ring1
    · change 1 * value.im + 0 * value.re = value.im
      ring1
  have northRotation : inverseQuarterUnit false true * value =
      (⟨value.im, -value.re⟩ : Gaussian.Basic.Canonical) := by
    apply Gaussian.Basic.Canonical.ext
    · change 0 * value.re - (-1) * value.im = value.im
      ring1
    · change 0 * value.im + (-1) * value.re = -value.re
      ring1
  have westRotation : inverseQuarterUnit true false * value =
      (⟨-value.re, -value.im⟩ : Gaussian.Basic.Canonical) := by
    apply Gaussian.Basic.Canonical.ext
    · change (-1) * value.re - 0 * value.im = -value.re
      ring1
    · change (-1) * value.im + 0 * value.re = -value.im
      ring1
  have southRotation : inverseQuarterUnit true true * value =
      (⟨-value.im, value.re⟩ : Gaussian.Basic.Canonical) := by
    apply Gaussian.Basic.Canonical.ext
    · change 0 * value.re - 1 * value.im = -value.im
      ring1
    · change 0 * value.im + 1 * value.re = value.re
      ring1
  cases first with
  | false =>
      cases second with
      | false =>
          have encoded : Code.sectorOfBits false false diagonal = canonicalSector diagonal := by
            cases diagonal <;> rfl
          rewrite [encoded, eastRotation]
          exact ⟨fun bounds => bounds, fun bounds => bounds⟩
      | true =>
          rw [northRotation]
          cases diagonal with
          | false =>
              change (-1 / 2 < value.re ∧ value.re < 1 / 2 ∧ 1 / 2 ≤ value.im) ↔
                (1 / 2 ≤ value.im ∧ -1 / 2 < -value.re ∧ -value.re < 1 / 2)
              constructor
              · intro bounds
                exact ⟨bounds.2.2,
                  (Bounds.Half.neg_half_lt_neg_iff value.re).mpr bounds.2.1,
                  (Bounds.Half.neg_lt_half_iff value.re).mpr bounds.1⟩
              · intro bounds
                exact ⟨(Bounds.Half.neg_lt_half_iff value.re).mp bounds.2.2,
                  (Bounds.Half.neg_half_lt_neg_iff value.re).mp bounds.2.1,
                  bounds.1⟩
          | true =>
              change (value.re ≤ -1 / 2 ∧ 1 / 2 ≤ value.im) ↔
                (1 / 2 ≤ value.im ∧ 1 / 2 ≤ -value.re)
              constructor
              · intro bounds
                exact ⟨bounds.2, (Bounds.Half.half_le_neg_iff value.re).mpr bounds.1⟩
              · intro bounds
                exact ⟨(Bounds.Half.half_le_neg_iff value.re).mp bounds.2, bounds.1⟩
  | true =>
      cases second with
      | false =>
          rw [westRotation]
          cases diagonal with
          | false =>
              change (value.re ≤ -1 / 2 ∧ -1 / 2 < value.im ∧ value.im < 1 / 2) ↔
                (1 / 2 ≤ -value.re ∧ -1 / 2 < -value.im ∧ -value.im < 1 / 2)
              constructor
              · intro bounds
                exact ⟨(Bounds.Half.half_le_neg_iff value.re).mpr bounds.1,
                  (Bounds.Half.neg_half_lt_neg_iff value.im).mpr bounds.2.2,
                  (Bounds.Half.neg_lt_half_iff value.im).mpr bounds.2.1⟩
              · intro bounds
                exact ⟨(Bounds.Half.half_le_neg_iff value.re).mp bounds.1,
                  (Bounds.Half.neg_lt_half_iff value.im).mp bounds.2.2,
                  (Bounds.Half.neg_half_lt_neg_iff value.im).mp bounds.2.1⟩
          | true =>
              change (value.re ≤ -1 / 2 ∧ value.im ≤ -1 / 2) ↔
                (1 / 2 ≤ -value.re ∧ 1 / 2 ≤ -value.im)
              constructor
              · intro bounds
                exact ⟨(Bounds.Half.half_le_neg_iff value.re).mpr bounds.1,
                  (Bounds.Half.half_le_neg_iff value.im).mpr bounds.2⟩
              · intro bounds
                exact ⟨(Bounds.Half.half_le_neg_iff value.re).mp bounds.1,
                  (Bounds.Half.half_le_neg_iff value.im).mp bounds.2⟩
      | true =>
          rw [southRotation]
          cases diagonal with
          | false =>
              change (-1 / 2 < value.re ∧ value.re < 1 / 2 ∧ value.im ≤ -1 / 2) ↔
                (1 / 2 ≤ -value.im ∧ -1 / 2 < value.re ∧ value.re < 1 / 2)
              constructor
              · intro bounds
                exact ⟨(Bounds.Half.half_le_neg_iff value.im).mpr bounds.2.2,
                  bounds.1, bounds.2.1⟩
              · intro bounds
                exact ⟨bounds.2.1, bounds.2.2,
                  (Bounds.Half.half_le_neg_iff value.im).mp bounds.1⟩
          | true =>
              change (1 / 2 ≤ value.re ∧ value.im ≤ -1 / 2) ↔
                (1 / 2 ≤ -value.im ∧ 1 / 2 ≤ value.re)
              constructor
              · intro bounds
                exact ⟨(Bounds.Half.half_le_neg_iff value.im).mpr bounds.2, bounds.1⟩
              · intro bounds
                exact ⟨bounds.2, (Bounds.Half.half_le_neg_iff value.im).mp bounds.1⟩

end Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Unit
