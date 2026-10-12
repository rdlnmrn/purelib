module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic

public import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Cached finite area comparison

Realizations consume supplied exact summaries and retain the finite pair-bound
certificates, residual, computed bound and payment separately.
-/

namespace Purelib.Integration.Path.AreaComparison

open Purelib.Data.Gaussian.Basic.Canonical

section
open Purelib.Data.Gaussian
open Purelib.Integration.Path
/-- The exact increment summary carrier for the first components of the original ordered pairs. -/
@[reducible] def FirstSummary (pairs : List (Basic.Canonical × Basic.Canonical)) :=
  IncrementArea.Summary (pairs.map Prod.fst)

/-- The exact increment summary carrier for the second components of the original ordered pairs. -/
@[reducible] def SecondSummary (pairs : List (Basic.Canonical × Basic.Canonical)) :=
  IncrementArea.Summary (pairs.map Prod.snd)

end

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Every original pair has squared difference bounded by the retained error. -/
@[reducible] def PairErrors (pairs : List (Basic.Canonical × Basic.Canonical))
    (error : Fraction.Rational) : Prop :=
  ∀ pair ∈ pairs, normSq (pair.1 - pair.2) ≤ error

/-- Every original first component has squared norm bounded by the retained magnitude. -/
@[reducible] def FirstBounds (pairs : List (Basic.Canonical × Basic.Canonical))
    (magnitude : Fraction.Rational) : Prop :=
  ∀ pair ∈ pairs, normSq pair.1 ≤ magnitude

/-- Every original second component has squared norm bounded by the retained magnitude. -/
@[reducible] def SecondBounds (pairs : List (Basic.Canonical × Basic.Canonical))
    (magnitude : Fraction.Rational) : Prop :=
  ∀ pair ∈ pairs, normSq pair.2 ≤ magnitude

/-- Nonnegative error and magnitude with pointwise difference and two-sided magnitude certificates for the exact pairs.
-/
structure PairBounds (pairs : List (Basic.Canonical × Basic.Canonical))
    (error magnitude : Fraction.Rational) where
  /-- The original pairwise squared-error allowance is nonnegative. -/ errorNonnegative : 0 ≤ error
  /-- The original common squared-magnitude bound is nonnegative. -/ magnitudeNonnegative : 0 ≤ magnitude
  /-- Every retained pair satisfies the original squared-difference bound. -/ errors : PairErrors pairs error
  /-- Every first component satisfies the original common magnitude bound. -/ firstBound : FirstBounds pairs magnitude
  /-- Every second component satisfies the original common magnitude bound. -/ secondBound : SecondBounds pairs
    magnitude

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- An area-comparison certificate retaining both original summaries, its exact residual and a paid fourth-power count
bound.

The ordered pairs and two summaries remain indexed; cached residual and bound equations tie the numerical estimate to
their actual area difference. -/
structure Cached (pairs : List (Basic.Canonical × Basic.Canonical))
    (error magnitude : Fraction.Rational) (first : FirstSummary pairs) (second : SecondSummary pairs) where
  /-- The retained nonnegative budgets and pointwise certificates for the exact original pairs. -/ evidence : PairBounds
    pairs error magnitude
  /-- The cached area difference of the two original summaries. -/ residual : Basic.Canonical
  /-- The residual equals the first retained area minus the second retained area. -/ residual_eq : residual = first.area
    - second.area
  /-- The cached count-dependent squared-norm area bound. -/ areaBound : Fraction.Rational
  /-- The bound is sixteen times count to the fourth power times original error and magnitude. -/ areaBound_eq :
    areaBound = 16 * (pairs.length : Fraction.Rational) ^ 4 * error * magnitude
  /-- The cached area bound is nonnegative. -/ areaBound_nonnegative : 0 ≤ areaBound
  /-- The exact cached residual's squared norm is bounded by the retained area bound. -/ bounded : normSq residual ≤
    areaBound

constructive_injectivity Cached

namespace Cached

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Retain the exact area residual and count-dependent bound for two original summaries with certified paired errors.

The builder reuses the supplied summaries and pair certificates, retaining the exact fourth-power cost formula and its
nonnegative squared-norm bound. -/
def realize (pairs : List (Basic.Canonical × Basic.Canonical))
    (error magnitude : Fraction.Rational) (first : FirstSummary pairs) (second : SecondSummary pairs)
    (errorNonnegative : 0 ≤ error) (magnitudeNonnegative : 0 ≤ magnitude)
    (errors : PairErrors pairs error)
    (firstBound : FirstBounds pairs magnitude)
    (secondBound : SecondBounds pairs magnitude) :
    Cached pairs error magnitude first second :=
  let residual := first.area - second.area
  let areaBound := 16 * (pairs.length : Fraction.Rational) ^ 4 * error * magnitude
  { evidence := ⟨errorNonnegative, magnitudeNonnegative, errors, firstBound, secondBound⟩
    residual := residual
    residual_eq := rfl
    areaBound := areaBound
    areaBound_eq := rfl
    areaBound_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
          errorNonnegative)
      magnitudeNonnegative
    bounded := by
      change normSq (first.area - second.area) ≤ areaBound
      rw [← Norm.Basic.normSq_eq_canonical, first.area_eq, second.area_eq]
      exact IncrementAreaComparison.pathArea_difference_bound
        pairs errorNonnegative magnitudeNonnegative
        (by intro pair member; rw [Norm.Basic.normSq_eq_canonical]; exact errors pair member)
        (by intro pair member; rw [Norm.Basic.normSq_eq_canonical]; exact firstBound pair member)
        (by intro pair member; rw [Norm.Basic.normSq_eq_canonical]; exact secondBound pair member) }

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Any target covering the retained area bound covers the exact cached residual's squared norm. -/
theorem pay {pairs : List (Basic.Canonical × Basic.Canonical)}
    {error magnitude : Fraction.Rational} {first : FirstSummary pairs} {second : SecondSummary pairs}
    (comparison : Cached pairs error magnitude first second) {target : Fraction.Rational}
    (paid : comparison.areaBound ≤ target) : normSq comparison.residual ≤ target :=
  comparison.bounded.trans paid

end Cached

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Conjugating one bounded error and adding a coefficient-scaled second error costs twice one plus coefficient norm
squared. -/
theorem mixed_error (left right coefficient : Basic.Canonical)
    {allowance : Fraction.Rational} (leftBound : normSq left ≤ allowance)
    (rightBound : normSq right ≤ allowance) :
    normSq (conj left + coefficient * right) ≤
      2 * (1 + normSq coefficient) * allowance := by
  have estimate := Norm.Bounds.normSq_add_le_two (conj left) (coefficient * right)
  change Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj left + coefficient * right) ≤
    2 * (Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Basic.conj left) +
      Data.Gaussian.Norm.Basic.normSq (coefficient * right)) at estimate
  rw [Norm.Basic.normSq_conj, Norm.Basic.normSq_mul] at estimate
  simp only [Norm.Basic.normSq_eq_canonical] at estimate

  have inner : normSq left + normSq coefficient * normSq right ≤
      allowance + normSq coefficient * allowance :=
    Fraction.Order.Arithmetic.add_le_add_direct leftBound
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rightBound (Basic.Canonical.normSq_nonneg
        coefficient))
  exact estimate.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inner
    (by decide : (0 : Fraction.Rational) ≤ 2)).trans_eq (by ring1))

/-- Compose the original outward, opposite-sheet and return displacement bounds along their exact three-step chain. -/
theorem stem_chain (chartSheet sourceSheet sourceOtherSheet chartOtherSheet : Basic.Canonical)
    {outwardBudget oppositeBudget otherBudget : Fraction.Rational}
    (outward : normSq (sourceSheet - chartSheet) ≤ outwardBudget)
    (opposite : normSq (sourceSheet - sourceOtherSheet) ≤ oppositeBudget)
    (other : normSq (sourceOtherSheet - chartOtherSheet) ≤ otherBudget) :
    normSq (chartSheet - chartOtherSheet) ≤
      2 * (outwardBudget + 2 * (oppositeBudget + otherBudget)) := by
  have first : normSq (chartSheet - sourceSheet) ≤ outwardBudget := by
    rw [show chartSheet - sourceSheet = -(sourceSheet - chartSheet) by ring1, Basic.Canonical.normSq_neg]
    exact outward
  rw [← Norm.Basic.normSq_eq_canonical] at opposite other
  have middle := (Norm.Bounds.normSq_sub_le_via sourceSheet sourceOtherSheet chartOtherSheet).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct opposite
      other) (by decide))
  rw [← Norm.Basic.normSq_eq_canonical] at first ⊢
  exact (Norm.Bounds.normSq_sub_le_via chartSheet sourceSheet chartOtherSheet).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct first
      middle) (by decide))

end

open Purelib.Data.Rat in
/-- Three one-tenth target budgets pay the exact nested twofold stem-chain cost. -/
theorem stem_tenth_payment (target : Fraction.Rational) :
    2 * (target / 10 + 2 * (target / 10 + target / 10)) = target :=
  (by ring1 : 2 * (target / 10 + 2 * (target / 10 + target / 10)) = target / 10 * 10).trans
    (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Factor the allowance from the original fourth-power chart-area error weight. -/
theorem mixed_chart_weight (count : Nat) (coefficient : Basic.Canonical)
    (magnitude allowance : Fraction.Rational) :
    16 * (count : Fraction.Rational)^4 * (2 * (1 + normSq coefficient) * allowance) * (8 * magnitude + 2) =
      (32 * (1 + normSq coefficient) * (count : Fraction.Rational)^4 * (8 * magnitude + 2)) * allowance := by
  ring1

/-- Factor the allowance from the original fourth-power walk-area error weight. -/
theorem mixed_walk_weight (count : Nat) (coefficient : Basic.Canonical)
    (magnitude allowance : Fraction.Rational) :
    16 * (count : Fraction.Rational)^4 * (2 * (1 + normSq coefficient) * allowance) * (4 * magnitude) =
      (128 * (1 + normSq coefficient) * (count : Fraction.Rational)^4 * magnitude) * allowance := by
  ring1

end Purelib.Integration.Path.AreaComparison
