import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import Mathlib.Data.Nat.Choose.Basic

/-!
# Finite constructive binomial expansion

The bounded sum below is primitive recursion on a natural count.  The
binomial theorem is proved directly from Pascal's recursion for `Nat.choose`.
No `Finset`, infinite series, completed object, carrier enumeration, or choice
principle enters this project-owned proof.
-/

namespace RFAP

variable {K : Type*} [CommRing K]

/-- Constructive diagonal value of Pascal's triangle.  The corresponding
upstream convenience theorem currently carries a choice-bearing proof route,
so the finite development keeps this direct recursion. -/
theorem finite_choose_self : ∀ row : Nat, row.choose row = 1
  | 0 => rfl
  | row + 1 => by
      rw [Nat.choose_succ_succ, finite_choose_self row,
        Nat.choose_succ_self, Nat.add_zero]

/-- Constructive value immediately below Pascal's diagonal. -/
theorem finite_choose_succ_self_right : ∀ row : Nat,
    (row + 1).choose row = row + 1
  | 0 => rfl
  | row + 1 => by
      rw [Nat.choose_succ_succ, finite_choose_succ_self_right row,
        finite_choose_self]

/-- Constructive symmetry of Pascal's triangle in additive coordinates.
The corresponding upstream convenience theorem currently passes through a
choice-bearing factorial/division proof, so we retain the direct two-axis
Pascal induction needed by the finite developments. -/
theorem finite_choose_symm_add : ∀ left right : Nat,
    (left + right).choose left = (left + right).choose right
  | 0, right => by
      simp only [Nat.zero_add, Nat.choose_zero_right,
        finite_choose_self]
  | left + 1, 0 => by
      simp only [Nat.add_zero, finite_choose_self,
        Nat.choose_zero_right]
  | left + 1, right + 1 => by
      have leftPascal :
          ((left + right + 1) + 1).choose (left + 1) =
            (left + right + 1).choose left +
              (left + right + 1).choose (left + 1) :=
        Nat.choose_succ_succ' (left + right + 1) left
      have rightPascal :
          ((left + right + 1) + 1).choose (right + 1) =
            (left + right + 1).choose right +
              (left + right + 1).choose (right + 1) :=
        Nat.choose_succ_succ' (left + right + 1) right
      have firstSymmetry := finite_choose_symm_add left (right + 1)
      have secondSymmetry := finite_choose_symm_add (left + 1) right
      rw [show left + (right + 1) = left + right + 1 by omega0]
        at firstSymmetry
      rw [show left + 1 + right = left + right + 1 by omega0]
        at secondSymmetry
      rw [show (left + 1) + (right + 1) =
          (left + right + 1) + 1 by omega0,
        leftPascal, rightPascal, firstSymmetry, secondSymmetry,
        Nat.add_comm]

/-- Constructive symmetry of a requested binomial coefficient. -/
theorem finite_choose_symm {row index : Nat} (within : index ≤ row) :
    row.choose (row - index) = row.choose index := by
  have symmetry := finite_choose_symm_add index (row - index)
  rw [show index + (row - index) = row by omega0] at symmetry
  exact symmetry.symm

/-- Sum the first `count` values of `term`, by primitive recursion. -/
def finitePrefixSum : Nat → (Nat → K) → K
  | 0, _ => 0
  | count + 1, term =>
      term 0 + finitePrefixSum count (fun index => term (index + 1))

@[simp] theorem finitePrefixSum_zero (term : Nat → K) :
    finitePrefixSum 0 term = 0 := rfl

@[simp] theorem finitePrefixSum_succ (count : Nat) (term : Nat → K) :
    finitePrefixSum (count + 1) term =
      term 0 + finitePrefixSum count (fun index => term (index + 1)) := rfl

/-- A finite prefix of ones is its natural length cast into the ring. -/
theorem finitePrefixSum_one (count : Nat) :
    finitePrefixSum count (fun _ : Nat => (1 : K)) = (count : K) := by
  induction count with
  | zero => simp only [finitePrefixSum_zero, Nat.cast_zero]
  | succ count inductionHypothesis =>
      change 1 + finitePrefixSum count (fun _ : Nat => (1 : K)) =
        (count + 1 : Nat)
      rw [inductionHypothesis, Nat.cast_add, Nat.cast_one]
      ring1

/-- The sum of a finite prefix of zero values is zero. -/
theorem finitePrefixSum_zero_values (count : Nat) :
    finitePrefixSum count (fun _ : Nat => (0 : K)) = 0 := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      change 0 + finitePrefixSum count (fun _ : Nat => (0 : K)) = 0
      rw [inductionHypothesis, zero_add]

/-- Pointwise equality on the requested finite prefix preserves its sum. -/
theorem finitePrefixSum_congr
    (count : Nat) (first second : Nat → K)
    (equal : ∀ index, index < count → first index = second index) :
    finitePrefixSum count first = finitePrefixSum count second := by
  induction count generalizing first second with
  | zero => rfl
  | succ count inductionHypothesis =>
      change
        first 0 + finitePrefixSum count (fun index => first (index + 1)) =
          second 0 + finitePrefixSum count (fun index => second (index + 1))
      rw [equal 0 (by omega0)]
      apply congrArg (second 0 + ·)
      apply inductionHypothesis
      intro index indexBound
      exact equal (index + 1) (by omega0)

/-- Addition distributes through an explicitly bounded prefix sum. -/
theorem finitePrefixSum_add
    (count : Nat) (first second : Nat → K) :
    finitePrefixSum count (fun index => first index + second index) =
      finitePrefixSum count first + finitePrefixSum count second := by
  induction count generalizing first second with
  | zero => simp only [finitePrefixSum_zero, zero_add]
  | succ count inductionHypothesis =>
      change
        first 0 + second 0 +
            finitePrefixSum count
              (fun index => first (index + 1) + second (index + 1)) =
          first 0 + finitePrefixSum count (fun index => first (index + 1)) +
            (second 0 +
              finitePrefixSum count (fun index => second (index + 1)))
      rw [inductionHypothesis]
      ring1

/-- Two explicitly bounded primitive-recursive sums may be interchanged. -/
theorem finitePrefixSum_swap
    (firstCount secondCount : Nat) (term : Nat → Nat → K) :
    finitePrefixSum firstCount (fun first =>
        finitePrefixSum secondCount (fun second => term first second)) =
      finitePrefixSum secondCount (fun second =>
        finitePrefixSum firstCount (fun first => term first second)) := by
  induction firstCount generalizing term with
  | zero =>
      calc
        finitePrefixSum 0 (fun first =>
            finitePrefixSum secondCount (fun second => term first second)) =
          0 := rfl
        _ = finitePrefixSum secondCount (fun _ : Nat => (0 : K)) :=
          (finitePrefixSum_zero_values secondCount).symm
        _ = finitePrefixSum secondCount (fun second =>
            finitePrefixSum 0 (fun first => term first second)) := rfl
  | succ firstCount inductionHypothesis =>
      change
        finitePrefixSum secondCount (fun second => term 0 second) +
            finitePrefixSum firstCount (fun first =>
              finitePrefixSum secondCount (fun second =>
                term (first + 1) second)) =
          finitePrefixSum secondCount (fun second =>
            term 0 second + finitePrefixSum firstCount (fun first =>
              term (first + 1) second))
      rw [inductionHypothesis, ← finitePrefixSum_add]

/-- A common left factor can be extracted from a bounded prefix sum. -/
theorem finitePrefixSum_mul_left
    (count : Nat) (factor : K) (term : Nat → K) :
    finitePrefixSum count (fun index => factor * term index) =
      factor * finitePrefixSum count term := by
  induction count generalizing term with
  | zero =>
      simp only [finitePrefixSum_zero, mul_zero]
  | succ count inductionHypothesis =>
      change
        factor * term 0 +
            finitePrefixSum count
              (fun index => factor * term (index + 1)) =
          factor *
            (term 0 +
              finitePrefixSum count (fun index => term (index + 1)))
      rw [inductionHypothesis]
      ring1

/-- Negation distributes through an explicitly bounded prefix sum. -/
theorem finitePrefixSum_neg (count : Nat) (term : Nat → K) :
    finitePrefixSum count (fun index => -term index) =
      -finitePrefixSum count term := by
  calc
    finitePrefixSum count (fun index => -term index) =
        finitePrefixSum count (fun index => (-1 : K) * term index) := by
          apply finitePrefixSum_congr
          intro index indexBound
          ring1
    _ = (-1 : K) * finitePrefixSum count term :=
      finitePrefixSum_mul_left count (-1) term
    _ = -finitePrefixSum count term := by ring1

/-- Subtraction distributes through an explicitly bounded prefix sum. -/
theorem finitePrefixSum_sub
    (count : Nat) (first second : Nat → K) :
    finitePrefixSum count (fun index => first index - second index) =
      finitePrefixSum count first - finitePrefixSum count second := by
  calc
    finitePrefixSum count (fun index => first index - second index) =
        finitePrefixSum count (fun index => first index + -second index) := by
          apply finitePrefixSum_congr
          intro index indexBound
          ring1
    _ = finitePrefixSum count first +
        finitePrefixSum count (fun index => -second index) :=
      finitePrefixSum_add count first (fun index => -second index)
    _ = finitePrefixSum count first - finitePrefixSum count second := by
      rw [finitePrefixSum_neg]
      ring1

/-- Extend a bounded prefix by its final term. -/
theorem finitePrefixSum_succ_last
    (count : Nat) (term : Nat → K) :
    finitePrefixSum (count + 1) term =
      finitePrefixSum count term + term count := by
  induction count generalizing term with
  | zero =>
      simp only [finitePrefixSum_zero, finitePrefixSum_succ, zero_add,
        add_zero]
  | succ count inductionHypothesis =>
      change
        term 0 +
            finitePrefixSum (count + 1) (fun index => term (index + 1)) =
          term 0 +
              finitePrefixSum count (fun index => term (index + 1)) +
            term (count + 1)
      rw [inductionHypothesis]
      ring1

/-- Reversing an explicitly bounded prefix does not change its sum.  The
right-hand side requests only the indices `count - 1, …, 0`; no list or
completed sequence is constructed. -/
theorem finitePrefixSum_reverse
    (count : Nat) (term : Nat → K) :
    finitePrefixSum count term =
      finitePrefixSum count (fun index => term (count - 1 - index)) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [finitePrefixSum_succ_last]
      change
        finitePrefixSum count term + term count =
          term count +
            finitePrefixSum count
              (fun index => term (count - (index + 1)))
      have reversedTail :
          finitePrefixSum count
              (fun index => term (count - (index + 1))) =
            finitePrefixSum count
              (fun index => term (count - 1 - index)) := by
        apply finitePrefixSum_congr
        intro index indexBound
        congr 1
        omega0
      rw [reversedTail, ← inductionHypothesis]
      ring1

/-- Group the first `2 * count` terms into adjacent pairs. -/
theorem finitePrefixSum_pairs
    (count : Nat) (term : Nat → K) :
    finitePrefixSum (count + count) term =
      finitePrefixSum count
        (fun index => term (index + index) + term (index + index + 1)) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [show Nat.succ count + Nat.succ count =
        (count + count + 1) + 1 by omega0]
      rw [finitePrefixSum_succ_last, finitePrefixSum_succ_last]
      rw [finitePrefixSum_succ_last, inductionHypothesis]
      ring1

/-- Group adjacent pairs and retain the one final even-indexed term. -/
theorem finitePrefixSum_pairs_and_last
    (count : Nat) (term : Nat → K) :
    finitePrefixSum (count + count + 1) term =
      finitePrefixSum count
          (fun index => term (index + index) + term (index + index + 1)) +
        term (count + count) := by
  rw [finitePrefixSum_succ_last, finitePrefixSum_pairs]

/-- The source-ordered finite binomial sum, with `x` descending from exponent
`n` and `y` ascending from exponent zero. -/
def finiteBinomialExpansion (exponent : Nat) (x y : K) : K :=
  finitePrefixSum (exponent + 1) (fun index =>
    y ^ index * x ^ (exponent - index) *
      (exponent.choose index : K))

/-- The binomial theorem as an explicitly bounded primitive-recursive sum. -/
theorem finite_binomial_theorem (exponent : Nat) (x y : K) :
    (x + y) ^ exponent = finiteBinomialExpansion exponent x y := by
  let term : Nat → Nat → K := fun row index =>
    y ^ index * x ^ (row - index) * (row.choose index : K)
  have firstTerm : ∀ row : Nat, term row 0 = x ^ row := by
    intro row
    simp only [term, pow_zero, Nat.sub_zero, Nat.choose_zero_right,
      Nat.cast_one, one_mul, mul_one]
  have afterLastTerm : ∀ row : Nat, term row (row + 1) = 0 := by
    intro row
    simp only [term, Nat.choose_succ_self, Nat.cast_zero, mul_zero]
  have pascalStep : ∀ row index : Nat, index ≤ row →
      term (row + 1) (index + 1) =
        y * term row index + x * term row (index + 1) := by
    intro row index indexBound
    dsimp only [term]
    rw [Nat.choose_succ_succ', Nat.cast_add, mul_add]
    congr 1
    · rw [pow_succ' y, Nat.succ_sub_succ]
      ring1
    · by_cases lastIndex : index = row
      · rw [lastIndex, Nat.choose_succ_self, Nat.cast_zero]
        ring1
      · rw [Nat.succ_sub (Nat.lt_of_le_of_ne indexBound lastIndex),
          pow_succ' x]
        ring1
  induction exponent with
  | zero =>
      unfold finiteBinomialExpansion
      simp only [pow_zero, finitePrefixSum_succ, finitePrefixSum_zero,
        Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, mul_one,
        add_zero]
  | succ exponent inductionHypothesis =>
      have shiftedLast :
          finitePrefixSum (exponent + 1)
              (fun index => term exponent (index + 1)) =
            finitePrefixSum exponent
              (fun index => term exponent (index + 1)) := by
        rw [finitePrefixSum_succ_last,
          afterLastTerm exponent, add_zero]
      have previousExpansion :
          finiteBinomialExpansion exponent x y =
            x ^ exponent +
              finitePrefixSum exponent
                (fun index => term exponent (index + 1)) := by
        unfold finiteBinomialExpansion
        change finitePrefixSum (exponent + 1) (term exponent) = _
        rw [finitePrefixSum_succ, firstTerm]
      have previousSum :
          finitePrefixSum (exponent + 1) (term exponent) =
            finiteBinomialExpansion exponent x y := by
        unfold finiteBinomialExpansion
        rfl
      have nextExpansion :
          finiteBinomialExpansion (Nat.succ exponent) x y =
            x ^ Nat.succ exponent +
              y * finitePrefixSum (exponent + 1) (term exponent) +
              x * finitePrefixSum (exponent + 1)
                (fun index => term exponent (index + 1)) := by
        unfold finiteBinomialExpansion
        change finitePrefixSum (Nat.succ exponent + 1)
          (term (Nat.succ exponent)) = _
        rw [show Nat.succ exponent + 1 = (exponent + 1) + 1 by omega0,
          finitePrefixSum_succ, firstTerm]
        have summedPascal := finitePrefixSum_congr
          (K := K) (exponent + 1)
          (fun index => term (exponent + 1) (index + 1))
          (fun index =>
            y * term exponent index + x * term exponent (index + 1))
          (by
            intro index indexBound
            exact pascalStep exponent index (by omega0))
        rw [summedPascal, finitePrefixSum_add,
          finitePrefixSum_mul_left, finitePrefixSum_mul_left]
        ring1
      calc
        (x + y) ^ Nat.succ exponent =
            (x + y) ^ exponent * (x + y) := by
          rw [pow_succ]
        _ = finiteBinomialExpansion exponent x y * (x + y) := by
          rw [inductionHypothesis]
        _ = finiteBinomialExpansion (Nat.succ exponent) x y := by
          rw [nextExpansion, previousSum, previousExpansion, shiftedLast,
            pow_succ]
          ring1

end RFAP
