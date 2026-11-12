module

public import Purelib.Curves.Legendre.Monodromy.StandardWords
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Int.Order
import Purelib.Data.Nat.Order
import Purelib.Data.List.Append
import Purelib.LinearAlgebra.Matrix.Integral.Two
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Topology.Knot.Braid.Word.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # Checked words for the exact signed standard-loop matrix image

Right multiplication by signed squared generators reduces the larger
magnitude in the first row. Its odd/even parity excludes equal magnitudes,
so the sum decreases strictly. The triangular endpoint is an even shear.
Reversing the retained reduction letters reconstructs the original matrix
in the original traversal order, without adjoining negative identity.
-/

namespace Purelib.Curves.Legendre.Monodromy.StandardWords

open Purelib
open Purelib.Data.Int
open Purelib.LinearAlgebra.Matrix
open Purelib.LinearAlgebra.Matrix.Integral
open Purelib.Topology.Knot
open Purelib.Topology.Knot.Braid.ThreeStrand.Integral

/-- A single standard letter is exactly the square of its signed braid generator. -/
private theorem singleton (letter : Braid.Generator 3) : matrix [letter] =
    Multiplication.mul (Generators.generatorMatrix letter) (Generators.generatorMatrix letter) :=
  (matrix_cons letter []).trans (Multiplication.identity_mul_int _)

/-- A standard head multiplies its actual singleton matrix on the right. -/
private theorem cons_singleton (letter : Braid.Generator 3) (word : Braid.Word 3) :
    matrix (letter :: word) = Multiplication.mul (matrix word) (matrix [letter]) :=
  (matrix_cons letter word).trans (congrArg (Multiplication.mul (matrix word)) (singleton letter).symm)

/-- The positive zero index has the original signed even upper shear. -/
private theorem positive_zero : matrix [(⟨0, .positive⟩ : Braid.Generator 3)] = Two.matrix₂ 1 (-2) 0 1 := by
  rewrite [singleton]
  change Multiplication.mul Generators.lowerPositiveMatrix Generators.lowerPositiveMatrix = _
  unfold Generators.lowerPositiveMatrix
  rewrite [Two.mul_matrix₂]
  rfl

/-- The positive one index has the original signed even lower shear. -/
private theorem positive_one : matrix [(⟨1, .positive⟩ : Braid.Generator 3)] = Two.matrix₂ 1 0 2 1 := by
  rewrite [singleton]
  change Multiplication.mul Generators.upperPositiveMatrix Generators.upperPositiveMatrix = _
  unfold Generators.upperPositiveMatrix
  rewrite [Two.mul_matrix₂]
  rfl

/-- The negative zero letter has the inverse signed even upper shear. -/
private theorem negative_zero : matrix [(⟨0, .negative⟩ : Braid.Generator 3)] = Two.matrix₂ 1 2 0 1 := by
  rewrite [singleton]
  change Multiplication.mul Generators.lowerNegativeMatrix Generators.lowerNegativeMatrix = _
  unfold Generators.lowerNegativeMatrix
  rewrite [Two.mul_matrix₂]
  rfl

/-- The negative one letter has the inverse signed even lower shear. -/
private theorem negative_one : matrix [(⟨1, .negative⟩ : Braid.Generator 3)] = Two.matrix₂ 1 0 (-2) 1 := by
  rewrite [singleton]
  change Multiplication.mul Generators.upperNegativeMatrix Generators.upperNegativeMatrix = _
  unfold Generators.upperNegativeMatrix
  rewrite [Two.mul_matrix₂]
  rfl

/-- The positive zero block subtracts twice the first column from the second. -/
private theorem right_zero_positive (a b c d : Int) :
    Multiplication.mul (Two.matrix₂ a b c d) (matrix [(⟨0, .positive⟩ : Braid.Generator 3)]) =
      Two.matrix₂ a (b - 2 * a) c (d - 2 * c) := by
  rewrite [positive_zero, Two.mul_matrix₂]
  simp only [Arithmetic.mul_one, Int.mul_zero, Int.add_zero]
  exact congrArg₂ (fun first last => Two.matrix₂ a first c last) (by ring1) (by ring1)

/-- The negative zero block adds twice the first column to the second. -/
private theorem right_zero_negative (a b c d : Int) :
    Multiplication.mul (Two.matrix₂ a b c d) (matrix [(⟨0, .negative⟩ : Braid.Generator 3)]) =
      Two.matrix₂ a (b + 2 * a) c (d + 2 * c) := by
  rewrite [negative_zero, Two.mul_matrix₂]
  simp only [Arithmetic.mul_one, Int.mul_zero, Int.add_zero]
  exact congrArg₂ (fun first last => Two.matrix₂ a first c last) (by ring1) (by ring1)

/-- The positive one block adds twice the second column to the first. -/
private theorem right_one_positive (a b c d : Int) :
    Multiplication.mul (Two.matrix₂ a b c d) (matrix [(⟨1, .positive⟩ : Braid.Generator 3)]) =
      Two.matrix₂ (a + 2 * b) b (c + 2 * d) d := by
  rewrite [positive_one, Two.mul_matrix₂]
  simp only [Arithmetic.mul_one, Int.mul_zero, Int.zero_add]
  exact congrArg₂ (fun first last => Two.matrix₂ first b last d) (by ring1) (by ring1)

/-- The negative one block subtracts twice the second column from the first. -/
private theorem right_one_negative (a b c d : Int) :
    Multiplication.mul (Two.matrix₂ a b c d) (matrix [(⟨1, .negative⟩ : Braid.Generator 3)]) =
      Two.matrix₂ (a - 2 * b) b (c - 2 * d) d := by
  rewrite [negative_one, Two.mul_matrix₂]
  simp only [Arithmetic.mul_one, Int.mul_zero, Int.zero_add]
  exact congrArg₂ (fun first last => Two.matrix₂ first b last d) (by ring1) (by ring1)

/-- Opposite first-row parities exclude a tie of absolute values. -/
private theorem magnitudes_ne (a b : Int) (odd : a % 4 = 1) (even : b % 2 = 0) :
    a.natAbs ≠ b.natAbs := by
  cases a with
  | ofNat a =>
      change (a : Int) % 4 = 1 at odd
      cases b with
      | ofNat b =>
          change (b : Int) % 2 = 0 at even
          change a ≠ b
          intro equal
          omega0 -splitNatAbs
      | negSucc b =>
          change (-((b + 1 : Nat) : Int)) % 2 = 0 at even
          change a ≠ b + 1
          intro equal
          omega0 -splitNatAbs
  | negSucc a =>
      change (-((a + 1 : Nat) : Int)) % 4 = 1 at odd
      cases b with
      | ofNat b =>
          change (b : Int) % 2 = 0 at even
          change a + 1 ≠ b
          intro equal
          omega0 -splitNatAbs
      | negSucc b =>
          change (-((b + 1 : Nat) : Int)) % 2 = 0 at even
          change a + 1 ≠ b + 1
          intro equal
          omega0 -splitNatAbs

/-- Subtracting twice a smaller nonzero integer on the same side strictly decreases magnitude. -/
private theorem subtract_decreases (x y : Int) (nonzero : y ≠ 0) (smaller : y.natAbs < x.natAbs)
    (sameSide : (0 ≤ x ∧ 0 ≤ y) ∨ (x < 0 ∧ y < 0)) : (x - 2 * y).natAbs < x.natAbs := by
  have bounds : -(x.natAbs : Int) < x - 2 * y ∧ x - 2 * y < (x.natAbs : Int) := by
    rcases sameSide with positive | negative
    · have left := Order.natAbs_of_nonneg positive.1
      have right := Order.natAbs_of_nonneg positive.2
      have signedSmaller := Order.natCast_lt_iff.mpr smaller
      rewrite [left, right] at signedSmaller
      rewrite [left]
      clear smaller left right
      constructor <;> omega0 -splitNatAbs
    · have xNotPositive : ¬0 < x := by clear smaller; omega0 -splitNatAbs
      have yNotPositive : ¬0 < y := by clear smaller; omega0 -splitNatAbs
      have left := Order.natAbs_of_not_pos xNotPositive
      have right := Order.natAbs_of_not_pos yNotPositive
      have signedSmaller := Order.natCast_lt_iff.mpr smaller
      rewrite [left, right] at signedSmaller
      rewrite [left]
      clear smaller left right
      constructor <;> omega0 -splitNatAbs
  cases result : x - 2 * y with
  | ofNat value =>
      have upper := bounds.2
      rewrite [result] at upper
      exact Order.natCast_lt_iff.mp upper
  | negSucc value =>
      have lower := bounds.1
      rewrite [result] at lower
      change -(x.natAbs : Int) < -((value + 1 : Nat) : Int) at lower
      change value + 1 < x.natAbs
      omega0 -splitNatAbs

/-- Adding twice a smaller nonzero integer on the opposite side strictly decreases magnitude. -/
private theorem add_decreases (x y : Int) (nonzero : y ≠ 0) (smaller : y.natAbs < x.natAbs)
    (different : ¬((0 ≤ x ∧ 0 ≤ y) ∨ (x < 0 ∧ y < 0))) : (x + 2 * y).natAbs < x.natAbs := by
  have negativeSame : (0 ≤ x ∧ 0 ≤ -y) ∨ (x < 0 ∧ -y < 0) := by
    by_cases positive : 0 ≤ x
    · have impossible : ¬0 ≤ y := fun nonnegative => different (Or.inl ⟨positive, nonnegative⟩)
      have negated : 0 ≤ -y := by clear different; omega0 -splitNatAbs
      exact Or.inl ⟨positive, negated⟩
    · have negative : x < 0 := by clear different; omega0 -splitNatAbs
      have impossible : ¬y < 0 := fun negativeY => different (Or.inr ⟨negative, negativeY⟩)
      have negated : -y < 0 := by clear different; omega0 -splitNatAbs
      exact Or.inr ⟨negative, negated⟩
  have negNonzero : -y ≠ 0 := by intro equal; apply nonzero; omega0 -splitNatAbs
  have magnitude : (-y).natAbs = y.natAbs := by
    cases y with
    | ofNat value => exact Int.natAbs_negOfNat value
    | negSucc value => rfl
  have reduced := subtract_decreases x (-y) negNonzero (magnitude.trans_lt smaller) negativeSame
  exact Eq.mp (congrArg (fun value : Int => value.natAbs < x.natAbs)
    (show x - 2 * -y = x + 2 * y by ring1)) reduced

/-- Choose the signed block that reduces the larger first-row magnitude. -/
private def reducingLetter (a b : Int) : Braid.Generator 3 :=
  if a.natAbs < b.natAbs then
    ⟨0, if (0 ≤ a ∧ 0 ≤ b) ∨ (a < 0 ∧ b < 0) then .positive else .negative⟩
  else
    ⟨1, if (0 ≤ a ∧ 0 ≤ b) ∨ (a < 0 ∧ b < 0) then .negative else .positive⟩

/-- The original first-row magnitude sum is a finite descent bound. -/
private def height (value : IntegralMatrix) : Nat := (value 0 0).natAbs + (value 0 1).natAbs

/-- The chosen actual squared block decreases the same first-row height. -/
private theorem reducingLetter_decreases (a b c d : Int) (odd : a % 4 = 1) (even : b % 2 = 0)
    (nonzero : b ≠ 0) :
    height (Multiplication.mul (Two.matrix₂ a b c d) (matrix [reducingLetter a b])) <
      a.natAbs + b.natAbs := by
  have aNonzero : a ≠ 0 := by intro equal; rewrite [equal] at odd; contradiction
  have distinct := magnitudes_ne a b odd even
  unfold reducingLetter
  split
  · rename_i smaller
    split
    · rename_i sameSide
      have swapped : (0 ≤ b ∧ 0 ≤ a) ∨ (b < 0 ∧ a < 0) :=
        sameSide.elim (fun pair => Or.inl ⟨pair.2, pair.1⟩) (fun pair => Or.inr ⟨pair.2, pair.1⟩)
      have decrease := subtract_decreases b a aNonzero smaller swapped
      rewrite [right_zero_positive]
      change a.natAbs + (b - 2 * a).natAbs < a.natAbs + b.natAbs
      omega0 -splitNatAbs
    · rename_i different
      have swapped : ¬((0 ≤ b ∧ 0 ≤ a) ∨ (b < 0 ∧ a < 0)) := fun same =>
        different (same.elim (fun pair => Or.inl ⟨pair.2, pair.1⟩) (fun pair => Or.inr ⟨pair.2, pair.1⟩))
      have decrease := add_decreases b a aNonzero smaller swapped
      rewrite [right_zero_negative]
      change a.natAbs + (b + 2 * a).natAbs < a.natAbs + b.natAbs
      omega0 -splitNatAbs
  · rename_i notSmaller
    have smaller : b.natAbs < a.natAbs := by omega0 -splitNatAbs
    split
    · rename_i sameSide
      have decrease := subtract_decreases a b nonzero smaller sameSide
      rewrite [right_one_negative]
      change (a - 2 * b).natAbs + b.natAbs < a.natAbs + b.natAbs
      omega0 -splitNatAbs
    · rename_i different
      have decrease := add_decreases a b nonzero smaller different
      rewrite [right_one_positive]
      change (a + 2 * b).natAbs + b.natAbs < a.natAbs + b.natAbs
      omega0 -splitNatAbs

/-- Repeated signed one letters evaluate to their original even lower shear. -/
private theorem repeated_one (sign : Braid.CrossingSign) (count : Nat) :
    matrix (List.replicate count (⟨1, sign⟩ : Braid.Generator 3)) =
      Two.matrix₂ 1 0 (match sign with | .positive => 2 * (count : Int) | .negative => -2 * (count : Int)) 1 := by
  cases sign
  · change matrix (List.replicate count (⟨1, .positive⟩ : Braid.Generator 3)) =
      Two.matrix₂ 1 0 (2 * (count : Int)) 1
    induction count with
    | zero => rfl
    | succ count prior =>
        rewrite [List.replicate_succ, cons_singleton, prior, right_one_positive]
        simp only [Int.mul_zero, Int.add_zero, Arithmetic.mul_one]
        exact congrArg (fun entry => Two.matrix₂ 1 0 entry 1) (by rewrite [Int.natCast_succ]; ring1)
  · change matrix (List.replicate count (⟨1, .negative⟩ : Braid.Generator 3)) =
      Two.matrix₂ 1 0 (-2 * (count : Int)) 1
    induction count with
    | zero => rfl
    | succ count prior =>
        rewrite [List.replicate_succ, cons_singleton, prior, right_one_negative]
        simp only [Int.mul_zero, Arithmetic.sub_zero, Arithmetic.mul_one]
        exact congrArg (fun entry => Two.matrix₂ 1 0 entry 1) (by rewrite [Int.natCast_succ]; ring1)

/-- An even lower shear has a directly constructed signed one-letter word. -/
private def lowerWord (c : Int) (even : c % 2 = 0) :
    {word : Braid.Word 3 // matrix word = Two.matrix₂ 1 0 c 1} :=
  match c with
  | .ofNat value =>
      ⟨List.replicate (value / 2) (⟨1, .positive⟩ : Braid.Generator 3),
        (repeated_one .positive (value / 2)).trans
          (congrArg (fun entry => Two.matrix₂ 1 0 entry 1)
            (show (2 : Int) * ((value / 2 : Nat) : Int) = (value : Int) by
              change ((value % 2 : Nat) : Int) = 0 at even
              omega0 -splitNatAbs))⟩
  | .negSucc value =>
      ⟨List.replicate ((value + 1) / 2) (⟨1, .negative⟩ : Braid.Generator 3),
        (repeated_one .negative ((value + 1) / 2)).trans
          (congrArg (fun entry => Two.matrix₂ 1 0 entry 1)
            (show (-2 : Int) * (((value + 1) / 2 : Nat) : Int) = Int.negSucc value by
              change (-((value + 1 : Nat) : Int)) % 2 = 0 at even
              omega0 -splitNatAbs))⟩

/-- Determinant and signed diagonal congruence identify the triangular endpoint as an even lower shear. -/
private def triangularWord (a c d : Int) (valid : SignedCongruence (Two.matrix₂ a 0 c d)) :
    {word : Braid.Word 3 // matrix word = Two.matrix₂ a 0 c d} := by
  have determinant : a * d = 1 := by
    have original := valid.1
    change a * d - 0 * c = 1 at original
    rewrite [Arithmetic.zero_mul, Arithmetic.sub_zero] at original
    exact original
  have magnitude : a.natAbs * d.natAbs = 1 :=
    (Arithmetic.natAbs_mul a d).symm.trans (congrArg Int.natAbs determinant)
  have unit : a.natAbs = 1 := by
    cases left : a.natAbs with
    | zero => rewrite [left, Nat.zero_mul] at magnitude; contradiction
    | succ left =>
        cases right : d.natAbs with
        | zero => rewrite [right, Nat.mul_zero] at magnitude; contradiction
        | succ right =>
            rewrite [left, right, Nat.succ_mul, Nat.mul_succ] at magnitude
            omega0 -splitNatAbs
  have diagonal : a % 4 = 1 := valid.2.1
  have first : a = 1 := by
    cases a with
    | ofNat a => exact congrArg Int.ofNat unit
    | negSucc a =>
        change a + 1 = 1 at unit
        change (-((a + 1 : Nat) : Int)) % 4 = 1 at diagonal
        omega0 -splitNatAbs
  have last : d = 1 := by rewrite [first, Int.one_mul] at determinant; exact determinant
  let result := lowerWord c valid.2.2.2.1
  exact ⟨result.val, result.property.trans (congrArg₂ (fun x y => Two.matrix₂ x 0 c y) first.symm last.symm)⟩

/-- A word for a right-reduced matrix reconstructs its original matrix by prepending the inverse letter. -/
private theorem undo (value : IntegralMatrix) (letter : Braid.Generator 3) (word : Braid.Word 3)
    (same : matrix word = Multiplication.mul value (matrix [letter])) :
    matrix (letter.reverse :: word) = value := by
  have cancel := (matrix_inverse_identities [letter]).2
  change Multiplication.mul (matrix [letter]) (matrix [letter.reverse]) = Multiplication.identity at cancel
  exact (cons_singleton letter.reverse word).trans
    ((congrArg (fun reduced => Multiplication.mul reduced (matrix [letter.reverse])) same).trans
      ((Multiplication.mul_assoc _ _ _).trans
        ((congrArg (Multiplication.mul value) cancel).trans (Multiplication.mul_identity_int value))))

/-- Reconstruct an integral matrix within its proved finite first-row descent bound. -/
private def reconstruct : (fuel : Nat) → (value : IntegralMatrix) → SignedCongruence value →
    height value ≤ fuel → {word : Braid.Word 3 // matrix word = value}
  | 0, value, valid, bounded => by
      have zero : value 0 1 = 0 := by
        unfold height at bounded
        have magnitude : (value 0 1).natAbs = 0 :=
          Nat.eq_zero_of_le_zero (Nat.le_of_add_left_le bounded)
        cases entry : value 0 1 with
        | ofNat entryValue =>
            have entryZero : entryValue = 0 := (congrArg Int.natAbs entry).symm.trans magnitude
            exact congrArg Int.ofNat entryZero
        | negSucc entryValue =>
            have impossible : entryValue + 1 = 0 := (congrArg Int.natAbs entry).symm.trans magnitude
            exact Nat.noConfusion impossible
      have display : Two.matrix₂ (value 0 0) 0 (value 1 0) (value 1 1) = value :=
        (congrArg (fun b => Two.matrix₂ (value 0 0) b (value 1 0) (value 1 1)) zero.symm).trans
          (Two.matrix₂_entries value)
      let result := triangularWord (value 0 0) (value 1 0) (value 1 1)
        (Eq.mpr (congrArg SignedCongruence display) valid)
      exact ⟨result.val, result.property.trans display⟩
  | fuel + 1, value, valid, bounded =>
      if zero : value 0 1 = 0 then
        let display : Two.matrix₂ (value 0 0) 0 (value 1 0) (value 1 1) = value :=
          (congrArg (fun b => Two.matrix₂ (value 0 0) b (value 1 0) (value 1 1)) zero.symm).trans
            (Two.matrix₂_entries value)
        let result := triangularWord (value 0 0) (value 1 0) (value 1 1)
          (Eq.mpr (congrArg SignedCongruence display) valid)
        ⟨result.val, result.property.trans display⟩
      else
        let letter := reducingLetter (value 0 0) (value 0 1)
        let next := Multiplication.mul value (matrix [letter])
        have nextValid : SignedCongruence next :=
          Eq.mpr (congrArg SignedCongruence (congrArg (Multiplication.mul value) (singleton letter)))
            (congruence_block value valid letter)
        have smaller : height next < height value :=
          Eq.mp (congrArg (fun displayed => height (Multiplication.mul displayed (matrix [letter])) < height value)
            (Two.matrix₂_entries value))
            (reducingLetter_decreases _ _ _ _ valid.2.1 valid.2.2.1 zero)
        let result := reconstruct fuel next nextValid (Nat.le_of_succ_le_succ (Nat.le_trans smaller bounded))
        ⟨letter.reverse :: result.val, undo value letter result.val result.property⟩

public section

/-- Return a finite signed standard-loop word and its exact original integral matrix equality.

The supplied decidable congruences are sufficient as well as necessary.
The algorithm uses its own first-row magnitude sum as the finite bound,
retains the signed lift and evaluates through the original doubled braid
interpreter. No projective quotient or assumed Gamma(2) surjectivity is used.
-/
def ofMatrix (value : IntegralMatrix) (valid : SignedCongruence value) :
    {word : Braid.Word 3 // matrix word = value} :=
  reconstruct (height value) value valid (Nat.le_refl _)

/-- The returned word's actual doubled braid expansion has the same checked original matrix. -/
theorem ofMatrix_braid (value : IntegralMatrix) (valid : SignedCongruence value) :
    Words.wordMatrix (braid (ofMatrix value valid).val) = value := (ofMatrix value valid).property

/-- The decidable signed congruences describe exactly the generated integral standard-loop image. -/
theorem image_iff (value : IntegralMatrix) : (∃ word : Braid.Word 3, matrix word = value) ↔ SignedCongruence value := by
  constructor
  · rintro ⟨word, same⟩
    exact Eq.mp (congrArg SignedCongruence same) (signedCongruence word)
  · intro valid
    exact ⟨(ofMatrix value valid).val, (ofMatrix value valid).property⟩

end

end Purelib.Curves.Legendre.Monodromy.StandardWords
