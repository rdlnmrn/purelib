module

public import Purelib.Polynomial.Dense.Roots.Bank.Evaluation
public import Purelib.Polynomial.Recurrence.Mode.Algebra
public import Purelib.Data.List.Erase.Index
import Purelib.Data.List.Map
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# First derivatives of original simple-root products

At an original indexed root, the same ordered product's first mode coefficient
is the product of all the other displayed differences. Original occurrences
are removed by their bounded positions, without identifying equal root values
or assuming any difference is a unit.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Product

open Purelib.Polynomial.Dense.Basic
open Purelib.Polynomial.Recurrence.Mode
open Purelib.Data

variable {K : Type*} [CommRing K] [DecidableEq K]

/-- A displayed multiplicity-one block evaluates to the original root difference. -/
private theorem block_eval_one (block : Block K) (simple : block.multiplicity = 1) (point : K) :
    block.polynomial.eval point = point - block.point := by
  have reading := Block.eval_map block id rfl (fun _ _ same => same) rfl
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) point
  rw [Dense.Map.map_id, simple, pow_one] at reading
  exact reading

/-- A displayed multiplicity-one block has original first mode coefficient one. -/
private theorem block_firstJet_one (block : Block K) (simple : block.multiplicity = 1) (point : K) :
    coefficientRow block.polynomial.coeffs point 1 0 = 1 := by
  have represented : block.polynomial =
      (⟨[1, -block.point]⟩ : DensePolynomial K) * DensePolynomial.constant 1 := by
    unfold Block.polynomial
    rw [simple]
    rfl
  rw [represented, coefficientRow_mul_first, DensePolynomial.eval_constant]
  have linear : coefficientRow [1, -block.point] point 1 0 = 1 := by
    change 1 * entry point 1 1 + ((-block.point) * entry point 1 0 + 0) = 1
    rw [entry_start, entry_before point 1 0 (Nat.zero_lt_succ 0), one_mul, mul_zero, zero_add, add_zero]
  have constant : coefficientRow (DensePolynomial.constant (1 : K)).coeffs point 1 0 = 0 := by
    change 1 * entry point 1 0 + 0 = 0
    rw [entry_before point 1 0 (Nat.zero_lt_succ 0), mul_zero, zero_add]
  rw [linear, constant, mul_one, mul_zero, add_zero]

/-- An original ordered simple-block product evaluates as the same ordered scalar differences. -/
theorem eval_simple (blocks : List (Block K))
    (simple : ∀ index : Fin blocks.length, (blocks[index.val]'index.isLt).multiplicity = 1) (point : K) :
    (Roots.product blocks).eval point = (blocks.map (fun block => point - block.point)).prod := by
  induction blocks with
  | nil => exact DensePolynomial.eval_constant 1 point
  | cons block remaining previous =>
      have head := simple ⟨0, Nat.zero_lt_succ remaining.length⟩
      have tail : ∀ index : Fin remaining.length, (remaining[index.val]'index.isLt).multiplicity = 1 :=
        fun index => simple index.succ
      change (block.polynomial * Roots.product remaining).eval point =
        (point - block.point) * (remaining.map (fun other => point - other.point)).prod
      rw [DensePolynomial.eval_mul, block_eval_one block head, previous tail]

/-- Each original indexed simple factor makes that same ordered product vanish at its displayed root. -/
theorem eval_at (blocks : List (Block K))
    (simple : ∀ index : Fin blocks.length, (blocks[index.val]'index.isLt).multiplicity = 1)
    (index : Fin blocks.length) : (Roots.product blocks).eval (blocks[index.val]'index.isLt).point = 0 := by
  induction blocks with
  | nil => exact Fin.elim0 index
  | cons block remaining previous =>
      have head := simple ⟨0, Nat.zero_lt_succ remaining.length⟩
      have tail : ∀ index : Fin remaining.length, (remaining[index.val]'index.isLt).multiplicity = 1 :=
        fun index => simple index.succ
      rcases index with ⟨position, bound⟩
      cases position with
      | zero =>
          change (block.polynomial * Roots.product remaining).eval block.point = 0
          rw [DensePolynomial.eval_mul, block_eval_one block head, sub_self, zero_mul]
      | succ position =>
          let retained : Fin remaining.length := ⟨position, Nat.lt_of_succ_lt_succ bound⟩
          change (block.polynomial * Roots.product remaining).eval (remaining[position]'retained.isLt).point = 0
          rw [DensePolynomial.eval_mul, previous tail retained, mul_zero]

/-- An original indexed factor separates from the same ordered scalar product at any point. -/
theorem factor_at (blocks : List (Block K))
    (simple : ∀ index : Fin blocks.length, (blocks[index.val]'index.isLt).multiplicity = 1)
    (point : K) (index : Fin blocks.length) :
    (Roots.product blocks).eval point = (point - (blocks[index.val]'index.isLt).point) *
      ((blocks.eraseIdx index.val).map (fun block => point - block.point)).prod := by
  induction blocks with
  | nil => exact Fin.elim0 index
  | cons block remaining previous =>
      have head := simple ⟨0, Nat.zero_lt_succ remaining.length⟩
      have tail : ∀ index : Fin remaining.length, (remaining[index.val]'index.isLt).multiplicity = 1 :=
        fun index => simple index.succ
      rcases index with ⟨position, bound⟩
      cases position with
      | zero =>
          change (block.polynomial * Roots.product remaining).eval point =
            (point - block.point) * (remaining.map (fun other => point - other.point)).prod
          rw [DensePolynomial.eval_mul, block_eval_one block head, eval_simple remaining tail point]
      | succ position =>
          let retained : Fin remaining.length := ⟨position, Nat.lt_of_succ_lt_succ bound⟩
          change (block.polynomial * Roots.product remaining).eval point =
            (point - (remaining[position]'retained.isLt).point) *
              ((block :: remaining.eraseIdx position).map (fun other => point - other.point)).prod
          rw [DensePolynomial.eval_mul, block_eval_one block head, previous tail retained]
          change (point - block.point) * ((point - (remaining[position]'retained.isLt).point) *
              (remaining.eraseIdx position |>.map (fun other => point - other.point)).prod) =
            (point - (remaining[position]'retained.isLt).point) *
              ((point - block.point) * (remaining.eraseIdx position |>.map (fun other => point - other.point)).prod)
          ring0

/-- The original product's first coefficient at an indexed simple root is its original cofactor-difference product.

Exactly the selected original occurrence is removed. Equal root values at
different positions remain separate factors, and their displayed difference
may be zero or a nonunit in a ring with zero divisors.
-/
theorem firstJet_at (blocks : List (Block K))
    (simple : ∀ index : Fin blocks.length, (blocks[index.val]'index.isLt).multiplicity = 1)
    (index : Fin blocks.length) :
    coefficientRow (Roots.product blocks).coeffs (blocks[index.val]'index.isLt).point 1 0 =
      ((blocks.eraseIdx index.val).map (fun block => (blocks[index.val]'index.isLt).point - block.point)).prod := by
  induction blocks with
  | nil => exact Fin.elim0 index
  | cons block remaining previous =>
      have head := simple ⟨0, Nat.zero_lt_succ remaining.length⟩
      have tail : ∀ index : Fin remaining.length, (remaining[index.val]'index.isLt).multiplicity = 1 :=
        fun index => simple index.succ
      rcases index with ⟨position, bound⟩
      cases position with
      | zero =>
          change coefficientRow (block.polynomial * Roots.product remaining).coeffs block.point 1 0 =
            (remaining.map (fun other => block.point - other.point)).prod
          rw [coefficientRow_mul_first, block_firstJet_one block head,
            block_eval_one block head, sub_self, one_mul, zero_mul, add_zero]
          exact eval_simple remaining tail block.point
      | succ position =>
          let retained : Fin remaining.length := ⟨position, Nat.lt_of_succ_lt_succ bound⟩
          change coefficientRow (block.polynomial * Roots.product remaining).coeffs
              (remaining[position]'retained.isLt).point 1 0 =
            ((block :: remaining.eraseIdx position).map
              (fun other => (remaining[position]'retained.isLt).point - other.point)).prod
          rw [coefficientRow_mul_first, block_firstJet_one block head,
            block_eval_one block head, eval_at remaining tail retained, one_mul, zero_add,
            previous tail retained]
          rfl

/-- The original displayed leading scalar survives the same indexed first-coefficient product readback. -/
theorem scale_firstJet_at (leading : K) (blocks : List (Block K))
    (simple : ∀ index : Fin blocks.length, (blocks[index.val]'index.isLt).multiplicity = 1)
    (index : Fin blocks.length) :
    coefficientRow (DensePolynomial.scale leading (Roots.product blocks)).coeffs
        (blocks[index.val]'index.isLt).point 1 0 =
      leading * ((blocks.eraseIdx index.val).map
        (fun block => (blocks[index.val]'index.isLt).point - block.point)).prod := by
  rw [coefficientRow_scale, firstJet_at blocks simple index]

omit [CommRing K] [DecidableEq K] in
/-- Deleting an original bounded occurrence preserves the multiplicity-one certificates of all retained blocks. -/
theorem simple_eraseIdx (blocks : List (Block K))
    (simple : ∀ index : Fin blocks.length, (blocks[index.val]'index.isLt).multiplicity = 1)
    (removed : Fin blocks.length) (retained : Fin (blocks.eraseIdx removed.val).length) :
    ((blocks.eraseIdx removed.val)[retained.val]'retained.isLt).multiplicity = 1 :=
  (congrArg Block.multiplicity (List.Erase.getElem_sourceIndex blocks removed retained)).trans
    (simple (List.Erase.sourceIndex blocks removed retained))

omit [CommRing K] [DecidableEq K] in
/-- An optional extra deletion retains its original bounded index different from the target factor. -/
abbrev OtherIndex (blocks : List (Block K)) (target : Fin blocks.length) :=
  {removed : Fin blocks.length // target ≠ removed}

omit [CommRing K] [DecidableEq K] in
/-- Retain the original block occurrences after one or two specified original bounded deletions. -/
@[expose] def cofactorBlocks (blocks : List (Block K)) (target : Fin blocks.length)
    (removed : Option (OtherIndex blocks target)) : List (Block K) :=
  match removed with
  | none => blocks.eraseIdx target.val
  | some earlier => (blocks.eraseIdx earlier.val.val).eraseIdx
      (List.Erase.index blocks earlier.val target earlier.property).val

/-- A second original factor separates from the same indexed first-derivative cofactor. -/
theorem firstJet_factor_at (blocks : List (Block K))
    (simple : ∀ index : Fin blocks.length, (blocks[index.val]'index.isLt).multiplicity = 1)
    (root target : Fin blocks.length) (different : target ≠ root) :
    coefficientRow (Roots.product blocks).coeffs (blocks[root.val]'root.isLt).point 1 0 =
      ((blocks[root.val]'root.isLt).point - (blocks[target.val]'target.isLt).point) *
        ((cofactorBlocks blocks target (some ⟨root, different⟩)).map
          (fun block => (blocks[root.val]'root.isLt).point - block.point)).prod := by
  let retained := List.Erase.index blocks root target different
  have simpleRetained := simple_eraseIdx blocks simple root
  rw [firstJet_at blocks simple root, ← eval_simple (blocks.eraseIdx root.val) simpleRetained]
  rw [factor_at (blocks.eraseIdx root.val) simpleRetained _ retained]
  rw [List.Erase.getElem_index]
  rfl

omit [DecidableEq K] in
/-- The original unit subtype for a displayed point-to-root difference. -/
abbrev InverseAt (blocks : List (Block K)) (point : K) (target : Fin blocks.length) :=
  {value : K // (point - (blocks[target.val]'target.isLt).point) * value = 1}

omit [DecidableEq K] in
set_option genInjectivity false in
/-- One actual excluded-factor product and its same original difference-unit inverse.

The original block list, bounded target and optional extra original deletion
are retained in the indices. The inverse is computed from this same cofactor,
displayed leading scalar and supplied whole-product inverse exactly once.
-/
structure DifferenceInverse (blocks : List (Block K)) (point : K) (target : Fin blocks.length)
    (removed : Option (OtherIndex blocks target)) (leading wholeInverse : K) where
  /-- The actual retained scalar product of the same remaining original factors. -/
  cofactor : K
  /-- The retained scalar consumes exactly the original specified exclusions. -/
  cofactor_eq : cofactor = ((cofactorBlocks blocks target removed).map (fun block => point - block.point)).prod
  /-- The computed inverse retains its original difference-unit certificate. -/
  inverse : InverseAt blocks point target
  /-- The same cached cofactor and supplied scalar data produce this actual inverse. -/
  inverse_eq : inverse.val = leading * cofactor * wholeInverse

constructive_injectivity DifferenceInverse

namespace DifferenceInverse

omit [DecidableEq K] in
/-- Materialize one original cofactor product and consume its certified same difference-unit formula. -/
@[expose] def ofCofactor (blocks : List (Block K)) (point : K) (target : Fin blocks.length)
    (removed : Option (OtherIndex blocks target)) (leading wholeInverse : K)
    (unit : (point - (blocks[target.val]'target.isLt).point) *
      (leading * ((cofactorBlocks blocks target removed).map (fun block => point - block.point)).prod *
        wholeInverse) = 1) : DifferenceInverse blocks point target removed leading wholeInverse :=
  let cofactor := ((cofactorBlocks blocks target removed).map (fun block => point - block.point)).prod
  let inverse := leading * cofactor * wholeInverse
  { cofactor := cofactor, cofactor_eq := rfl, inverse := ⟨inverse, unit⟩, inverse_eq := rfl }

/-- Extract one original difference inverse from the same retained scaled whole-product unit.

The actual cofactor product is computed once. The proof consumes the original
whole-product unit; it neither evaluates a derivative nor tests whether an
arbitrary nonzero scalar is invertible.
-/
@[expose] def ofEvalUnit (blocks : List (Block K))
    (simple : ∀ index : Fin blocks.length, (blocks[index.val]'index.isLt).multiplicity = 1)
    (point : K) (target : Fin blocks.length) (leading wholeInverse : K)
    (unit : (leading * (Roots.product blocks).eval point) * wholeInverse = 1) :
    DifferenceInverse blocks point target none leading wholeInverse :=
  ofCofactor blocks point target none leading wholeInverse (by
    change (point - (blocks[target.val]'target.isLt).point) *
      (leading * ((blocks.eraseIdx target.val).map (fun block => point - block.point)).prod * wholeInverse) = 1
    have relation := factor_at blocks simple point target
    calc
      _ = (leading * (Roots.product blocks).eval point) * wholeInverse := by rw [relation]; ring0
      _ = 1 := unit)

/-- Extract an original root-difference inverse from the same retained scaled first-derivative unit.

Both original bounded root occurrences remain in the result's indices. Only
their twice-excluded scalar cofactor and inverse are computed; the supplied
whole inverse is reused without re-evaluating its first derivative.
-/
@[expose] def ofFirstJetUnit (blocks : List (Block K))
    (simple : ∀ index : Fin blocks.length, (blocks[index.val]'index.isLt).multiplicity = 1)
    (root target : Fin blocks.length) (different : target ≠ root) (leading wholeInverse : K)
    (unit : (leading * coefficientRow (Roots.product blocks).coeffs
      (blocks[root.val]'root.isLt).point 1 0) * wholeInverse = 1) :
    DifferenceInverse blocks (blocks[root.val]'root.isLt).point target
      (some ⟨root, different⟩) leading wholeInverse :=
  ofCofactor blocks (blocks[root.val]'root.isLt).point target (some ⟨root, different⟩) leading wholeInverse (by
    have relation := firstJet_factor_at blocks simple root target different
    calc
      _ = (leading * coefficientRow (Roots.product blocks).coeffs
          (blocks[root.val]'root.isLt).point 1 0) * wholeInverse := by rw [relation]; ring0
      _ = 1 := unit)

end DifferenceInverse

end Purelib.Polynomial.Dense.Roots.Product

end
