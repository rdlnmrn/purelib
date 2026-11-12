module

import Purelib.Polynomial.Recurrence.Mode.Hermite.Shift
import Purelib.Polynomial.Recurrence.Mode.Hermite.Solution
import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Data.Gaussian.Field

/-!
# Original confluent modes over a ring with zero divisors

A zero block and a nonzero nilpotent perturbation of one are interleaved.
The computed complete inverse agrees with an independent literal table.
-/

namespace TestPurelib.Polynomial.Recurrence.Mode.Hermite

open Purelib.Algebra.Quadratic
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Polynomial
open Dense.Basic (DensePolynomial)
open Dense.Division
open Purelib.Polynomial.Dense.Roots
open Purelib.Polynomial.Recurrence.Mode
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.LinearAlgebra.Matrix

/-- The original square-zero quadratic coefficient ring. -/
private abbrev Dual := Pair Purelib.Data.Gaussian.Basic.Canonical 0

/-- The nonzero nilpotent coordinate in the same original ring. -/
private def epsilon : Dual := Pair.generator

/-- The original zero root and a unit root retain their actual multiplicities. -/
private def blocks : List (Block Dual) :=
  [⟨0, 2, by decide⟩, ⟨1 + epsilon, 1, by decide⟩]

/-- The original ordered root-difference inverses. -/
private def differences : SquareMatrix Dual blocks.length := matrixOfFn fun row column =>
  if row.val = column.val then 0 else if row.val = 0 then -(1 - epsilon) else 1 - epsilon

/-- Both distinct original block differences multiply the retained entries to one. -/
private theorem units : ∀ first second : Fin blocks.length, first ≠ second →
    (Hermite.point blocks first - Hermite.point blocks second) * differences first second = 1 := by
  decide +kernel

/-- The same root occurs again after the other original block. -/
private def word : List (Fin blocks.length) := [⟨0, by decide⟩, ⟨1, by decide⟩, ⟨0, by decide⟩]

/-- The original constructor computes the complete same-owner basis and inverse. -/
private def basis : Hermite blocks differences word := Hermite.prepare blocks differences units word

/-- The retained orders are exactly the displayed interleaved confluent orders. -/
private theorem orders : ∀ index : Fin 3, basis.occurrences.orders index =
    if index.val = 2 then 1 else 0 := by decide +kernel

/-- The actual matrix is the independently specified zero-root confluent table. -/
private theorem entries : ∀ row column : Fin 3, basis.matrix row column =
    if row.val = 0 then if column.val = 2 then 0 else 1
    else if row.val = 1 then if column.val = 0 then 0 else if column.val = 1 then 1 + epsilon else 1
    else if column.val = 1 then 1 + 2 * epsilon else 0 := by decide +kernel

/-- The complete constructed inverse agrees with the independent literal table. -/
private theorem inverse_entries : ∀ row column : Fin 3, basis.inverse.inverse row column =
    if row.val = 0 then if column.val = 0 then 1 else if column.val = 1 then 0 else -(1 - 2 * epsilon)
    else if row.val = 1 then if column.val = 2 then 1 - 2 * epsilon else 0
    else if column.val = 0 then 0 else if column.val = 1 then 1 else -(1 - epsilon) := by decide +kernel

/-- Extraction reads the independently calculated coefficient vector. -/
private theorem extracted : basis.coordinates (.cons 1 (.cons 2 (.cons 3 .nil))) =
    .cons (-2 + 6 * epsilon) (.cons (3 - 6 * epsilon) (.cons (-1 + 3 * epsilon) .nil)) := by
  apply vector_ext
  intro index
  have readings : ∀ position : Fin 3,
      basis.coordinates (.cons 1 (.cons 2 (.cons 3 .nil))) position =
        (.cons (-2 + 6 * epsilon) (.cons (3 - 6 * epsilon) (.cons (-1 + 3 * epsilon) .nil)) :
          Vec Dual 3) position := by
    decide +kernel
  exact readings index

/-- The same computed coefficients reconstruct the entire original input vector. -/
private theorem reconstructed :
    Rectangular.apply basis.matrix (basis.coordinates (.cons 1 (.cons 2 (.cons 3 .nil)))) =
      .cons 1 (.cons 2 (.cons 3 .nil)) := basis.reconstruct _

/-- A complete late window recovers the same shifted coefficients even with interleaved zero-root jets. -/
private theorem late_recovery (start : Nat) (coefficients : Vec Dual word.length) :
    basis.coordinates (Rectangular.apply (basis.horizonFrom start word.length) coefficients) =
      Rectangular.apply
        (Arithmetic.power (Hermite.Shift.transition (Hermite.point blocks) word basis.occurrences) start)
        coefficients := basis.coordinates_horizonFrom start coefficients

/-- The same original zero-root jets disappear from the literal late coefficient vector. -/
private theorem late_recovery_values :
    basis.coordinates (Rectangular.apply (basis.horizonFrom 4 word.length)
      (.cons 2 (.cons 3 (.cons 5 .nil)))) = .cons 0 (.cons (3 + 12 * epsilon) (.cons 0 .nil)) := by
  rewrite [basis.coordinates_horizonFrom]
  apply vector_ext
  intro index
  have readings : ∀ position : Fin 3,
      Rectangular.apply (Arithmetic.power (Hermite.Shift.transition (Hermite.point blocks) word basis.occurrences) 4)
        (.cons 2 (.cons 3 (.cons 5 .nil))) position =
      (.cons 0 (.cons (3 + 12 * epsilon) (.cons 0 .nil)) : Vec Dual 3) position := by decide +kernel
  exact readings index

/-- A zero-start consecutive horizon preserves the complete original horizon value. -/
private theorem original_horizon (count : Nat) : basis.horizonFrom 0 count = basis.horizon count :=
  basis.horizonFrom_zero count

/-- The original cubic retains the repeated zero root and the same perturbed unit root. -/
private def polynomial : DensePolynomial Dual := ⟨[1, -(1 + epsilon), 0, 0]⟩

/-- The actual original polynomial bank certifies its literal coefficient factorization. -/
private def bank : Bank polynomial where
  blocks := blocks
  count_eq := by decide +kernel
  monicProduct := product blocks
  product_eq := rfl
  factorization := by decide +kernel
  differenceInverses := differences
  difference_unit := units

/-- The automatic bank word has the same original cubic degree. -/
private theorem bank_degree : (Word.expand bank.blocks).length = polynomial.natDegree :=
  Hermite.ofBank_count bank

/-- The automatic expanded word reads the retained original indices in block order. -/
private theorem bank_word : ∀ index : Fin 3,
    ((Word.expand bank.blocks)[index.val]'index.isLt).val = if index.val < 2 then 0 else 1 := by decide +kernel

/-- The automatic original bank basis has exactly the retained zero-block jet orders. -/
private theorem bank_orders : ∀ index : Fin 3,
    (Hermite.ofBank bank).occurrences.orders index = if index.val = 1 then 1 else 0 := by decide +kernel

/-- The automatic original bank constructor reconstructs every degree-sized initial vector. -/
private theorem bank_reconstruct (values : Vec Dual (Word.expand bank.blocks).length) :
    Rectangular.apply (Hermite.ofBank bank).matrix ((Hermite.ofBank bank).coordinates values) = values :=
  (Hermite.ofBank bank).reconstruct values

/-- The original cubic companion uses its same retained unit leading coefficient. -/
private def companion : Dense.Companion polynomial :=
  Dense.Companion.ofUnit polynomial (by decide +kernel) 1 (by decide +kernel)

/-- The original first zero-factor division is retained with its same quotient and remainder. -/
private def firstZero : Synthetic.Result polynomial 0 := Synthetic.divide polynomial 0

/-- The original second zero-factor division consumes that exact retained first quotient. -/
private def secondZero : Synthetic.Result firstZero.quotient 0 := Synthetic.divide firstZero.quotient 0

/-- The original unit-root division consumes the same original polynomial. -/
private def unitRoot : Synthetic.Result polynomial (1 + epsilon) := Synthetic.divide polynomial (1 + epsilon)

/-- Two actual retained synthetic divisions certify every finite repeated-zero mode row. -/
private theorem repeated_zero_all_rows (start : Nat) :
    coefficientRow polynomial.normalize.coeffs (0 : Dual) 1 start = 0 := by
  have normalized : polynomial.normalize.coeffs = polynomial.coeffs := by decide +kernel
  rw [normalized, coefficientRow_synthetic_vanish firstZero (by decide +kernel) (by decide +kernel) 0,
    coefficientRow_synthetic_zero secondZero (by decide +kernel)]
  have remainder : secondZero.remainder = 0 := by decide +kernel
  rw [remainder, zero_mul]

/-- One actual retained synthetic division certifies every finite perturbed-unit mode row. -/
private theorem unit_root_all_rows (start : Nat) :
    coefficientRow polynomial.normalize.coeffs (1 + epsilon) 0 start = 0 := by
  have normalized : polynomial.normalize.coeffs = polynomial.coeffs := by decide +kernel
  rw [normalized, coefficientRow_synthetic_zero unitRoot (by decide +kernel)]
  have remainder : unitRoot.remainder = 0 := by decide +kernel
  rw [remainder, zero_mul]

/-- All complete rows of the original repeated-zero window satisfy the original companion recurrence. -/
private theorem repeated_zero_rows : companion.Satisfies (window (0 : Dual) 1 7) :=
  window_satisfies companion 0 1 7 (fun start _ => repeated_zero_all_rows start)

/-- All complete rows of the actual perturbed-unit mode satisfy the same original companion recurrence. -/
private theorem unit_root_rows : companion.Satisfies (window (1 + epsilon) 0 7) :=
  window_satisfies companion (1 + epsilon) 0 7 (fun start _ => unit_root_all_rows start)

/-- The first zero-root order beyond the retained multiplicity fails an actual original row. -/
private theorem excluded_zero_order : coefficientRow polynomial.normalize.coeffs (0 : Dual) 2 0 ≠ 0 := by
  decide +kernel

/-- A repeated unit-root word also supplies an auxiliary confluent coordinate completion. -/
private def unitWord : List (Fin blocks.length) := [⟨1, by decide⟩, ⟨1, by decide⟩]

/-- The same original difference-unit table prepares the auxiliary completed basis. -/
private def unitBasis : Hermite blocks differences unitWord := Hermite.prepare blocks differences units unitWord

/-- Retain the same original root inverse at both bounded repeated occurrences. -/
private def rootInverses : Vec Dual unitWord.length := .cons (1 - epsilon) (.cons (1 - epsilon) .nil)

/-- Both original unit-root occurrences multiply their same retained inverses to one. -/
private theorem root_units : ∀ index : Fin unitWord.length,
    Hermite.point blocks (unitWord[index.val]'index.isLt) * rootInverses index = 1 := by decide +kernel

/-- Prepare the actual mode transition and its original scalar-one inverse once. -/
private def modeShift : Hermite.Shift blocks unitWord unitBasis.occurrences :=
  Hermite.Shift.prepare blocks unitWord unitBasis.occurrences rootInverses root_units

/-- The retained original shift is the independently specified repeated-root Jordan table. -/
private theorem shift_entries : ∀ row column : Fin 2, modeShift.matrix row column =
    if row = column then 1 + epsilon else if row.val = 0 then 1 else 0 := by decide +kernel

/-- Its actual retained inverse is the independent exact nilpotent table. -/
private theorem shift_inverse_entries : ∀ row column : Fin 2, modeShift.inverse.inverse row column =
    if row = column then 1 - epsilon else if row.val = 0 then -(1 - 2 * epsilon) else 0 := by decide +kernel

/-- Later horizon rows use the exact original repeated-root readings beyond the cached initial rows. -/
private theorem later_horizon : ∀ column : Fin 2, unitBasis.horizon 5 ⟨4, by decide⟩ column =
    if column.val = 0 then 1 + 4 * epsilon else 4 + 12 * epsilon := by decide +kernel

/-- The original complete initial horizon is the same retained matrix. -/
private theorem initial_horizon : unitBasis.horizon unitWord.length = unitBasis.matrix := unitBasis.horizon_initial

/-- Every finite successor row consumes that same retained original shift matrix. -/
private theorem shifted_rows (index : Fin 4) (column : Fin 2) :
    Rectangular.mul (unitBasis.horizon 5) modeShift.matrix index.castSucc column =
      unitBasis.horizon 5 index.succ column := modeShift.horizon_step unitBasis 4 index column

/-- The literal original bank certifies every finite row of every displayed generalized order. -/
private theorem bank_all_rows (index : Fin bank.blocks.length) (order : Nat)
    (bound : order < (bank.block index).multiplicity) (start : Nat) :
    coefficientRow polynomial.normalize.coeffs (bank.block index).point order start = 0 :=
  bank_coefficientRow bank index order bound start

/-- The same bank proves original companion rows for every finite repeated-zero window. -/
private theorem bank_zero_windows (count : Nat) : companion.Satisfies (window (0 : Dual) 1 count) :=
  bank_window_satisfies bank companion ⟨0, by decide⟩ 1 (by decide +kernel) count

/-- The same bank proves original companion rows for its nonzero nilpotent-perturbed root. -/
private theorem bank_unit_windows (count : Nat) : companion.Satisfies (window (1 + epsilon) 0 count) :=
  bank_window_satisfies bank companion ⟨1, by decide⟩ 0 (by decide +kernel) count

/-- All three slots of an all-zero block retain the genuine zero-root startup jets. -/
private def zeroPolynomial : DensePolynomial Dual := ⟨[1, 0, 0, 0]⟩

/-- A single original multiplicity-three zero block certifies its complete literal source. -/
private def zeroBank : Bank zeroPolynomial where
  blocks := [⟨0, 3, by decide⟩]
  count_eq := by decide +kernel
  monicProduct := product [⟨0, 3, by decide⟩]
  product_eq := rfl
  factorization := by decide +kernel
  differenceInverses := matrixOfFn fun _ _ => 0
  difference_unit := by decide +kernel

/-- Every retained all-zero jet order annihilates every finite complete source row. -/
private theorem all_zero_rows (order : Fin 3) (start : Nat) :
    coefficientRow zeroPolynomial.normalize.coeffs (0 : Dual) order.val start = 0 :=
  bank_coefficientRow zeroBank ⟨0, by decide⟩ order.val order.isLt start

/-- The first order outside that actual multiplicity has a nonvanishing original row. -/
private theorem all_zero_excluded : coefficientRow zeroPolynomial.normalize.coeffs (0 : Dual) 3 0 = 1 := by
  decide +kernel

/-- The original retained zero-root synthetic result has the bank-certified zero remainder. -/
private theorem bank_zero_remainder : (Synthetic.divide polynomial.normalize 0).remainder = 0 :=
  bank_synthetic_remainder bank ⟨0, by decide⟩ (Synthetic.divide polynomial.normalize 0)

/-- The automatic bank basis reconstructs every supplied complete finite solution of the original cubic. -/
private theorem every_finite_solution {count : Nat} (values : Vec Dual count) (enough : 3 ≤ count)
    (equations : companion.Satisfies values) :
    Rectangular.apply ((Hermite.ofBank bank).horizon count)
      ((Hermite.ofBank bank).coordinates (Purelib.Data.Vector.Split.take enough values)) = values :=
  Hermite.ofBank_horizon_reconstruct bank companion values enough equations

/-- The ordered original bank extracts the independent literal startup coefficients. -/
private theorem automatic_coefficients : (Hermite.ofBank bank).coordinates (.cons 1 (.cons 2 (.cons 3 .nil))) =
    .cons (-2 + 6 * epsilon) (.cons (-1 + 3 * epsilon) (.cons (3 - 6 * epsilon) .nil)) := by
  apply vector_ext
  intro index
  have readings : ∀ position : Fin 3,
      (Hermite.ofBank bank).coordinates (.cons 1 (.cons 2 (.cons 3 .nil))) position =
        (.cons (-2 + 6 * epsilon) (.cons (-1 + 3 * epsilon) (.cons (3 - 6 * epsilon) .nil)) : Vec Dual 3)
          position := by decide +kernel
  exact readings index

/-- The same computed mode combination reads the independently calculated later nilpotent values. -/
private theorem automatic_later_values :
    Rectangular.apply ((Hermite.ofBank bank).horizon 7)
      ((Hermite.ofBank bank).coordinates (.cons 1 (.cons 2 (.cons 3 .nil)))) =
        .cons 1 (.cons 2 (.cons 3 (.cons (3 + 3 * epsilon) (.cons (3 + 6 * epsilon)
          (.cons (3 + 9 * epsilon) (.cons (3 + 12 * epsilon) .nil)))))) := by
  rw [automatic_coefficients]
  apply vector_ext
  intro index
  have readings : ∀ position : Fin 7,
      Rectangular.apply ((Hermite.ofBank bank).horizon 7)
        (.cons (-2 + 6 * epsilon) (.cons (-1 + 3 * epsilon) (.cons (3 - 6 * epsilon) .nil))) position =
          (.cons 1 (.cons 2 (.cons 3 (.cons (3 + 3 * epsilon) (.cons (3 + 6 * epsilon)
            (.cons (3 + 9 * epsilon) (.cons (3 + 12 * epsilon) .nil)))))) : Vec Dual 7) position := by
    decide +kernel
  exact readings index

end TestPurelib.Polynomial.Recurrence.Mode.Hermite
