import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import RFAP.Polynomial.NormalizedEliminant

/-!
# Resource bounds for displayed fraction-free Bézout cofactors

The separated-Sylvester scalar is only one component of the certificate.
This module also bounds the coefficient slots of every polynomial in the
scaled inverse.  The recurrence is source-only: a Schur round doubles the
matrix slot bound, and unwinding a block adds twice the current bound.
-/

namespace RFAP.NormalizedBezoutResource

abbrev WorkingGaussian := RFAP.NormalizedEliminant.WorkingGaussian
abbrev WorkingPolynomial := RFAP.NormalizedEliminant.WorkingPolynomial
abbrev WorkingMatrix := RFAP.NormalizedEliminant.WorkingMatrix
abbrev ScaledInverseData (count : Nat) :=
  RFAP.ConstructivePolynomialMatrix.ScaledInverseData WorkingGaussian count

open RFAP.ComputablePolynomial.DensePolynomial

private theorem degreeCount_le_length (polynomial : WorkingPolynomial) :
    polynomial.degreeCount ≤ polynomial.coeffs.length := by
  unfold degreeCount
  exact List.Sublist.length_le
    (List.dropWhile_sublist (fun coefficient : WorkingGaussian =>
      decide (coefficient = 0)))

private theorem add_slots (left right : WorkingPolynomial) :
    (left + right).coeffs.length ≤
      max left.coeffs.length right.coeffs.length := by
  let count := max left.coeffs.length right.coeffs.length
  let leftPadded := padLeft (count - left.coeffs.length) left.coeffs
  let rightPadded := padLeft (count - right.coeffs.length) right.coeffs
  have leftLength : leftPadded.length = count := by
    simp only [leftPadded, padLeft, List.length_append,
      List.length_replicate]
    exact Nat.sub_add_cancel (le_max_left _ _)
  have rightLength : rightPadded.length = count := by
    simp only [rightPadded, padLeft, List.length_append,
      List.length_replicate]
    exact Nat.sub_add_cancel (le_max_right _ _)
  change ((List.zipWith (· + ·) leftPadded rightPadded).dropWhile
    (· = 0)).length ≤ count
  exact (List.Sublist.length_le (List.dropWhile_sublist _)).trans (by
    rw [List.length_zipWith, leftLength, rightLength, min_self])

private theorem neg_slots (polynomial : WorkingPolynomial) :
    (-polynomial).coeffs.length ≤ polynomial.coeffs.length := by
  rw [neg_coeffs, List.length_map]
  exact degreeCount_le_length polynomial

private theorem mul_slots (left right : WorkingPolynomial) :
    (left * right).coeffs.length ≤
      left.coeffs.length + right.coeffs.length := by
  have degree := degreeCount_mul_le left right
  have normalized := normalize_mul left right
  have lengthEqual : (left * right).coeffs.length =
      (left * right).degreeCount := by
    unfold degreeCount
    rw [normalized]
  rw [lengthEqual]
  exact degree.trans ((Nat.sub_le _ _).trans
    (Nat.add_le_add (degreeCount_le_length left)
      (degreeCount_le_length right)))

private theorem foldl_add_slots : ∀ (values : List WorkingPolynomial)
    (accumulator : WorkingPolynomial) (bound : Nat),
    accumulator.coeffs.length ≤ bound →
    (∀ value ∈ values, value.coeffs.length ≤ bound) →
    (values.foldl (· + ·) accumulator).coeffs.length ≤ bound
  | [], _, _, accumulatorBound, _ => accumulatorBound
  | value :: remaining, accumulator, bound, accumulatorBound, valuesBound => by
      simp only [List.foldl_cons]
      apply foldl_add_slots remaining (accumulator + value) bound
      · exact (add_slots accumulator value).trans
          (max_le accumulatorBound (valuesBound value List.mem_cons_self))
      · intro candidate member
        exact valuesBound candidate (List.mem_cons_of_mem value member)

private theorem sumFin_slots {count : Nat}
    (values : Fin count → WorkingPolynomial) (bound : Nat)
    (valuesBound : ∀ index, (values index).coeffs.length ≤ bound) :
    (RFAP.ConstructivePolynomialMatrix.sumFin values).coeffs.length ≤
      bound := by
  unfold RFAP.ConstructivePolynomialMatrix.sumFin
  apply foldl_add_slots _ 0 bound (Nat.zero_le _)
  intro value member
  rw [List.mem_ofFn] at member
  rcases member with ⟨index, rfl⟩
  exact valuesBound index

private theorem dot_slots {count : Nat}
    (left right : RFAP.ConstructivePolynomialMatrix.Vector
      WorkingGaussian count)
    (leftBound rightBound : Nat)
    (leftWithin : ∀ index, (left index).coeffs.length ≤ leftBound)
    (rightWithin : ∀ index, (right index).coeffs.length ≤ rightBound) :
    (RFAP.ConstructivePolynomialMatrix.dot left right).coeffs.length ≤
      leftBound + rightBound := by
  apply sumFin_slots
  intro index
  exact (mul_slots (left index) (right index)).trans
    (Nat.add_le_add (leftWithin index) (rightWithin index))

def MatrixSlotsWithin {count : Nat} (matrix : WorkingMatrix count)
    (slots : Nat) : Prop :=
  ∀ row column, (matrix row column).coeffs.length ≤ slots

private theorem maxFin_le {count : Nat} (values : Fin count → Nat)
    (bound : Nat) (within : ∀ index, values index ≤ bound) :
    RFAP.NormalizedEliminant.maxFin count values ≤ bound := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ count inductionHypothesis =>
      unfold RFAP.NormalizedEliminant.maxFin
      apply max_le (within 0)
      exact inductionHypothesis (fun index => values index.succ)
        (fun index => within index.succ)

theorem matrixSlotBound_le {count : Nat} {matrix : WorkingMatrix count}
    {slots : Nat} (within : MatrixSlotsWithin matrix slots) :
    RFAP.NormalizedEliminant.matrixSlotBound matrix ≤ slots := by
  unfold RFAP.NormalizedEliminant.matrixSlotBound
  apply maxFin_le
  intro row
  apply maxFin_le
  intro column
  exact within row column

def dataSlotEnvelope : Nat → Nat → Nat
  | 0, _ => 1
  | count + 1, slots =>
      2 * slots + dataSlotEnvelope count (2 * slots)

structure DataSlotsWithin {count : Nat} (data : ScaledInverseData count)
    (slots : Nat) : Prop where
  scalar : data.scalar.coeffs.length ≤ slots
  inverse : MatrixSlotsWithin data.inverse slots

theorem scaledInverseData_slots :
    ∀ (count : Nat) (matrix : WorkingMatrix count) (slots : Nat),
      MatrixSlotsWithin matrix slots →
      DataSlotsWithin
        (RFAP.ConstructivePolynomialMatrix.scaledInverseData count matrix)
        (dataSlotEnvelope count slots)
  | 0, _, _, _ => by
      constructor
      · rfl
      · intro row
        exact Fin.elim0 row
  | count + 1, matrix, slots, matrixWithin => by
      let schurMatrix := RFAP.ConstructivePolynomialMatrix.schur matrix
      have schurWithin : MatrixSlotsWithin schurMatrix (2 * slots) := by
        intro row column
        exact (RFAP.NormalizedEliminant.schur_slots matrix row column).trans
          (Nat.mul_le_mul_left 2 (matrixSlotBound_le matrixWithin))
      let smaller := RFAP.ConstructivePolynomialMatrix.scaledInverseData
        count schurMatrix
      have smallerWithin : DataSlotsWithin smaller
          (dataSlotEnvelope count (2 * slots)) :=
        scaledInverseData_slots count schurMatrix (2 * slots) schurWithin
      let recursiveSlots := dataSlotEnvelope count (2 * slots)
      change DataSlotsWithin
        (RFAP.ConstructivePolynomialMatrix.scaledInverseData (count + 1) matrix)
        (2 * slots + recursiveSlots)
      have headSlots :
          (RFAP.ConstructivePolynomialMatrix.head matrix).coeffs.length ≤
            slots := matrixWithin 0 0
      have smallerScalarSlots : smaller.scalar.coeffs.length ≤
          recursiveSlots := smallerWithin.scalar
      have scalarSlots :
          (RFAP.ConstructivePolynomialMatrix.head matrix * smaller.scalar).coeffs.length ≤
            2 * slots + recursiveSlots :=
        (mul_slots _ _).trans (calc
          (RFAP.ConstructivePolynomialMatrix.head matrix).coeffs.length +
                smaller.scalar.coeffs.length ≤ slots + recursiveSlots :=
            Nat.add_le_add headSlots smallerScalarSlots
          _ ≤ 2 * slots + recursiveSlots := by
            apply Nat.add_le_add_right
            rw [two_mul]
            exact Nat.le_add_right slots slots)
      constructor
      · exact scalarSlots
      · intro row column
        let a := RFAP.ConstructivePolynomialMatrix.head matrix
        let top := RFAP.ConstructivePolynomialMatrix.topRow matrix
        let left := RFAP.ConstructivePolynomialMatrix.leftColumn matrix
        let inverse := smaller.inverse
        have aSlots : a.coeffs.length ≤ slots := matrixWithin 0 0
        have topSlots : ∀ index, (top index).coeffs.length ≤ slots :=
          fun index => by
            simpa only [top, RFAP.ConstructivePolynomialMatrix.topRow,
              RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
              matrixWithin 0 index.succ
        have leftSlots : ∀ index, (left index).coeffs.length ≤ slots :=
          fun index => by
            simpa only [left, RFAP.ConstructivePolynomialMatrix.leftColumn,
              RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
              matrixWithin index.succ 0
        have inverseSlots : ∀ i j,
            (inverse i j).coeffs.length ≤ recursiveSlots :=
          smallerWithin.inverse
        have inverseColumnSlots : ∀ index,
            (RFAP.ConstructivePolynomialMatrix.matrixVector inverse left index
                ).coeffs.length ≤ recursiveSlots + slots := by
          intro index
          simpa only [RFAP.ConstructivePolynomialMatrix.matrixVector,
            RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
            dot_slots (inverse index) left recursiveSlots slots
              (fun middle => inverseSlots index middle) leftSlots
        have rowInverseSlots : ∀ index,
            (RFAP.ConstructivePolynomialMatrix.vectorMatrix top inverse index
                ).coeffs.length ≤ slots + recursiveSlots := by
          intro index
          simpa only [RFAP.ConstructivePolynomialMatrix.vectorMatrix,
            RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
            dot_slots top
              (RFAP.ConstructiveFiniteMatrix.vectorOfFn fun middle =>
                inverse middle index)
              slots recursiveSlots topSlots
              (fun middle => by
                simpa only [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
                  inverseSlots middle index)
        unfold RFAP.ConstructivePolynomialMatrix.scaledInverseData
          RFAP.ConstructivePolynomialMatrix.blockInverse
        simp only [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
        refine Fin.cases ?_ (fun rowIndex => ?_) row
        · refine Fin.cases ?_ (fun columnIndex => ?_) column
          · have innerDot := dot_slots top
                (RFAP.ConstructivePolynomialMatrix.matrixVector inverse left)
                slots (recursiveSlots + slots) topSlots inverseColumnSlots
            exact (add_slots smaller.scalar _).trans (by
              apply max_le
              · exact smallerWithin.scalar.trans
                  (Nat.le_add_left recursiveSlots (2 * slots))
              · exact innerDot.trans (Nat.le_of_eq (by ring1)))
          · have negA := neg_slots a
            have rowBound := rowInverseSlots columnIndex
            exact (mul_slots (-a)
              (RFAP.ConstructivePolynomialMatrix.vectorMatrix top inverse
                columnIndex)).trans (calc
                  (-a).coeffs.length +
                      (RFAP.ConstructivePolynomialMatrix.vectorMatrix top
                        inverse columnIndex).coeffs.length ≤
                    slots + (slots + recursiveSlots) :=
                      Nat.add_le_add (negA.trans aSlots) rowBound
                  _ = 2 * slots + recursiveSlots := by ring1)
        · refine Fin.cases ?_ (fun columnIndex => ?_) column
          · have negA := neg_slots a
            have columnBound := inverseColumnSlots rowIndex
            exact (mul_slots (-a)
              (RFAP.ConstructivePolynomialMatrix.matrixVector inverse left
                rowIndex)).trans (calc
                  (-a).coeffs.length +
                      (RFAP.ConstructivePolynomialMatrix.matrixVector inverse
                        left rowIndex).coeffs.length ≤
                    slots + (recursiveSlots + slots) :=
                      Nat.add_le_add (negA.trans aSlots) columnBound
                  _ = 2 * slots + recursiveSlots := by ring1)
          · have square := mul_slots a a
            have inverseBound := inverseSlots rowIndex columnIndex
            exact (mul_slots (a * a) (inverse rowIndex columnIndex)).trans
              (calc
                (a * a).coeffs.length +
                      (inverse rowIndex columnIndex).coeffs.length ≤
                    (slots + slots) + recursiveSlots :=
                  Nat.add_le_add
                    (square.trans (Nat.add_le_add aSlots aSlots)) inverseBound
                _ = 2 * slots + recursiveSlots := by ring1)

/-! ## Coefficient magnitudes -/

open RFAP.NormalizedPolynomialResource

def dataMagnitudeEnvelope : Nat → Nat → Nat → Nat
  | 0, _, bound => bound
  | count + 1, slots, bound =>
      let schurBound := grow RFAP.NormalizedEliminant.gaussianModel bound
        (2 * slots + 2)
      let recursiveBound := dataMagnitudeEnvelope count (2 * slots) schurBound
      let recursiveSlots := dataSlotEnvelope count (2 * slots)
      grow RFAP.NormalizedEliminant.gaussianModel recursiveBound
        (8 * (slots + recursiveSlots + count + 1))

theorem bound_le_dataMagnitudeEnvelope : ∀ count slots bound,
    bound ≤ dataMagnitudeEnvelope count slots bound
  | 0, _, _ => le_refl _
  | count + 1, slots, bound => by
      dsimp only [dataMagnitudeEnvelope]
      exact (bound_le_grow RFAP.NormalizedEliminant.gaussianModel bound _).trans
        ((bound_le_dataMagnitudeEnvelope count (2 * slots) _).trans
          (bound_le_grow RFAP.NormalizedEliminant.gaussianModel _ _))

private theorem weighted_sum_le_outputSteps
    (slots recursiveSlots count slotWeight recursiveWeight countWeight
      constantWeight : Nat)
    (slotWeightLe : slotWeight ≤ 8)
    (recursiveWeightLe : recursiveWeight ≤ 8)
    (countWeightLe : countWeight ≤ 8)
    (constantWeightLe : constantWeight ≤ 8) :
    slotWeight * slots + recursiveWeight * recursiveSlots +
        countWeight * count + constantWeight ≤
      8 * (slots + recursiveSlots + count + 1) := by
  calc
    slotWeight * slots + recursiveWeight * recursiveSlots +
          countWeight * count + constantWeight ≤
        8 * slots + 8 * recursiveSlots + 8 * count + 8 :=
      Nat.add_le_add
        (Nat.add_le_add
          (Nat.add_le_add
            (Nat.mul_le_mul_right slots slotWeightLe)
            (Nat.mul_le_mul_right recursiveSlots recursiveWeightLe))
          (Nat.mul_le_mul_right count countWeightLe))
        constantWeightLe
    _ = 8 * (slots + recursiveSlots + count + 1) := by ring1

private theorem foldl_add_within : ∀
    (values : List WorkingPolynomial) (accumulator : WorkingPolynomial)
    (bound : Nat),
    RFAP.NormalizedEliminant.gaussianModel.magnitude 0 ≤ bound →
    (∀ value ∈ values, PolynomialWithin
      RFAP.NormalizedEliminant.gaussianModel value bound) →
    PolynomialWithin RFAP.NormalizedEliminant.gaussianModel accumulator bound →
    PolynomialWithin RFAP.NormalizedEliminant.gaussianModel
      (values.foldl (· + ·) accumulator)
      (grow RFAP.NormalizedEliminant.gaussianModel bound values.length)
  | [], _, _, _, _, accumulatorWithin => by
      simpa using accumulatorWithin
  | value :: remaining, accumulator, bound, zeroBound, valuesWithin,
      accumulatorWithin => by
      simp only [List.foldl_cons, List.length_cons]
      have next := add_within RFAP.NormalizedEliminant.gaussianModel zeroBound
        accumulatorWithin (valuesWithin value List.mem_cons_self)
      have remainingWithin : ∀ candidate ∈ remaining,
          PolynomialWithin RFAP.NormalizedEliminant.gaussianModel candidate
            (grow RFAP.NormalizedEliminant.gaussianModel bound 1) := by
        intro candidate member
        exact polynomialWithin_mono RFAP.NormalizedEliminant.gaussianModel
          (valuesWithin candidate (List.mem_cons_of_mem value member))
          (bound_le_grow RFAP.NormalizedEliminant.gaussianModel bound 1)
      have recursive := foldl_add_within remaining (accumulator + value)
        (grow RFAP.NormalizedEliminant.gaussianModel bound 1)
        (zeroBound.trans
          (bound_le_grow RFAP.NormalizedEliminant.gaussianModel bound 1))
        remainingWithin next
      rw [grow_add] at recursive
      simpa only [Nat.add_comm] using recursive

private theorem sumFin_within {count : Nat}
    (values : Fin count → WorkingPolynomial) (bound : Nat)
    (zeroBound : RFAP.NormalizedEliminant.gaussianModel.magnitude 0 ≤ bound)
    (valuesWithin : ∀ index, PolynomialWithin
      RFAP.NormalizedEliminant.gaussianModel (values index) bound) :
    PolynomialWithin RFAP.NormalizedEliminant.gaussianModel
      (RFAP.ConstructivePolynomialMatrix.sumFin values)
      (grow RFAP.NormalizedEliminant.gaussianModel bound count) := by
  unfold RFAP.ConstructivePolynomialMatrix.sumFin
  have allWithin : ∀ value ∈ List.ofFn values,
      PolynomialWithin RFAP.NormalizedEliminant.gaussianModel value bound := by
    intro value member
    rw [List.mem_ofFn] at member
    rcases member with ⟨index, rfl⟩
    exact valuesWithin index
  simpa only [QuotientFreeList.length_ofFn] using
    foldl_add_within (List.ofFn values) 0 bound zeroBound allWithin
      (zero_within RFAP.NormalizedEliminant.gaussianModel bound)

private theorem dot_within {count : Nat}
    (left right : RFAP.ConstructivePolynomialMatrix.Vector
      WorkingGaussian count)
    (bound leftSlots : Nat)
    (zeroBound : RFAP.NormalizedEliminant.gaussianModel.magnitude 0 ≤ bound)
    (leftWithin : ∀ index, PolynomialWithin
      RFAP.NormalizedEliminant.gaussianModel (left index) bound)
    (rightWithin : ∀ index, PolynomialWithin
      RFAP.NormalizedEliminant.gaussianModel (right index) bound)
    (leftSlotBound : ∀ index,
      (left index).coeffs.length ≤ leftSlots) :
    PolynomialWithin RFAP.NormalizedEliminant.gaussianModel
      (RFAP.ConstructivePolynomialMatrix.dot left right)
      (grow RFAP.NormalizedEliminant.gaussianModel bound
        (2 * leftSlots + count)) := by
  have products : ∀ index, PolynomialWithin
      RFAP.NormalizedEliminant.gaussianModel (left index * right index)
      (grow RFAP.NormalizedEliminant.gaussianModel bound (2 * leftSlots)) := by
    intro index
    exact polynomialWithin_mono RFAP.NormalizedEliminant.gaussianModel
      (mul_within RFAP.NormalizedEliminant.gaussianModel zeroBound
        (leftWithin index) (rightWithin index))
      (grow_mono_steps RFAP.NormalizedEliminant.gaussianModel bound
        (Nat.mul_le_mul_left 2 (leftSlotBound index)))
  have summed := sumFin_within
    (fun index => left index * right index)
    (grow RFAP.NormalizedEliminant.gaussianModel bound (2 * leftSlots))
    (zeroBound.trans
      (bound_le_grow RFAP.NormalizedEliminant.gaussianModel bound _)) products
  rw [grow_add] at summed
  exact summed

structure DataWithin {count : Nat} (data : ScaledInverseData count)
    (bound : Nat) : Prop where
  scalar : PolynomialWithin RFAP.NormalizedEliminant.gaussianModel
    data.scalar bound
  inverse : RFAP.NormalizedEliminant.MatrixWithin data.inverse bound

theorem scaledInverseData_within :
    ∀ (count : Nat) (matrix : WorkingMatrix count)
      (slots bound : Nat),
      RFAP.NormalizedEliminant.gaussianModel.magnitude 0 ≤ bound →
      RFAP.NormalizedEliminant.gaussianModel.magnitude
        (1 : WorkingGaussian) ≤ bound →
      MatrixSlotsWithin matrix slots →
      RFAP.NormalizedEliminant.MatrixWithin matrix bound →
      DataWithin
        (RFAP.ConstructivePolynomialMatrix.scaledInverseData count matrix)
        (dataMagnitudeEnvelope count slots bound)
  | 0, _, _, bound, _, oneBound, _, _ => by
      constructor
      · simpa only [RFAP.ConstructivePolynomialMatrix.scaledInverseData,
          dataMagnitudeEnvelope] using
          constant_within RFAP.NormalizedEliminant.gaussianModel oneBound
      · intro row
        exact Fin.elim0 row
  | count + 1, matrix, slots, bound, zeroBound, oneBound, matrixSlots,
      matrixWithin => by
      let schurMatrix := RFAP.ConstructivePolynomialMatrix.schur matrix
      let schurBound := grow RFAP.NormalizedEliminant.gaussianModel bound
        (2 * slots + 2)
      have schurSlots : MatrixSlotsWithin schurMatrix (2 * slots) := by
        intro row column
        exact (RFAP.NormalizedEliminant.schur_slots matrix row column).trans
          (Nat.mul_le_mul_left 2 (matrixSlotBound_le matrixSlots))
      have rawSchurWithin := RFAP.NormalizedEliminant.schur_within
        zeroBound matrixWithin
      have schurWithin : RFAP.NormalizedEliminant.MatrixWithin
          schurMatrix schurBound := by
        intro row column
        exact polynomialWithin_mono RFAP.NormalizedEliminant.gaussianModel
          (rawSchurWithin row column)
          (grow_mono_steps RFAP.NormalizedEliminant.gaussianModel bound
            (Nat.add_le_add_right
              (Nat.mul_le_mul_left 2 (matrixSlotBound_le matrixSlots)) 2))
      let smaller := RFAP.ConstructivePolynomialMatrix.scaledInverseData
        count schurMatrix
      let recursiveBound := dataMagnitudeEnvelope count (2 * slots) schurBound
      let recursiveSlots := dataSlotEnvelope count (2 * slots)
      have smallerWithin : DataWithin smaller recursiveBound :=
        scaledInverseData_within count schurMatrix (2 * slots) schurBound
          (zeroBound.trans
            (bound_le_grow RFAP.NormalizedEliminant.gaussianModel bound _))
          (oneBound.trans
            (bound_le_grow RFAP.NormalizedEliminant.gaussianModel bound _))
          schurSlots schurWithin
      have smallerSlotData := scaledInverseData_slots count schurMatrix
        (2 * slots) schurSlots
      let outputSteps := 8 * (slots + recursiveSlots + count + 1)
      let outputBound := grow RFAP.NormalizedEliminant.gaussianModel
        recursiveBound outputSteps
      have sourceToRecursive : bound ≤ recursiveBound :=
        (bound_le_grow RFAP.NormalizedEliminant.gaussianModel bound _).trans
          (bound_le_dataMagnitudeEnvelope count (2 * slots) schurBound)
      have zeroRecursive := zeroBound.trans sourceToRecursive
      have matrixRecursive : RFAP.NormalizedEliminant.MatrixWithin
          matrix recursiveBound := by
        intro row column
        exact polynomialWithin_mono RFAP.NormalizedEliminant.gaussianModel
          (matrixWithin row column) sourceToRecursive
      have promote : ∀ {polynomial : WorkingPolynomial} {steps : Nat},
          PolynomialWithin RFAP.NormalizedEliminant.gaussianModel polynomial
            (grow RFAP.NormalizedEliminant.gaussianModel recursiveBound steps) →
          steps ≤ outputSteps →
          PolynomialWithin RFAP.NormalizedEliminant.gaussianModel polynomial
            outputBound := by
        intro polynomial steps within stepsLe
        exact polynomialWithin_mono RFAP.NormalizedEliminant.gaussianModel within
          (grow_mono_steps RFAP.NormalizedEliminant.gaussianModel recursiveBound
            stepsLe)
      change DataWithin
        (RFAP.ConstructivePolynomialMatrix.scaledInverseData (count + 1) matrix)
        outputBound
      constructor
      · dsimp only [RFAP.ConstructivePolynomialMatrix.scaledInverseData]
        have product := mul_within RFAP.NormalizedEliminant.gaussianModel
          zeroRecursive (matrixRecursive 0 0) smallerWithin.scalar
        exact promote product (by
          have headSlots := matrixSlots 0 0
          calc
            2 * (RFAP.ConstructivePolynomialMatrix.head matrix).coeffs.length ≤
                2 * slots := Nat.mul_le_mul_left 2 headSlots
            _ = 2 * slots + 0 * recursiveSlots + 0 * count + 0 := by ring1
            _ ≤ outputSteps :=
              weighted_sum_le_outputSteps slots recursiveSlots count
                2 0 0 0 (by decide) (by decide) (by decide) (by decide))
      · intro row column
        let a := RFAP.ConstructivePolynomialMatrix.head matrix
        let top := RFAP.ConstructivePolynomialMatrix.topRow matrix
        let left := RFAP.ConstructivePolynomialMatrix.leftColumn matrix
        let inverse := smaller.inverse
        have aWithin : PolynomialWithin RFAP.NormalizedEliminant.gaussianModel
            a recursiveBound := matrixRecursive 0 0
        have aSlots : a.coeffs.length ≤ slots := matrixSlots 0 0
        have topWithin : ∀ index, PolynomialWithin
            RFAP.NormalizedEliminant.gaussianModel (top index) recursiveBound :=
          fun index => by
            simpa only [top, RFAP.ConstructivePolynomialMatrix.topRow,
              RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
              matrixRecursive 0 index.succ
        have topSlots : ∀ index, (top index).coeffs.length ≤ slots :=
          fun index => by
            simpa only [top, RFAP.ConstructivePolynomialMatrix.topRow,
              RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
              matrixSlots 0 index.succ
        have leftWithin : ∀ index, PolynomialWithin
            RFAP.NormalizedEliminant.gaussianModel (left index) recursiveBound :=
          fun index => by
            simpa only [left, RFAP.ConstructivePolynomialMatrix.leftColumn,
              RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
              matrixRecursive index.succ 0
        have inverseWithin : ∀ i j, PolynomialWithin
            RFAP.NormalizedEliminant.gaussianModel (inverse i j)
              recursiveBound := smallerWithin.inverse
        have inverseSlots : ∀ i j,
            (inverse i j).coeffs.length ≤ recursiveSlots :=
          smallerSlotData.inverse
        have inverseColumn : ∀ index, PolynomialWithin
            RFAP.NormalizedEliminant.gaussianModel
              (RFAP.ConstructivePolynomialMatrix.matrixVector inverse left index)
              (grow RFAP.NormalizedEliminant.gaussianModel recursiveBound
                (2 * recursiveSlots + count)) := by
          intro index
          simpa only [RFAP.ConstructivePolynomialMatrix.matrixVector,
            RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
            dot_within (inverse index) left recursiveBound recursiveSlots
              zeroRecursive (fun middle => inverseWithin index middle)
              leftWithin (fun middle => inverseSlots index middle)
        have rowInverse : ∀ index, PolynomialWithin
            RFAP.NormalizedEliminant.gaussianModel
              (RFAP.ConstructivePolynomialMatrix.vectorMatrix top inverse index)
              (grow RFAP.NormalizedEliminant.gaussianModel recursiveBound
                (2 * slots + count)) := by
          intro index
          simpa only [RFAP.ConstructivePolynomialMatrix.vectorMatrix,
            RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
            dot_within top
              (RFAP.ConstructiveFiniteMatrix.vectorOfFn fun middle =>
                inverse middle index)
              recursiveBound slots zeroRecursive topWithin
              (fun middle => by
                simpa only [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
                  inverseWithin middle index)
              topSlots
        unfold RFAP.ConstructivePolynomialMatrix.scaledInverseData
          RFAP.ConstructivePolynomialMatrix.blockInverse
        simp only [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
        refine Fin.cases ?_ (fun rowIndex => ?_) row
        · refine Fin.cases ?_ (fun columnIndex => ?_) column
          · let preSteps := 2 * recursiveSlots + count
            let preBound := grow RFAP.NormalizedEliminant.gaussianModel
              recursiveBound preSteps
            have topPre : ∀ index, PolynomialWithin
                RFAP.NormalizedEliminant.gaussianModel (top index) preBound :=
              fun index => polynomialWithin_mono
                RFAP.NormalizedEliminant.gaussianModel (topWithin index)
                (bound_le_grow RFAP.NormalizedEliminant.gaussianModel
                  recursiveBound preSteps)
            have columnPre : ∀ index, PolynomialWithin
                RFAP.NormalizedEliminant.gaussianModel
                  (RFAP.ConstructivePolynomialMatrix.matrixVector inverse left index)
                  preBound := inverseColumn
            have inner := dot_within top
              (RFAP.ConstructivePolynomialMatrix.matrixVector inverse left)
              preBound slots
              (zeroRecursive.trans (bound_le_grow
                RFAP.NormalizedEliminant.gaussianModel recursiveBound preSteps))
              topPre columnPre topSlots
            have scalarPre := polynomialWithin_mono
              RFAP.NormalizedEliminant.gaussianModel smallerWithin.scalar
              (bound_le_grow RFAP.NormalizedEliminant.gaussianModel
                recursiveBound (preSteps + (2 * slots + count)))
            rw [grow_add] at inner
            have corner := add_within RFAP.NormalizedEliminant.gaussianModel
              (zeroRecursive.trans (bound_le_grow
                RFAP.NormalizedEliminant.gaussianModel recursiveBound _))
              scalarPre inner
            rw [grow_add] at corner
            exact promote corner (by
              dsimp only [preSteps, outputSteps]
              calc
                2 * recursiveSlots + count + (2 * slots + count) + 1 =
                    2 * slots + 2 * recursiveSlots + 2 * count + 1 := by ring1
                _ ≤ 8 * (slots + recursiveSlots + count + 1) :=
                  weighted_sum_le_outputSteps slots recursiveSlots count
                    2 2 2 1 (by decide) (by decide) (by decide) (by decide))
          · let preSteps := 2 * slots + count + 1
            let preBound := grow RFAP.NormalizedEliminant.gaussianModel
              recursiveBound preSteps
            have oneLePre : 1 ≤ preSteps := by
              unfold preSteps
              exact Nat.succ_le_succ (Nat.zero_le (2 * slots + count))
            have negated := neg_within RFAP.NormalizedEliminant.gaussianModel
              aWithin
            have negPre := polynomialWithin_mono
              RFAP.NormalizedEliminant.gaussianModel negated
              (grow_mono_steps RFAP.NormalizedEliminant.gaussianModel
                recursiveBound oneLePre)
            have rowPre : PolynomialWithin
                RFAP.NormalizedEliminant.gaussianModel
                (RFAP.ConstructivePolynomialMatrix.vectorMatrix top inverse
                  columnIndex) preBound := polynomialWithin_mono
              RFAP.NormalizedEliminant.gaussianModel (rowInverse columnIndex)
              (grow_mono_steps RFAP.NormalizedEliminant.gaussianModel
                recursiveBound (show 2 * slots + count ≤ preSteps by
                  unfold preSteps
                  exact Nat.le_add_right (2 * slots + count) 1))
            have product := mul_within RFAP.NormalizedEliminant.gaussianModel
              (zeroRecursive.trans (bound_le_grow
                RFAP.NormalizedEliminant.gaussianModel recursiveBound preSteps))
              negPre rowPre
            rw [grow_add] at product
            exact promote product (by
              dsimp only [preSteps, outputSteps]
              have negSlots := neg_slots a
              have twiceNegLe : 2 * (-a).coeffs.length ≤ 2 * slots :=
                Nat.mul_le_mul_left 2 (negSlots.trans aSlots)
              refine (Nat.add_le_add_left twiceNegLe
                (2 * slots + count + 1)).trans ?_
              calc
                2 * slots + count + 1 + 2 * slots =
                    4 * slots + 0 * recursiveSlots + 1 * count + 1 := by ring1
                _ ≤ 8 * (slots + recursiveSlots + count + 1) :=
                  weighted_sum_le_outputSteps slots recursiveSlots count
                    4 0 1 1 (by decide) (by decide) (by decide) (by decide))
        · refine Fin.cases ?_ (fun columnIndex => ?_) column
          · let preSteps := 2 * recursiveSlots + count + 1
            let preBound := grow RFAP.NormalizedEliminant.gaussianModel
              recursiveBound preSteps
            have oneLePre : 1 ≤ preSteps := by
              unfold preSteps
              exact Nat.succ_le_succ
                (Nat.zero_le (2 * recursiveSlots + count))
            have negated := neg_within RFAP.NormalizedEliminant.gaussianModel
              aWithin
            have negPre := polynomialWithin_mono
              RFAP.NormalizedEliminant.gaussianModel negated
              (grow_mono_steps RFAP.NormalizedEliminant.gaussianModel
                recursiveBound oneLePre)
            have columnPre : PolynomialWithin
                RFAP.NormalizedEliminant.gaussianModel
                (RFAP.ConstructivePolynomialMatrix.matrixVector inverse left
                  rowIndex) preBound := polynomialWithin_mono
              RFAP.NormalizedEliminant.gaussianModel (inverseColumn rowIndex)
              (grow_mono_steps RFAP.NormalizedEliminant.gaussianModel
                recursiveBound
                  (show 2 * recursiveSlots + count ≤ preSteps by
                    unfold preSteps
                    exact Nat.le_add_right
                      (2 * recursiveSlots + count) 1))
            have product := mul_within RFAP.NormalizedEliminant.gaussianModel
              (zeroRecursive.trans (bound_le_grow
                RFAP.NormalizedEliminant.gaussianModel recursiveBound preSteps))
              negPre columnPre
            rw [grow_add] at product
            exact promote product (by
              dsimp only [preSteps, outputSteps]
              have negSlots := neg_slots a
              have twiceNegLe : 2 * (-a).coeffs.length ≤ 2 * slots :=
                Nat.mul_le_mul_left 2 (negSlots.trans aSlots)
              refine (Nat.add_le_add_left twiceNegLe
                (2 * recursiveSlots + count + 1)).trans ?_
              calc
                2 * recursiveSlots + count + 1 + 2 * slots =
                    2 * slots + 2 * recursiveSlots + 1 * count + 1 := by ring1
                _ ≤ 8 * (slots + recursiveSlots + count + 1) :=
                  weighted_sum_le_outputSteps slots recursiveSlots count
                    2 2 1 1 (by decide) (by decide) (by decide) (by decide))
          · have square := mul_within
              RFAP.NormalizedEliminant.gaussianModel zeroRecursive aWithin aWithin
            let preSteps := 2 * slots
            let preBound := grow RFAP.NormalizedEliminant.gaussianModel
              recursiveBound preSteps
            have squarePre := polynomialWithin_mono
              RFAP.NormalizedEliminant.gaussianModel square
              (grow_mono_steps RFAP.NormalizedEliminant.gaussianModel
                recursiveBound (Nat.mul_le_mul_left 2 aSlots))
            have inversePre := polynomialWithin_mono
              RFAP.NormalizedEliminant.gaussianModel
              (inverseWithin rowIndex columnIndex)
              (bound_le_grow RFAP.NormalizedEliminant.gaussianModel
                recursiveBound preSteps)
            have product := mul_within RFAP.NormalizedEliminant.gaussianModel
              (zeroRecursive.trans (bound_le_grow
                RFAP.NormalizedEliminant.gaussianModel recursiveBound preSteps))
              squarePre inversePre
            rw [grow_add] at product
            exact promote product (by
              dsimp only [preSteps, outputSteps]
              have squareSlots := mul_slots a a
              have squareLe : (a * a).coeffs.length ≤ 2 * slots :=
                calc
                  (a * a).coeffs.length ≤ a.coeffs.length + a.coeffs.length :=
                    squareSlots
                  _ ≤ slots + slots := Nat.add_le_add aSlots aSlots
                  _ = 2 * slots := by ring1
              have twiceSquareLe :
                  2 * (a * a).coeffs.length ≤ 4 * slots := by
                exact (Nat.mul_le_mul_left 2 squareLe).trans_eq (by ring1)
              refine (Nat.add_le_add_left twiceSquareLe (2 * slots)).trans ?_
              calc
                2 * slots + 4 * slots =
                    6 * slots + 0 * recursiveSlots + 0 * count + 0 := by ring1
                _ ≤ 8 * (slots + recursiveSlots + count + 1) :=
                  weighted_sum_le_outputSteps slots recursiveSlots count
                    6 0 0 0 (by decide) (by decide) (by decide) (by decide))

/-- Complete source recurrence for the normalized separated-Sylvester scalar
and every displayed inverse/cofactor polynomial. -/
def separatedDataMagnitudeEnvelope
    (polynomial : RFAP.NormalizedEliminant.SemanticPolynomial) : Nat :=
  let working := RFAP.NormalizedEliminant.canonicalPolynomial polynomial
  let count := (RFAP.NormalizedEliminant.erasePolynomial working).natDegree +
    (RFAP.NormalizedEliminant.erasePolynomial working).natDegree
  let matrix := RFAP.NormalizedEliminant.separatedSylvester working
  dataMagnitudeEnvelope count
    (RFAP.NormalizedEliminant.matrixSlotBound matrix)
    (RFAP.NormalizedEliminant.separatedMatrixMagnitudeEnvelope working)

theorem normalizedSeparatedData_within
    (polynomial : RFAP.NormalizedEliminant.SemanticPolynomial) :
    DataWithin
      (RFAP.NormalizedEliminant.separatedData
        (RFAP.NormalizedEliminant.canonicalPolynomial polynomial))
      (separatedDataMagnitudeEnvelope polynomial) := by
  let working := RFAP.NormalizedEliminant.canonicalPolynomial polynomial
  let matrix := RFAP.NormalizedEliminant.separatedSylvester working
  apply scaledInverseData_within
  · exact (RFAP.NormalizedEliminant.source_zero_within working).trans
      (bound_le_grow RFAP.NormalizedEliminant.gaussianModel _ _)
  · exact (RFAP.NormalizedEliminant.source_one_within working).trans
      (bound_le_grow RFAP.NormalizedEliminant.gaussianModel _ _)
  · exact RFAP.NormalizedEliminant.matrixSlot_le matrix
  · exact RFAP.NormalizedEliminant.separatedSylvester_within working

end RFAP.NormalizedBezoutResource
