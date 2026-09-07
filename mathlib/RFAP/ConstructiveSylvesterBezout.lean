import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.SeparatedVariables
import RFAP.Geometry.PathClearance
import RFAP.Polynomial.Path

/-!
# Finite Bézout extraction from the separated Sylvester inverse

This module turns the first column of the fraction-free scaled inverse into
two explicit dense cofactors.  The only summation identity involved is a
finite shifted coefficient-list calculation.
-/

namespace RFAP.ConstructiveSylvesterBezout

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Gaussian
abbrev ParameterPolynomial := GaussianPolynomial
abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev CoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.SeparatedVariables

private theorem sumPrefix_evalLow (outer parameter : Gaussian) :
    ∀ (coefficients : List ParameterPolynomial) (extra : Nat),
      RFAP.ConstructiveFiniteMatrix.sumFin
        (fun row : Fin (coefficients.length + extra) =>
          if (row : Nat) < coefficients.length then
            (coefficients.getD (row : Nat) 0).eval parameter *
              outer ^ (row : Nat)
          else 0) =
        evalLow coefficients outer parameter
  | [], extra => by
      change RFAP.ConstructiveFiniteMatrix.sumFin
        (fun row : Fin (0 + extra) =>
          if (row : Nat) < 0 then
            ([].getD (row : Nat) 0 : ParameterPolynomial).eval parameter *
              outer ^ (row : Nat)
          else 0) = 0
      calc
        RFAP.ConstructiveFiniteMatrix.sumFin
            (fun row : Fin (0 + extra) =>
              if (row : Nat) < 0 then
                ([].getD (row : Nat) 0 : ParameterPolynomial).eval parameter *
                  outer ^ (row : Nat)
              else 0) =
            RFAP.ConstructiveFiniteMatrix.sumFin
              (fun _ : Fin (0 + extra) => (0 : Gaussian)) := by
          apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
          intro row
          rw [if_neg (Nat.not_lt_zero (row : Nat))]
        _ = 0 := RFAP.ConstructiveFiniteMatrix.sumFin_zero
  | coefficient :: remaining, extra => by
      rw [show (coefficient :: remaining).length + extra =
        (remaining.length + extra) + 1 by
          simp only [List.length_cons, Nat.succ_add, Nat.add_one]]
      rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
      simp only [Fin.val_zero]
      have headInside : (0 : Nat) < (coefficient :: remaining).length :=
        Nat.zero_lt_succ remaining.length
      rw [if_pos headInside, List.getD_cons_zero, pow_zero, mul_one]
      have tailIdentity :
          RFAP.ConstructiveFiniteMatrix.sumFin
            (fun row : Fin (remaining.length + extra) =>
            if (row.succ : Nat) < remaining.length + 1 then
              ((coefficient :: remaining).getD (row.succ : Nat) 0).eval
                  parameter * outer ^ (row.succ : Nat)
            else 0) =
          RFAP.ConstructiveFiniteMatrix.sumFin
            (fun row : Fin (remaining.length + extra) =>
            (if (row : Nat) < remaining.length then
              (remaining.getD (row : Nat) 0).eval parameter *
                outer ^ (row : Nat)
            else 0) * outer) := by
        apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
        intro row
        simp only [Fin.val_succ, Nat.succ_lt_succ_iff,
          List.getD_cons_succ]
        split
        · rw [pow_succ]
          ring1
        · rw [zero_mul]
      have tailCurrent :
          RFAP.ConstructiveFiniteMatrix.sumFin
            (fun row : Fin (remaining.length + extra) =>
              if (row.succ : Nat) < (coefficient :: remaining).length then
                ((coefficient :: remaining).getD (row.succ : Nat) 0).eval
                    parameter * outer ^ (row.succ : Nat)
              else 0) =
            RFAP.ConstructiveFiniteMatrix.sumFin
              (fun row : Fin (remaining.length + extra) =>
                if (row.succ : Nat) < remaining.length + 1 then
                  ((coefficient :: remaining).getD (row.succ : Nat) 0).eval
                      parameter * outer ^ (row.succ : Nat)
                else 0) := by
        apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
        intro row
        rw [List.length_cons]
      rw [tailCurrent, tailIdentity,
        RFAP.ConstructiveFiniteMatrix.sumFin_mul_right,
        sumPrefix_evalLow outer parameter remaining extra,
        evalLow_cons]
      ring1

private theorem sumShifted_evalLow (outer parameter : Gaussian) :
    ∀ (offset : Nat) (coefficients : List ParameterPolynomial) (suffix : Nat),
      RFAP.ConstructiveFiniteMatrix.sumFin
        (fun row : Fin (offset + coefficients.length + suffix) =>
          if offset ≤ (row : Nat) ∧
              (row : Nat) < offset + coefficients.length then
            (coefficients.getD ((row : Nat) - offset) 0).eval parameter *
              outer ^ (row : Nat)
          else 0) =
        outer ^ offset * evalLow coefficients outer parameter
  | 0, coefficients, suffix => by
      rw [Nat.zero_add, pow_zero, one_mul]
      calc
        RFAP.ConstructiveFiniteMatrix.sumFin
            (fun row : Fin (coefficients.length + suffix) =>
              if 0 ≤ (row : Nat) ∧ (row : Nat) < coefficients.length then
                (coefficients.getD ((row : Nat) - 0) 0).eval parameter *
                  outer ^ (row : Nat)
              else 0) =
            RFAP.ConstructiveFiniteMatrix.sumFin
              (fun row : Fin (coefficients.length + suffix) =>
                if (row : Nat) < coefficients.length then
                  (coefficients.getD (row : Nat) 0).eval parameter *
                    outer ^ (row : Nat)
                else 0) := by
          apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
          intro row
          simp only [Nat.zero_le, true_and, Nat.sub_zero]
        _ = evalLow coefficients outer parameter :=
          sumPrefix_evalLow outer parameter coefficients suffix
  | offset + 1, coefficients, suffix => by
      rw [show (offset + 1) + coefficients.length + suffix =
        (offset + coefficients.length + suffix) + 1 by
          simp only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]]
      rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
      simp only [Fin.val_zero]
      rw [if_neg (fun condition =>
        Nat.not_succ_le_zero offset condition.1)]
      rw [zero_add]
      have upperIdentity :
          offset + 1 + coefficients.length =
            Nat.succ (offset + coefficients.length) := by
        calc
          offset + 1 + coefficients.length =
              offset + (1 + coefficients.length) :=
            Nat.add_assoc _ _ _
          _ = offset + (coefficients.length + 1) := by
            rw [Nat.add_comm 1 coefficients.length]
          _ = (offset + coefficients.length) + 1 :=
            (Nat.add_assoc _ _ _).symm
          _ = Nat.succ (offset + coefficients.length) :=
            Nat.add_one _
      have tailIdentity :
          RFAP.ConstructiveFiniteMatrix.sumFin
            (fun row : Fin (offset + coefficients.length + suffix) =>
            if offset + 1 ≤ (row.succ : Nat) ∧
                (row.succ : Nat) < offset + 1 + coefficients.length then
              (coefficients.getD ((row.succ : Nat) - (offset + 1)) 0).eval
                  parameter * outer ^ (row.succ : Nat)
            else 0) =
          RFAP.ConstructiveFiniteMatrix.sumFin
            (fun row : Fin (offset + coefficients.length + suffix) =>
            (if offset ≤ (row : Nat) ∧
                (row : Nat) < offset + coefficients.length then
              (coefficients.getD ((row : Nat) - offset) 0).eval parameter *
                outer ^ (row : Nat)
            else 0) * outer) := by
        apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
        intro row
        by_cases condition :
            offset ≤ (row : Nat) ∧
              (row : Nat) < offset + coefficients.length
        · have shiftedCondition :
              offset + 1 ≤ (row.succ : Nat) ∧
                (row.succ : Nat) < offset + 1 + coefficients.length := by
            change Nat.succ offset ≤ Nat.succ (row : Nat) ∧
              Nat.succ (row : Nat) < offset + 1 + coefficients.length
            rw [upperIdentity]
            exact ⟨Nat.succ_le_succ condition.1,
              Nat.succ_lt_succ condition.2⟩
          rw [if_pos condition, if_pos shiftedCondition]
          have indexIdentity :
              (row.succ : Nat) - (offset + 1) =
                (row : Nat) - offset := by
            simp only [Fin.val_succ, Nat.succ_sub_succ_eq_sub]
          rw [indexIdentity]
          change (coefficients.getD ((row : Nat) - offset) 0).eval parameter *
              outer ^ ((row : Nat) + 1) =
            (coefficients.getD ((row : Nat) - offset) 0).eval parameter *
              outer ^ (row : Nat) * outer
          rw [pow_succ]
          ring1
        · have shiftedCondition :
              ¬(offset + 1 ≤ (row.succ : Nat) ∧
                (row.succ : Nat) < offset + 1 + coefficients.length) := by
            intro shifted
            have shifted' :
                Nat.succ offset ≤ Nat.succ (row : Nat) ∧
                  Nat.succ (row : Nat) <
                    Nat.succ (offset + coefficients.length) := by
              change Nat.succ offset ≤ Nat.succ (row : Nat) ∧
                Nat.succ (row : Nat) <
                  offset + 1 + coefficients.length at shifted
              rw [upperIdentity] at shifted
              exact shifted
            exact condition ⟨Nat.le_of_succ_le_succ shifted'.1,
              Nat.lt_of_succ_lt_succ shifted'.2⟩
          rw [if_neg condition, if_neg shiftedCondition, zero_mul]
      rw [tailIdentity,
        RFAP.ConstructiveFiniteMatrix.sumFin_mul_right,
        sumShifted_evalLow outer parameter offset coefficients suffix,
        pow_succ]
      ring1

theorem separatedLeftColumnPowerSum (p : GaussianPolynomial)
    (nonzero : p.isZero = false) (outer parameter : Gaussian)
    (column : Fin p.natDegree) :
    RFAP.ConstructiveFiniteMatrix.sumFin
      (fun row : Fin (p.natDegree + p.natDegree) =>
        (RFAP.ConstructivePolynomialMatrix.evalMatrix parameter
          (separatedSylvester p) row
          (Fin.castAdd p.natDegree column)) * outer ^ (row : Nat)) =
      outer ^ (column : Nat) *
        RFAP.ConstructiveBivariate.eval (reflected p) outer parameter := by
  let suffix := p.natDegree - ((column : Nat) + 1)
  have coefficientsLength := reflectedCoefficients_shape p nonzero
  have totalIdentity :
      (column : Nat) + (reflectedCoefficients p).length + suffix =
        p.natDegree + p.natDegree := by
    dsimp only [suffix]
    rw [coefficientsLength.length_eq]
    have columnBound := column.isLt
    omega
  have shifted := sumShifted_evalLow outer parameter (column : Nat)
    (reflectedCoefficients p) suffix
  rw [totalIdentity] at shifted
  have summandsEqual :
      RFAP.ConstructiveFiniteMatrix.sumFin
        (fun row : Fin (p.natDegree + p.natDegree) =>
        (RFAP.ConstructivePolynomialMatrix.evalMatrix parameter
          (separatedSylvester p) row
          (Fin.castAdd p.natDegree column)) * outer ^ (row : Nat)) =
      RFAP.ConstructiveFiniteMatrix.sumFin
        (fun row : Fin (p.natDegree + p.natDegree) =>
        if (column : Nat) ≤ (row : Nat) ∧
            (row : Nat) <
              (column : Nat) + (reflectedCoefficients p).length then
          ((reflectedCoefficients p).getD
            ((row : Nat) - (column : Nat)) 0).eval parameter *
              outer ^ (row : Nat)
        else 0) := by
          apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
          intro row
          simp only [separatedSylvester,
            RFAP.ConstructiveBivariate.sylvester,
            RFAP.ConstructivePolynomialMatrix.evalMatrix_apply,
            RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
            QuotientFreeFin.addCases_left]
          have upperIdentity :
              (row : Nat) ≤ (column : Nat) + p.natDegree ↔
                (row : Nat) <
                  (column : Nat) + (reflectedCoefficients p).length := by
            rw [coefficientsLength.length_eq]
            rw [← Nat.add_assoc]
            exact Nat.lt_add_one_iff.symm
          by_cases inside :
              (column : Nat) ≤ (row : Nat) ∧
                (row : Nat) ≤ (column : Nat) + p.natDegree
          · rw [if_pos inside, if_pos ⟨inside.1, upperIdentity.mp inside.2⟩,
              outerCoeff_reflected]
          · have outside :
                ¬((column : Nat) ≤ (row : Nat) ∧
                  (row : Nat) <
                    (column : Nat) + (reflectedCoefficients p).length) := by
              intro candidate
              exact inside ⟨candidate.1, upperIdentity.mpr candidate.2⟩
            rw [if_neg inside, if_neg outside, eval_zero, zero_mul]
  rw [summandsEqual]
  change _ = outer ^ (column : Nat) *
    evalLow (reflectedCoefficients p) outer parameter
  exact shifted

theorem separatedRightColumnPowerSum (p : GaussianPolynomial)
    (nonzero : p.isZero = false) (outer parameter : Gaussian)
    (column : Fin p.natDegree) :
    RFAP.ConstructiveFiniteMatrix.sumFin
      (fun row : Fin (p.natDegree + p.natDegree) =>
        (RFAP.ConstructivePolynomialMatrix.evalMatrix parameter
          (separatedSylvester p) row
          (Fin.natAdd p.natDegree column)) * outer ^ (row : Nat)) =
      outer ^ (column : Nat) *
        RFAP.ConstructiveBivariate.eval (lifted p) outer parameter := by
  let suffix := p.natDegree - ((column : Nat) + 1)
  have coefficientsLength := liftedCoefficients_length p nonzero
  have totalIdentity :
      (column : Nat) + (liftedCoefficients p).length + suffix =
        p.natDegree + p.natDegree := by
    dsimp only [suffix]
    rw [coefficientsLength]
    have columnBound := column.isLt
    omega
  have shifted := sumShifted_evalLow outer parameter (column : Nat)
    (liftedCoefficients p) suffix
  rw [totalIdentity] at shifted
  have summandsEqual :
      RFAP.ConstructiveFiniteMatrix.sumFin
        (fun row : Fin (p.natDegree + p.natDegree) =>
        (RFAP.ConstructivePolynomialMatrix.evalMatrix parameter
          (separatedSylvester p) row
          (Fin.natAdd p.natDegree column)) * outer ^ (row : Nat)) =
      RFAP.ConstructiveFiniteMatrix.sumFin
        (fun row : Fin (p.natDegree + p.natDegree) =>
        if (column : Nat) ≤ (row : Nat) ∧
            (row : Nat) < (column : Nat) + (liftedCoefficients p).length then
          ((liftedCoefficients p).getD
            ((row : Nat) - (column : Nat)) 0).eval parameter *
              outer ^ (row : Nat)
        else 0) := by
          apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
          intro row
          simp only [separatedSylvester,
            RFAP.ConstructiveBivariate.sylvester,
            RFAP.ConstructivePolynomialMatrix.evalMatrix_apply,
            RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
            QuotientFreeFin.addCases_right]
          have upperIdentity :
              (row : Nat) ≤ (column : Nat) + p.natDegree ↔
                (row : Nat) <
                  (column : Nat) + (liftedCoefficients p).length := by
            rw [coefficientsLength]
            rw [← Nat.add_assoc]
            exact Nat.lt_add_one_iff.symm
          by_cases inside :
              (column : Nat) ≤ (row : Nat) ∧
                (row : Nat) ≤ (column : Nat) + p.natDegree
          · rw [if_pos inside, if_pos ⟨inside.1, upperIdentity.mp inside.2⟩,
              outerCoeff_lifted]
          · have outside :
                ¬((column : Nat) ≤ (row : Nat) ∧
                  (row : Nat) <
                    (column : Nat) + (liftedCoefficients p).length) := by
              intro candidate
              exact inside ⟨candidate.1, upperIdentity.mpr candidate.2⟩
            rw [if_neg inside, if_neg outside, eval_zero, zero_mul]
  rw [summandsEqual]
  change _ = outer ^ (column : Nat) *
    evalLow (liftedCoefficients p) outer parameter
  exact shifted

/-! ## Cofactor vectors as dense polynomials -/

def polynomialFromLow : (n : Nat) → (Fin n → Gaussian) →
    GaussianPolynomial
  | 0, _ => 0
  | n + 1, coefficients =>
      constant (coefficients 0) +
        shift 1 (polynomialFromLow n (fun index => coefficients index.succ))

@[simp] theorem eval_polynomialFromLow (outer : Gaussian) :
    ∀ (n : Nat) (coefficients : Fin n → Gaussian),
      (polynomialFromLow n coefficients).eval outer =
        RFAP.ConstructiveFiniteMatrix.sumFin
          (fun index => coefficients index * outer ^ (index : Nat))
  | 0, _ => by
      simp [polynomialFromLow, RFAP.ConstructiveFiniteMatrix.sumFin]
  | n + 1, coefficients => by
      rw [polynomialFromLow, eval_add, eval_constant, eval_shift,
        eval_polynomialFromLow outer n,
        RFAP.ConstructiveFiniteMatrix.sumFin_succ]
      change coefficients 0 +
          RFAP.ConstructiveFiniteMatrix.sumFin
            (fun index : Fin n => coefficients index.succ * outer ^ (index : Nat)) *
              outer ^ 1 =
        coefficients 0 * outer ^ 0 +
          RFAP.ConstructiveFiniteMatrix.sumFin
            (fun index : Fin n =>
              coefficients index.succ * outer ^ (index.succ : Nat))
      have tailPower :
          RFAP.ConstructiveFiniteMatrix.sumFin
              (fun index : Fin n =>
                coefficients index.succ * outer ^ (index.succ : Nat)) =
            RFAP.ConstructiveFiniteMatrix.sumFin
              (fun index : Fin n =>
                (coefficients index.succ * outer ^ (index : Nat)) * outer) :=
        RFAP.ConstructiveFiniteMatrix.sumFin_congr
        (left := fun index : Fin n =>
          coefficients index.succ * outer ^ (index.succ : Nat))
        (right := fun index : Fin n =>
          (coefficients index.succ * outer ^ (index : Nat)) * outer)
        (fun index => by
          change coefficients index.succ * outer ^ ((index : Nat) + 1) = _
          rw [pow_succ]
          ring1)
      rw [tailPower]
      rw [RFAP.ConstructiveFiniteMatrix.sumFin_mul_right]
      ring1

private theorem foldl_add_from (values : List Gaussian)
    (accumulator : Gaussian) :
    values.foldl (fun a b => a + b) accumulator =
      accumulator + values.foldl (fun a b => a + b) 0 := by
  induction values generalizing accumulator with
  | nil =>
      change accumulator = accumulator + 0
      ring1
  | cons value remaining inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      rw [List.foldl_cons, show (0 : Gaussian) + value = value by ring1]
      rw [inductionHypothesis value]
      ring1

private theorem sumFin_addCases {m n : Nat}
    (left : Fin m → Gaussian) (right : Fin n → Gaussian) :
    RFAP.ConstructiveFiniteMatrix.sumFin
        (fun index : Fin (m + n) =>
          QuotientFreeFin.addCases left right index) =
      RFAP.ConstructiveFiniteMatrix.sumFin left +
        RFAP.ConstructiveFiniteMatrix.sumFin right := by
  unfold RFAP.ConstructiveFiniteMatrix.sumFin
  rw [QuotientFreeList.ofFn_add, QuotientFreeList.foldl_append,
    foldl_add_from]
  congr 2
  · exact QuotientFreeList.ofFn_congr
      (QuotientFreeFin.addCases_left left right)
  · exact QuotientFreeList.ofFn_congr
      (QuotientFreeFin.addCases_right left right)

private theorem weighted_matrixVector {n : Nat}
    (matrix : RFAP.ConstructiveFiniteMatrix.Matrix Gaussian n)
    (vector weights : RFAP.ConstructiveFiniteMatrix.Vector Gaussian n) :
    RFAP.ConstructiveFiniteMatrix.sumFin
        (fun row =>
          RFAP.ConstructiveFiniteMatrix.matrixVector matrix vector row *
            weights row) =
      RFAP.ConstructiveFiniteMatrix.sumFin
        (fun column =>
          RFAP.ConstructiveFiniteMatrix.sumFin
              (fun row => matrix row column * weights row) *
            vector column) := by
  calc
    RFAP.ConstructiveFiniteMatrix.sumFin
        (fun row =>
          RFAP.ConstructiveFiniteMatrix.matrixVector matrix vector row *
            weights row) =
        RFAP.ConstructiveFiniteMatrix.sumFin
        (fun row =>
          RFAP.ConstructiveFiniteMatrix.sumFin
              (fun column => matrix row column * vector column) *
            weights row) := by
        apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
        intro row
        rw [RFAP.ConstructiveFiniteMatrix.matrixVector,
          RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply]
        rfl
    _ =
        RFAP.ConstructiveFiniteMatrix.sumFin
          (fun row => RFAP.ConstructiveFiniteMatrix.sumFin
            (fun column =>
              (matrix row column * vector column) * weights row)) := by
                apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
                intro row
                rw [RFAP.ConstructiveFiniteMatrix.sumFin_mul_right]
    _ = RFAP.ConstructiveFiniteMatrix.sumFin
          (fun column => RFAP.ConstructiveFiniteMatrix.sumFin
            (fun row =>
              (matrix row column * vector column) * weights row)) :=
      RFAP.ConstructiveFiniteMatrix.sumFin_swap _
    _ = RFAP.ConstructiveFiniteMatrix.sumFin
          (fun column =>
            RFAP.ConstructiveFiniteMatrix.sumFin
                (fun row => matrix row column * weights row) *
              vector column) := by
                apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
                intro column
                rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
                  (right := fun row =>
                    (matrix row column * weights row) * vector column)
                  (fun _ => by ring1)]
                rw [RFAP.ConstructiveFiniteMatrix.sumFin_mul_right]

def separatedData (p : GaussianPolynomial) :=
  RFAP.ConstructivePolynomialMatrix.scaledInverseData
    (p.natDegree + p.natDegree) (separatedSylvester p)

def firstColumnIndex (p : GaussianPolynomial)
    (degreePositive : 0 < p.natDegree) :
    Fin (p.natDegree + p.natDegree) :=
  ⟨0, by omega⟩

def leftCofactor (p : GaussianPolynomial)
    (degreePositive : 0 < p.natDegree) (parameter : Gaussian) :
    GaussianPolynomial :=
  polynomialFromLow p.natDegree (fun index =>
    ((separatedData p).inverse (Fin.castAdd p.natDegree index)
      (firstColumnIndex p degreePositive)).eval parameter)

def rightCofactor (p : GaussianPolynomial)
    (degreePositive : 0 < p.natDegree) (parameter : Gaussian) :
    GaussianPolynomial :=
  polynomialFromLow p.natDegree (fun index =>
    ((separatedData p).inverse (Fin.natAdd p.natDegree index)
      (firstColumnIndex p degreePositive)).eval parameter)

/-- The specialized first inverse column is an explicit Bézout identity for
the separated pair. -/
theorem separated_bezout_identity (p : GaussianPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (outer parameter : Gaussian) :
    (leftCofactor p degreePositive parameter).eval outer *
        RFAP.ConstructiveBivariate.eval (reflected p) outer parameter +
      (rightCofactor p degreePositive parameter).eval outer *
        RFAP.ConstructiveBivariate.eval (lifted p) outer parameter =
      (separatedData p).scalar.eval parameter := by
  let size := p.natDegree + p.natDegree
  let matrix := RFAP.ConstructivePolynomialMatrix.evalMatrix parameter
    (separatedSylvester p)
  let inverse := RFAP.ConstructivePolynomialMatrix.evalMatrix parameter
    (separatedData p).inverse
  let scalar := (separatedData p).scalar.eval parameter
  let first := firstColumnIndex p degreePositive
  let vector : RFAP.ConstructiveFiniteMatrix.Vector Gaussian size :=
    RFAP.ConstructiveFiniteMatrix.vectorOfFn fun column =>
      inverse column first
  let weights : RFAP.ConstructiveFiniteMatrix.Vector Gaussian size :=
    RFAP.ConstructiveFiniteMatrix.vectorOfFn fun row => outer ^ (row : Nat)
  have inverseIdentity :=
    (RFAP.ConstructivePolynomialMatrix.scaledInverseData_spec parameter size
      (separatedSylvester p)).2
  have matrixVectorIdentity :
      RFAP.ConstructiveFiniteMatrix.matrixVector matrix vector =
        RFAP.ConstructiveFiniteMatrix.vectorOfFn fun row =>
          if row = first then scalar else 0 := by
    apply RFAP.ConstructiveFiniteMatrix.vector_ext
    intro row
    have entryIdentity := RFAP.ConstructiveFiniteMatrix.matrix_eq_at
      inverseIdentity row first
    change RFAP.ConstructiveFiniteMatrix.mul matrix inverse row first =
      RFAP.ConstructiveFiniteMatrix.scaleIdentity scalar row first
      at entryIdentity
    rw [RFAP.ConstructiveFiniteMatrix.mul,
      RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
      RFAP.ConstructiveFiniteMatrix.scaleIdentity,
      RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply] at entryIdentity
    rw [RFAP.ConstructiveFiniteMatrix.matrixVector,
      RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
      RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply]
    exact entryIdentity
  have weightedIdentity :
      RFAP.ConstructiveFiniteMatrix.sumFin
          (fun row =>
            RFAP.ConstructiveFiniteMatrix.matrixVector matrix vector row *
              weights row) = scalar := by
    rw [matrixVectorIdentity]
    rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
      (left := fun row =>
        (RFAP.ConstructiveFiniteMatrix.vectorOfFn fun row =>
          if row = first then scalar else 0) row * weights row)
      (right := fun row =>
        (if row = first then scalar else 0) * weights row)
      (fun row => by
        rw [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply])]
    rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
      (left := fun row =>
        (if row = first then scalar else 0) * weights row)
      (right := fun row =>
        if row = first then scalar * weights row else 0)
      (fun row => by
        split <;> ring1)]
    rw [RFAP.ConstructiveFiniteMatrix.sumFin_ite_eq]
    simp only [weights, first,
      RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply, firstColumnIndex]
    change scalar * outer ^ (0 : Nat) = scalar
    rw [pow_zero, mul_one]
  have columnIdentity := weighted_matrixVector matrix vector weights
  rw [weightedIdentity] at columnIdentity
  calc
    (leftCofactor p degreePositive parameter).eval outer *
          RFAP.ConstructiveBivariate.eval (reflected p) outer parameter +
        (rightCofactor p degreePositive parameter).eval outer *
          RFAP.ConstructiveBivariate.eval (lifted p) outer parameter =
      RFAP.ConstructiveFiniteMatrix.sumFin
        (fun column : Fin size =>
          RFAP.ConstructiveFiniteMatrix.sumFin
              (fun row : Fin size => matrix row column * weights row) *
            vector column) := by
              rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
                (left := fun column : Fin size =>
                  RFAP.ConstructiveFiniteMatrix.sumFin
                      (fun row : Fin size => matrix row column * weights row) *
                    vector column)
                (right := fun column : Fin size =>
                  QuotientFreeFin.addCases
                    (fun index =>
                      (outer ^ (index : Nat) *
                        RFAP.ConstructiveBivariate.eval (reflected p)
                          outer parameter) * vector (Fin.castAdd p.natDegree index))
                    (fun index =>
                      (outer ^ (index : Nat) *
                        RFAP.ConstructiveBivariate.eval (lifted p)
                          outer parameter) * vector
                            (Fin.natAdd p.natDegree index)) column)
                (fun column => by
                  rcases QuotientFreeFin.addCases_split column with
                    ⟨index, rfl⟩ | ⟨index, rfl⟩
                  · simp only [QuotientFreeFin.addCases_left]
                    rw [show
                      RFAP.ConstructiveFiniteMatrix.sumFin
                          (fun row : Fin size =>
                            matrix row (Fin.castAdd p.natDegree index) *
                              weights row) =
                        outer ^ (index : Nat) *
                          RFAP.ConstructiveBivariate.eval (reflected p)
                            outer parameter by
                          calc
                            RFAP.ConstructiveFiniteMatrix.sumFin
                                (fun row : Fin size =>
                                  matrix row
                                      (Fin.castAdd p.natDegree index) *
                                    weights row) =
                                RFAP.ConstructiveFiniteMatrix.sumFin
                                  (fun row : Fin size =>
                                    RFAP.ConstructivePolynomialMatrix.evalMatrix
                                        parameter (separatedSylvester p) row
                                        (Fin.castAdd p.natDegree index) *
                                      outer ^ (row : Nat)) := by
                              apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
                              intro row
                              rw [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply]
                            _ = outer ^ (index : Nat) *
                                  RFAP.ConstructiveBivariate.eval (reflected p)
                                    outer parameter :=
                              separatedLeftColumnPowerSum p nonzero
                                outer parameter index]
                  · simp only [QuotientFreeFin.addCases_right]
                    rw [show
                      RFAP.ConstructiveFiniteMatrix.sumFin
                          (fun row : Fin size =>
                            matrix row (Fin.natAdd p.natDegree index) *
                              weights row) =
                        outer ^ (index : Nat) *
                          RFAP.ConstructiveBivariate.eval (lifted p)
                            outer parameter by
                          calc
                            RFAP.ConstructiveFiniteMatrix.sumFin
                                (fun row : Fin size =>
                                  matrix row
                                      (Fin.natAdd p.natDegree index) *
                                    weights row) =
                                RFAP.ConstructiveFiniteMatrix.sumFin
                                  (fun row : Fin size =>
                                    RFAP.ConstructivePolynomialMatrix.evalMatrix
                                        parameter (separatedSylvester p) row
                                        (Fin.natAdd p.natDegree index) *
                                      outer ^ (row : Nat)) := by
                              apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
                              intro row
                              rw [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply]
                            _ = outer ^ (index : Nat) *
                                  RFAP.ConstructiveBivariate.eval (lifted p)
                                    outer parameter :=
                              separatedRightColumnPowerSum p nonzero
                                outer parameter index])]
              rw [sumFin_addCases]
              unfold leftCofactor rightCofactor
              rw [eval_polynomialFromLow, eval_polynomialFromLow]
              rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
                (left := fun index : Fin p.natDegree =>
                  (outer ^ (index : Nat) *
                    RFAP.ConstructiveBivariate.eval (reflected p)
                      outer parameter) *
                    vector (Fin.castAdd p.natDegree index))
                (right := fun index : Fin p.natDegree =>
                  (((separatedData p).inverse
                    (Fin.castAdd p.natDegree index)
                    (firstColumnIndex p degreePositive)).eval parameter *
                      outer ^ (index : Nat)) *
                    RFAP.ConstructiveBivariate.eval (reflected p)
                      outer parameter)
                (fun index => by
                  dsimp only [vector, inverse]
                  rw [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
                    RFAP.ConstructivePolynomialMatrix.evalMatrix_apply]
                  ring1)]
              rw [RFAP.ConstructiveFiniteMatrix.sumFin_mul_right]
              rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
                (left := fun index : Fin p.natDegree =>
                  (outer ^ (index : Nat) *
                    RFAP.ConstructiveBivariate.eval (lifted p)
                      outer parameter) *
                    vector (Fin.natAdd p.natDegree index))
                (right := fun index : Fin p.natDegree =>
                  (((separatedData p).inverse
                    (Fin.natAdd p.natDegree index)
                    (firstColumnIndex p degreePositive)).eval parameter *
                      outer ^ (index : Nat)) *
                    RFAP.ConstructiveBivariate.eval (lifted p)
                      outer parameter)
                (fun index => by
                  dsimp only [vector, inverse]
                  rw [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
                    RFAP.ConstructivePolynomialMatrix.evalMatrix_apply]
                  ring1)]
              rw [RFAP.ConstructiveFiniteMatrix.sumFin_mul_right]
    _ = scalar := columnIdentity.symm
    _ = (separatedData p).scalar.eval parameter := rfl

/-! ## A nonzero rational-coordinate eliminant -/

/-- Select the real leading-coordinate polynomial unless that leading
coordinate is zero, in which case select the imaginary coordinate. -/
def selectedCoordinate (p : GaussianPolynomial) : CoordinatePolynomial :=
  if p.leadingCoeff.re = 0 then
    RFAP.PathPolynomial.imagPart p.normalize
  else RFAP.PathPolynomial.realPart p.normalize

theorem selectedCoordinate_nonzero (p : GaussianPolynomial)
    (nonzero : p.isZero = false) :
    (selectedCoordinate p).isZero = false := by
  have leadingNonzero := leadingCoeff_ne_zero nonzero
  cases coefficients : p.normalize.coeffs with
  | nil =>
      change p.normalize.coeffs.headD 0 ≠ 0 at leadingNonzero
      rw [coefficients] at leadingNonzero
      exact (leadingNonzero rfl).elim
  | cons leading remaining =>
      have leadingIdentity : p.leadingCoeff = leading := by
        simp only [leadingCoeff, coefficients, List.headD_cons]
      by_cases realZero : p.leadingCoeff.re = 0
      · rw [selectedCoordinate, if_pos realZero]
        have leadingRealZero : leading.re = 0 := by
          simpa only [leadingIdentity] using realZero
        have imaginaryNonzero : leading.im ≠ 0 := by
          intro imaginaryZero
          apply leadingNonzero
          rw [leadingIdentity]
          apply RFAP.ConstructiveGaussian.Gaussian.ext
          · exact leadingRealZero
          · exact imaginaryZero
        change ((p.normalize.coeffs.map
          RFAP.ConstructiveGaussian.Gaussian.im).dropWhile
            (· = 0)).isEmpty = false
        rw [coefficients]
        simp only [List.map_cons]
        rw [List.dropWhile_cons_of_neg (by simp [imaginaryNonzero])]
        rfl
      · rw [selectedCoordinate, if_neg realZero]
        have leadingRealNonzero : leading.re ≠ 0 := by
          simpa only [leadingIdentity] using realZero
        change ((p.normalize.coeffs.map
          RFAP.ConstructiveGaussian.Gaussian.re).dropWhile
            (· = 0)).isEmpty = false
        rw [coefficients]
        simp only [List.map_cons]
        rw [List.dropWhile_cons_of_neg (by simp [leadingRealNonzero])]
        rfl

@[simp] theorem eval_selectedCoordinate (p : GaussianPolynomial)
    (parameter : Coordinate) :
    (selectedCoordinate p).eval parameter =
      if p.leadingCoeff.re = 0 then
        (p.eval (RFAP.PathPolynomial.ofCoordinate parameter)).im
      else
        (p.eval (RFAP.PathPolynomial.ofCoordinate parameter)).re := by
  unfold selectedCoordinate
  split
  · rw [RFAP.PathPolynomial.eval_imagPart,
      eval_normalize]
  · rw [RFAP.PathPolynomial.eval_realPart,
      eval_normalize]

def scalarEliminant (p : GaussianPolynomial) : CoordinatePolynomial :=
  selectedCoordinate (separatedData p).scalar

theorem scalarEliminant_nonzero (p : GaussianPolynomial)
    (nonzero : p.isZero = false) :
    (scalarEliminant p).isZero = false :=
  selectedCoordinate_nonzero _ (separatedScalar_nonzero p nonzero)

theorem scalar_ne_zero_of_eliminant_eval_ne_zero
    (p : GaussianPolynomial) (parameter : Coordinate)
    (nonzeroEvaluation : (scalarEliminant p).eval parameter ≠ 0) :
    (separatedData p).scalar.eval
      (RFAP.PathPolynomial.ofCoordinate parameter) ≠ 0 := by
  intro scalarZero
  apply nonzeroEvaluation
  rw [scalarEliminant, eval_selectedCoordinate]
  rw [scalarZero]
  split <;> rfl

/-! ## Specialized rational Bézout certificates -/

def normalizedLeftCofactor (p : GaussianPolynomial)
    (degreePositive : 0 < p.natDegree) (parameter : Coordinate) :
    GaussianPolynomial :=
  let gaussianParameter :=
    RFAP.PathPolynomial.ofCoordinate parameter
  scale ((separatedData p).scalar.eval gaussianParameter)⁻¹
    (leftCofactor p degreePositive gaussianParameter)

def normalizedRightCofactor (p : GaussianPolynomial)
    (degreePositive : 0 < p.natDegree) (parameter : Coordinate) :
    GaussianPolynomial :=
  let gaussianParameter :=
    RFAP.PathPolynomial.ofCoordinate parameter
  scale ((separatedData p).scalar.eval gaussianParameter)⁻¹
    (rightCofactor p degreePositive gaussianParameter)

theorem normalizedSeparatedIdentity (p : GaussianPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (parameter : Coordinate)
    (scalarNonzero : (separatedData p).scalar.eval
      (RFAP.PathPolynomial.ofCoordinate parameter) ≠ 0)
    (outer : Gaussian) :
    (normalizedLeftCofactor p degreePositive parameter).eval outer *
        RFAP.ConstructiveBivariate.eval (reflected p) outer
          (RFAP.PathPolynomial.ofCoordinate parameter) +
      (normalizedRightCofactor p degreePositive parameter).eval outer *
        RFAP.ConstructiveBivariate.eval (lifted p) outer
          (RFAP.PathPolynomial.ofCoordinate parameter) = 1 := by
  rw [normalizedLeftCofactor, normalizedRightCofactor, eval_scale, eval_scale]
  let scalar := (separatedData p).scalar.eval
    (RFAP.PathPolynomial.ofCoordinate parameter)
  have identity := separated_bezout_identity p nonzero degreePositive outer
    (RFAP.PathPolynomial.ofCoordinate parameter)
  change scalar⁻¹ * (leftCofactor p degreePositive
      (RFAP.PathPolynomial.ofCoordinate parameter)).eval outer *
        RFAP.ConstructiveBivariate.eval (reflected p) outer
          (RFAP.PathPolynomial.ofCoordinate parameter) +
      scalar⁻¹ * (rightCofactor p degreePositive
        (RFAP.PathPolynomial.ofCoordinate parameter)).eval outer *
          RFAP.ConstructiveBivariate.eval (lifted p) outer
            (RFAP.PathPolynomial.ofCoordinate parameter) = 1
  calc
    scalar⁻¹ * (leftCofactor p degreePositive
          (RFAP.PathPolynomial.ofCoordinate parameter)).eval outer *
          RFAP.ConstructiveBivariate.eval (reflected p) outer
            (RFAP.PathPolynomial.ofCoordinate parameter) +
        scalar⁻¹ * (rightCofactor p degreePositive
          (RFAP.PathPolynomial.ofCoordinate parameter)).eval outer *
          RFAP.ConstructiveBivariate.eval (lifted p) outer
            (RFAP.PathPolynomial.ofCoordinate parameter) =
      scalar⁻¹ *
        ((leftCofactor p degreePositive
            (RFAP.PathPolynomial.ofCoordinate parameter)).eval outer *
            RFAP.ConstructiveBivariate.eval (reflected p) outer
              (RFAP.PathPolynomial.ofCoordinate parameter) +
          (rightCofactor p degreePositive
            (RFAP.PathPolynomial.ofCoordinate parameter)).eval outer *
            RFAP.ConstructiveBivariate.eval (lifted p) outer
              (RFAP.PathPolynomial.ofCoordinate parameter)) := by
                rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
                  RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
                exact
                  (RFAP.ConstructiveGaussian.Gaussian.left_distrib _ _ _).symm
    _ = scalar⁻¹ * scalar := by rw [identity]
    _ = 1 := by
      rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq]
      exact RFAP.ConstructiveGaussian.Gaussian.inv_mul scalar scalarNonzero

private theorem verticalReflection (x y : Coordinate) :
    RFAP.ConstructiveGaussian.Gaussian.conj
      (2 * RFAP.PathPolynomial.ofCoordinate x -
        RFAP.Winding.point x y) =
      RFAP.Winding.point x y := by
  rw [show (2 : Gaussian) *
      RFAP.PathPolynomial.ofCoordinate x =
    RFAP.PathPolynomial.ofCoordinate x +
      RFAP.PathPolynomial.ofCoordinate x by ring1]
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · simp only [RFAP.ConstructiveGaussian.Gaussian.conj,
      RFAP.PathPolynomial.ofCoordinate,
      RFAP.Winding.point,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_re]
    ring1
  · simp only [RFAP.ConstructiveGaussian.Gaussian.conj,
      RFAP.PathPolynomial.ofCoordinate,
      RFAP.Winding.point,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_im]
    ring1

def verticalBezoutLeft (p : GaussianPolynomial)
    (degreePositive : 0 < p.natDegree) (x : Coordinate) :
    CoordinatePolynomial :=
  RFAP.PathPolynomial.pathReal
      (normalizedLeftCofactor p degreePositive x)
      (RFAP.Winding.verticalBase x)
      RFAP.Winding.verticalDirection +
    RFAP.PathPolynomial.pathReal
      (normalizedRightCofactor p degreePositive x)
      (RFAP.Winding.verticalBase x)
      RFAP.Winding.verticalDirection

def verticalBezoutRight (p : GaussianPolynomial)
    (degreePositive : 0 < p.natDegree) (x : Coordinate) :
    CoordinatePolynomial :=
  RFAP.PathPolynomial.pathImag
      (normalizedLeftCofactor p degreePositive x)
      (RFAP.Winding.verticalBase x)
      RFAP.Winding.verticalDirection -
    RFAP.PathPolynomial.pathImag
      (normalizedRightCofactor p degreePositive x)
      (RFAP.Winding.verticalBase x)
      RFAP.Winding.verticalDirection

def verticalCoprimeCertificate (p : GaussianPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (x : Coordinate) (eliminantNonzero : (scalarEliminant p).eval x ≠ 0) :
    RFAP.PathClearance.CoprimeCertificate
      (RFAP.PathPolynomial.pathReal p
        (RFAP.Winding.verticalBase x)
        RFAP.Winding.verticalDirection)
      (RFAP.PathPolynomial.pathImag p
        (RFAP.Winding.verticalBase x)
        RFAP.Winding.verticalDirection) where
  left := verticalBezoutLeft p degreePositive x
  right := verticalBezoutRight p degreePositive x
  identity := by
    intro y
    let point := RFAP.Winding.point x y
    have scalarNonzero := scalar_ne_zero_of_eliminant_eval_ne_zero p x
      eliminantNonzero
    have complexIdentity := normalizedSeparatedIdentity p nonzero
      degreePositive x scalarNonzero point
    rw [eval_reflected, eval_lifted, verticalReflection] at complexIdentity
    have realIdentity := congrArg RFAP.ConstructiveGaussian.Gaussian.re
      complexIdentity
    change 1 =
      (verticalBezoutLeft p degreePositive x).eval y *
          (RFAP.PathPolynomial.pathReal p
            (RFAP.Winding.verticalBase x)
            RFAP.Winding.verticalDirection).eval y +
        (verticalBezoutRight p degreePositive x).eval y *
          (RFAP.PathPolynomial.pathImag p
            (RFAP.Winding.verticalBase x)
            RFAP.Winding.verticalDirection).eval y
    simp only [verticalBezoutLeft, verticalBezoutRight, eval_add, eval_sub,
      RFAP.PathPolynomial.eval_pathReal,
      RFAP.PathPolynomial.eval_pathImag,
      RFAP.Winding.line_vertical]
    simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.one_re,
      RFAP.ConstructiveGaussian.Gaussian.conj] at realIdentity
    rw [← realIdentity]
    ring1

/-! ## Quarter-turn reduction for horizontal lines -/

def imaginaryUnit : Gaussian := ⟨0, 1⟩

def quarterTurnStep (state : GaussianPolynomial) (coefficient : Gaussian) :
    GaussianPolynomial :=
  shift 1 (scale imaginaryUnit state) + parameterConstant coefficient

def quarterTurn (p : GaussianPolynomial) : GaussianPolynomial :=
  match p.normalize.coeffs with
  | [] => 0
  | leading :: remaining =>
      remaining.foldl quarterTurnStep (parameterConstant leading)

private theorem eval_foldl_quarterTurnStep (z : Gaussian) :
    ∀ (coefficients : List Gaussian) (state : GaussianPolynomial)
      (value : Gaussian),
      state.eval z = value →
      (coefficients.foldl quarterTurnStep state).eval z =
        coefficients.foldl
          (fun accumulator coefficient =>
            accumulator * (z * imaginaryUnit) + coefficient) value
  | [], _, _, stateEvaluation => stateEvaluation
  | coefficient :: remaining, state, value, stateEvaluation => by
      simp only [List.foldl_cons]
      apply eval_foldl_quarterTurnStep z remaining
      rw [quarterTurnStep, eval_add, eval_shift, eval_scale,
        eval_parameterConstant, stateEvaluation]
      change imaginaryUnit * value * z ^ 1 + coefficient =
        value * (z * imaginaryUnit) + coefficient
      ring1

@[simp] theorem eval_quarterTurn (p : GaussianPolynomial) (z : Gaussian) :
    (quarterTurn p).eval z = p.eval (z * imaginaryUnit) := by
  rw [← eval_normalize p (z * imaginaryUnit)]
  change (quarterTurn p).eval z =
    p.normalize.coeffs.foldl
      (fun value coefficient =>
        value * (z * imaginaryUnit) + coefficient) 0
  cases coefficients : p.normalize.coeffs with
  | nil =>
      rw [quarterTurn, coefficients, eval_zero]
      change 0 = [].foldl
        (fun value coefficient =>
          value * (z * imaginaryUnit) + coefficient) 0
      rfl
  | cons leading remaining =>
      rw [quarterTurn, coefficients]
      have initial : (parameterConstant leading).eval z = leading :=
        eval_parameterConstant leading z
      rw [eval_foldl_quarterTurnStep z remaining
        (parameterConstant leading) leading initial]
      simp only [List.foldl_cons]
      change remaining.foldl
          (fun value coefficient =>
            value * (z * imaginaryUnit) + coefficient) leading =
        remaining.foldl
          (fun value coefficient =>
            value * (z * imaginaryUnit) + coefficient)
          (0 * (z * imaginaryUnit) + leading)
      rw [zero_mul, zero_add]

def quarterTurnLeadingStep (leading : Gaussian) (_ : Gaussian) : Gaussian :=
  imaginaryUnit * leading

private theorem foldl_quarterTurnLeading :
    ∀ (coefficients : List Gaussian) (state : GaussianPolynomial)
      (degree : Nat) (leading : Gaussian),
      RFAP.ConstructivePolynomialLeading.LeadingTerm state degree leading →
      RFAP.ConstructivePolynomialLeading.LeadingTerm
        (coefficients.foldl quarterTurnStep state)
        (degree + coefficients.length)
        (coefficients.foldl quarterTurnLeadingStep leading)
  | [], _, _, _, shape => shape
  | coefficient :: remaining, state, degree, leading, shape => by
      simp only [List.foldl_cons, List.length_cons]
      have imaginaryNonzero : imaginaryUnit ≠ 0 := by decide
      have scaled := RFAP.ConstructivePolynomialLeading.LeadingTerm.scale
        imaginaryNonzero shape
      have shifted := RFAP.ConstructivePolynomialLeading.LeadingTerm.shift 1 scaled
      have coefficientBelow :
        RFAP.ConstructivePolynomialLeading.DegreeBelow
            (parameterConstant coefficient) (degree + 1) :=
        RFAP.ConstructivePolynomialLeading.DegreeBelow.mono
          (parameterConstant_atMost coefficient).toBelowSucc
          (Nat.succ_le_succ (Nat.zero_le degree))
      have next : RFAP.ConstructivePolynomialLeading.LeadingTerm
          (quarterTurnStep state coefficient) (degree + 1)
          (imaginaryUnit * leading) := by
        unfold quarterTurnStep
        exact RFAP.ConstructivePolynomialLeading.LeadingTerm.addBelow shifted
          coefficientBelow
      have final := foldl_quarterTurnLeading remaining
        (quarterTurnStep state coefficient) (degree + 1)
        (imaginaryUnit * leading) next
      exact RFAP.ConstructivePolynomialLeading.LeadingTerm.of_equal
        rfl
        (by
          calc
            degree + (remaining.length + 1) =
                degree + (1 + remaining.length) :=
              congrArg (fun value => degree + value)
                (Nat.add_comm remaining.length 1)
            _ = degree + 1 + remaining.length :=
              (Nat.add_assoc degree 1 remaining.length).symm)
        rfl final

def quarterTurnLeading (p : GaussianPolynomial) : Gaussian :=
  match p.normalize.coeffs with
  | [] => 0
  | leading :: remaining =>
      remaining.foldl quarterTurnLeadingStep leading

theorem quarterTurn_shape (p : GaussianPolynomial)
    (nonzero : p.isZero = false) :
    RFAP.ConstructivePolynomialLeading.LeadingTerm (quarterTurn p)
      p.natDegree (quarterTurnLeading p) := by
  cases coefficients : p.normalize.coeffs with
  | nil =>
      have contradiction := nonzero
      change p.normalize.coeffs.isEmpty = false at contradiction
      rw [coefficients] at contradiction
      exact Bool.noConfusion contradiction
  | cons leading remaining =>
      have leadingNonzero : leading ≠ 0 := by
        have := leadingCoeff_ne_zero nonzero
        change p.normalize.coeffs.headD 0 ≠ 0 at this
        simpa only [coefficients, List.headD_cons] using this
      have initial := parameterConstant_leading leadingNonzero
      have folded := foldl_quarterTurnLeading remaining
        (parameterConstant leading) 0 leading initial
      have degreeIdentity : p.natDegree = remaining.length := by
        have count := natDegree_add_one_eq_degreeCount nonzero
        rw [degreeCount, coefficients] at count
        simp only [List.length_cons] at count
        exact Nat.add_right_cancel count
      exact RFAP.ConstructivePolynomialLeading.LeadingTerm.of_equal
        (by rw [quarterTurn, coefficients])
        (by rw [degreeIdentity, Nat.zero_add])
        (by rw [quarterTurnLeading, coefficients]) folded

theorem quarterTurn_nonzero (p : GaussianPolynomial)
    (nonzero : p.isZero = false) : (quarterTurn p).isZero = false :=
  (quarterTurn_shape p nonzero).nonzero

theorem quarterTurn_natDegree (p : GaussianPolynomial)
    (nonzero : p.isZero = false) :
    (quarterTurn p).natDegree = p.natDegree :=
  (quarterTurn_shape p nonzero).degree_eq

def horizontalEliminant (p : GaussianPolynomial) : CoordinatePolynomial :=
  scalarEliminant (quarterTurn p)

theorem horizontalEliminant_nonzero (p : GaussianPolynomial)
    (nonzero : p.isZero = false) :
    (horizontalEliminant p).isZero = false :=
  scalarEliminant_nonzero (quarterTurn p) (quarterTurn_nonzero p nonzero)

def negativeVerticalDirection : Gaussian := ⟨0, -1⟩

@[simp] theorem line_negativeVertical (y x : Coordinate) :
    RFAP.PathPolynomial.line
      (RFAP.Winding.verticalBase y) negativeVerticalDirection x =
      RFAP.Winding.point y (-x) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · change y + (x * 0 - 0 * -1) = y
    ring1
  · change 0 + (x * -1 + 0 * 0) = -x
    ring1

@[simp] theorem quarterTurn_horizontalPoint (x y : Coordinate) :
    RFAP.Winding.point y (-x) * imaginaryUnit =
      RFAP.Winding.point x y := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · change y * 0 - -x * 1 = x
    ring1
  · change y * 1 + -x * 0 = y
    ring1

def horizontalBezoutLeft (p : GaussianPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (y : Coordinate) : CoordinatePolynomial :=
  let rotated := quarterTurn p
  let rotatedDegreePositive : 0 < rotated.natDegree := by
    rw [quarterTurn_natDegree p nonzero]
    exact degreePositive
  RFAP.PathPolynomial.pathReal
      (normalizedLeftCofactor rotated rotatedDegreePositive y)
      (RFAP.Winding.verticalBase y) negativeVerticalDirection +
    RFAP.PathPolynomial.pathReal
      (normalizedRightCofactor rotated rotatedDegreePositive y)
      (RFAP.Winding.verticalBase y) negativeVerticalDirection

def horizontalBezoutRight (p : GaussianPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (y : Coordinate) : CoordinatePolynomial :=
  let rotated := quarterTurn p
  let rotatedDegreePositive : 0 < rotated.natDegree := by
    rw [quarterTurn_natDegree p nonzero]
    exact degreePositive
  RFAP.PathPolynomial.pathImag
      (normalizedLeftCofactor rotated rotatedDegreePositive y)
      (RFAP.Winding.verticalBase y) negativeVerticalDirection -
    RFAP.PathPolynomial.pathImag
      (normalizedRightCofactor rotated rotatedDegreePositive y)
      (RFAP.Winding.verticalBase y) negativeVerticalDirection

def horizontalCoprimeCertificate (p : GaussianPolynomial)
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (y : Coordinate)
    (eliminantNonzero : (horizontalEliminant p).eval y ≠ 0) :
    RFAP.PathClearance.CoprimeCertificate
      (RFAP.PathPolynomial.pathReal p
        (RFAP.Winding.horizontalBase y)
        RFAP.Winding.horizontalDirection)
      (RFAP.PathPolynomial.pathImag p
        (RFAP.Winding.horizontalBase y)
        RFAP.Winding.horizontalDirection) := by
  let rotated := quarterTurn p
  have rotatedNonzero : rotated.isZero = false := quarterTurn_nonzero p nonzero
  have rotatedDegreePositive : 0 < rotated.natDegree := by
    rw [quarterTurn_natDegree p nonzero]
    exact degreePositive
  let left := normalizedLeftCofactor rotated rotatedDegreePositive y
  let right := normalizedRightCofactor rotated rotatedDegreePositive y
  exact
    { left := horizontalBezoutLeft p nonzero degreePositive y
      right := horizontalBezoutRight p nonzero degreePositive y
      identity := by
        intro x
        let rotatedPoint := RFAP.Winding.point y (-x)
        have scalarNonzero := scalar_ne_zero_of_eliminant_eval_ne_zero
          rotated y eliminantNonzero
        have complexIdentity := normalizedSeparatedIdentity rotated
          rotatedNonzero rotatedDegreePositive y scalarNonzero rotatedPoint
        rw [eval_reflected, eval_lifted, verticalReflection,
          eval_quarterTurn, quarterTurn_horizontalPoint] at complexIdentity
        have realIdentity := congrArg RFAP.ConstructiveGaussian.Gaussian.re
          complexIdentity
        change 1 =
          (horizontalBezoutLeft p nonzero degreePositive y).eval x *
              (RFAP.PathPolynomial.pathReal p
                (RFAP.Winding.horizontalBase y)
                RFAP.Winding.horizontalDirection).eval x +
            (horizontalBezoutRight p nonzero degreePositive y).eval x *
              (RFAP.PathPolynomial.pathImag p
                (RFAP.Winding.horizontalBase y)
                RFAP.Winding.horizontalDirection).eval x
        simp only [horizontalBezoutLeft, horizontalBezoutRight,
          eval_add, eval_sub,
          RFAP.PathPolynomial.eval_pathReal,
          RFAP.PathPolynomial.eval_pathImag,
          line_negativeVertical,
          RFAP.Winding.line_horizontal]
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.mul_re,
          RFAP.ConstructiveGaussian.Gaussian.one_re,
          RFAP.ConstructiveGaussian.Gaussian.conj] at realIdentity
        rw [← realIdentity]
        ring1 }

end RFAP.ConstructiveSylvesterBezout
