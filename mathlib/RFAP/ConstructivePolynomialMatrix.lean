import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructiveBivariate
import mathlib.RFAP.ConstructiveFiniteMatrix

/-!
# Polynomial-valued fraction-free matrix inversion

The block recursion is run symbolically over dense coordinate polynomials.
Evaluation at any coordinate commutes with every finite sum and block
operation, so the resulting scalar and matrix specialize to the constructive
scaled inverse from `RFAP.ConstructiveFiniteMatrix`.
-/

namespace RFAP.ConstructivePolynomialMatrix

abbrev Polynomial (K : Type*) := RFAP.ComputablePolynomial.DensePolynomial K
abbrev Vector (K : Type*) (n : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Vector (Polynomial K) n
abbrev Matrix (K : Type*) (n : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Matrix (Polynomial K) n

variable {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]

open RFAP.ComputablePolynomial.DensePolynomial

def sumFin {n : Nat} (values : Fin n → Polynomial K) : Polynomial K :=
  (List.ofFn values).foldl (fun a b => a + b) 0

theorem sumFin_congr {n : Nat} {left right : Fin n → Polynomial K}
    (equal : ∀ index, left index = right index) :
    sumFin left = sumFin right := by
  unfold sumFin
  rw [QuotientFreeList.ofFn_congr equal]

def dot {n : Nat} (left right : Vector K n) : Polynomial K :=
  sumFin (fun i => left i * right i)

def mul {n : Nat} (left right : Matrix K n) : Matrix K n :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    dot (left row) (RFAP.ConstructiveFiniteMatrix.vectorOfFn fun middle =>
      right middle column)

def scaleIdentity {n : Nat} (a : Polynomial K) : Matrix K n :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    if row = column then a else 0

def head (matrix : Matrix K (n + 1)) : Polynomial K := matrix 0 0

def topRow (matrix : Matrix K (n + 1)) : Vector K n :=
  RFAP.ConstructiveFiniteMatrix.vectorOfFn fun column =>
    matrix 0 column.succ

def leftColumn (matrix : Matrix K (n + 1)) : Vector K n :=
  RFAP.ConstructiveFiniteMatrix.vectorOfFn fun row => matrix row.succ 0

omit [RFAP.ExplicitField K] [DecidableEq K] in
@[simp] theorem topRow_apply (matrix : Matrix K (n + 1))
    (column : Fin n) :
    topRow matrix column = matrix 0 column.succ := by
  exact RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply _ _

omit [RFAP.ExplicitField K] [DecidableEq K] in
@[simp] theorem leftColumn_apply (matrix : Matrix K (n + 1))
    (row : Fin n) :
    leftColumn matrix row = matrix row.succ 0 := by
  exact RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply _ _

def tail (matrix : Matrix K (n + 1)) : Matrix K n :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    matrix row.succ column.succ

omit [RFAP.ExplicitField K] [DecidableEq K] in
@[simp] theorem tail_apply (matrix : Matrix K (n + 1))
    (row column : Fin n) :
    tail matrix row column = matrix row.succ column.succ := by
  exact RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

def schur (matrix : Matrix K (n + 1)) : Matrix K n :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    head matrix * tail matrix row column -
      leftColumn matrix row * topRow matrix column

theorem schur_apply (matrix : Matrix K (n + 1))
    (row column : Fin n) :
    schur matrix row column =
      head matrix * tail matrix row column -
        leftColumn matrix row * topRow matrix column := by
  unfold schur
  rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]

def matrixVector {n : Nat} (matrix : Matrix K n) (vector : Vector K n) :
    Vector K n :=
  RFAP.ConstructiveFiniteMatrix.vectorOfFn fun row => dot (matrix row) vector

def vectorMatrix {n : Nat} (vector : Vector K n) (matrix : Matrix K n) :
    Vector K n :=
  RFAP.ConstructiveFiniteMatrix.vectorOfFn fun column =>
    dot vector (RFAP.ConstructiveFiniteMatrix.vectorOfFn fun row =>
      matrix row column)

structure ScaledInverseData (K : Type*) (n : Nat) where
  scalar : Polynomial K
  inverse : Matrix K n

def blockInverse {n : Nat} (matrix : Matrix K (n + 1))
    (smaller : ScaledInverseData K n) : Matrix K (n + 1) :=
  let a := head matrix
  let row := topRow matrix
  let column := leftColumn matrix
  let inverse := smaller.inverse
  let inverseColumn := matrixVector inverse column
  let rowInverse := vectorMatrix row inverse
  let corner := smaller.scalar + dot row inverseColumn
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun i j => i.cases
    (j.cases corner (fun columnIndex => -a * rowInverse columnIndex))
    (fun rowIndex => j.cases
      (-a * inverseColumn rowIndex)
      (fun columnIndex => (a * a) * inverse rowIndex columnIndex))

/-- The symbolic division-free block inverse evaluated at one finite
entry. -/
theorem blockInverse_apply {n : Nat} (matrix : Matrix K (n + 1))
    (smaller : ScaledInverseData K n) (row column : Fin (n + 1)) :
    blockInverse matrix smaller row column =
      row.cases
        (column.cases
          (smaller.scalar + dot (topRow matrix)
            (matrixVector smaller.inverse (leftColumn matrix)))
          (fun columnIndex =>
            -head matrix * vectorMatrix (topRow matrix) smaller.inverse
              columnIndex))
        (fun rowIndex => column.cases
          (-head matrix * matrixVector smaller.inverse (leftColumn matrix)
            rowIndex)
          (fun columnIndex =>
            (head matrix * head matrix) *
              smaller.inverse rowIndex columnIndex)) := by
  unfold blockInverse
  rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]

/-- Total fraction-free recursion.  Nonvanishing of its scalar is proved
separately from leading-term data for the particular Sylvester matrix. -/
def scaledInverseData : (n : Nat) → Matrix K n → ScaledInverseData K n
  | 0, _ =>
      { scalar := constant 1
        inverse := RFAP.ConstructiveFiniteMatrix.matrixOfFn fun index =>
          Fin.elim0 index }
  | n + 1, matrix =>
      let smaller := scaledInverseData n (schur matrix)
      { scalar := head matrix * smaller.scalar
        inverse := blockInverse matrix smaller }

def evalVector (t : K) (vector : Vector K n) :
    RFAP.ConstructiveFiniteMatrix.Vector K n :=
  RFAP.ConstructiveFiniteMatrix.vectorOfFn fun i => (vector i).eval t

def evalMatrix (t : K) (matrix : Matrix K n) :
    RFAP.ConstructiveFiniteMatrix.Matrix K n :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    (matrix row column).eval t

omit [DecidableEq K] in
@[simp] theorem evalVector_apply (t : K) (vector : Vector K n)
    (index : Fin n) :
    evalVector t vector index = (vector index).eval t := by
  exact RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply _ _

omit [DecidableEq K] in
@[simp] theorem evalMatrix_apply (t : K) (matrix : Matrix K n)
    (row column : Fin n) :
    evalMatrix t matrix row column = (matrix row column).eval t := by
  exact RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

omit [DecidableEq K] in
@[simp] theorem evalVector_vectorOfFn (t : K)
    (entries : Fin n → Polynomial K) :
    evalVector t (RFAP.ConstructiveFiniteMatrix.vectorOfFn entries) =
      RFAP.ConstructiveFiniteMatrix.vectorOfFn fun index =>
        (entries index).eval t := by
  apply RFAP.ConstructiveFiniteMatrix.vector_ext
  intro index
  simp only [evalVector_apply,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply]

omit [DecidableEq K] in
@[simp] theorem evalMatrix_row (t : K) (matrix : Matrix K n)
    (row : Fin n) :
    evalMatrix t matrix row = evalVector t (matrix row) := by
  apply RFAP.ConstructiveFiniteMatrix.vector_ext
  intro column
  simp only [evalMatrix_apply, evalVector_apply]

omit [DecidableEq K] in
@[simp] theorem eval_head (t : K) (matrix : Matrix K (n + 1)) :
    RFAP.ConstructiveFiniteMatrix.head (evalMatrix t matrix) =
      (head matrix).eval t := by
  simp only [RFAP.ConstructiveFiniteMatrix.head, head, evalMatrix_apply]

omit [DecidableEq K] in
@[simp] theorem eval_topRow (t : K) (matrix : Matrix K (n + 1)) :
    RFAP.ConstructiveFiniteMatrix.topRow (evalMatrix t matrix) =
      evalVector t (topRow matrix) := by
  apply RFAP.ConstructiveFiniteMatrix.vector_ext
  intro column
  rw [RFAP.ConstructiveFiniteMatrix.topRow_apply, evalMatrix_apply,
    evalVector_apply, topRow_apply]

omit [DecidableEq K] in
@[simp] theorem eval_leftColumn (t : K) (matrix : Matrix K (n + 1)) :
    RFAP.ConstructiveFiniteMatrix.leftColumn (evalMatrix t matrix) =
      evalVector t (leftColumn matrix) := by
  apply RFAP.ConstructiveFiniteMatrix.vector_ext
  intro row
  rw [RFAP.ConstructiveFiniteMatrix.leftColumn_apply, evalMatrix_apply,
    evalVector_apply, leftColumn_apply]

-- `DecidableEq K` is inherited from the surrounding section but is not used
-- here; omitting it prevents the unused-section-variable linter warning.
omit [DecidableEq K] in
theorem eval_scaleIdentity (t : K) (a : Polynomial K) :
    evalMatrix t (scaleIdentity (n := n) a) =
      RFAP.ConstructiveFiniteMatrix.scaleIdentity (a.eval t) := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [evalMatrix_apply]
  unfold scaleIdentity
  rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
  unfold RFAP.ConstructiveFiniteMatrix.scaleIdentity
  rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
  by_cases equal : row = column
  · rw [if_pos equal, if_pos equal]
  · rw [if_neg equal, if_neg equal, eval_zero]

theorem eval_sumFin (t : K) (values : Fin n → Polynomial K) :
    (sumFin values).eval t =
      RFAP.ConstructiveFiniteMatrix.sumFin (fun i => (values i).eval t) := by
  have foldEvaluation (polynomials : List (Polynomial K))
      (accumulator : Polynomial K) :
      (polynomials.foldl (fun a b => a + b) accumulator).eval t =
        (polynomials.map (fun p => p.eval t)).foldl
          (fun a b => a + b) (accumulator.eval t) := by
    induction polynomials generalizing accumulator with
    | nil => rfl
    | cons polynomial remaining inductionHypothesis =>
        rw [List.foldl_cons, List.map_cons, List.foldl_cons,
          inductionHypothesis, eval_add]
  unfold sumFin RFAP.ConstructiveFiniteMatrix.sumFin
  rw [foldEvaluation]
  rw [eval_zero]
  rw [QuotientFreeList.map_ofFn]
  change (List.ofFn fun i => (values i).eval t).foldl
      (fun a b => a + b) 0 =
    (List.ofFn fun i => (values i).eval t).foldl
      (fun a b => a + b) 0
  rfl

theorem eval_dot (t : K) (left right : Vector K n) :
    (dot left right).eval t =
      RFAP.ConstructiveFiniteMatrix.dot (evalVector t left)
        (evalVector t right) := by
  unfold dot RFAP.ConstructiveFiniteMatrix.dot
  rw [eval_sumFin]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro i
  simp only [eval_mul, evalVector,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply]

theorem eval_matrixMul (t : K) (left right : Matrix K n) :
    evalMatrix t (mul left right) =
      RFAP.ConstructiveFiniteMatrix.mul
        (evalMatrix t left) (evalMatrix t right) := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [evalMatrix_apply]
  unfold mul
  rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.mul_apply]
  rw [eval_dot]
  unfold RFAP.ConstructiveFiniteMatrix.dot
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro middle
  simp only [evalVector_apply,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
    evalMatrix_apply]

theorem eval_matrixVector (t : K) (matrix : Matrix K n)
    (vector : Vector K n) :
    evalVector t (matrixVector matrix vector) =
      RFAP.ConstructiveFiniteMatrix.matrixVector
        (evalMatrix t matrix) (evalVector t vector) := by
  apply RFAP.ConstructiveFiniteMatrix.vector_ext
  intro row
  simp only [evalVector_apply, matrixVector,
    RFAP.ConstructiveFiniteMatrix.matrixVector,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply]
  simpa only [evalMatrix_row] using eval_dot t (matrix row) vector

theorem eval_vectorMatrix (t : K) (vector : Vector K n)
    (matrix : Matrix K n) :
    evalVector t (vectorMatrix vector matrix) =
      RFAP.ConstructiveFiniteMatrix.vectorMatrix
        (evalVector t vector) (evalMatrix t matrix) := by
  apply RFAP.ConstructiveFiniteMatrix.vector_ext
  intro column
  rw [evalVector_apply, vectorMatrix,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.vectorMatrix,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply, eval_dot]
  apply congrArg (RFAP.ConstructiveFiniteMatrix.dot (evalVector t vector))
  apply RFAP.ConstructiveFiniteMatrix.vector_ext
  intro row
  rw [evalVector_apply,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
    RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
    evalMatrix_apply]

theorem eval_schur (t : K) (matrix : Matrix K (n + 1)) :
    evalMatrix t (schur matrix) =
      RFAP.ConstructiveFiniteMatrix.schur (evalMatrix t matrix) := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [evalMatrix_apply, schur_apply, eval_sub, eval_mul,
    eval_mul, RFAP.ConstructiveFiniteMatrix.schur_apply,
    head, RFAP.ConstructiveFiniteMatrix.head,
    tail_apply, RFAP.ConstructiveFiniteMatrix.tail_apply,
    leftColumn_apply, RFAP.ConstructiveFiniteMatrix.leftColumn_apply,
    topRow_apply, RFAP.ConstructiveFiniteMatrix.topRow_apply,
    evalMatrix_apply, evalMatrix_apply, evalMatrix_apply, evalMatrix_apply]

theorem eval_blockInverse (t : K) (matrix : Matrix K (n + 1))
    (smaller : ScaledInverseData K n)
    (certificate : RFAP.ConstructiveFiniteMatrix.ScaledInverse
      (RFAP.ConstructiveFiniteMatrix.schur (evalMatrix t matrix)))
    (scalarEqual : certificate.scalar = smaller.scalar.eval t)
    (inverseEqual : certificate.inverse = evalMatrix t smaller.inverse) :
    evalMatrix t (blockInverse matrix smaller) =
      RFAP.ConstructiveFiniteMatrix.blockInverse (evalMatrix t matrix)
        certificate := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [evalMatrix_apply, blockInverse_apply,
    RFAP.ConstructiveFiniteMatrix.blockInverse_apply,
    scalarEqual, inverseEqual]
  refine Fin.cases ?_ (fun rowIndex => ?_) row
  · refine Fin.cases ?_ (fun columnIndex => ?_) column
    · simp only [Fin.cases_zero]
      rw [eval_add, eval_dot, eval_matrixVector,
        eval_topRow, eval_leftColumn]
    · simp only [Fin.cases_zero, Fin.cases_succ]
      rw [eval_mul, eval_neg, eval_head]
      apply congrArg (fun value => -((head matrix).eval t) * value)
      have evaluated := RFAP.ConstructiveFiniteMatrix.vector_eq_at
        (eval_vectorMatrix t (topRow matrix) smaller.inverse) columnIndex
      rw [evalVector_apply] at evaluated
      rw [eval_topRow]
      exact evaluated
  · refine Fin.cases ?_ (fun columnIndex => ?_) column
    · simp only [Fin.cases_zero, Fin.cases_succ]
      rw [eval_mul, eval_neg, eval_head]
      apply congrArg (fun value => -((head matrix).eval t) * value)
      have evaluated := RFAP.ConstructiveFiniteMatrix.vector_eq_at
        (eval_matrixVector t smaller.inverse (leftColumn matrix)) rowIndex
      rw [evalVector_apply] at evaluated
      rw [eval_leftColumn]
      exact evaluated
    · simp only [Fin.cases_succ]
      rw [eval_mul, eval_mul, eval_head, evalMatrix_apply]
      ring1

/-- Every specialization of the symbolic recursion is a genuine two-sided
scaled inverse. -/
theorem scaledInverseData_spec (t : K) :
    ∀ (n : Nat) (matrix : Matrix K n),
      let data := scaledInverseData n matrix
      RFAP.ConstructiveFiniteMatrix.mul (evalMatrix t data.inverse)
          (evalMatrix t matrix) =
          RFAP.ConstructiveFiniteMatrix.scaleIdentity (data.scalar.eval t) ∧
        RFAP.ConstructiveFiniteMatrix.mul (evalMatrix t matrix)
          (evalMatrix t data.inverse) =
          RFAP.ConstructiveFiniteMatrix.scaleIdentity (data.scalar.eval t)
  | 0, matrix => by
      constructor
      · apply RFAP.ConstructiveFiniteMatrix.matrix_ext
        intro row
        exact Fin.elim0 row
      · apply RFAP.ConstructiveFiniteMatrix.matrix_ext
        intro row
        exact Fin.elim0 row
  | n + 1, matrix => by
      let smallerData := scaledInverseData n (schur matrix)
      have smallerSpecification :=
        scaledInverseData_spec t n (schur matrix)
      let smallerCertificate :
          RFAP.ConstructiveFiniteMatrix.ScaledInverse
            (RFAP.ConstructiveFiniteMatrix.schur (evalMatrix t matrix)) :=
        { scalar := smallerData.scalar.eval t
          inverse := evalMatrix t smallerData.inverse
          left_identity := by
            rw [← eval_schur]
            exact smallerSpecification.1
          right_identity := by
            rw [← eval_schur]
            exact smallerSpecification.2 }
      have blockEvaluation :
          evalMatrix t (blockInverse matrix smallerData) =
            RFAP.ConstructiveFiniteMatrix.blockInverse
              (evalMatrix t matrix) smallerCertificate :=
        eval_blockInverse t matrix smallerData smallerCertificate rfl rfl
      change
        RFAP.ConstructiveFiniteMatrix.mul
            (evalMatrix t (blockInverse matrix smallerData))
            (evalMatrix t matrix) =
            RFAP.ConstructiveFiniteMatrix.scaleIdentity
              ((head matrix * smallerData.scalar).eval t) ∧
          RFAP.ConstructiveFiniteMatrix.mul (evalMatrix t matrix)
            (evalMatrix t (blockInverse matrix smallerData)) =
            RFAP.ConstructiveFiniteMatrix.scaleIdentity
              ((head matrix * smallerData.scalar).eval t)
      rw [eval_mul]
      rw [blockEvaluation]
      exact
        ⟨by
            simpa only [eval_head] using
              RFAP.ConstructiveFiniteMatrix.blockInverse_mul
                (evalMatrix t matrix) smallerCertificate,
          by
            simpa only [eval_head] using
              RFAP.ConstructiveFiniteMatrix.mul_blockInverse
                (evalMatrix t matrix) smallerCertificate⟩

/-- Package the evaluated symbolic data as the finite matrix certificate. -/
def evaluatedScaledInverse (t : K) (matrix : Matrix K n) :
    RFAP.ConstructiveFiniteMatrix.ScaledInverse (evalMatrix t matrix) :=
  let data := scaledInverseData n matrix
  let specification := scaledInverseData_spec t n matrix
  { scalar := data.scalar.eval t
    inverse := evalMatrix t data.inverse
    left_identity := specification.1
    right_identity := specification.2 }

end RFAP.ConstructivePolynomialMatrix
