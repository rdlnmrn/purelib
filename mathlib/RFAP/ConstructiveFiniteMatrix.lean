import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ConstructivePolynomial

/-!
# Fraction-free finite matrix inversion

Vectors and matrices are dimension-indexed structural `Vector` data, exposed
through entry lookup, and every sum is a fold over `List.ofFn`.  A scaled
inverse records both multiplication identities.  The block extension below
is division-free: a pivot and a scaled inverse of its Schur complement produce
a scaled inverse of the whole matrix.
-/

namespace RFAP.ConstructiveFiniteMatrix

universe u

/-- Structural finite vectors retain their dimension in the carrier rather
than representing finite data by a function whose equality needs `funext`.
The inductive carrier is project-owned because the built-in array-backed
`Vector.ofFn` lookup theorem has a choice-bearing proof route. -/
inductive Vector (K : Type u) : Nat → Type u
  | nil : Vector K 0
  | cons {n : Nat} : K → Vector K n → Vector K (n + 1)

/-- Total lookup follows the finite index and the structural vector in
lockstep. -/
def Vector.get {K : Type*} : {n : Nat} → Vector K n → Fin n → K
  | 0, .nil, index => Fin.elim0 index
  | _ + 1, .cons head tail, index =>
      Fin.cases head (fun tailIndex => tail.get tailIndex) index

instance vectorCoeFun {K : Type*} {n : Nat} :
    CoeFun (Vector K n) (fun _ => Fin n → K) where
  coe := Vector.get

/-- Materialize a bounded lookup function as structural vector data. -/
def vectorOfFn {K : Type*} : {n : Nat} → (Fin n → K) → Vector K n
  | 0, _ => .nil
  | _ + 1, entries =>
      .cons (entries 0) (vectorOfFn fun index => entries index.succ)

@[simp] theorem vectorOfFn_apply {K : Type*} {n : Nat}
    (entries : Fin n → K) (index : Fin n) :
    vectorOfFn entries index = entries index := by
  induction n with
  | zero => exact Fin.elim0 index
  | succ n inductionHypothesis =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · rfl
      · exact inductionHypothesis
          (fun nextIndex => entries nextIndex.succ) tailIndex

instance vectorOfFnCoe {K : Type*} {n : Nat} :
    Coe (Fin n → K) (Vector K n) where
  coe := vectorOfFn

/-- A square matrix is a structural vector of structural rows. -/
abbrev Matrix (K : Type*) (n : Nat) := Vector (Vector K n) n

/-- Materialize an entry function as structural square-matrix data. -/
def matrixOfFn {K : Type*} {n : Nat}
    (entries : Fin n → Fin n → K) : Matrix K n :=
  vectorOfFn fun row => vectorOfFn (entries row)

@[simp] theorem matrixOfFn_apply {K : Type*} {n : Nat}
    (entries : Fin n → Fin n → K) (row column : Fin n) :
    matrixOfFn entries row column = entries row column := by
  rw [matrixOfFn, vectorOfFn_apply, vectorOfFn_apply]

instance matrixOfFnCoe {K : Type*} {n : Nat} :
    Coe (Fin n → Fin n → K) (Matrix K n) where
  coe := matrixOfFn

/-- Pointwise equality proves structural equality of a finite vector. -/
theorem vector_ext {n : Nat} {left right : Vector K n}
    (equal : ∀ index, left index = right index) : left = right := by
  induction n with
  | zero =>
      cases left
      cases right
      rfl
  | succ n inductionHypothesis =>
      cases left with
      | cons leftHead leftTail =>
          cases right with
          | cons rightHead rightTail =>
              have headEqual : leftHead = rightHead := equal 0
              have tailEqual : leftTail = rightTail :=
                inductionHypothesis (fun index => equal index.succ)
              cases headEqual
              cases tailEqual
              rfl

/-- Entrywise equality proves structural equality of a finite matrix. -/
theorem matrix_ext {n : Nat} {left right : Matrix K n}
    (equal : ∀ row column, left row column = right row column) :
    left = right := by
  apply vector_ext
  intro row
  apply vector_ext
  exact equal row

theorem vector_eq_at {n : Nat} {left right : Vector K n}
    (equal : left = right) (index : Fin n) : left index = right index :=
  congrArg (fun vector : Vector K n => vector index) equal

theorem matrix_eq_at {n : Nat} {left right : Matrix K n}
    (equal : left = right) (row column : Fin n) :
    left row column = right row column :=
  congrArg (fun matrix : Matrix K n => matrix row column) equal

variable {K : Type*} [CommRing K]

def sumFin {n : Nat} (values : Fin n → K) : K :=
  (List.ofFn values).foldl (fun a b => a + b) 0

@[simp] theorem sumFin_zero {n : Nat} :
    sumFin (fun _ : Fin n => (0 : K)) = 0 := by
  unfold sumFin
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [QuotientFreeList.ofFn_succ, List.foldl_cons]
      rw [zero_add]
      exact inductionHypothesis

private theorem foldl_add_eq_accumulator_add
    (values : List K) (accumulator : K) :
    values.foldl (fun a b => a + b) accumulator =
      accumulator + values.foldl (fun a b => a + b) 0 := by
  induction values generalizing accumulator with
  | nil =>
      change accumulator = accumulator + 0
      ring1
  | cons value remaining inductionHypothesis =>
      rw [List.foldl_cons, inductionHypothesis]
      rw [List.foldl_cons, show (0 : K) + value = value by ring1]
      rw [inductionHypothesis value]
      ring1

theorem sumFin_succ (values : Fin (n + 1) → K) :
    sumFin values = values 0 + sumFin (fun i : Fin n => values i.succ) := by
  unfold sumFin
  rw [QuotientFreeList.ofFn_succ, List.foldl_cons]
  rw [foldl_add_eq_accumulator_add]
  ring1

theorem sumFin_congr {n : Nat} {left right : Fin n → K}
    (equal : ∀ index, left index = right index) :
    sumFin left = sumFin right := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      rw [sumFin_succ, sumFin_succ, equal 0,
        inductionHypothesis (fun index => equal index.succ)]

theorem sumFin_add {n : Nat} (left right : Fin n → K) :
    sumFin (fun i => left i + right i) = sumFin left + sumFin right := by
  induction n with
  | zero => simp [sumFin]
  | succ n inductionHypothesis =>
      rw [sumFin_succ, sumFin_succ, sumFin_succ,
        inductionHypothesis (fun i => left i.succ) (fun i => right i.succ)]
      ring1

theorem sumFin_mul_left {n : Nat} (a : K) (values : Fin n → K) :
    sumFin (fun i => a * values i) = a * sumFin values := by
  induction n with
  | zero =>
      change (0 : K) = a * 0
      exact (mul_zero a).symm
  | succ n inductionHypothesis =>
      rw [sumFin_succ, sumFin_succ,
        inductionHypothesis (fun i => values i.succ)]
      ring1

theorem sumFin_mul_right {n : Nat} (values : Fin n → K) (a : K) :
    sumFin (fun i => values i * a) = sumFin values * a := by
  calc
    sumFin (fun i => values i * a) =
        sumFin (fun i => a * values i) :=
      sumFin_congr (fun _ => _root_.mul_comm _ _)
    _ = a * sumFin values := sumFin_mul_left a values
    _ = sumFin values * a := _root_.mul_comm _ _

theorem sumFin_neg {n : Nat} (values : Fin n → K) :
    sumFin (fun i => -values i) = -sumFin values := by
  calc
    sumFin (fun i => -values i) =
        sumFin (fun i => (-1 : K) * values i) :=
      sumFin_congr (fun _ => by ring1)
    _ = (-1 : K) * sumFin values := sumFin_mul_left _ _
    _ = -sumFin values := by ring1

theorem sumFin_sub {n : Nat} (left right : Fin n → K) :
    sumFin (fun i => left i - right i) = sumFin left - sumFin right := by
  calc
    sumFin (fun i => left i - right i) =
        sumFin (fun i => left i + -right i) :=
      sumFin_congr (fun _ => sub_eq_add_neg _ _)
    _ = sumFin left + sumFin (fun i => -right i) := sumFin_add _ _
    _ = sumFin left + -sumFin right := by rw [sumFin_neg]
    _ = sumFin left - sumFin right := (sub_eq_add_neg _ _).symm

theorem sumFin_swap {m n : Nat}
    (values : Fin m → Fin n → K) :
    sumFin (fun i => sumFin (values i)) =
      sumFin (fun j => sumFin (fun i => values i j)) := by
  induction m with
  | zero =>
      change (0 : K) = sumFin (fun _ : Fin n => 0)
      exact sumFin_zero.symm
  | succ m inductionHypothesis =>
      rw [sumFin_succ, inductionHypothesis]
      rw [← sumFin_add]
      apply sumFin_congr
      intro j
      rw [sumFin_succ]

theorem sumFin_ite_eq {n : Nat} (target : Fin n) (values : Fin n → K) :
    sumFin (fun i => if i = target then values i else 0) = values target := by
  induction n with
  | zero => exact Fin.elim0 target
  | succ n inductionHypothesis =>
      refine Fin.cases ?_ (fun targetTail => ?_) target
      · rw [sumFin_succ, if_pos rfl]
        rw [sumFin_congr (right := fun _ => (0 : K)) (fun i => by
          rw [if_neg (Fin.succ_ne_zero i)])]
        rw [sumFin_zero]
        ring1
      · rw [sumFin_succ, if_neg (Ne.symm (Fin.succ_ne_zero targetTail))]
        rw [sumFin_congr
          (right := fun i : Fin n =>
            if i = targetTail then values i.succ else 0) (fun i => by
          by_cases equal : i = targetTail
          · subst i
            rw [if_pos rfl, if_pos rfl]
          · rw [if_neg equal, if_neg (fun successorEqual =>
              equal (Fin.ext (Nat.succ.inj
                (congrArg Fin.val successorEqual))))])]
        rw [show (0 : K) +
            sumFin (fun i : Fin n =>
              if i = targetTail then values i.succ else 0) =
            sumFin (fun i : Fin n =>
              if i = targetTail then values i.succ else 0) by ring1]
        exact inductionHypothesis targetTail (fun i => values i.succ)

def dot {n : Nat} (left right : Vector K n) : K :=
  sumFin (fun i => left i * right i)

def mul {n : Nat} (left right : Matrix K n) : Matrix K n :=
  matrixOfFn fun row column =>
    dot (left row) (vectorOfFn fun middle => right middle column)

def identity {n : Nat} : Matrix K n :=
  matrixOfFn fun row column => if row = column then 1 else 0

def scaleIdentity {n : Nat} (a : K) : Matrix K n :=
  matrixOfFn fun row column => if row = column then a else 0

/-- Matrix multiplication is the displayed finite dot product at each
entry. -/
theorem mul_apply {n : Nat} (left right : Matrix K n)
    (row column : Fin n) :
    mul left right row column =
      sumFin (fun middle => left row middle * right middle column) := by
  unfold mul dot
  rw [matrixOfFn_apply]
  exact sumFin_congr (fun middle => by rw [vectorOfFn_apply])

theorem mul_assoc {n : Nat} (first second third : Matrix K n) :
    mul (mul first second) third = mul first (mul second third) := by
  apply matrix_ext
  intro row column
  calc
    mul (mul first second) third row column =
        sumFin (fun middle =>
          mul first second row middle * third middle column) :=
      mul_apply _ _ row column
    _ = sumFin (fun middle =>
        sumFin (fun inner => first row inner * second inner middle) *
          third middle column) := by
      apply sumFin_congr
      intro middle
      rw [mul_apply]
    _ =
        sumFin (fun middle => sumFin (fun inner =>
          (first row inner * second inner middle) * third middle column)) := by
            apply sumFin_congr
            intro middle
            rw [sumFin_mul_right]
    _ = sumFin (fun inner => sumFin (fun middle =>
          (first row inner * second inner middle) * third middle column)) :=
      sumFin_swap _
    _ = sumFin (fun inner => first row inner *
        sumFin (fun middle => second inner middle * third middle column)) := by
          apply sumFin_congr
          intro inner
          rw [← sumFin_mul_left]
          apply sumFin_congr
          intro middle
          ring1
    _ = sumFin (fun inner =>
          first row inner * mul second third inner column) := by
      apply sumFin_congr
      intro inner
      rw [mul_apply]
    _ = mul first (mul second third) row column :=
      (mul_apply _ _ row column).symm

theorem mul_scaleIdentity {n : Nat} (matrix : Matrix K n) (a : K) :
    mul matrix (scaleIdentity a) =
      fun row column => matrix row column * a := by
  apply matrix_ext
  intro row column
  unfold mul
  rw [matrixOfFn_apply, matrixOfFn_apply]
  unfold dot
  rw [sumFin_congr
      (right := fun middle => matrix row middle *
        (if middle = column then a else 0)) (fun middle => by
    rw [vectorOfFn_apply]
    unfold scaleIdentity
    rw [matrixOfFn_apply])]
  rw [sumFin_congr
      (right := fun middle => if middle = column then
        matrix row middle * a else 0) (fun middle => by
    by_cases equal : middle = column
    · rw [if_pos equal, if_pos equal]
    · rw [if_neg equal, if_neg equal,
        mul_zero])]
  exact sumFin_ite_eq column (fun middle => matrix row middle * a)

theorem scaleIdentity_mul {n : Nat} (a : K) (matrix : Matrix K n) :
    mul (scaleIdentity a) matrix =
      fun row column => a * matrix row column := by
  apply matrix_ext
  intro row column
  unfold mul
  rw [matrixOfFn_apply, matrixOfFn_apply]
  unfold dot
  rw [sumFin_congr
      (right := fun middle =>
        (if row = middle then a else 0) * matrix middle column)
      (fun middle => by
    rw [vectorOfFn_apply]
    unfold scaleIdentity
    rw [matrixOfFn_apply])]
  rw [sumFin_congr
      (right := fun middle => if middle = row then
        a * matrix middle column else 0) (fun middle => by
    by_cases equal : middle = row
    · subst middle
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg equal, if_neg (Ne.symm equal)]
      rw [_root_.mul_comm, mul_zero])]
  exact sumFin_ite_eq row (fun middle => a * matrix middle column)

structure ScaledInverse {n : Nat} (matrix : Matrix K n) where
  scalar : K
  inverse : Matrix K n
  left_identity : mul inverse matrix = scaleIdentity scalar
  right_identity : mul matrix inverse = scaleIdentity scalar

def head (matrix : Matrix K (n + 1)) : K := matrix 0 0

def topRow (matrix : Matrix K (n + 1)) : Vector K n :=
  vectorOfFn fun column => matrix 0 column.succ

def leftColumn (matrix : Matrix K (n + 1)) : Vector K n :=
  vectorOfFn fun row => matrix row.succ 0

omit [CommRing K] in
@[simp] theorem topRow_apply (matrix : Matrix K (n + 1))
    (column : Fin n) :
    topRow matrix column = matrix 0 column.succ := by
  exact vectorOfFn_apply _ _

omit [CommRing K] in
@[simp] theorem leftColumn_apply (matrix : Matrix K (n + 1))
    (row : Fin n) :
    leftColumn matrix row = matrix row.succ 0 := by
  exact vectorOfFn_apply _ _

def tail (matrix : Matrix K (n + 1)) : Matrix K n :=
  matrixOfFn fun row column => matrix row.succ column.succ

omit [CommRing K] in
@[simp] theorem tail_apply (matrix : Matrix K (n + 1))
    (row column : Fin n) :
    tail matrix row column = matrix row.succ column.succ := by
  exact matrixOfFn_apply _ _ _

def schur (matrix : Matrix K (n + 1)) : Matrix K n :=
  matrixOfFn fun row column =>
    head matrix * tail matrix row column -
      leftColumn matrix row * topRow matrix column

/-- The Schur matrix evaluated at one displayed entry. -/
theorem schur_apply {n : Nat} (matrix : Matrix K (n + 1))
    (row column : Fin n) :
    schur matrix row column =
      head matrix * tail matrix row column -
        leftColumn matrix row * topRow matrix column := by
  unfold schur
  rw [matrixOfFn_apply]

def matrixVector {n : Nat} (matrix : Matrix K n) (vector : Vector K n) : Vector K n :=
  vectorOfFn fun row => dot (matrix row) vector

def vectorMatrix {n : Nat} (vector : Vector K n) (matrix : Matrix K n) : Vector K n :=
  vectorOfFn fun column =>
    dot vector (vectorOfFn fun row => matrix row column)

/-- Matrix-vector multiplication evaluated at one displayed row. -/
theorem matrixVector_apply {n : Nat} (matrix : Matrix K n)
    (vector : Vector K n) (row : Fin n) :
    matrixVector matrix vector row =
      sumFin (fun column => matrix row column * vector column) := by
  unfold matrixVector
  rw [vectorOfFn_apply]
  rfl

/-- Vector-matrix multiplication evaluated at one displayed column. -/
theorem vectorMatrix_apply {n : Nat} (vector : Vector K n)
    (matrix : Matrix K n) (column : Fin n) :
    vectorMatrix vector matrix column =
      sumFin (fun row => vector row * matrix row column) := by
  unfold vectorMatrix
  rw [vectorOfFn_apply]
  unfold dot
  exact sumFin_congr (fun row => by rw [vectorOfFn_apply])

/-- A scaled identity matrix evaluated at one displayed entry. -/
theorem scaleIdentity_apply {n : Nat} (a : K) (row column : Fin n) :
    scaleIdentity a row column = if row = column then a else 0 := by
  unfold scaleIdentity
  rw [matrixOfFn_apply]

/-- A displayed row-vector product is the corresponding matrix-product
entry. -/
theorem vectorMatrix_row_eq_mul_apply {n : Nat}
    (left right : Matrix K n) (row column : Fin n) :
    vectorMatrix (vectorOfFn fun i => left row i) right column =
      mul left right row column := by
  unfold vectorMatrix
  rw [vectorOfFn_apply]
  unfold dot
  rw [mul_apply]
  exact sumFin_congr (fun i => by
    rw [vectorOfFn_apply, vectorOfFn_apply])

/-- A displayed matrix row multiplied by a matrix, expanded as a bounded
entry sum. -/
theorem vectorMatrix_row_apply {n : Nat}
    (left right : Matrix K n) (row column : Fin n) :
    vectorMatrix (vectorOfFn fun i => left row i) right column =
      sumFin (fun i => left row i * right i column) := by
  calc
    vectorMatrix (vectorOfFn fun i => left row i) right column =
        sumFin (fun i => vectorOfFn (fun j => left row j) i *
          right i column) := vectorMatrix_apply _ _ _
    _ = sumFin (fun i => left row i * right i column) :=
      sumFin_congr (fun i => by rw [vectorOfFn_apply])

/-- Dotting a displayed matrix row with a vector, expanded as a bounded
entry sum. -/
theorem dot_row_apply {n : Nat} (matrix : Matrix K n)
    (row : Fin n) (vector : Vector K n) :
    dot (vectorOfFn fun i => matrix row i) vector =
      sumFin (fun i => matrix row i * vector i) := by
  unfold dot
  exact sumFin_congr (fun i => by rw [vectorOfFn_apply])

/-- Dotting a vector with a displayed matrix column, expanded as a bounded
entry sum. -/
theorem dot_column_apply {n : Nat} (vector : Vector K n)
    (matrix : Matrix K n) (column : Fin n) :
    dot vector (vectorOfFn fun i => matrix i column) =
      sumFin (fun i => vector i * matrix i column) := by
  unfold dot
  exact sumFin_congr (fun i => by rw [vectorOfFn_apply])

/-- A displayed matrix-column product is the corresponding matrix-product
entry. -/
theorem matrixVector_column_eq_mul_apply {n : Nat}
    (left right : Matrix K n) (row column : Fin n) :
    matrixVector left (vectorOfFn fun i => right i column) row =
      mul left right row column := by
  unfold matrixVector
  rw [vectorOfFn_apply]
  unfold dot
  rw [mul_apply]
  exact sumFin_congr (fun i => by rw [vectorOfFn_apply])

/-- Multiplication by a displayed matrix column, expanded as a bounded entry
sum. -/
theorem matrixVector_column_apply {n : Nat}
    (left right : Matrix K n) (row column : Fin n) :
    matrixVector left (vectorOfFn fun i => right i column) row =
      sumFin (fun i => left row i * right i column) := by
  calc
    matrixVector left (vectorOfFn fun i => right i column) row =
        sumFin (fun i => left row i *
          vectorOfFn (fun j => right j column) i) :=
      matrixVector_apply _ _ _
    _ = sumFin (fun i => left row i * right i column) :=
      sumFin_congr (fun i => by rw [vectorOfFn_apply])

theorem matrixVector_mul {n : Nat} (left right : Matrix K n)
    (vector : Vector K n) :
    matrixVector (mul left right) vector =
      matrixVector left (matrixVector right vector) := by
  apply vector_ext
  intro row
  rw [matrixVector_apply]
  rw [sumFin_congr
    (right := fun middle =>
      sumFin (fun inner => left row inner * right inner middle) *
        vector middle)
    (fun middle => by rw [mul_apply])]
  rw [matrixVector_apply]
  have rightExpansion :
      sumFin (fun inner => left row inner *
          matrixVector right vector inner) =
        sumFin (fun inner => left row inner *
          sumFin (fun middle => right inner middle * vector middle)) :=
    sumFin_congr (fun inner =>
      congrArg (fun entry => left row inner * entry)
        (matrixVector_apply right vector inner))
  rw [rightExpansion]
  calc
    sumFin (fun middle =>
        sumFin (fun inner => left row inner * right inner middle) *
          vector middle) =
        sumFin (fun middle => sumFin (fun inner =>
          (left row inner * right inner middle) * vector middle)) := by
            apply sumFin_congr
            intro middle
            rw [sumFin_mul_right]
    _ = sumFin (fun inner => sumFin (fun middle =>
          (left row inner * right inner middle) * vector middle)) :=
      sumFin_swap _
    _ = sumFin (fun inner => left row inner *
        sumFin (fun middle => right inner middle * vector middle)) := by
          apply sumFin_congr
          intro inner
          rw [← sumFin_mul_left]
          apply sumFin_congr
          intro middle
          ring1

theorem vectorMatrix_mul {n : Nat} (vector : Vector K n)
    (left right : Matrix K n) :
    vectorMatrix vector (mul left right) =
      vectorMatrix (vectorMatrix vector left) right := by
  apply vector_ext
  intro column
  rw [vectorMatrix_apply]
  rw [sumFin_congr
    (right := fun outer => vector outer *
      sumFin (fun inner => left outer inner * right inner column))
    (fun outer => by rw [mul_apply])]
  rw [vectorMatrix_apply]
  have rightExpansion :
      sumFin (fun inner => vectorMatrix vector left inner *
          right inner column) =
        sumFin (fun inner =>
          sumFin (fun outer => vector outer * left outer inner) *
            right inner column) :=
    sumFin_congr (fun inner =>
      congrArg (fun entry => entry * right inner column)
        (vectorMatrix_apply vector left inner))
  rw [rightExpansion]
  calc
    sumFin (fun outer => vector outer *
        sumFin (fun inner => left outer inner * right inner column)) =
      sumFin (fun outer => sumFin (fun inner =>
        vector outer * (left outer inner * right inner column))) := by
          apply sumFin_congr
          intro outer
          rw [← sumFin_mul_left]
    _ = sumFin (fun inner => sumFin (fun outer =>
          vector outer * (left outer inner * right inner column))) :=
      sumFin_swap _
    _ = sumFin (fun inner =>
        sumFin (fun outer => vector outer * left outer inner) *
          right inner column) := by
            apply sumFin_congr
            intro inner
            rw [sumFin_congr
              (right := fun outer => (vector outer * left outer inner) *
                right inner column) (fun _ => by ring1)]
            rw [sumFin_mul_right]

theorem dot_vectorMatrix_matrixVector {n : Nat} (left : Vector K n)
    (matrix : Matrix K n) (right : Vector K n) :
    dot (vectorMatrix left matrix) right =
      dot left (matrixVector matrix right) := by
  unfold dot
  calc
    sumFin (fun column => vectorMatrix left matrix column * right column) =
        sumFin (fun column =>
          sumFin (fun row => left row * matrix row column) * right column) := by
      apply sumFin_congr
      intro column
      unfold vectorMatrix
      rw [vectorOfFn_apply]
      unfold dot
      rw [sumFin_congr (right := fun row =>
        left row * matrix row column) (fun row => by
          rw [vectorOfFn_apply])]
    _ =
        sumFin (fun column => sumFin (fun row =>
          (left row * matrix row column) * right column)) := by
      apply sumFin_congr
      intro column
      rw [sumFin_mul_right]
    _ = sumFin (fun row => sumFin (fun column =>
          (left row * matrix row column) * right column)) :=
      sumFin_swap _
    _ = sumFin (fun row => left row *
        sumFin (fun column => matrix row column * right column)) := by
          apply sumFin_congr
          intro row
          rw [← sumFin_mul_left]
          apply sumFin_congr
          intro column
          ring1
    _ = sumFin (fun row => left row * matrixVector matrix right row) := by
      apply sumFin_congr
      intro row
      unfold matrixVector
      rw [vectorOfFn_apply]
      rfl

theorem matrixVector_scaleIdentity {n : Nat} (a : K)
    (vector : Vector K n) :
    matrixVector (scaleIdentity a) vector = fun row => a * vector row := by
  apply vector_ext
  intro row
  unfold matrixVector
  rw [vectorOfFn_apply, vectorOfFn_apply]
  unfold dot
  rw [sumFin_congr
      (right := fun middle => if middle = row then
        a * vector middle else 0) (fun middle => by
    unfold scaleIdentity
    rw [matrixOfFn_apply]
    by_cases equal : middle = row
    · subst middle
      rw [if_pos rfl, if_pos rfl]
    · rw [if_neg equal, if_neg (Ne.symm equal)]
      rw [_root_.mul_comm,
        mul_zero])]
  exact sumFin_ite_eq row (fun middle => a * vector middle)

theorem vectorMatrix_scaleIdentity {n : Nat} (vector : Vector K n)
    (a : K) :
    vectorMatrix vector (scaleIdentity a) = fun column => vector column * a := by
  apply vector_ext
  intro column
  unfold vectorMatrix
  rw [vectorOfFn_apply]
  unfold dot
  rw [sumFin_congr
      (right := fun row => if row = column then vector row * a else 0)
      (fun row => by
    rw [vectorOfFn_apply]
    unfold scaleIdentity
    rw [matrixOfFn_apply]
    by_cases equal : row = column
    · rw [if_pos equal, if_pos equal]
    · rw [if_neg equal, if_neg equal,
        mul_zero])]
  rw [vectorOfFn_apply]
  exact sumFin_ite_eq column (fun row => vector row * a)

theorem matrixVector_schur {n : Nat} (matrix : Matrix K (n + 1))
    (vector : Vector K n) (row : Fin n) :
    matrixVector (schur matrix) vector row =
      head matrix * matrixVector (tail matrix) vector row -
        leftColumn matrix row * dot (topRow matrix) vector := by
  calc
    matrixVector (schur matrix) vector row =
        sumFin (fun i => schur matrix row i * vector i) :=
      matrixVector_apply (schur matrix) vector row
    _ = sumFin (fun i =>
        (head matrix * tail matrix row i -
          leftColumn matrix row * topRow matrix i) * vector i) :=
      sumFin_congr (fun i =>
        congrArg (fun entry => entry * vector i)
          (schur_apply matrix row i))
    _ = sumFin (fun i => head matrix * tail matrix row i * vector i -
        leftColumn matrix row * topRow matrix i * vector i) :=
      sumFin_congr (fun _ => by ring1)
    _ = sumFin (fun i => head matrix * tail matrix row i * vector i) -
        sumFin (fun i =>
          leftColumn matrix row * topRow matrix i * vector i) :=
      sumFin_sub _ _
    _ = sumFin (fun i => head matrix *
          (tail matrix row i * vector i)) -
        sumFin (fun i => leftColumn matrix row *
          (topRow matrix i * vector i)) :=
      congrArg₂ (fun left right => left - right)
        (sumFin_congr (fun _ => by ring1))
        (sumFin_congr (fun _ => by ring1))
    _ = head matrix * sumFin (fun i => tail matrix row i * vector i) -
        leftColumn matrix row *
          sumFin (fun i => topRow matrix i * vector i) := by
      rw [sumFin_mul_left, sumFin_mul_left]
    _ = head matrix * matrixVector (tail matrix) vector row -
        leftColumn matrix row * dot (topRow matrix) vector := by
      rw [matrixVector_apply]
      unfold dot
      rfl

theorem vectorMatrix_schur {n : Nat} (vector : Vector K n)
    (matrix : Matrix K (n + 1)) (column : Fin n) :
    vectorMatrix vector (schur matrix) column =
      head matrix * vectorMatrix vector (tail matrix) column -
        dot vector (leftColumn matrix) * topRow matrix column := by
  unfold vectorMatrix
  rw [vectorOfFn_apply, vectorOfFn_apply]
  unfold dot
  have tailColumn :
      sumFin (fun i => vector i *
          vectorOfFn (fun row => tail matrix row column) i) =
        sumFin (fun i => vector i * tail matrix i column) :=
    sumFin_congr (fun i => by rw [vectorOfFn_apply])
  rw [tailColumn]
  rw [sumFin_congr
    (right := fun i => vector i *
      (head matrix * tail matrix i column -
        leftColumn matrix i * topRow matrix column))
    (fun i => by
      rw [vectorOfFn_apply]
      unfold schur
      rw [matrixOfFn_apply])]
  calc
    sumFin (fun i => vector i *
        (head matrix * tail matrix i column -
          leftColumn matrix i * topRow matrix column)) =
      sumFin (fun i => vector i * (head matrix * tail matrix i column) -
        vector i * (leftColumn matrix i * topRow matrix column)) :=
      sumFin_congr (fun _ => by ring1)
    _ = sumFin (fun i => vector i *
          (head matrix * tail matrix i column)) -
        sumFin (fun i => vector i *
          (leftColumn matrix i * topRow matrix column)) :=
      sumFin_sub _ _
    _ = sumFin (fun i => head matrix *
          (vector i * tail matrix i column)) -
        sumFin (fun i => (vector i * leftColumn matrix i) *
          topRow matrix column) :=
      congrArg₂ (fun left right => left - right)
        (sumFin_congr (fun _ => by ring1))
        (sumFin_congr (fun _ => by ring1))
    _ = head matrix *
          sumFin (fun i => vector i * tail matrix i column) -
        sumFin (fun i => vector i * leftColumn matrix i) *
          topRow matrix column := by
      rw [sumFin_mul_left, sumFin_mul_right]

def blockInverse {n : Nat} (matrix : Matrix K (n + 1))
    (smaller : ScaledInverse (schur matrix)) : Matrix K (n + 1) :=
  let a := head matrix
  let row := topRow matrix
  let column := leftColumn matrix
  let inverse := smaller.inverse
  let inverseColumn := matrixVector inverse column
  let rowInverse := vectorMatrix row inverse
  let corner := smaller.scalar + dot row inverseColumn
  matrixOfFn fun i j => i.cases
    (j.cases corner (fun columnIndex => -a * rowInverse columnIndex))
    (fun rowIndex => j.cases
      (-a * inverseColumn rowIndex)
      (fun columnIndex => a ^ 2 * inverse rowIndex columnIndex))

/-- The division-free block inverse evaluated at one displayed entry. -/
theorem blockInverse_apply {n : Nat} (matrix : Matrix K (n + 1))
    (smaller : ScaledInverse (schur matrix)) (row column : Fin (n + 1)) :
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
            head matrix ^ 2 * smaller.inverse rowIndex columnIndex)) := by
  unfold blockInverse
  rw [matrixOfFn_apply]

theorem mul_blockInverse {n : Nat} (matrix : Matrix K (n + 1))
    (smaller : ScaledInverse (schur matrix)) :
    mul matrix (blockInverse matrix smaller) =
      scaleIdentity (head matrix * smaller.scalar) := by
  let a := head matrix
  let row := topRow matrix
  let column := leftColumn matrix
  let remaining := tail matrix
  let inverse := smaller.inverse
  let inverseColumn := matrixVector inverse column
  let rowInverse := vectorMatrix row inverse
  let corner := smaller.scalar + dot row inverseColumn
  have schurInverseColumn :
      matrixVector (schur matrix) inverseColumn =
        fun i => smaller.scalar * column i := by
    dsimp only [inverseColumn, inverse, column]
    rw [← matrixVector_mul, smaller.right_identity,
      matrixVector_scaleIdentity]
  apply matrix_ext
  intro matrixRow matrixColumn
  refine Fin.cases ?_ (fun rowIndex => ?_) matrixRow
  · refine Fin.cases ?_ (fun columnIndex => ?_) matrixColumn
    · rw [mul_apply, scaleIdentity_apply, sumFin_succ,
        blockInverse_apply matrix smaller 0 0, if_pos rfl]
      rw [sumFin_congr
        (right := fun i => row i * (-a * inverseColumn i))
        (fun i => by
          rw [blockInverse_apply]
          simp only [Fin.cases_zero, Fin.cases_succ]
          rw [show matrix 0 i.succ = row i by
            unfold row topRow
            rw [vectorOfFn_apply]])]
      change a * corner +
          sumFin (fun i => row i * (-a * inverseColumn i)) =
        a * smaller.scalar
      have summed : sumFin (fun i => row i * (-a * inverseColumn i)) =
          -a * dot row inverseColumn := by
        rw [sumFin_congr
          (right := fun i => -a * (row i * inverseColumn i))
          (fun _ => by ring1)]
        exact sumFin_mul_left (-a) (fun i => row i * inverseColumn i)
      rw [summed]
      dsimp only [corner]
      ring1
    · rw [mul_apply, scaleIdentity_apply, sumFin_succ,
        blockInverse_apply matrix smaller 0 columnIndex.succ,
        if_neg (Ne.symm (Fin.succ_ne_zero columnIndex))]
      rw [sumFin_congr
        (right := fun i => row i * (a ^ 2 * inverse i columnIndex))
        (fun i => by
          rw [blockInverse_apply]
          simp only [Fin.cases_succ]
          rw [show matrix 0 i.succ = row i by
            unfold row topRow
            rw [vectorOfFn_apply]])]
      change a * (-a * rowInverse columnIndex) +
          sumFin (fun i => row i *
            (a ^ 2 * inverse i columnIndex)) = 0
      rw [sumFin_congr
        (right := fun i => a ^ 2 * (row i * inverse i columnIndex))
        (fun _ => by ring1)]
      rw [sumFin_mul_left]
      have rowInverseAt : rowInverse columnIndex =
          sumFin (fun i => row i * inverse i columnIndex) :=
        vectorMatrix_apply row inverse columnIndex
      rw [rowInverseAt]
      ring1
  · refine Fin.cases ?_ (fun columnIndex => ?_) matrixColumn
    · rw [mul_apply, scaleIdentity_apply, sumFin_succ,
        blockInverse_apply matrix smaller 0 0,
        if_neg (Fin.succ_ne_zero rowIndex)]
      rw [show matrix rowIndex.succ 0 = column rowIndex by
        unfold column leftColumn
        rw [vectorOfFn_apply]]
      rw [sumFin_congr
        (right := fun i => remaining rowIndex i *
          (-a * inverseColumn i))
        (fun i => by
          rw [blockInverse_apply]
          simp only [Fin.cases_zero, Fin.cases_succ]
          rw [show matrix rowIndex.succ i.succ =
              remaining rowIndex i by
            unfold remaining tail
            rw [matrixOfFn_apply]])]
      change column rowIndex * corner +
          sumFin (fun i => remaining rowIndex i *
            (-a * inverseColumn i)) = 0
      have summed : sumFin (fun i => remaining rowIndex i *
            (-a * inverseColumn i)) =
          -a * matrixVector remaining inverseColumn rowIndex := by
        rw [sumFin_congr
          (right := fun i => -a *
            (remaining rowIndex i * inverseColumn i))
          (fun _ => by ring1)]
        rw [matrixVector_apply]
        exact sumFin_mul_left (-a)
          (fun i => remaining rowIndex i * inverseColumn i)
      rw [summed]
      have schurAt := vector_eq_at schurInverseColumn rowIndex
      rw [matrixVector_schur] at schurAt
      simp only [vectorOfFn_apply] at schurAt
      have rearranged :
          a * matrixVector remaining inverseColumn rowIndex =
            smaller.scalar * column rowIndex +
              column rowIndex * dot row inverseColumn := by
        calc
          a * matrixVector remaining inverseColumn rowIndex =
              (a * matrixVector remaining inverseColumn rowIndex -
                column rowIndex * dot row inverseColumn) +
                column rowIndex * dot row inverseColumn := by ring1
          _ = smaller.scalar * column rowIndex +
                column rowIndex * dot row inverseColumn := by rw [schurAt]
      rw [show -a * matrixVector remaining inverseColumn rowIndex =
          -(a * matrixVector remaining inverseColumn rowIndex) by ring1,
        rearranged]
      dsimp only [corner]
      ring1
    · rw [mul_apply, scaleIdentity_apply, sumFin_succ,
        blockInverse_apply matrix smaller 0 columnIndex.succ]
      rw [show matrix rowIndex.succ 0 = column rowIndex by
        unfold column leftColumn
        rw [vectorOfFn_apply]]
      rw [sumFin_congr
        (right := fun i => remaining rowIndex i *
          (a ^ 2 * inverse i columnIndex))
        (fun i => by
          rw [blockInverse_apply]
          simp only [Fin.cases_succ]
          rw [show matrix rowIndex.succ i.succ =
              remaining rowIndex i by
            unfold remaining tail
            rw [matrixOfFn_apply]])]
      change column rowIndex * (-a * rowInverse columnIndex) +
          sumFin (fun i => remaining rowIndex i *
            (a ^ 2 * inverse i columnIndex)) =
          (if rowIndex.succ = columnIndex.succ then
          a * smaller.scalar else 0)
      rw [sumFin_congr
        (right := fun i => a ^ 2 *
          (remaining rowIndex i * inverse i columnIndex))
        (fun _ => by ring1)]
      rw [sumFin_mul_left]
      have schurEntry := matrix_eq_at smaller.right_identity
        rowIndex columnIndex
      have schurEntryAt : matrixVector (schur matrix)
          (fun i => inverse i columnIndex) rowIndex =
          (if rowIndex = columnIndex then smaller.scalar else 0) := by
        calc
          matrixVector (schur matrix)
                (vectorOfFn fun i => inverse i columnIndex) rowIndex =
              mul (schur matrix) inverse rowIndex columnIndex :=
            matrixVector_column_eq_mul_apply (schur matrix) inverse
              rowIndex columnIndex
          _ = scaleIdentity smaller.scalar rowIndex columnIndex :=
            schurEntry
          _ = (if rowIndex = columnIndex then smaller.scalar else 0) :=
            scaleIdentity_apply smaller.scalar rowIndex columnIndex
      rw [matrixVector_schur] at schurEntryAt
      have schurEntryAlias :
          a * sumFin (fun i => remaining rowIndex i * inverse i columnIndex) -
              column rowIndex *
                sumFin (fun i => row i * inverse i columnIndex) =
            (if rowIndex = columnIndex then smaller.scalar else 0) := by
        rw [matrixVector_column_apply remaining inverse rowIndex columnIndex,
          dot_column_apply row inverse columnIndex] at schurEntryAt
        change a * sumFin (fun i => remaining rowIndex i *
              inverse i columnIndex) -
            column rowIndex *
              sumFin (fun i => row i * inverse i columnIndex) =
          (if rowIndex = columnIndex then smaller.scalar else 0) at schurEntryAt
        exact schurEntryAt
      have rowInverseAt : rowInverse columnIndex =
          sumFin (fun i => row i * inverse i columnIndex) :=
        vectorMatrix_apply row inverse columnIndex
      rw [rowInverseAt]
      by_cases equal : rowIndex = columnIndex
      · have successorEqual : rowIndex.succ = columnIndex.succ :=
          congrArg Fin.succ equal
        rw [if_pos equal] at schurEntryAlias
        rw [if_pos successorEqual]
        calc
          column rowIndex *
                (-a * sumFin (fun i => row i * inverse i columnIndex)) +
              a ^ 2 *
                sumFin (fun i => remaining rowIndex i * inverse i columnIndex) =
              a * (a *
                sumFin (fun i => remaining rowIndex i * inverse i columnIndex) -
                column rowIndex *
                  sumFin (fun i => row i * inverse i columnIndex)) := by ring1
          _ = a * smaller.scalar := by rw [schurEntryAlias]
      · have successorNe : rowIndex.succ ≠ columnIndex.succ := by
          intro successorEqual
          exact equal (Fin.ext (Nat.succ.inj
            (congrArg Fin.val successorEqual)))
        rw [if_neg equal] at schurEntryAlias
        rw [if_neg successorNe]
        calc
          column rowIndex *
                (-a * sumFin (fun i => row i * inverse i columnIndex)) +
              a ^ 2 *
                sumFin (fun i => remaining rowIndex i * inverse i columnIndex) =
              a * (a *
                sumFin (fun i => remaining rowIndex i * inverse i columnIndex) -
                column rowIndex *
                  sumFin (fun i => row i * inverse i columnIndex)) := by ring1
          _ = a * 0 := by rw [schurEntryAlias]
          _ = 0 := mul_zero a

theorem blockInverse_mul {n : Nat} (matrix : Matrix K (n + 1))
    (smaller : ScaledInverse (schur matrix)) :
    mul (blockInverse matrix smaller) matrix =
      scaleIdentity (head matrix * smaller.scalar) := by
  let a := head matrix
  let row := topRow matrix
  let column := leftColumn matrix
  let remaining := tail matrix
  let inverse := smaller.inverse
  let inverseColumn := matrixVector inverse column
  let rowInverse := vectorMatrix row inverse
  let corner := smaller.scalar + dot row inverseColumn
  have rowInverseSchur :
      vectorMatrix rowInverse (schur matrix) =
        fun j => row j * smaller.scalar := by
    dsimp only [rowInverse, inverse, row]
    rw [← vectorMatrix_mul, smaller.left_identity,
      vectorMatrix_scaleIdentity]
  have cornerDot : dot rowInverse column = dot row inverseColumn := by
    exact dot_vectorMatrix_matrixVector row inverse column
  apply matrix_ext
  intro matrixRow matrixColumn
  refine Fin.cases ?_ (fun rowIndex => ?_) matrixRow
  · refine Fin.cases ?_ (fun columnIndex => ?_) matrixColumn
    · rw [mul_apply, scaleIdentity_apply, sumFin_succ,
        blockInverse_apply matrix smaller 0 0, if_pos rfl]
      rw [sumFin_congr
        (right := fun i => (-a * rowInverse i) * column i)
        (fun i => by
          rw [blockInverse_apply]
          simp only [Fin.cases_zero, Fin.cases_succ]
          rw [show matrix i.succ 0 = column i by
            unfold column leftColumn
            rw [vectorOfFn_apply]])]
      change corner * a +
          sumFin (fun i => (-a * rowInverse i) * column i) =
        a * smaller.scalar
      have summed : sumFin (fun i => (-a * rowInverse i) * column i) =
          -a * dot rowInverse column := by
        rw [sumFin_congr
          (right := fun i => -a * (rowInverse i * column i))
          (fun _ => by ring1)]
        exact sumFin_mul_left (-a) (fun i => rowInverse i * column i)
      rw [summed, cornerDot]
      dsimp only [corner]
      ring1
    · rw [mul_apply, scaleIdentity_apply, sumFin_succ,
        blockInverse_apply matrix smaller 0 0,
        if_neg (Ne.symm (Fin.succ_ne_zero columnIndex))]
      rw [show matrix 0 columnIndex.succ = row columnIndex by
        unfold row topRow
        rw [vectorOfFn_apply]]
      rw [sumFin_congr
        (right := fun i => (-a * rowInverse i) *
          remaining i columnIndex)
        (fun i => by
          rw [blockInverse_apply]
          simp only [Fin.cases_zero, Fin.cases_succ]
          rw [show matrix i.succ columnIndex.succ =
              remaining i columnIndex by
            unfold remaining tail
            rw [matrixOfFn_apply]])]
      change corner * row columnIndex +
          sumFin (fun i => (-a * rowInverse i) *
            remaining i columnIndex) = 0
      have summed : sumFin (fun i => (-a * rowInverse i) *
            remaining i columnIndex) =
          -a * vectorMatrix rowInverse remaining columnIndex := by
        rw [sumFin_congr
          (right := fun i => -a *
            (rowInverse i * remaining i columnIndex))
          (fun _ => by ring1)]
        rw [vectorMatrix_apply]
        exact sumFin_mul_left (-a)
          (fun i => rowInverse i * remaining i columnIndex)
      rw [summed]
      have schurAt := vector_eq_at rowInverseSchur columnIndex
      rw [vectorMatrix_schur] at schurAt
      simp only [vectorOfFn_apply] at schurAt
      have schurAtAlias :
          a * vectorMatrix rowInverse remaining columnIndex -
              dot rowInverse column * row columnIndex =
            row columnIndex * smaller.scalar := by
        simpa only [a, remaining, column, row] using schurAt
      have rearranged :
          a * vectorMatrix rowInverse remaining columnIndex =
            row columnIndex * smaller.scalar +
              dot rowInverse column * row columnIndex := by
        calc
          a * vectorMatrix rowInverse remaining columnIndex =
              (a * vectorMatrix rowInverse remaining columnIndex -
                dot rowInverse column * row columnIndex) +
                dot rowInverse column * row columnIndex := by ring1
          _ = row columnIndex * smaller.scalar +
                dot rowInverse column * row columnIndex := by
              rw [schurAtAlias]
      rw [show -a * vectorMatrix rowInverse remaining columnIndex =
          -(a * vectorMatrix rowInverse remaining columnIndex) by ring1,
        rearranged]
      dsimp only [corner]
      rw [← cornerDot]
      ring1
  · refine Fin.cases ?_ (fun columnIndex => ?_) matrixColumn
    · rw [mul_apply, scaleIdentity_apply, sumFin_succ,
        blockInverse_apply matrix smaller rowIndex.succ 0,
        if_neg (Fin.succ_ne_zero rowIndex)]
      rw [sumFin_congr
        (right := fun i => (a ^ 2 * inverse rowIndex i) * column i)
        (fun i => by
          rw [blockInverse_apply]
          simp only [Fin.cases_succ]
          rw [show matrix i.succ 0 = column i by
            unfold column leftColumn
            rw [vectorOfFn_apply]])]
      change (-a * inverseColumn rowIndex) * a +
          sumFin (fun i => (a ^ 2 * inverse rowIndex i) * column i) = 0
      rw [sumFin_congr
        (right := fun i => a ^ 2 * (inverse rowIndex i * column i))
        (fun _ => by ring1)]
      rw [sumFin_mul_left]
      have inverseColumnAt : inverseColumn rowIndex =
          sumFin (fun i => inverse rowIndex i * column i) :=
        matrixVector_apply inverse column rowIndex
      rw [inverseColumnAt]
      ring1
    · rw [mul_apply, scaleIdentity_apply, sumFin_succ,
        blockInverse_apply matrix smaller rowIndex.succ 0]
      rw [show matrix 0 columnIndex.succ = row columnIndex by
        unfold row topRow
        rw [vectorOfFn_apply]]
      rw [sumFin_congr
        (right := fun i => (a ^ 2 * inverse rowIndex i) *
          remaining i columnIndex)
        (fun i => by
          rw [blockInverse_apply]
          simp only [Fin.cases_succ]
          rw [show matrix i.succ columnIndex.succ =
              remaining i columnIndex by
            unfold remaining tail
            rw [matrixOfFn_apply]])]
      change (-a * inverseColumn rowIndex) * row columnIndex +
          sumFin (fun i => (a ^ 2 * inverse rowIndex i) *
            remaining i columnIndex) =
          (if rowIndex.succ = columnIndex.succ then
          a * smaller.scalar else 0)
      rw [sumFin_congr
        (right := fun i => a ^ 2 *
          (inverse rowIndex i * remaining i columnIndex))
        (fun _ => by ring1)]
      rw [sumFin_mul_left]
      have schurEntry := matrix_eq_at smaller.left_identity
        rowIndex columnIndex
      have schurEntryAt : vectorMatrix (fun i => inverse rowIndex i)
          (schur matrix) columnIndex =
          (if rowIndex = columnIndex then smaller.scalar else 0) := by
        calc
          vectorMatrix (vectorOfFn fun i => inverse rowIndex i)
                (schur matrix) columnIndex =
              mul inverse (schur matrix) rowIndex columnIndex :=
            vectorMatrix_row_eq_mul_apply inverse (schur matrix)
              rowIndex columnIndex
          _ = scaleIdentity smaller.scalar rowIndex columnIndex :=
            schurEntry
          _ = (if rowIndex = columnIndex then smaller.scalar else 0) :=
            scaleIdentity_apply smaller.scalar rowIndex columnIndex
      rw [vectorMatrix_schur] at schurEntryAt
      have schurEntryAlias :
          a * sumFin (fun i => inverse rowIndex i *
                remaining i columnIndex) -
              sumFin (fun i => inverse rowIndex i * column i) *
                row columnIndex =
            (if rowIndex = columnIndex then smaller.scalar else 0) := by
        rw [vectorMatrix_row_apply inverse remaining rowIndex columnIndex,
          dot_row_apply inverse rowIndex column] at schurEntryAt
        change a * sumFin (fun i => inverse rowIndex i *
              remaining i columnIndex) -
            sumFin (fun i => inverse rowIndex i * column i) *
              row columnIndex =
          (if rowIndex = columnIndex then smaller.scalar else 0) at schurEntryAt
        exact schurEntryAt
      have inverseColumnAt : inverseColumn rowIndex =
          sumFin (fun i => inverse rowIndex i * column i) :=
        matrixVector_apply inverse column rowIndex
      rw [inverseColumnAt]
      by_cases equal : rowIndex = columnIndex
      · have successorEqual : rowIndex.succ = columnIndex.succ :=
          congrArg Fin.succ equal
        rw [if_pos equal] at schurEntryAlias
        rw [if_pos successorEqual]
        calc
          (-a * sumFin (fun i => inverse rowIndex i * column i)) *
                row columnIndex +
              a ^ 2 * sumFin (fun i => inverse rowIndex i *
                remaining i columnIndex) =
              a * (a * sumFin (fun i => inverse rowIndex i *
                remaining i columnIndex) -
                sumFin (fun i => inverse rowIndex i * column i) *
                  row columnIndex) := by ring1
          _ = a * smaller.scalar := by rw [schurEntryAlias]
      · have successorNe : rowIndex.succ ≠ columnIndex.succ := by
          intro successorEqual
          exact equal (Fin.ext (Nat.succ.inj
            (congrArg Fin.val successorEqual)))
        rw [if_neg equal] at schurEntryAlias
        rw [if_neg successorNe]
        calc
          (-a * sumFin (fun i => inverse rowIndex i * column i)) *
                row columnIndex +
              a ^ 2 * sumFin (fun i => inverse rowIndex i *
                remaining i columnIndex) =
              a * (a * sumFin (fun i => inverse rowIndex i *
                remaining i columnIndex) -
                sumFin (fun i => inverse rowIndex i * column i) *
                  row columnIndex) := by ring1
          _ = a * 0 := by rw [schurEntryAlias]
          _ = 0 := mul_zero a

/-- Division-free block extension of a two-sided scaled inverse. -/
def extendScaledInverse {n : Nat} (matrix : Matrix K (n + 1))
    (smaller : ScaledInverse (schur matrix)) : ScaledInverse matrix where
  scalar := head matrix * smaller.scalar
  inverse := blockInverse matrix smaller
  left_identity := blockInverse_mul matrix smaller
  right_identity := mul_blockInverse matrix smaller

/-- Every finite square matrix has a canonically computed fraction-free
scaled inverse.  The construction makes no invertibility decision: its
displayed scalar may be zero.  A later use as an actual inverse must supply a
separate constructive nonzero witness for that one finite scalar. -/
def scaledInverse : {n : Nat} -> (matrix : Matrix K n) -> ScaledInverse matrix
  | 0, matrix =>
      { scalar := 1
        inverse := .nil
        left_identity := by
          apply matrix_ext
          intro row
          exact Fin.elim0 row
        right_identity := by
          apply matrix_ext
          intro row
          exact Fin.elim0 row }
  | n + 1, matrix =>
      extendScaledInverse matrix (scaledInverse (schur matrix))

/-- The recursively constructed inverse satisfies the left scaled identity. -/
theorem scaledInverse_left_identity {n : Nat} (matrix : Matrix K n) :
    mul (scaledInverse matrix).inverse matrix =
      scaleIdentity (scaledInverse matrix).scalar :=
  (scaledInverse matrix).left_identity

/-- The recursively constructed inverse satisfies the right scaled identity. -/
theorem scaledInverse_right_identity {n : Nat} (matrix : Matrix K n) :
    mul matrix (scaledInverse matrix).inverse =
      scaleIdentity (scaledInverse matrix).scalar :=
  (scaledInverse matrix).right_identity

end RFAP.ConstructiveFiniteMatrix
