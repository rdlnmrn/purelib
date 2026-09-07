import CCL.Riemann.FiniteMatrixApproximation

/-!
# Pivot-complete finite scaled inversion

The basic fraction-free block inverse is deliberately total, but fixes the
upper-left entry as its pivot at every recursive stage.  Its scalar can
therefore vanish for an invertible matrix.  This module keeps the construction
finite and polynomial while removing that accidental restriction: at every
stage it evaluates every displayed row/column pivot, transports the resulting
scaled inverses back to the original matrix, and combines them with conjugate
weights.  The combined scalar is a finite sum of Gaussian norm squares, so
there is no cancellation between successful pivot branches.
-/

namespace CCL.Riemann.PivotedScaledInverse

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Matrix (size : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Matrix Gaussian size
abbrev ScaledInverse {size : Nat} (matrix : Matrix size) :=
  RFAP.ConstructiveFiniteMatrix.ScaledInverse matrix

open RFAP.ConstructiveGaussian.Gaussian

/-! ## Finite transpositions -/

/-- Swap index zero with one displayed pivot index. -/
def swapZero {size : Nat} (pivot index : Fin (size + 1)) : Fin (size + 1) :=
  if index = 0 then pivot else if index = pivot then 0 else index

@[simp] theorem swapZero_zero {size : Nat} (pivot : Fin (size + 1)) :
    swapZero pivot 0 = pivot := by
  simp only [swapZero, ↓reduceIte]

theorem swapZero_pivot {size : Nat} (pivot : Fin (size + 1)) :
    swapZero pivot pivot = 0 := by
  by_cases pivotZero : pivot = 0
  · subst pivot
    rfl
  · simp only [swapZero, pivotZero, ↓reduceIte]

theorem swapZero_of_ne {size : Nat} {pivot index : Fin (size + 1)}
    (indexZero : index ≠ 0) (indexPivot : index ≠ pivot) :
    swapZero pivot index = index := by
  simp only [swapZero, indexZero, indexPivot, ↓reduceIte]

@[simp] theorem swapZero_involutive {size : Nat}
    (pivot index : Fin (size + 1)) :
    swapZero pivot (swapZero pivot index) = index := by
  by_cases pivotZero : pivot = 0
  · subst pivot
    simp only [swapZero]
    by_cases indexZero : index = 0
    · simp only [indexZero, ↓reduceIte]
    · simp only [indexZero, ↓reduceIte]
  · by_cases indexZero : index = 0
    · subst index
      rw [swapZero_zero, swapZero_pivot]
    · by_cases indexPivot : index = pivot
      · subst index
        rw [swapZero_pivot, swapZero_zero]
      · rw [swapZero_of_ne indexZero indexPivot,
          swapZero_of_ne indexZero indexPivot]

theorem swapZero_injective {size : Nat} (pivot : Fin (size + 1))
    {left right : Fin (size + 1)}
    (equal : swapZero pivot left = swapZero pivot right) : left = right := by
  have reapplied := congrArg (swapZero pivot) equal
  simpa only [swapZero_involutive] using reapplied

/-- A finite commutative sum is invariant under the displayed transposition.
The proof exposes the two changed summands and cancels their corrections. -/
theorem sumFin_swapZero {K : Type*} [CommRing K] {size : Nat}
    (pivot : Fin (size + 1)) (values : Fin (size + 1) → K) :
    RFAP.ConstructiveFiniteMatrix.sumFin
        (fun index => values (swapZero pivot index)) =
      RFAP.ConstructiveFiniteMatrix.sumFin values := by
  by_cases pivotZero : pivot = 0
  · subst pivot
    apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
    intro index
    simp only [swapZero]
    by_cases indexZero : index = 0
    · simp only [indexZero, ↓reduceIte]
    · simp only [indexZero, ↓reduceIte]
  · let correctionZero : Fin (size + 1) → K := fun index =>
      if index = 0 then values pivot - values 0 else 0
    let correctionPivot : Fin (size + 1) → K := fun index =>
      if index = pivot then values 0 - values pivot else 0
    have pointwise : forall index,
        values (swapZero pivot index) =
          values index + correctionZero index + correctionPivot index := by
      intro index
      by_cases indexZero : index = 0
      · subst index
        simp only [swapZero_zero, correctionZero, correctionPivot,
          Ne.symm pivotZero, ↓reduceIte]
        ring1
      · by_cases indexPivot : index = pivot
        · subst index
          simp only [swapZero_pivot, correctionZero, correctionPivot,
            pivotZero, ↓reduceIte]
          ring1
        · rw [swapZero_of_ne indexZero indexPivot]
          simp only [correctionZero, correctionPivot, indexZero, indexPivot,
            ↓reduceIte]
          ring1
    rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr pointwise]
    rw [RFAP.ConstructiveFiniteMatrix.sumFin_add,
      RFAP.ConstructiveFiniteMatrix.sumFin_add]
    have zeroCorrection :
        RFAP.ConstructiveFiniteMatrix.sumFin correctionZero =
          values pivot - values 0 := by
      unfold correctionZero
      exact RFAP.ConstructiveFiniteMatrix.sumFin_ite_eq 0
        (fun _ => values pivot - values 0)
    have pivotCorrection :
        RFAP.ConstructiveFiniteMatrix.sumFin correctionPivot =
          values 0 - values pivot := by
      unfold correctionPivot
      exact RFAP.ConstructiveFiniteMatrix.sumFin_ite_eq pivot
        (fun _ => values 0 - values pivot)
    rw [zeroCorrection, pivotCorrection]
    ring1

/-- Swap two rows, retaining structural finite matrix data. -/
def swapRows {size : Nat} (matrix : Matrix (size + 1))
    (pivot : Fin (size + 1)) : Matrix (size + 1) :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    matrix (swapZero pivot row) column

/-- Swap two columns. -/
def swapColumns {size : Nat} (matrix : Matrix (size + 1))
    (pivot : Fin (size + 1)) : Matrix (size + 1) :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    matrix row (swapZero pivot column)

@[simp] theorem swapRows_apply {size : Nat} (matrix : Matrix (size + 1))
    (pivot row column : Fin (size + 1)) :
    swapRows matrix pivot row column = matrix (swapZero pivot row) column :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

@[simp] theorem swapColumns_apply {size : Nat} (matrix : Matrix (size + 1))
    (pivot row column : Fin (size + 1)) :
    swapColumns matrix pivot row column = matrix row (swapZero pivot column) :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

@[simp] theorem swapRows_involutive {size : Nat}
    (matrix : Matrix (size + 1)) (pivot : Fin (size + 1)) :
    swapRows (swapRows matrix pivot) pivot = matrix := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  simp only [swapRows_apply, swapZero_involutive]

@[simp] theorem swapColumns_involutive {size : Nat}
    (matrix : Matrix (size + 1)) (pivot : Fin (size + 1)) :
    swapColumns (swapColumns matrix pivot) pivot = matrix := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  simp only [swapColumns_apply, swapZero_involutive]

/-! ## Transporting scaled inverses across pivots -/

theorem mul_swapColumns_swapRows {size : Nat}
    (left right : Matrix (size + 1)) (pivot : Fin (size + 1)) :
    RFAP.ConstructiveFiniteMatrix.mul (swapColumns left pivot)
        (swapRows right pivot) =
      RFAP.ConstructiveFiniteMatrix.mul left right := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [RFAP.ConstructiveFiniteMatrix.mul_apply,
    RFAP.ConstructiveFiniteMatrix.mul_apply]
  calc
    RFAP.ConstructiveFiniteMatrix.sumFin (fun middle =>
        swapColumns left pivot row middle *
          swapRows right pivot middle column) =
        RFAP.ConstructiveFiniteMatrix.sumFin (fun middle =>
          left row (swapZero pivot middle) *
            right (swapZero pivot middle) column) := by
      apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
      intro middle
      rw [swapColumns_apply, swapRows_apply]
    _ = RFAP.ConstructiveFiniteMatrix.sumFin (fun middle =>
          left row middle * right middle column) :=
      sumFin_swapZero pivot
        (fun middle => left row middle * right middle column)

theorem mul_swapColumns_left {size : Nat}
    (left right : Matrix (size + 1)) (pivot : Fin (size + 1)) :
    RFAP.ConstructiveFiniteMatrix.mul (swapColumns left pivot) right =
      RFAP.ConstructiveFiniteMatrix.mul left (swapRows right pivot) := by
  have cancellation := mul_swapColumns_swapRows left
    (swapRows right pivot) pivot
  simpa only [swapRows_involutive] using cancellation

theorem mul_swapRows_right {size : Nat}
    (left right : Matrix (size + 1)) (pivot : Fin (size + 1)) :
    RFAP.ConstructiveFiniteMatrix.mul left (swapRows right pivot) =
      RFAP.ConstructiveFiniteMatrix.mul (swapColumns left pivot) right :=
  (mul_swapColumns_left left right pivot).symm

theorem mul_swapColumns_right {size : Nat}
    (left right : Matrix (size + 1)) (pivot : Fin (size + 1)) :
    RFAP.ConstructiveFiniteMatrix.mul left (swapColumns right pivot) =
      swapColumns (RFAP.ConstructiveFiniteMatrix.mul left right) pivot := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [RFAP.ConstructiveFiniteMatrix.mul_apply, swapColumns_apply,
    RFAP.ConstructiveFiniteMatrix.mul_apply]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro middle
  rw [swapColumns_apply]

theorem mul_swapRows_left {size : Nat}
    (left right : Matrix (size + 1)) (pivot : Fin (size + 1)) :
    RFAP.ConstructiveFiniteMatrix.mul (swapRows left pivot) right =
      swapRows (RFAP.ConstructiveFiniteMatrix.mul left right) pivot := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [RFAP.ConstructiveFiniteMatrix.mul_apply, swapRows_apply,
    RFAP.ConstructiveFiniteMatrix.mul_apply]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro middle
  rw [swapRows_apply]

theorem swapRows_swapColumns_scaleIdentity {size : Nat}
    (scalar : Gaussian) (pivot : Fin (size + 1)) :
    swapRows
        (swapColumns
          (RFAP.ConstructiveFiniteMatrix.scaleIdentity scalar) pivot) pivot =
      RFAP.ConstructiveFiniteMatrix.scaleIdentity scalar := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  simp only [swapRows_apply, swapColumns_apply,
    RFAP.ConstructiveFiniteMatrix.scaleIdentity_apply]
  by_cases equal : row = column
  · subst column
    simp only [if_pos]
  · rw [if_neg equal]
    rw [if_neg (fun swappedEqual =>
      equal (swapZero_injective pivot swappedEqual))]

theorem swapColumns_swapRows_scaleIdentity {size : Nat}
    (scalar : Gaussian) (pivot : Fin (size + 1)) :
    swapColumns
        (swapRows
          (RFAP.ConstructiveFiniteMatrix.scaleIdentity scalar) pivot) pivot =
      RFAP.ConstructiveFiniteMatrix.scaleIdentity scalar := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  simp only [swapColumns_apply, swapRows_apply,
    RFAP.ConstructiveFiniteMatrix.scaleIdentity_apply]
  by_cases equal : row = column
  · subst column
    simp only [if_pos]
  · rw [if_neg equal]
    rw [if_neg (fun swappedEqual =>
      equal (swapZero_injective pivot swappedEqual))]

/-- Move one displayed entry to the upper-left corner. -/
def pivotMatrix {size : Nat} (matrix : Matrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) : Matrix (size + 1) :=
  swapColumns (swapRows matrix rowPivot) columnPivot

/-! ## Constructive left-kernel completeness -/

/-- A finite square matrix has trivial displayed left kernel.  This
formulation is deliberately pointwise: both the vector and every vanishing
column are finite structural data. -/
def LeftKernelTrivial {size : Nat} (matrix : Matrix size) : Prop :=
  forall vector : RFAP.ConstructiveFiniteMatrix.Vector Gaussian size,
    (forall column,
      RFAP.ConstructiveFiniteMatrix.vectorMatrix vector matrix column = 0) ->
      forall row, vector row = 0

/-- Moving a displayed matrix entry to the upper-left corner preserves
triviality of the finite left kernel. -/
theorem leftKernelTrivial_pivotMatrix {size : Nat}
    {matrix : Matrix (size + 1)} (trivial : LeftKernelTrivial matrix)
    (rowPivot columnPivot : Fin (size + 1)) :
    LeftKernelTrivial (pivotMatrix matrix rowPivot columnPivot) := by
  intro vector kernel row
  let unpivoted := RFAP.ConstructiveFiniteMatrix.vectorOfFn fun index =>
    vector (swapZero rowPivot index)
  have unpivotedKernel : forall column,
      RFAP.ConstructiveFiniteMatrix.vectorMatrix unpivoted matrix column = 0 := by
    intro column
    have pivotKernel := kernel (swapZero columnPivot column)
    rw [RFAP.ConstructiveFiniteMatrix.vectorMatrix_apply] at pivotKernel
    rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
      (right := fun index => vector index *
        matrix (swapZero rowPivot index) column)
      (fun index => by
        unfold pivotMatrix
        rw [swapColumns_apply, swapRows_apply, swapZero_involutive])]
      at pivotKernel
    rw [RFAP.ConstructiveFiniteMatrix.vectorMatrix_apply]
    have sumZero : RFAP.ConstructiveFiniteMatrix.sumFin
        (fun index => vector (swapZero rowPivot index) * matrix index column) =
          0 := by
      calc
      RFAP.ConstructiveFiniteMatrix.sumFin
          (fun index => vector (swapZero rowPivot index) * matrix index column) =
          RFAP.ConstructiveFiniteMatrix.sumFin
            (fun index =>
              (fun source => vector source *
                matrix (swapZero rowPivot source) column)
                  (swapZero rowPivot index)) := by
            apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
            intro index
            change vector (swapZero rowPivot index) * matrix index column =
              vector (swapZero rowPivot index) *
                matrix (swapZero rowPivot (swapZero rowPivot index)) column
            rw [swapZero_involutive]
      _ = RFAP.ConstructiveFiniteMatrix.sumFin
            (fun index => vector index *
              matrix (swapZero rowPivot index) column) :=
          by
            let values := fun source => vector source *
              matrix (swapZero rowPivot source) column
            change RFAP.ConstructiveFiniteMatrix.sumFin (fun index =>
                values (swapZero rowPivot index)) =
              RFAP.ConstructiveFiniteMatrix.sumFin values
            exact sumFin_swapZero rowPivot values
      _ = 0 := pivotKernel
    rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
      (right := fun index =>
        vector (swapZero rowPivot index) * matrix index column)
      (fun index => by
        rw [show unpivoted index = vector (swapZero rowPivot index) by
          unfold unpivoted
          exact RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply _ _])]
    exact sumZero
  have zero := trivial unpivoted unpivotedKernel (swapZero rowPivot row)
  rw [show unpivoted (swapZero rowPivot row) =
      vector (swapZero rowPivot (swapZero rowPivot row)) by
        exact RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply _ _] at zero
  rw [swapZero_involutive] at zero
  exact zero

private inductive NonzeroVectorResult (count : Nat)
    (values : Fin count -> Gaussian) where
  | found (index : Fin count) (nonzero : values index ≠ 0)
  | allZero (zero : forall index, values index = 0)

private def nonzeroVectorSearch (count : Nat)
    (values : Fin count -> Gaussian) :
    NonzeroVectorResult count values := by
  cases count with
  | zero =>
      exact .allZero fun index => Fin.elim0 index
  | succ count =>
      by_cases headZero : values 0 = 0
      · cases nonzeroVectorSearch count (fun index => values index.succ) with
        | found index nonzero => exact .found index.succ nonzero
        | allZero tailZero =>
            exact .allZero fun index =>
              Fin.cases headZero (fun tail => tailZero tail) index
      · exact .found 0 headZero

private inductive NonzeroMatrixResult (rowCount columnCount : Nat)
    (matrix : Fin rowCount -> Fin columnCount -> Gaussian) where
  | found (row : Fin rowCount) (column : Fin columnCount)
      (nonzero : matrix row column ≠ 0)
  | allZero (zero : forall row column, matrix row column = 0)

private def nonzeroMatrixSearch (rowCount columnCount : Nat)
    (matrix : Fin rowCount -> Fin columnCount -> Gaussian) :
    NonzeroMatrixResult rowCount columnCount matrix := by
  cases rowCount with
  | zero =>
      exact .allZero fun row => Fin.elim0 row
  | succ rowCount =>
      cases nonzeroVectorSearch columnCount (matrix 0) with
      | found column nonzero => exact .found 0 column nonzero
      | allZero headZero =>
          cases nonzeroMatrixSearch rowCount columnCount
              (fun row => matrix row.succ) with
          | found row column nonzero =>
              exact .found row.succ column nonzero
          | allZero tailZero =>
              exact .allZero fun row =>
                Fin.cases headZero (fun tail => tailZero tail) row

/-- A nonempty matrix with trivial left kernel contains a displayed nonzero
entry.  The witness is found by explicit structural search over its two
finite index dimensions. -/
theorem exists_nonzero_entry_of_leftKernelTrivial {size : Nat}
    (matrix : Matrix (size + 1)) (trivial : LeftKernelTrivial matrix) :
    exists row column, matrix row column ≠ 0 := by
  cases nonzeroMatrixSearch (size + 1) (size + 1)
      (fun row column => matrix row column) with
  | found row column nonzero => exact ⟨row, column, nonzero⟩
  | allZero allZero =>
    let selected := RFAP.ConstructiveFiniteMatrix.vectorOfFn fun row =>
      if row = (0 : Fin (size + 1)) then (1 : Gaussian) else 0
    have selectedKernel : forall column,
        RFAP.ConstructiveFiniteMatrix.vectorMatrix selected matrix column = 0 := by
      intro column
      rw [RFAP.ConstructiveFiniteMatrix.vectorMatrix_apply]
      rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
        (right := fun _ => (0 : Gaussian)) (fun row => by
          rw [allZero row column, mul_zero])]
      exact RFAP.ConstructiveFiniteMatrix.sumFin_zero
    have selectedZero := trivial selected selectedKernel 0
    change (if (0 : Fin (size + 1)) = 0 then (1 : Gaussian) else 0) = 0 at selectedZero
    exact (one_ne_zero selectedZero).elim

/-- With a nonzero upper-left pivot, triviality of the full left kernel
descends constructively to the fraction-free Schur matrix. -/
theorem leftKernelTrivial_schur_of_head_nonzero {size : Nat}
    (matrix : Matrix (size + 1)) (trivial : LeftKernelTrivial matrix)
    (headNonzero : RFAP.ConstructiveFiniteMatrix.head matrix ≠ 0) :
    LeftKernelTrivial (RFAP.ConstructiveFiniteMatrix.schur matrix) := by
  intro vector kernel row
  let columnPairing := RFAP.ConstructiveFiniteMatrix.dot vector
    (RFAP.ConstructiveFiniteMatrix.leftColumn matrix)
  let lifted : RFAP.ConstructiveFiniteMatrix.Vector Gaussian (size + 1) :=
    RFAP.ConstructiveFiniteMatrix.vectorOfFn fun index =>
      index.cases (-columnPairing)
        (fun tail => RFAP.ConstructiveFiniteMatrix.head matrix * vector tail)
  have lifted_zero : lifted 0 = -columnPairing := by
    unfold lifted
    rw [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply, Fin.cases_zero]
  have lifted_succ (index : Fin size) :
      lifted index.succ =
        RFAP.ConstructiveFiniteMatrix.head matrix * vector index := by
    unfold lifted
    rw [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply, Fin.cases_succ]
  have liftedKernel : forall column,
      RFAP.ConstructiveFiniteMatrix.vectorMatrix lifted matrix column = 0 := by
    intro column
    refine Fin.cases ?_ (fun tailColumn => ?_) column
    · rw [RFAP.ConstructiveFiniteMatrix.vectorMatrix_apply,
        RFAP.ConstructiveFiniteMatrix.sumFin_succ]
      rw [lifted_zero]
      rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
        (right := fun index => RFAP.ConstructiveFiniteMatrix.head matrix *
          vector index * matrix index.succ 0)
        (fun index => by rw [lifted_succ index])]
      calc
        -columnPairing * matrix 0 0 +
            RFAP.ConstructiveFiniteMatrix.sumFin (fun index =>
              matrix 0 0 * vector index * matrix index.succ 0) =
            -columnPairing * RFAP.ConstructiveFiniteMatrix.head matrix +
              RFAP.ConstructiveFiniteMatrix.sumFin (fun index =>
                RFAP.ConstructiveFiniteMatrix.head matrix * vector index *
                  RFAP.ConstructiveFiniteMatrix.leftColumn matrix index) := by
          change -columnPairing * RFAP.ConstructiveFiniteMatrix.head matrix +
              RFAP.ConstructiveFiniteMatrix.sumFin (fun index =>
                RFAP.ConstructiveFiniteMatrix.head matrix * vector index *
                  matrix index.succ 0) = _
          apply congrArg (fun total : Gaussian =>
            -columnPairing * RFAP.ConstructiveFiniteMatrix.head matrix + total)
          apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
          intro index
          rw [RFAP.ConstructiveFiniteMatrix.leftColumn_apply]
        _ = 0 := by
          rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
            (right := fun index => RFAP.ConstructiveFiniteMatrix.head matrix *
              (vector index *
                RFAP.ConstructiveFiniteMatrix.leftColumn matrix index))
            (fun _ => by ring1)]
          rw [RFAP.ConstructiveFiniteMatrix.sumFin_mul_left]
          unfold columnPairing RFAP.ConstructiveFiniteMatrix.dot
          ring1
    · rw [RFAP.ConstructiveFiniteMatrix.vectorMatrix_apply,
        RFAP.ConstructiveFiniteMatrix.sumFin_succ]
      rw [lifted_zero]
      rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
        (right := fun index => RFAP.ConstructiveFiniteMatrix.head matrix *
          vector index * matrix index.succ tailColumn.succ)
        (fun index => by rw [lifted_succ index])]
      calc
        -columnPairing * matrix 0 tailColumn.succ +
            RFAP.ConstructiveFiniteMatrix.sumFin (fun index =>
              RFAP.ConstructiveFiniteMatrix.head matrix * vector index *
                matrix index.succ tailColumn.succ) =
            -columnPairing *
                RFAP.ConstructiveFiniteMatrix.topRow matrix tailColumn +
              RFAP.ConstructiveFiniteMatrix.sumFin (fun index =>
                RFAP.ConstructiveFiniteMatrix.head matrix * vector index *
                  RFAP.ConstructiveFiniteMatrix.tail matrix index
                    tailColumn) := by
          rw [show matrix 0 tailColumn.succ =
              RFAP.ConstructiveFiniteMatrix.topRow matrix tailColumn by
            exact (RFAP.ConstructiveFiniteMatrix.topRow_apply
              matrix tailColumn).symm]
          apply congrArg (fun total : Gaussian =>
            -columnPairing *
              RFAP.ConstructiveFiniteMatrix.topRow matrix tailColumn + total)
          apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
          intro index
          rw [RFAP.ConstructiveFiniteMatrix.tail_apply]
        _ = RFAP.ConstructiveFiniteMatrix.head matrix *
                RFAP.ConstructiveFiniteMatrix.vectorMatrix vector
                  (RFAP.ConstructiveFiniteMatrix.tail matrix) tailColumn -
              RFAP.ConstructiveFiniteMatrix.dot vector
                  (RFAP.ConstructiveFiniteMatrix.leftColumn matrix) *
                RFAP.ConstructiveFiniteMatrix.topRow matrix tailColumn := by
          rw [RFAP.ConstructiveFiniteMatrix.vectorMatrix_apply]
          rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
            (right := fun index =>
              RFAP.ConstructiveFiniteMatrix.head matrix *
                (vector index *
                  RFAP.ConstructiveFiniteMatrix.tail matrix index tailColumn))
            (fun _ => by ring1)]
          rw [RFAP.ConstructiveFiniteMatrix.sumFin_mul_left]
          unfold columnPairing
          ring1
        _ = RFAP.ConstructiveFiniteMatrix.vectorMatrix vector
              (RFAP.ConstructiveFiniteMatrix.schur matrix) tailColumn := by
          exact (RFAP.ConstructiveFiniteMatrix.vectorMatrix_schur
            vector matrix tailColumn).symm
        _ = 0 := kernel tailColumn
  have productZero := trivial lifted liftedKernel row.succ
  rw [show lifted row.succ =
      RFAP.ConstructiveFiniteMatrix.head matrix * vector row by
        exact RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply _ _] at productZero
  by_cases vectorZero : vector row = 0
  · exact vectorZero
  · exact (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      headNonzero vectorZero productZero).elim

/-- Transport a scaled inverse of a row/column-pivoted matrix back to the
original matrix. -/
def unpivotScaledInverse {size : Nat} (matrix : Matrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (inverse : ScaledInverse (pivotMatrix matrix rowPivot columnPivot)) :
    ScaledInverse matrix where
  scalar := inverse.scalar
  inverse := swapColumns (swapRows inverse.inverse columnPivot) rowPivot
  left_identity := by
    have pivotLeft := inverse.left_identity
    unfold pivotMatrix at pivotLeft
    rw [mul_swapColumns_right] at pivotLeft
    have uncolumned := congrArg
      (fun value : Matrix (size + 1) => swapColumns value columnPivot)
      pivotLeft
    simp only [swapColumns_involutive] at uncolumned
    calc
      RFAP.ConstructiveFiniteMatrix.mul
          (swapColumns (swapRows inverse.inverse columnPivot) rowPivot)
            matrix =
          RFAP.ConstructiveFiniteMatrix.mul
            (swapRows inverse.inverse columnPivot)
              (swapRows matrix rowPivot) :=
        mul_swapColumns_left _ _ _
      _ = swapRows
            (RFAP.ConstructiveFiniteMatrix.mul inverse.inverse
              (swapRows matrix rowPivot)) columnPivot :=
        mul_swapRows_left _ _ _
      _ = swapRows
            (swapColumns
              (RFAP.ConstructiveFiniteMatrix.scaleIdentity inverse.scalar)
                columnPivot) columnPivot := by
        rw [uncolumned]
      _ = RFAP.ConstructiveFiniteMatrix.scaleIdentity inverse.scalar :=
        swapRows_swapColumns_scaleIdentity _ _
  right_identity := by
    have pivotRight := inverse.right_identity
    unfold pivotMatrix at pivotRight
    rw [mul_swapColumns_left, mul_swapRows_left] at pivotRight
    have unrowed := congrArg
      (fun value : Matrix (size + 1) => swapRows value rowPivot) pivotRight
    simp only [swapRows_involutive] at unrowed
    calc
      RFAP.ConstructiveFiniteMatrix.mul matrix
          (swapColumns (swapRows inverse.inverse columnPivot) rowPivot) =
          swapColumns
            (RFAP.ConstructiveFiniteMatrix.mul matrix
              (swapRows inverse.inverse columnPivot)) rowPivot :=
        mul_swapColumns_right _ _ _
      _ = swapColumns
            (swapRows
              (RFAP.ConstructiveFiniteMatrix.scaleIdentity inverse.scalar)
                rowPivot) rowPivot := by
        rw [unrowed]
      _ = RFAP.ConstructiveFiniteMatrix.scaleIdentity inverse.scalar :=
        swapColumns_swapRows_scaleIdentity _ _

@[simp] theorem unpivotScaledInverse_scalar {size : Nat}
    (matrix : Matrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (inverse : ScaledInverse (pivotMatrix matrix rowPivot columnPivot)) :
    (unpivotScaledInverse matrix rowPivot columnPivot inverse).scalar =
      inverse.scalar := rfl

/-! ## Finite aggregation of scaled inverses -/

/-- Entrywise finite weighted sum of square matrices. -/
def weightedMatrix {count size : Nat} (weights : Fin count → Gaussian)
    (matrices : Fin count → Matrix size) : Matrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    RFAP.ConstructiveFiniteMatrix.sumFin fun index =>
      weights index * matrices index row column

@[simp] theorem weightedMatrix_apply {count size : Nat}
    (weights : Fin count → Gaussian) (matrices : Fin count → Matrix size)
    (row column : Fin size) :
    weightedMatrix weights matrices row column =
      RFAP.ConstructiveFiniteMatrix.sumFin fun index =>
        weights index * matrices index row column :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

theorem mul_weightedMatrix_left {count size : Nat}
    (weights : Fin count → Gaussian) (matrices : Fin count → Matrix size)
    (right : Matrix size) :
    RFAP.ConstructiveFiniteMatrix.mul (weightedMatrix weights matrices) right =
      weightedMatrix weights
        (fun index => RFAP.ConstructiveFiniteMatrix.mul
          (matrices index) right) := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [RFAP.ConstructiveFiniteMatrix.mul_apply, weightedMatrix_apply]
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
    (right := fun middle =>
      RFAP.ConstructiveFiniteMatrix.sumFin fun index =>
        (weights index * matrices index row middle) * right middle column)
    (fun middle => by
      rw [weightedMatrix_apply]
      exact (RFAP.ConstructiveFiniteMatrix.sumFin_mul_right
        (fun index => weights index * matrices index row middle)
          (right middle column)).symm)]
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_swap]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro index
  rw [RFAP.ConstructiveFiniteMatrix.mul_apply]
  rw [← RFAP.ConstructiveFiniteMatrix.sumFin_mul_left]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro middle
  ring1

theorem mul_weightedMatrix_right {count size : Nat}
    (left : Matrix size) (weights : Fin count → Gaussian)
    (matrices : Fin count → Matrix size) :
    RFAP.ConstructiveFiniteMatrix.mul left (weightedMatrix weights matrices) =
      weightedMatrix weights
        (fun index => RFAP.ConstructiveFiniteMatrix.mul left
          (matrices index)) := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [RFAP.ConstructiveFiniteMatrix.mul_apply, weightedMatrix_apply]
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
    (right := fun middle =>
      RFAP.ConstructiveFiniteMatrix.sumFin fun index =>
        weights index * (left row middle * matrices index middle column))
    (fun middle => by
      rw [weightedMatrix_apply]
      rw [← RFAP.ConstructiveFiniteMatrix.sumFin_mul_left]
      apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
      intro index
      ring1)]
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_swap]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro index
  rw [RFAP.ConstructiveFiniteMatrix.mul_apply]
  rw [← RFAP.ConstructiveFiniteMatrix.sumFin_mul_left]

theorem weightedMatrix_scaleIdentity {count size : Nat}
    (weights scalars : Fin count → Gaussian) :
    weightedMatrix weights
        (fun index => (RFAP.ConstructiveFiniteMatrix.scaleIdentity
          (scalars index) : Matrix size)) =
      RFAP.ConstructiveFiniteMatrix.scaleIdentity
        (RFAP.ConstructiveFiniteMatrix.sumFin fun index =>
          weights index * scalars index) := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [weightedMatrix_apply,
    RFAP.ConstructiveFiniteMatrix.scaleIdentity_apply]
  by_cases equal : row = column
  · subst column
    rw [if_pos rfl]
    apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
    intro index
    rw [RFAP.ConstructiveFiniteMatrix.scaleIdentity_apply, if_pos rfl]
  · rw [if_neg equal]
    rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
      (right := fun _ => (0 : Gaussian)) (fun index => by
        rw [RFAP.ConstructiveFiniteMatrix.scaleIdentity_apply, if_neg equal,
          mul_zero])]
    exact RFAP.ConstructiveFiniteMatrix.sumFin_zero

/-- Any finite weighted sum of scaled inverses is another scaled inverse.
This algebraic closure is what permits all pivot branches to be retained
without making a discontinuous pivot choice. -/
def aggregateScaledInverse {count size : Nat} {matrix : Matrix size}
    (branches : Fin count → ScaledInverse matrix)
    (weights : Fin count → Gaussian) : ScaledInverse matrix where
  scalar := RFAP.ConstructiveFiniteMatrix.sumFin fun index =>
    weights index * (branches index).scalar
  inverse := weightedMatrix weights fun index => (branches index).inverse
  left_identity := by
    rw [mul_weightedMatrix_left]
    calc
      weightedMatrix weights
          (fun index => RFAP.ConstructiveFiniteMatrix.mul
            (branches index).inverse matrix) =
          weightedMatrix weights
            (fun index => (RFAP.ConstructiveFiniteMatrix.scaleIdentity
              (branches index).scalar : Matrix size)) := by
        apply RFAP.ConstructiveFiniteMatrix.matrix_ext
        intro row column
        rw [weightedMatrix_apply, weightedMatrix_apply]
        apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
        intro index
        rw [RFAP.ConstructiveFiniteMatrix.matrix_eq_at
          (branches index).left_identity row column]
      _ = RFAP.ConstructiveFiniteMatrix.scaleIdentity
            (RFAP.ConstructiveFiniteMatrix.sumFin fun index =>
              weights index * (branches index).scalar) :=
        weightedMatrix_scaleIdentity weights
          (fun index => (branches index).scalar)
  right_identity := by
    rw [mul_weightedMatrix_right]
    calc
      weightedMatrix weights
          (fun index => RFAP.ConstructiveFiniteMatrix.mul matrix
            (branches index).inverse) =
          weightedMatrix weights
            (fun index => (RFAP.ConstructiveFiniteMatrix.scaleIdentity
              (branches index).scalar : Matrix size)) := by
        apply RFAP.ConstructiveFiniteMatrix.matrix_ext
        intro row column
        rw [weightedMatrix_apply, weightedMatrix_apply]
        apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
        intro index
        rw [RFAP.ConstructiveFiniteMatrix.matrix_eq_at
          (branches index).right_identity row column]
      _ = RFAP.ConstructiveFiniteMatrix.scaleIdentity
            (RFAP.ConstructiveFiniteMatrix.sumFin fun index =>
              weights index * (branches index).scalar) :=
        weightedMatrix_scaleIdentity weights
          (fun index => (branches index).scalar)

@[simp] theorem aggregateScaledInverse_scalar {count size : Nat}
    {matrix : Matrix size} (branches : Fin count → ScaledInverse matrix)
    (weights : Fin count → Gaussian) :
    (aggregateScaledInverse branches weights).scalar =
      RFAP.ConstructiveFiniteMatrix.sumFin fun index =>
        weights index * (branches index).scalar := rfl

theorem coordinateSum_mono {count : Nat}
    (left right : Fin count → Coordinate)
    (entry_le : forall index, left index <= right index) :
    RFAP.ConstructiveFiniteMatrix.sumFin left <=
      RFAP.ConstructiveFiniteMatrix.sumFin right := by
  induction count with
  | zero => exact le_rfl
  | succ count inductionHypothesis =>
      rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ,
        RFAP.ConstructiveFiniteMatrix.sumFin_succ]
      exact add_le_add (entry_le 0)
        (inductionHypothesis (fun index => left index.succ)
          (fun index => right index.succ)
          (fun index => entry_le index.succ))

theorem coordinateSum_positive_of_index {count : Nat}
    (values : Fin count → Coordinate) (selected : Fin count)
    (nonnegative : forall index, 0 <= values index)
    (positive : 0 < values selected) :
    0 < RFAP.ConstructiveFiniteMatrix.sumFin values := by
  have selected_le_sum :
      values selected <= RFAP.ConstructiveFiniteMatrix.sumFin values := by
    calc
      values selected =
          RFAP.ConstructiveFiniteMatrix.sumFin (fun index =>
            if index = selected then values index else 0) :=
        (RFAP.ConstructiveFiniteMatrix.sumFin_ite_eq selected values).symm
      _ <= RFAP.ConstructiveFiniteMatrix.sumFin values :=
        coordinateSum_mono _ _ (fun index => by
          by_cases equal : index = selected
          · rw [if_pos equal]
          · rw [if_neg equal]
            exact nonnegative index)
  exact positive.trans_le selected_le_sum

theorem sumFin_re {count : Nat} (values : Fin count → Gaussian) :
    (RFAP.ConstructiveFiniteMatrix.sumFin values).re =
      RFAP.ConstructiveFiniteMatrix.sumFin (fun index => (values index).re) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ,
        RFAP.ConstructiveFiniteMatrix.sumFin_succ,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        inductionHypothesis (fun index => values index.succ)]

theorem conj_mul_self_re (value : Gaussian) :
    (conj value * value).re = normSq value := by
  simp only [conj, RFAP.ConstructiveGaussian.Gaussian.mul_re, normSq]
  ring1

/-- A successful finite pivot branch cannot be cancelled by the other
branches: conjugate weighting makes the aggregate scalar's real coordinate a
sum of squared norms. -/
theorem aggregateConjugate_scalar_nonzero_of_branch {count size : Nat}
    {matrix : Matrix size} (branches : Fin count → ScaledInverse matrix)
    (selected : Fin count) (selectedNonzero : (branches selected).scalar ≠ 0) :
    (aggregateScaledInverse branches
      (fun index => conj (branches index).scalar)).scalar ≠ 0 := by
  have realIdentity :
      (aggregateScaledInverse branches
        (fun index => conj (branches index).scalar)).scalar.re =
        RFAP.ConstructiveFiniteMatrix.sumFin fun index =>
          normSq (branches index).scalar := by
    rw [aggregateScaledInverse_scalar, sumFin_re]
    apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
    intro index
    exact conj_mul_self_re (branches index).scalar
  have realPositive :
      0 < RFAP.ConstructiveFiniteMatrix.sumFin fun index =>
        normSq (branches index).scalar :=
    coordinateSum_positive_of_index _ selected
      (fun index => normSq_nonneg (branches index).scalar)
      (normSq_pos selectedNonzero)
  intro aggregateZero
  have zeroReal := congrArg RFAP.ConstructiveGaussian.Gaussian.re aggregateZero
  rw [realIdentity] at zeroReal
  change RFAP.ConstructiveFiniteMatrix.sumFin
      (fun index => normSq (branches index).scalar) = 0 at zeroReal
  rw [zeroReal] at realPositive
  exact lt_irrefl 0 realPositive

/-! ## Pivot-complete exact recursion -/

/-- One exact pivot branch, parameterized by the recursively computed scaled
inverse of its Schur matrix. -/
def pivotBranch {size : Nat} (matrix : Matrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (smaller : ScaledInverse
      (RFAP.ConstructiveFiniteMatrix.schur
        (pivotMatrix matrix rowPivot columnPivot))) : ScaledInverse matrix :=
  let pivoted := pivotMatrix matrix rowPivot columnPivot
  unpivotScaledInverse matrix rowPivot columnPivot
    (RFAP.ConstructiveFiniteMatrix.extendScaledInverse pivoted smaller)

/-- All row/column pivot branches of the fraction-free recursion are retained.
Each finite aggregation uses conjugate scalar weights, so its new scalar is a
sum of Gaussian norm squares rather than a cancellation-prone sum. -/
def completeScaledInverse : {size : Nat} ->
    (matrix : Matrix size) -> ScaledInverse matrix
  | 0, matrix => RFAP.ConstructiveFiniteMatrix.scaledInverse matrix
  | _size + 1, matrix =>
      let branch := fun rowPivot columnPivot =>
        pivotBranch matrix rowPivot columnPivot
          (completeScaledInverse
            (RFAP.ConstructiveFiniteMatrix.schur
              (pivotMatrix matrix rowPivot columnPivot)))
      let rowBranch := fun rowPivot =>
        aggregateScaledInverse (branch rowPivot)
          (fun columnPivot => conj (branch rowPivot columnPivot).scalar)
      aggregateScaledInverse rowBranch
        (fun rowPivot => conj (rowBranch rowPivot).scalar)

def completeExactBranch {size : Nat} (matrix : Matrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) : ScaledInverse matrix :=
  pivotBranch matrix rowPivot columnPivot
    (completeScaledInverse
      (RFAP.ConstructiveFiniteMatrix.schur
        (pivotMatrix matrix rowPivot columnPivot)))

def completeExactRow {size : Nat} (matrix : Matrix (size + 1))
    (rowPivot : Fin (size + 1)) : ScaledInverse matrix :=
  aggregateScaledInverse (completeExactBranch matrix rowPivot)
    (fun columnPivot =>
      conj (completeExactBranch matrix rowPivot columnPivot).scalar)

theorem completeScaledInverse_succ {size : Nat}
    (matrix : Matrix (size + 1)) :
    completeScaledInverse matrix =
      aggregateScaledInverse (completeExactRow matrix)
        (fun rowPivot => conj (completeExactRow matrix rowPivot).scalar) := rfl

theorem completeScaledInverse_left_identity {size : Nat}
    (matrix : Matrix size) :
    RFAP.ConstructiveFiniteMatrix.mul
        (completeScaledInverse matrix).inverse matrix =
      RFAP.ConstructiveFiniteMatrix.scaleIdentity
        (completeScaledInverse matrix).scalar :=
  (completeScaledInverse matrix).left_identity

theorem completeScaledInverse_right_identity {size : Nat}
    (matrix : Matrix size) :
    RFAP.ConstructiveFiniteMatrix.mul matrix
        (completeScaledInverse matrix).inverse =
      RFAP.ConstructiveFiniteMatrix.scaleIdentity
        (completeScaledInverse matrix).scalar :=
  (completeScaledInverse matrix).right_identity

private theorem sumFin_one (values : Fin 1 -> Gaussian) :
    RFAP.ConstructiveFiniteMatrix.sumFin values = values 0 := by
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change values 0 + 0 = values 0
  ring1

private theorem completeExactBranch_one_scalar (matrix : Matrix 1) :
    (completeExactBranch matrix 0 0).scalar = matrix 0 0 := by
  unfold completeExactBranch pivotBranch
  rw [unpivotScaledInverse_scalar]
  change RFAP.ConstructiveFiniteMatrix.head (pivotMatrix matrix 0 0) * 1 =
    matrix 0 0
  unfold RFAP.ConstructiveFiniteMatrix.head pivotMatrix
  rw [swapColumns_apply, swapRows_apply, swapZero_zero]
  ring1

/-- In dimension one the pivot-complete recursion has just one row and one
column branch.  Its two conjugate aggregations therefore expose the fourth
power construction explicitly. -/
theorem completeScaledInverse_one_scalar (matrix : Matrix 1) :
    (completeScaledInverse matrix).scalar =
      conj (conj (matrix 0 0) * matrix 0 0) *
        (conj (matrix 0 0) * matrix 0 0) := by
  rw [completeScaledInverse_succ, aggregateScaledInverse_scalar, sumFin_one]
  unfold completeExactRow
  rw [aggregateScaledInverse_scalar, sumFin_one]
  rw [completeExactBranch_one_scalar]

/-- Consequently the squared norm of the dimension-one canonical scalar is
the fourth power of the squared norm of the sole matrix entry. -/
theorem normSq_completeScaledInverse_one_scalar (matrix : Matrix 1) :
    normSq (completeScaledInverse matrix).scalar =
      normSq (matrix 0 0) ^ 4 := by
  rw [completeScaledInverse_one_scalar]
  repeat' rw [normSq_mul, normSq_conj]
  ring1

/-! ## Synchronized geometric recursion -/

abbrev GeometricApproximation :=
  CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation
abbrev GeometricMatrix (size : Nat) :=
  CCL.Riemann.FiniteMatrixApproximation.GeometricMatrix size
abbrev ScaledInverseApproximation (size : Nat) :=
  CCL.Riemann.FiniteMatrixApproximation.ScaledInverseApproximation size

/-- Conjugation preserves every geometric movement and boundedness estimate. -/
def geometricConj (source : GeometricApproximation) :
    GeometricApproximation where
  sample := fun index => conj (source.sample index)
  errorScale := source.errorScale
  errorScale_nonneg := source.errorScale_nonneg
  later_close := by
    intro earlier later order
    have movement := source.later_close order
    have difference :
        conj (source.sample later) - conj (source.sample earlier) =
          conj (source.sample later - source.sample earlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext
      · simp only [conj, RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im]
      · simp only [conj, RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im]
        ring1
    rw [difference, normSq_conj]
    exact movement
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [normSq_conj]
    exact source.sample_bounded index

@[simp] theorem geometricConj_sample (source : GeometricApproximation)
    (index : Nat) :
    (geometricConj source).sample index = conj (source.sample index) := rfl

def geometricSwapRows {size : Nat} (matrix : GeometricMatrix (size + 1))
    (pivot : Fin (size + 1)) : GeometricMatrix (size + 1) :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    matrix (swapZero pivot row) column

def geometricSwapColumns {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (pivot : Fin (size + 1)) : GeometricMatrix (size + 1) :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    matrix row (swapZero pivot column)

@[simp] theorem geometricSwapRows_apply {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (pivot row column : Fin (size + 1)) :
    geometricSwapRows matrix pivot row column =
      matrix (swapZero pivot row) column :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

@[simp] theorem geometricSwapColumns_apply {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (pivot row column : Fin (size + 1)) :
    geometricSwapColumns matrix pivot row column =
      matrix row (swapZero pivot column) :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

def geometricPivotMatrix {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) : GeometricMatrix (size + 1) :=
  geometricSwapColumns (geometricSwapRows matrix rowPivot) columnPivot

def geometricUnpivotInverse {size : Nat}
    (inverse : GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) :
    GeometricMatrix (size + 1) :=
  geometricSwapColumns (geometricSwapRows inverse columnPivot) rowPivot

/-- Entrywise synchronized weighted sum. -/
def geometricWeightedMatrix {count size : Nat}
    (weights : Fin count → GeometricApproximation)
    (matrices : Fin count → GeometricMatrix size) : GeometricMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sum
      fun index =>
        CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
          (weights index) (matrices index row column)

@[simp] theorem geometricWeightedMatrix_apply {count size : Nat}
    (weights : Fin count → GeometricApproximation)
    (matrices : Fin count → GeometricMatrix size)
    (row column : Fin size) :
    geometricWeightedMatrix weights matrices row column =
      CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sum
        fun index =>
          CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
            (weights index) (matrices index row column) :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

def geometricAggregate {count size : Nat}
    (branches : Fin count → ScaledInverseApproximation size)
    (weights : Fin count → GeometricApproximation) :
    ScaledInverseApproximation size where
  scalar := CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sum
    fun index =>
      CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
        (weights index) (branches index).scalar
  inverse := geometricWeightedMatrix weights
    fun index => (branches index).inverse

/-- One synchronized pivot branch, parameterized by the recursively computed
Schur approximation. -/
def geometricPivotBranch {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (smaller : ScaledInverseApproximation size) :
    ScaledInverseApproximation (size + 1) :=
  let pivoted := geometricPivotMatrix matrix rowPivot columnPivot
  { scalar :=
      CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
        (pivoted 0 0) smaller.scalar
    inverse := geometricUnpivotInverse
      (CCL.Riemann.FiniteMatrixApproximation.blockInverse pivoted smaller)
        rowPivot columnPivot }

/-- The synchronized all-pivots recursion mirrors `completeScaledInverse`
exactly at every sample index. -/
def completeApproximation : {size : Nat} ->
    GeometricMatrix size -> ScaledInverseApproximation size
  | 0, _matrix =>
      { scalar :=
          CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact 1
        inverse := RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row =>
          Fin.elim0 row }
  | _size + 1, matrix =>
      let branch := fun rowPivot columnPivot =>
        geometricPivotBranch matrix rowPivot columnPivot
          (completeApproximation
            (CCL.Riemann.FiniteMatrixApproximation.schur
              (geometricPivotMatrix matrix rowPivot columnPivot)))
      let rowBranch := fun rowPivot =>
        geometricAggregate (branch rowPivot)
          (fun columnPivot =>
            geometricConj (branch rowPivot columnPivot).scalar)
      geometricAggregate rowBranch
        (fun rowPivot => geometricConj (rowBranch rowPivot).scalar)

/-- Any successful recursive row/column pivot proves the complete scalar
nonzero; all other branches can only add squared-norm contributions. -/
theorem completeScaledInverse_scalar_nonzero_of_branch {size : Nat}
    (matrix : Matrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1))
    (branchNonzero :
      (completeExactBranch matrix rowPivot columnPivot).scalar ≠ 0) :
    (completeScaledInverse matrix).scalar ≠ 0 := by
  have rowNonzero : (completeExactRow matrix rowPivot).scalar ≠ 0 :=
    aggregateConjugate_scalar_nonzero_of_branch
      (completeExactBranch matrix rowPivot) columnPivot branchNonzero
  rw [completeScaledInverse_succ]
  exact aggregateConjugate_scalar_nonzero_of_branch
    (completeExactRow matrix) rowPivot rowNonzero

/-- The pivot-complete fraction-free construction is complete for finite
Gaussian matrices: a trivial displayed left kernel constructively produces a
nonzero canonical scalar.  The proof searches the bounded entry table for a
pivot, descends to its Schur matrix, and retains that successful branch in the
conjugate-weighted aggregate. -/
theorem completeScaledInverse_scalar_nonzero_of_leftKernelTrivial :
    {size : Nat} -> (matrix : Matrix size) -> LeftKernelTrivial matrix ->
      (completeScaledInverse matrix).scalar ≠ 0
  | 0, matrix, _trivial => by
      change (1 : Gaussian) ≠ 0
      decide
  | size + 1, matrix, trivial => by
      rcases exists_nonzero_entry_of_leftKernelTrivial matrix trivial with
        ⟨rowPivot, columnPivot, pivotNonzero⟩
      let pivoted := pivotMatrix matrix rowPivot columnPivot
      have pivotedTrivial : LeftKernelTrivial pivoted := by
        simpa only [pivoted] using
          leftKernelTrivial_pivotMatrix trivial rowPivot columnPivot
      have headNonzero : RFAP.ConstructiveFiniteMatrix.head pivoted ≠ 0 := by
        simpa only [pivoted, RFAP.ConstructiveFiniteMatrix.head,
          pivotMatrix, swapColumns_apply, swapRows_apply, swapZero_zero] using
          pivotNonzero
      have smallerTrivial : LeftKernelTrivial
          (RFAP.ConstructiveFiniteMatrix.schur pivoted) :=
        leftKernelTrivial_schur_of_head_nonzero pivoted pivotedTrivial
          headNonzero
      have smallerNonzero :
          (completeScaledInverse
            (RFAP.ConstructiveFiniteMatrix.schur pivoted)).scalar ≠ 0 :=
        completeScaledInverse_scalar_nonzero_of_leftKernelTrivial
          (RFAP.ConstructiveFiniteMatrix.schur pivoted) smallerTrivial
      have branchNonzero :
          (completeExactBranch matrix rowPivot columnPivot).scalar ≠ 0 := by
        change RFAP.ConstructiveFiniteMatrix.head pivoted *
            (completeScaledInverse
              (RFAP.ConstructiveFiniteMatrix.schur pivoted)).scalar ≠ 0
        exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
          headNonzero smallerNonzero
      exact completeScaledInverse_scalar_nonzero_of_branch matrix rowPivot
        columnPivot branchNonzero

/-- The smallest matrix rejected by the fixed-pivot recursion is accepted by
the complete construction.  This executable regression is the row-swap
matrix `[[0,1],[1,0]]`. -/
def twoByTwoSwap : Matrix 2 :=
  swapRows (RFAP.ConstructiveFiniteMatrix.identity : Matrix 2) 1

theorem twoByTwoSwap_fixedScalar_zero :
    (RFAP.ConstructiveFiniteMatrix.scaledInverse twoByTwoSwap).scalar = 0 := by
  decide

theorem twoByTwoSwap_completeScalar_nonzero :
    (completeScaledInverse twoByTwoSwap).scalar ≠ 0 := by decide

def completeGeometricBranch {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) :
    ScaledInverseApproximation (size + 1) :=
  geometricPivotBranch matrix rowPivot columnPivot
    (completeApproximation
      (CCL.Riemann.FiniteMatrixApproximation.schur
        (geometricPivotMatrix matrix rowPivot columnPivot)))

def completeGeometricRow {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (rowPivot : Fin (size + 1)) : ScaledInverseApproximation (size + 1) :=
  geometricAggregate (completeGeometricBranch matrix rowPivot)
    (fun columnPivot =>
      geometricConj
        (completeGeometricBranch matrix rowPivot columnPivot).scalar)

theorem completeApproximation_succ {size : Nat}
    (matrix : GeometricMatrix (size + 1)) :
    completeApproximation matrix =
      geometricAggregate (completeGeometricRow matrix)
        (fun rowPivot =>
          geometricConj (completeGeometricRow matrix rowPivot).scalar) := rfl

@[simp] theorem sampleMatrix_geometricSwapRows {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (pivot : Fin (size + 1)) (index : Nat) :
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
        (geometricSwapRows matrix pivot) index =
      swapRows
        (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix matrix index)
          pivot := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  simp only [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply,
    geometricSwapRows_apply, swapRows_apply]

@[simp] theorem sampleMatrix_geometricSwapColumns {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (pivot : Fin (size + 1)) (index : Nat) :
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
        (geometricSwapColumns matrix pivot) index =
      swapColumns
        (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix matrix index)
          pivot := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  simp only [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply,
    geometricSwapColumns_apply, swapColumns_apply]

@[simp] theorem sampleMatrix_geometricPivotMatrix {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) (index : Nat) :
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
        (geometricPivotMatrix matrix rowPivot columnPivot) index =
      pivotMatrix
        (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix matrix index)
          rowPivot columnPivot := by
  unfold geometricPivotMatrix pivotMatrix
  rw [sampleMatrix_geometricSwapColumns,
    sampleMatrix_geometricSwapRows]

@[simp] theorem sampleMatrix_geometricUnpivotInverse {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) (index : Nat) :
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
        (geometricUnpivotInverse matrix rowPivot columnPivot) index =
      swapColumns
        (swapRows
          (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix matrix index)
            columnPivot) rowPivot := by
  unfold geometricUnpivotInverse
  rw [sampleMatrix_geometricSwapColumns,
    sampleMatrix_geometricSwapRows]

@[simp] theorem sampleMatrix_geometricWeightedMatrix {count size : Nat}
    (weights : Fin count → GeometricApproximation)
    (matrices : Fin count → GeometricMatrix size) (index : Nat) :
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
        (geometricWeightedMatrix weights matrices) index =
      weightedMatrix (fun branch => (weights branch).sample index)
        (fun branch =>
          CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
            (matrices branch) index) := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply,
    geometricWeightedMatrix_apply, weightedMatrix_apply,
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sum_sample]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro branch
  rw [CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul_sample,
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply]

@[simp] theorem geometricAggregate_scalar_sample {count size : Nat}
    (branches : Fin count → ScaledInverseApproximation size)
    (weights : Fin count → GeometricApproximation) (index : Nat) :
    (geometricAggregate branches weights).scalar.sample index =
      RFAP.ConstructiveFiniteMatrix.sumFin fun branch =>
        (weights branch).sample index * (branches branch).scalar.sample index := by
  unfold geometricAggregate
  rw [CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sum_sample]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro branch
  rw [CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul_sample]

@[simp] theorem geometricAggregate_inverse_sample {count size : Nat}
    (branches : Fin count → ScaledInverseApproximation size)
    (weights : Fin count → GeometricApproximation) (index : Nat) :
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
        (geometricAggregate branches weights).inverse index =
      weightedMatrix (fun branch => (weights branch).sample index)
        (fun branch =>
          CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
            (branches branch).inverse index) := by
  unfold geometricAggregate
  exact sampleMatrix_geometricWeightedMatrix weights
    (fun branch => (branches branch).inverse) index

theorem geometricAggregate_sample {count size : Nat}
    {matrix : Matrix size}
    (geometricBranches : Fin count → ScaledInverseApproximation size)
    (exactBranches : Fin count → ScaledInverse matrix)
    (geometricWeights : Fin count → GeometricApproximation)
    (exactWeights : Fin count → Gaussian) (index : Nat)
    (scalarSamples : forall branch,
      (geometricBranches branch).scalar.sample index =
        (exactBranches branch).scalar)
    (inverseSamples : forall branch,
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
          (geometricBranches branch).inverse index =
        (exactBranches branch).inverse)
    (weightSamples : forall branch,
      (geometricWeights branch).sample index = exactWeights branch) :
    (geometricAggregate geometricBranches geometricWeights).scalar.sample index =
        (aggregateScaledInverse exactBranches exactWeights).scalar ∧
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
          (geometricAggregate geometricBranches geometricWeights).inverse index =
        (aggregateScaledInverse exactBranches exactWeights).inverse := by
  constructor
  · rw [geometricAggregate_scalar_sample,
      aggregateScaledInverse_scalar]
    apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
    intro branch
    rw [weightSamples branch, scalarSamples branch]
  · rw [geometricAggregate_inverse_sample]
    apply RFAP.ConstructiveFiniteMatrix.matrix_ext
    intro row column
    change
      weightedMatrix
          (fun branch => (geometricWeights branch).sample index)
          (fun branch =>
            CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
              (geometricBranches branch).inverse index) row column =
        weightedMatrix exactWeights
          (fun branch => (exactBranches branch).inverse) row column
    rw [weightedMatrix_apply, weightedMatrix_apply]
    apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
    intro branch
    rw [weightSamples branch]
    have entrySample := RFAP.ConstructiveFiniteMatrix.matrix_eq_at
      (inverseSamples branch) row column
    rw [entrySample]

/-! The raw block formula is separated from its identity proofs so sampling
can be checked entrywise without transporting a dependent proof object across
matrix extensional equality. -/

def rawBlockInverse {size : Nat} (matrix : Matrix (size + 1))
    (scalar : Gaussian) (inverse : Matrix size) : Matrix (size + 1) :=
  let a := RFAP.ConstructiveFiniteMatrix.head matrix
  let row := RFAP.ConstructiveFiniteMatrix.topRow matrix
  let column := RFAP.ConstructiveFiniteMatrix.leftColumn matrix
  let inverseColumn :=
    RFAP.ConstructiveFiniteMatrix.matrixVector inverse column
  let rowInverse := RFAP.ConstructiveFiniteMatrix.vectorMatrix row inverse
  let corner := scalar +
    RFAP.ConstructiveFiniteMatrix.dot row inverseColumn
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun i j => i.cases
    (j.cases corner (fun columnIndex => -a * rowInverse columnIndex))
    (fun rowIndex => j.cases
      (-a * inverseColumn rowIndex)
      (fun columnIndex => (a * a) * inverse rowIndex columnIndex))

@[simp] theorem rawBlockInverse_apply {size : Nat}
    (matrix : Matrix (size + 1)) (scalar : Gaussian)
    (inverse : Matrix size) (row column : Fin (size + 1)) :
    rawBlockInverse matrix scalar inverse row column =
      row.cases
        (column.cases
          (scalar + RFAP.ConstructiveFiniteMatrix.dot
            (RFAP.ConstructiveFiniteMatrix.topRow matrix)
            (RFAP.ConstructiveFiniteMatrix.matrixVector inverse
              (RFAP.ConstructiveFiniteMatrix.leftColumn matrix)))
          (fun columnIndex =>
            -RFAP.ConstructiveFiniteMatrix.head matrix *
              RFAP.ConstructiveFiniteMatrix.vectorMatrix
                (RFAP.ConstructiveFiniteMatrix.topRow matrix) inverse
                  columnIndex))
        (fun rowIndex => column.cases
          (-RFAP.ConstructiveFiniteMatrix.head matrix *
            RFAP.ConstructiveFiniteMatrix.matrixVector inverse
              (RFAP.ConstructiveFiniteMatrix.leftColumn matrix) rowIndex)
          (fun columnIndex =>
            (RFAP.ConstructiveFiniteMatrix.head matrix *
              RFAP.ConstructiveFiniteMatrix.head matrix) *
                inverse rowIndex columnIndex)) := by
  unfold rawBlockInverse
  rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]

@[simp] theorem rawBlockInverse_eq_blockInverse {size : Nat}
    (matrix : Matrix (size + 1))
    (smaller : ScaledInverse (RFAP.ConstructiveFiniteMatrix.schur matrix)) :
    rawBlockInverse matrix smaller.scalar smaller.inverse =
      RFAP.ConstructiveFiniteMatrix.blockInverse matrix smaller := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  refine Fin.cases ?_ (fun rowIndex => ?_) row
  · refine Fin.cases ?_ (fun columnIndex => ?_) column
    · rw [rawBlockInverse_apply,
        RFAP.ConstructiveFiniteMatrix.blockInverse_apply]
      repeat' rw [Fin.cases_zero]
    · rw [rawBlockInverse_apply,
        RFAP.ConstructiveFiniteMatrix.blockInverse_apply]
      repeat' rw [Fin.cases_zero]
  · refine Fin.cases ?_ (fun columnIndex => ?_) column
    · rw [rawBlockInverse_apply,
        RFAP.ConstructiveFiniteMatrix.blockInverse_apply]
      repeat' rw [Fin.cases_succ]
      repeat' rw [Fin.cases_zero]
    · rw [rawBlockInverse_apply,
        RFAP.ConstructiveFiniteMatrix.blockInverse_apply]
      repeat' rw [Fin.cases_succ]
      rw [pow_two]

theorem geometricBlockInverse_sample {size : Nat}
    (geometricMatrix : GeometricMatrix (size + 1))
    (smaller : ScaledInverseApproximation size) (index : Nat)
    (exactMatrix : Matrix (size + 1)) (exactScalar : Gaussian)
    (exactInverse : Matrix size)
    (matrixSample :
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix geometricMatrix index =
        exactMatrix)
    (scalarSample : smaller.scalar.sample index = exactScalar)
    (inverseSample :
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix smaller.inverse index =
        exactInverse) :
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
        (CCL.Riemann.FiniteMatrixApproximation.blockInverse
          geometricMatrix smaller) index =
      rawBlockInverse exactMatrix exactScalar exactInverse := by
  have rowSample :
      CCL.Riemann.FiniteMatrixApproximation.sampleVector
          (fun entry : Fin size => geometricMatrix 0 entry.succ) index =
        RFAP.ConstructiveFiniteMatrix.topRow exactMatrix := by
    apply RFAP.ConstructiveFiniteMatrix.vector_ext
    intro entry
    rw [CCL.Riemann.FiniteMatrixApproximation.sampleVector_apply,
      RFAP.ConstructiveFiniteMatrix.topRow_apply]
    have sampledEntry := RFAP.ConstructiveFiniteMatrix.matrix_eq_at
      matrixSample 0 entry.succ
    rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply]
      at sampledEntry
    exact sampledEntry
  have columnSample :
      CCL.Riemann.FiniteMatrixApproximation.sampleVector
          (fun entry : Fin size => geometricMatrix entry.succ 0) index =
        RFAP.ConstructiveFiniteMatrix.leftColumn exactMatrix := by
    apply RFAP.ConstructiveFiniteMatrix.vector_ext
    intro entry
    rw [CCL.Riemann.FiniteMatrixApproximation.sampleVector_apply,
      RFAP.ConstructiveFiniteMatrix.leftColumn_apply]
    have sampledEntry := RFAP.ConstructiveFiniteMatrix.matrix_eq_at
      matrixSample entry.succ 0
    rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply]
      at sampledEntry
    exact sampledEntry
  have inverseColumnSample :
      CCL.Riemann.FiniteMatrixApproximation.sampleVector
          (CCL.Riemann.FiniteMatrixApproximation.matrixVector smaller.inverse
            (fun entry : Fin size => geometricMatrix entry.succ 0)) index =
        RFAP.ConstructiveFiniteMatrix.matrixVector exactInverse
          (RFAP.ConstructiveFiniteMatrix.leftColumn exactMatrix) := by
    apply RFAP.ConstructiveFiniteMatrix.vector_ext
    intro entry
    rw [CCL.Riemann.FiniteMatrixApproximation.sampleVector_apply,
      CCL.Riemann.FiniteMatrixApproximation.matrixVector_sample,
      inverseSample, columnSample]
  have rowInverseSample :
      CCL.Riemann.FiniteMatrixApproximation.sampleVector
          (CCL.Riemann.FiniteMatrixApproximation.vectorMatrix
            (fun entry : Fin size => geometricMatrix 0 entry.succ)
              smaller.inverse) index =
        RFAP.ConstructiveFiniteMatrix.vectorMatrix
          (RFAP.ConstructiveFiniteMatrix.topRow exactMatrix)
            exactInverse := by
    apply RFAP.ConstructiveFiniteMatrix.vector_ext
    intro entry
    rw [CCL.Riemann.FiniteMatrixApproximation.sampleVector_apply,
      CCL.Riemann.FiniteMatrixApproximation.vectorMatrix_sample,
      inverseSample, rowSample]
  have headSample : (geometricMatrix 0 0).sample index =
      RFAP.ConstructiveFiniteMatrix.head exactMatrix := by
    have sampledEntry := RFAP.ConstructiveFiniteMatrix.matrix_eq_at
      matrixSample 0 0
    rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply]
      at sampledEntry
    exact sampledEntry
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply,
    CCL.Riemann.FiniteMatrixApproximation.blockInverse_apply,
    rawBlockInverse_apply]
  refine Fin.cases ?_ (fun rowIndex => ?_) row
  · refine Fin.cases ?_ (fun columnIndex => ?_) column
    · simp only [Fin.cases_zero,
        CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.add_sample,
        scalarSample,
        CCL.Riemann.FiniteMatrixApproximation.dot_sample,
        rowSample, inverseColumnSample]
    · simp only [Fin.cases_zero, Fin.cases_succ,
        CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul_sample,
        CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.neg_sample,
        headSample]
      have entrySample := RFAP.ConstructiveFiniteMatrix.vector_eq_at
        rowInverseSample columnIndex
      rw [CCL.Riemann.FiniteMatrixApproximation.sampleVector_apply]
        at entrySample
      rw [entrySample]
  · refine Fin.cases ?_ (fun columnIndex => ?_) column
    · simp only [Fin.cases_zero, Fin.cases_succ,
        CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul_sample,
        CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.neg_sample,
        headSample]
      have entrySample := RFAP.ConstructiveFiniteMatrix.vector_eq_at
        inverseColumnSample rowIndex
      rw [CCL.Riemann.FiniteMatrixApproximation.sampleVector_apply]
        at entrySample
      rw [entrySample]
    · simp only [Fin.cases_succ,
        CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul_sample,
        headSample]
      have entrySample := RFAP.ConstructiveFiniteMatrix.matrix_eq_at
        inverseSample rowIndex columnIndex
      rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply]
        at entrySample
      rw [entrySample]

theorem geometricPivotBranch_sample {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (rowPivot columnPivot : Fin (size + 1)) (index : Nat)
    (smaller : ScaledInverseApproximation size)
    (exactSmaller : ScaledInverse
      (RFAP.ConstructiveFiniteMatrix.schur
        (pivotMatrix
          (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix matrix index)
            rowPivot columnPivot)))
    (scalarSample : smaller.scalar.sample index = exactSmaller.scalar)
    (inverseSample :
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix smaller.inverse index =
        exactSmaller.inverse) :
    (geometricPivotBranch matrix rowPivot columnPivot smaller).scalar.sample
          index =
        (pivotBranch
          (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix matrix index)
            rowPivot columnPivot exactSmaller).scalar ∧
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
          (geometricPivotBranch matrix rowPivot columnPivot smaller).inverse
            index =
        (pivotBranch
          (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix matrix index)
            rowPivot columnPivot exactSmaller).inverse := by
  let geometricPivot := geometricPivotMatrix matrix rowPivot columnPivot
  let exactMatrix :=
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix matrix index
  let exactPivot := pivotMatrix exactMatrix rowPivot columnPivot
  have pivotSample :
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix geometricPivot index =
        exactPivot :=
    sampleMatrix_geometricPivotMatrix matrix rowPivot columnPivot index
  have extendedInverseSample :
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
          (CCL.Riemann.FiniteMatrixApproximation.blockInverse
            geometricPivot smaller) index =
        (RFAP.ConstructiveFiniteMatrix.extendScaledInverse
          exactPivot exactSmaller).inverse := by
    calc
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
          (CCL.Riemann.FiniteMatrixApproximation.blockInverse
            geometricPivot smaller) index =
          rawBlockInverse exactPivot exactSmaller.scalar
            exactSmaller.inverse :=
        geometricBlockInverse_sample geometricPivot smaller index exactPivot
          exactSmaller.scalar exactSmaller.inverse pivotSample scalarSample
            inverseSample
      _ = (RFAP.ConstructiveFiniteMatrix.extendScaledInverse
            exactPivot exactSmaller).inverse :=
        rawBlockInverse_eq_blockInverse exactPivot exactSmaller
  constructor
  · change
      (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
        (geometricPivot 0 0) smaller.scalar).sample index =
        (RFAP.ConstructiveFiniteMatrix.extendScaledInverse
          exactPivot exactSmaller).scalar
    rw [CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul_sample]
    have pivotEntry := RFAP.ConstructiveFiniteMatrix.matrix_eq_at
      pivotSample 0 0
    rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply]
      at pivotEntry
    rw [pivotEntry, scalarSample]
    rfl
  · change
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
        (geometricUnpivotInverse
          (CCL.Riemann.FiniteMatrixApproximation.blockInverse
            geometricPivot smaller) rowPivot columnPivot) index = _
    rw [sampleMatrix_geometricUnpivotInverse, extendedInverseSample]
    rfl


/-- Every synchronized finite sample is exactly the pivot-complete scaled
inverse of the source matrix at that same sample index. -/
theorem completeApproximation_sample : forall {size : Nat}
    (matrix : GeometricMatrix size) (index : Nat),
    (completeApproximation matrix).scalar.sample index =
        (completeScaledInverse
          (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix matrix index)).scalar ∧
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
          (completeApproximation matrix).inverse index =
        (completeScaledInverse
          (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix matrix index)).inverse
  | 0, _matrix, _index => by
      constructor
      · rfl
      · rfl
  | size + 1, matrix, index => by
      let exactMatrix :=
        CCL.Riemann.FiniteMatrixApproximation.sampleMatrix matrix index
      have branchSample : forall rowPivot columnPivot,
          (completeGeometricBranch matrix rowPivot columnPivot).scalar.sample
                index =
              (completeExactBranch exactMatrix rowPivot columnPivot).scalar ∧
            CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
                (completeGeometricBranch matrix rowPivot columnPivot).inverse
                  index =
              (completeExactBranch exactMatrix rowPivot columnPivot).inverse := by
        intro rowPivot columnPivot
        let geometricPivot :=
          geometricPivotMatrix matrix rowPivot columnPivot
        have recursive := completeApproximation_sample
          (CCL.Riemann.FiniteMatrixApproximation.schur geometricPivot) index
        have pivotSample := sampleMatrix_geometricPivotMatrix matrix
          rowPivot columnPivot index
        rw [CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_schur,
          pivotSample] at recursive
        exact geometricPivotBranch_sample matrix rowPivot columnPivot index
          (completeApproximation
            (CCL.Riemann.FiniteMatrixApproximation.schur geometricPivot))
          (completeScaledInverse
            (RFAP.ConstructiveFiniteMatrix.schur
              (pivotMatrix exactMatrix rowPivot columnPivot)))
          recursive.1 recursive.2
      have rowSample : forall rowPivot,
          (completeGeometricRow matrix rowPivot).scalar.sample index =
                (completeExactRow exactMatrix rowPivot).scalar ∧
            CCL.Riemann.FiniteMatrixApproximation.sampleMatrix
                (completeGeometricRow matrix rowPivot).inverse index =
              (completeExactRow exactMatrix rowPivot).inverse := by
        intro rowPivot
        apply geometricAggregate_sample
          (completeGeometricBranch matrix rowPivot)
          (completeExactBranch exactMatrix rowPivot)
          (fun columnPivot => geometricConj
            (completeGeometricBranch matrix rowPivot columnPivot).scalar)
          (fun columnPivot => conj
            (completeExactBranch exactMatrix rowPivot columnPivot).scalar)
          index
        · intro columnPivot
          exact (branchSample rowPivot columnPivot).1
        · intro columnPivot
          exact (branchSample rowPivot columnPivot).2
        · intro columnPivot
          rw [geometricConj_sample,
            (branchSample rowPivot columnPivot).1]
      rw [completeApproximation_succ matrix,
        completeScaledInverse_succ exactMatrix]
      exact geometricAggregate_sample
        (completeGeometricRow matrix) (completeExactRow exactMatrix)
        (fun rowPivot =>
          geometricConj (completeGeometricRow matrix rowPivot).scalar)
        (fun rowPivot => conj (completeExactRow exactMatrix rowPivot).scalar)
        index
        (fun rowPivot => (rowSample rowPivot).1)
        (fun rowPivot => (rowSample rowPivot).2)
        (fun rowPivot => by
          rw [geometricConj_sample, (rowSample rowPivot).1])

end CCL.Riemann.PivotedScaledInverse
