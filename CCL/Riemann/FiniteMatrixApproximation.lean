import CCL.Progressive.Sampling
import mathlib.RFAP.ConstructiveFiniteMatrix

/-!
# Synchronized finite matrix approximations

This file provides a small constructive algebra of Gaussian-rational sample
streams whose error allowance is an explicit quarter-power schedule.  Unlike
wrapping an intermediate CCL name and sampling it again, these operations
preserve the same finite sample index through every polynomial operation.

The final construction mirrors the total division-free scaled-inverse
algorithm in `RFAP.ConstructiveFiniteMatrix`.  It therefore produces finite
approximations to the canonical scalar and adjugate of every finite named
matrix without making an invertibility decision or choosing a completed
value.
-/

namespace CCL.Riemann.FiniteMatrixApproximation

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Approximation := CCL.ProgressiveApproximation.Approximation
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev Matrix (value : Type) (size : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Matrix value size
abbrev Vector (value : Type) (size : Nat) := Fin size -> value

open RFAP.ConstructiveGaussian.Gaussian

/-- A finite sample stream with an explicit geometric error scale. -/
structure GeometricApproximation where
  sample : Nat -> Gaussian
  errorScale : Coordinate
  errorScale_nonneg : 0 <= errorScale
  later_close : forall {earlier later : Nat}, earlier <= later ->
    normSq (sample later - sample earlier) <=
      CCL.FiniteGeometric.quarterRadius errorScale earlier
  centerBound : Coordinate
  centerBound_nonneg : 0 <= centerBound
  sample_bounded : forall index, normSq (sample index) <= centerBound

namespace GeometricApproximation

/-- Forget the displayed scale while retaining it as an ordinary productive
finite approximation. -/
def toApproximation (source : GeometricApproximation) : Approximation where
  sample := source.sample
  radiusSq := CCL.FiniteGeometric.quarterRadius source.errorScale
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg source.errorScale_nonneg
  later_close := source.later_close
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow source.errorScale current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge
      source.errorScale current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate
      source.errorScale source.errorScale_nonneg
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := source.sample_bounded

@[simp] theorem toApproximation_sample
    (source : GeometricApproximation) (index : Nat) :
    source.toApproximation.sample index = source.sample index := rfl

/-- The canonical nested sampler of an arbitrary productive CCL name. -/
def ofNamed (name : Named) : GeometricApproximation where
  sample := (CCL.ProgressiveSampling.approximation name).sample
  errorScale := 4
  errorScale_nonneg := by decide
  later_close :=
    (CCL.ProgressiveSampling.approximation name).later_close
  centerBound :=
    (CCL.ProgressiveSampling.approximation name).centerBound
  centerBound_nonneg :=
    (CCL.ProgressiveSampling.approximation name).centerBound_nonneg
  sample_bounded :=
    (CCL.ProgressiveSampling.approximation name).sample_bounded

@[simp] theorem ofNamed_sample (name : Named) (index : Nat) :
    (ofNamed name).sample index =
      (CCL.ProgressiveSampling.approximation name).sample index := rfl

/-- A constant Gaussian rational, with zero movement allowance. -/
def exact (value : Gaussian) : GeometricApproximation where
  sample := fun _ => value
  errorScale := 0
  errorScale_nonneg := le_rfl
  later_close := by
    intro earlier later order
    change normSq (value - value) <=
      CCL.FiniteGeometric.quarterRadius 0 earlier
    rw [sub_self, normSq_zero]
    exact CCL.FiniteGeometric.quarterRadius_nonneg le_rfl earlier
  centerBound := normSq value
  centerBound_nonneg := normSq_nonneg value
  sample_bounded := fun _ => le_rfl

@[simp] theorem exact_sample (value : Gaussian) (index : Nat) :
    (exact value).sample index = value := rfl

/-- Discard a finite prefix of a geometric approximation.  The retained
stream uses the original (conservative) error scale; antitonicity of the
quarter-radius schedule proves the shifted tail bound. -/
def drop (source : GeometricApproximation) (anchor : Nat) :
    GeometricApproximation where
  sample := fun index => source.sample (anchor + index)
  errorScale := source.errorScale
  errorScale_nonneg := source.errorScale_nonneg
  later_close := by
    intro earlier later order
    exact (source.later_close (by omega0)).trans
      (CCL.FiniteGeometric.quarterRadius_antitone
        source.errorScale_nonneg (by omega0))
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := fun index => source.sample_bounded (anchor + index)

@[simp] theorem drop_sample (source : GeometricApproximation)
    (anchor index : Nat) :
    (source.drop anchor).sample index = source.sample (anchor + index) := rfl

@[simp] theorem drop_errorScale (source : GeometricApproximation)
    (anchor : Nat) :
    (source.drop anchor).errorScale = source.errorScale := rfl

/-- Pointwise negation preserves the geometric scale and center bound. -/
def neg (source : GeometricApproximation) : GeometricApproximation where
  sample := fun index => -source.sample index
  errorScale := source.errorScale
  errorScale_nonneg := source.errorScale_nonneg
  later_close := by
    intro earlier later order
    have movement := source.later_close order
    have identity :
        -source.sample later - -source.sample earlier =
          -(source.sample later - source.sample earlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
    rw [identity, normSq_neg]
    exact movement
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [normSq_neg]
    exact source.sample_bounded index

@[simp] theorem neg_sample (source : GeometricApproximation) (index : Nat) :
    (neg source).sample index = -source.sample index := rfl

/-- Equal-index Gaussian conjugation preserves every squared movement and
global sample bound. -/
def conj (source : GeometricApproximation) : GeometricApproximation where
  sample := fun index => source.sample index |>.conj
  errorScale := source.errorScale
  errorScale_nonneg := source.errorScale_nonneg
  later_close := by
    intro earlier later order
    have movement := source.later_close order
    have identity :
        (source.sample later).conj - (source.sample earlier).conj =
          (source.sample later - source.sample earlier).conj := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext
      · rfl
      · change
          -(source.sample later).im - -(source.sample earlier).im =
            -((source.sample later).im - (source.sample earlier).im)
        ring1
    rw [identity, normSq_conj]
    exact movement
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [normSq_conj]
    exact source.sample_bounded index

@[simp] theorem conj_sample (source : GeometricApproximation) (index : Nat) :
    (conj source).sample index = (source.sample index).conj := rfl

/-- Equal-index addition with a conservative rational movement bound. -/
def add (left right : GeometricApproximation) : GeometricApproximation where
  sample := fun index => left.sample index + right.sample index
  errorScale := 2 * (left.errorScale + right.errorScale)
  errorScale_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg left.errorScale_nonneg right.errorScale_nonneg)
  later_close := by
    intro earlier later order
    have leftMovement := left.later_close order
    have rightMovement := right.later_close order
    have identity :
        left.sample later + right.sample later -
            (left.sample earlier + right.sample earlier) =
          (left.sample later - left.sample earlier) +
            (right.sample later - right.sample earlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im] <;> ring1
    rw [identity]
    calc
      normSq
          ((left.sample later - left.sample earlier) +
            (right.sample later - right.sample earlier)) <=
        2 *
          (normSq (left.sample later - left.sample earlier) +
            normSq (right.sample later - right.sample earlier)) :=
        normSq_add_le_two _ _
      _ <= 2 *
          (CCL.FiniteGeometric.quarterRadius left.errorScale earlier +
            CCL.FiniteGeometric.quarterRadius right.errorScale earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add leftMovement rightMovement) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
          (2 * (left.errorScale + right.errorScale)) earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        ring1
  centerBound := 2 * (left.centerBound + right.centerBound)
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg left.centerBound_nonneg right.centerBound_nonneg)
  sample_bounded := by
    intro index
    exact (normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add (left.sample_bounded index)
          (right.sample_bounded index)) (by decide))

@[simp] theorem add_sample (left right : GeometricApproximation)
    (index : Nat) :
    (add left right).sample index =
      left.sample index + right.sample index := rfl

/-- Equal-index subtraction. -/
def sub (left right : GeometricApproximation) : GeometricApproximation :=
  add left (neg right)

@[simp] theorem sub_sample (left right : GeometricApproximation)
    (index : Nat) :
    (sub left right).sample index =
      left.sample index - right.sample index := by
  change left.sample index + -right.sample index = _
  exact (sub_eq_add_neg _ _).symm

/-- Equal-index multiplication.  Both global sample bounds are carried into
the explicit movement scale, so no limit or compactness argument is used. -/
def mul (left right : GeometricApproximation) : GeometricApproximation where
  sample := fun index => left.sample index * right.sample index
  errorScale :=
    2 * (left.errorScale * right.centerBound +
      left.centerBound * right.errorScale)
  errorScale_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          left.errorScale_nonneg right.centerBound_nonneg)
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          left.centerBound_nonneg right.errorScale_nonneg))
  later_close := by
    intro earlier later order
    have leftMovement := left.later_close order
    have rightMovement := right.later_close order
    have firstTerm :
        normSq
            ((left.sample later - left.sample earlier) *
              right.sample later) <=
          CCL.FiniteGeometric.quarterRadius left.errorScale earlier *
            right.centerBound := by
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct leftMovement
        (right.sample_bounded later) (normSq_nonneg _)
        (CCL.FiniteGeometric.quarterRadius_nonneg
          left.errorScale_nonneg earlier)
    have secondTerm :
        normSq
            (left.sample earlier *
              (right.sample later - right.sample earlier)) <=
          left.centerBound *
            CCL.FiniteGeometric.quarterRadius right.errorScale earlier := by
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct
        (left.sample_bounded earlier) rightMovement (normSq_nonneg _)
        left.centerBound_nonneg
    have identity :
        left.sample later * right.sample later -
            left.sample earlier * right.sample earlier =
          (left.sample later - left.sample earlier) * right.sample later +
            left.sample earlier *
              (right.sample later - right.sample earlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1
    rw [identity]
    calc
      normSq
          ((left.sample later - left.sample earlier) * right.sample later +
            left.sample earlier *
              (right.sample later - right.sample earlier)) <=
        2 *
          (normSq
              ((left.sample later - left.sample earlier) *
                right.sample later) +
            normSq
              (left.sample earlier *
                (right.sample later - right.sample earlier))) :=
        normSq_add_le_two _ _
      _ <= 2 *
          (CCL.FiniteGeometric.quarterRadius left.errorScale earlier *
              right.centerBound +
            left.centerBound *
              CCL.FiniteGeometric.quarterRadius right.errorScale earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTerm secondTerm) (by decide)
      _ = CCL.FiniteGeometric.quarterRadius
          (2 * (left.errorScale * right.centerBound +
            left.centerBound * right.errorScale)) earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        ring1
  centerBound := left.centerBound * right.centerBound
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      left.centerBound_nonneg right.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [normSq_mul]
    exact RFAP.ConstructiveFraction.mul_le_mul_direct
      (left.sample_bounded index) (right.sample_bounded index)
      (normSq_nonneg _) left.centerBound_nonneg

@[simp] theorem mul_sample (left right : GeometricApproximation)
    (index : Nat) :
    (mul left right).sample index =
      left.sample index * right.sample index := rfl

/-- A finite recursive sum retaining one common sample index. -/
def sum : {count : Nat} ->
    (Fin count -> GeometricApproximation) -> GeometricApproximation
  | 0, _ => exact 0
  | count + 1, values =>
      add (values 0) (sum fun index : Fin count => values index.succ)

@[simp] theorem sum_sample {count : Nat}
    (values : Fin count -> GeometricApproximation) (index : Nat) :
    (sum values).sample index =
      RFAP.ConstructiveFiniteMatrix.sumFin
        (fun entry => (values entry).sample index) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      change (values 0).sample index +
          (sum (fun entry : Fin count => values entry.succ)).sample index = _
      rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ,
        inductionHypothesis (fun entry : Fin count => values entry.succ)]

end GeometricApproximation

abbrev GeometricMatrix (size : Nat) := Matrix GeometricApproximation size

/-- Evaluate every entry of a synchronized matrix at one finite index. -/
def sampleMatrix {size : Nat} (matrix : GeometricMatrix size)
    (index : Nat) : Matrix Gaussian size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    (matrix row column).sample index

@[simp] theorem sampleMatrix_apply {size : Nat}
    (matrix : GeometricMatrix size) (index : Nat) (row column : Fin size) :
    sampleMatrix matrix index row column =
      (matrix row column).sample index :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- The division-free Schur matrix, computed in synchronized approximation
arithmetic. -/
def schur {size : Nat} (matrix : GeometricMatrix (size + 1)) :
    GeometricMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    GeometricApproximation.sub
      (GeometricApproximation.mul (matrix 0 0)
        (matrix row.succ column.succ))
      (GeometricApproximation.mul (matrix row.succ 0)
        (matrix 0 column.succ))

@[simp] theorem schur_apply {size : Nat}
    (matrix : GeometricMatrix (size + 1)) (row column : Fin size) :
    schur matrix row column =
      GeometricApproximation.sub
        (GeometricApproximation.mul (matrix 0 0)
          (matrix row.succ column.succ))
        (GeometricApproximation.mul (matrix row.succ 0)
          (matrix 0 column.succ)) :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

theorem sampleMatrix_schur {size : Nat}
    (matrix : GeometricMatrix (size + 1)) (index : Nat) :
    sampleMatrix (schur matrix) index =
      RFAP.ConstructiveFiniteMatrix.schur (sampleMatrix matrix index) := by
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  rw [sampleMatrix_apply, schur_apply,
    RFAP.ConstructiveFiniteMatrix.schur_apply]
  simp only [GeometricApproximation.sub_sample,
    GeometricApproximation.mul_sample,
    RFAP.ConstructiveFiniteMatrix.head,
    RFAP.ConstructiveFiniteMatrix.tail_apply,
    RFAP.ConstructiveFiniteMatrix.leftColumn_apply,
    RFAP.ConstructiveFiniteMatrix.topRow_apply, sampleMatrix_apply]

/-- Matrix-vector multiplication in synchronized approximation arithmetic. -/
def matrixVector {size : Nat} (matrix : GeometricMatrix size)
    (vector : Vector GeometricApproximation size) :
    Vector GeometricApproximation size := fun row =>
  GeometricApproximation.sum fun column =>
    GeometricApproximation.mul (matrix row column) (vector column)

/-- Vector-matrix multiplication in synchronized approximation arithmetic. -/
def vectorMatrix {size : Nat} (vector : Vector GeometricApproximation size)
    (matrix : GeometricMatrix size) : Vector GeometricApproximation size :=
  fun column => GeometricApproximation.sum fun row =>
    GeometricApproximation.mul (vector row) (matrix row column)

/-- Dot product in synchronized approximation arithmetic. -/
def dot {size : Nat} (left right : Vector GeometricApproximation size) :
    GeometricApproximation :=
  GeometricApproximation.sum fun index =>
    GeometricApproximation.mul (left index) (right index)

/-- Evaluate a synchronized vector at one finite index. -/
def sampleVector {size : Nat} (vector : Vector GeometricApproximation size)
    (index : Nat) : RFAP.ConstructiveFiniteMatrix.Vector Gaussian size :=
  RFAP.ConstructiveFiniteMatrix.vectorOfFn fun entry =>
    (vector entry).sample index

@[simp] theorem sampleVector_apply {size : Nat}
    (vector : Vector GeometricApproximation size) (index : Nat)
    (entry : Fin size) :
    sampleVector vector index entry = (vector entry).sample index :=
  RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply _ _

@[simp] theorem matrixVector_sample {size : Nat}
    (matrix : GeometricMatrix size)
    (vector : Vector GeometricApproximation size) (index : Nat)
    (row : Fin size) :
    (matrixVector matrix vector row).sample index =
      RFAP.ConstructiveFiniteMatrix.matrixVector
        (sampleMatrix matrix index) (sampleVector vector index) row := by
  rw [RFAP.ConstructiveFiniteMatrix.matrixVector_apply]
  unfold matrixVector
  rw [GeometricApproximation.sum_sample]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro column
  simp only [GeometricApproximation.mul_sample, sampleMatrix_apply,
    sampleVector_apply]

@[simp] theorem vectorMatrix_sample {size : Nat}
    (vector : Vector GeometricApproximation size)
    (matrix : GeometricMatrix size) (index : Nat)
    (column : Fin size) :
    (vectorMatrix vector matrix column).sample index =
      RFAP.ConstructiveFiniteMatrix.vectorMatrix
        (sampleVector vector index) (sampleMatrix matrix index) column := by
  rw [RFAP.ConstructiveFiniteMatrix.vectorMatrix_apply]
  unfold vectorMatrix
  rw [GeometricApproximation.sum_sample]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro row
  simp only [GeometricApproximation.mul_sample, sampleMatrix_apply,
    sampleVector_apply]

@[simp] theorem dot_sample {size : Nat}
    (left right : Vector GeometricApproximation size) (index : Nat) :
    (dot left right).sample index =
      RFAP.ConstructiveFiniteMatrix.dot
        (sampleVector left index) (sampleVector right index) := by
  unfold dot RFAP.ConstructiveFiniteMatrix.dot
  rw [GeometricApproximation.sum_sample]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro entry
  simp only [GeometricApproximation.mul_sample, sampleVector_apply]

/-- The data portion of a fraction-free inverse; no invertibility or completed
matrix is asserted. -/
structure ScaledInverseApproximation (size : Nat) where
  scalar : GeometricApproximation
  inverse : GeometricMatrix size

/-- Division-free block extension mirroring the finite Gaussian algorithm. -/
def blockInverse {size : Nat} (matrix : GeometricMatrix (size + 1))
    (smaller : ScaledInverseApproximation size) :
    GeometricMatrix (size + 1) :=
  let a := matrix 0 0
  let row : Vector GeometricApproximation size := fun column =>
    matrix 0 column.succ
  let column : Vector GeometricApproximation size := fun row =>
    matrix row.succ 0
  let inverseColumn := matrixVector smaller.inverse column
  let rowInverse := vectorMatrix row smaller.inverse
  let corner := GeometricApproximation.add smaller.scalar
    (dot row inverseColumn)
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun i j => i.cases
    (j.cases corner (fun columnIndex =>
      GeometricApproximation.mul (GeometricApproximation.neg a)
        (rowInverse columnIndex)))
    (fun rowIndex => j.cases
      (GeometricApproximation.mul (GeometricApproximation.neg a)
        (inverseColumn rowIndex))
      (fun columnIndex =>
        GeometricApproximation.mul
          (GeometricApproximation.mul a a)
          (smaller.inverse rowIndex columnIndex)))

@[simp] theorem blockInverse_apply {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (smaller : ScaledInverseApproximation size)
    (row column : Fin (size + 1)) :
    blockInverse matrix smaller row column =
      row.cases
        (column.cases
          (GeometricApproximation.add smaller.scalar
            (dot (fun entry => matrix 0 entry.succ)
              (matrixVector smaller.inverse
                (fun entry => matrix entry.succ 0))))
          (fun columnIndex =>
            GeometricApproximation.mul
              (GeometricApproximation.neg (matrix 0 0))
              (vectorMatrix (fun entry => matrix 0 entry.succ)
                smaller.inverse columnIndex)))
        (fun rowIndex => column.cases
          (GeometricApproximation.mul
            (GeometricApproximation.neg (matrix 0 0))
            (matrixVector smaller.inverse
              (fun entry => matrix entry.succ 0) rowIndex))
          (fun columnIndex =>
            GeometricApproximation.mul
              (GeometricApproximation.mul (matrix 0 0) (matrix 0 0))
              (smaller.inverse rowIndex columnIndex))) := by
  unfold blockInverse
  rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]

theorem sampleMatrix_blockInverse {size : Nat}
    (matrix : GeometricMatrix (size + 1))
    (smaller : ScaledInverseApproximation size) (index : Nat)
    (exactSmaller : RFAP.ConstructiveFiniteMatrix.ScaledInverse
      (RFAP.ConstructiveFiniteMatrix.schur (sampleMatrix matrix index)))
    (scalarSample : smaller.scalar.sample index = exactSmaller.scalar)
    (inverseSample : forall row column,
      (smaller.inverse row column).sample index =
        exactSmaller.inverse row column) :
    sampleMatrix (blockInverse matrix smaller) index =
      RFAP.ConstructiveFiniteMatrix.blockInverse
        (sampleMatrix matrix index) exactSmaller := by
  have inverseMatrixSample :
      sampleMatrix smaller.inverse index = exactSmaller.inverse := by
    apply RFAP.ConstructiveFiniteMatrix.matrix_ext
    intro row column
    rw [sampleMatrix_apply, inverseSample]
  have rowSample :
      sampleVector (fun entry : Fin size => matrix 0 entry.succ) index =
        RFAP.ConstructiveFiniteMatrix.topRow
          (sampleMatrix matrix index) := by
    apply RFAP.ConstructiveFiniteMatrix.vector_ext
    intro entry
    rw [sampleVector_apply,
      RFAP.ConstructiveFiniteMatrix.topRow_apply, sampleMatrix_apply]
  have columnSample :
      sampleVector (fun entry : Fin size => matrix entry.succ 0) index =
        RFAP.ConstructiveFiniteMatrix.leftColumn
          (sampleMatrix matrix index) := by
    apply RFAP.ConstructiveFiniteMatrix.vector_ext
    intro entry
    rw [sampleVector_apply,
      RFAP.ConstructiveFiniteMatrix.leftColumn_apply, sampleMatrix_apply]
  have inverseColumnSample :
      sampleVector
          (matrixVector smaller.inverse
            (fun entry : Fin size => matrix entry.succ 0)) index =
        RFAP.ConstructiveFiniteMatrix.matrixVector exactSmaller.inverse
          (RFAP.ConstructiveFiniteMatrix.leftColumn
            (sampleMatrix matrix index)) := by
    apply RFAP.ConstructiveFiniteMatrix.vector_ext
    intro entry
    rw [sampleVector_apply, matrixVector_sample,
      inverseMatrixSample, columnSample]
  have rowInverseSample :
      sampleVector
          (vectorMatrix (fun entry : Fin size => matrix 0 entry.succ)
            smaller.inverse) index =
        RFAP.ConstructiveFiniteMatrix.vectorMatrix
          (RFAP.ConstructiveFiniteMatrix.topRow
            (sampleMatrix matrix index)) exactSmaller.inverse := by
    apply RFAP.ConstructiveFiniteMatrix.vector_ext
    intro entry
    rw [sampleVector_apply, vectorMatrix_sample,
      inverseMatrixSample, rowSample]
  apply RFAP.ConstructiveFiniteMatrix.matrix_ext
  intro row column
  refine Fin.cases ?_ (fun rowIndex => ?_) row
  · refine Fin.cases ?_ (fun columnIndex => ?_) column
    · rw [sampleMatrix_apply, blockInverse_apply,
        RFAP.ConstructiveFiniteMatrix.blockInverse_apply]
      repeat' rw [Fin.cases_zero]
      rw [GeometricApproximation.add_sample, scalarSample, dot_sample,
        rowSample, inverseColumnSample]
    · rw [sampleMatrix_apply, blockInverse_apply,
        RFAP.ConstructiveFiniteMatrix.blockInverse_apply]
      repeat' rw [Fin.cases_zero]
      repeat' rw [Fin.cases_succ]
      repeat' rw [GeometricApproximation.mul_sample]
      rw [GeometricApproximation.neg_sample,
        RFAP.ConstructiveFiniteMatrix.head, sampleMatrix_apply]
      have entrySample := RFAP.ConstructiveFiniteMatrix.vector_eq_at
        rowInverseSample columnIndex
      rw [sampleVector_apply] at entrySample
      rw [entrySample]
  · refine Fin.cases ?_ (fun columnIndex => ?_) column
    · rw [sampleMatrix_apply, blockInverse_apply,
        RFAP.ConstructiveFiniteMatrix.blockInverse_apply]
      repeat' rw [Fin.cases_succ]
      repeat' rw [Fin.cases_zero]
      repeat' rw [GeometricApproximation.mul_sample]
      rw [GeometricApproximation.neg_sample,
        RFAP.ConstructiveFiniteMatrix.head, sampleMatrix_apply]
      have entrySample := RFAP.ConstructiveFiniteMatrix.vector_eq_at
        inverseColumnSample rowIndex
      rw [sampleVector_apply] at entrySample
      rw [entrySample]
    · rw [sampleMatrix_apply, blockInverse_apply,
        RFAP.ConstructiveFiniteMatrix.blockInverse_apply]
      repeat' rw [Fin.cases_succ]
      repeat' rw [GeometricApproximation.mul_sample]
      rw [RFAP.ConstructiveFiniteMatrix.head, sampleMatrix_apply,
        inverseSample, pow_two]

/-- Total recursive construction of the synchronized fraction-free inverse. -/
def scaledInverse : {size : Nat} -> GeometricMatrix size ->
    ScaledInverseApproximation size
  | 0, _ =>
      { scalar := GeometricApproximation.exact 1
        inverse := RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row =>
          Fin.elim0 row }
  | _size + 1, matrix =>
      let smaller := scaledInverse (schur matrix)
      { scalar := GeometricApproximation.mul (matrix 0 0) smaller.scalar
        inverse := blockInverse matrix smaller }

/-- At every finite index, the synchronized construction is exactly the
canonical Gaussian-rational scaled inverse of the source matrix displayed at
that same index. -/
theorem scaledInverse_sample : forall {size : Nat}
    (matrix : GeometricMatrix size) (index : Nat),
    ((scaledInverse matrix).scalar.sample index =
        (RFAP.ConstructiveFiniteMatrix.scaledInverse
          (sampleMatrix matrix index)).scalar) ∧
      sampleMatrix (scaledInverse matrix).inverse index =
        (RFAP.ConstructiveFiniteMatrix.scaledInverse
          (sampleMatrix matrix index)).inverse
  | 0, matrix, index => by
      constructor
      · rfl
      · apply RFAP.ConstructiveFiniteMatrix.matrix_ext
        intro row
        exact Fin.elim0 row
  | size + 1, matrix, index => by
      let smaller := scaledInverse (schur matrix)
      let exactSmaller := RFAP.ConstructiveFiniteMatrix.scaledInverse
        (RFAP.ConstructiveFiniteMatrix.schur (sampleMatrix matrix index))
      have smallerSample := scaledInverse_sample (schur matrix) index
      rw [sampleMatrix_schur] at smallerSample
      constructor
      · change
          (GeometricApproximation.mul
              (matrix 0 0) smaller.scalar).sample index =
            (RFAP.ConstructiveFiniteMatrix.extendScaledInverse
              (sampleMatrix matrix index) exactSmaller).scalar
        rw [GeometricApproximation.mul_sample]
        change (matrix 0 0).sample index * smaller.scalar.sample index =
          RFAP.ConstructiveFiniteMatrix.head
              (sampleMatrix matrix index) * exactSmaller.scalar
        rw [smallerSample.1]
        rfl
      · change sampleMatrix (blockInverse matrix smaller) index =
          (RFAP.ConstructiveFiniteMatrix.extendScaledInverse
            (sampleMatrix matrix index) exactSmaller).inverse
        change sampleMatrix (blockInverse matrix smaller) index =
          RFAP.ConstructiveFiniteMatrix.blockInverse
            (sampleMatrix matrix index) exactSmaller
        apply sampleMatrix_blockInverse matrix smaller index exactSmaller
          smallerSample.1
        intro row column
        simpa only [sampleMatrix_apply, smaller, exactSmaller] using
          RFAP.ConstructiveFiniteMatrix.matrix_eq_at
            smallerSample.2 row column

theorem scaledInverse_scalar_sample {size : Nat}
    (matrix : GeometricMatrix size) (index : Nat) :
    (scaledInverse matrix).scalar.sample index =
      (RFAP.ConstructiveFiniteMatrix.scaledInverse
        (sampleMatrix matrix index)).scalar :=
  (scaledInverse_sample matrix index).1

theorem scaledInverse_inverse_sample {size : Nat}
    (matrix : GeometricMatrix size) (index : Nat) (row column : Fin size) :
    ((scaledInverse matrix).inverse row column).sample index =
      (RFAP.ConstructiveFiniteMatrix.scaledInverse
        (sampleMatrix matrix index)).inverse row column :=
  by
    simpa only [sampleMatrix_apply] using
      RFAP.ConstructiveFiniteMatrix.matrix_eq_at
        (scaledInverse_sample matrix index).2 row column

end CCL.Riemann.FiniteMatrixApproximation
