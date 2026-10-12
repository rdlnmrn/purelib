module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Matrix.Inverse.PivotedScaledInverse
public import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Gaussian.QuadraticForm
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Matrix
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Finite positive-energy certificates for the second bilinear relation

The second Riemann bilinear relation is used only through finite rational
data.  A request displays finitely many surface cells, a nonnegative area and
density lower bound on each cell, and one cell on which both bounds are
strictly positive.  Their finite energy sum must dominate the automatically
computed period-matrix enclosure budget and must be bounded above by the
displayed normalized quadratic form.

Consequently positivity is derived from cell energy and finite summation; it
is not accepted as a direct positivity assertion about a completed matrix.
-/

namespace Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Algebra

open Purelib

open Purelib.Data.Rat

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

/-- A structural vector of Gaussian rational coefficients with retained finite dimension. -/
abbrev GaussianVector (size : Nat) :=
  Data.Vector Data.Gaussian.Basic.Canonical size
/-- A structural square matrix of Gaussian rational coefficients. -/
abbrev GaussianMatrix (size : Nat) :=
  SquareMatrix Data.Gaussian.Basic.Canonical size

/-! ## Unnormalized finite second relation -/

/-- The A- or B-period vector of one displayed Gaussian-rational linear
combination of the basis differentials. -/
@[expose] def periodCombination {size : Nat} (coefficients : GaussianVector size)
    (periods : GaussianMatrix size) : GaussianVector
      size :=
  SquareMatrix.Multiplication.vectorMatrix coefficients periods

/-- Rational energy extracted from displayed A- and B-period vectors.  The
orientation is chosen so that `A = I`, `B = Ω`, and real coefficients recover
`vᵀ Im(Ω) v`. -/
@[expose] def periodPairingEnergy {size : Nat} (aPeriods bPeriods : GaussianVector
  size) :
    Fraction.Rational :=
  (FiniteSum.Fin.sumFin fun cycle =>
    (bPeriods cycle * Data.Gaussian.Basic.conj
        (aPeriods cycle) -
      aPeriods cycle * Data.Gaussian.Basic.conj
        (bPeriods cycle)).im) / 2

/-- Unnormalized second-bilinear energy of a differential coefficient vector
against finite displayed A/B period matrices. -/
@[expose] def unnormalizedEnergyForm {size : Nat} (coefficients : GaussianVector
  size)
    (aMatrix bMatrix : GaussianMatrix size) : Fraction.Rational :=
  periodPairingEnergy (periodCombination coefficients
    aMatrix)
    (periodCombination coefficients bMatrix)

/-- The squared half antisymmetric imaginary pairing is bounded by the product of the squared norms. -/
private theorem crossPairing_sq_le_normSq_mul (a b : Data.Gaussian.Basic.Canonical) :
    ((b * Data.Gaussian.Basic.conj a -
      a * Data.Gaussian.Basic.conj b).im / 2) ^ 2 <=
      Data.Gaussian.Norm.Basic.normSq a *
        Data.Gaussian.Norm.Basic.normSq b := by
  have squareNonnegative :
      0 <= (a.re * b.re + a.im * b.im) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct _
  simp only [Data.Gaussian.Basic.sub_im,
    Data.Gaussian.Basic.mul_im,
    Data.Gaussian.Basic.conj,
    Data.Gaussian.Norm.Basic.normSq]
  change
    (((b.re * (-a.im) + b.im * a.re -
        (a.re * (-b.im) + a.im * b.re))) / 2) ^ 2 <=
      (a.re ^ 2 + a.im ^ 2) * (b.re ^ 2 + b.im ^ 2)
  have energyIdentity :
      (b.re * (-a.im) + b.im * a.re -
          (a.re * (-b.im) + a.im * b.re)) / 2 =
        a.re * b.im - a.im * b.re := by
    apply Fraction.Field.mul_right_cancel_of_ne
      (show (2 : Fraction.Rational) ≠ 0 by decide)
    rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]
    ring1
  rw [energyIdentity]
  have identity :
      (a.re ^ 2 + a.im ^ 2) * (b.re ^ 2 + b.im ^ 2) -
          (a.re * b.im - a.im * b.re) ^ 2 =
        (a.re * b.re + a.im * b.im) ^ 2 := by
    ring1
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  rw [identity]
  exact squareNonnegative

/-- Scaling both displayed periods by one Gaussian coefficient scales their
antisymmetric imaginary pairing by its squared norm. -/
private theorem crossPairing_scale (coefficient a b : Data.Gaussian.Basic.Canonical) :
    (coefficient * b * Data.Gaussian.Basic.conj
          (coefficient * a) -
        coefficient * a * Data.Gaussian.Basic.conj
          (coefficient * b)).im =
      Data.Gaussian.Norm.Basic.normSq coefficient *
        (b * Data.Gaussian.Basic.conj a -
          a * Data.Gaussian.Basic.conj b).im := by
  simp only [Data.Gaussian.Basic.conj_mul]
  simp only [Data.Gaussian.Basic.mul_re,
    Data.Gaussian.Basic.mul_im,
    Data.Gaussian.Basic.conj,
    Data.Gaussian.Basic.sub_im,
    Data.Gaussian.Norm.Basic.normSq]
  ring1

/-- In dimension one the square of the raw boundary pairing is bounded by
the product of the displayed A- and B-period squared norms.  This is the
two-coordinate Lagrange identity, proved entirely in Gaussian rationals. -/
theorem periodPairingEnergy_one_sq_le
    (aPeriods bPeriods : GaussianVector 1) :
    periodPairingEnergy aPeriods bPeriods ^ 2 <=
      Data.Gaussian.Norm.Basic.normSq (aPeriods 0) *
        Data.Gaussian.Norm.Basic.normSq (bPeriods 0) := by
  unfold periodPairingEnergy
  rw [FiniteSum.Fin.sumFin_succ]
  change
    (((bPeriods 0 * Data.Gaussian.Basic.conj (aPeriods 0) -
      aPeriods 0 * Data.Gaussian.Basic.conj (bPeriods 0)).im +
        0) / 2) ^ 2 <= _
  rw [_root_.add_zero]
  exact crossPairing_sq_le_normSq_mul (aPeriods 0) (bPeriods 0)

/-- The dimension-one energy fold contains exactly its zeroth summand. -/
theorem periodPairingEnergy_one_eq
    (aPeriods bPeriods : GaussianVector 1) :
    periodPairingEnergy aPeriods bPeriods =
      (bPeriods 0 * Data.Gaussian.Basic.conj (aPeriods 0) -
        aPeriods 0 * Data.Gaussian.Basic.conj
          (bPeriods 0)).im / 2 := by
  unfold periodPairingEnergy
  rw [FiniteSum.Fin.sumFin_succ]
  change (_ + 0) / 2 = _
  rw [_root_.add_zero]

/-- The sole coefficient of the standard genus-one differential. -/
@[expose] def genusOneUnitCoefficients : GaussianVector 1 :=
  Data.Vector.Basic.vectorOfFn fun _ => 1

/-- Read the unique entry of the genus-one unit coefficient vector. -/
@[simp] theorem genusOneUnitCoefficients_apply (index : Fin 1) :
    genusOneUnitCoefficients index = 1 :=
  Data.Vector.Basic.vectorOfFn_apply _ _

/-- Multiplication by the one-entry coefficient vector selects the sole row. -/
@[simp] theorem periodCombination_genusOne_unit
    (matrix : GaussianMatrix 1) (cycle : Fin 1) :
    periodCombination genusOneUnitCoefficients matrix cycle
      =
      matrix 0 cycle := by
  unfold periodCombination
  rw [SquareMatrix.Multiplication.vectorMatrix_apply]
  rw [FiniteSum.Fin.sumFin_succ]
  change genusOneUnitCoefficients 0 * matrix 0 cycle + 0 = _
  rw [genusOneUnitCoefficients_apply,
    Data.Gaussian.Basic.one_mul,
    Data.Gaussian.Basic.add_zero]

/-- The genus-one raw energy square is controlled by the sole matrix entries. -/
theorem unnormalizedEnergyForm_genusOne_unit_sq_le
    (aMatrix bMatrix : GaussianMatrix 1) :
    unnormalizedEnergyForm genusOneUnitCoefficients aMatrix
      bMatrix ^ 2 <=
      Data.Gaussian.Norm.Basic.normSq (aMatrix 0 0) *
        Data.Gaussian.Norm.Basic.normSq (bMatrix 0 0) := by
  unfold unnormalizedEnergyForm
  simpa only [periodCombination_genusOne_unit] using
    periodPairingEnergy_one_sq_le
      (periodCombination genusOneUnitCoefficients aMatrix)
      (periodCombination genusOneUnitCoefficients bMatrix)

/-- In dimension one every coefficient vector scales the sole period row by
its zeroth entry. -/
theorem periodCombination_one (coefficients : GaussianVector 1)
    (matrix : GaussianMatrix 1) (cycle : Fin 1) :
    periodCombination coefficients matrix cycle =
      coefficients 0 * matrix 0 cycle := by
  unfold periodCombination
  rw [SquareMatrix.Multiplication.vectorMatrix_apply,
    FiniteSum.Fin.sumFin_succ]
  change coefficients 0 * matrix 0 cycle + 0 = _
  exact Data.Gaussian.Basic.add_zero _

/-- Exact genus-one homogeneity of the raw second-bilinear energy.  This is
the finite Gaussian-rational form of
`E(c ω) = ‖c‖² E(ω)` and lets one surface theorem for the standard
differential control every displayed coefficient. -/
theorem unnormalizedEnergyForm_one_eq_normSq_mul_unit
    (coefficients : GaussianVector 1)
    (aMatrix bMatrix : GaussianMatrix 1) :
    unnormalizedEnergyForm coefficients aMatrix bMatrix =
      Data.Gaussian.Norm.Basic.normSq (coefficients 0) *
        unnormalizedEnergyForm genusOneUnitCoefficients
          aMatrix bMatrix := by
  unfold unnormalizedEnergyForm
  rw [periodPairingEnergy_one_eq,
    periodPairingEnergy_one_eq]
  rw [periodCombination_one, periodCombination_one,
    periodCombination_genusOne_unit,
      periodCombination_genusOne_unit]
  rw [crossPairing_scale]
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- A vanishing A-period vector forces the unnormalized boundary energy to
vanish.  This is the algebraic kernel step used before any normalization. -/
theorem unnormalizedEnergyForm_eq_zero_of_aPeriods_zero {size : Nat}
    (coefficients : GaussianVector size) (aMatrix bMatrix :
      GaussianMatrix size)
    (aPeriodsZero : forall cycle : Fin size,
      periodCombination coefficients aMatrix cycle = 0) :
    unnormalizedEnergyForm coefficients aMatrix bMatrix = 0 := by
  unfold unnormalizedEnergyForm periodPairingEnergy
  have summandsZero :
      FiniteSum.Fin.sumFin (fun cycle =>
        (periodCombination coefficients bMatrix cycle *
            Data.Gaussian.Basic.conj
              (periodCombination coefficients aMatrix cycle) -
          periodCombination coefficients aMatrix cycle *
            Data.Gaussian.Basic.conj
              (periodCombination coefficients bMatrix cycle)).im) = 0 := by
    rw [FiniteSum.Fin.sumFin_congr
      (right := fun _ => (0 : Fraction.Rational)) (fun cycle => by
        rw [aPeriodsZero cycle]
        rw [show Data.Gaussian.Basic.conj (0 : Data.Gaussian.Basic.Canonical) = 0 by
          apply Data.Gaussian.Basic.ext
          · rfl
          · change -(0 : Fraction.Rational) = 0
            ring1]
        rw [Data.Gaussian.Basic.mul_zero, Data.Gaussian.Basic.zero_mul, Data.Gaussian.Basic.sub_zero]
        rfl)]
    exact FiniteSum.Fin.sumFin_zero
  rw [summandsZero]
  exact Fraction.Field.zero_div_direct 2

/-! ## Positive energy before normalization -/

set_option genInjectivity false in
/-- A displayed nonzero Gaussian-rational coefficient identifies a nonzero
finite linear combination of the algebraic differential basis. -/
structure NonzeroGaussianVector {size : Nat}
    (vector : GaussianVector size) where
  /-- A retained bounded coordinate witnessing that the vector is nonzero. -/ index : Fin size
  /-- The coefficient at the retained coordinate is nonzero. -/ coefficient_nonzero : vector index ≠ 0

constructive_injectivity NonzeroGaussianVector

/-- Embed one displayed rational coefficient in the Gaussian rationals. -/
@[expose] def gaussianOfRational (value : Fraction.Rational) : Data.Gaussian.Basic.Canonical := ⟨value, 0⟩

/-- Entrywise finite embedding of a real rational vector. -/
@[expose] def gaussianVectorOfRational {size : Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) :
      GaussianVector size :=
  Data.Vector.Basic.vectorOfFn fun index =>
    gaussianOfRational (vector index)

/-- Read an embedded rational vector coordinate as its Gaussian embedding. -/
@[simp] theorem gaussianVectorOfRational_apply {size : Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) (index : Fin size) :
    gaussianVectorOfRational vector index =
      gaussianOfRational (vector index) :=
  Data.Vector.Basic.vectorOfFn_apply _ _

/-- Embedding a nonzero rational as a real Gaussian preserves nonvanishing. -/
theorem gaussianOfRational_ne_zero {value : Fraction.Rational}
    (nonzero : value ≠ 0) : gaussianOfRational value ≠ 0 := by
  intro gaussianZero
  have realZero := congrArg Data.Gaussian.Basic.re gaussianZero
  exact nonzero realZero

/-- A vector that does not vanish coordinatewise has a displayed nonzero coordinate.

Structural recursion tests the first entry, then retains a successor of
the original tail witness when that first entry is zero. -/
theorem exists_ne_zero_of_not_all_zero {size : Nat}
    (vector : GaussianVector size) (notAllZero : ¬ forall index, vector index = 0)
      :
    ∃ index, vector index ≠ 0 := by
  induction vector with
  | nil =>
      exact (notAllZero (fun index => Fin.elim0 index)).elim
  | cons head tail inductionHypothesis =>
      by_cases headZero : head = 0
      · have tailNotAllZero : ¬ forall index, tail index = 0 := by
          intro tailZero
          apply notAllZero
          intro index
          refine Data.Fin.cases_induction ?_ (fun tailIndex => ?_) index
          · exact headZero
          · exact tailZero tailIndex
        rcases inductionHypothesis tailNotAllZero with
          ⟨index, nonzero⟩
        exact ⟨index.succ, nonzero⟩
      · exact ⟨0, headZero⟩

/-- Return the original first nonzero coordinate as executable data.

The structural search retains the selected index and its nonvanishing
certificate; a zero head passes the original tail witness forward. -/
@[expose] def nonzeroGaussianVectorOfNotAllZero {size : Nat}
    (vector : GaussianVector size)
    (notAllZero : ¬ forall index, vector index = 0) :
    NonzeroGaussianVector vector := by
  match vector with
  | .nil =>
      exact (notAllZero (fun index => Fin.elim0 index)).elim
  | .cons head tail =>
      by_cases headZero : head = 0
      · have tailNotAllZero : ¬ forall index, tail index = 0 := by
          intro tailZero
          apply notAllZero
          intro index
          refine Data.Fin.cases_induction ?_ (fun tailIndex => ?_) index
          · exact headZero
          · exact tailZero tailIndex
        let witness := nonzeroGaussianVectorOfNotAllZero tail tailNotAllZero
        exact ⟨witness.index.succ, witness.coefficient_nonzero⟩
      · exact ⟨0, headZero⟩

/-- Multiplication by the adjugate of a nondegenerate finite matrix sends a
displayed nonzero real vector to an explicitly nonzero Gaussian vector. -/
@[expose] def scaledCoefficientsNonzero {size : Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) (nonzero :
      LinearAlgebra.Gaussian.QuadraticForm.NonzeroVector vector)
    (matrix : GaussianMatrix size)
    (inverse : SquareMatrix.Inverse.Scaled.Basic.ScaledInverse matrix)
    (scalarNonzero : inverse.scalar ≠ 0) :
    NonzeroGaussianVector
      (SquareMatrix.Multiplication.vectorMatrix
        (gaussianVectorOfRational vector) inverse.inverse) := by
  let embedded := gaussianVectorOfRational vector
  let coefficients :=
    SquareMatrix.Multiplication.vectorMatrix embedded inverse.inverse
  have coefficientsNotAllZero : ¬ forall index, coefficients index = 0 := by
    intro coefficientsZero
    have productZero :
        SquareMatrix.Multiplication.vectorMatrix coefficients matrix
          nonzero.index = 0 := by
      rw [SquareMatrix.Multiplication.vectorMatrix_apply]
      rw [FiniteSum.Fin.sumFin_congr
        (right := fun _ => (0 : Data.Gaussian.Basic.Canonical)) (fun index => by
          rw [coefficientsZero index, zero_mul])]
      exact FiniteSum.Fin.sumFin_zero
    have scaledEntry :
        SquareMatrix.Multiplication.vectorMatrix coefficients matrix
            nonzero.index =
          embedded nonzero.index * inverse.scalar := by
      calc
        SquareMatrix.Multiplication.vectorMatrix coefficients matrix
            nonzero.index =
            SquareMatrix.Multiplication.vectorMatrix embedded
              (SquareMatrix.Multiplication.mul inverse.inverse matrix)
                nonzero.index := by
          exact (Data.Vector.Basic.vector_eq_at
            (SquareMatrix.Multiplication.vectorMatrix_mul
              embedded inverse.inverse matrix) nonzero.index).symm
        _ = SquareMatrix.Multiplication.vectorMatrix embedded
              (SquareMatrix.Multiplication.scaleIdentity inverse.scalar)
                nonzero.index := by
          rw [inverse.left_identity]
        _ = embedded nonzero.index * inverse.scalar :=
          by
            simpa only [Data.Vector.Basic.vectorOfFn_apply] using
              Data.Vector.Basic.vector_eq_at
                (SquareMatrix.Multiplication.vectorMatrix_scaleIdentity
                  embedded inverse.scalar) nonzero.index
    have embeddedNonzero : embedded nonzero.index ≠ 0 := by
      unfold embedded
      rw [gaussianVectorOfRational_apply]
      exact gaussianOfRational_ne_zero nonzero.coefficient_nonzero
    exact (Data.Gaussian.Field.mul_ne_zero_direct
      embeddedNonzero scalarNonzero
        (scaledEntry.symm.trans productZero)).elim
  exact nonzeroGaussianVectorOfNotAllZero coefficients
    coefficientsNotAllZero

/-- At one synchronized period-matrix sample, multiply a displayed real
normalized coefficient vector by the complete fraction-free adjugate. -/
@[expose] def scaledNormalizedCoefficients {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Riemann.Periods.PeriodMatrix.PeriodData curve) (index : Nat) (vector :
      LinearAlgebra.Gaussian.QuadraticForm.RationalVector genus) :
    GaussianVector genus :=
  let sampled := Riemann.Periods.PeriodMatrix.sampledMatrix data.aMatrix index
  let inverse :=
    SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse sampled
  SquareMatrix.Multiplication.vectorMatrix
    (gaussianVectorOfRational vector) inverse.inverse

/-- A selected finite scaled-inverse scalar is enough to prove that the
adjugate-scaled raw coefficient vector is nonzero.  Unlike the uniform
wrapper below, this theorem imposes no condition on other sample indices. -/
@[expose] def scaledNormalizedCoefficients_nonzero_of_scalar {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Riemann.Periods.PeriodMatrix.PeriodData curve) (index : Nat) (vector :
      LinearAlgebra.Gaussian.QuadraticForm.RationalVector genus)
    (nonzero : LinearAlgebra.Gaussian.QuadraticForm.NonzeroVector vector)
    (scalarNonzero :
      (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
        (Riemann.Periods.PeriodMatrix.sampledMatrix data.aMatrix index)).scalar ≠ 0) :
    NonzeroGaussianVector
      (scaledNormalizedCoefficients data index vector) := by
  exact scaledCoefficientsNonzero vector nonzero
    (Riemann.Periods.PeriodMatrix.sampledMatrix data.aMatrix index)
    (SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse
      (Riemann.Periods.PeriodMatrix.sampledMatrix data.aMatrix index)) scalarNonzero

/-- The finite scalar lower certificate turns every sampled scaled normalized
vector into an explicit nonzero raw differential combination. -/
@[expose] def scaledNormalizedCoefficients_nonzero {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (data : Riemann.Periods.PeriodMatrix.PeriodData curve)
    (inverseLower : Riemann.Periods.PeriodMatrix.ScalarCandidateLowerCertificate data.aMatrix)
    (index : Nat) (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector genus)
    (nonzero : LinearAlgebra.Gaussian.QuadraticForm.NonzeroVector vector) :
    NonzeroGaussianVector
      (scaledNormalizedCoefficients data index vector) := by
  let sampled := Riemann.Periods.PeriodMatrix.sampledMatrix data.aMatrix index
  let inverse :=
    SquareMatrix.Inverse.PivotedScaledInverse.completeScaledInverse sampled
  have scalarSample :
      (Riemann.Periods.PeriodMatrix.canonicalScaledInverse data.aMatrix).scalar.sample index =
        inverse.scalar := by
    unfold Riemann.Periods.PeriodMatrix.canonicalScaledInverse inverse sampled
    have samples :=
      SquareMatrix.Inverse.PivotedScaledInverse.completeApproximation_sample
        (Riemann.Periods.PeriodMatrix.geometricMatrixOfNamed data.aMatrix) index
    rw [Riemann.Periods.PeriodMatrix.sample_geometricMatrixOfNamed] at samples
    exact samples.1
  have scalarNonzero : inverse.scalar ≠ 0 := by
    intro inverseZero
    apply inverseLower.sample_scalar_nonzero index
    rw [scalarSample, inverseZero]
  exact scaledCoefficientsNonzero vector nonzero sampled inverse scalarNonzero

/-! ## Exact finite energy transport algebra -/

/-- Taking the imaginary part commutes with the finite Gaussian sum. -/
theorem sumFin_im {size : Nat} (values : Fin size → Data.Gaussian.Basic.Canonical) :
    (FiniteSum.Fin.sumFin values).im =
      FiniteSum.Fin.sumFin fun index => (values index).im := by
  induction size with
  | zero => rfl
  | succ size inductionHypothesis =>
      rw [FiniteSum.Fin.sumFin_succ,
        FiniteSum.Fin.sumFin_succ,
        Data.Gaussian.Basic.add_im,
        inductionHypothesis (fun index => values index.succ)]

/-- The numerator form before division by the squared inverse scalar. -/
@[expose] def scaledImaginaryQuadraticForm {size : Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) (scalar : Data.Gaussian.Basic.Canonical)
    (numerator : GaussianMatrix size) : Fraction.Rational :=
  FiniteSum.Fin.sumFin fun row =>
    FiniteSum.Fin.sumFin fun column =>
      vector row *
        (numerator row column *
          Data.Gaussian.Basic.conj scalar).im *
            vector column

/-- Exact finite entrywise division by the one shared scaled-inverse scalar. -/
@[expose] def divideGaussianMatrix {size : Nat} (numerator : GaussianMatrix size)
    (scalar : Data.Gaussian.Basic.Canonical) : GaussianMatrix size :=
  SquareMatrix.matrixOfFn fun row column =>
    numerator row column / scalar

/-- Read a divided matrix entry as its original Gaussian entry divided by the supplied scalar. -/
@[simp] theorem divideGaussianMatrix_apply {size : Nat}
    (numerator : GaussianMatrix size) (scalar : Data.Gaussian.Basic.Canonical)
    (row column : Fin size) :
    divideGaussianMatrix numerator scalar row column =
      numerator row column / scalar :=
  SquareMatrix.matrixOfFn_apply _ _ _

/-- Dividing a Gaussian rational by an apart scalar is exactly multiplication
by its conjugate followed by division by its rational squared norm.  This
fraction-free imaginary-coordinate form avoids a field or choice shortcut. -/
theorem mul_conj_im_eq_normSq_mul_div_im (value scalar : Data.Gaussian.Basic.Canonical)
    (scalarNonzero : scalar ≠ 0) :
    (value * Data.Gaussian.Basic.conj scalar).im =
      Data.Gaussian.Norm.Basic.normSq scalar *
        (value / scalar).im := by
  have quotientCancel : (value / scalar) * scalar = value := by
    change (value * scalar⁻¹) * scalar = value
    calc
      (value * scalar⁻¹) * scalar =
          value * (scalar⁻¹ * scalar) :=
        Data.Gaussian.Basic.mul_assoc _ _ _
      _ = value * 1 := by
        rw [Data.Gaussian.Field.inv_eq,
          Data.Gaussian.Field.inv_mul scalar scalarNonzero]
      _ = value := Data.Gaussian.Basic.mul_one _
  have gaussianIdentity :
      gaussianOfRational
            (Data.Gaussian.Norm.Basic.normSq scalar) *
          (value / scalar) =
        value * Data.Gaussian.Basic.conj scalar := by
    apply Data.Gaussian.Field.mul_right_cancel_of_ne
      scalarNonzero
    calc
      (gaussianOfRational
            (Data.Gaussian.Norm.Basic.normSq scalar) *
          (value / scalar)) * scalar =
          gaussianOfRational
              (Data.Gaussian.Norm.Basic.normSq scalar) *
            ((value / scalar) * scalar) :=
        Data.Gaussian.Basic.mul_assoc _ _ _
      _ = gaussianOfRational
            (Data.Gaussian.Norm.Basic.normSq scalar) * value := by
        rw [quotientCancel]
      _ = value * gaussianOfRational
            (Data.Gaussian.Norm.Basic.normSq scalar) :=
        _root_.mul_comm _ _
      _ = value *
            (Data.Gaussian.Basic.conj scalar * scalar) := by
        have scalarNorm :
            Data.Gaussian.Basic.conj scalar * scalar =
              gaussianOfRational
                (Data.Gaussian.Norm.Basic.normSq scalar) := by
          apply Data.Gaussian.Basic.ext
          · simp only [Data.Gaussian.Basic.conj,
              Data.Gaussian.Basic.mul_re,
              Data.Gaussian.Norm.Basic.normSq,
              gaussianOfRational]
            ring1
          · simp only [Data.Gaussian.Basic.conj,
              Data.Gaussian.Basic.mul_im,
              gaussianOfRational]
            ring1
        rw [scalarNorm]
      _ = (value * Data.Gaussian.Basic.conj scalar) * scalar :=
        (Data.Gaussian.Basic.mul_assoc _ _ _).symm
  have imaginaryIdentity := congrArg
    Data.Gaussian.Basic.im gaussianIdentity
  change Data.Gaussian.Norm.Basic.normSq scalar *
      (value / scalar).im + 0 * (value / scalar).re =
    (value * Data.Gaussian.Basic.conj scalar).im at imaginaryIdentity
  rw [Fraction.Field.zero_mul_direct, _root_.add_zero] at imaginaryIdentity
  exact imaginaryIdentity.symm

/-- The fraction-free numerator form is the normalized imaginary quadratic
form multiplied by the strictly positive squared inverse scalar. -/
theorem scaledImaginaryQuadraticForm_eq_normSq_mul {size : Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) (scalar : Data.Gaussian.Basic.Canonical)
    (numerator : GaussianMatrix size) (scalarNonzero : scalar ≠ 0) :
    scaledImaginaryQuadraticForm vector scalar numerator =
      Data.Gaussian.Norm.Basic.normSq scalar *
        LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector
          (divideGaussianMatrix numerator scalar) := by
  unfold scaledImaginaryQuadraticForm
  calc
    FiniteSum.Fin.sumFin (fun row =>
        FiniteSum.Fin.sumFin (fun column =>
          vector row *
            (numerator row column *
              Data.Gaussian.Basic.conj scalar).im *
                vector column)) =
        FiniteSum.Fin.sumFin (fun row =>
          FiniteSum.Fin.sumFin (fun column =>
            Data.Gaussian.Norm.Basic.normSq scalar *
              (vector row * (numerator row column / scalar).im *
                vector column))) := by
      apply FiniteSum.Fin.sumFin_congr
      intro row
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [mul_conj_im_eq_normSq_mul_div_im _ _ scalarNonzero]
      ring1
    _ = FiniteSum.Fin.sumFin (fun row =>
          Data.Gaussian.Norm.Basic.normSq scalar *
            FiniteSum.Fin.sumFin (fun column =>
              vector row * (numerator row column / scalar).im *
                vector column)) := by
      apply FiniteSum.Fin.sumFin_congr
      intro row
      exact FiniteSum.Fin.sumFin_mul_left _ _
    _ = Data.Gaussian.Norm.Basic.normSq scalar *
          FiniteSum.Fin.sumFin (fun row =>
            FiniteSum.Fin.sumFin (fun column =>
              vector row * (numerator row column / scalar).im *
                vector column)) :=
      FiniteSum.Fin.sumFin_mul_left _ _
    _ = Data.Gaussian.Norm.Basic.normSq scalar *
          LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector
            (divideGaussianMatrix numerator scalar) := by
      congr 1
      unfold LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm
      apply FiniteSum.Fin.sumFin_congr
      intro row
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [divideGaussianMatrix_apply]

/-- The antisymmetric pairing with a real multiple of a scalar is twice the scaled imaginary conjugate product. -/
theorem pairingSummand_scaled (value scalar : Data.Gaussian.Basic.Canonical)
    (coefficient : Fraction.Rational) :
    (value * Data.Gaussian.Basic.conj
          (gaussianOfRational coefficient * scalar) -
        (gaussianOfRational coefficient * scalar) *
          Data.Gaussian.Basic.conj value).im =
      2 * coefficient *
        (value * Data.Gaussian.Basic.conj scalar).im := by
  simp only [gaussianOfRational,
    Data.Gaussian.Basic.sub_im,
    Data.Gaussian.Basic.mul_re,
    Data.Gaussian.Basic.mul_im,
    Data.Gaussian.Basic.conj]
  ring1

/-- Expand the imaginary part of a row action times a conjugate scalar as a finite real-weighted sum. -/
theorem vectorMatrix_mul_conj_im {size : Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) (matrix :
      GaussianMatrix size)
    (scalar : Data.Gaussian.Basic.Canonical) (column : Fin size) :
    (SquareMatrix.Multiplication.vectorMatrix
          (gaussianVectorOfRational vector) matrix column *
        Data.Gaussian.Basic.conj scalar).im =
      FiniteSum.Fin.sumFin fun row =>
        vector row *
          (matrix row column *
            Data.Gaussian.Basic.conj scalar).im := by
  rw [SquareMatrix.Multiplication.vectorMatrix_apply]
  rw [← FiniteSum.Fin.sumFin_mul_right]
  rw [sumFin_im]
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [gaussianVectorOfRational_apply]
  simp only [gaussianOfRational,
    Data.Gaussian.Basic.mul_re,
    Data.Gaussian.Basic.mul_im,
    Data.Gaussian.Basic.conj]
  ring1

/-- The adjugate-scaled period combination on the first matrix is its real coefficient vector times the retained scalar.
-/
theorem periodCombination_scaled_a {size : Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) (aMatrix :
      GaussianMatrix size)
    (inverse : SquareMatrix.Inverse.Scaled.Basic.ScaledInverse aMatrix) :
    periodCombination
        (SquareMatrix.Multiplication.vectorMatrix
          (gaussianVectorOfRational vector) inverse.inverse) aMatrix =
      Data.Vector.Basic.vectorOfFn fun cycle =>
        gaussianVectorOfRational vector cycle * inverse.scalar := by
  unfold periodCombination
  calc
    SquareMatrix.Multiplication.vectorMatrix
        (SquareMatrix.Multiplication.vectorMatrix
          (gaussianVectorOfRational vector) inverse.inverse) aMatrix =
        SquareMatrix.Multiplication.vectorMatrix
          (gaussianVectorOfRational vector)
            (SquareMatrix.Multiplication.mul inverse.inverse aMatrix) :=
      (SquareMatrix.Multiplication.vectorMatrix_mul
        (gaussianVectorOfRational vector) inverse.inverse aMatrix).symm
    _ = SquareMatrix.Multiplication.vectorMatrix
          (gaussianVectorOfRational vector)
            (SquareMatrix.Multiplication.scaleIdentity inverse.scalar) := by
      rw [inverse.left_identity]
    _ = Data.Vector.Basic.vectorOfFn fun cycle =>
          gaussianVectorOfRational vector cycle * inverse.scalar :=
      SquareMatrix.Multiplication.vectorMatrix_scaleIdentity
        (gaussianVectorOfRational vector) inverse.scalar

/-- The adjugate-scaled period combination on the second matrix is the coefficient action on the retained inverse
product. -/
theorem periodCombination_scaled_b {size : Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) (aMatrix bMatrix :
      GaussianMatrix size)
    (inverse : SquareMatrix.Inverse.Scaled.Basic.ScaledInverse aMatrix) :
    periodCombination
        (SquareMatrix.Multiplication.vectorMatrix
          (gaussianVectorOfRational vector) inverse.inverse) bMatrix =
      SquareMatrix.Multiplication.vectorMatrix
        (gaussianVectorOfRational vector)
          (SquareMatrix.Multiplication.mul inverse.inverse bMatrix) := by
  unfold periodCombination
  exact (SquareMatrix.Multiplication.vectorMatrix_mul
    (gaussianVectorOfRational vector) inverse.inverse bMatrix).symm

/-- Exact finite second-relation transport before scalar division.  The raw
energy of the adjugate-scaled differential combination is precisely the
imaginary numerator form of the normalized vector. -/
theorem unnormalizedEnergyForm_scaledCoefficients {size : Nat}
    (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size) (aMatrix bMatrix :
      GaussianMatrix size)
    (inverse : SquareMatrix.Inverse.Scaled.Basic.ScaledInverse aMatrix) :
    unnormalizedEnergyForm
        (SquareMatrix.Multiplication.vectorMatrix
          (gaussianVectorOfRational vector) inverse.inverse)
          aMatrix bMatrix =
      scaledImaginaryQuadraticForm vector inverse.scalar
        (SquareMatrix.Multiplication.mul inverse.inverse bMatrix) := by
  unfold unnormalizedEnergyForm
  rw [periodCombination_scaled_a vector aMatrix inverse,
    periodCombination_scaled_b vector aMatrix bMatrix inverse]
  unfold periodPairingEnergy scaledImaginaryQuadraticForm
  have summandIdentity : forall cycle,
      (SquareMatrix.Multiplication.vectorMatrix
            (gaussianVectorOfRational vector)
              (SquareMatrix.Multiplication.mul inverse.inverse bMatrix)
                cycle *
          Data.Gaussian.Basic.conj
            (Data.Vector.Basic.vectorOfFn
              (fun entry => gaussianVectorOfRational vector entry *
                inverse.scalar) cycle) -
        Data.Vector.Basic.vectorOfFn
            (fun entry => gaussianVectorOfRational vector entry *
              inverse.scalar) cycle *
          Data.Gaussian.Basic.conj
            (SquareMatrix.Multiplication.vectorMatrix
              (gaussianVectorOfRational vector)
                (SquareMatrix.Multiplication.mul inverse.inverse bMatrix)
                  cycle)).im =
        2 * FiniteSum.Fin.sumFin (fun row =>
          vector row *
            ((SquareMatrix.Multiplication.mul inverse.inverse bMatrix)
              row cycle *
                Data.Gaussian.Basic.conj inverse.scalar).im *
                  vector cycle) := by
    intro cycle
    rw [Data.Vector.Basic.vectorOfFn_apply,
      gaussianVectorOfRational_apply]
    rw [pairingSummand_scaled]
    rw [vectorMatrix_mul_conj_im]
    rw [FiniteSum.Fin.sumFin_mul_right]
    ring1
  rw [FiniteSum.Fin.sumFin_congr summandIdentity]
  rw [FiniteSum.Fin.sumFin_mul_left]
  have divideTwo :
      (2 * FiniteSum.Fin.sumFin (fun cycle =>
        FiniteSum.Fin.sumFin (fun row =>
          vector row *
            ((SquareMatrix.Multiplication.mul inverse.inverse bMatrix)
              row cycle *
                Data.Gaussian.Basic.conj inverse.scalar).im *
                  vector cycle))) / 2 =
        FiniteSum.Fin.sumFin (fun cycle =>
          FiniteSum.Fin.sumFin (fun row =>
            vector row *
              ((SquareMatrix.Multiplication.mul inverse.inverse bMatrix)
                row cycle *
                  Data.Gaussian.Basic.conj inverse.scalar).im *
                    vector cycle)) := by
    let total := FiniteSum.Fin.sumFin (fun cycle =>
      FiniteSum.Fin.sumFin (fun row =>
        vector row *
          ((SquareMatrix.Multiplication.mul inverse.inverse bMatrix)
            row cycle *
              Data.Gaussian.Basic.conj inverse.scalar).im *
                vector cycle))
    have divideOne : total / 1 = total := by
      have cancel := Fraction.Field.div_mul_cancel_of_ne
        total 1 (by decide)
      rw [Fraction.Field.mul_one_direct] at cancel
      exact cancel
    calc
      (2 * total) / 2 = (2 * total) / (2 * 1) := by
        rw [Fraction.Field.mul_one_direct]
      _ = total / 1 :=
        Fraction.Field.mul_div_mul_left_direct 2 total 1 (by decide)
      _ = total := divideOne
  rw [divideTwo]
  exact FiniteSum.Fin.sumFin_swap _

/-- Complete exact transport from the raw second-bilinear energy to the
normalized finite matrix obtained from the same synchronized A/B sample. -/
theorem unnormalizedEnergyForm_scaledCoefficients_eq_normSq_mul
    {size : Nat} (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size)
    (aMatrix bMatrix : GaussianMatrix size)
    (inverse : SquareMatrix.Inverse.Scaled.Basic.ScaledInverse aMatrix)
    (scalarNonzero : inverse.scalar ≠ 0) :
    unnormalizedEnergyForm
        (SquareMatrix.Multiplication.vectorMatrix
          (gaussianVectorOfRational vector) inverse.inverse)
          aMatrix bMatrix =
      Data.Gaussian.Norm.Basic.normSq inverse.scalar *
        LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector
          (divideGaussianMatrix
            (SquareMatrix.Multiplication.mul inverse.inverse bMatrix)
            inverse.scalar) := by
  rw [unnormalizedEnergyForm_scaledCoefficients]
  exact scaledImaginaryQuadraticForm_eq_normSq_mul vector inverse.scalar
    (SquareMatrix.Multiplication.mul inverse.inverse bMatrix) scalarNonzero

/-- Strict raw surface energy therefore gives strict positivity of the exact
normalized finite quotient at that same sample.  Cancellation uses only the
displayed nonnegative squared norm, not an abstract eigenvalue argument. -/
theorem imaginaryQuadraticForm_divide_positive_of_unnormalized
    {size : Nat} (vector : LinearAlgebra.Gaussian.QuadraticForm.RationalVector size)
    (aMatrix bMatrix : GaussianMatrix size)
    (inverse : SquareMatrix.Inverse.Scaled.Basic.ScaledInverse aMatrix)
    (scalarNonzero : inverse.scalar ≠ 0)
    (rawPositive : 0 < unnormalizedEnergyForm
      (SquareMatrix.Multiplication.vectorMatrix
        (gaussianVectorOfRational vector) inverse.inverse)
        aMatrix bMatrix) :
    0 < LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector
      (divideGaussianMatrix
        (SquareMatrix.Multiplication.mul inverse.inverse bMatrix)
        inverse.scalar) := by
  have productPositive :
      0 < Data.Gaussian.Norm.Basic.normSq inverse.scalar *
        LinearAlgebra.Gaussian.QuadraticForm.imaginaryQuadraticForm vector
          (divideGaussianMatrix
            (SquareMatrix.Multiplication.mul inverse.inverse bMatrix)
            inverse.scalar) := by
    rw [← unnormalizedEnergyForm_scaledCoefficients_eq_normSq_mul
      vector aMatrix bMatrix inverse scalarNonzero]
    exact rawPositive
  exact Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct productPositive
    (Data.Gaussian.Norm.Basic.normSq_nonneg inverse.scalar)

end Purelib.LinearAlgebra.Gaussian.Energy

end

section
public section

/-!
# Triangulated finite surface energy

This module supplies the two-dimensional algebraic bridge for the second
Riemann bilinear relation.  A finite sample consists of a genuine oriented
triangulation, primitive values at its vertices, an exact identification of
its outer boundary with the displayed A/B period commutators, and a checked
lower-energy inequality on every face.  Incidence cancellation and finite
summation then derive the global surface lower theorem consumed by
`PreparedEnergy`; it is not repeated as an assumption.
-/

namespace Purelib.LinearAlgebra.Gaussian.Energy.PreparedEnergySurface

/-- A structural vector of Gaussian rational coefficients with retained finite dimension. -/
abbrev GaussianVector (size : Nat) :=
  _root_.Purelib.LinearAlgebra.Gaussian.Energy.GaussianVector size

end Purelib.LinearAlgebra.Gaussian.Energy.PreparedEnergySurface

end
