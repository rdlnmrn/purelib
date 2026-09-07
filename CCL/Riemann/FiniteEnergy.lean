import CCL.Riemann.FinitePositivity

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

namespace CCL.Riemann.FiniteEnergy

open CCL.Riemann.PeriodMatrix

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev RationalVector := CCL.Riemann.PeriodMatrix.RationalVector
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianVector (size : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Vector Gaussian size
abbrev GaussianMatrix (size : Nat) :=
  RFAP.ConstructiveFiniteMatrix.Matrix Gaussian size

/-! ## Unnormalized finite second relation -/

/-- The A- or B-period vector of one displayed Gaussian-rational linear
combination of the basis differentials. -/
def periodCombination {size : Nat} (coefficients : GaussianVector size)
    (periods : GaussianMatrix size) : GaussianVector size :=
  RFAP.ConstructiveFiniteMatrix.vectorMatrix coefficients periods

/-- Rational energy extracted from displayed A- and B-period vectors.  The
orientation is chosen so that `A = I`, `B = Ω`, and real coefficients recover
`vᵀ Im(Ω) v`. -/
def periodPairingEnergy {size : Nat} (aPeriods bPeriods : GaussianVector size) :
    Coordinate :=
  (RFAP.ConstructiveFiniteMatrix.sumFin fun cycle =>
    (bPeriods cycle * RFAP.ConstructiveGaussian.Gaussian.conj
        (aPeriods cycle) -
      aPeriods cycle * RFAP.ConstructiveGaussian.Gaussian.conj
        (bPeriods cycle)).im) / 2

/-- Unnormalized second-bilinear energy of a differential coefficient vector
against finite displayed A/B period matrices. -/
def unnormalizedEnergyForm {size : Nat} (coefficients : GaussianVector size)
    (aMatrix bMatrix : GaussianMatrix size) : Coordinate :=
  periodPairingEnergy (periodCombination coefficients aMatrix)
    (periodCombination coefficients bMatrix)

private theorem crossPairing_sq_le_normSq_mul (a b : Gaussian) :
    ((b * RFAP.ConstructiveGaussian.Gaussian.conj a -
      a * RFAP.ConstructiveGaussian.Gaussian.conj b).im / 2) ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq a *
        RFAP.ConstructiveGaussian.Gaussian.normSq b := by
  have squareNonnegative :
      0 <= (a.re * b.re + a.im * b.im) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct _
  simp only [RFAP.ConstructiveGaussian.Gaussian.sub_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.conj,
    RFAP.ConstructiveGaussian.Gaussian.normSq]
  change
    (((b.re * (-a.im) + b.im * a.re -
        (a.re * (-b.im) + a.im * b.re))) / 2) ^ 2 <=
      (a.re ^ 2 + a.im ^ 2) * (b.re ^ 2 + b.im ^ 2)
  have energyIdentity :
      (b.re * (-a.im) + b.im * a.re -
          (a.re * (-b.im) + a.im * b.re)) / 2 =
        a.re * b.im - a.im * b.re := by
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      (show (2 : Coordinate) ≠ 0 by decide)
    rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _ (by decide)]
    ring1
  rw [energyIdentity]
  have identity :
      (a.re ^ 2 + a.im ^ 2) * (b.re ^ 2 + b.im ^ 2) -
          (a.re * b.im - a.im * b.re) ^ 2 =
        (a.re * b.re + a.im * b.im) ^ 2 := by
    ring1
  apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
  rw [identity]
  exact squareNonnegative

/-- Scaling both displayed periods by one Gaussian coefficient scales their
antisymmetric imaginary pairing by its squared norm. -/
private theorem crossPairing_scale (coefficient a b : Gaussian) :
    (coefficient * b * RFAP.ConstructiveGaussian.Gaussian.conj
          (coefficient * a) -
        coefficient * a * RFAP.ConstructiveGaussian.Gaussian.conj
          (coefficient * b)).im =
      RFAP.ConstructiveGaussian.Gaussian.normSq coefficient *
        (b * RFAP.ConstructiveGaussian.Gaussian.conj a -
          a * RFAP.ConstructiveGaussian.Gaussian.conj b).im := by
  simp only [RFAP.ConstructiveGaussian.Gaussian.conj_mul]
  simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.conj,
    RFAP.ConstructiveGaussian.Gaussian.sub_im,
    RFAP.ConstructiveGaussian.Gaussian.normSq]
  ring1

/-- In dimension one the square of the raw boundary pairing is bounded by
the product of the displayed A- and B-period squared norms.  This is the
two-coordinate Lagrange identity, proved entirely in Gaussian rationals. -/
theorem periodPairingEnergy_one_sq_le
    (aPeriods bPeriods : GaussianVector 1) :
    periodPairingEnergy aPeriods bPeriods ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (aPeriods 0) *
        RFAP.ConstructiveGaussian.Gaussian.normSq (bPeriods 0) := by
  unfold periodPairingEnergy
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change
    (((bPeriods 0 * RFAP.ConstructiveGaussian.Gaussian.conj (aPeriods 0) -
      aPeriods 0 * RFAP.ConstructiveGaussian.Gaussian.conj (bPeriods 0)).im +
        0) / 2) ^ 2 <= _
  rw [_root_.add_zero]
  exact crossPairing_sq_le_normSq_mul (aPeriods 0) (bPeriods 0)

/-- The dimension-one energy fold contains exactly its zeroth summand. -/
theorem periodPairingEnergy_one_eq
    (aPeriods bPeriods : GaussianVector 1) :
    periodPairingEnergy aPeriods bPeriods =
      (bPeriods 0 * RFAP.ConstructiveGaussian.Gaussian.conj (aPeriods 0) -
        aPeriods 0 * RFAP.ConstructiveGaussian.Gaussian.conj
          (bPeriods 0)).im / 2 := by
  unfold periodPairingEnergy
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change (_ + 0) / 2 = _
  rw [_root_.add_zero]

/-- The sole coefficient of the standard genus-one differential. -/
def genusOneUnitCoefficients : GaussianVector 1 :=
  RFAP.ConstructiveFiniteMatrix.vectorOfFn fun _ => 1

@[simp] theorem genusOneUnitCoefficients_apply (index : Fin 1) :
    genusOneUnitCoefficients index = 1 :=
  RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply _ _

/-- Multiplication by the one-entry coefficient vector selects the sole row. -/
@[simp] theorem periodCombination_genusOne_unit
    (matrix : GaussianMatrix 1) (cycle : Fin 1) :
    periodCombination genusOneUnitCoefficients matrix cycle =
      matrix 0 cycle := by
  unfold periodCombination
  rw [RFAP.ConstructiveFiniteMatrix.vectorMatrix_apply]
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change genusOneUnitCoefficients 0 * matrix 0 cycle + 0 = _
  rw [genusOneUnitCoefficients_apply,
    RFAP.ConstructiveGaussian.Gaussian.one_mul,
    RFAP.ConstructiveGaussian.Gaussian.add_zero]

/-- The genus-one raw energy square is controlled by the sole matrix entries. -/
theorem unnormalizedEnergyForm_genusOne_unit_sq_le
    (aMatrix bMatrix : GaussianMatrix 1) :
    unnormalizedEnergyForm genusOneUnitCoefficients aMatrix bMatrix ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq (aMatrix 0 0) *
        RFAP.ConstructiveGaussian.Gaussian.normSq (bMatrix 0 0) := by
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
  rw [RFAP.ConstructiveFiniteMatrix.vectorMatrix_apply,
    RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change coefficients 0 * matrix 0 cycle + 0 = _
  exact RFAP.ConstructiveGaussian.Gaussian.add_zero _

/-- Exact genus-one homogeneity of the raw second-bilinear energy.  This is
the finite Gaussian-rational form of
`E(c ω) = ‖c‖² E(ω)` and lets one surface theorem for the standard
differential control every displayed coefficient. -/
theorem unnormalizedEnergyForm_one_eq_normSq_mul_unit
    (coefficients : GaussianVector 1)
    (aMatrix bMatrix : GaussianMatrix 1) :
    unnormalizedEnergyForm coefficients aMatrix bMatrix =
      RFAP.ConstructiveGaussian.Gaussian.normSq (coefficients 0) *
        unnormalizedEnergyForm genusOneUnitCoefficients aMatrix bMatrix := by
  unfold unnormalizedEnergyForm
  rw [periodPairingEnergy_one_eq, periodPairingEnergy_one_eq]
  rw [periodCombination_one, periodCombination_one,
    periodCombination_genusOne_unit, periodCombination_genusOne_unit]
  rw [crossPairing_scale]
  simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  ring1

/-- A vanishing A-period vector forces the unnormalized boundary energy to
vanish.  This is the algebraic kernel step used before any normalization. -/
theorem unnormalizedEnergyForm_eq_zero_of_aPeriods_zero {size : Nat}
    (coefficients : GaussianVector size) (aMatrix bMatrix : GaussianMatrix size)
    (aPeriodsZero : forall cycle : Fin size,
      periodCombination coefficients aMatrix cycle = 0) :
    unnormalizedEnergyForm coefficients aMatrix bMatrix = 0 := by
  unfold unnormalizedEnergyForm periodPairingEnergy
  have summandsZero :
      RFAP.ConstructiveFiniteMatrix.sumFin (fun cycle =>
        (periodCombination coefficients bMatrix cycle *
            RFAP.ConstructiveGaussian.Gaussian.conj
              (periodCombination coefficients aMatrix cycle) -
          periodCombination coefficients aMatrix cycle *
            RFAP.ConstructiveGaussian.Gaussian.conj
              (periodCombination coefficients bMatrix cycle)).im) = 0 := by
    rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
      (right := fun _ => (0 : Coordinate)) (fun cycle => by
        rw [aPeriodsZero cycle]
        rw [show RFAP.ConstructiveGaussian.Gaussian.conj (0 : Gaussian) = 0 by
          apply RFAP.ConstructiveGaussian.Gaussian.ext
          · rfl
          · change -(0 : Coordinate) = 0
            ring1]
        rw [mul_zero, zero_mul, sub_zero]
        rfl)]
    exact RFAP.ConstructiveFiniteMatrix.sumFin_zero
  rw [summandsZero]
  exact RFAP.ConstructiveFraction.zero_div_direct 2

/-- One rational lower contribution to the positive surface energy. -/
structure Cell where
  areaLower : Coordinate
  densityLower : Coordinate
  areaLower_nonnegative : 0 <= areaLower
  densityLower_nonnegative : 0 <= densityLower

namespace Cell

/-- The lower energy contributed by a single finite cell. -/
def contribution (cell : Cell) : Coordinate :=
  cell.areaLower * cell.densityLower

theorem contribution_nonnegative (cell : Cell) :
    0 <= cell.contribution :=
  RFAP.ConstructiveFraction.mul_nonneg_direct
    cell.areaLower_nonnegative cell.densityLower_nonnegative

theorem contribution_positive (cell : Cell)
    (areaPositive : 0 < cell.areaLower)
    (densityPositive : 0 < cell.densityLower) :
    0 < cell.contribution :=
  RFAP.ConstructiveFraction.mul_pos_direct areaPositive densityPositive

end Cell

/-- Exact finite sum of the displayed cellwise energy lower bounds. -/
def cellEnergy {cellCount : Nat} (cells : Fin cellCount -> Cell) : Coordinate :=
  RFAP.ConstructiveFiniteMatrix.sumFin fun index =>
    (cells index).contribution

theorem cellEnergy_nonnegative {cellCount : Nat}
    (cells : Fin cellCount -> Cell) : 0 <= cellEnergy cells := by
  calc
    0 = RFAP.ConstructiveFiniteMatrix.sumFin
          (fun _ : Fin cellCount => (0 : Coordinate)) :=
      RFAP.ConstructiveFiniteMatrix.sumFin_zero.symm
    _ <= cellEnergy cells :=
      CCL.Riemann.FinitePositivity.sumFin_mono _ _
        (fun index => (cells index).contribution_nonnegative)

/-- One strictly positive cell makes the complete sum positive because every
other displayed contribution is nonnegative. -/
theorem cellEnergy_positive_of_cell {cellCount : Nat}
    (cells : Fin cellCount -> Cell) (positiveCell : Fin cellCount)
    (areaPositive : 0 < (cells positiveCell).areaLower)
    (densityPositive : 0 < (cells positiveCell).densityLower) :
    0 < cellEnergy cells := by
  have selectedPositive : 0 < (cells positiveCell).contribution :=
    Cell.contribution_positive _ areaPositive densityPositive
  have selected_le_energy :
      (cells positiveCell).contribution <= cellEnergy cells := by
    calc
      (cells positiveCell).contribution =
          RFAP.ConstructiveFiniteMatrix.sumFin (fun index =>
            if index = positiveCell then (cells index).contribution else 0) :=
        (RFAP.ConstructiveFiniteMatrix.sumFin_ite_eq positiveCell
          (fun index => (cells index).contribution)).symm
      _ <= cellEnergy cells :=
        CCL.Riemann.FinitePositivity.sumFin_mono _ _ (fun index => by
          by_cases equal : index = positiveCell
          · rw [if_pos equal]
          · rw [if_neg equal]
            exact (cells index).contribution_nonnegative)
  exact selectedPositive.trans_le selected_le_energy

/-! ## Positive energy before normalization -/

/-- A displayed nonzero Gaussian-rational coefficient identifies a nonzero
finite linear combination of the algebraic differential basis. -/
structure NonzeroGaussianVector {size : Nat}
    (vector : GaussianVector size) where
  index : Fin size
  coefficient_nonzero : vector index ≠ 0

/-- Embed one displayed rational coefficient in the Gaussian rationals. -/
def gaussianOfRational (value : Coordinate) : Gaussian := ⟨value, 0⟩

/-- Entrywise finite embedding of a real rational vector. -/
def gaussianVectorOfRational {size : Nat}
    (vector : RationalVector size) : GaussianVector size :=
  RFAP.ConstructiveFiniteMatrix.vectorOfFn fun index =>
    gaussianOfRational (vector index)

@[simp] theorem gaussianVectorOfRational_apply {size : Nat}
    (vector : RationalVector size) (index : Fin size) :
    gaussianVectorOfRational vector index =
      gaussianOfRational (vector index) :=
  RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply _ _

theorem gaussianOfRational_ne_zero {value : Coordinate}
    (nonzero : value ≠ 0) : gaussianOfRational value ≠ 0 := by
  intro gaussianZero
  have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re gaussianZero
  exact nonzero realZero

/-- Finite structural search turns failure of coordinatewise vanishing into
an explicit nonzero coordinate witness, without classical quantifier
negation. -/
theorem exists_ne_zero_of_not_all_zero {size : Nat}
    (vector : GaussianVector size) (notAllZero : ¬ forall index, vector index = 0) :
    ∃ index, vector index ≠ 0 := by
  induction size with
  | zero =>
      cases vector
      exact (notAllZero (fun index => Fin.elim0 index)).elim
  | succ size inductionHypothesis =>
      cases vector with
      | cons head tail =>
          by_cases headZero : head = 0
          · have tailNotAllZero : ¬ forall index, tail index = 0 := by
              intro tailZero
              apply notAllZero
              intro index
              refine Fin.cases ?_ (fun tailIndex => ?_) index
              · exact headZero
              · exact tailZero tailIndex
            rcases inductionHypothesis tail tailNotAllZero with
              ⟨index, nonzero⟩
            exact ⟨index.succ, nonzero⟩
          · exact ⟨0, headZero⟩

/-- Executable structural search returns the first nonzero coordinate as
data.  Unlike an existential proposition, this witness can be consumed by the
finite energy certificate interface. -/
def nonzeroGaussianVectorOfNotAllZero {size : Nat}
    (vector : GaussianVector size)
    (notAllZero : ¬ forall index, vector index = 0) :
    NonzeroGaussianVector vector := by
  induction size with
  | zero =>
      cases vector
      exact (notAllZero (fun index => Fin.elim0 index)).elim
  | succ size inductionHypothesis =>
      cases vector with
      | cons head tail =>
          by_cases headZero : head = 0
          · have tailNotAllZero : ¬ forall index, tail index = 0 := by
              intro tailZero
              apply notAllZero
              intro index
              refine Fin.cases ?_ (fun tailIndex => ?_) index
              · exact headZero
              · exact tailZero tailIndex
            let witness := inductionHypothesis tail tailNotAllZero
            exact ⟨witness.index.succ, witness.coefficient_nonzero⟩
          · exact ⟨0, headZero⟩

/-- Multiplication by the adjugate of a nondegenerate finite matrix sends a
displayed nonzero real vector to an explicitly nonzero Gaussian vector. -/
def scaledCoefficientsNonzero {size : Nat}
    (vector : RationalVector size) (nonzero : NonzeroVector vector)
    (matrix : GaussianMatrix size)
    (inverse : RFAP.ConstructiveFiniteMatrix.ScaledInverse matrix)
    (scalarNonzero : inverse.scalar ≠ 0) :
    NonzeroGaussianVector
      (RFAP.ConstructiveFiniteMatrix.vectorMatrix
        (gaussianVectorOfRational vector) inverse.inverse) := by
  let embedded := gaussianVectorOfRational vector
  let coefficients :=
    RFAP.ConstructiveFiniteMatrix.vectorMatrix embedded inverse.inverse
  have coefficientsNotAllZero : ¬ forall index, coefficients index = 0 := by
    intro coefficientsZero
    have productZero :
        RFAP.ConstructiveFiniteMatrix.vectorMatrix coefficients matrix
          nonzero.index = 0 := by
      rw [RFAP.ConstructiveFiniteMatrix.vectorMatrix_apply]
      rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr
        (right := fun _ => (0 : Gaussian)) (fun index => by
          rw [coefficientsZero index, zero_mul])]
      exact RFAP.ConstructiveFiniteMatrix.sumFin_zero
    have scaledEntry :
        RFAP.ConstructiveFiniteMatrix.vectorMatrix coefficients matrix
            nonzero.index =
          embedded nonzero.index * inverse.scalar := by
      calc
        RFAP.ConstructiveFiniteMatrix.vectorMatrix coefficients matrix
            nonzero.index =
            RFAP.ConstructiveFiniteMatrix.vectorMatrix embedded
              (RFAP.ConstructiveFiniteMatrix.mul inverse.inverse matrix)
                nonzero.index := by
          exact (RFAP.ConstructiveFiniteMatrix.vector_eq_at
            (RFAP.ConstructiveFiniteMatrix.vectorMatrix_mul
              embedded inverse.inverse matrix) nonzero.index).symm
        _ = RFAP.ConstructiveFiniteMatrix.vectorMatrix embedded
              (RFAP.ConstructiveFiniteMatrix.scaleIdentity inverse.scalar)
                nonzero.index := by
          rw [inverse.left_identity]
        _ = embedded nonzero.index * inverse.scalar :=
          by
            simpa only [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply] using
              RFAP.ConstructiveFiniteMatrix.vector_eq_at
                (RFAP.ConstructiveFiniteMatrix.vectorMatrix_scaleIdentity
                  embedded inverse.scalar) nonzero.index
    have embeddedNonzero : embedded nonzero.index ≠ 0 := by
      unfold embedded
      rw [gaussianVectorOfRational_apply]
      exact gaussianOfRational_ne_zero nonzero.coefficient_nonzero
    exact (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
      embeddedNonzero scalarNonzero
        (scaledEntry.symm.trans productZero)).elim
  exact nonzeroGaussianVectorOfNotAllZero coefficients
    coefficientsNotAllZero

/-- At one synchronized period-matrix sample, multiply a displayed real
normalized coefficient vector by the complete fraction-free adjugate. -/
def scaledNormalizedCoefficients {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) (index : Nat) (vector : RationalVector genus) :
    GaussianVector genus :=
  let sampled := sampledMatrix data.aMatrix index
  let inverse :=
    CCL.Riemann.PivotedScaledInverse.completeScaledInverse sampled
  RFAP.ConstructiveFiniteMatrix.vectorMatrix
    (gaussianVectorOfRational vector) inverse.inverse

/-- A selected finite scaled-inverse scalar is enough to prove that the
adjugate-scaled raw coefficient vector is nonzero.  Unlike the uniform
wrapper below, this theorem imposes no condition on other sample indices. -/
def scaledNormalizedCoefficients_nonzero_of_scalar {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) (index : Nat) (vector : RationalVector genus)
    (nonzero : NonzeroVector vector)
    (scalarNonzero :
      (CCL.Riemann.PivotedScaledInverse.completeScaledInverse
        (sampledMatrix data.aMatrix index)).scalar ≠ 0) :
    NonzeroGaussianVector
      (scaledNormalizedCoefficients data index vector) := by
  exact scaledCoefficientsNonzero vector nonzero
    (sampledMatrix data.aMatrix index)
    (CCL.Riemann.PivotedScaledInverse.completeScaledInverse
      (sampledMatrix data.aMatrix index)) scalarNonzero

/-- The finite scalar lower certificate turns every sampled scaled normalized
vector into an explicit nonzero raw differential combination. -/
def scaledNormalizedCoefficients_nonzero {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (index : Nat) (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) :
    NonzeroGaussianVector
      (scaledNormalizedCoefficients data index vector) := by
  let sampled := sampledMatrix data.aMatrix index
  let inverse :=
    CCL.Riemann.PivotedScaledInverse.completeScaledInverse sampled
  have scalarSample :
      (canonicalScaledInverse data.aMatrix).scalar.sample index =
        inverse.scalar := by
    unfold canonicalScaledInverse inverse sampled
    have samples :=
      CCL.Riemann.PivotedScaledInverse.completeApproximation_sample
        (geometricMatrixOfNamed data.aMatrix) index
    rw [sample_geometricMatrixOfNamed] at samples
    exact samples.1
  have scalarNonzero : inverse.scalar ≠ 0 := by
    intro inverseZero
    apply inverseLower.sample_scalar_nonzero index
    rw [scalarSample, inverseZero]
  exact scaledCoefficientsNonzero vector nonzero sampled inverse scalarNonzero

/-! ## Exact finite energy transport algebra -/

theorem sumFin_im {size : Nat} (values : Fin size → Gaussian) :
    (RFAP.ConstructiveFiniteMatrix.sumFin values).im =
      RFAP.ConstructiveFiniteMatrix.sumFin fun index => (values index).im := by
  induction size with
  | zero => rfl
  | succ size inductionHypothesis =>
      rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ,
        RFAP.ConstructiveFiniteMatrix.sumFin_succ,
        RFAP.ConstructiveGaussian.Gaussian.add_im,
        inductionHypothesis (fun index => values index.succ)]

/-- The numerator form before division by the squared inverse scalar. -/
def scaledImaginaryQuadraticForm {size : Nat}
    (vector : RationalVector size) (scalar : Gaussian)
    (numerator : GaussianMatrix size) : Coordinate :=
  RFAP.ConstructiveFiniteMatrix.sumFin fun row =>
    RFAP.ConstructiveFiniteMatrix.sumFin fun column =>
      vector row *
        (numerator row column *
          RFAP.ConstructiveGaussian.Gaussian.conj scalar).im *
            vector column

/-- Exact finite entrywise division by the one shared scaled-inverse scalar. -/
def divideGaussianMatrix {size : Nat} (numerator : GaussianMatrix size)
    (scalar : Gaussian) : GaussianMatrix size :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn fun row column =>
    numerator row column / scalar

@[simp] theorem divideGaussianMatrix_apply {size : Nat}
    (numerator : GaussianMatrix size) (scalar : Gaussian)
    (row column : Fin size) :
    divideGaussianMatrix numerator scalar row column =
      numerator row column / scalar :=
  RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply _ _ _

/-- Dividing a Gaussian rational by an apart scalar is exactly multiplication
by its conjugate followed by division by its rational squared norm.  This
fraction-free imaginary-coordinate form avoids a field or choice shortcut. -/
theorem mul_conj_im_eq_normSq_mul_div_im (value scalar : Gaussian)
    (scalarNonzero : scalar ≠ 0) :
    (value * RFAP.ConstructiveGaussian.Gaussian.conj scalar).im =
      RFAP.ConstructiveGaussian.Gaussian.normSq scalar *
        (value / scalar).im := by
  have quotientCancel : (value / scalar) * scalar = value := by
    change (value * scalar⁻¹) * scalar = value
    calc
      (value * scalar⁻¹) * scalar =
          value * (scalar⁻¹ * scalar) :=
        RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
      _ = value * 1 := by
        rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq,
          RFAP.ConstructiveGaussian.Gaussian.inv_mul scalar scalarNonzero]
      _ = value := RFAP.ConstructiveGaussian.Gaussian.mul_one _
  have gaussianIdentity :
      gaussianOfRational
            (RFAP.ConstructiveGaussian.Gaussian.normSq scalar) *
          (value / scalar) =
        value * RFAP.ConstructiveGaussian.Gaussian.conj scalar := by
    apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
      scalarNonzero
    calc
      (gaussianOfRational
            (RFAP.ConstructiveGaussian.Gaussian.normSq scalar) *
          (value / scalar)) * scalar =
          gaussianOfRational
              (RFAP.ConstructiveGaussian.Gaussian.normSq scalar) *
            ((value / scalar) * scalar) :=
        RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _
      _ = gaussianOfRational
            (RFAP.ConstructiveGaussian.Gaussian.normSq scalar) * value := by
        rw [quotientCancel]
      _ = value * gaussianOfRational
            (RFAP.ConstructiveGaussian.Gaussian.normSq scalar) :=
        RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
      _ = value *
            (RFAP.ConstructiveGaussian.Gaussian.conj scalar * scalar) := by
        have scalarNorm :
            RFAP.ConstructiveGaussian.Gaussian.conj scalar * scalar =
              gaussianOfRational
                (RFAP.ConstructiveGaussian.Gaussian.normSq scalar) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext
          · simp only [RFAP.ConstructiveGaussian.Gaussian.conj,
              RFAP.ConstructiveGaussian.Gaussian.mul_re,
              RFAP.ConstructiveGaussian.Gaussian.normSq,
              gaussianOfRational]
            ring1
          · simp only [RFAP.ConstructiveGaussian.Gaussian.conj,
              RFAP.ConstructiveGaussian.Gaussian.mul_im,
              gaussianOfRational]
            ring1
        rw [scalarNorm]
      _ = (value * RFAP.ConstructiveGaussian.Gaussian.conj scalar) * scalar :=
        (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm
  have imaginaryIdentity := congrArg
    RFAP.ConstructiveGaussian.Gaussian.im gaussianIdentity
  change RFAP.ConstructiveGaussian.Gaussian.normSq scalar *
      (value / scalar).im + 0 * (value / scalar).re =
    (value * RFAP.ConstructiveGaussian.Gaussian.conj scalar).im at imaginaryIdentity
  rw [RFAP.ConstructiveFraction.zero_mul_direct, _root_.add_zero] at imaginaryIdentity
  exact imaginaryIdentity.symm

/-- The fraction-free numerator form is the normalized imaginary quadratic
form multiplied by the strictly positive squared inverse scalar. -/
theorem scaledImaginaryQuadraticForm_eq_normSq_mul {size : Nat}
    (vector : RationalVector size) (scalar : Gaussian)
    (numerator : GaussianMatrix size) (scalarNonzero : scalar ≠ 0) :
    scaledImaginaryQuadraticForm vector scalar numerator =
      RFAP.ConstructiveGaussian.Gaussian.normSq scalar *
        imaginaryQuadraticForm vector
          (divideGaussianMatrix numerator scalar) := by
  unfold scaledImaginaryQuadraticForm
  calc
    RFAP.ConstructiveFiniteMatrix.sumFin (fun row =>
        RFAP.ConstructiveFiniteMatrix.sumFin (fun column =>
          vector row *
            (numerator row column *
              RFAP.ConstructiveGaussian.Gaussian.conj scalar).im *
                vector column)) =
        RFAP.ConstructiveFiniteMatrix.sumFin (fun row =>
          RFAP.ConstructiveFiniteMatrix.sumFin (fun column =>
            RFAP.ConstructiveGaussian.Gaussian.normSq scalar *
              (vector row * (numerator row column / scalar).im *
                vector column))) := by
      apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
      intro row
      apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
      intro column
      rw [mul_conj_im_eq_normSq_mul_div_im _ _ scalarNonzero]
      ring1
    _ = RFAP.ConstructiveFiniteMatrix.sumFin (fun row =>
          RFAP.ConstructiveGaussian.Gaussian.normSq scalar *
            RFAP.ConstructiveFiniteMatrix.sumFin (fun column =>
              vector row * (numerator row column / scalar).im *
                vector column)) := by
      apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
      intro row
      exact RFAP.ConstructiveFiniteMatrix.sumFin_mul_left _ _
    _ = RFAP.ConstructiveGaussian.Gaussian.normSq scalar *
          RFAP.ConstructiveFiniteMatrix.sumFin (fun row =>
            RFAP.ConstructiveFiniteMatrix.sumFin (fun column =>
              vector row * (numerator row column / scalar).im *
                vector column)) :=
      RFAP.ConstructiveFiniteMatrix.sumFin_mul_left _ _
    _ = RFAP.ConstructiveGaussian.Gaussian.normSq scalar *
          imaginaryQuadraticForm vector
            (divideGaussianMatrix numerator scalar) := by
      congr 1
      unfold imaginaryQuadraticForm
      apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
      intro row
      apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
      intro column
      rw [divideGaussianMatrix_apply]

theorem pairingSummand_scaled (value scalar : Gaussian)
    (coefficient : Coordinate) :
    (value * RFAP.ConstructiveGaussian.Gaussian.conj
          (gaussianOfRational coefficient * scalar) -
        (gaussianOfRational coefficient * scalar) *
          RFAP.ConstructiveGaussian.Gaussian.conj value).im =
      2 * coefficient *
        (value * RFAP.ConstructiveGaussian.Gaussian.conj scalar).im := by
  simp only [gaussianOfRational,
    RFAP.ConstructiveGaussian.Gaussian.sub_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.conj]
  ring1

theorem vectorMatrix_mul_conj_im {size : Nat}
    (vector : RationalVector size) (matrix : GaussianMatrix size)
    (scalar : Gaussian) (column : Fin size) :
    (RFAP.ConstructiveFiniteMatrix.vectorMatrix
          (gaussianVectorOfRational vector) matrix column *
        RFAP.ConstructiveGaussian.Gaussian.conj scalar).im =
      RFAP.ConstructiveFiniteMatrix.sumFin fun row =>
        vector row *
          (matrix row column *
            RFAP.ConstructiveGaussian.Gaussian.conj scalar).im := by
  rw [RFAP.ConstructiveFiniteMatrix.vectorMatrix_apply]
  rw [← RFAP.ConstructiveFiniteMatrix.sumFin_mul_right]
  rw [sumFin_im]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro row
  rw [gaussianVectorOfRational_apply]
  simp only [gaussianOfRational,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.conj]
  ring1

theorem periodCombination_scaled_a {size : Nat}
    (vector : RationalVector size) (aMatrix : GaussianMatrix size)
    (inverse : RFAP.ConstructiveFiniteMatrix.ScaledInverse aMatrix) :
    periodCombination
        (RFAP.ConstructiveFiniteMatrix.vectorMatrix
          (gaussianVectorOfRational vector) inverse.inverse) aMatrix =
      RFAP.ConstructiveFiniteMatrix.vectorOfFn fun cycle =>
        gaussianVectorOfRational vector cycle * inverse.scalar := by
  unfold periodCombination
  calc
    RFAP.ConstructiveFiniteMatrix.vectorMatrix
        (RFAP.ConstructiveFiniteMatrix.vectorMatrix
          (gaussianVectorOfRational vector) inverse.inverse) aMatrix =
        RFAP.ConstructiveFiniteMatrix.vectorMatrix
          (gaussianVectorOfRational vector)
            (RFAP.ConstructiveFiniteMatrix.mul inverse.inverse aMatrix) :=
      (RFAP.ConstructiveFiniteMatrix.vectorMatrix_mul
        (gaussianVectorOfRational vector) inverse.inverse aMatrix).symm
    _ = RFAP.ConstructiveFiniteMatrix.vectorMatrix
          (gaussianVectorOfRational vector)
            (RFAP.ConstructiveFiniteMatrix.scaleIdentity inverse.scalar) := by
      rw [inverse.left_identity]
    _ = RFAP.ConstructiveFiniteMatrix.vectorOfFn fun cycle =>
          gaussianVectorOfRational vector cycle * inverse.scalar :=
      RFAP.ConstructiveFiniteMatrix.vectorMatrix_scaleIdentity
        (gaussianVectorOfRational vector) inverse.scalar

theorem periodCombination_scaled_b {size : Nat}
    (vector : RationalVector size) (aMatrix bMatrix : GaussianMatrix size)
    (inverse : RFAP.ConstructiveFiniteMatrix.ScaledInverse aMatrix) :
    periodCombination
        (RFAP.ConstructiveFiniteMatrix.vectorMatrix
          (gaussianVectorOfRational vector) inverse.inverse) bMatrix =
      RFAP.ConstructiveFiniteMatrix.vectorMatrix
        (gaussianVectorOfRational vector)
          (RFAP.ConstructiveFiniteMatrix.mul inverse.inverse bMatrix) := by
  unfold periodCombination
  exact (RFAP.ConstructiveFiniteMatrix.vectorMatrix_mul
    (gaussianVectorOfRational vector) inverse.inverse bMatrix).symm

/-- Exact finite second-relation transport before scalar division.  The raw
energy of the adjugate-scaled differential combination is precisely the
imaginary numerator form of the normalized vector. -/
theorem unnormalizedEnergyForm_scaledCoefficients {size : Nat}
    (vector : RationalVector size) (aMatrix bMatrix : GaussianMatrix size)
    (inverse : RFAP.ConstructiveFiniteMatrix.ScaledInverse aMatrix) :
    unnormalizedEnergyForm
        (RFAP.ConstructiveFiniteMatrix.vectorMatrix
          (gaussianVectorOfRational vector) inverse.inverse)
          aMatrix bMatrix =
      scaledImaginaryQuadraticForm vector inverse.scalar
        (RFAP.ConstructiveFiniteMatrix.mul inverse.inverse bMatrix) := by
  unfold unnormalizedEnergyForm
  rw [periodCombination_scaled_a vector aMatrix inverse,
    periodCombination_scaled_b vector aMatrix bMatrix inverse]
  unfold periodPairingEnergy scaledImaginaryQuadraticForm
  have summandIdentity : forall cycle,
      (RFAP.ConstructiveFiniteMatrix.vectorMatrix
            (gaussianVectorOfRational vector)
              (RFAP.ConstructiveFiniteMatrix.mul inverse.inverse bMatrix)
                cycle *
          RFAP.ConstructiveGaussian.Gaussian.conj
            (RFAP.ConstructiveFiniteMatrix.vectorOfFn
              (fun entry => gaussianVectorOfRational vector entry *
                inverse.scalar) cycle) -
        RFAP.ConstructiveFiniteMatrix.vectorOfFn
            (fun entry => gaussianVectorOfRational vector entry *
              inverse.scalar) cycle *
          RFAP.ConstructiveGaussian.Gaussian.conj
            (RFAP.ConstructiveFiniteMatrix.vectorMatrix
              (gaussianVectorOfRational vector)
                (RFAP.ConstructiveFiniteMatrix.mul inverse.inverse bMatrix)
                  cycle)).im =
        2 * RFAP.ConstructiveFiniteMatrix.sumFin (fun row =>
          vector row *
            ((RFAP.ConstructiveFiniteMatrix.mul inverse.inverse bMatrix)
              row cycle *
                RFAP.ConstructiveGaussian.Gaussian.conj inverse.scalar).im *
                  vector cycle) := by
    intro cycle
    rw [RFAP.ConstructiveFiniteMatrix.vectorOfFn_apply,
      gaussianVectorOfRational_apply]
    rw [pairingSummand_scaled]
    rw [vectorMatrix_mul_conj_im]
    rw [RFAP.ConstructiveFiniteMatrix.sumFin_mul_right]
    ring1
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_congr summandIdentity]
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_mul_left]
  have divideTwo :
      (2 * RFAP.ConstructiveFiniteMatrix.sumFin (fun cycle =>
        RFAP.ConstructiveFiniteMatrix.sumFin (fun row =>
          vector row *
            ((RFAP.ConstructiveFiniteMatrix.mul inverse.inverse bMatrix)
              row cycle *
                RFAP.ConstructiveGaussian.Gaussian.conj inverse.scalar).im *
                  vector cycle))) / 2 =
        RFAP.ConstructiveFiniteMatrix.sumFin (fun cycle =>
          RFAP.ConstructiveFiniteMatrix.sumFin (fun row =>
            vector row *
              ((RFAP.ConstructiveFiniteMatrix.mul inverse.inverse bMatrix)
                row cycle *
                  RFAP.ConstructiveGaussian.Gaussian.conj inverse.scalar).im *
                    vector cycle)) := by
    let total := RFAP.ConstructiveFiniteMatrix.sumFin (fun cycle =>
      RFAP.ConstructiveFiniteMatrix.sumFin (fun row =>
        vector row *
          ((RFAP.ConstructiveFiniteMatrix.mul inverse.inverse bMatrix)
            row cycle *
              RFAP.ConstructiveGaussian.Gaussian.conj inverse.scalar).im *
                vector cycle))
    have divideOne : total / 1 = total := by
      have cancel := RFAP.ConstructiveFraction.div_mul_cancel_of_ne
        total 1 (by decide)
      rw [RFAP.ConstructiveFraction.mul_one_direct] at cancel
      exact cancel
    calc
      (2 * total) / 2 = (2 * total) / (2 * 1) := by
        rw [RFAP.ConstructiveFraction.mul_one_direct]
      _ = total / 1 :=
        RFAP.ConstructiveFraction.mul_div_mul_left_direct 2 total 1 (by decide)
      _ = total := divideOne
  rw [divideTwo]
  exact RFAP.ConstructiveFiniteMatrix.sumFin_swap _

/-- Complete exact transport from the raw second-bilinear energy to the
normalized finite matrix obtained from the same synchronized A/B sample. -/
theorem unnormalizedEnergyForm_scaledCoefficients_eq_normSq_mul
    {size : Nat} (vector : RationalVector size)
    (aMatrix bMatrix : GaussianMatrix size)
    (inverse : RFAP.ConstructiveFiniteMatrix.ScaledInverse aMatrix)
    (scalarNonzero : inverse.scalar ≠ 0) :
    unnormalizedEnergyForm
        (RFAP.ConstructiveFiniteMatrix.vectorMatrix
          (gaussianVectorOfRational vector) inverse.inverse)
          aMatrix bMatrix =
      RFAP.ConstructiveGaussian.Gaussian.normSq inverse.scalar *
        imaginaryQuadraticForm vector
          (divideGaussianMatrix
            (RFAP.ConstructiveFiniteMatrix.mul inverse.inverse bMatrix)
            inverse.scalar) := by
  rw [unnormalizedEnergyForm_scaledCoefficients]
  exact scaledImaginaryQuadraticForm_eq_normSq_mul vector inverse.scalar
    (RFAP.ConstructiveFiniteMatrix.mul inverse.inverse bMatrix) scalarNonzero

/-- Strict raw surface energy therefore gives strict positivity of the exact
normalized finite quotient at that same sample.  Cancellation uses only the
displayed nonnegative squared norm, not an abstract eigenvalue argument. -/
theorem imaginaryQuadraticForm_divide_positive_of_unnormalized
    {size : Nat} (vector : RationalVector size)
    (aMatrix bMatrix : GaussianMatrix size)
    (inverse : RFAP.ConstructiveFiniteMatrix.ScaledInverse aMatrix)
    (scalarNonzero : inverse.scalar ≠ 0)
    (rawPositive : 0 < unnormalizedEnergyForm
      (RFAP.ConstructiveFiniteMatrix.vectorMatrix
        (gaussianVectorOfRational vector) inverse.inverse)
        aMatrix bMatrix) :
    0 < imaginaryQuadraticForm vector
      (divideGaussianMatrix
        (RFAP.ConstructiveFiniteMatrix.mul inverse.inverse bMatrix)
        inverse.scalar) := by
  have productPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq inverse.scalar *
        imaginaryQuadraticForm vector
          (divideGaussianMatrix
            (RFAP.ConstructiveFiniteMatrix.mul inverse.inverse bMatrix)
            inverse.scalar) := by
    rw [← unnormalizedEnergyForm_scaledCoefficients_eq_normSq_mul
      vector aMatrix bMatrix inverse scalarNonzero]
    exact rawPositive
  exact RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct productPositive
    (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg inverse.scalar)

/-- One finite second-relation request stated entirely for the raw A/B period
matrices.  It therefore precedes, rather than assumes, construction of A⁻¹. -/
structure UnnormalizedRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) (coefficients : GaussianVector genus)
    (_nonzero : NonzeroGaussianVector coefficients)
    (target : Coordinate) (_positive : 0 < target) where
  refinementRadius : Coordinate
  refinementRadiusPositive : 0 < refinementRadius
  refinementTarget_lt_target :
    CCL.Riemann.FinitePositivity.squaredRefinementTarget refinementRadius <
      target
  cellCount : Nat
  cells : Fin cellCount -> Cell
  positiveCell : Fin cellCount
  positiveCell_area : 0 < (cells positiveCell).areaLower
  positiveCell_density : 0 < (cells positiveCell).densityLower
  energy_le_periodPairing :
    cellEnergy cells <= unnormalizedEnergyForm coefficients
      (data.aCenterMatrix
        (CCL.Riemann.FinitePositivity.squaredRefinementTarget refinementRadius)
        (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
          refinementRadiusPositive))
      (data.bCenterMatrix
        (CCL.Riemann.FinitePositivity.squaredRefinementTarget refinementRadius)
        (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
          refinementRadiusPositive))

namespace UnnormalizedRequestCertificate

theorem energy_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : GaussianVector genus}
    {nonzero : NonzeroGaussianVector coefficients}
    {target : Coordinate} {positive : 0 < target}
    (certificate :
      UnnormalizedRequestCertificate data coefficients nonzero target positive) :
    0 < cellEnergy certificate.cells :=
  cellEnergy_positive_of_cell certificate.cells certificate.positiveCell
    certificate.positiveCell_area certificate.positiveCell_density

/-- The raw finite A/B period pairing is strictly positive before any inverse
or normalized period matrix has been introduced. -/
theorem periodPairing_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : GaussianVector genus}
    {nonzero : NonzeroGaussianVector coefficients}
    {target : Coordinate} {positive : 0 < target}
    (certificate :
      UnnormalizedRequestCertificate data coefficients nonzero target positive) :
    0 < unnormalizedEnergyForm coefficients
      (data.aCenterMatrix
        (CCL.Riemann.FinitePositivity.squaredRefinementTarget
          certificate.refinementRadius)
        (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
          certificate.refinementRadiusPositive))
      (data.bCenterMatrix
        (CCL.Riemann.FinitePositivity.squaredRefinementTarget
          certificate.refinementRadius)
        (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
          certificate.refinementRadiusPositive)) :=
  certificate.energy_positive.trans_le certificate.energy_le_periodPairing

/-- A nonzero differential combination cannot have every displayed A-period
equal to zero: that would force its positive boundary energy to be zero. -/
theorem not_all_aPeriods_zero {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : GaussianVector genus}
    {nonzero : NonzeroGaussianVector coefficients}
    {target : Coordinate} {positive : 0 < target}
    (certificate :
      UnnormalizedRequestCertificate data coefficients nonzero target positive) :
    ¬ forall cycle : Fin genus,
      periodCombination coefficients
        (data.aCenterMatrix
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget
            certificate.refinementRadius)
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)) cycle = 0 := by
  intro allZero
  have pairingZero := unnormalizedEnergyForm_eq_zero_of_aPeriods_zero
    coefficients
    (data.aCenterMatrix
      (CCL.Riemann.FinitePositivity.squaredRefinementTarget
        certificate.refinementRadius)
      (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
        certificate.refinementRadiusPositive))
    (data.bCenterMatrix
      (CCL.Riemann.FinitePositivity.squaredRefinementTarget
        certificate.refinementRadius)
      (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
        certificate.refinementRadiusPositive)) allZero
  have pairingPositive := certificate.periodPairing_positive
  rw [pairingZero] at pairingPositive
  exact lt_irrefl 0 pairingPositive

/-- Constructively expose a displayed A-cycle on which the nonzero
differential combination has nonzero finite A-period centre. -/
theorem exists_aPeriod_ne_zero {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} {coefficients : GaussianVector genus}
    {nonzero : NonzeroGaussianVector coefficients}
    {target : Coordinate} {positive : 0 < target}
    (certificate :
      UnnormalizedRequestCertificate data coefficients nonzero target positive) :
    ∃ cycle : Fin genus,
      periodCombination coefficients
        (data.aCenterMatrix
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget
            certificate.refinementRadius)
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)) cycle ≠ 0 :=
  exists_ne_zero_of_not_all_zero _ certificate.not_all_aPeriods_zero

end UnnormalizedRequestCertificate

/-- Pointwise pre-normalization energy evidence for every displayed nonzero
Gaussian-rational differential combination. -/
structure UnnormalizedCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) where
  certify : forall (coefficients : GaussianVector genus)
    (nonzero : NonzeroGaussianVector coefficients) (target : Coordinate)
    (positive : 0 < target),
    UnnormalizedRequestCertificate data coefficients nonzero target positive

namespace UnnormalizedCertificate

/-- Feed one normalized rational vector through a synchronized adjugate
sample and into the pre-normalization energy oracle.  Its nonzero witness is
derived from the scaled identity and scalar lower certificate. -/
def certifyScaledNormalized {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve} (certificate : UnnormalizedCertificate data)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (index : Nat) (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) (target : Coordinate)
    (positive : 0 < target) :
    UnnormalizedRequestCertificate data
      (scaledNormalizedCoefficients data index vector)
      (scaledNormalizedCoefficients_nonzero data inverseLower index
        vector nonzero) target positive :=
  certificate.certify (scaledNormalizedCoefficients data index vector)
    (scaledNormalizedCoefficients_nonzero data inverseLower index
      vector nonzero) target positive

end UnnormalizedCertificate

/-- Finite positive-energy evidence for one vector and precision request.
The two comparison fields are rational inequalities: the cell energy clears
the matrix enclosure error and is a certified lower bound for the displayed
quadratic form. -/
structure RequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (vector : RationalVector genus) (_nonzero : NonzeroVector vector)
    (target : Coordinate) (_positive : 0 < target) where
  refinementRadius : Coordinate
  refinementRadiusPositive : 0 < refinementRadius
  refinementTarget_lt_target :
    CCL.Riemann.FinitePositivity.squaredRefinementTarget refinementRadius <
      target
  cellCount : Nat
  cells : Fin cellCount -> Cell
  positiveCell : Fin cellCount
  positiveCell_area : 0 < (cells positiveCell).areaLower
  positiveCell_density : 0 < (cells positiveCell).densityLower
  budget_lt_energy :
    CCL.Riemann.FinitePositivity.totalBudget
      (CCL.Riemann.FinitePositivity.automaticBudget vector
        (CCL.Riemann.FinitePositivity.automaticRadius data refinementRadius
          refinementRadiusPositive)) <
      cellEnergy cells
  energy_le_center :
    cellEnergy cells <= imaginaryQuadraticForm vector
      (CCL.Riemann.FinitePositivity.centerMatrix data
        (CCL.Riemann.FinitePositivity.squaredRefinementTarget
          refinementRadius)
        (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
          refinementRadiusPositive))

namespace RequestCertificate

/-- The distinguished cell and nonnegativity of every other contribution make
the complete finite energy sum strictly positive. -/
theorem energy_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : RequestCertificate data vector nonzero target positive) :
    0 < cellEnergy certificate.cells :=
  cellEnergy_positive_of_cell certificate.cells certificate.positiveCell
    certificate.positiveCell_area certificate.positiveCell_density

/-- The finite energy comparisons imply the strict centre-versus-budget
margin consumed by the rational robustness theorem. -/
def toMarginCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : RequestCertificate data vector nonzero target positive) :
    CCL.Riemann.FinitePositivity.MarginCertificate
      data vector nonzero target positive where
  refinementRadius := certificate.refinementRadius
  refinementRadiusPositive := certificate.refinementRadiusPositive
  refinementTarget_lt_target := certificate.refinementTarget_lt_target
  center_exceeds_budget :=
    certificate.budget_lt_energy.trans_le certificate.energy_le_center

end RequestCertificate

/-- Pointwise finite positive-energy data for every nonzero rational vector
and positive refinement request. -/
structure Certificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve) where
  certify : forall (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) (target : Coordinate)
    (positive : 0 < target),
    RequestCertificate data vector nonzero target positive

namespace Certificate

/-- Derive the normalized-matrix robustness certificate from finite cell
energy at every request. -/
def toPositivity {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve} (certificate : Certificate data) :
    CCL.Riemann.FinitePositivity.Certificate data where
  certify := fun vector nonzero target positive =>
    (certificate.certify vector nonzero target positive).toMarginCertificate

end Certificate

/-! ## Finite transport from raw energy to persistent normalized positivity -/

/-- The normalized period package determined by the displayed finite scalar
lower certificate. -/
def normalizedData {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    NormalizedPeriodData curve where
  toPeriodData := data
  aInverse := inverseLower.toScaledInverseCertificate

/-- Complete fraction-free inverse of one synchronized finite A-period
sample. -/
def synchronizedScaledInverse {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) (index : Nat) :
    RFAP.ConstructiveFiniteMatrix.ScaledInverse
      (sampledMatrix data.aMatrix index) :=
  CCL.Riemann.PivotedScaledInverse.completeScaledInverse
    (sampledMatrix data.aMatrix index)

/-- Exact normalized Gaussian-rational matrix computed at the same raw A/B
sample index. -/
def synchronizedNormalizedMatrix {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) (index : Nat) : GaussianMatrix genus :=
  let inverse := synchronizedScaledInverse data index
  divideGaussianMatrix
    (RFAP.ConstructiveFiniteMatrix.mul inverse.inverse
      (sampledMatrix data.bMatrix index)) inverse.scalar

/-- The scalar lower certificate separates the complete inverse scalar at
every synchronized finite raw sample. -/
theorem synchronizedScaledInverse_scalar_nonzero {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (index : Nat) :
    (synchronizedScaledInverse data index).scalar ≠ 0 := by
  let inverse := synchronizedScaledInverse data index
  have scalarSample :
      (canonicalScaledInverse data.aMatrix).scalar.sample index =
        inverse.scalar := by
    unfold canonicalScaledInverse inverse synchronizedScaledInverse
    have samples :=
      CCL.Riemann.PivotedScaledInverse.completeApproximation_sample
        (geometricMatrixOfNamed data.aMatrix) index
    rw [sample_geometricMatrixOfNamed] at samples
    exact samples.1
  intro scalarZero
  apply inverseLower.sample_scalar_nonzero index
  rw [scalarSample, scalarZero]

/-- Raw cell energy divided by the positive squared scaled-inverse scalar is
the corresponding lower bound in normalized coordinates. -/
def synchronizedNormalizedEnergyLower {genus cellCount : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) (index : Nat)
    (cells : Fin cellCount → Cell) : Coordinate :=
  cellEnergy cells /
    RFAP.ConstructiveGaussian.Gaussian.normSq
      (synchronizedScaledInverse data index).scalar

/-- One auditable finite bridge request.  Its surface cells bound the raw
second-bilinear energy at a synchronized A/B sample.  A separate rational
entrywise comparison then connects the exact quotient of that same sample to
one persistent normalized centre.  The sole strict margin pays for both this
transport and the public output box. -/
structure TransportRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (vector : RationalVector genus) (_nonzero : NonzeroVector vector)
    (target : Coordinate) (_positive : 0 < target) where
  sampleIndex : Nat
  cellCount : Nat
  cells : Fin cellCount → Cell
  positiveCell : Fin cellCount
  positiveCell_area : 0 < (cells positiveCell).areaLower
  positiveCell_density : 0 < (cells positiveCell).densityLower
  energy_le_raw :
    cellEnergy cells <= unnormalizedEnergyForm
      (scaledNormalizedCoefficients data sampleIndex vector)
      (sampledMatrix data.aMatrix sampleIndex)
      (sampledMatrix data.bMatrix sampleIndex)
  refinementRadius : Coordinate
  refinementRadiusPositive : 0 < refinementRadius
  refinementTarget_lt_target :
    CCL.Riemann.FinitePositivity.squaredRefinementTarget refinementRadius <
      target
  comparisonRadius : Coordinate
  comparisonRadiusPositive : 0 < comparisonRadius
  synchronized_close : forall row column : Fin genus,
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePositivity.centerMatrix
            (normalizedData data inverseLower)
            (CCL.Riemann.FinitePositivity.squaredRefinementTarget
              refinementRadius)
            (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
              refinementRadiusPositive) row column -
          synchronizedNormalizedMatrix data sampleIndex row column) <
      comparisonRadius ^ 2
  margin :
    CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius
              (normalizedData data inverseLower) refinementRadius
              refinementRadiusPositive)) +
        CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius
              (normalizedData data inverseLower) comparisonRadius
              comparisonRadiusPositive)) <
      synchronizedNormalizedEnergyLower data sampleIndex cells

namespace TransportRequestCertificate

def outputBudget {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TransportRequestCertificate data inverseLower vector
      nonzero target positive) : Coordinate :=
  CCL.Riemann.FinitePositivity.totalBudget
    (CCL.Riemann.FinitePositivity.automaticBudget vector
      (CCL.Riemann.FinitePositivity.automaticRadius
        (normalizedData data inverseLower) certificate.refinementRadius
        certificate.refinementRadiusPositive))

def comparisonBudget {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TransportRequestCertificate data inverseLower vector
      nonzero target positive) : Coordinate :=
  CCL.Riemann.FinitePositivity.totalBudget
    (CCL.Riemann.FinitePositivity.automaticBudget vector
      (CCL.Riemann.FinitePositivity.automaticRadius
        (normalizedData data inverseLower) certificate.comparisonRadius
        certificate.comparisonRadiusPositive))

/-- The part of the normalized raw-cell lower bound left after paying for
the exact-quotient-to-centre comparison. -/
def transportedEnergy {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TransportRequestCertificate data inverseLower vector
      nonzero target positive) : Coordinate :=
  synchronizedNormalizedEnergyLower data certificate.sampleIndex
      certificate.cells -
    certificate.comparisonBudget

theorem rawCellEnergy_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TransportRequestCertificate data inverseLower vector
      nonzero target positive) :
    0 < cellEnergy certificate.cells :=
  cellEnergy_positive_of_cell certificate.cells certificate.positiveCell
    certificate.positiveCell_area certificate.positiveCell_density

theorem normalizedEnergyLower_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TransportRequestCertificate data inverseLower vector
      nonzero target positive) :
    0 < synchronizedNormalizedEnergyLower data certificate.sampleIndex
      certificate.cells := by
  unfold synchronizedNormalizedEnergyLower
  exact RFAP.ConstructiveFraction.div_pos_direct
    certificate.rawCellEnergy_positive
    (RFAP.ConstructiveGaussian.Gaussian.normSq_pos
      (synchronizedScaledInverse_scalar_nonzero data inverseLower
        certificate.sampleIndex))

/-- Exact normalization turns the raw cell bound into a lower bound for the
synchronized normalized quadratic form. -/
theorem normalizedEnergyLower_le_exact {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TransportRequestCertificate data inverseLower vector
      nonzero target positive) :
    synchronizedNormalizedEnergyLower data certificate.sampleIndex
        certificate.cells <=
      imaginaryQuadraticForm vector
        (synchronizedNormalizedMatrix data certificate.sampleIndex) := by
  let inverse := synchronizedScaledInverse data certificate.sampleIndex
  have scalarNonzero : inverse.scalar ≠ 0 :=
    synchronizedScaledInverse_scalar_nonzero data inverseLower
      certificate.sampleIndex
  have scalarNormPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq inverse.scalar :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_pos scalarNonzero
  apply (RFAP.ConstructiveFraction.div_le_iff_pos scalarNormPositive).2
  calc
    cellEnergy certificate.cells <=
        unnormalizedEnergyForm
          (scaledNormalizedCoefficients data certificate.sampleIndex vector)
          (sampledMatrix data.aMatrix certificate.sampleIndex)
          (sampledMatrix data.bMatrix certificate.sampleIndex) :=
      certificate.energy_le_raw
    _ = RFAP.ConstructiveGaussian.Gaussian.normSq inverse.scalar *
          imaginaryQuadraticForm vector
            (synchronizedNormalizedMatrix data certificate.sampleIndex) := by
      simpa only [scaledNormalizedCoefficients, synchronizedScaledInverse,
        synchronizedNormalizedMatrix, inverse] using
        unnormalizedEnergyForm_scaledCoefficients_eq_normSq_mul vector
          (sampledMatrix data.aMatrix certificate.sampleIndex)
          (sampledMatrix data.bMatrix certificate.sampleIndex) inverse
          scalarNonzero
    _ = imaginaryQuadraticForm vector
          (synchronizedNormalizedMatrix data certificate.sampleIndex) *
            RFAP.ConstructiveGaussian.Gaussian.normSq inverse.scalar :=
      RFAP.ConstructiveFraction.mul_comm _ _

theorem outputBudget_nonnegative {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TransportRequestCertificate data inverseLower vector
      nonzero target positive) :
    0 <= certificate.outputBudget := by
  unfold outputBudget
  apply CCL.Riemann.FinitePositivity.totalAutomaticBudget_nonnegative
  intro row column
  exact (CCL.Riemann.FinitePositivity.automaticRadius_positive
    (normalizedData data inverseLower) certificate.refinementRadius
    certificate.refinementRadiusPositive row column).le

theorem comparisonBudget_nonnegative {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TransportRequestCertificate data inverseLower vector
      nonzero target positive) :
    0 <= certificate.comparisonBudget := by
  unfold comparisonBudget
  apply CCL.Riemann.FinitePositivity.totalAutomaticBudget_nonnegative
  intro row column
  exact (CCL.Riemann.FinitePositivity.automaticRadius_positive
    (normalizedData data inverseLower) certificate.comparisonRadius
    certificate.comparisonRadiusPositive row column).le

/-- The explicit entrywise comparison pays exactly its automatic finite
budget when transporting the exact normalized sample to the persistent
centre matrix. -/
theorem exact_sub_comparisonBudget_le_center {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TransportRequestCertificate data inverseLower vector
      nonzero target positive) :
    imaginaryQuadraticForm vector
          (synchronizedNormalizedMatrix data certificate.sampleIndex) -
        certificate.comparisonBudget <=
      imaginaryQuadraticForm vector
        (CCL.Riemann.FinitePositivity.centerMatrix
          (normalizedData data inverseLower)
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget
            certificate.refinementRadius)
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)) := by
  unfold comparisonBudget
  exact CCL.Riemann.FinitePositivity.imaginaryQuadraticForm_sub_automaticBudget_le
      vector
      (synchronizedNormalizedMatrix data certificate.sampleIndex)
      (CCL.Riemann.FinitePositivity.centerMatrix
        (normalizedData data inverseLower)
        (CCL.Riemann.FinitePositivity.squaredRefinementTarget
          certificate.refinementRadius)
        (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
          certificate.refinementRadiusPositive))
      (CCL.Riemann.FinitePositivity.automaticRadius
        (normalizedData data inverseLower) certificate.comparisonRadius
        certificate.comparisonRadiusPositive)
      (CCL.Riemann.FinitePositivity.automaticRadius_positive
        (normalizedData data inverseLower) certificate.comparisonRadius
        certificate.comparisonRadiusPositive)
      (by
        intro row column
        simpa only [CCL.Riemann.FinitePositivity.automaticRadius_apply] using
          certificate.synchronized_close row column)

theorem transportedEnergy_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TransportRequestCertificate data inverseLower vector
      nonzero target positive) :
    0 < certificate.transportedEnergy := by
  apply RFAP.ConstructiveFraction.sub_pos_direct
  have comparisonLeSum : certificate.comparisonBudget <=
      certificate.outputBudget + certificate.comparisonBudget := by
    calc
      certificate.comparisonBudget =
          0 + certificate.comparisonBudget :=
        (RFAP.ConstructiveFraction.zero_add _).symm
      _ <= certificate.outputBudget + certificate.comparisonBudget :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          certificate.outputBudget_nonnegative certificate.comparisonBudget
  have transportMargin :
      certificate.outputBudget + certificate.comparisonBudget <
        synchronizedNormalizedEnergyLower data certificate.sampleIndex
          certificate.cells := by
    change CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius
              (normalizedData data inverseLower) certificate.refinementRadius
              certificate.refinementRadiusPositive)) +
        CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius
              (normalizedData data inverseLower) certificate.comparisonRadius
              certificate.comparisonRadiusPositive)) <
        synchronizedNormalizedEnergyLower data certificate.sampleIndex
          certificate.cells
    exact certificate.margin
  exact comparisonLeSum.trans_lt transportMargin

theorem outputBudget_lt_transportedEnergy {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TransportRequestCertificate data inverseLower vector
      nonzero target positive) :
    certificate.outputBudget < certificate.transportedEnergy := by
  have transportMargin :
      certificate.outputBudget + certificate.comparisonBudget <
        synchronizedNormalizedEnergyLower data certificate.sampleIndex
          certificate.cells := by
    change CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius
              (normalizedData data inverseLower) certificate.refinementRadius
              certificate.refinementRadiusPositive)) +
        CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius
              (normalizedData data inverseLower) certificate.comparisonRadius
              certificate.comparisonRadiusPositive)) <
        synchronizedNormalizedEnergyLower data certificate.sampleIndex
          certificate.cells
    exact certificate.margin
  have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
    transportMargin (-certificate.comparisonBudget)
  unfold transportedEnergy
  calc
    certificate.outputBudget =
        (certificate.outputBudget + certificate.comparisonBudget) +
          -certificate.comparisonBudget := by ring1
    _ < synchronizedNormalizedEnergyLower data certificate.sampleIndex
          certificate.cells + -certificate.comparisonBudget := shifted
    _ = synchronizedNormalizedEnergyLower data certificate.sampleIndex
          certificate.cells - certificate.comparisonBudget := by ring1

theorem transportedEnergy_le_center {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TransportRequestCertificate data inverseLower vector
      nonzero target positive) :
    certificate.transportedEnergy <=
      imaginaryQuadraticForm vector
        (CCL.Riemann.FinitePositivity.centerMatrix
          (normalizedData data inverseLower)
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget
            certificate.refinementRadius)
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)) := by
  unfold transportedEnergy
  calc
    synchronizedNormalizedEnergyLower data certificate.sampleIndex
          certificate.cells - certificate.comparisonBudget <=
        imaginaryQuadraticForm vector
            (synchronizedNormalizedMatrix data certificate.sampleIndex) -
          certificate.comparisonBudget := by
      rw [RFAP.ConstructiveFraction.sub_eq_add_neg_direct,
        RFAP.ConstructiveFraction.sub_eq_add_neg_direct]
      exact RFAP.ConstructiveFraction.add_le_add_right_direct
        certificate.normalizedEnergyLower_le_exact
        (-certificate.comparisonBudget)
    _ <= imaginaryQuadraticForm vector
        (CCL.Riemann.FinitePositivity.centerMatrix
          (normalizedData data inverseLower)
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget
            certificate.refinementRadius)
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)) :=
      certificate.exact_sub_comparisonBudget_le_center

/-- Aggregate the transported rational lower bound into one derived positive
cell.  Its area is not new analytic input: it is computed from the displayed
raw surface cells, scalar norm, and comparison budget. -/
def transportedCell {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TransportRequestCertificate data inverseLower vector
      nonzero target positive) : Cell where
  areaLower := certificate.transportedEnergy
  densityLower := 1
  areaLower_nonnegative := certificate.transportedEnergy_positive.le
  densityLower_nonnegative := by decide

theorem cellEnergy_singleton (cell : Cell) :
    cellEnergy (fun _ : Fin 1 => cell) = cell.contribution := by
  unfold cellEnergy
  rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ]
  change cell.contribution + 0 = cell.contribution
  rw [_root_.add_zero]

/-- Expand the raw-cell transport bridge into the established normalized
energy request interface. -/
def toRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : TransportRequestCertificate data inverseLower vector
      nonzero target positive) :
    RequestCertificate (normalizedData data inverseLower) vector nonzero
      target positive where
  refinementRadius := certificate.refinementRadius
  refinementRadiusPositive := certificate.refinementRadiusPositive
  refinementTarget_lt_target := certificate.refinementTarget_lt_target
  cellCount := 1
  cells := fun _ => certificate.transportedCell
  positiveCell := 0
  positiveCell_area := certificate.transportedEnergy_positive
  positiveCell_density := by
    change (0 : Coordinate) < 1
    decide
  budget_lt_energy := by
    rw [cellEnergy_singleton]
    unfold Cell.contribution transportedCell
    rw [RFAP.ConstructiveFraction.mul_one_direct]
    simpa only [outputBudget] using certificate.outputBudget_lt_transportedEnergy
  energy_le_center := by
    rw [cellEnergy_singleton]
    unfold Cell.contribution transportedCell
    rw [RFAP.ConstructiveFraction.mul_one_direct]
    exact certificate.transportedEnergy_le_center

end TransportRequestCertificate

/-- Pointwise raw-cell transport data for every displayed nonzero rational
vector and positive output request. -/
structure TransportCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) where
  certify : forall (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) (target : Coordinate)
    (positive : 0 < target),
    TransportRequestCertificate data inverseLower vector nonzero target positive

namespace TransportCertificate

/-- All normalized positive-energy fields are derived from raw surface cells,
exact finite normalization, and the displayed finite comparison budget. -/
def toCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    (certificate : TransportCertificate data inverseLower) :
    Certificate (normalizedData data inverseLower) where
  certify := fun vector nonzero target positive =>
    (certificate.certify vector nonzero target positive).toRequestCertificate

/-- Direct public pointwise positivity obtained from the finite transport
certificate. -/
def toPositivity {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    {inverseLower : ScalarCandidateLowerCertificate data.aMatrix}
    (certificate : TransportCertificate data inverseLower) :
    CCL.Riemann.FinitePositivity.Certificate
      (normalizedData data inverseLower) :=
  certificate.toCertificate.toPositivity

end TransportCertificate

/-! ## Presentation-independent finite energy transport -/

/-- Algebraic transport from one exact Gaussian-rational comparison matrix
to an arbitrary operational presentation of normalized period data.  The
strict lower bound is produced by the raw-sample constructor below; this
record isolates the entrywise perturbation argument so it does not depend on
how the inverse scalar was apartified. -/
structure PresentationTransportRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (vector : RationalVector genus) (_nonzero : NonzeroVector vector)
    (target : Coordinate) (_positive : 0 < target) where
  exactMatrix : GaussianMatrix genus
  energyLower : Coordinate
  energyLower_positive : 0 < energyLower
  energyLower_le_exact :
    energyLower <= imaginaryQuadraticForm vector exactMatrix
  refinementRadius : Coordinate
  refinementRadiusPositive : 0 < refinementRadius
  refinementTarget_lt_target :
    CCL.Riemann.FinitePositivity.squaredRefinementTarget refinementRadius <
      target
  comparisonRadius : Coordinate
  comparisonRadiusPositive : 0 < comparisonRadius
  exact_close : forall row column : Fin genus,
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePositivity.centerMatrix data
            (CCL.Riemann.FinitePositivity.squaredRefinementTarget
              refinementRadius)
            (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
              refinementRadiusPositive) row column -
          exactMatrix row column) <
      comparisonRadius ^ 2
  margin :
    CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius data
              refinementRadius refinementRadiusPositive)) +
        CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius data
              comparisonRadius comparisonRadiusPositive)) <
      energyLower

namespace PresentationTransportRequestCertificate

def outputBudget {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : PresentationTransportRequestCertificate data vector
      nonzero target positive) : Coordinate :=
  CCL.Riemann.FinitePositivity.totalBudget
    (CCL.Riemann.FinitePositivity.automaticBudget vector
      (CCL.Riemann.FinitePositivity.automaticRadius data
        certificate.refinementRadius certificate.refinementRadiusPositive))

def comparisonBudget {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : PresentationTransportRequestCertificate data vector
      nonzero target positive) : Coordinate :=
  CCL.Riemann.FinitePositivity.totalBudget
    (CCL.Riemann.FinitePositivity.automaticBudget vector
      (CCL.Riemann.FinitePositivity.automaticRadius data
        certificate.comparisonRadius certificate.comparisonRadiusPositive))

/-- The exact lower bound after paying for transport to the persistent
centre. -/
def transportedEnergy {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : PresentationTransportRequestCertificate data vector
      nonzero target positive) : Coordinate :=
  certificate.energyLower - certificate.comparisonBudget

theorem outputBudget_nonnegative {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : PresentationTransportRequestCertificate data vector
      nonzero target positive) :
    0 <= certificate.outputBudget := by
  unfold outputBudget
  apply CCL.Riemann.FinitePositivity.totalAutomaticBudget_nonnegative
  intro row column
  exact (CCL.Riemann.FinitePositivity.automaticRadius_positive data
    certificate.refinementRadius certificate.refinementRadiusPositive
      row column).le

theorem exact_sub_comparisonBudget_le_center {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : PresentationTransportRequestCertificate data vector
      nonzero target positive) :
    imaginaryQuadraticForm vector certificate.exactMatrix -
        certificate.comparisonBudget <=
      imaginaryQuadraticForm vector
        (CCL.Riemann.FinitePositivity.centerMatrix data
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget
            certificate.refinementRadius)
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)) := by
  unfold comparisonBudget
  exact CCL.Riemann.FinitePositivity.imaginaryQuadraticForm_sub_automaticBudget_le
    vector certificate.exactMatrix
    (CCL.Riemann.FinitePositivity.centerMatrix data
      (CCL.Riemann.FinitePositivity.squaredRefinementTarget
        certificate.refinementRadius)
      (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
        certificate.refinementRadiusPositive))
    (CCL.Riemann.FinitePositivity.automaticRadius data
      certificate.comparisonRadius certificate.comparisonRadiusPositive)
    (CCL.Riemann.FinitePositivity.automaticRadius_positive data
      certificate.comparisonRadius certificate.comparisonRadiusPositive)
    (by
      intro row column
      simpa only [CCL.Riemann.FinitePositivity.automaticRadius_apply] using
        certificate.exact_close row column)

theorem transportedEnergy_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : PresentationTransportRequestCertificate data vector
      nonzero target positive) :
    0 < certificate.transportedEnergy := by
  apply RFAP.ConstructiveFraction.sub_pos_direct
  have comparisonLeSum : certificate.comparisonBudget <=
      certificate.outputBudget + certificate.comparisonBudget := by
    calc
      certificate.comparisonBudget =
          0 + certificate.comparisonBudget :=
        (RFAP.ConstructiveFraction.zero_add _).symm
      _ <= certificate.outputBudget + certificate.comparisonBudget :=
        RFAP.ConstructiveFraction.add_le_add_right_direct
          certificate.outputBudget_nonnegative certificate.comparisonBudget
  exact comparisonLeSum.trans_lt certificate.margin

theorem outputBudget_lt_transportedEnergy {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : PresentationTransportRequestCertificate data vector
      nonzero target positive) :
    certificate.outputBudget < certificate.transportedEnergy := by
  have shifted := RFAP.ConstructiveFraction.add_lt_add_right_direct
    certificate.margin (-certificate.comparisonBudget)
  unfold transportedEnergy
  calc
    certificate.outputBudget =
        (certificate.outputBudget + certificate.comparisonBudget) +
          -certificate.comparisonBudget := by ring1
    _ < certificate.energyLower + -certificate.comparisonBudget := shifted
    _ = certificate.energyLower - certificate.comparisonBudget := by ring1

theorem transportedEnergy_le_center {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : PresentationTransportRequestCertificate data vector
      nonzero target positive) :
    certificate.transportedEnergy <=
      imaginaryQuadraticForm vector
        (CCL.Riemann.FinitePositivity.centerMatrix data
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget
            certificate.refinementRadius)
          (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
            certificate.refinementRadiusPositive)) := by
  unfold transportedEnergy
  calc
    certificate.energyLower - certificate.comparisonBudget <=
        imaginaryQuadraticForm vector certificate.exactMatrix -
          certificate.comparisonBudget := by
      rw [RFAP.ConstructiveFraction.sub_eq_add_neg_direct,
        RFAP.ConstructiveFraction.sub_eq_add_neg_direct]
      exact RFAP.ConstructiveFraction.add_le_add_right_direct
        certificate.energyLower_le_exact (-certificate.comparisonBudget)
    _ <= _ := certificate.exact_sub_comparisonBudget_le_center

def transportedCell {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : PresentationTransportRequestCertificate data vector
      nonzero target positive) : Cell where
  areaLower := certificate.transportedEnergy
  densityLower := 1
  areaLower_nonnegative := certificate.transportedEnergy_positive.le
  densityLower_nonnegative := by decide

/-- Convert the presentation-independent comparison into the public finite
cell-energy request. -/
def toRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : PresentationTransportRequestCertificate data vector
      nonzero target positive) :
    RequestCertificate data vector nonzero target positive where
  refinementRadius := certificate.refinementRadius
  refinementRadiusPositive := certificate.refinementRadiusPositive
  refinementTarget_lt_target := certificate.refinementTarget_lt_target
  cellCount := 1
  cells := fun _ => certificate.transportedCell
  positiveCell := 0
  positiveCell_area := certificate.transportedEnergy_positive
  positiveCell_density := by
    change (0 : Coordinate) < 1
    decide
  budget_lt_energy := by
    rw [TransportRequestCertificate.cellEnergy_singleton]
    unfold Cell.contribution transportedCell
    rw [RFAP.ConstructiveFraction.mul_one_direct]
    simpa only [outputBudget] using certificate.outputBudget_lt_transportedEnergy
  energy_le_center := by
    rw [TransportRequestCertificate.cellEnergy_singleton]
    unfold Cell.contribution transportedCell
    rw [RFAP.ConstructiveFraction.mul_one_direct]
    exact certificate.transportedEnergy_le_center

end PresentationTransportRequestCertificate

/-- Raw surface-cell transport to any operational normalized presentation.
The exact comparison matrix still comes from one synchronized finite A/B
sample, but scalar nonvanishing is required only at that selected sample.
This is the bridge needed by tail-separated normalization. -/
structure SampleTransportRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve)
    (vector : RationalVector genus) (_nonzero : NonzeroVector vector)
    (target : Coordinate) (_positive : 0 < target) where
  sampleIndex : Nat
  scalarNonzero :
    (synchronizedScaledInverse data.toPeriodData sampleIndex).scalar ≠ 0
  cellCount : Nat
  cells : Fin cellCount -> Cell
  positiveCell : Fin cellCount
  positiveCell_area : 0 < (cells positiveCell).areaLower
  positiveCell_density : 0 < (cells positiveCell).densityLower
  energy_le_raw :
    cellEnergy cells <= unnormalizedEnergyForm
      (scaledNormalizedCoefficients data.toPeriodData sampleIndex vector)
      (sampledMatrix data.toPeriodData.aMatrix sampleIndex)
      (sampledMatrix data.toPeriodData.bMatrix sampleIndex)
  refinementRadius : Coordinate
  refinementRadiusPositive : 0 < refinementRadius
  refinementTarget_lt_target :
    CCL.Riemann.FinitePositivity.squaredRefinementTarget refinementRadius <
      target
  comparisonRadius : Coordinate
  comparisonRadiusPositive : 0 < comparisonRadius
  synchronized_close : forall row column : Fin genus,
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (CCL.Riemann.FinitePositivity.centerMatrix data
            (CCL.Riemann.FinitePositivity.squaredRefinementTarget
              refinementRadius)
            (CCL.Riemann.FinitePositivity.squaredRefinementTarget_positive
              refinementRadiusPositive) row column -
          synchronizedNormalizedMatrix data.toPeriodData sampleIndex
            row column) <
      comparisonRadius ^ 2
  margin :
    CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius data
              refinementRadius refinementRadiusPositive)) +
        CCL.Riemann.FinitePositivity.totalBudget
          (CCL.Riemann.FinitePositivity.automaticBudget vector
            (CCL.Riemann.FinitePositivity.automaticRadius data
              comparisonRadius comparisonRadiusPositive)) <
      synchronizedNormalizedEnergyLower data.toPeriodData sampleIndex cells

namespace SampleTransportRequestCertificate

theorem normalizedEnergyLower_positive {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : SampleTransportRequestCertificate data vector nonzero
      target positive) :
    0 < synchronizedNormalizedEnergyLower data.toPeriodData
      certificate.sampleIndex certificate.cells := by
  unfold synchronizedNormalizedEnergyLower
  exact RFAP.ConstructiveFraction.div_pos_direct
    (cellEnergy_positive_of_cell certificate.cells certificate.positiveCell
      certificate.positiveCell_area certificate.positiveCell_density)
    (RFAP.ConstructiveGaussian.Gaussian.normSq_pos
      certificate.scalarNonzero)

theorem normalizedEnergyLower_le_exact {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : SampleTransportRequestCertificate data vector nonzero
      target positive) :
    synchronizedNormalizedEnergyLower data.toPeriodData
        certificate.sampleIndex certificate.cells <=
      imaginaryQuadraticForm vector
        (synchronizedNormalizedMatrix data.toPeriodData
          certificate.sampleIndex) := by
  let inverse := synchronizedScaledInverse data.toPeriodData
    certificate.sampleIndex
  have scalarNormPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq inverse.scalar :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_pos certificate.scalarNonzero
  apply (RFAP.ConstructiveFraction.div_le_iff_pos scalarNormPositive).2
  calc
    cellEnergy certificate.cells <=
        unnormalizedEnergyForm
          (scaledNormalizedCoefficients data.toPeriodData
            certificate.sampleIndex vector)
          (sampledMatrix data.toPeriodData.aMatrix certificate.sampleIndex)
          (sampledMatrix data.toPeriodData.bMatrix certificate.sampleIndex) :=
      certificate.energy_le_raw
    _ = RFAP.ConstructiveGaussian.Gaussian.normSq inverse.scalar *
          imaginaryQuadraticForm vector
            (synchronizedNormalizedMatrix data.toPeriodData
              certificate.sampleIndex) := by
      simpa only [scaledNormalizedCoefficients, synchronizedScaledInverse,
        synchronizedNormalizedMatrix, inverse] using
        unnormalizedEnergyForm_scaledCoefficients_eq_normSq_mul vector
          (sampledMatrix data.toPeriodData.aMatrix certificate.sampleIndex)
          (sampledMatrix data.toPeriodData.bMatrix certificate.sampleIndex)
          inverse certificate.scalarNonzero
    _ = imaginaryQuadraticForm vector
          (synchronizedNormalizedMatrix data.toPeriodData
            certificate.sampleIndex) *
            RFAP.ConstructiveGaussian.Gaussian.normSq inverse.scalar :=
      RFAP.ConstructiveFraction.mul_comm _ _

/-- Forget the raw normalization algebra only after deriving the exact
normalized lower bound. -/
def toPresentationTransportRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : SampleTransportRequestCertificate data vector nonzero
      target positive) :
    PresentationTransportRequestCertificate data vector nonzero target
      positive where
  exactMatrix := synchronizedNormalizedMatrix data.toPeriodData
    certificate.sampleIndex
  energyLower := synchronizedNormalizedEnergyLower data.toPeriodData
    certificate.sampleIndex certificate.cells
  energyLower_positive := certificate.normalizedEnergyLower_positive
  energyLower_le_exact := certificate.normalizedEnergyLower_le_exact
  refinementRadius := certificate.refinementRadius
  refinementRadiusPositive := certificate.refinementRadiusPositive
  refinementTarget_lt_target := certificate.refinementTarget_lt_target
  comparisonRadius := certificate.comparisonRadius
  comparisonRadiusPositive := certificate.comparisonRadiusPositive
  exact_close := certificate.synchronized_close
  margin := certificate.margin

def toRequestCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    {vector : RationalVector genus} {nonzero : NonzeroVector vector}
    {target : Coordinate} {positive : 0 < target}
    (certificate : SampleTransportRequestCertificate data vector nonzero
      target positive) :
    RequestCertificate data vector nonzero target positive :=
  certificate.toPresentationTransportRequestCertificate.toRequestCertificate

end SampleTransportRequestCertificate

/-- Pointwise raw-cell transport for an arbitrary normalized inverse
presentation, including a certified tail presentation. -/
structure SampleTransportCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : NormalizedPeriodData curve) where
  certify : forall (vector : RationalVector genus)
    (nonzero : NonzeroVector vector) (target : Coordinate)
    (positive : 0 < target),
    SampleTransportRequestCertificate data vector nonzero target positive

namespace SampleTransportCertificate

def toCertificate {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    (certificate : SampleTransportCertificate data) : Certificate data where
  certify := fun vector nonzero target positive =>
    (certificate.certify vector nonzero target positive).toRequestCertificate

end SampleTransportCertificate

end CCL.Riemann.FiniteEnergy
