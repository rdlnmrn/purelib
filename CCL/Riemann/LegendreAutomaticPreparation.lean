import CCL.Riemann.LegendrePeriodMonodromy

/-!
# Guaranteed finite preparation from one positive period enclosure

A positive imaginary lower bound is supplied once, at one finite state of
the input ratio. Every nonzero integral row then has a computable positive
norm bound. The existing apartification algorithm turns that bound into a
prepared denominator by a prescribed finite refinement, without searching.
-/

namespace CCL.Riemann.LegendreAutomaticPreparation

open CCL.Riemann.LegendreGaussManin
open CCL.Riemann.LegendreModularMonodromy
open RFAP.ConstructiveGaussian.Gaussian

abbrev Q := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev IntegralMatrix := CCL.Riemann.LegendrePicardLefschetz.IntegralMatrix

/-- One finite positive enclosure, retained with its exact source state.
Only this one positivity witness is needed for all subsequent integral rows. -/
structure PositiveEnclosure (tau : CoherentNamed) where
  state : tau.name.process.State
  lower : Q
  positive : 0 < lower
  inside_lower : forall {value : Gaussian},
    (tau.name.process.ball state).Contains value → lower ≤ value.im

namespace PositiveEnclosure

def based {tau : CoherentNamed} (certificate : PositiveEnclosure tau) :
    CoherentNamed := tau.based certificate.state

theorem possible_lower {tau : CoherentNamed}
    (certificate : PositiveEnclosure tau)
    (state : certificate.based.name.process.State) {value : Gaussian}
    (possible : certificate.based.name.process.Possible state value) :
    certificate.lower ≤ value.im :=
  certificate.inside_lower (tau.name.process.possible_inside
    (state.persists possible))

end PositiveEnclosure

/-- A directly executable affine row, with exact integral coefficients. -/
def affine (a b : Int) (tau : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (CCL.ProgressiveCoherence.CoherentNamed.exact (integralGaussian a))
    (CCL.ProgressiveCoherence.CoherentNamed.mul
      (CCL.ProgressiveCoherence.CoherentNamed.exact (integralGaussian b)) tau)

/-- The rational lower bound selected by the row coefficients. -/
def rowLower (a b : Int) (epsilon : Q) : Q :=
  if b = 0 then (a : Q) ^ 2 else (b : Q) ^ 2 * epsilon ^ 2

private theorem integer_square_positive (a : Int) (nonzero : a ≠ 0) :
    (0 : Q) < (a : Q) ^ 2 := by
  have castNonzero : (a : Q) ≠ 0 := fun equal =>
    nonzero (RFAP.ConstructiveFraction.intCast_injective_direct equal)
  have nonnegative := RFAP.ConstructiveFraction.sq_nonneg_direct (a : Q)
  exact ⟨nonnegative, fun reverse => castNonzero
    ((RFAP.ConstructiveFraction.sq_eq_zero_direct (a : Q)).mp
      (le_antisymm reverse nonnegative))⟩

theorem rowLower_positive (a b : Int) (epsilon : Q)
    (positive : 0 < epsilon) (nonzero : a ≠ 0 ∨ b ≠ 0) :
    0 < rowLower a b epsilon := by
  unfold rowLower
  split
  next equal =>
    have aNonzero : a ≠ 0 := nonzero.resolve_right (fun h => h equal)
    exact integer_square_positive a aNonzero
  next different =>
    apply RFAP.ConstructiveFraction.mul_pos_direct
    · exact integer_square_positive b different
    · exact RFAP.ConstructiveFraction.pow_pos_direct positive 2

theorem rowLower_le (a b : Int) (epsilon : Q) (value : Gaussian)
    (positive : 0 < epsilon) (lower : epsilon ≤ value.im) :
    rowLower a b epsilon ≤ normSq (integralGaussian a + integralGaussian b * value) := by
  unfold rowLower
  split
  next equal =>
    subst b
    change (a : Q) ^ 2 ≤
      ((a : Q) + (0 * value.re - 0 * value.im)) ^ 2 +
      (0 + (0 * value.im + 0 * value.re)) ^ 2
    simp only [MulZeroClass.zero_mul, _root_.sub_zero, _root_.add_zero,
      zero_pow (by decide : 2 ≠ 0)]
    exact le_rfl
  next _ =>
    have squareLe := RFAP.ConstructiveFraction.pow_le_pow_direct
      positive.le lower 2
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      squareLe (RFAP.ConstructiveFraction.sq_nonneg_direct (b : Q))
    calc
      (b : Q) ^ 2 * epsilon ^ 2 ≤ (b : Q) ^ 2 * value.im ^ 2 := scaled
      _ ≤ normSq (integralGaussian a + integralGaussian b * value) := by
        change (b : Q) ^ 2 * value.im ^ 2 ≤
          ((a : Q) + ((b : Q) * value.re - 0 * value.im)) ^ 2 +
          (0 + ((b : Q) * value.im + 0 * value.re)) ^ 2
        simp only [MulZeroClass.zero_mul, _root_.add_zero, _root_.zero_add, _root_.sub_zero]
        calc
          (b : Q) ^ 2 * value.im ^ 2 = ((b : Q) * value.im) ^ 2 := by ring1
          _ ≤ ((a : Q) + (b : Q) * value.re) ^ 2 +
              ((b : Q) * value.im) ^ 2 :=
            le_add_of_nonneg_left (RFAP.ConstructiveFraction.sq_nonneg_direct
              ((a : Q) + (b : Q) * value.re))

/-- Candidate apartness for every nonzero row, obtained directly from the
single retained positivity enclosure. -/
def affineApart {tau : CoherentNamed} (certificate : PositiveEnclosure tau)
    (a b : Int) (nonzero : a ≠ 0 ∨ b ≠ 0) :
    CCL.ProgressiveCharts.PossibleApart (affine a b certificate.based).name.process where
  lowerSq := rowLower a b certificate.lower
  positive := rowLower_positive a b certificate.lower certificate.positive nonzero
  lower := by
    intro state value possible
    rcases possible with ⟨x, y, hx, hy, rfl⟩
    rcases hy with ⟨z, w, hz, hw, rfl⟩
    change x = integralGaussian a at hx
    change z = integralGaussian b at hz
    subst x
    subst z
    exact rowLower_le a b certificate.lower w certificate.positive
      (certificate.possible_lower _ hw)

/-- The expanded affine program denotes the same row as the public matrix
action. Rebasing occurs only at the supplied positive enclosure. -/
def denominator_affine {tau : CoherentNamed}
    (certificate : PositiveEnclosure tau) (matrix : IntegralMatrix) :
    NamedEquivalent (fractionalDenominator matrix tau).name
      (affine (matrix 0 0) (matrix 0 1) certificate.based).name := by
  have expanded := matrixAction_row_two matrix (fractionalVector tau) 0
  rw [fractionalVector_zero, fractionalVector_one] at expanded
  exact CCL.OperationalEquivalence.NamedEquivalent.trans expanded
    (CCL.TranscendentalCoherence.coherentAdd_respects _ _ _ _
      (CCL.OperationalFieldLaws.coherentMul_one_right _)
      (CCL.TranscendentalCoherence.coherentMul_respects _ _ _ _
        (CCL.OperationalEquivalence.NamedEquivalent.refl _)
        (tau.basedEquivalent certificate.state)))

/-- Guaranteed finite denominator preparation for any nonzero integral row.
The executable apartifier requests squared radius below `rowLower / 12`;
its resulting whole-ball bound is `rowLower / 8`. -/
def prepare {tau : CoherentNamed} (certificate : PositiveEnclosure tau)
    (matrix : IntegralMatrix) (nonzero : matrix 0 0 ≠ 0 ∨ matrix 0 1 ≠ 0) :
    DenominatorPreparation (fractionalDenominator matrix tau) :=
  let ready := DenominatorPreparation.ofPossibleApart
    (affine (matrix 0 0) (matrix 0 1) certificate.based)
    (affineApart certificate (matrix 0 0) (matrix 0 1) nonzero)
  { prepared := ready.prepared
    apart := ready.apart
    equivalent := CCL.OperationalEquivalence.NamedEquivalent.trans
      (denominator_affine certificate matrix) ready.equivalent }

/-- The prescribed finite preparation retains an explicit whole-ball lower
bound, including for negative coefficients and constant rows. -/
theorem prepare_lowerSq {tau : CoherentNamed}
    (certificate : PositiveEnclosure tau) (matrix : IntegralMatrix)
    (nonzero : matrix 0 0 ≠ 0 ∨ matrix 0 1 ≠ 0) :
    (prepare certificate matrix nonzero).apart.certificate.lowerSq =
      rowLower (matrix 0 0) (matrix 0 1) certificate.lower / 8 := rfl

/-- An explicitly right-invertible matrix has a nonzero first row. -/
theorem row_nonzero_of_inverse (matrix inverse : IntegralMatrix)
    (identity : RFAP.ConstructiveFiniteMatrix.mul matrix inverse =
      RFAP.ConstructiveFiniteMatrix.identity) :
    matrix 0 0 ≠ 0 ∨ matrix 0 1 ≠ 0 := by
  by_cases first : matrix 0 0 = 0
  · right
    intro second
    have entry := congrArg (fun value : IntegralMatrix => value 0 0) identity
    simp only [RFAP.ConstructiveFiniteMatrix.mul_apply,
      CCL.Riemann.LegendrePicardLefschetz.sumFin_two, first, second,
      MulZeroClass.zero_mul, _root_.add_zero] at entry
    exact (by decide : (0 : Int) ≠ 1) entry
  · exact Or.inl first

/-- Every finite dual braid word has its denominator prepared automatically
from the same positive enclosure. No per-word separation witness is an input. -/
def prepareWord {tau : CoherentNamed} (certificate : PositiveEnclosure tau)
    (word : CCL.Knot.FiniteBraid.Word 3) :
    DenominatorPreparation
      (fractionalDenominator
        (CCL.Riemann.LegendrePicardLefschetz.periodMatrix word) tau) :=
  prepare certificate _ (row_nonzero_of_inverse _ _
    (CCL.Riemann.LegendrePicardLefschetz.periodMatrix_inverse_identities word).1)

/-- The genus-one direction for extracting one positive imaginary enclosure. -/
def unitDirection : CCL.Riemann.PeriodMatrix.RationalVector 1 :=
  RFAP.ConstructiveFiniteMatrix.vectorOfFn fun _ => 1

def unitDirection_nonzero : CCL.Riemann.PeriodMatrix.NonzeroVector unitDirection :=
  ⟨0, by decide⟩

/-- Consume the existing finite period positivity interface. One request in
the unit direction supplies the reusable enclosure for every finite word. -/
def enclosureOfPeriodPositivity {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (data : CCL.Riemann.LegendrePeriodMonodromy.NormalizedData frame)
    (positivity : CCL.Riemann.PeriodMatrix.PointwisePositivity data.normalized) :
    PositiveEnclosure data.ratio := by
  let certificate := positivity.certify unitDirection unitDirection_nonzero 1 (by decide)
  refine
    { state := (data.normalized.refinedOmegaEntry certificate.refinementTarget
        certificate.refinementPositive 0 0).state
      lower := certificate.epsilon
      positive := certificate.epsilon_positive
      inside_lower := ?_ }
  intro value inside
  have lower := certificate.compatible_positive
    (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun _ _ => value) (by
      intro row column
      have rowZero : row = 0 := Fin.ext (by omega)
      have columnZero : column = 0 := Fin.ext (by omega)
      subst row
      subst column
      rw [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply]
      exact inside)
  change certificate.epsilon ≤ value.im
  have quadratic : CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm unitDirection
      (RFAP.ConstructiveFiniteMatrix.matrixOfFn fun _ _ => value) = value.im := by
    unfold CCL.Riemann.PeriodMatrix.imaginaryQuadraticForm
    rw [RFAP.ConstructiveFiniteMatrix.sumFin_succ,
      RFAP.ConstructiveFiniteMatrix.sumFin_succ]
    change (1 * value.im * 1 + 0) + 0 = value.im
    ring1
  rw [quadratic] at lower
  exact lower.le

end CCL.Riemann.LegendreAutomaticPreparation
