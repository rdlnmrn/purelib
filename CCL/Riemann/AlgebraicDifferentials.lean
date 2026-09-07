import CCL.Riemann.LiftedPaths
import CCL.Riemann.SquareRootSheets
import CCL.Riemann.OperationalQuotients
import CCL.Bridge.ProjectiveRationalEvaluation
import RFAP.Polynomial.Squarefree

/-!
# Hyperelliptic data and certified algebraic differential observations

The period integrator must not accept an arbitrary convergent integrand under
the name `x^k dx / y`.  Each observation below therefore supplies an exact
finite point `y`, proves `y^2 = f(x)`, proves `y` nonzero, records the selected
sheet, and checks the differential equation after clearing the denominator.
These certificates are aligned cell-by-cell with the sheet-aware lifted path.
-/

namespace CCL.Riemann.AlgebraicDifferentials

open CCL.Riemann.LiftedPaths

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev CellModel := CCL.ProgressiveGaussianIntegration.CellModel
abbrev LocalObservation := CCL.ProgressiveGaussianIntegration.LocalObservation
abbrev RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent

/-- The two finite degree cases that give genus `g`. -/
inductive HyperellipticDegreeShape
    (polynomial : GaussianPolynomial) (genus : Nat) : Type
  | odd (degree_eq : polynomial.natDegree = 2 * genus + 1)
  | even (degree_eq : polynomial.natDegree = 2 * genus + 2)

/-- Executable squarefree input data for a genus-`g` hyperelliptic curve. -/
structure HyperellipticCurve (genus : Nat) where
  polynomial : GaussianPolynomial
  nonzero : polynomial.isZero = false
  squarefree : RFAP.Squarefree.SquarefreeCertificate polynomial
  degreeShape : HyperellipticDegreeShape polynomial genus

namespace HyperellipticCurve

/-- The finite branch-at-infinity profile selected by the displayed degree
certificate. -/
def branchProfile {genus : Nat} (curve : HyperellipticCurve genus) :
    CCL.Riemann.BranchProfile :=
  match curve.degreeShape with
  | .odd _ => CCL.Riemann.Hyperelliptic.oddDegreeProfile genus
  | .even _ => CCL.Riemann.Hyperelliptic.evenDegreeProfile genus

def genusCertificate {genus : Nat} (curve : HyperellipticCurve genus) :
    CCL.Riemann.GenusCertificate curve.branchProfile := by
  cases curve with
  | mk polynomial nonzero squarefree degreeShape =>
      cases degreeShape with
      | odd degreeEqual =>
          exact CCL.Riemann.Hyperelliptic.oddDegreeGenusCertificate genus
      | even degreeEqual =>
          exact CCL.Riemann.Hyperelliptic.evenDegreeGenusCertificate genus

theorem computedGenus {genus : Nat} (curve : HyperellipticCurve genus) :
    curve.genusCertificate.genus = genus := by
  cases curve with
  | mk polynomial nonzero squarefree degreeShape =>
      cases degreeShape with
      | odd degreeEqual =>
          exact CCL.Riemann.Hyperelliptic.oddDegree_computedGenus genus
      | even degreeEqual =>
          exact CCL.Riemann.Hyperelliptic.evenDegree_computedGenus genus

def finiteCellModel {genus : Nat} (curve : HyperellipticCurve genus) :
    CCL.Riemann.BranchedCellModel :=
  CCL.Riemann.finiteBranchedCover curve.branchProfile

theorem finiteCellModel_eulerCharacteristic {genus : Nat}
    (curve : HyperellipticCurve genus) :
    curve.finiteCellModel.eulerCharacteristic = (2 : Int) - 2 * genus := by
  have genusIdentity :=
    CCL.Riemann.GenusCertificate.eulerCharacteristic_eq_two_sub_twice_genus
      curve.genusCertificate
      (CCL.Riemann.spherePolygonCellulation curve.branchProfile.cycles.length)
  rw [curve.computedGenus] at genusIdentity
  exact genusIdentity

end HyperellipticCurve

/-- The standard holomorphic differential `x^k dx/y`, where `k` is the
zero-based finite index. -/
structure Differential (genus : Nat) where
  index : Fin genus

namespace Differential

def exponent {genus : Nat} (differential : Differential genus) : Nat :=
  differential.index.val

end Differential

/-- The affine base point used by one local integration observation. -/
def observationPoint (cell : CellModel)
    (observation : LocalObservation cell.polynomial cell.localAllowance) :
    Gaussian :=
  cell.start + CCL.FiniteExp.scale observation.parameter cell.displacement

/-- Finite repeated power in the operational CCL arithmetic. -/
def namedPower (value : CoherentNamed) : Nat -> CoherentNamed
  | 0 => CCL.ProgressiveCoherence.CoherentNamed.exact 1
  | exponent + 1 => CCL.ProgressiveCoherence.CoherentNamed.mul
      (namedPower value exponent) value

@[simp] theorem namedPower_exact_centerBound (point : Gaussian)
    (exponent : Nat) :
    (namedPower (CCL.ProgressiveCoherence.CoherentNamed.exact point)
      exponent).name.process.centerBound =
        RFAP.ConstructiveGaussian.Gaussian.normSq point ^ exponent := by
  induction exponent with
  | zero =>
      simp only [namedPower, pow_zero,
        CCL.ProgressiveCoherence.CoherentNamed.exact,
        CCL.ProgressiveTransducer.Named.exact,
        CCL.ProgressiveEnclosures.Process.exact,
        RFAP.ConstructiveGaussian.Gaussian.normSq_one]
  | succ exponent inductionHypothesis =>
      simp only [namedPower,
        CCL.ProgressiveCoherence.CoherentNamed.mul,
        CCL.ProgressiveTransducer.Named.mul,
        CCL.ProgressiveEnclosures.Process.mul, pow_succ]
      rw [inductionHypothesis]
      rfl

/-- Every possible finite reading of an exact rational power is that exact
power; multiplication introduces no semantic branch. -/
theorem namedPower_exact_possible_eq (point : Gaussian) (exponent : Nat)
    (state : (namedPower
      (CCL.ProgressiveCoherence.CoherentNamed.exact point)
        exponent).name.process.State)
    {candidate : Gaussian}
    (possible : (namedPower
      (CCL.ProgressiveCoherence.CoherentNamed.exact point)
        exponent).name.process.Possible state candidate) :
    candidate = point ^ exponent := by
  induction exponent generalizing candidate with
  | zero =>
      change candidate = 1 at possible
      simpa only [pow_zero] using possible
  | succ exponent inductionHypothesis =>
      rcases possible with ⟨left, right, leftPossible, rightPossible, rfl⟩
      have leftEqual := inductionHypothesis state.1 leftPossible
      change right = point at rightPossible
      rw [leftEqual, rightPossible, pow_succ]

/-- One operationally certified sheet value above a displayed rational base
point.  The curve equation is equality of finite CCL observations, so it does
not require the generally irrational `y` coordinate to be a rational witness. -/
structure AlgebraicSheetValue {genus : Nat}
    (curve : HyperellipticCurve genus) (point : Gaussian) where
  value : CoherentNamed
  apart : CCL.ProgressiveTransducer.Named.Apart value.name
  sheet : Fin 2
  curveEquation : NamedEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.mul value value).name
    (CCL.ProjectiveRationalEvaluation.polynomialEval curve.polynomial
      (CCL.ProgressiveCoherence.CoherentNamed.exact point)).name

namespace AlgebraicSheetValue

/-- Automatically construct either algebraic sheet over a displayed rational
base point whose radicand is certified nonzero.  The two finite owners come
from isolation of `Z^2 - f(x)`; the curve equation is then transported to the
actual CCL Horner evaluation of `f` at `x`. -/
def automatic {genus : Nat} (curve : HyperellipticCurve genus)
    (point : Gaussian) (radicandNonzero : curve.polynomial.eval point ≠ 0)
    (sheet : Fin 2) : AlgebraicSheetValue curve point := by
  let root := CCL.Riemann.SquareRootSheets.sheet radicandNonzero sheet
  exact
    { value := root.value
      apart := root.apart
      sheet := sheet
      curveEquation :=
        CCL.OperationalEquivalence.NamedEquivalent.trans root.square
          (CCL.OperationalEquivalence.NamedEquivalent.symm
            (CCL.ProjectiveRationalEvaluation.polynomialEval_exact
              curve.polynomial point)) }

/-- Uniform apartness of a terminating nonzero rational name. -/
def exactApart (value : Gaussian) (nonzero : value ≠ 0) :
    CCL.ProgressiveTransducer.Named.Apart
      (CCL.ProgressiveCoherence.CoherentNamed.exact value).name where
  certificate :=
    { lowerSq := RFAP.ConstructiveGaussian.Gaussian.normSq value
      positive := RFAP.ConstructiveGaussian.Gaussian.normSq_pos nonzero
      lower := by
        intro state candidate inside
        change RFAP.ConstructiveGaussian.Gaussian.normSq
          (candidate - value) <= 0 at inside
        have normZero : RFAP.ConstructiveGaussian.Gaussian.normSq
            (candidate - value) = 0 :=
          le_antisymm inside
            (RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _)
        have differenceZero :=
          RFAP.ConstructiveGaussian.Gaussian.normSq_eq_zero.mp normZero
        have equal : candidate = value := sub_eq_zero.mp differenceZero
        rw [equal] }

/-- Promote a displayed rational sheet value when one happens to be exact.
Generic algebraic sheets use the operational constructor directly. -/
def exact {genus : Nat} (curve : HyperellipticCurve genus)
    (point value : Gaussian) (nonzero : value ≠ 0) (sheet : Fin 2)
    (equation : value ^ 2 = curve.polynomial.eval point) :
    AlgebraicSheetValue curve point := by
  let valueName := CCL.ProgressiveCoherence.CoherentNamed.exact value
  let pointName := CCL.ProgressiveCoherence.CoherentNamed.exact point
  have productEquivalent : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul valueName valueName).name
      (CCL.ProgressiveTransducer.Named.exact (value * value)) := by
    simpa only [valueName,
      CCL.ProgressiveCoherence.CoherentNamed.mul,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using
      CCL.TranscendentalCoherence.exactMul_named_equivalent value value
  have evaluationEquivalent :=
    CCL.ProjectiveRationalEvaluation.polynomialEval_exact
      curve.polynomial point
  have productEqual : value * value = curve.polynomial.eval point := by
    simpa only [pow_two] using equation
  exact
    { value := valueName
      apart := exactApart value nonzero
      sheet := sheet
      curveEquation := CCL.OperationalEquivalence.NamedEquivalent.trans
        productEquivalent
        (CCL.OperationalEquivalence.NamedEquivalent.trans
          (by
            rw [productEqual]
            exact CCL.OperationalEquivalence.NamedEquivalent.refl _)
          (CCL.OperationalEquivalence.NamedEquivalent.symm
            evaluationEquivalent)) }

end AlgebraicSheetValue

/-- The named coefficient `x^k/y` of the differential.  The affine path
displacement is applied exactly once by `CellModel.integralSample`; it is not
duplicated inside this coefficient. -/
def differentialValue {genus : Nat}
    (differential : Differential genus) (point : Gaussian)
    (sheetValue : CoherentNamed)
    (apart : CCL.ProgressiveTransducer.Named.Apart sheetValue.name) :
    CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.div
    (namedPower (CCL.ProgressiveCoherence.CoherentNamed.exact point)
      differential.exponent)
    sheetValue apart

/-- Operational coefficient of the local wedge of two standard algebraic
differentials.  Both one-forms are scalar multiples of the same displayed
`dx`, so the antisymmetric coefficient is the finite CCL expression
`left * right - right * left`. -/
def differentialWedgeCoefficient {genus : Nat}
    (left right : Differential genus) (point : Gaussian)
    (sheetValue : CoherentNamed)
    (apart : CCL.ProgressiveTransducer.Named.Apart sheetValue.name) :
    CoherentNamed :=
  let leftValue := differentialValue left point sheetValue apart
  let rightValue := differentialValue right point sheetValue apart
  CCL.ProgressiveCoherence.CoherentNamed.add
    (CCL.ProgressiveCoherence.CoherentNamed.mul leftValue rightValue)
    (CCL.ProgressiveCoherence.CoherentNamed.neg
      (CCL.ProgressiveCoherence.CoherentNamed.mul rightValue leftValue))

/-- The local wedge of any two displayed hyperelliptic basis differentials
vanishes operationally.  The proof is finite arithmetic-name commutativity
followed by exact additive cancellation; it does not invoke a completed
function field or exterior-algebra space. -/
def differentialWedgeCoefficient_zero {genus : Nat}
    (left right : Differential genus) (point : Gaussian)
    (sheetValue : CoherentNamed)
    (apart : CCL.ProgressiveTransducer.Named.Apart sheetValue.name) :
    NamedEquivalent
      (differentialWedgeCoefficient left right point sheetValue apart).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name := by
  let leftValue := differentialValue left point sheetValue apart
  let rightValue := differentialValue right point sheetValue apart
  let leftRight :=
    CCL.ProgressiveCoherence.CoherentNamed.mul leftValue rightValue
  let rightLeft :=
    CCL.ProgressiveCoherence.CoherentNamed.mul rightValue leftValue
  let negativeRightLeft :=
    CCL.ProgressiveCoherence.CoherentNamed.neg rightLeft
  have commute : NamedEquivalent leftRight.name rightLeft.name := by
    simpa only [leftRight, rightLeft,
      CCL.ProgressiveCoherence.CoherentNamed.mul] using
      CCL.TranscendentalCoherence.coherentMul_comm leftValue rightValue
  have replaceFirst : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        leftRight negativeRightLeft).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        rightLeft negativeRightLeft).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      leftRight rightLeft negativeRightLeft negativeRightLeft commute
      (CCL.OperationalEquivalence.NamedEquivalent.refl negativeRightLeft.name)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans replaceFirst (by
    simpa only [negativeRightLeft,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.neg,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using
      CCL.OperationalFieldLaws.coherentAdd_neg_right rightLeft)

/-- Replacing the division-ready sheet name by an operationally equivalent
one preserves the named differential coefficient.  Apartness is supplied
separately on the two finite processes; no lower bound is transported through
an asserted completed value. -/
def differentialValue_respects_sheet {genus : Nat}
    (differential : Differential genus) (point : Gaussian)
    (first second : CoherentNamed)
    (firstApart : CCL.ProgressiveTransducer.Named.Apart first.name)
    (secondApart : CCL.ProgressiveTransducer.Named.Apart second.name)
    (equivalent : NamedEquivalent first.name second.name) :
    NamedEquivalent
      (differentialValue differential point first firstApart).name
      (differentialValue differential point second secondApart).name := by
  let numerator := namedPower
    (CCL.ProgressiveCoherence.CoherentNamed.exact point)
      differential.exponent
  exact CCL.Riemann.OperationalQuotients.coherentDiv_respects
    numerator numerator first second firstApart secondApart
      (CCL.OperationalEquivalence.NamedEquivalent.refl numerator.name)
      equivalent

@[simp] theorem differentialValue_centerBound {genus : Nat}
    (differential : Differential genus) (point : Gaussian)
    (sheetValue : CoherentNamed)
    (apart : CCL.ProgressiveTransducer.Named.Apart sheetValue.name) :
    (differentialValue differential point sheetValue apart).name.process.centerBound =
      RFAP.ConstructiveGaussian.Gaussian.normSq point ^ differential.exponent /
        apart.certificate.lowerSq := by
  change (namedPower (CCL.ProgressiveCoherence.CoherentNamed.exact point)
      differential.exponent).name.process.centerBound /
        apart.certificate.lowerSq =
      RFAP.ConstructiveGaussian.Gaussian.normSq point ^ differential.exponent /
        apart.certificate.lowerSq
  rw [namedPower_exact_centerBound]

/-- A possible finite quotient reading exposes an actual candidate of the
stored denominator name; the numerator is the exact displayed rational
power. -/
theorem differentialValue_possible_components {genus : Nat}
    (differential : Differential genus) (point : Gaussian)
    (sheetValue : CoherentNamed)
    (apart : CCL.ProgressiveTransducer.Named.Apart sheetValue.name)
    (state : (differentialValue differential point sheetValue apart).name.process.State)
    {candidate : Gaussian}
    (possible : (differentialValue differential point sheetValue apart).name.process.Possible
      state candidate) :
    ∃ denominator : Gaussian,
      sheetValue.name.process.Possible state.2 denominator ∧
        candidate = point ^ differential.exponent / denominator := by
  rcases possible with
    ⟨numerator, denominator, numeratorPossible, denominatorPossible, rfl⟩
  refine ⟨denominator, denominatorPossible, ?_⟩
  rw [namedPower_exact_possible_eq point differential.exponent state.1
    numeratorPossible]

/-- Finite algebraic evidence behind one sampled differential value.  The
generally irrational sheet coordinate remains a coherent CCL name satisfying
the curve equation operationally.  The displayed rational integrand reading
must be admitted by one explicit finite state of the named quotient. -/
structure AlgebraicObservation {genus : Nat}
    (curve : HyperellipticCurve genus) (differential : Differential genus)
    {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish)
    (cell : CellModel)
    (observation : LocalObservation cell.polynomial cell.localAllowance) where
  point : Gaussian
  point_eq : point = observationPoint cell observation
  sheetValue : AlgebraicSheetValue curve point
  chosenSheet_eq : sheetValue.sheet = start.sheet
  readingState :
    (differentialValue differential point
      sheetValue.value sheetValue.apart).name.process.State
  readingPossible :
    (differentialValue differential point
      sheetValue.value sheetValue.apart).name.process.Possible readingState
        observation.integrandReading

/-- Algebraic certificates for every displayed observation of one integration
cell.  This is useful finite diagnostic data, but a finite list of samples is
not by itself a uniform integration certificate. -/
inductive ObservationCertificates {genus : Nat}
    (curve : HyperellipticCurve genus) (differential : Differential genus)
    {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish)
    (cell : CellModel) :
    List (LocalObservation cell.polynomial cell.localAllowance) -> Type 2
  | nil : ObservationCertificates curve differential liftedCell cell []
  | cons {observation : LocalObservation cell.polynomial cell.localAllowance}
      {remaining : List
        (LocalObservation cell.polynomial cell.localAllowance)}
      (head : AlgebraicObservation curve differential liftedCell cell observation)
      (tail : ObservationCertificates curve differential liftedCell cell remaining) :
      ObservationCertificates curve differential liftedCell cell
        (observation :: remaining)

/-! ## Uniform local semantics -/

/-- The explicitly generated algebraic observation answering one rational
parameter query.  Its parameter is required to be exactly the queried one;
the observation's decomposition and bound therefore certify the local
polynomial model at that point. -/
structure UniformObservation {genus : Nat}
    (curve : HyperellipticCurve genus) (differential : Differential genus)
    {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish)
    (cell : CellModel) (parameter : RFAP.ConstructiveFraction.Rational) where
  observation : LocalObservation cell.polynomial cell.localAllowance
  parameter_eq : observation.parameter = parameter
  algebraic : AlgebraicObservation curve differential liftedCell cell
    observation
  semantic_error_le :
    2 *
        (4 *
            ((differentialValue differential algebraic.point
              algebraic.sheetValue.value
              algebraic.sheetValue.apart).name.process.ball
                algebraic.readingState).radiusSq +
          RFAP.ConstructiveGaussian.Gaussian.normSq observation.error) <=
      cell.localAllowance

namespace UniformObservation

/-- Every later finite reading admitted by the certified quotient state lies
within the cell's displayed local allowance of the polynomial value.  The
factor eight pays constructively for comparing two points of one squared
ball; the final factor two is the Gaussian triangle estimate. -/
theorem candidate_error_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus}
    {start finish : LiftedPoint 2} {liftedCell : LiftedCell start finish}
    {cell : CellModel}
    {parameter : RFAP.ConstructiveFraction.Rational}
    (uniform : UniformObservation curve differential liftedCell cell parameter)
    {candidate : Gaussian}
    (possible :
      (differentialValue differential uniform.algebraic.point
        uniform.algebraic.sheetValue.value
        uniform.algebraic.sheetValue.apart).name.process.Possible
          uniform.algebraic.readingState candidate) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (candidate - CCL.FiniteGaussianPolynomial.eval cell.polynomial
          ⟨parameter, 0⟩) <= cell.localAllowance := by
  let value := differentialValue differential uniform.algebraic.point
    uniform.algebraic.sheetValue.value uniform.algebraic.sheetValue.apart
  let ball := value.name.process.ball uniform.algebraic.readingState
  have candidateInside : ball.Contains candidate :=
    value.name.process.possible_inside possible
  have readingInside : ball.Contains uniform.observation.integrandReading :=
    value.name.process.possible_inside uniform.algebraic.readingPossible
  have candidateReadingIdentity :
      candidate - uniform.observation.integrandReading =
        (candidate - ball.center) +
          (ball.center - uniform.observation.integrandReading) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  have candidateReadingBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (candidate - uniform.observation.integrandReading) <=
        4 * ball.radiusSq := by
    rw [candidateReadingIdentity]
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((candidate - ball.center) +
            (ball.center - uniform.observation.integrandReading)) <=
          2 *
            (RFAP.ConstructiveGaussian.Gaussian.normSq
                (candidate - ball.center) +
              RFAP.ConstructiveGaussian.Gaussian.normSq
                (ball.center - uniform.observation.integrandReading)) :=
        RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _
      _ <= 2 * (ball.radiusSq + ball.radiusSq) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add candidateInside (by
            have reversed :
                ball.center - uniform.observation.integrandReading =
                  -(uniform.observation.integrandReading - ball.center) := by
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
                  RFAP.ConstructiveGaussian.Gaussian.sub_im,
                  RFAP.ConstructiveGaussian.Gaussian.neg_re,
                  RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1
            rw [reversed,
              RFAP.ConstructiveGaussian.Gaussian.normSq_neg]
            exact readingInside)) (by decide)
      _ = 4 * ball.radiusSq := by ring1
  have totalIdentity :
      candidate - CCL.FiniteGaussianPolynomial.eval cell.polynomial
          ⟨parameter, 0⟩ =
        (candidate - uniform.observation.integrandReading) +
          uniform.observation.error := by
    have inputEqual :
        (⟨parameter, 0⟩ : Gaussian) =
          ⟨uniform.observation.parameter, 0⟩ := by
      rw [uniform.parameter_eq]
    rw [inputEqual, ← uniform.observation.decomposition]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.add_re,
        RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1
  rw [totalIdentity]
  exact (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans
    ((RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (add_le_add candidateReadingBound le_rfl) (by decide)).trans
        uniform.semantic_error_le)

end UniformObservation

/-- Productive uniform semantics for a nonstationary integration cell.  A
query supplies a rational unit-interval parameter and receives a finite
algebraic sheet value, an admitted differential reading, and the checked
model-error inequality at that exact parameter. -/
structure UniformCellCertificate {genus : Nat}
    (curve : HyperellipticCurve genus) (differential : Differential genus)
    {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish)
    (cell : CellModel) where
  query : forall parameter : RFAP.ConstructiveFraction.Rational,
    (0 : RFAP.ConstructiveFraction.Rational) <= parameter ->
    parameter <= 1 ->
      UniformObservation curve differential liftedCell cell parameter

/-- A stationary cell contributes exactly zero regardless of its integrand.
Every nonstationary cell must instead carry the uniform algebraic model
contract.  In particular, an empty observation list can no longer certify an
arbitrary nonzero segment as a period integrand. -/
inductive ValidCellCertificate {genus : Nat}
    (curve : HyperellipticCurve genus) (differential : Differential genus)
    {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish)
    (cell : CellModel) : Type 2
  | stationary (equal : cell.start = cell.finish) :
      ValidCellCertificate curve differential liftedCell cell
  | uniform (certificate :
      UniformCellCertificate curve differential liftedCell cell) :
      ValidCellCertificate curve differential liftedCell cell

/-- Cell-for-cell sampled algebraic diagnostics against a finite sheet-aware
path.  Period programs use `UniformPathCertificates` below. -/
inductive PathCertificates {genus : Nat}
    (curve : HyperellipticCurve genus) (differential : Differential genus) :
    List CellModel -> {start finish : LiftedPoint 2} ->
      LiftedPath 2 start finish -> Type 2
  | nil (point : LiftedPoint 2) : PathCertificates curve differential [] (.nil point)
  | cons {start middle finish : LiftedPoint 2}
      {cell : CellModel} {cells : List CellModel}
      {liftedCell : LiftedCell start middle}
      {remaining : LiftedPath 2 middle finish}
      (start_eq : cell.start = start.coordinate)
      (finish_eq : cell.finish = middle.coordinate)
      (observations : ObservationCertificates curve differential liftedCell cell
        cell.observations)
      (tail : PathCertificates curve differential cells remaining) :
      PathCertificates curve differential (cell :: cells)
        (.cons liftedCell remaining)

namespace PathCertificates

/-- Forget only the algebraic equations, retaining the proof that the same
integration cells follow the same lifted path. -/
theorem toFollowedBy {genus : Nat}
    {curve : HyperellipticCurve genus} {differential : Differential genus}
    {cells : List CellModel} {start finish : LiftedPoint 2}
    {path : LiftedPath 2 start finish}
    (certificates : PathCertificates curve differential cells path) :
    LiftedPath.FollowedBy cells path :=
  match certificates with
  | .nil point => .nil point
  | .cons start_eq finish_eq _ tail =>
      .cons start_eq finish_eq (toFollowedBy tail)

end PathCertificates

/-- Cell-for-cell uniform algebraic certification of an integration model.
Unlike `PathCertificates`, this relation rules out the one-point and
empty-list loopholes on every nonstationary segment. -/
inductive UniformPathCertificates {genus : Nat}
    (curve : HyperellipticCurve genus) (differential : Differential genus) :
    List CellModel -> {start finish : LiftedPoint 2} ->
      LiftedPath 2 start finish -> Type 2
  | nil (point : LiftedPoint 2) :
      UniformPathCertificates curve differential [] (.nil point)
  | cons {start middle finish : LiftedPoint 2}
      {cell : CellModel} {cells : List CellModel}
      {liftedCell : LiftedCell start middle}
      {remaining : LiftedPath 2 middle finish}
      (start_eq : cell.start = start.coordinate)
      (finish_eq : cell.finish = middle.coordinate)
      (valid : ValidCellCertificate curve differential liftedCell cell)
      (tail : UniformPathCertificates curve differential cells remaining) :
      UniformPathCertificates curve differential (cell :: cells)
        (.cons liftedCell remaining)

namespace UniformPathCertificates

/-- Transport uniform certificates across an equality of starting lifted
points. -/
def castStart {genus : Nat}
    {curve : HyperellipticCurve genus} {differential : Differential genus}
    {cells : List CellModel} {left right finish : LiftedPoint 2}
    {path : LiftedPath 2 left finish} (equal : left = right)
    (certificates : UniformPathCertificates curve differential cells path) :
    UniformPathCertificates curve differential cells
      (path.castStart equal) := by
  subst right
  exact certificates

/-- Transport uniform certificates across an equality of finishing lifted
points. -/
def castFinish {genus : Nat}
    {curve : HyperellipticCurve genus} {differential : Differential genus}
    {cells : List CellModel} {start left right : LiftedPoint 2}
    {path : LiftedPath 2 start left} (equal : left = right)
    (certificates : UniformPathCertificates curve differential cells path) :
    UniformPathCertificates curve differential cells
      (path.castFinish equal) := by
  subst right
  exact certificates

/-- Concatenate two uniformly certified finite algebraic paths meeting at the
same lifted point.  Recursion follows the executable lifted path; the indexed
certificate argument supplies the matching cell certificate at each step. -/
def append {genus : Nat}
    {curve : HyperellipticCurve genus} {differential : Differential genus}
    {firstCells secondCells : List CellModel}
    {start middle finish : LiftedPoint 2}
    {second : LiftedPath 2 middle finish} :
    (first : LiftedPath 2 start middle) ->
      UniformPathCertificates curve differential firstCells first ->
        UniformPathCertificates curve differential secondCells second ->
          UniformPathCertificates curve differential
            (firstCells ++ secondCells) (first.append second)
  | .nil _, .nil _, secondCertificates => secondCertificates
  | .cons _ remaining, .cons start_eq finish_eq valid tail,
      secondCertificates =>
      .cons start_eq finish_eq valid
        (append remaining tail secondCertificates)

theorem toFollowedBy {genus : Nat}
    {curve : HyperellipticCurve genus} {differential : Differential genus}
    {cells : List CellModel} {start finish : LiftedPoint 2}
    {path : LiftedPath 2 start finish}
    (certificates :
      UniformPathCertificates curve differential cells path) :
    LiftedPath.FollowedBy cells path :=
  match certificates with
  | .nil point => .nil point
  | .cons start_eq finish_eq _ tail =>
      .cons start_eq finish_eq (toFollowedBy tail)

end UniformPathCertificates

/-- A persistent period program whose every finite integrand observation is
uniformly certified to be the requested algebraic differential on the chosen
sheet. -/
structure CertifiedPeriodProgram {genus : Nat}
    (curve : HyperellipticCurve genus) (differential : Differential genus)
    (cycle : LiftedCycleRefinement 2) where
  integral : RefinementProgram
  certificates : forall index,
    UniformPathCertificates curve differential (integral.model index).cells
      (cycle.liftedPath index).path

namespace CertifiedPeriodProgram

/-- Cache a proved dominating rational error scale without changing any
finite cycle model or uniform differential certificate. -/
def withLargerErrorScale {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : Differential genus} {cycle : LiftedCycleRefinement 2}
    (program : CertifiedPeriodProgram curve differential cycle)
    (scale : CCL.ProgressiveGaussianIntegration.Coordinate)
    (scaleNonnegative : 0 <= scale)
    (dominates : program.integral.errorScale <= scale) :
    CertifiedPeriodProgram curve differential cycle where
  integral := program.integral.withLargerErrorScale scale scaleNonnegative
    dominates
  certificates := program.certificates

def toPeriodProgram {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus} {cycle : LiftedCycleRefinement 2}
    (program : CertifiedPeriodProgram curve differential cycle) :
    PeriodProgram cycle where
  integral := program.integral
  follows := fun index => UniformPathCertificates.toFollowedBy
    (program.certificates index)

def output {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : Differential genus} {cycle : LiftedCycleRefinement 2}
    (program : CertifiedPeriodProgram curve differential cycle) :
    CCL.ProgressiveCoherence.CoherentNamed :=
  program.toPeriodProgram.output

theorem finite_refinement_cellCount {genus : Nat}
    {curve : HyperellipticCurve genus} {differential : Differential genus}
    {cycle : LiftedCycleRefinement 2}
    (program : CertifiedPeriodProgram curve differential cycle)
    (index : Nat) :
    (program.integral.model index).cells.length =
      (cycle.liftedPath index).cellCount :=
  program.toPeriodProgram.finite_refinement_cellCount index

end CertifiedPeriodProgram

end CCL.Riemann.AlgebraicDifferentials
