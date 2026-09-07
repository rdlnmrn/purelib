import CCL.Riemann.LegendrePicardFuchs
import CCL.Progressive.FiniteTable

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace CCL.Riemann.LegendrePeriodJets

open CCL.Riemann.LiftedPaths
open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.LegendrePicardFuchs

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev CellModel := CCL.ProgressiveGaussianIntegration.CellModel
abbrev LocalObservation :=
  CCL.ProgressiveGaussianIntegration.LocalObservation
abbrev RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram
abbrev ClosedPrimitiveBoundary :=
  CCL.Riemann.FiniteBilinear.ClosedPrimitiveBoundary

/-! ## Odd-power algebraic integrands -/

/-- A displayed differential
`scale * numerator(x) * dx / y^(2*denominatorPairs+1)`. -/
structure OddPowerDifferential where
  numerator : GaussianPolynomial
  denominatorPairs : Nat
  scale : Gaussian

namespace OddPowerDifferential

def denominatorExponent (differential : OddPowerDifferential) : Nat :=
  2 * differential.denominatorPairs + 1

/-- The actual productive coefficient name at one displayed point and sheet.
Only division by the already apart sheet value is used; higher reciprocal
powers are total finite multiplications. -/
def value (differential : OddPowerDifferential) (point : Gaussian)
    (sheetValue : CoherentNamed)
    (apart : CCL.ProgressiveTransducer.Named.Apart sheetValue.name) :
    CoherentNamed :=
  let numerator := CCL.ProgressiveCoherence.CoherentNamed.exact
    (differential.scale * differential.numerator.eval point)
  let reciprocal := CCL.ProgressiveCoherence.CoherentNamed.div
    (CCL.ProgressiveCoherence.CoherentNamed.exact 1) sheetValue apart
  CCL.ProgressiveCoherence.CoherentNamed.mul numerator
    (namedPower reciprocal differential.denominatorExponent)

end OddPowerDifferential

/-- Finite algebraic evidence behind one sampled odd-power differential
value. -/
structure AlgebraicObservation {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : OddPowerDifferential)
    {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish)
    (cell : CellModel)
    (observation : LocalObservation cell.polynomial cell.localAllowance) where
  point : Gaussian
  point_eq : point = observationPoint cell observation
  sheetValue : AlgebraicSheetValue curve point
  chosenSheet_eq : sheetValue.sheet = start.sheet
  readingState :
    (differential.value point sheetValue.value
      sheetValue.apart).name.process.State
  readingPossible :
    (differential.value point sheetValue.value
      sheetValue.apart).name.process.Possible readingState
        observation.integrandReading

/-- A query at every rational unit parameter, together with enough explicit
error budget to control every later reading of the admitted CCL state. -/
structure UniformObservation {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : OddPowerDifferential)
    {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish)
    (cell : CellModel) (parameter : Coordinate) where
  observation : LocalObservation cell.polynomial cell.localAllowance
  parameter_eq : observation.parameter = parameter
  algebraic : AlgebraicObservation curve differential liftedCell cell
    observation
  semantic_error_le :
    2 *
        (4 *
            (((differential.value algebraic.point
              algebraic.sheetValue.value
              algebraic.sheetValue.apart).name.process.ball
                algebraic.readingState).radiusSq) +
          RFAP.ConstructiveGaussian.Gaussian.normSq observation.error) <=
      cell.localAllowance

namespace UniformObservation

/-- Every admitted later reading remains within the displayed local
polynomial allowance.  The proof is independent of the odd exponent once the
coherent arithmetic name has been constructed. -/
theorem candidate_error_le {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : OddPowerDifferential}
    {start finish : LiftedPoint 2} {liftedCell : LiftedCell start finish}
    {cell : CellModel} {parameter : Coordinate}
    (uniform : UniformObservation curve differential liftedCell cell parameter)
    {candidate : Gaussian}
    (possible :
      (differential.value uniform.algebraic.point
        uniform.algebraic.sheetValue.value
        uniform.algebraic.sheetValue.apart).name.process.Possible
          uniform.algebraic.readingState candidate) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (candidate - CCL.FiniteGaussianPolynomial.eval cell.polynomial
          ⟨parameter, 0⟩) <= cell.localAllowance := by
  let value := differential.value uniform.algebraic.point
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
    have inputEqual : (⟨parameter, 0⟩ : Gaussian) =
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

/-- A nonstationary cell must answer every rational unit-interval query with
uniform odd-power algebraic evidence. -/
structure UniformCellCertificate {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : OddPowerDifferential)
    {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish)
    (cell : CellModel) where
  query : forall parameter : Coordinate, 0 <= parameter -> parameter <= 1 ->
    UniformObservation curve differential liftedCell cell parameter

inductive ValidCellCertificate {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : OddPowerDifferential)
    {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish)
    (cell : CellModel) : Type 2
  | stationary (equal : cell.start = cell.finish) :
      ValidCellCertificate curve differential liftedCell cell
  | uniform (certificate :
      UniformCellCertificate curve differential liftedCell cell) :
      ValidCellCertificate curve differential liftedCell cell

/-- Cell-for-cell uniform certification against one displayed lifted path. -/
inductive UniformPathCertificates {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : OddPowerDifferential) :
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

theorem toFollowedBy {genus : Nat}
    {curve : HyperellipticCurve genus}
    {differential : OddPowerDifferential}
    {cells : List CellModel} {start finish : LiftedPoint 2}
    {path : LiftedPath 2 start finish}
    (certificates : UniformPathCertificates curve differential cells path) :
    LiftedPath.FollowedBy cells path :=
  match certificates with
  | .nil point => .nil point
  | .cons start_eq finish_eq _ tail =>
      .cons start_eq finish_eq (toFollowedBy tail)

end UniformPathCertificates

/-- A persistent finite integral program uniformly realizing one displayed
odd-power algebraic differential on one displayed lifted cycle. -/
structure CertifiedPeriodProgram {genus : Nat}
    (curve : HyperellipticCurve genus)
    (differential : OddPowerDifferential)
    (cycle : LiftedCycleRefinement 2) where
  integral : RefinementProgram
  certificates : forall index,
    UniformPathCertificates curve differential (integral.model index).cells
      (cycle.liftedPath index).path

namespace CertifiedPeriodProgram

def toPeriodProgram {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : OddPowerDifferential}
    {cycle : LiftedCycleRefinement 2}
    (program : CertifiedPeriodProgram curve differential cycle) :
    PeriodProgram cycle where
  integral := program.integral
  follows := fun index => UniformPathCertificates.toFollowedBy
    (program.certificates index)

def output {genus : Nat} {curve : HyperellipticCurve genus}
    {differential : OddPowerDifferential}
    {cycle : LiftedCycleRefinement 2}
    (program : CertifiedPeriodProgram curve differential cycle) :
    CoherentNamed := program.integral.output

end CertifiedPeriodProgram

/-! ## The displayed Legendre value/derivative specifications -/

def constantOnePolynomial : GaussianPolynomial := ⟨[1]⟩

def squaredBasePolynomial : GaussianPolynomial := ⟨[1, -2, 1, 0, 0]⟩

def weightedSquaredBasePolynomial : GaussianPolynomial :=
  ⟨[1, -2, 1, 0, 0, 0]⟩

@[simp] theorem constantOnePolynomial_eval (point : Gaussian) :
    constantOnePolynomial.eval point = 1 := by
  unfold constantOnePolynomial
    RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

@[simp] theorem squaredBasePolynomial_eval (point : Gaussian) :
    squaredBasePolynomial.eval point = (point * (point - 1)) ^ 2 := by
  unfold squaredBasePolynomial
    RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

@[simp] theorem weightedSquaredBasePolynomial_eval (point : Gaussian) :
    weightedSquaredBasePolynomial.eval point =
      point * (point * (point - 1)) ^ 2 := by
  unfold weightedSquaredBasePolynomial
    RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

def realGaussian (value : Coordinate) : Gaussian := ⟨value, 0⟩

/-- The value-channel integrand `x^k/y`, for `k=0,1`. -/
def valueSpecification (coordinate : Fin 2) : OddPowerDifferential :=
  if coordinate = 0 then
    { numerator := constantOnePolynomial
      denominatorPairs := 0
      scale := 1 }
  else
    { numerator := coordinatePolynomial
      denominatorPairs := 0
      scale := 1 }

/-- The first parameter derivative
`x^k g(x)/(2 y^3)`. -/
def firstDerivativeSpecification (coordinate : Fin 2) :
    OddPowerDifferential :=
  if coordinate = 0 then
    { numerator := basePolynomial
      denominatorPairs := 1
      scale := realGaussian (1 / 2) }
  else
    { numerator := weightedBasePolynomial
      denominatorPairs := 1
      scale := realGaussian (1 / 2) }

/-- The second parameter derivative
`3 x^k g(x)^2/(4 y^5)`. -/
def secondDerivativeSpecification (coordinate : Fin 2) :
    OddPowerDifferential :=
  if coordinate = 0 then
    { numerator := squaredBasePolynomial
      denominatorPairs := 2
      scale := realGaussian (3 / 4) }
  else
    { numerator := weightedSquaredBasePolynomial
      denominatorPairs := 2
      scale := realGaussian (3 / 4) }

@[simp] theorem valueSpecification_zero :
    valueSpecification 0 =
      { numerator := constantOnePolynomial
        denominatorPairs := 0
        scale := 1 } := rfl

@[simp] theorem valueSpecification_one :
    valueSpecification 1 =
      { numerator := coordinatePolynomial
        denominatorPairs := 0
        scale := 1 } := by
  unfold valueSpecification
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

@[simp] theorem firstDerivativeSpecification_zero :
    firstDerivativeSpecification 0 =
      { numerator := basePolynomial
        denominatorPairs := 1
        scale := realGaussian (1 / 2) } := rfl

@[simp] theorem firstDerivativeSpecification_one :
    firstDerivativeSpecification 1 =
      { numerator := weightedBasePolynomial
        denominatorPairs := 1
        scale := realGaussian (1 / 2) } := by
  unfold firstDerivativeSpecification
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

@[simp] theorem secondDerivativeSpecification_zero :
    secondDerivativeSpecification 0 =
      { numerator := squaredBasePolynomial
        denominatorPairs := 2
        scale := realGaussian (3 / 4) } := rfl

@[simp] theorem secondDerivativeSpecification_one :
    secondDerivativeSpecification 1 =
      { numerator := weightedSquaredBasePolynomial
        denominatorPairs := 2
        scale := realGaussian (3 / 4) } := by
  unfold secondDerivativeSpecification
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

private theorem finTwo_cases (coordinate : Fin 2) :
    coordinate = 0 ∨ coordinate = 1 := by
  rcases coordinate with ⟨value, bound⟩
  omega0

/-! ## One common lifted-cycle period jet -/

/-- Value, first derivative, and second derivative are certified on literally
the same displayed lifted cycle for each of the two genus-one coordinates. -/
structure SynchronizedPeriodJet {parameter : Gaussian}
    (frame : CCL.Riemann.LegendrePaths.Frame parameter) where
  cycle : Fin 2 -> LiftedCycleRefinement 2
  value : forall coordinate,
    CertifiedPeriodProgram
      (CCL.Riemann.LegendreGaussManin.frameCurve frame)
      (valueSpecification coordinate) (cycle coordinate)
  first : forall coordinate,
    CertifiedPeriodProgram
      (CCL.Riemann.LegendreGaussManin.frameCurve frame)
      (firstDerivativeSpecification coordinate) (cycle coordinate)
  second : forall coordinate,
    CertifiedPeriodProgram
      (CCL.Riemann.LegendreGaussManin.frameCurve frame)
      (secondDerivativeSpecification coordinate) (cycle coordinate)

namespace SynchronizedPeriodJet

def valueName {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2) : CoherentNamed :=
  (jet.value coordinate).output

def firstName {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2) : CoherentNamed :=
  (jet.first coordinate).output

def secondName {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2) : CoherentNamed :=
  (jet.second coordinate).output

/-- The six actual productive channels, in value/first/second and then
`a`/`b` order. -/
def channels {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) : List CoherentNamed :=
  [jet.valueName 0, jet.valueName 1,
    jet.firstName 0, jet.firstName 1,
    jet.secondName 0, jet.secondName 1]

def table {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) : CCL.ProgressiveFiniteTable.Table :=
  ⟨jet.channels⟩

@[simp] theorem channels_length {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) : jet.channels.length = 6 := rfl

theorem valueName_mem_channels {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2) :
    jet.valueName coordinate ∈ jet.channels := by
  rcases finTwo_cases coordinate with equal | equal <;>
    subst coordinate <;> simp only [channels, List.mem_cons, true_or,
      or_true]

theorem firstName_mem_channels {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2) :
    jet.firstName coordinate ∈ jet.channels := by
  rcases finTwo_cases coordinate with equal | equal <;>
    subst coordinate <;> simp only [channels, List.mem_cons, true_or,
      or_true]

theorem secondName_mem_channels {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2) :
    jet.secondName coordinate ∈ jet.channels := by
  rcases finTwo_cases coordinate with equal | equal <;>
    subst coordinate <;> simp only [channels, List.mem_cons, true_or,
      or_true]

/-- Every value channel answers one request shared by all six channels. -/
theorem value_joint_request {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract jet.channels
      (jet.valueName coordinate) target positive count :=
  jet.table.member_bitstream_and_allowance
    (jet.valueName_mem_channels coordinate) target positive count

/-- Every first-derivative channel answers the same joint request. -/
theorem first_joint_request {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract jet.channels
      (jet.firstName coordinate) target positive count :=
  jet.table.member_bitstream_and_allowance
    (jet.firstName_mem_channels coordinate) target positive count

/-- Every second-derivative channel answers the same joint request. -/
theorem second_joint_request {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    CCL.ProgressiveFiniteTable.RequestContract jet.channels
      (jet.secondName coordinate) target positive count :=
  jet.table.member_bitstream_and_allowance
    (jet.secondName_mem_channels coordinate) target positive count

end SynchronizedPeriodJet

/-- A displayed finite owner set simultaneously covering the value, first-,
and second-derivative quadrature cells at every requested refinement.  The
three programs may use different literal cell lists, but their comparison is
therefore not allowed to hide unrelated subdivisions. -/
structure JetCommonSubdivision {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) where
  commonCount : Fin 2 -> Nat -> Nat
  valueOwner : forall coordinate refinement,
    Fin (commonCount coordinate refinement) ->
      Fin ((jet.value coordinate).integral.model refinement).cells.length
  firstOwner : forall coordinate refinement,
    Fin (commonCount coordinate refinement) ->
      Fin ((jet.first coordinate).integral.model refinement).cells.length
  secondOwner : forall coordinate refinement,
    Fin (commonCount coordinate refinement) ->
      Fin ((jet.second coordinate).integral.model refinement).cells.length
  valueCovered : forall coordinate refinement
      (cell : Fin
        ((jet.value coordinate).integral.model refinement).cells.length),
    ∃ common : Fin (commonCount coordinate refinement),
      valueOwner coordinate refinement common = cell
  firstCovered : forall coordinate refinement
      (cell : Fin
        ((jet.first coordinate).integral.model refinement).cells.length),
    ∃ common : Fin (commonCount coordinate refinement),
      firstOwner coordinate refinement common = cell
  secondCovered : forall coordinate refinement
      (cell : Fin
        ((jet.second coordinate).integral.model refinement).cells.length),
    ∃ common : Fin (commonCount coordinate refinement),
      secondOwner coordinate refinement common = cell

/-! ## Fraction-free operational connection -/

abbrev CommonSchedule := CCL.Riemann.LegendreGaussManin.CommonSchedule

/-- The four finite sources of error kept visible when the synchronized jet
channels are compared.  The single total below is used for both connection
rows, so no independently chosen derivative schedule is hidden in the
statement. -/
structure JetErrorBudget where
  algebraic : Coordinate
  quadrature : Coordinate
  primitive : Coordinate
  synchronization : Coordinate
  algebraic_nonnegative : 0 <= algebraic
  quadrature_nonnegative : 0 <= quadrature
  primitive_nonnegative : 0 <= primitive
  synchronization_nonnegative : 0 <= synchronization

namespace JetErrorBudget

def total (budget : JetErrorBudget) : Coordinate :=
  8 * (budget.algebraic + budget.quadrature +
    budget.primitive + budget.synchronization)

theorem total_nonnegative (budget : JetErrorBudget) : 0 <= budget.total :=
  RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
    (add_nonneg
      (add_nonneg
        (add_nonneg budget.algebraic_nonnegative
          budget.quadrature_nonnegative)
        budget.primitive_nonnegative)
      budget.synchronization_nonnegative)

end JetErrorBudget

def exactName (value : Gaussian) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.exact value

def scaleName (factor : Gaussian) (value : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.mul (exactName factor) value

def subtractName (left right : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add left
    (CCL.ProgressiveCoherence.CoherentNamed.neg right)

/-- Repackage a coherent arithmetic expression as an ordinary one-cell
refinement program so the same scheduled finite comparison theorem used by
raw Gauss--Manin transport applies without a new semantic route. -/
def namedCarrier (value : CoherentNamed) : RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram.ofCoherentNamed value

/-- A shrinking finite comparison between two actual coherent arithmetic
expressions implies their operational equality. -/
def namedEquivalent_of_scheduled_samples
    (left right : CoherentNamed) (schedule : CommonSchedule)
    (bridgeScale : Coordinate) (bridgeScale_nonnegative : 0 <= bridgeScale)
    (samples : forall request,
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (((namedCarrier left).model
              (schedule.targetIndex request)).integralSample -
            ((namedCarrier right).model
              (schedule.comparisonIndex request)).integralSample) <=
        CCL.FiniteGeometric.quarterRadius bridgeScale request) :
    NamedEquivalent left.name right.name := by
  have leftCarrier : NamedEquivalent left.name (namedCarrier left).output.name :=
    CCL.Riemann.FiniteBilinear.ofCoherentNamed_output_equivalent left
  have carriers : NamedEquivalent (namedCarrier left).output.name
      (namedCarrier right).output.name :=
    CCL.Riemann.LegendreGaussManin.scheduledProgram_output_equivalent
      (namedCarrier left) (namedCarrier right) schedule bridgeScale
      bridgeScale_nonnegative samples
  have rightCarrier : NamedEquivalent right.name
      (namedCarrier right).output.name :=
    CCL.Riemann.FiniteBilinear.ofCoherentNamed_output_equivalent right
  exact CCL.OperationalEquivalence.NamedEquivalent.trans leftCarrier
    (CCL.OperationalEquivalence.NamedEquivalent.trans carriers
      (CCL.OperationalEquivalence.NamedEquivalent.symm rightCarrier))

/-- The canonical symbolic reduction selected by a row of the genus-one
period vector. -/
def connectionReduction (parameter : Gaussian) (coordinate : Fin 2) :
    ConnectionReduction parameter :=
  if coordinate = 0 then firstConnectionReduction parameter
  else secondConnectionReduction parameter

@[simp] theorem connectionReduction_zero (parameter : Gaussian) :
    connectionReduction parameter 0 = firstConnectionReduction parameter :=
  rfl

@[simp] theorem connectionReduction_one (parameter : Gaussian) :
    connectionReduction parameter 1 = secondConnectionReduction parameter := by
  unfold connectionReduction
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- The left side `2 lambda (1-lambda) u'` of one connection row. -/
def connectionScaledFirst {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2) : CoherentNamed :=
  scaleName (ParameterClearance.connectionDenominator parameter)
    (jet.firstName coordinate)

/-- The fraction-free connection matrix numerator
`[[lambda,-1],[lambda,-lambda]]` acting on the two value channels. -/
def connectionAction {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) (coordinate : Fin 2) : CoherentNamed :=
  if coordinate = 0 then
    subtractName (scaleName parameter (jet.valueName 0)) (jet.valueName 1)
  else
    subtractName (scaleName parameter (jet.valueName 0))
      (scaleName parameter (jet.valueName 1))

@[simp] theorem connectionAction_zero {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) :
    connectionAction jet 0 =
      subtractName (scaleName parameter (jet.valueName 0))
        (jet.valueName 1) := rfl

@[simp] theorem connectionAction_one {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) :
    connectionAction jet 1 =
      subtractName (scaleName parameter (jet.valueName 0))
        (scaleName parameter (jet.valueName 1)) := by
  unfold connectionAction
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

def connectionWithPrimitive {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame)
    (primitive : Fin 2 -> ClosedPrimitiveBoundary)
    (coordinate : Fin 2) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add (connectionAction jet coordinate)
    (primitive coordinate).integralSum

/-- Complete finite evidence for both rows of the fraction-free connection.
The canonical polynomial reductions are fixed by `connectionReduction`; this
certificate supplies their closed primitive realizations and one common
finite schedule/error allocation for comparing the actual period programs. -/
structure ConnectionCertificate {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) where
  clearance : ParameterClearance parameter
  primitive : Fin 2 -> ClosedPrimitiveBoundary
  subdivision : JetCommonSubdivision jet
  schedule : CommonSchedule
  budget : JetErrorBudget
  connection_samples_close : forall coordinate request,
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (((namedCarrier (connectionScaledFirst jet coordinate)).model
            (schedule.targetIndex request)).integralSample -
          ((namedCarrier
            (connectionWithPrimitive jet primitive coordinate)).model
              (schedule.comparisonIndex request)).integralSample) <=
      CCL.FiniteGeometric.quarterRadius budget.total request

namespace ConnectionCertificate

/-- The scheduled finite comparison realizes the canonical algebraic
connection row together with its exact differential. -/
def coordinate_with_primitive {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {jet : SynchronizedPeriodJet frame}
    (certificate : ConnectionCertificate jet) (coordinate : Fin 2) :
    NamedEquivalent (connectionScaledFirst jet coordinate).name
      (connectionWithPrimitive jet certificate.primitive coordinate).name :=
  namedEquivalent_of_scheduled_samples _ _ certificate.schedule
    certificate.budget.total certificate.budget.total_nonnegative
    (certificate.connection_samples_close coordinate)

private def action_primitive_to_action {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {jet : SynchronizedPeriodJet frame}
    (certificate : ConnectionCertificate jet) (coordinate : Fin 2) :
    NamedEquivalent
      (connectionWithPrimitive jet certificate.primitive coordinate).name
      (connectionAction jet coordinate).name := by
  let action := connectionAction jet coordinate
  let primitive := (certificate.primitive coordinate).integralSum
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  have discardPrimitive : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add action primitive).name
      (CCL.ProgressiveCoherence.CoherentNamed.add action zero).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects action action
      primitive zero
      (CCL.OperationalEquivalence.NamedEquivalent.refl action.name)
      (CCL.Riemann.PeriodLinearity.exactDifferential_closed_operational_zero
        (certificate.primitive coordinate))
  exact CCL.OperationalEquivalence.NamedEquivalent.trans discardPrimitive
    (CCL.OperationalFieldLaws.coherentAdd_zero_right action)

/-- One row of the finite fraction-free Gauss--Manin connection,
`2 lambda (1-lambda) U' = [[lambda,-1],[lambda,-lambda]] U`. -/
def coordinate_connection {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {jet : SynchronizedPeriodJet frame}
    (certificate : ConnectionCertificate jet) (coordinate : Fin 2) :
    NamedEquivalent (connectionScaledFirst jet coordinate).name
      (connectionAction jet coordinate).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (certificate.coordinate_with_primitive coordinate)
    (certificate.action_primitive_to_action coordinate)

/-- Vector form of the finite fraction-free Gauss--Manin connection. -/
def connection {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {jet : SynchronizedPeriodJet frame}
    (certificate : ConnectionCertificate jet) :
    CCL.Riemann.LegendreGaussManin.VectorEquivalent
      (fun coordinate => connectionScaledFirst jet coordinate)
      (fun coordinate => connectionAction jet coordinate) :=
  certificate.coordinate_connection

end ConnectionCertificate

/-! ## Fraction-free Picard--Fuchs residual -/

def picardFuchsSecondTerm {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) : CoherentNamed :=
  scaleName (4 * parameter * (1 - parameter)) (jet.secondName 0)

def picardFuchsFirstTerm {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) : CoherentNamed :=
  scaleName (4 * (1 - 2 * parameter)) (jet.firstName 0)

/-- The actual coherent arithmetic expression
`4 lambda (1-lambda) u'' + 4(1-2 lambda) u' - u`. -/
def picardFuchsResidual {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (CCL.ProgressiveCoherence.CoherentNamed.add
      (picardFuchsSecondTerm jet) (picardFuchsFirstTerm jet))
    (CCL.ProgressiveCoherence.CoherentNamed.neg (jet.valueName 0))

/-- Finite analytic evidence which realizes the fixed symbolic
`picardFuchsReduction` on the synchronized period jet. -/
structure PicardFuchsCertificate {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    (jet : SynchronizedPeriodJet frame) where
  clearance : ParameterClearance parameter
  primitive : ClosedPrimitiveBoundary
  subdivision : JetCommonSubdivision jet
  schedule : CommonSchedule
  budget : JetErrorBudget
  residual_samples_close : forall request,
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (((namedCarrier (picardFuchsResidual jet)).model
            (schedule.targetIndex request)).integralSample -
          ((namedCarrier primitive.integralSum).model
            (schedule.comparisonIndex request)).integralSample) <=
      CCL.FiniteGeometric.quarterRadius budget.total request

namespace PicardFuchsCertificate

/-- The finite comparison identifies the actual residual with the exact
primitive dictated by the polynomial reduction. -/
def residual_equivalent_primitive {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {jet : SynchronizedPeriodJet frame}
    (certificate : PicardFuchsCertificate jet) :
    NamedEquivalent (picardFuchsResidual jet).name
      certificate.primitive.integralSum.name :=
  namedEquivalent_of_scheduled_samples _ _ certificate.schedule
    certificate.budget.total certificate.budget.total_nonnegative
    certificate.residual_samples_close

/-- Finite operational Legendre Picard--Fuchs equation.  Its six channels use
one displayed lifted cycle, and the certificate exposes the common schedule
and complete finite error allocation used to make the residual vanish. -/
def operational_zero {parameter : Gaussian}
    {frame : CCL.Riemann.LegendrePaths.Frame parameter}
    {jet : SynchronizedPeriodJet frame}
    (certificate : PicardFuchsCertificate jet) :
    NamedEquivalent (picardFuchsResidual jet).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    certificate.residual_equivalent_primitive
    (CCL.Riemann.PeriodLinearity.exactDifferential_closed_operational_zero
      certificate.primitive)

end PicardFuchsCertificate

end CCL.Riemann.LegendrePeriodJets
