import RFAP.Isolation.GeneralBoxFTA
import RFAP.CalculationSize
import RFAP.Polynomial.Irreducible
import RFAP.Polynomial.MultiplicityResidual
import RFAP.Sturm.OneDimensional
import RFAP.Rational.Sites
import RFAP.Rational.ResidualChordal
import RFAP.Geometry.GlobalResidual
import RFAP.Rational.FunctionArgumentPrinciple

/-!
# Paper-I API for finite constructive FTA

This facade exposes only the finite coefficient, Sturm, winding, and rational
box development.  It contains no finite-name encoder, parser, cylinder, or
persistent-prefix dependency.  `isolateByBoxes` returns an exact displayed
Gaussian-rational root in degree one, or exact degree-many winding-box
isolation and degree-sharp maximality in higher degree.

The `isolateIrreducible...` wrappers derive the finite squarefree Bézout
certificate from a constructive proper-divisor irreducibility certificate.
For arbitrary displayed polynomials, `isolateGeneralByBoxes` first computes an
exact weighted product of pairwise-coprime squarefree positive-degree factors.
Every distinct factor is isolated once and carries its exact multiplicity.
-/

namespace RFAP.Paper

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.BoxFTA.GaussianPolynomial
abbrev SquarefreeCertificate (p : GaussianPolynomial) :=
  RFAP.BoxFTA.SquarefreeCertificate p
abbrev IrreducibleCertificate (p : GaussianPolynomial) :=
  RFAP.Irreducible.IrreducibleCertificate p
abbrev Preprocessing (p : GaussianPolynomial) :=
  RFAP.Factorization.Preprocessing p
abbrev GeneralBoxResult (p : GaussianPolynomial) :=
  RFAP.GeneralBoxFTA.BoxResult p
abbrev MultiplicityEntry :=
  RFAP.Multiplicity.PositiveEntry
abbrev BoxInput (p : GaussianPolynomial) :=
  RFAP.BoxFTA.PositiveInput p

abbrev HigherBoxInput (p : GaussianPolynomial) :=
  RFAP.BoxFTA.Input p

/-- Standalone exact degree-many winding-box result and maximality theorem. -/
abbrev BoxResult (p : GaussianPolynomial) :=
  RFAP.BoxFTA.PositiveResult p

abbrev HigherBoxResult (p : GaussianPolynomial) :=
  RFAP.BoxFTA.Result p

/-- Displayed RFAP-I data for the finite eliminant, clearing, Sturm,
safe-cut, winding, and repeated-refinement resource calculation. -/
abbrev StageThreeInput := RFAP.PaperCalculationSize.StageThreeInput

/-- Build the standard resource input from the same executable
separated-Sylvester axis certificate used by RFAP-I subdivision. -/
def separatedStageThreeInput
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (state : RFAP.RawSubdivision.RawWindingState p ambient)
    (threshold : Coordinate) : StageThreeInput :=
  RFAP.PaperCalculationSize.StageThreeInput.ofSeparated nonzero degreePositive
    state threshold

abbrev ResidualChordalResult
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current :
      RFAP.ShrinkingTrack.WindingOneState p ambient)
    (sample : Gaussian) (epsilon : Coordinate) :=
  RFAP.ResidualChordal.ResidualChordalResult
    squarefree elimination current sample epsilon

abbrev ResidualChordalObservation
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current :
      RFAP.ShrinkingTrack.WindingOneState p ambient)
    (sample : Gaussian) (epsilon : Coordinate) :=
  RFAP.ResidualChordal.ResidualChordalObservation
    squarefree elimination current sample epsilon

/-- Output of the residual corollary at a caller-supplied rational factor. -/
abbrev AdjustableLinearResidualChordalResult
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current :
      RFAP.ShrinkingTrack.WindingOneState p ambient)
    (sample : Gaussian) (factor : Coordinate) :=
  RFAP.ResidualChordal.AdjustableLinearResidualChordalResult
    squarefree elimination current sample factor

/-- Exact-zero-or-band output of the factor-parameterized residual
corollary. -/
abbrev AdjustableLinearResidualChordalObservation
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current :
      RFAP.ShrinkingTrack.WindingOneState p ambient)
    (sample : Gaussian) (factor : Coordinate) :=
  RFAP.ResidualChordal.AdjustableLinearResidualChordalObservation
    squarefree elimination current sample factor

/-- Globally localized winding-one box and its finite isolation owner. -/
abbrev GlobalResidualAssignedResult
    {p : GaussianPolynomial} (input : HigherBoxInput p)
    (sample : Gaussian) (epsilon : Coordinate) :=
  RFAP.GlobalResidual.AssignedResult input sample epsilon

/-- Exact-zero, globally assigned box, or explicit residual-threshold
failure for an arbitrary displayed sample. -/
abbrev GlobalResidualObservation
    {p : GaussianPolynomial} (input : HigherBoxInput p)
    (sample : Gaussian) (epsilon : Coordinate) :=
  RFAP.GlobalResidual.Observation input sample epsilon

abbrev MultiplicitySmallFactor
    {p : GaussianPolynomial} (decomposition : RFAP.Factorization.Decomposition p)
    (sample : Gaussian) (delta : Coordinate) :=
  RFAP.MultiplicityResidual.SmallFactor decomposition sample delta

abbrev RationalReduction
    (numerator denominator : GaussianPolynomial) :=
  RFAP.RationalReduction.ReducedPair numerator denominator

abbrev RationalResult
    (numerator denominator : GaussianPolynomial) :=
  RFAP.RationalSites.Result numerator denominator

abbrev NonzeroRationalResult
    (numerator denominator : GaussianPolynomial) :=
  RFAP.RationalSites.NonzeroResult numerator denominator

abbrev SquarefreeRationalInput
    (numerator denominator : GaussianPolynomial) :=
  RFAP.RationalFunctionArgumentPrinciple.SquarefreeInput
    numerator denominator

abbrev SquarefreeRationalResult
    (numerator denominator : GaussianPolynomial) :=
  RFAP.RationalFunctionArgumentPrinciple.SquarefreeResult
    numerator denominator

abbrev LocalQuotientContext
    (source opposite : GaussianPolynomial)
    (ambient : RFAP.Boxes.Box) :=
  RFAP.RationalResidualChordal.LocalQuotientContext
    source opposite ambient

/-- Squared norm of a displayed reduced quotient value.  Quantitative uses
carry a nonvanishing proof for the displayed denominator value. -/
def quotientResidualSq
    (source opposite : GaussianPolynomial) (sample : Gaussian) : Coordinate :=
  RFAP.RationalResidualChordal.quotientResidualSq
    source opposite sample

/-- Total zero/constant/positive-degree preprocessing into finite squarefree
occurrences.  `multiplicityEntries` performs the further exact overlap
refinement on its positive decomposition. -/
def preprocessPolynomial (p : GaussianPolynomial) : Preprocessing p :=
  RFAP.Factorization.preprocess p

/-- Exact pairwise-coprime positive-degree multiplicity basis of a complete
squarefree occurrence decomposition. -/
def multiplicityEntries
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p) :
    List MultiplicityEntry :=
  decomposition.positiveMultiplicityEntries

/-- Total box preprocessing and isolation for zero, constant, and
positive-degree displayed polynomials, isolating each pairwise-coprime
squarefree factor once with its exact multiplicity. -/
def isolateGeneralByBoxes (p : GaussianPolynomial) : GeneralBoxResult p :=
  RFAP.GeneralBoxFTA.isolateByBoxes p

/-- Box-only finite FTA in every positive degree.  Degree one returns its
exact rational terminal; higher degree returns exact degree-many isolation,
pairwise separation, zero-winding remainder evidence, and maximality. -/
def isolateByBoxes
    {p : GaussianPolynomial} (input : BoxInput p) : BoxResult p :=
  RFAP.BoxFTA.provePositive input

/-- Degree-greater-than-one box theorem from the explicit finite squarefree
certificate used by the numerical proof. -/
def isolateDegreeGtOneByBoxes
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (degree : 1 < p.natDegree) : BoxResult p :=
  RFAP.BoxFTA.provePositiveDegreeGtOne squarefree degree

/-- Box-only isolation with the squarefree input derived constructively from
finite proper-divisor irreducibility. -/
def isolateIrreducibleByBoxes
    {p : GaussianPolynomial} (irreducible : IrreducibleCertificate p) :
    BoxResult p :=
  isolateByBoxes
    { squarefree :=
        RFAP.Irreducible.squarefreeOfIrreducible irreducible
      degreePositive := irreducible.degreePositive }

/-! ## Local residual-to-chordal converse -/

/-- Positive point-specific residual threshold for constructing a nearby
winding-one box at a requested chordal scale. -/
def residualChordalTarget
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    (squarefree : SquarefreeCertificate p)
    (current :
      RFAP.ShrinkingTrack.WindingOneState p ambient)
    (sample : Gaussian) (epsilon : Coordinate) : Coordinate :=
  RFAP.ResidualChordal.residualTarget
    squarefree current sample epsilon

/-- Local constructive converse to the box-to-residual estimate.  A small
displayed residual inside a known winding-one state constructs a strictly
nested winding-one box, its total RAT, and the explicit `18 * epsilon^2`
affine chordal bound. -/
def isolateNearSmallResidual
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current :
      RFAP.ShrinkingTrack.WindingOneState p ambient)
    (sample : Gaussian) (strict : current.box.StrictContains sample)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon)
    (residualSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq (p.eval sample) <
        residualChordalTarget squarefree current sample epsilon) :
    ResidualChordalObservation squarefree elimination current sample epsilon :=
  RFAP.ResidualChordal.observeOfResidual degreeAtLeastTwo squarefree
    elimination current sample strict epsilonPositive residualSmall

/-- Positive coefficient- and box-computed scale `mu` in the sharper local
dyadic residual corollary. -/
def linearResidualChordalScale
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    (squarefree : SquarefreeCertificate p)
    (current :
      RFAP.ShrinkingTrack.WindingOneState p ambient) : Coordinate :=
  RFAP.ResidualChordal.linearResidualScale squarefree current

/-- Positive point-specific threshold placing the requested finite bracket
beneath all geometric, derivative, and Taylor safety caps. -/
def adjustableLinearResidualChordalThreshold
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    (squarefree : SquarefreeCertificate p)
    (current :
      RFAP.ShrinkingTrack.WindingOneState p ambient)
    (sample : Gaussian) (factor : Coordinate) : Coordinate :=
  RFAP.ResidualChordal.adjustableLinearResidualThreshold
    squarefree current sample factor

/-- Factor-parameterized local converse.  For every displayed rational
`factor > 1`, a precomputed finite number of rational comparisons gives
`chi^2 <= ((18 * factor) / mu) * normSq (p.eval sample)` and
`diagonalSq <= ((32 * factor) / mu) * normSq (p.eval sample)`. -/
def isolateNearAdjustableLinearResidual
    {p : GaussianPolynomial} {ambient : RFAP.Boxes.Box}
    {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination :
      RFAP.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current :
      RFAP.ShrinkingTrack.WindingOneState p ambient)
    (sample : Gaussian) (strict : current.box.StrictContains sample)
    (factor : Coordinate) (factorGreater : 1 < factor)
    (residualSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq (p.eval sample) <
        adjustableLinearResidualChordalThreshold squarefree current sample
          factor) :
    AdjustableLinearResidualChordalObservation squarefree elimination current
      sample factor :=
  RFAP.ResidualChordal.observeOfAdjustableLinearResidual degreeAtLeastTwo
    squarefree elimination current sample strict factor factorGreater
      residualSmall

/-! ## Global residual-to-box localization -/

/-- Positive coefficient-computed threshold used to classify an arbitrary
displayed sample globally. -/
def globalResidualChordalThreshold
    {p : GaussianPolynomial} (input : HigherBoxInput p)
    (sample : Gaussian) (epsilon : Coordinate) : Coordinate :=
  RFAP.GlobalResidual.residualThreshold input sample epsilon

/-- Total global displayed-sample classifier.  The assigned branch returns a
nearby winding-one box, total track, and deterministic member of the existing
degree-sized isolation; the failure branch proves the explicit threshold was
not met. -/
def classifyGlobalResidual
    {p : GaussianPolynomial} (input : HigherBoxInput p)
    (sample : Gaussian) {epsilon : Coordinate}
    (epsilonPositive : 0 < epsilon) :
    GlobalResidualObservation input sample epsilon :=
  RFAP.GlobalResidual.classify input sample epsilonPositive

/-! ## Repeated-factor residual selection -/

/-- Select one displayed squarefree multiplicity-basis factor from a small
original-polynomial residual, using the exact nonzero unit quadrance and the
finite total multiplicity in the threshold. -/
def selectSmallMultiplicityFactor
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p)
    (sample : Gaussian) {delta : Coordinate} (deltaPositive : 0 < delta)
    (small : RFAP.ConstructiveGaussian.Gaussian.normSq (p.eval sample) <
      RFAP.MultiplicityResidual.unitQuadrance decomposition *
        delta ^ RFAP.MultiplicityResidual.multiplicityCount
          decomposition.positiveMultiplicityEntries) :
    MultiplicitySmallFactor decomposition sample delta :=
  RFAP.MultiplicityResidual.selectSmallFactor decomposition sample
    deltaPositive small

/-! ## Rational-function addendum -/

/-- Execute finite gcd cancellation and retain the exact factorization,
Bézout, and degree-balance certificates. -/
def reduceRationalFunction
    (numerator denominator : GaussianPolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    RationalReduction numerator denominator :=
  RFAP.RationalReduction.reduce numerator denominator
    denominatorNonzero

/-- Total constructive RFAP for an arbitrary displayed numerator and
nonzero denominator.  A zero numerator has its own constructor; otherwise
the result contains the finite multiplicity families, exact rational
terminals or shrinking tracks, joint separation, signed local windings, and
the outer reduced-degree difference. -/
def rationalFunctionArgumentPrinciple
    (numerator denominator : GaussianPolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    RationalResult numerator denominator :=
  RFAP.RationalSites.prove numerator denominator
    denominatorNonzero

/-- Degree-sharp `+1`/`-1` specialization when both displayed reduced
cofactors carry finite squarefree certificates. -/
def squarefreeRationalFunctionArgumentPrinciple
    {numerator denominator : GaussianPolynomial}
    (input : SquarefreeRationalInput numerator denominator) :
    SquarefreeRationalResult numerator denominator :=
  RFAP.RationalFunctionArgumentPrinciple.proveSquarefree input

/-! ## Finite RFAP-I calculation-size certificate -/

/-- Aggregate accounted-operation budget for the normalized RFAP-I
eliminant, clearing, Sturm, winding, and repeated-refinement calculation. -/
def stageThreeStepBudget (input : StageThreeInput) : Nat :=
  RFAP.PaperCalculationSize.stageThreeStepBudget input

/-- Aggregate component-bit budget for the same RFAP-I calculation. -/
def stageThreeBitBudget (input : StageThreeInput) : Nat :=
  RFAP.PaperCalculationSize.stageThreeBitBudget input

/-- A single constructive certificate for the normalized eliminant and
B\'ezout records, cleared coefficients, every retained refinement box, and
every Sturm chain used by the subdivision windings. -/
theorem stageThreeResourceCertificate (input : StageThreeInput) :
    RFAP.PaperCalculationSize.StageThreeResourcesWithin input
      (stageThreeStepBudget input) (stageThreeBitBudget input) :=
  RFAP.PaperCalculationSize.stageThree_resource_certificate input

end RFAP.Paper
