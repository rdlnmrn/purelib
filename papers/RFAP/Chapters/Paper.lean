module
public import Purelib.RootIsolation.Resource.Basic
import Purelib.RootIsolation.Resource.Budget
import Purelib.RootIsolation.Resource.Build
import Purelib.RootIsolation.Resource.Input
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Selection
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.RationalFunctions.ArgumentPrinciple.General
public import Purelib.RationalFunctions.ArgumentPrinciple.Squarefree
import Purelib.RationalFunctions.Reduction.Basic
import Purelib.RationalFunctions.Reduction.Build
public import Purelib.RationalFunctions.Residual.Basic
public import Purelib.RationalFunctions.Residual.Local.Basic
import Purelib.RootIsolation.FTA.Multiplicity.Basic
public import Purelib.RootIsolation.FTA.Multiplicity.Build
import Purelib.RootIsolation.FTA.Positive.Basic
import Purelib.RootIsolation.FTA.Positive.Build
import Purelib.RootIsolation.FTA.Positive.Input
import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.RootIsolation.FTA.Squarefree.Input
public import Purelib.RootIsolation.Residual.Chordal.Adjustable
import Purelib.RootIsolation.Residual.Chordal.Basic
import Purelib.RootIsolation.Residual.Chordal.Linear
import Purelib.RootIsolation.Residual.Global.Assignment
public import Purelib.RootIsolation.Residual.Global.Observation
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Dense.Gaussian.Irreducible.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Irreducible

@[expose] public section

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

namespace Purelib.Papers.RFAP.Paper

open Purelib.Data.Rat in
/-- The executable rational coordinate type. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical pair of executable rational coordinates. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian.Basic in
/-- Dense polynomials with canonical Gaussian-rational coefficients. -/
abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic in
/-- Finite Bézout evidence relating the retained polynomial and its derivative. -/
abbrev SquarefreeCertificate (p : GaussianPolynomial) :=
  Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p
open Purelib.Polynomial.Dense.Gaussian.Irreducible in
/-- Constructive positive-degree irreducibility against proper polynomial divisors. -/
abbrev IrreducibleCertificate (p : GaussianPolynomial) :=
  Basic.IrreducibleCertificate p
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition in
/-- Exact zero, constant or squarefree-factor preprocessing of the original polynomial. -/
abbrev Preprocessing (p : GaussianPolynomial) :=
  Compute.Preprocessing p
open Purelib.RootIsolation.FTA.Multiplicity in
/-- Total box isolation retaining the original polynomial and exact multiplicities. -/
abbrev GeneralBoxResult (p : GaussianPolynomial) :=
  Basic.BoxResult p
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis in
/-- A positive-degree squarefree factor with its retained positive multiplicity. -/
abbrev MultiplicityEntry :=
  Positive.PositiveEntry
open Purelib.RootIsolation.FTA.Positive in
/-- Squarefree evidence and a positive-degree certificate for box isolation. -/
abbrev BoxInput (p : GaussianPolynomial) :=
  Input.PositiveInput p

open Purelib.RootIsolation.FTA.Squarefree in
/-- The finite input for squarefree box isolation in degree greater than one. -/
abbrev HigherBoxInput (p : GaussianPolynomial) :=
  RootIsolation.FTA.Squarefree.Input p

open Purelib.RootIsolation.FTA.Positive in
/-- Standalone exact degree-many winding-box result and maximality theorem. -/
abbrev BoxResult (p : GaussianPolynomial) :=
  Basic.PositiveResult p

open Purelib.RootIsolation.FTA in
/-- Degree-many squarefree root boxes with separation and maximality evidence. -/
abbrev HigherBoxResult (p : GaussianPolynomial) :=
  Squarefree.BoxResult p

open Purelib.RootIsolation.Resource in
/-- Displayed RFAP-I data for the finite eliminant, clearing, Sturm,
safe-cut, winding, and repeated-refinement resource calculation. -/
abbrev StageThreeInput := Input.StageThreeInput

open Purelib.Geometry.Rational (Box) in
open Purelib.RootIsolation.Resource.Input in
open Purelib.RootIsolation.State in
/-- Build the standard resource input from the same executable
separated-Sylvester axis certificate used by RFAP-I subdivision. -/
def separatedStageThreeInput
    {p : GaussianPolynomial} {ambient : Box}
    (nonzero : p.isZero = false) (degreePositive : 0 < p.natDegree)
    (state : Raw.RawWindingState p ambient)
    (threshold : Coordinate) : StageThreeInput :=
  StageThreeInput.ofSeparated nonzero degreePositive
    state threshold

section
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Elimination.Axis.Certificate
open Purelib.RootIsolation.Residual.Chordal
open Purelib.RootIsolation.State.WindingOne
/-- A retained local root-box result with the requested residual-to-chordal bound. -/
abbrev ResidualChordalResult
    {p : GaussianPolynomial} {ambient : Box}
    {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination :
      AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current :
      Basic.WindingOneState p ambient)
    (sample : Gaussian) (epsilon : Coordinate) :=
  Basic.ResidualChordalResult
    squarefree elimination current sample epsilon

/-- The exact-zero or certified local root-box observation at the supplied sample and scale. -/
abbrev ResidualChordalObservation
    {p : GaussianPolynomial} {ambient : Box}
    {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination :
      AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current :
      Basic.WindingOneState p ambient)
    (sample : Gaussian) (epsilon : Coordinate) :=
  Basic.ResidualChordalObservation
    squarefree elimination current sample epsilon

/-- Output of the residual corollary at a caller-supplied rational factor. -/
abbrev AdjustableLinearResidualChordalResult
    {p : GaussianPolynomial} {ambient : Box}
    {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination :
      AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current :
      Basic.WindingOneState p ambient)
    (sample : Gaussian) (factor : Coordinate) :=
  Adjustable.AdjustableLinearResidualChordalResult
    squarefree elimination current sample factor

/-- Exact-zero-or-band output of the factor-parameterized residual
corollary. -/
abbrev AdjustableLinearResidualChordalObservation
    {p : GaussianPolynomial} {ambient : Box}
    {degreeBound : Nat}
    (squarefree : SquarefreeCertificate p)
    (elimination :
      AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current :
      Basic.WindingOneState p ambient)
    (sample : Gaussian) (factor : Coordinate) :=
  Adjustable.AdjustableLinearResidualChordalObservation
    squarefree elimination current sample factor

end

section
open Purelib.RootIsolation.Residual.Global
/-- Globally localized winding-one box and its finite isolation owner. -/
abbrev GlobalResidualAssignedResult
    {p : GaussianPolynomial} (input : HigherBoxInput p)
    (sample : Gaussian) (epsilon : Coordinate) :=
  Assignment.AssignedResult input sample epsilon

/-- Exact-zero, globally assigned box, or explicit residual-threshold
failure for an arbitrary displayed sample. -/
abbrev GlobalResidualObservation
    {p : GaussianPolynomial} (input : HigherBoxInput p)
    (sample : Gaussian) (epsilon : Coordinate) :=
  RootIsolation.Residual.Global.Observation input sample epsilon

end

open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual in
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition in
/-- A selected retained multiplicity factor with the required small-residual bound. -/
abbrev MultiplicitySmallFactor
    {p : GaussianPolynomial} (decomposition : Polynomial.Dense.Gaussian.Squarefree.Decomposition p)
    (sample : Gaussian) (delta : Coordinate) :=
  Selection.SmallFactor decomposition sample delta

open Purelib.RationalFunctions.Reduction in
/-- Exact common-factor cancellation preserving the original numerator and denominator. -/
abbrev RationalReduction
    (numerator denominator : GaussianPolynomial) :=
  Basic.ReducedPair numerator denominator

section
open Purelib.RationalFunctions.ArgumentPrinciple
/-- The total finite argument-principle result for the supplied rational-function presentation. -/
abbrev RationalResult
    (numerator denominator : GaussianPolynomial) :=
  General.Result numerator denominator

/-- The finite zero and pole families for a nonzero rational-function presentation. -/
abbrev NonzeroRationalResult
    (numerator denominator : GaussianPolynomial) :=
  General.NonzeroResult numerator denominator

/-- A reduced rational-function presentation with finite squarefree cofactor evidence. -/
abbrev SquarefreeRationalInput
    (numerator denominator : GaussianPolynomial) :=
  Squarefree.SquarefreeInput
    numerator denominator

/-- Degree-sharp zero and pole isolation for the retained squarefree rational input. -/
abbrev SquarefreeRationalResult
    (numerator denominator : GaussianPolynomial) :=
  Squarefree.SquarefreeResult
    numerator denominator

end

open Purelib.Geometry.Rational (Box) in
open Purelib.RationalFunctions.Residual.Local in
/-- The retained local quotient data for both polynomial owners and the ambient rational box. -/
abbrev LocalQuotientContext
    (source opposite : GaussianPolynomial)
    (ambient : Box) :=
  Basic.LocalQuotientContext
    source opposite ambient

open Purelib.RationalFunctions.Residual in
/-- Squared norm of a displayed reduced quotient value.  Quantitative uses
carry a nonvanishing proof for the displayed denominator value. -/
def quotientResidualSq
    (source opposite : GaussianPolynomial) (sample : Gaussian) : Coordinate :=
  Basic.quotientResidualSq
    source opposite sample

section
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition
/-- Total zero/constant/positive-degree preprocessing into finite squarefree
occurrences.  `multiplicityEntries` performs the further exact overlap
refinement on its positive decomposition. -/
def preprocessPolynomial (p : GaussianPolynomial) : Preprocessing p :=
  Compute.preprocess p

/-- Exact pairwise-coprime positive-degree multiplicity basis of a complete
squarefree occurrence decomposition. -/
def multiplicityEntries
    {p : GaussianPolynomial}
    (decomposition : Polynomial.Dense.Gaussian.Squarefree.Decomposition p) :
    List MultiplicityEntry :=
  decomposition.positiveMultiplicityEntries

end

open Purelib.RootIsolation.FTA.Multiplicity in
/-- Total box preprocessing and isolation for zero, constant, and
positive-degree displayed polynomials, isolating each pairwise-coprime
squarefree factor once with its exact multiplicity. -/
def isolateGeneralByBoxes (p : GaussianPolynomial) : GeneralBoxResult p :=
  Build.isolateByBoxes p

section
open Purelib.RootIsolation.FTA.Positive
/-- Box-only finite FTA in every positive degree.  Degree one returns its
exact rational terminal; higher degree returns exact degree-many isolation,
pairwise separation, zero-winding remainder evidence, and maximality. -/
def isolateByBoxes
    {p : GaussianPolynomial} (input : BoxInput p) : BoxResult p :=
  Build.provePositive input

/-- Degree-greater-than-one box theorem from the explicit finite squarefree
certificate used by the numerical proof. -/
def isolateDegreeGtOneByBoxes
    {p : GaussianPolynomial} (squarefree : SquarefreeCertificate p)
    (degree : 1 < p.natDegree) : BoxResult p :=
  Build.provePositiveDegreeGtOne squarefree degree

end

open Purelib.Polynomial.Dense.Gaussian.Squarefree in
/-- Box-only isolation with the squarefree input derived constructively from
finite proper-divisor irreducibility. -/
def isolateIrreducibleByBoxes
    {p : GaussianPolynomial} (irreducible : IrreducibleCertificate p) :
    BoxResult p :=
  isolateByBoxes
    { squarefree :=
        Irreducible.squarefreeOfIrreducible irreducible
      degreePositive := irreducible.degreePositive }

/-! ## Local residual-to-chordal converse -/

open Purelib.Geometry.Rational (Box) in
open Purelib.RootIsolation.Residual.Chordal in
open Purelib.RootIsolation.State.WindingOne in
/-- Positive point-specific residual threshold for constructing a nearby
winding-one box at a requested chordal scale. -/
def residualChordalTarget
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current :
      Basic.WindingOneState p ambient)
    (sample : Gaussian) (epsilon : Coordinate) : Coordinate :=
  Basic.residualTarget
    squarefree current sample epsilon

open Purelib.Data.Gaussian.Norm.Basic in
open Purelib.Geometry.Rational (Box) in
open Purelib.Polynomial.Elimination.Axis.Certificate in
open Purelib.RootIsolation.Residual.Chordal in
open Purelib.RootIsolation.State.WindingOne in
/-- Local constructive converse to the box-to-residual estimate.  A small
displayed residual inside a known winding-one state constructs a strictly
nested winding-one box, its total RAT, and the explicit `18 * epsilon^2`
affine chordal bound. -/
def isolateNearSmallResidual
    {p : GaussianPolynomial} {ambient : Box}
    {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination :
      AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current :
      Basic.WindingOneState p ambient)
    (sample : Gaussian) (strict : current.box.StrictContains sample)
    {epsilon : Coordinate} (epsilonPositive : 0 < epsilon)
    (residualSmall :
      normSq (p.eval sample) <
        residualChordalTarget squarefree current sample epsilon) :
    ResidualChordalObservation squarefree elimination current sample epsilon :=
  Basic.observeOfResidual degreeAtLeastTwo squarefree
    elimination current sample strict epsilonPositive residualSmall

section
open Purelib.Geometry.Rational (Box)
open Purelib.RootIsolation.Residual.Chordal
open Purelib.RootIsolation.State.WindingOne
/-- Positive coefficient- and box-computed scale `mu` in the sharper local
dyadic residual corollary. -/
def linearResidualChordalScale
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current :
      Basic.WindingOneState p ambient) : Coordinate :=
  Linear.linearResidualScale squarefree current

/-- Positive point-specific threshold placing the requested finite bracket
beneath all geometric, derivative, and Taylor safety caps. -/
def adjustableLinearResidualChordalThreshold
    {p : GaussianPolynomial} {ambient : Box}
    (squarefree : SquarefreeCertificate p)
    (current :
      Basic.WindingOneState p ambient)
    (sample : Gaussian) (factor : Coordinate) : Coordinate :=
  Adjustable.adjustableLinearResidualThreshold
    squarefree current sample factor

end

open Purelib.Data.Gaussian.Norm.Basic in
open Purelib.Geometry.Rational (Box) in
open Purelib.Polynomial.Elimination.Axis.Certificate in
open Purelib.RootIsolation.Residual.Chordal in
open Purelib.RootIsolation.State.WindingOne in
/-- Factor-parameterized local converse.  For every displayed rational
`factor > 1`, a precomputed finite number of rational comparisons gives
`chi^2 <= ((18 * factor) / mu) * normSq (p.eval sample)` and
`diagonalSq <= ((32 * factor) / mu) * normSq (p.eval sample)`. -/
def isolateNearAdjustableLinearResidual
    {p : GaussianPolynomial} {ambient : Box}
    {degreeBound : Nat}
    (degreeAtLeastTwo : 2 <= p.natDegree)
    (squarefree : SquarefreeCertificate p)
    (elimination :
      AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current :
      Basic.WindingOneState p ambient)
    (sample : Gaussian) (strict : current.box.StrictContains sample)
    (factor : Coordinate) (factorGreater : 1 < factor)
    (residualSmall :
      normSq (p.eval sample) <
        adjustableLinearResidualChordalThreshold squarefree current sample
          factor) :
    AdjustableLinearResidualChordalObservation squarefree elimination current
      sample factor :=
  Adjustable.observeOfAdjustableLinearResidual degreeAtLeastTwo
    squarefree elimination current sample strict factor factorGreater
      residualSmall

/-! ## Global residual-to-box localization -/

section
open Purelib.RootIsolation.Residual.Global
/-- Positive coefficient-computed threshold used to classify an arbitrary
displayed sample globally. -/
def globalResidualChordalThreshold
    {p : GaussianPolynomial} (input : HigherBoxInput p)
    (sample : Gaussian) (epsilon : Coordinate) : Coordinate :=
  Assignment.residualThreshold input sample epsilon

/-- Total global displayed-sample classifier.  The assigned branch returns a
nearby winding-one box, total track, and deterministic member of the existing
degree-sized isolation; the failure branch proves the explicit threshold was
not met. -/
def classifyGlobalResidual
    {p : GaussianPolynomial} (input : HigherBoxInput p)
    (sample : Gaussian) {epsilon : Coordinate}
    (epsilonPositive : 0 < epsilon) :
    GlobalResidualObservation input sample epsilon :=
  Observation.classify input sample epsilonPositive

/-! ## Repeated-factor residual selection -/

end

open Purelib.Data.Gaussian.Norm.Basic in
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual in
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition in
/-- Select one displayed squarefree multiplicity-basis factor from a small
original-polynomial residual, using the exact nonzero unit quadrance and the
finite total multiplicity in the threshold. -/
def selectSmallMultiplicityFactor
    {p : GaussianPolynomial}
    (decomposition : Polynomial.Dense.Gaussian.Squarefree.Decomposition p)
    (sample : Gaussian) {delta : Coordinate} (deltaPositive : 0 < delta)
    (small : normSq (p.eval sample) <
      Basic.unitQuadrance decomposition *
        delta ^ Basic.multiplicityCount
          decomposition.positiveMultiplicityEntries) :
    MultiplicitySmallFactor decomposition sample delta :=
  Selection.selectSmallFactor decomposition sample
    deltaPositive small

/-! ## Rational-function addendum -/

open Purelib.RationalFunctions.Reduction in
/-- Execute finite gcd cancellation and retain the exact factorization,
Bézout, and degree-balance certificates. -/
def reduceRationalFunction
    (numerator denominator : GaussianPolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    RationalReduction numerator denominator :=
  Build.reduce numerator denominator
    denominatorNonzero

section
open Purelib.RationalFunctions.ArgumentPrinciple
/-- Total constructive RFAP for an arbitrary displayed numerator and
nonzero denominator.  A zero numerator has its own constructor; otherwise
the result contains the finite multiplicity families, exact rational
terminals or shrinking tracks, joint separation, signed local windings, and
the outer reduced-degree difference. -/
def rationalFunctionArgumentPrinciple
    (numerator denominator : GaussianPolynomial)
    (denominatorNonzero : denominator.isZero = false) :
    RationalResult numerator denominator :=
  General.prove numerator denominator
    denominatorNonzero

/-- Degree-sharp `+1`/`-1` specialization when both displayed reduced
cofactors carry finite squarefree certificates. -/
def squarefreeRationalFunctionArgumentPrinciple
    {numerator denominator : GaussianPolynomial}
    (input : SquarefreeRationalInput numerator denominator) :
    SquarefreeRationalResult numerator denominator :=
  Squarefree.proveSquarefree input

/-! ## Finite RFAP-I calculation-size certificate -/

end

open Purelib.RootIsolation.Resource
/-- Aggregate accounted-operation budget for the normalized RFAP-I
eliminant, clearing, Sturm, winding, and repeated-refinement calculation. -/
def stageThreeStepBudget (input : StageThreeInput) : Nat :=
  Budget.stageThreeStepBudget input

/-- Aggregate component-bit budget for the same RFAP-I calculation. -/
def stageThreeBitBudget (input : StageThreeInput) : Nat :=
  Budget.stageThreeBitBudget input

/-- A single constructive certificate for the normalized eliminant and
B\'ezout records, cleared coefficients, every retained refinement box, and
every Sturm chain used by the subdivision windings. -/
theorem stageThreeResourceCertificate (input : StageThreeInput) :
    Basic.StageThreeResourcesWithin input
      (stageThreeStepBudget input) (stageThreeBitBudget input) :=
  Build.stageThree_resource_certificate input

end Purelib.Papers.RFAP.Paper
