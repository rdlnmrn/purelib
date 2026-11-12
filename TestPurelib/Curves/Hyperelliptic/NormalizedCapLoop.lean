module

-- Diagnostic: compare the complete original coefficient comparison procedures, whose bodies remain opaque.
import all Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Normalization

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Normalization.Program
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Laurent
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Bounds
import Purelib.Tactic.QuotientFreeOmega

/-! # Whole coefficient-channel preservation and normalized cap-loop interfaces -/

namespace TestPurelib.Curves.Hyperelliptic.NormalizedCapLoop

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.RationalFunctions.Curve.Canonical.Circle

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : OddPowerDifferential curve.polynomial} {data : FormReadings.Circle.Polynomials differential}
    {jet : InfinityCoefficients.Jet curve} {origin : Owners.Point cap 0}
    {base : Canonical} {nonzero : base ≠ 0}
    {retained : jet.Principal data.1.val differential.scale}
    (circuit : Integral.Circuit base nonzero)
    (parameterCached : ParameterPrimitives retained circuit)
    (degreeBound : differential.numerator.natDegree ≤ 2 * genus)

/-- The complete original coefficient channel before accepting its exact table directly. -/
private abbrev formerCoefficientChannel :=
  (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart).mul
    (Coherence.exact (Ascending.Gaussian.Coefficient.coefficient parameterCached.table.val (parameterOrder curve)))

/-- Every retained primitive bank supplies the identical whole original coefficient channel. -/
example : Normalization.coefficientChannel (origin := origin) parameterCached.table =
    formerCoefficientChannel (origin := origin) (circuit := circuit) parameterCached := rfl

/-- The whole original ramified operational comparison, retained as an independent default regression. -/
private def formerOdd (ramified : HyperellipticReciprocal.originOrder curve = 1) :
    Equivalence.NamedEquivalent (formerCoefficientChannel (origin := origin) (circuit := circuit) parameterCached).name
      (Coherence.exact 0).name := by
  let reciprocal := div (Coherence.exact 1) origin.certificate.value origin.certificate.apart
  have coefficient := parameterPolynomial_odd_pivot retained ramified parameterCached.table
  have names := congrArg (fun value : Canonical => (reciprocal.mul (Coherence.exact value)).name) coefficient
  exact Eq.mp (congrArg (fun source => Equivalence.NamedEquivalent source (Coherence.exact 0).name) names.symm)
    (Arithmetic.Mul.coherentMul_zero_right reciprocal)

/-- The same retained table preserves the whole ramified comparison procedure. -/
example (ramified : HyperellipticReciprocal.originOrder curve = 1) :
    Normalization.coefficientChannel_odd (origin := origin) parameterCached.table ramified =
      formerOdd (origin := origin) (circuit := circuit) parameterCached ramified := rfl

include degreeBound in
/-- The whole original unramified operational comparison, retained as an independent default regression. -/
private def formerEven (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    Equivalence.NamedEquivalent (formerCoefficientChannel (origin := origin) (circuit := circuit) parameterCached).name
      ((div (Coherence.exact 1) origin.certificate.value origin.certificate.apart).mul
        (Coherence.exact (-differential.scale * InfinityCoefficients.evenFunctional curve jet
          (Ascending.Gaussian.Dense.Evaluation.toVector (2 * genus + 1)
            (Ascending.Gaussian.Dense.Evaluation.fromDense differential.numerator.normalize))))).name := by
  have count : differential.numerator.degreeCount ≤ 2 * genus + 1 := by
    have smaller := degreeBound
    change differential.numerator.degreeCount - 1 ≤ 2 * genus at smaller
    omega0
  have coefficient := (parameterPolynomial_even_pivot retained unramified parameterCached.table).trans
    (InfinityCoefficients.Jet.Principal.even_coefficient curve jet differential.numerator differential.scale
      count data.1 retained)
  let reciprocal := div (Coherence.exact 1) origin.certificate.value origin.certificate.apart
  have names := congrArg (fun value : Canonical => (reciprocal.mul (Coherence.exact value)).name) coefficient
  exact Eq.mp (congrArg (fun last => Equivalence.NamedEquivalent
    (formerCoefficientChannel (origin := origin) (circuit := circuit) parameterCached).name last) names)
      (Equivalence.NamedEquivalent.refl _)

/-- The same retained table preserves the whole signed comparison procedure. -/
example (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    Normalization.coefficientChannel_even (origin := origin) (degreeBound := degreeBound)
      parameterCached.table unramified =
      formerEven (origin := origin) (circuit := circuit) (degreeBound := degreeBound) parameterCached unramified := rfl

end TestPurelib.Curves.Hyperelliptic.NormalizedCapLoop

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs.Normalization

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Integration
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Division
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Rational.Geometric
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Riemann.Normalization
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {differential : OddPowerDifferential curve.polynomial} {base : Canonical} {nonzero : base ≠ 0}
  {unitBound : Norm.Basic.normSq base ≤ 1}
  {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
  {data : Polynomials differential} {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
  {origin : Owners.Point cap 0} {jet : InfinityCoefficients.Jet curve}
  {remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val}
  {retained : jet.Principal data.1.val differential.scale}
  {primitive : Antiderivative.ReciprocalPrimitive retained.val genus}

variable (circuit : Integral.Circuit base nonzero) (cached : data.Bounds base)
  (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
  (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
  (edges : DyadicEdges 0 start finish)
  (stored : Built (unitBound := unitBound) (collarBound := collarBound)
    circuit.1 cached pairs degreeBound bounds edges)
  (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
  (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor)
  (prepared : { value : Expansions (origin := origin) (jet := jet) (remainder := remainder)
      (retained := retained) (primitive := primitive) stored.val //
    value = expand circuit.1 cached pairs degreeBound bounds edges stored jetBounds anchor setup })
  (near : Norm.Basic.normSq base ≤ setup.val.1.val ^ 2)
  (expanded : { value : Expanded (origin := origin) (jet := jet) (remainder := remainder)
      (retained := retained) (primitive := primitive) stored.val //
    value = realize circuit.1 cached pairs degreeBound bounds edges stored jetBounds anchor setup prepared near })

variable
  (supplied : { value : stored.val.Result // value = stored.val.concatenate })
  (logarithmic : { value :
    (program : CertifiedProgram.Program (Integral.Logarithmic.operations circuit)) ×
      Equivalence.NamedEquivalent circuit.channel.name program.output.name //
    value = Integral.Logarithmic.program circuit })
  (parameterCached : ParameterPrimitives retained circuit)
  (polar : { value : (program : RefinementProgram) ×
    Equivalence.NamedEquivalent program.output.name (Coherence.exact 0).name //
    value = ⟨parameterCached.polarEdges.val.concatenate parameterCached.polar_count,
      parameterCached.polarEdges.val.concatenate_zero parameterCached.polar_count⟩ })
  (regular : { value : (program : RefinementProgram) ×
    Equivalence.NamedEquivalent program.output.name (Coherence.exact 0).name //
    value = ⟨parameterCached.regularEdges.val.concatenate parameterCached.regular_count,
      parameterCached.regularEdges.val.concatenate_zero parameterCached.regular_count⟩ })
  (principalSource : ParameterPrimitives.Program.View logarithmic parameterCached polar regular)
  (weighted : { value : _ // value = Principal.build logarithmic parameterCached polar regular principalSource
    (origin := origin) cached jetBounds })
  (selected : { value : stored.val.Result // value = selectLogarithmic stored.val logarithmic supplied })

variable (normalizer : { value : Division.Prepared circuit.channel // value = circuit.prepared })

include expanded

/-- The complete former prepared quotient comparison, retained independently to check its whole default procedure. -/
private def formerCompare (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
    (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (small : Norm.Basic.normSq base ≤ errorBounds.baseBudget
      (SmallWidth.shrinkingWidth 2
        (operandTarget (origin := origin) (circuit := circuit) parameterCached normalizer target) / 16384)) :
    Equivalence.Comparison
      (Name.Sampling.approximation (normalizer.val.quotient supplied.val.1.output).name)
      (Name.Sampling.approximation
        (normalizer.val.quotient (candidate (origin := origin) (circuit := circuit) parameterCached)).name)
      leftStart rightStart target := by
  let reference := candidate (origin := origin) (circuit := circuit) parameterCached
  let precision := SmallWidth.shrinkingWidth 2 target
  have precisionPositive : 0 < precision := SmallWidth.shrinkingWidth_pos (by decide) positive
  let input := SampleEquivalence.quotientComparisonTarget reference normalizer.val.denominator
    normalizer.val.apart normalizer.val.apart (precision / 4)
  have inputPositive : 0 < input :=
    operandTarget_positive (origin := origin) (circuit := circuit) parameterCached normalizer positive
  let numerator := compareShrinking circuit cached pairs degreeBound bounds edges stored jetBounds anchor setup
    prepared near expanded supplied logarithmic parameterCached polar regular principalSource weighted selected
    errorBounds 0 0 input inputPositive small
  let denominator := (Equivalence.NamedEquivalent.refl normalizer.val.denominator.name).compare
    0 0 input inputPositive
  let compared := Name.Coherent.Division.Equivalence.coherentDiv_comparison supplied.val.1.output
    reference normalizer.val.denominator normalizer.val.denominator
    normalizer.val.apart normalizer.val.apart numerator denominator leftStart rightStart precision precisionPositive
  have budget := SampleEquivalence.quotientComparison_budget_lt
    reference normalizer.val.denominator normalizer.val.apart normalizer.val.apart
    (Fraction.Order.Field.div_pos_direct precisionPositive (by decide : (0 : Fraction.Rational) < 4))
  have paid := (Fraction.Order.Field.lt_div_iff_pos (by decide : (0 : Fraction.Rational) < 4)).mp budget
  have bound : 4 * Approximation.Rational.Budget.Quotient.quotientBound 1
      (Name.Sampling.approximation reference.name).centerBound
      (Name.Sampling.approximation normalizer.val.denominator.name).centerBound
      (SampleEquivalence.commonLower normalizer.val.apart normalizer.val.apart) input input < precision := by
    exact (Fraction.Field.mul_comm _ _).trans_lt paid
  have doubled := SmallWidth.coefficient_mul_shrinkingWidth_lt (by decide : (0 : Fraction.Rational) ≤ 2) positive
  have margin := (Fraction.Order.Arithmetic.add_lt_add_right_direct bound precision).trans_eq
    (show precision + precision = 2 * precision by ring1)
  exact compared.weaken target (margin.trans doubled).le

/-- Every original input, comparison field and payment remains identical. -/
example : @compare = @formerCompare := rfl

/-- The complete former coefficient comparison, with only its proved identical table endpoint made explicit. -/
private def formerCompareCoefficient (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
    (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (small : Norm.Basic.normSq base ≤ errorBounds.baseBudget
      (SmallWidth.shrinkingWidth 2 (operandTarget (origin := origin) (circuit := circuit) parameterCached normalizer
        (SmallWidth.shrinkingWidth 4 target)) / 16384)) :
    Equivalence.Comparison
      (Name.Sampling.approximation (normalizer.val.quotient supplied.val.1.output).name)
      (Name.Sampling.approximation
        (coefficientChannel (origin := origin) parameterCached.table).name)
      leftStart rightStart target := by
  let precision := SmallWidth.shrinkingWidth 4 target
  have precisionPositive : 0 < precision := SmallWidth.shrinkingWidth_pos (by decide) positive
  let first := compare circuit cached pairs degreeBound bounds edges stored jetBounds anchor setup
    prepared near expanded supplied logarithmic parameterCached polar regular principalSource weighted selected
    normalizer errorBounds leftStart 0 precision precisionPositive small
  let second := (candidate_quotient_equivalent (origin := origin) (circuit := circuit)
    parameterCached normalizer).compare 0 rightStart precision precisionPositive
  have paid := SmallWidth.coefficient_mul_shrinkingWidth_lt (by decide : (0 : Fraction.Rational) ≤ 4) positive
  have grouped : 2 * (precision + precision) = 4 * precision := by ring1
  exact (first.trans second).weaken target (grouped.trans_lt paid).le

attribute [local irreducible] compare candidate_quotient_equivalent

/-- The entire original two-leg coefficient comparison and payment are unchanged for all inputs. -/
example (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
    (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (small : Norm.Basic.normSq base ≤ errorBounds.baseBudget
      (SmallWidth.shrinkingWidth 2 (operandTarget (origin := origin) (circuit := circuit) parameterCached normalizer
        (SmallWidth.shrinkingWidth 4 target)) / 16384)) :
    compareCoefficient circuit cached pairs degreeBound bounds edges stored jetBounds anchor setup
      prepared near expanded supplied logarithmic parameterCached polar regular principalSource weighted selected
      normalizer errorBounds leftStart rightStart target positive small =
    formerCompareCoefficient circuit cached pairs degreeBound bounds edges stored jetBounds anchor setup
      prepared near expanded supplied logarithmic parameterCached polar regular principalSource weighted selected
      normalizer errorBounds leftStart rightStart target positive small := by
  unfold compareCoefficient formerCompareCoefficient
  rfl

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs.Normalization
