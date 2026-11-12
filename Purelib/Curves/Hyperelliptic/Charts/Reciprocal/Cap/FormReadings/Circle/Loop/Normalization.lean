module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Comparison
import Purelib.Approximation.Gaussian.Division.Prepared.Quotient
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Division.SampleEquivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Rational.Budget.Quotient
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.SmallWidth
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.InfinityCoefficients
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Laurent
import Purelib.Approximation.Gaussian.Arithmetic.Mul

/-! # Normalization of the actual shrinking total-form loop by its retained logarithmic integral -/

public section

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

/-- The original guarded reciprocal, finite pivot and logarithmic channel viewed as one actual numerator. -/
abbrev candidate :=
  (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart).mul
    ((Coherence.exact (Ascending.Gaussian.Coefficient.coefficient parameterCached.table.val
      (parameterOrder curve))).mul circuit.channel)

/-- The original logarithmic request pays both operand errors below the strict normalization margin. -/
def operandTarget (target : Fraction.Rational) : Fraction.Rational :=
  SampleEquivalence.quotientComparisonTarget (candidate (origin := origin) (circuit := circuit) parameterCached)
    normalizer.val.denominator
    normalizer.val.apart normalizer.val.apart (SmallWidth.shrinkingWidth 2 target / 4)

/-- The normalization request uses the actual supplied numerator, prepared denominator and retained guards. -/
theorem operandTarget_eq (target : Fraction.Rational) :
    operandTarget (origin := origin) (circuit := circuit) parameterCached normalizer target =
      SampleEquivalence.quotientComparisonTarget (candidate (origin := origin) (circuit := circuit) parameterCached)
        normalizer.val.denominator normalizer.val.apart normalizer.val.apart
        (SmallWidth.shrinkingWidth 2 target / 4) := (rfl)

/-- The computed normalization operand request is positive for every positive requested output tolerance. -/
theorem operandTarget_positive {target : Fraction.Rational} (positive : 0 < target) :
    0 < operandTarget (origin := origin) (circuit := circuit) parameterCached normalizer target :=
  SampleEquivalence.quotientComparisonTarget_positive
    (candidate (origin := origin) (circuit := circuit) parameterCached)
    normalizer.val.denominator
    normalizer.val.apart normalizer.val.apart
    (Fraction.Order.Field.div_pos_direct (SmallWidth.shrinkingWidth_pos (by decide) positive) (by decide))

/-- The actual origin reciprocal times the same retained substituted-table pivot. -/
abbrev coefficientChannel
    (table : { value : CoefficientPolynomial // value = parameterPolynomial retained }) :=
  (div (Coherence.exact 1) origin.certificate.value origin.certificate.apart).mul
    (Coherence.exact (Ascending.Gaussian.Coefficient.coefficient table.val (parameterOrder curve)))

/-- The prepared actual logarithmic denominator cancels from the same original principal numerator.

Associativity and the prepared integral's original operational comparison
relate the actual numerator to its retained denominator product. Original
guarded quotient cancellation then gives the stated channel identity;
no exact value for the integral or independent preparation is assumed.
-/
def candidate_quotient_equivalent :
    Equivalence.NamedEquivalent
      (normalizer.val.quotient (candidate (origin := origin) (circuit := circuit) parameterCached)).name
      (coefficientChannel (origin := origin) parameterCached.table).name := by
  let reciprocal := div (Coherence.exact 1) origin.certificate.value origin.certificate.apart
  let pivot := Coherence.exact (Ascending.Gaussian.Coefficient.coefficient parameterCached.table.val
    (parameterOrder curve))
  let logarithm := circuit.channel
  let actual := reciprocal.mul (pivot.mul logarithm)
  let first := Laws.coherentMul_assoc reciprocal pivot normalizer.val.denominator
  let second := Congruence.coherentMul_respects pivot pivot normalizer.val.denominator logarithm
    (Equivalence.NamedEquivalent.refl _) normalizer.val.equivalent.symm
  let replaced := Congruence.coherentMul_respects reciprocal reciprocal
    (pivot.mul normalizer.val.denominator) (pivot.mul logarithm)
    (Equivalence.NamedEquivalent.refl _) second
  exact (Division.Cancellation.coherentDiv_of_mul (reciprocal.mul pivot) normalizer.val.denominator
    actual normalizer.val.apart
    (first.trans replaced)).symm

/-- The actual ramified table makes the retained normalized coefficient channel operationally zero.

The original odd-pivot theorem consumes the supplied complete table.
Its scalar equality transports the same origin reciprocal product, and
original multiplication by zero gives the operational identity.
-/
def coefficientChannel_odd
    (table : { value : CoefficientPolynomial // value = parameterPolynomial retained })
    (ramified : HyperellipticReciprocal.originOrder curve = 1) :
    Equivalence.NamedEquivalent (coefficientChannel (origin := origin) table).name
      (Coherence.exact 0).name := by
  let reciprocal := div (Coherence.exact 1) origin.certificate.value origin.certificate.apart
  have coefficient := parameterPolynomial_odd_pivot retained ramified table
  have names := congrArg (fun value : Canonical => (reciprocal.mul (Coherence.exact value)).name) coefficient
  exact Eq.mp (congrArg (fun source => Equivalence.NamedEquivalent source (Coherence.exact 0).name) names.symm)
    (Arithmetic.Mul.coherentMul_zero_right reciprocal)

include degreeBound in
/-- The actual unramified table reads the original signed finite infinity functional on the same retained jet.

The original numerator degree bound gives its bounded coefficient vector.
The original table pivot and principal-product coefficient laws identify
the scalar; transport retains the actual origin reciprocal and scale.
This is an operational coefficient-channel identity, before construction
of an intrinsic physical residue channel.
-/
def coefficientChannel_even
    (table : { value : CoefficientPolynomial // value = parameterPolynomial retained })
    (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    Equivalence.NamedEquivalent (coefficientChannel (origin := origin) table).name
      ((div (Coherence.exact 1) origin.certificate.value origin.certificate.apart).mul
        (Coherence.exact (-differential.scale * InfinityCoefficients.evenFunctional curve jet
          (Ascending.Gaussian.Dense.Evaluation.toVector (2 * genus + 1)
            (Ascending.Gaussian.Dense.Evaluation.fromDense differential.numerator.normalize))))).name := by
  have count : differential.numerator.degreeCount ≤ 2 * genus + 1 := by
    have smaller := degreeBound
    change differential.numerator.degreeCount - 1 ≤ 2 * genus at smaller
    omega0
  have coefficient := (parameterPolynomial_even_pivot retained unramified table).trans
    (InfinityCoefficients.Jet.Principal.even_coefficient curve jet differential.numerator differential.scale
      count data.1 retained)
  let reciprocal := div (Coherence.exact 1) origin.certificate.value origin.certificate.apart
  have names := congrArg (fun value : Canonical => (reciprocal.mul (Coherence.exact value)).name) coefficient
  exact Eq.mp (congrArg (fun last => Equivalence.NamedEquivalent
    (coefficientChannel (origin := origin) table).name last) names)
      (Equivalence.NamedEquivalent.refl _)

include expanded

/-- Normalize the total-form and principal outputs through the same actual prepared logarithmic denominator.

The numerator comparison consumes the supplied total-form aggregate and
retained principal programme. The denominator comparison retains the same
prepared integral on both sides. Original finite quotient bounds and
sampler bridges pay the output starts and strict tolerance independently
of the radius payment; no completed integral or algebraic winding value
replaces the actual guarded normalizer.
-/
def compare (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
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

/-- The actual normalized total-form loop approaches its same retained finite coefficient channel.

Both comparison legs pay their own starts. The first consumes the actual
prepared logarithmic denominator and radius-paid total-form loop; the
second uses original guarded cancellation of that same retained integral.
The coefficient channel is identified by this operational estimate rather
than substituted for the actual normalized loop programme.
-/
def compareCoefficient (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
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

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs.Normalization

end
