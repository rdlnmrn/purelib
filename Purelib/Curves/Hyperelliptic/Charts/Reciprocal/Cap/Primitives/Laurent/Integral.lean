module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Laurent
public import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.PrimitiveLoop
public import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.Logarithmic
import Purelib.Polynomial.Ascending.Gaussian.Antiderivative.Taylor
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Tactic.Ring

/-! # Actual four-quarter primitive programmes of the retained cap Laurent polynomial -/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives

open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.RationalFunctions.Curve.Canonical
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : HyperellipticCurve genus} {jet : InfinityCoefficients.Jet curve}
  {polynomial : Dense.Basic.DensePolynomial Canonical} {scale base : Canonical} {nonzero : base ≠ 0}

/-- The actual substituted table, both original primitive caches and both paid quarter banks on one original circuit.

The exact dependent pair retains the original C product and circuit as its
parents. Each original bounded edge bank is tied to its actual construction
from the supplied table, primitive and shared box cache. It introduces no
replacement programme, curve, primitive or integration certificate type.
-/
abbrev ParameterPrimitives (retained : jet.Principal polynomial scale)
    (circuit : Circle.Integral.Circuit base nonzero) :=
  (table : { value : CoefficientPolynomial // value = parameterPolynomial retained }) ×
    (polar : Antiderivative.ReciprocalPrimitive table.val (parameterOrder curve)) ×
      (tail : { value : CoefficientPolynomial //
        value = Arithmetic.divideByPower (parameterOrder curve + 1) table.val }) ×
        (regular : { value : CoefficientPolynomial // value = Antiderivative.antiderivative tail.val }) ×
          (polarBounds : Antiderivative.BoxPreparation polar.1.val polar.2
            (Circle.Integral.reciprocalBox base nonzero)) ×
            (regularBounds : Antiderivative.BoxPreparation tail.val regular (Circle.Integral.circleBox base)) ×
              (_polar : { value : Circle.Integral.PrimitiveEdges circuit.1 polar.value //
                value = circuit.1.reciprocalEdges polar polarBounds }) ×
                { value : Circle.Integral.PrimitiveEdges circuit.1 (Evaluation.eval regular.val) //
                  value = circuit.1.polynomialEdges tail.val regular regularBounds }

namespace ParameterPrimitives

variable {retained : jet.Principal polynomial scale} {circuit : Circle.Integral.Circuit base nonzero}

/-- Substitute once, prepare both finite primitives once and materialize their actual original quarter banks once. -/
@[expose] def build (retained : jet.Principal polynomial scale) (circuit : Circle.Integral.Circuit base nonzero)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial retained } :=
      ⟨parameterPolynomial retained, rfl⟩) : ParameterPrimitives retained circuit :=
  let polar := Antiderivative.reciprocalPrimitive table.val (parameterOrder curve)
  let tail : { value : CoefficientPolynomial //
      value = Arithmetic.divideByPower (parameterOrder curve + 1) table.val } :=
    ⟨Arithmetic.divideByPower (parameterOrder curve + 1) table.val, rfl⟩
  let regular : { value : CoefficientPolynomial // value = Antiderivative.antiderivative tail.val } :=
    ⟨Antiderivative.antiderivative tail.val, rfl⟩
  let polarBounds := Antiderivative.prepareInBox polar.1.val polar.2 (Circle.Integral.reciprocalBox base nonzero)
  let regularBounds := Antiderivative.prepareInBox tail.val regular (Circle.Integral.circleBox base)
  let polarEdges := circuit.1.reciprocalEdges polar polarBounds
  let regularEdges := circuit.1.polynomialEdges tail.val regular regularBounds
  ⟨table, polar, tail, regular, polarBounds, regularBounds, ⟨polarEdges, rfl⟩, ⟨regularEdges, rfl⟩⟩

/-- Building the original primitive banks retains the same supplied complete substituted table. -/
theorem build_table (retained : jet.Principal polynomial scale) (circuit : Circle.Integral.Circuit base nonzero)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial retained }) :
    (build retained circuit table).1 = table := (rfl)

/-- Read the complete actual substituted coefficient table. -/
@[expose] def table (cached : ParameterPrimitives retained circuit) :
    { value : CoefficientPolynomial // value = parameterPolynomial retained } := cached.1

/-- Read the original reciprocal primitive constructed from that same retained table. -/
@[expose] def polar (cached : ParameterPrimitives retained circuit) :
    Antiderivative.ReciprocalPrimitive cached.table.val (parameterOrder curve) := cached.2.1

/-- Read the same retained literal regular tail of the substituted table. -/
@[expose] def tail (cached : ParameterPrimitives retained circuit) :
    { value : CoefficientPolynomial //
      value = Arithmetic.divideByPower (parameterOrder curve + 1) cached.table.val } := cached.2.2.1

/-- Read the original retained antiderivative of that same regular tail. -/
@[expose] def regular (cached : ParameterPrimitives retained circuit) :
    { value : CoefficientPolynomial // value = Antiderivative.antiderivative cached.tail.val } := cached.2.2.2.1

/-- Read the whole original shared reciprocal-box primitive and coefficient preparation. -/
@[expose] def polarBounds (cached : ParameterPrimitives retained circuit) :
    Antiderivative.BoxPreparation cached.polar.1.val cached.polar.2 (Circle.Integral.reciprocalBox base nonzero) :=
  cached.2.2.2.2.1

/-- Read the whole original shared circle-box primitive and coefficient preparation. -/
@[expose] def regularBounds (cached : ParameterPrimitives retained circuit) :
    Antiderivative.BoxPreparation cached.tail.val cached.regular (Circle.Integral.circleBox base) := cached.2.2.2.2.2.1

/-- Read the actual original paid polar edge bank with its complete producer identity. -/
@[expose] def polarEdges (cached : ParameterPrimitives retained circuit) :
    { value : Circle.Integral.PrimitiveEdges circuit.1 cached.polar.value //
      value = circuit.1.reciprocalEdges cached.polar cached.polarBounds } := cached.2.2.2.2.2.2.1

/-- Read the actual original paid regular edge bank with its complete producer identity. -/
@[expose] def regularEdges (cached : ParameterPrimitives retained circuit) :
    { value : Circle.Integral.PrimitiveEdges circuit.1 (Evaluation.eval cached.regular.val) //
      value = circuit.1.polynomialEdges cached.tail.val cached.regular cached.regularBounds } := cached.2.2.2.2.2.2.2

/-- Each stored polar quarter programme retains the original dyadic count at every actual stage. -/
theorem polar_count (cached : ParameterPrimitives retained circuit) (quarter : Fin Circle.Integral.quarters.length)
    (index : Nat) : ((cached.polarEdges.val.get quarter).program.model index).cells.length = 2 ^ index := by
  rewrite [cached.polarEdges.property]
  exact circuit.1.reciprocalEdges_count cached.polar cached.polarBounds quarter index

/-- Each stored regular quarter programme retains the original dyadic count at every actual stage. -/
theorem regular_count (cached : ParameterPrimitives retained circuit) (quarter : Fin Circle.Integral.quarters.length)
    (index : Nat) : ((cached.regularEdges.val.get quarter).program.model index).cells.length = 2 ^ index := by
  rewrite [cached.regularEdges.property]
  exact circuit.1.polynomialEdges_count cached.tail.val cached.regular cached.regularBounds quarter index

/-- Both stored programmes use the same literal parameter split of the original retained principal value. -/
theorem coefficient_split (cached : ParameterPrimitives retained circuit) (parameter : Canonical)
    (pointNonzero : parameter ≠ 0) :
    ((degree curve : Canonical) * Evaluation.eval retained.val (point curve parameter)) *
        (parameter ^ (degree curve * (genus + 1)))⁻¹ =
      cached.polar.derivativeValue parameter +
        Coefficient.coefficient cached.table.val (parameterOrder curve) * parameter⁻¹ +
          Evaluation.eval cached.tail.val parameter := by
  rewrite [cached.tail.property]
  exact parameter_split retained cached.table cached.polar parameter pointNonzero

/-- The actual same-mesh principal sample splits into stored polar and regular programme samples and a dw/w sample.

Every coefficient is evaluated at the same supplied quarter's original
left endpoint. The original dyadic traversal proves scalar linearity;
the actual retained primitive-program model laws supply the polar and
regular samples. The displayed logarithmic dyadic sample is not identified
here with the original circuit's independently approximated log programme.
-/
theorem quarter_sample_split (cached : ParameterPrimitives retained circuit)
    (quarter : Fin Circle.Integral.quarters.length) (index : Nat) :
    let actual := (circuit.1.get quarter).1
    let currentBase := Circle.Integral.quarterBase base
      (Circle.Integral.quarters[quarter.val]'quarter.isLt)
    (Circle.Integral.Dyadic.model currentBase actual
      (fun parameter => ((degree curve : Canonical) * Evaluation.eval retained.val (point curve parameter)) *
        (parameter ^ (degree curve * (genus + 1)))⁻¹)
      index ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩).integralSample =
      ((cached.polarEdges.val.get quarter).program.model index).integralSample +
        Coefficient.coefficient cached.table.val (parameterOrder curve) *
          (Circle.Integral.Dyadic.model currentBase actual (fun parameter => parameter⁻¹)
            index ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩).integralSample +
        ((cached.regularEdges.val.get quarter).program.model index).integralSample := by
  dsimp only
  let actual := (circuit.1.get quarter).1
  let currentBase := Circle.Integral.quarterBase base
    (Circle.Integral.quarters[quarter.val]'quarter.isLt)
  let pivot := Coefficient.coefficient cached.table.val (parameterOrder curve)
  let first := cached.polar.derivativeValue
  let last := Evaluation.eval cached.tail.val
  let principal := fun parameter => ((degree curve : Canonical) *
    Evaluation.eval retained.val (point curve parameter)) * (parameter ^ (degree curve * (genus + 1)))⁻¹
  have scalar := Circle.Integral.Dyadic.model_sample_congr currentBase actual principal
    (fun parameter => (1 : Canonical) * (1 * first parameter + pivot * parameter⁻¹) + 1 * last parameter)
    (fun time => (cached.coefficient_split (actual.val.point time)
      (circuit.1.point_ne_zero quarter time)).trans (by ring1))
    index ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩
  have outer := Circle.Integral.Dyadic.model_sample_linear currentBase actual
    (fun parameter => (1 : Canonical) * first parameter + pivot * parameter⁻¹) last 1 1
    index ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩
  have inner := Circle.Integral.Dyadic.model_sample_linear currentBase actual first
    (fun parameter => parameter⁻¹) 1 pivot index ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩
  have combined := scalar.trans outer
  rewrite [inner] at combined
  have polarModel : (cached.polarEdges.val.get quarter).program.model index =
      Circle.Integral.Dyadic.model currentBase actual first index ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩ := by
    rewrite [cached.polarEdges.property]
    exact circuit.1.reciprocalEdges_model cached.polar cached.polarBounds quarter index
  have regularModel : (cached.regularEdges.val.get quarter).program.model index =
      Circle.Integral.Dyadic.model currentBase actual last index ⟨0, by decide +kernel⟩ ⟨1, by decide +kernel⟩ := by
    rewrite [cached.regularEdges.property]
    exact circuit.1.polynomialEdges_model cached.tail.val cached.regular cached.regularBounds quarter index
  rewrite [polarModel, regularModel]
  exact combined.trans (by ring1)

/-- The actual four-quarter principal sample is the sum of the retained primitive samples and same-mesh dw/w sample.

All four terms read the same supplied original quarter curves at the same
actual dyadic depth. The polar and regular terms are the existing closed
primitive programmes, including their original cached banks and counts.
This finite sample identity does not identify different programme meshes.
-/
theorem model_sample_split (cached : ParameterPrimitives retained circuit) (index : Nat) :
    (circuit.1.dyadicModel (fun parameter =>
      ((degree curve : Canonical) * Evaluation.eval retained.val (point curve parameter)) *
        (parameter ^ (degree curve * (genus + 1)))⁻¹) index).integralSample =
      ((cached.polarEdges.val.concatenate cached.polar_count).model index).integralSample +
        Coefficient.coefficient cached.table.val (parameterOrder curve) *
          (circuit.1.dyadicModel (fun parameter => parameter⁻¹) index).integralSample +
        ((cached.regularEdges.val.concatenate cached.regular_count).model index).integralSample := by
  rewrite [Circle.Integral.Entries.dyadicModel_sample,
    Circle.Integral.PrimitiveEdges.concatenate_model, Circle.Integral.PrimitiveEdges.concatenate_model,
    PathModel.integralSample_concat,
    PathModel.integralSample_concat,
    PathModel.integralSample_concat,
    PathModel.integralSample_concat,
    PathModel.integralSample_concat,
    PathModel.integralSample_concat]
  rewrite [cached.quarter_sample_split ⟨0, by decide +kernel⟩,
    cached.quarter_sample_split ⟨1, by decide +kernel⟩, cached.quarter_sample_split ⟨2, by decide +kernel⟩,
    cached.quarter_sample_split ⟨3, by decide +kernel⟩, Circle.Integral.Entries.dyadicModel_sample]
  ring1

/-- Construct both actual closed primitive programmes and their paid zero comparisons, retaining the actual log guard.

The same supplied eight quarter programmes are concatenated in their
original order. Their existing primitive comparisons derive exact-zero
output comparisons. The logarithmic denominator comes from the original
circuit's actual first observation, not an algebraic winding constant.
-/
@[expose] def integrate (cached : ParameterPrimitives retained circuit) :
    (polarProgram : RefinementProgram) × (regularProgram : RefinementProgram) ×
      (_polarZero : NamedEquivalent polarProgram.output.name (Coherence.exact 0).name) ×
        (_regularZero : NamedEquivalent regularProgram.output.name (Coherence.exact 0).name) ×
          (logarithmic : Integration.CertifiedProgram.Program
            (Circle.Integral.Logarithmic.operations circuit)) ×
            (_logarithmic : NamedEquivalent circuit.channel.name logarithmic.output.name) ×
              Division.Prepared circuit.channel :=
  let polarProgram := cached.polarEdges.val.concatenate cached.polar_count
  let regularProgram := cached.regularEdges.val.concatenate cached.regular_count
  let polarZero := cached.polarEdges.val.concatenate_zero cached.polar_count
  let regularZero := cached.regularEdges.val.concatenate_zero cached.regular_count
  let logarithmic := Circle.Integral.Logarithmic.program circuit
  let normalizer := circuit.prepared
  ⟨polarProgram, regularProgram, polarZero, regularZero, logarithmic.1, logarithmic.2, normalizer⟩

/-- The closed polar programme is the exact concatenation of the supplied actual polar quarter bank. -/
theorem integrate_polar (cached : ParameterPrimitives retained circuit) :
    cached.integrate.1 = cached.polarEdges.val.concatenate cached.polar_count := rfl

/-- The closed regular programme is the exact concatenation of the supplied actual regular quarter bank. -/
theorem integrate_regular (cached : ParameterPrimitives retained circuit) :
    cached.integrate.2.1 = cached.regularEdges.val.concatenate cached.regular_count := rfl

/-- The polar fields retain the complete original programme-and-zero-comparison pair. -/
theorem integrate_polar_pair (cached : ParameterPrimitives retained circuit) :
    (⟨cached.integrate.1, cached.integrate.2.2.1⟩ :
      (program : RefinementProgram) × NamedEquivalent program.output.name (Coherence.exact 0).name) =
      ⟨cached.polarEdges.val.concatenate cached.polar_count,
        cached.polarEdges.val.concatenate_zero cached.polar_count⟩ := rfl

/-- The regular fields retain the complete original programme-and-zero-comparison pair. -/
theorem integrate_regular_pair (cached : ParameterPrimitives retained circuit) :
    (⟨cached.integrate.2.1, cached.integrate.2.2.2.1⟩ :
      (program : RefinementProgram) × NamedEquivalent program.output.name (Coherence.exact 0).name) =
      ⟨cached.regularEdges.val.concatenate cached.regular_count,
        cached.regularEdges.val.concatenate_zero cached.regular_count⟩ := rfl

/-- The retained logarithmic programme is the actual adaptive-dyadic construction on the same supplied circuit. -/
theorem integrate_logarithmic (cached : ParameterPrimitives retained circuit) :
    cached.integrate.2.2.2.2.1 = (Circle.Integral.Logarithmic.program circuit).1 := rfl

/-- The normalization guard is the original prepared denominator of that same retained logarithmic circuit. -/
theorem integrate_normalizer (cached : ParameterPrimitives retained circuit) :
    cached.integrate.2.2.2.2.2.2 = circuit.prepared := rfl

/-- The two logarithmic fields retain the complete literal original programme-and-comparison pair. -/
theorem integrate_logarithmic_pair (cached : ParameterPrimitives retained circuit) :
    (⟨cached.integrate.2.2.2.2.1, cached.integrate.2.2.2.2.2.1⟩ :
      (program : Integration.CertifiedProgram.Program (Circle.Integral.Logarithmic.operations circuit)) ×
        NamedEquivalent circuit.channel.name program.output.name) = Circle.Integral.Logarithmic.program circuit := rfl

end ParameterPrimitives

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives

end
