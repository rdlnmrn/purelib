module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Normalization.Radius
public import Purelib.Approximation.Gaussian.Geometric.Comparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Bounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Principal
import Purelib.RationalFunctions.Curve.Canonical.Circle.Integral.Logarithmic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Division.Prepared.Quotient
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Polynomial.Ascending.Gaussian.Antiderivative
import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Bounds

/-! # Actual normalized cap programmes on their retained shrinking circuits -/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs.Normalization

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {differential : OddPowerDifferential curve.polynomial} {data : Polynomials differential}
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}

namespace Sources

/-- The exact factory equation for one original quotient and its actual supplied logarithmic preparation. -/
def QuotientEquation {numerator denominator : Name.Coherent.CoherentNamed}
    (prepared : Division.Prepared denominator) (value : Division.Prepared.Quotient numerator denominator) : Prop :=
  value = Division.Prepared.Quotient.quotient numerator prepared

namespace QuotientEquation

/-- Read the original whole-quotient factory equation from its compact proposition. -/
theorem eq {numerator denominator : Name.Coherent.CoherentNamed}
    {prepared : Division.Prepared denominator} {value : Division.Prepared.Quotient numerator denominator}
    (same : QuotientEquation prepared value) : value = Division.Prepared.Quotient.quotient numerator prepared := same

/-- The original quotient constructor supplies its own complete factory equation. -/
theorem built {numerator denominator : Name.Coherent.CoherentNamed}
    (prepared : Division.Prepared denominator) :
    QuotientEquation prepared (Division.Prepared.Quotient.quotient numerator prepared) := (rfl)

end QuotientEquation

end Sources

attribute [local irreducible] Sources.QuotientEquation

namespace Sources

variable {base : Canonical} {nonzero : base ≠ 0}
    {unitBound : Norm.Basic.normSq base ≤ 1}
    {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
    (circuit : Integral.Circuit base nonzero)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish)

/-- The original whole quotient with the exact factory equation on its same circuit. -/
abbrev Quotient (source : Name.Coherent.CoherentNamed) :=
  { value : Division.Prepared.Quotient source circuit.channel // QuotientEquation circuit.prepared value }

/-- One original complete programme result and its same original normalized quotient. -/
abbrev Result (cached : data.Bounds base)
    (stored : Built (unitBound := unitBound) (collarBound := collarBound)
      circuit.1 cached pairs degreeBound bounds edges) :=
  (source : { value : stored.val.Result // value = stored.val.concatenate }) × Quotient circuit source.val.1.output

/-- The actual four programmes and their complete original result on the same form cache. -/
abbrev Stages (cached : data.Bounds base) :=
  (stored : Built (unitBound := unitBound) (collarBound := collarBound)
    circuit.1 cached pairs degreeBound bounds edges) × Result circuit pairs degreeBound bounds edges cached stored

/-- Both original form bounds and their dependent original programme caches on one retained circuit. -/
abbrev Bounds :=
  (cached : data.Bounds base) × Stages (unitBound := unitBound) (collarBound := collarBound)
    circuit pairs degreeBound bounds edges cached

end Sources

/-- The actual circuit, form caches, four programmes, complete source and original prepared logarithm.

This is an exact dependent view of the existing owners. Both source and
normalizer retain their original factory equalities on that same supplied
circuit and actual four-quarter form programme; no replacement channel or
integration certificate is introduced.
-/
@[expose] def Sources {base : Canonical} (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish) :=
  (circuit : Integral.Circuit base nonzero) × Sources.Bounds (data := data)
    (unitBound := unitBound) (collarBound := collarBound) circuit pairs degreeBound bounds edges

/-- Construct one actual normalized-loop source from its original four retained quarter curves.

Each coefficient cache and total-form programme is built once. The complete
concatenation and the original logarithmic preparation are retained with
their exact factory equations; output observations remain demanded later.
-/
def sources (base : Canonical) (nonzero : base ≠ 0)
    (unitBound : Norm.Basic.normSq base ≤ 1)
    (collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish) :
    Sources (data := data) nonzero unitBound collarBound pairs degreeBound bounds edges :=
  let circuit := Integral.circuit base nonzero
  let cached := data.bounds base
  let stored : Built (unitBound := unitBound) (collarBound := collarBound)
      circuit.1 cached pairs degreeBound bounds edges :=
    ⟨programs circuit.1 cached pairs degreeBound bounds edges, rfl⟩
  let actual : { value : stored.val.Result // value = stored.val.concatenate } := ⟨stored.val.concatenate, rfl⟩
  let normalized : { value : Division.Prepared.Quotient actual.val.1.output circuit.channel //
      Sources.QuotientEquation circuit.prepared value } :=
    ⟨Division.Prepared.Quotient.quotient actual.val.1.output circuit.prepared,
      Sources.QuotientEquation.built circuit.prepared⟩
  ⟨circuit, cached, stored, actual, normalized⟩

namespace Sources

variable {base : Canonical} {nonzero : base ≠ 0}
    {unitBound : Norm.Basic.normSq base ≤ 1}
    {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
    {pairs : differential.denominatorPairs = 0} {degreeBound : differential.numerator.natDegree ≤ 2 * genus}
    {bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial}
    {edges : DyadicEdges 0 start finish}
    (retained : Sources (data := data) nonzero unitBound collarBound pairs degreeBound bounds edges)

/-- Read the original four-curve logarithmic circuit. -/
abbrev circuit := retained.1

/-- Read both original whole form-coefficient caches on that same actual circle. -/
abbrev cached := retained.2.1

/-- Read the same original four total-form programmes with their whole factory equality. -/
abbrev programs := retained.2.2.1

/-- Read the complete actual concatenated total-form programme with its original factory equality. -/
abbrev source := retained.2.2.2.1

/-- Read the stored original quotient with its same complete factory equality and prepared denominator. -/
abbrev quotient := retained.2.2.2.2

/-- Read the original logarithmic preparation from that identical stored quotient. -/
def normalizer : { value : Division.Prepared retained.circuit.channel // value = retained.circuit.prepared } :=
  ⟨retained.quotient.val.prepared,
    congrArg (fun value : Division.Prepared.Quotient retained.source.val.1.output retained.circuit.channel =>
      value.prepared) retained.quotient.property.eq⟩

/-- Read the actual stored normalized total-form output without rebuilding its quotient. -/
def channel : Name.Coherent.CoherentNamed := retained.quotient.val.output

/-- The normalized source reads the literal stored output of the original quotient. -/
theorem channel_output : retained.channel = retained.quotient.val.output := (rfl)

/-- The stored original quotient retains the actual source output and identical logarithmic preparation. -/
theorem channel_eq : retained.channel = retained.normalizer.val.quotient retained.source.val.1.output :=
  retained.quotient.val.output_eq

end Sources

attribute [local irreducible] Sources sources Sources.channel Sources.normalizer

variable {origin : Owners.Point cap 0} {jet : InfinityCoefficients.Jet curve}
    {remainder : InverseSquareRoot.ResidualFactor (InfinityCoefficients.radicand curve) genus jet.val}
    {principal : jet.Principal data.1.val differential.scale}
    {primitive : Antiderivative.ReciprocalPrimitive principal.val genus}

/-- One intrinsically radius-paid normalized-loop request retains its original sources and actual comparison.

The radius is computed from the supplied original table and numerical setup.
Its same original circuit, form programmes and prepared logarithm remain
explicit parents of the returned comparison; its fixed reference is the
coefficient channel on that identical supplied table.
-/
abbrev Request (origin : Owners.Point cap 0)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial principal })
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish)
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
    (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor)
    (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
    (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target) :=
  let chosen := chooseBase origin table setup.val.1 errorBounds target positive
  (actual : Sources (data := data) chosen.property.1 chosen.property.2.1 chosen.property.2.2.1
    pairs degreeBound bounds edges) ×
    Equivalence.Comparison (Name.Sampling.approximation actual.channel.name)
      (Name.Sampling.approximation (coefficientChannel (origin := origin) table).name)
      leftStart rightStart target

namespace Sources

/-- Compare the actual retained sources on the intrinsically selected radius with the original coefficient channel.

The supplied sources retain their original circuit, programmes, prepared
logarithm and cached quotient. This operation constructs the primitive and
weighted comparisons on those same abstract owners before the factory is
specialized, keeping the dependent interface compact.
-/
def compareCoefficient (origin : Owners.Point cap 0)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial principal })
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish)
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
    (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor)
    (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
    (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (circuit : let chosen := chooseBase origin table setup.val.1 errorBounds target positive
      Integral.Circuit chosen.val chosen.property.1)
    (cachedBounds : data.Bounds (chooseBase origin table setup.val.1 errorBounds target positive).val)
    (stored : Built (unitBound := (chooseBase origin table setup.val.1 errorBounds target positive).property.2.1)
      (collarBound := (chooseBase origin table setup.val.1 errorBounds target positive).property.2.2.1)
      circuit.1 cachedBounds pairs degreeBound bounds edges)
    (supplied : { value : stored.val.Result // value = stored.val.concatenate })
    (quotient : Sources.Quotient circuit supplied.val.1.output) :
    Equivalence.Comparison (Name.Sampling.approximation quotient.val.output.name)
      (Name.Sampling.approximation (coefficientChannel (origin := origin) table).name)
      leftStart rightStart target := by
  let chosen := chooseBase origin table setup.val.1 errorBounds target positive
  let normalizer : { value : Division.Prepared circuit.channel // value = circuit.prepared } :=
    ⟨quotient.val.prepared,
      congrArg (fun value : Division.Prepared.Quotient supplied.val.1.output circuit.channel =>
        value.prepared) quotient.property.eq⟩
  have channelEq : quotient.val.output = normalizer.val.quotient supplied.val.1.output := quotient.val.output_eq
  let prepared : { value : Expansions (origin := origin) (jet := jet) (remainder := remainder)
      (retained := principal) (primitive := primitive) stored.val //
    value = expand circuit.1 cachedBounds pairs degreeBound bounds edges stored
      jetBounds anchor setup } :=
    ⟨expand circuit.1 cachedBounds pairs degreeBound bounds edges stored
      jetBounds anchor setup, rfl⟩
  have near : Norm.Basic.normSq chosen.val ≤ setup.val.1.val ^ 2 := chosen.property.2.2.2.1
  let expanded : { value : Expanded (origin := origin) (jet := jet) (remainder := remainder)
      (retained := principal) (primitive := primitive) stored.val //
    value = realize circuit.1 cachedBounds pairs degreeBound bounds edges stored
      jetBounds anchor setup prepared near } :=
    ⟨realize circuit.1 cachedBounds pairs degreeBound bounds edges stored
      jetBounds anchor setup prepared near, rfl⟩
  let logarithmic : { value :
      (program : CertifiedProgram.Program (Integral.Logarithmic.operations circuit)) ×
        Equivalence.NamedEquivalent circuit.channel.name program.output.name //
      value = Integral.Logarithmic.program circuit } :=
    ⟨Integral.Logarithmic.program circuit, rfl⟩
  let cached := ParameterPrimitives.build principal circuit table
  let polarPair : (program : Program.Gaussian.Basic.RefinementProgram) ×
      Equivalence.NamedEquivalent program.output.name (Coherence.exact 0).name :=
    ⟨cached.polarEdges.val.concatenate cached.polar_count,
      cached.polarEdges.val.concatenate_zero cached.polar_count⟩
  let polar : { value : (program : Program.Gaussian.Basic.RefinementProgram) ×
      Equivalence.NamedEquivalent program.output.name (Coherence.exact 0).name //
    value = polarPair } := ⟨polarPair, rfl⟩
  let regularPair : (program : Program.Gaussian.Basic.RefinementProgram) ×
      Equivalence.NamedEquivalent program.output.name (Coherence.exact 0).name :=
    ⟨cached.regularEdges.val.concatenate cached.regular_count,
      cached.regularEdges.val.concatenate_zero cached.regular_count⟩
  let regular : { value : (program : Program.Gaussian.Basic.RefinementProgram) ×
      Equivalence.NamedEquivalent program.output.name (Coherence.exact 0).name //
    value = regularPair } := ⟨regularPair, rfl⟩
  let principalSource : ParameterPrimitives.Program.View logarithmic cached polar regular :=
    ⟨ParameterPrimitives.Program.build logarithmic cached polar regular, rfl⟩
  let weighted : { value : _ // value = Principal.build logarithmic cached polar regular principalSource
      (origin := origin) cachedBounds jetBounds } :=
    ⟨Principal.build logarithmic cached polar regular principalSource (origin := origin) cachedBounds jetBounds, rfl⟩
  let selected : { value : stored.val.Result //
      value = selectLogarithmic stored.val logarithmic supplied } :=
    ⟨selectLogarithmic stored.val logarithmic supplied, rfl⟩
  have small := chooseBase_paid origin table setup.val.1 errorBounds target positive
    circuit ⟨cached, rfl⟩ normalizer
  let compared := Normalization.compareCoefficient (origin := origin) (retained := principal) (primitive := primitive)
    (remainder := remainder) circuit cachedBounds pairs degreeBound bounds edges stored
    jetBounds anchor setup prepared near expanded supplied logarithmic cached polar regular principalSource
    weighted selected normalizer errorBounds leftStart rightStart target positive small
  have tableEq : cached.table = table := ParameterPrimitives.build_table principal circuit table
  exact compared.withSamples (Name.Sampling.approximation quotient.val.output.name)
    (Name.Sampling.approximation (coefficientChannel (origin := origin) table).name)
    (fun index => congrArg (fun value : Name.Coherent.CoherentNamed =>
      (Name.Sampling.approximation value.name).sample index) channelEq) (fun index => congrArg
      (fun value : { value : CoefficientPolynomial // value = parameterPolynomial principal } =>
        (Name.Sampling.approximation (coefficientChannel (origin := origin) value).name).sample index)
      tableEq.symm)

end Sources

/-- Construct one actual normalized cap-loop request and consume its retained original sources. -/
def request (origin : Owners.Point cap 0)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial principal })
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish)
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
    (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor)
    (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)
    (leftStart rightStart : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    Request origin table pairs degreeBound bounds edges jetBounds anchor setup errorBounds
      leftStart rightStart target positive :=
  let chosen := chooseBase origin table setup.val.1 errorBounds target positive
  let actual := sources (data := data) chosen.val chosen.property.1 chosen.property.2.1 chosen.property.2.2.1
    pairs degreeBound bounds edges
  let compared := Sources.compareCoefficient (primitive := primitive) origin table pairs degreeBound bounds edges
    jetBounds anchor setup errorBounds leftStart rightStart target positive actual.circuit actual.cached
    actual.programs actual.source actual.quotient
  ⟨actual, compared.withSamples (Name.Sampling.approximation actual.channel.name)
    (Name.Sampling.approximation (coefficientChannel (origin := origin) table).name)
    (fun index => congrArg (fun value : Name.Coherent.CoherentNamed =>
      (Name.Sampling.approximation value.name).sample index) actual.channel_output) (fun _ => rfl)⟩

variable (origin : Owners.Point cap 0)
    (table : { value : CoefficientPolynomial // value = parameterPolynomial principal })
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (edges : DyadicEdges 0 start finish)
    (jetBounds : jet.Bounds collar.box) (anchor : Division.Prepared (RootCoordinates.originJetFactor origin jet))
    (setup : RootCoordinates.JetFactors.View origin jet root bounds jetBounds anchor)
    (errorBounds : Readings.Jets.ErrorBounds origin jet remainder data.1)

/-- The actual normalized cap programme and its same retained comparison at one requested geometric stage.

Each stage computes its original radius-paid request once and selects that
same request's source and paid index. The supplied coefficient table,
root setup, primitive and error bounds remain common to all stages.
-/
def stage (index : Nat) :
    (source : Sequence.ApproximationData) × Equivalence.Comparison source
      (Name.Sampling.approximation (coefficientChannel (origin := origin) table).name)
      0 0 (Basic.quarterRadius 1 index) :=
  let actual := request (primitive := primitive) origin table pairs degreeBound bounds edges jetBounds anchor setup
    errorBounds 0 0 (Basic.quarterRadius 1 index) (Basic.quarterRadius_pos (by decide) index)
  ⟨Name.Sampling.approximation actual.1.channel.name, actual.2⟩

/-- A geometric stream samples the actual normalized cap programmes at their own retained paid stages.

The same original coefficient channel supplies the comparison reference.
The existing geometric constructor derives its all-future Cauchy bound
from those actual paid comparisons; no fixed completed contour integral
or substituted algebraic value supplies a source sample.
-/
def geometric : Geometric.GeometricApproximation :=
  Geometric.GeometricApproximation.fromComparisons
    (Name.Sampling.approximation (coefficientChannel (origin := origin) table).name)
    (stage (primitive := primitive) origin table pairs degreeBound bounds edges jetBounds anchor setup errorBounds)

/-- The normalized cap stream retains its operational comparison with the original fixed coefficient channel. -/
def geometric_equivalent : Equivalence.Equivalent
    (geometric (primitive := primitive) origin table pairs degreeBound bounds edges jetBounds anchor setup
      errorBounds).toApproximation
    (Name.Sampling.approximation (coefficientChannel (origin := origin) table).name) :=
  Geometric.GeometricApproximation.fromComparisons_equivalent
    (Name.Sampling.approximation (coefficientChannel (origin := origin) table).name)
    (stage (primitive := primitive) origin table pairs degreeBound bounds edges jetBounds anchor setup errorBounds)

/-- The coherent normalized cap channel is produced by the actual shrinking-loop geometric samples. -/
def channel : Name.Coherent.CoherentNamed :=
  ofApproximation (geometric (primitive := primitive) origin table pairs degreeBound bounds edges
    jetBounds anchor setup errorBounds).toApproximation

/-- The actual normalized cap channel agrees operationally with the same retained finite coefficient.

The existing sampling bridge pays the new channel's requested name floor.
It composes directly with the retained geometric comparison to the fixed
coefficient channel; no additional wrapper of that coefficient is built.
-/
def channel_equivalent : Equivalence.NamedEquivalent
    (channel (primitive := primitive) origin table pairs degreeBound bounds edges jetBounds anchor setup
      errorBounds).name
    (coefficientChannel (origin := origin) table).name :=
  (Equivalence.Equivalent.toNamed_sampling
    (geometric (primitive := primitive) origin table pairs degreeBound bounds edges jetBounds anchor setup
      errorBounds).toApproximation).trans
    (geometric_equivalent (primitive := primitive) origin table pairs degreeBound bounds edges
      jetBounds anchor setup errorBounds)

/-- At a ramified infinity the actual normalized cap channel is operationally zero. -/
def channel_odd (ramified : HyperellipticReciprocal.originOrder curve = 1) :
    Equivalence.NamedEquivalent
      (channel (primitive := primitive) origin table pairs degreeBound bounds edges jetBounds anchor setup
        errorBounds).name
      (Coherence.exact 0).name :=
  (channel_equivalent (primitive := primitive) origin table pairs degreeBound bounds edges jetBounds anchor setup
    errorBounds).trans (coefficientChannel_odd (origin := origin) table ramified)

/-- At an unramified infinity the actual normalized cap channel reads the original signed infinity functional.

The same origin reciprocal, differential scale, bounded numerator vector
and retained jet determine the signed scalar. This is the fixed-model
normalized-loop channel; persistence across independently chosen charts
or cyclic sheets requires its separate original geometric relation.
-/
def channel_even (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    Equivalence.NamedEquivalent
      (channel (primitive := primitive) origin table pairs degreeBound bounds edges jetBounds anchor setup
        errorBounds).name
      ((div (Coherence.exact 1) origin.certificate.value origin.certificate.apart).mul
        (Coherence.exact (-differential.scale * InfinityCoefficients.evenFunctional curve jet
          (Dense.Evaluation.toVector (2 * genus + 1)
            (Dense.Evaluation.fromDense differential.numerator.normalize))))).name :=
  (channel_equivalent (primitive := primitive) origin table pairs degreeBound bounds edges jetBounds anchor setup
    errorBounds).trans (coefficientChannel_even (origin := origin) (degreeBound := degreeBound) table unramified)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Loop.Programs.Normalization

end
