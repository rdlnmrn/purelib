module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Potential
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
public import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.Cells
public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Algebra.Quadratic.Pair.Gaussian.Power
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Dense.Power
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Requested integration of the retained operational cap potential

The actual r/t quotient is compared with P(w) times the same local inverse
model. Its differential cell consumes that inverse model and its retained
cube. Original endpoint reading requests and the finite residual bound pay
both endpoints and the complete integral on the original local segment.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap (Potential)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial half)
open Purelib.Riemann.Normalization.InverseModelPrimitiveBounds (PrimitiveDerivativeBounds)
open Purelib.Riemann.Normalization.InverseModelPrimitiveResidual (PrimitiveResidualBounds)
open Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds (Cell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds UniformRequest)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Polynomial.Dense.Derivative (derivative)
open Purelib.Polynomial.Dense.Basic.DensePolynomial (eval_scale)
open Purelib.Algebra.Quadratic.Pair.Gaussian (ReadingPrecision)
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

variable {genus count : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
    {center : Gaussian}
    {centerOwner : Riemann.Topology.SquareRootContinuationChain.Owner
      ((HyperellipticReciprocal.polynomial curve).eval center)}
    {terminal : TerminalModels.Terminal cap centerOwner count} {differential : Differential genus}
    {comparison : TerminalComparison.Data terminal differential}

section Endpoints

variable {point : Gaussian}
    {pointOwner : Riemann.Topology.SquareRootContinuationChain.Owner
      ((HyperellipticReciprocal.polynomial curve).eval point)}
    {overlap : Overlap cap point pointOwner}

/-- Compare the actual cached numerator denotation with the same original source-root quotient.

This uses the ordinary inverse exponent zero, retaining the complete supplied
denotation. The general odd-power and exact-constant laws derive the quotient
presentation; no source observation or cap potential is acquired here.
-/
private def denotation_quotient (source : ContinuedInverseRoot.ContinuedNeighborhood.Point
      terminal.neighborhood.patch point)
    (original : PrimitiveDenotation source 0 cap.polynomial) :
    NamedEquivalent original.channel.name
      (div (Coherence.exact (cap.polynomial.eval point)) source.certificate.value source.certificate.apart).name := by
  have equation : Approximation.Gaussian.Provenance.Power.PowerIdentity source.certificate.value 2
      (-(-(HyperellipticReciprocal.polynomial curve).eval point)) := by
    rewrite [neg_neg]
    exact original.identity
  have nonzero : -(-(HyperellipticReciprocal.polynomial curve).eval point) ≠ 0 := by
    rewrite [neg_neg]
    exact original.identity.square_coefficient_nonzero source.certificate.apart
  have normalized := Algebra.Quadratic.Pair.Gaussian.reciprocal_odd_power
    (cap.polynomial.eval point) source.certificate.value equation nonzero source.certificate.apart 0
  have readback : original.value =
      ⟨0, cap.polynomial.eval point / ((HyperellipticReciprocal.polynomial curve).eval point ^ 1)⟩ := by
    rewrite [original.value_eq]
    apply Algebra.Quadratic.Pair.ext
    · rewrite [Expression.evaluate_re]
      change (0 : Gaussian) / _ = 0
      exact Algebra.Field.ExplicitField.zero_div _
    · rewrite [Expression.evaluate_im]
      change cap.polynomial.eval point /
        (Polynomial.Dense.Power.power (HyperellipticReciprocal.polynomial curve) 1).eval point = _
      rewrite [Polynomial.Dense.Power.eval_power]
      rfl
  have actual : NamedEquivalent
      (mul (Coherence.exact (cap.polynomial.eval point))
        (Power.namedPower (div (Coherence.exact 1) source.certificate.value source.certificate.apart) 1)).name
      original.channel.name := by
    rewrite [original.channel_eq, readback]
    simpa only [neg_neg] using normalized
  have quotient := (Congruence.coherentMul_respects
    (Coherence.exact (cap.polynomial.eval point)) (Coherence.exact (cap.polynomial.eval point))
    (Power.namedPower (div (Coherence.exact 1) source.certificate.value source.certificate.apart) 1)
    (div (Coherence.exact 1) source.certificate.value source.certificate.apart)
    (NamedEquivalent.refl _) (Power.namedPower_one _)).trans
    (ReciprocalRootNames.constant_mul_quotient (cap.polynomial.eval point) 1
      source.certificate.value source.certificate.apart)
  have unit : cap.polynomial.eval point * 1 = cap.polynomial.eval point := Basic.mul_one _
  rewrite [unit] at quotient
  exact actual.symm.trans quotient

/-- Derive the endpoint channel relation from the retained original Point ownership and actual r/t quotient. -/
def endpointEquivalent (data : EndpointComparison.Data comparison overlap)
    (potential : Potential overlap)
    (original : PrimitiveDenotation data.owner.point 0 cap.polynomial) :
    NamedEquivalent original.channel.name potential.val.output.name :=
  (denotation_quotient data.owner.point original).trans
    ((Approximation.Gaussian.Name.Coherent.Division.Equivalence.coherentDiv_respects
      (Coherence.exact (cap.polynomial.eval point)) (Coherence.exact (cap.polynomial.eval point))
      data.owner.point.certificate.value overlap.reciprocal.value
      data.owner.point.certificate.apart overlap.reciprocal.apart
      (NamedEquivalent.refl _) data.owner.equivalent.symm).trans potential.reciprocal.symm)

/-- The actual source request, coefficient cache, root precision and requested original potential reading.

All four original owners are retained before choosing a common polynomial
stage. The potential request refines the existing r/t channel, and the source
request uses the Point already stored in the endpoint comparison data.
-/
@[expose] def EndpointRequest (data : EndpointComparison.Data comparison overlap)
    (potential : Potential overlap) (target : Coordinate) (floor : Nat) : Type _ :=
  (_source : PrimitiveRequest data.owner.point 0 cap.polynomial floor (target / 4)) ×
  (original : PrimitiveDenotation data.owner.point 0 cap.polynomial) ×
  (_precision : ReadingPrecision (Norm.Basic.normSq original.value.im) (target / 16)) ×
  Observation.Request potential.val.output (target / 256)

namespace EndpointRequest

/-- Retain the four actual endpoint request factories without acquiring another Point or quotient. -/
def build (data : EndpointComparison.Data comparison overlap) (potential : Potential overlap)
    (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    EndpointRequest data potential target floor :=
  let localBounds := data.owner.point.primitiveBounds
  let source := localBounds.request 0 cap.polynomial floor (target / 4)
    (Field.div_pos_direct positive (by decide +kernel))
  let original := retainPrimitiveDenotation data.owner.point localBounds 0 cap.polynomial
    ⟨source.factor, source.factor_eq⟩
  let precision := ReadingPrecision.build (Norm.Basic.normSq original.value.im) (target / 16)
    (Norm.Basic.normSq_nonneg _) (Field.div_pos_direct positive (by decide +kernel))
  let bank := Observation.Request.build potential.val.output (target / 256)
    (Field.div_pos_direct positive (by decide +kernel))
  ⟨source, original, precision, bank⟩

/-- The endpoint request preserves the complete original factories, including their floors and witnesses. -/
private theorem packaged_build_factory (data : EndpointComparison.Data comparison overlap)
    (potential : Potential overlap) (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    build data potential target positive floor =
      (let localBounds := data.owner.point.primitiveBounds
       let source := localBounds.request 0 cap.polynomial floor (target / 4)
         (Field.div_pos_direct positive (by decide +kernel))
       let original := retainPrimitiveDenotation data.owner.point localBounds 0 cap.polynomial
         ⟨source.factor, source.factor_eq⟩
       let precision := ReadingPrecision.build (Norm.Basic.normSq original.value.im) (target / 16)
         (Norm.Basic.normSq_nonneg _) (Field.div_pos_direct positive (by decide +kernel))
       let bank := Observation.Request.build potential.val.output (target / 256)
         (Field.div_pos_direct positive (by decide +kernel))
       ⟨source, original, precision, bank⟩ : EndpointRequest data potential target floor) := by rfl

/-- The endpoint request preserves the complete original factories, including their floors and witnesses. -/
theorem build_factory (data : EndpointComparison.Data comparison overlap)
    (potential : Potential overlap) (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    build data potential target positive floor =
      (let localBounds := data.owner.point.primitiveBounds
       let source := localBounds.request 0 cap.polynomial floor (target / 4)
         (Field.div_pos_direct positive (by decide +kernel))
       let original := retainPrimitiveDenotation data.owner.point localBounds 0 cap.polynomial
         ⟨source.factor, source.factor_eq⟩
       let precision := ReadingPrecision.build (Norm.Basic.normSq original.value.im) (target / 16)
         (Norm.Basic.normSq_nonneg _) (Field.div_pos_direct positive (by decide +kernel))
       let bank := Observation.Request.build potential.val.output (target / 256)
         (Field.div_pos_direct positive (by decide +kernel))
       ⟨source, original, precision, bank⟩ : EndpointRequest data potential target floor) :=
  packaged_build_factory data potential target positive floor

end EndpointRequest

end Endpoints

/-- The original numerator derivative and uniform source caches needed for this cap potential.

The original reciprocal differential residual and root derivative cache are
reused from the terminal comparison. Only the new numerator product bound,
its exact mismatch budget and the uniform odd-reading bounds are built.
-/
@[expose] def Preparation (comparison : TerminalComparison.Data terminal differential) : Type _ :=
  (primitive : PrimitiveDerivativeBounds comparison.rootBounds cap.polynomial) ×
  (_residual : PrimitiveResidualBounds comparison.rootBounds terminal.preparation.reciprocal primitive 0) ×
  UniformBounds terminal.neighborhood.patch

namespace Preparation

/-- Build the new potential bounds while retaining both existing terminal residual and root derivative owners. -/
def build (comparison : TerminalComparison.Data terminal differential) : Preparation comparison :=
  let primitive := PrimitiveDerivativeBounds.build comparison.rootBounds cap.polynomial
  let residual := PrimitiveResidualBounds.build comparison.rootBounds terminal.preparation.reciprocal primitive 0
  let uniform := UniformBounds.build terminal.neighborhood.patch
  ⟨primitive, residual, uniform⟩

/-- The preparation retains its complete three original factory values on the unchanged terminal source. -/
private theorem packaged_build_factory (comparison : TerminalComparison.Data terminal differential) :
    build comparison =
      (let primitive := PrimitiveDerivativeBounds.build comparison.rootBounds cap.polynomial
       let residual := PrimitiveResidualBounds.build comparison.rootBounds terminal.preparation.reciprocal primitive 0
       let uniform := UniformBounds.build terminal.neighborhood.patch
       ⟨primitive, residual, uniform⟩ : Preparation comparison) := by rfl

/-- The preparation retains its complete three original factory values on the unchanged terminal source. -/
theorem build_factory (comparison : TerminalComparison.Data terminal differential) :
    build comparison =
      (let primitive := PrimitiveDerivativeBounds.build comparison.rootBounds cap.polynomial
       let residual := PrimitiveResidualBounds.build comparison.rootBounds terminal.preparation.reciprocal primitive 0
       let uniform := UniformBounds.build terminal.neighborhood.patch
       ⟨primitive, residual, uniform⟩ : Preparation comparison) :=
  packaged_build_factory comparison

/-- The actual density numerator is the finite cleared derivative of the original P/v potential. -/
theorem density_numerator (preparation : Preparation comparison) (point : Gaussian) :
    (preparation.2.1.coefficient.scale half).eval point =
      (HyperellipticReciprocal.polynomial curve).eval point *
        (derivative cap.polynomial).eval point -
      half * cap.polynomial.eval point *
        (derivative (HyperellipticReciprocal.polynomial curve)).eval point := by
  rewrite [eval_scale, preparation.2.1.coefficient_eq,
    preparation.2.1.factor_eq]
  have twiceHalf : (2 : Gaussian) * half = 1 := by decide +kernel
  calc
    _ = (2 * half) * (HyperellipticReciprocal.polynomial curve).eval point *
        (derivative cap.polynomial).eval point -
      half * cap.polynomial.eval point *
        (derivative (HyperellipticReciprocal.polynomial curve)).eval point := by ring1
    _ = _ := by rewrite [twiceHalf, Basic.one_mul]; rfl

end Preparation

section Endpoints

variable {point : Gaussian}
    {pointOwner : Riemann.Topology.SquareRootContinuationChain.Owner
      ((HyperellipticReciprocal.polynomial curve).eval point)}
    {overlap : Overlap cap point pointOwner}
    {preparation : Preparation comparison} {start finish : Gaussian}
    {coordinate : Spatial.Coordinate start finish} {stage floor : Nat} {allowance target : Coordinate}
    {nonnegative : 0 ≤ allowance} {endpointData : EndpointComparison.Data comparison overlap}
    {potential : Potential overlap}

/-- The complete endpoint reading, shared-model view, source evaluation and internally paid original comparison. -/
@[expose] def EndpointSample (paid : EndpointRequest endpointData potential target floor)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) : Type _ :=
  (root : PrimitiveRoot endpointData.owner.point stage paid.2.2.1.target) ×
  (reading : { value : PrimitiveReading endpointData.owner.point stage retained.inverse retained.powers //
    value = root.readModel retained.inverse retained.inverse_eq retained.powers }) ×
  (value : { value : PrimitiveValue reading.val 0 cap.polynomial paid.2.1 retained.value //
    value = retainPrimitiveValue reading.val 0 cap.polynomial paid.2.1 retained.value
      (by
        have original := retained.value_eval point
        rewrite [← retained.inverse_eq] at original
        exact original) ⟨paid.1.factor, paid.1.factor_eq⟩ }) ×
  PrimitiveValue.Comparison value.val paid.2.2.2

namespace EndpointSample

/-- Read the original requested root once and compare the retained potential polynomial to the actual r/t reading. -/
def build (paid : EndpointRequest endpointData potential target floor)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative)
    (later : paid.1.stage ≤ stage) (positive : 0 < target) : EndpointSample paid retained := by
  let root := selectPrimitiveRoot endpointData.owner.point stage paid.2.2.1.target paid.2.2.1.target_positive
  let reading := root.readModel retained.inverse retained.inverse_eq retained.powers
  have compiled : retained.value.eval point = cap.polynomial.eval point *
      (primitivePolynomial retained.powers 0).eval point := by
    have original := retained.value_eval point
    rewrite [← retained.inverse_eq] at original
    exact original
  let value := retainPrimitiveValue reading 0 cap.polynomial paid.2.1 retained.value compiled
    ⟨paid.1.factor, paid.1.factor_eq⟩
  let compared := value.compare paid.2.2.2 paid.2.2.1 root rfl (Data.Rat.Fraction.Order.Basic.le_refl _) paid.1
    endpointData.inside later (endpointEquivalent endpointData potential paid.2.1) positive
  exact ⟨root, ⟨reading, rfl⟩, ⟨value, rfl⟩, compared⟩

/-- The complete endpoint result retains the one shared-root reading and its actual original comparison. -/
private theorem packaged_build_factory (paid : EndpointRequest endpointData potential target floor)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative)
    (later : paid.1.stage ≤ stage) (positive : 0 < target) :
    build paid retained later positive =
      (by
        let root := selectPrimitiveRoot endpointData.owner.point stage paid.2.2.1.target paid.2.2.1.target_positive
        let reading := root.readModel retained.inverse retained.inverse_eq retained.powers
        have compiled : retained.value.eval point = cap.polynomial.eval point *
            (primitivePolynomial retained.powers 0).eval point := by
          have original := retained.value_eval point
          rewrite [← retained.inverse_eq] at original
          exact original
        let value := retainPrimitiveValue reading 0 cap.polynomial paid.2.1 retained.value compiled
          ⟨paid.1.factor, paid.1.factor_eq⟩
        let compared := value.compare paid.2.2.2 paid.2.2.1 root rfl
          (Data.Rat.Fraction.Order.Basic.le_refl _) paid.1
          endpointData.inside later (endpointEquivalent endpointData potential paid.2.1) positive
        exact ⟨root, ⟨reading, rfl⟩, ⟨value, rfl⟩, compared⟩ : EndpointSample paid retained) := by rfl

/-- The complete endpoint result retains the one shared-root reading and its actual original comparison. -/
theorem build_factory (paid : EndpointRequest endpointData potential target floor)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative)
    (later : paid.1.stage ≤ stage) (positive : 0 < target) :
    build paid retained later positive =
      (by
        let root := selectPrimitiveRoot endpointData.owner.point stage paid.2.2.1.target paid.2.2.1.target_positive
        let reading := root.readModel retained.inverse retained.inverse_eq retained.powers
        have compiled : retained.value.eval point = cap.polynomial.eval point *
            (primitivePolynomial retained.powers 0).eval point := by
          have original := retained.value_eval point
          rewrite [← retained.inverse_eq] at original
          exact original
        let value := retainPrimitiveValue reading 0 cap.polynomial paid.2.1 retained.value compiled
          ⟨paid.1.factor, paid.1.factor_eq⟩
        let compared := value.compare paid.2.2.2 paid.2.2.1 root rfl
          (Data.Rat.Fraction.Order.Basic.le_refl _) paid.1
          endpointData.inside later (endpointEquivalent endpointData potential paid.2.1) positive
        exact ⟨root, ⟨reading, rfl⟩, ⟨value, rfl⟩, compared⟩ : EndpointSample paid retained) :=
  packaged_build_factory paid retained later positive

/-- The stored comparison pays the actual retained polynomial and original r/t bank reading. -/
theorem error_le (paid : EndpointRequest endpointData potential target floor)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative)
    (sample : EndpointSample paid retained) :
    Norm.Basic.normSq (retained.value.eval point - paid.2.2.2.reading.value) ≤ target := by
  have estimate := sample.2.2.2.residual_le
  rewrite [sample.2.2.2.source_residual] at estimate
  exact estimate

end EndpointSample

end Endpoints

section Segments

variable {preparation : Preparation comparison} {target : Coordinate} {floor : Nat}
    {positive : 0 < target} {segment : TerminalComparison.LocalSegment comparison}
    {data : PrimitiveComparison.Data segment}
    {firstPotential : Potential data.first.coordinates} {lastPotential : Potential data.last.coordinates}
    {coordinate : Spatial.Coordinate segment.comparison.first segment.comparison.last}

/-- Both actual endpoint requests, the residual integral selection and the original uniform cubic request.

The common finite stage is computed from these same four paid floors. The
local cell allowance is the supplied positive target; endpoint and interior
budgets are conservative fractions of that original target.
-/
@[expose] def Request (preparation : Preparation comparison) (data : PrimitiveComparison.Data segment)
    (firstPotential : Potential data.first.coordinates) (lastPotential : Potential data.last.coordinates)
    (coordinate : Spatial.Coordinate segment.comparison.first segment.comparison.last)
    (target : Coordinate) (_positive : 0 < target) (floor : Nat) : Type _ :=
  (first : EndpointRequest data.first.data firstPotential (target / 32) floor) ×
  (last : EndpointRequest data.last.data lastPotential (target / 32) floor) ×
  (interior : Selection
    (2 * Norm.Basic.normSq coordinate.displacement * preparation.2.1.scale) floor (target / 8)) ×
  (uniform : UniformRequest preparation.2.2 1 (preparation.2.1.coefficient.scale half) floor (target / 4)) ×
  { stage : Nat // stage = max (max first.1.stage last.1.stage)
      (max interior.stage uniform.selection.stage) }

namespace Request

/-- Pay both original r/t endpoints and the full residual integral before constructing the one shared model. -/
def build (preparation : Preparation comparison) (data : PrimitiveComparison.Data segment)
    (firstPotential : Potential data.first.coordinates) (lastPotential : Potential data.last.coordinates)
    (coordinate : Spatial.Coordinate segment.comparison.first segment.comparison.last)
    (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    Request preparation data firstPotential lastPotential coordinate target positive floor :=
  let endpointPositive : 0 < target / 32 := Field.div_pos_direct positive (by decide +kernel)
  let first := EndpointRequest.build data.first.data firstPotential (target / 32) endpointPositive floor
  let last := EndpointRequest.build data.last.data lastPotential (target / 32) endpointPositive floor
  let interior := Cell.choose preparation.2.1 coordinate floor (target / 8)
    (Field.div_pos_direct positive (by decide +kernel))
  let uniform := preparation.2.2.request 1 (preparation.2.1.coefficient.scale half) floor (target / 4)
    (Field.div_pos_direct positive (by decide +kernel))
  let stage := max (max first.1.stage last.1.stage) (max interior.stage uniform.selection.stage)
  ⟨first, last, interior, uniform, ⟨stage, rfl⟩⟩

/-- The request stores the four actual selected cache values and their literal common maximum. -/
private theorem packaged_build_factory (preparation : Preparation comparison) (data : PrimitiveComparison.Data segment)
    (firstPotential : Potential data.first.coordinates) (lastPotential : Potential data.last.coordinates)
    (coordinate : Spatial.Coordinate segment.comparison.first segment.comparison.last)
    (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    build preparation data firstPotential lastPotential coordinate target positive floor =
      (let endpointPositive : 0 < target / 32 := Field.div_pos_direct positive (by decide +kernel)
       let first := EndpointRequest.build data.first.data firstPotential (target / 32) endpointPositive floor
       let last := EndpointRequest.build data.last.data lastPotential (target / 32) endpointPositive floor
       let interior := Cell.choose preparation.2.1 coordinate floor (target / 8)
         (Field.div_pos_direct positive (by decide +kernel))
       let uniform := preparation.2.2.request 1 (preparation.2.1.coefficient.scale half) floor (target / 4)
         (Field.div_pos_direct positive (by decide +kernel))
       let stage := max (max first.1.stage last.1.stage) (max interior.stage uniform.selection.stage)
       ⟨first, last, interior, uniform, ⟨stage, rfl⟩⟩ :
        Request preparation data firstPotential lastPotential coordinate target positive floor) := by rfl

/-- The request stores the four actual selected cache values and their literal common maximum. -/
theorem build_factory (preparation : Preparation comparison) (data : PrimitiveComparison.Data segment)
    (firstPotential : Potential data.first.coordinates) (lastPotential : Potential data.last.coordinates)
    (coordinate : Spatial.Coordinate segment.comparison.first segment.comparison.last)
    (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    build preparation data firstPotential lastPotential coordinate target positive floor =
      (let endpointPositive : 0 < target / 32 := Field.div_pos_direct positive (by decide +kernel)
       let first := EndpointRequest.build data.first.data firstPotential (target / 32) endpointPositive floor
       let last := EndpointRequest.build data.last.data lastPotential (target / 32) endpointPositive floor
       let interior := Cell.choose preparation.2.1 coordinate floor (target / 8)
         (Field.div_pos_direct positive (by decide +kernel))
       let uniform := preparation.2.2.request 1 (preparation.2.1.coefficient.scale half) floor (target / 4)
         (Field.div_pos_direct positive (by decide +kernel))
       let stage := max (max first.1.stage last.1.stage) (max interior.stage uniform.selection.stage)
       ⟨first, last, interior, uniform, ⟨stage, rfl⟩⟩ :
        Request preparation data firstPotential lastPotential coordinate target positive floor) :=
  packaged_build_factory preparation data firstPotential lastPotential coordinate target positive floor

/-- The common stage retains the actual first endpoint's selected source floor. -/
theorem first_le (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    paid.1.1.stage ≤ paid.2.2.2.2.val := by
  rewrite [paid.2.2.2.2.property]
  exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)

/-- The selected shared model stage preserves the original requested floor. -/
theorem floor_le (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    floor ≤ paid.2.2.2.2.val := paid.1.1.stage_ge.trans paid.first_le

/-- The common stage retains the actual last endpoint's selected source floor. -/
theorem last_le (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    paid.2.1.1.stage ≤ paid.2.2.2.2.val := by
  rewrite [paid.2.2.2.2.property]
  exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)

/-- The common stage retains the actual residual integral selection. -/
theorem interior_le (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    paid.2.2.1.stage ≤ paid.2.2.2.2.val := by
  rewrite [paid.2.2.2.2.property]
  exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)

/-- The common stage retains the actual uniform cubic request. -/
theorem uniform_le (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    paid.2.2.2.1.selection.stage ≤ paid.2.2.2.2.val := by
  rewrite [paid.2.2.2.2.property]
  exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)

/-- Read the complete first endpoint observation request retained in the same paid cell request. -/
def firstObservation (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    Observation.Request firstPotential.val.output ((target / 32) / 256) :=
  paid.1.2.2.2

/-- The first observation is the original complete endpoint request, without numerical preparation. -/
theorem firstObservation_eq
    (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    firstObservation paid = paid.1.2.2.2 := by rfl

/-- Read the complete last endpoint observation request retained in the same paid cell request. -/
def lastObservation (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    Observation.Request lastPotential.val.output ((target / 32) / 256) :=
  paid.2.1.2.2.2

/-- The last observation is the original complete endpoint request, without numerical preparation. -/
theorem lastObservation_eq
    (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    lastObservation paid = paid.2.1.2.2.2 := by rfl

end Request

/-- One shared original model cell and both internally compared operational endpoint readings. -/
@[expose] def Sample
    (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) : Type _ :=
  (retained : Cell preparation.2.1 coordinate paid.2.2.2.2.val target positive.le) ×
  EndpointSample paid.1 retained × EndpointSample paid.2.1 retained

namespace Sample

/-- Execute the inverse refinement and power factory once, then read both endpoints from that same retained cell. -/
def build (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    Sample paid :=
  let retained := Cell.build preparation.2.1 coordinate paid.2.2.2.2.val target positive.le
  let first := EndpointSample.build paid.1 retained paid.first_le
    (Field.div_pos_direct positive (by decide +kernel))
  let last := EndpointSample.build paid.2.1 retained paid.last_le
    (Field.div_pos_direct positive (by decide +kernel))
  ⟨retained, first, last⟩

/-- The complete result retains one original model cell and its two actual endpoint comparisons. -/
private theorem packaged_build_factory
    (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    build paid =
      (let retained := Cell.build preparation.2.1 coordinate paid.2.2.2.2.val target positive.le
       let first := EndpointSample.build paid.1 retained paid.first_le
         (Field.div_pos_direct positive (by decide +kernel))
       let last := EndpointSample.build paid.2.1 retained paid.last_le
         (Field.div_pos_direct positive (by decide +kernel))
       ⟨retained, first, last⟩ : Sample paid) := by rfl

/-- The complete result retains one original model cell and its two actual endpoint comparisons. -/
theorem build_factory
    (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    build paid =
      (let retained := Cell.build preparation.2.1 coordinate paid.2.2.2.2.val target positive.le
       let first := EndpointSample.build paid.1 retained paid.first_le
         (Field.div_pos_direct positive (by decide +kernel))
       let last := EndpointSample.build paid.2.1 retained paid.last_le
         (Field.div_pos_direct positive (by decide +kernel))
       ⟨retained, first, last⟩ : Sample paid) := packaged_build_factory paid

/-- The actual retained potential readings give an oriented numerical increment. -/
def increment (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    Gaussian :=
  paid.2.1.2.2.2.reading.value - paid.1.2.2.2.reading.value

/-- The oriented increment reads precisely the two original retained potential witnesses. -/
private theorem packaged_increment_eq
    (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    increment paid = paid.2.1.2.2.2.reading.value - paid.1.2.2.2.reading.value := by rfl

/-- The oriented increment reads precisely the two original retained potential witnesses. -/
theorem increment_eq
    (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    increment paid = paid.2.1.2.2.2.reading.value - paid.1.2.2.2.reading.value :=
  packaged_increment_eq paid

/-- The same oriented increment reads the two retained whole observation requests. -/
theorem increment_observations
    (paid : Request preparation data firstPotential lastPotential coordinate target positive floor) :
    increment paid = paid.lastObservation.reading.value - paid.firstObservation.reading.value := by rfl

/-- The internally paid endpoints and residual give the requested physical integral comparison.

The integral is the actual stored cubic-density cell. Both endpoint readings
belong to the original retained r/t channels, with no exact finite root or
polynomial identity imposed on their independently selected witnesses.
-/
theorem accurate (paid : Request preparation data firstPotential lastPotential coordinate target positive floor)
    (sample : Sample paid) :
    Norm.Basic.normSq (increment paid - sample.1.pullback.model.integralSample) < target := by
  have first := EndpointSample.error_le paid.1 sample.1 sample.2.1
  have last := EndpointSample.error_le paid.2.1 sample.1 sample.2.2
  have interior := sample.1.accurate paid.2.2.1 paid.interior_le
    (terminal.neighborhood.patch.box_refines.contains segment.firstInside)
    (terminal.neighborhood.patch.box_refines.contains segment.lastInside)
  let firstValue := paid.1.2.2.2.reading.value
  let lastValue := paid.2.1.2.2.2.reading.value
  let firstModel := sample.1.value.eval segment.comparison.first
  let lastModel := sample.1.value.eval segment.comparison.last
  let integral := sample.1.pullback.model.integralSample
  have endpoints : Norm.Basic.normSq ((lastValue - firstValue) - (lastModel - firstModel)) ≤ target / 8 := by
    have difference : (lastValue - firstValue) - (lastModel - firstModel) =
        (firstModel - firstValue) - (lastModel - lastValue) := by ring1
    rewrite [difference]
    exact (Norm.Bounds.normSq_sub_le_two _ _).trans
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct first last) (by decide +kernel)).trans_eq (by
          rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
          have scalar : 4 * (32 : Coordinate)⁻¹ = (8 : Coordinate)⁻¹ := by decide +kernel
          calc
            _ = target * (4 * (32 : Coordinate)⁻¹) := by ring1
            _ = _ := by rewrite [scalar]; rfl))
  have split : (lastValue - firstValue) - integral =
      ((lastValue - firstValue) - (lastModel - firstModel)) + ((lastModel - firstModel) - integral) := by ring1
  have total : Norm.Basic.normSq ((lastValue - firstValue) - integral) ≤ target / 2 := by
    rewrite [split]
    exact (Norm.Bounds.normSq_add_le_two _ _).trans
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct endpoints interior.le) (by decide +kernel)).trans_eq (by
          rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
          have scalar : 4 * (8 : Coordinate)⁻¹ = (2 : Coordinate)⁻¹ := by decide +kernel
          calc
            _ = target * (4 * (8 : Coordinate)⁻¹) := by ring1
            _ = _ := by rewrite [scalar]; rfl))
  have halfLess := Arithmetic.mul_lt_mul_of_pos_right_direct
    (by decide +kernel : (1 / 2 : Coordinate) < 1) positive
  have half : target / 2 < target := by
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.mul_comm target]
    exact halfLess.trans_eq (Fraction.Field.one_mul target)
  change Norm.Basic.normSq ((lastValue - firstValue) - integral) < target
  exact total.trans_lt half

/-- Read the complete original integration model from the same retained finite cell. -/
def model (paid : Request preparation data firstPotential lastPotential coordinate target positive floor)
    (sample : Sample paid) : CellModel :=
  sample.1.pullback.model

/-- The model reader returns the exact original pullback model without any new cell construction. -/
theorem model_eq (paid : Request preparation data firstPotential lastPotential coordinate target positive floor)
    (sample : Sample paid) : model paid sample = sample.1.pullback.model := by rfl

/-- The requested physical comparison also reads through the retained whole-model projection. -/
theorem accurate_model (paid : Request preparation data firstPotential lastPotential coordinate target positive floor)
    (sample : Sample paid) :
    Norm.Basic.normSq (increment paid - (model paid sample).integralSample) < target :=
  (congrArg (fun cell : CellModel => Norm.Basic.normSq (increment paid - cell.integralSample))
    (model_eq paid sample)).trans_lt (accurate paid sample)

/-- The stored density has actual same-sheet observations on the original supplied lifted segment.

The Point family is physical source data on the original continued box. Its
members are used directly, while only their newly requested root readings
are refined. This certificate does not acquire an alternative Point bank.
-/
def certificate (paid : Request preparation data firstPotential lastPotential coordinate target positive floor)
    (sample : Sample paid) {firstSheet lastSheet : Fin 2}
    (lifted : LiftedCell ⟨segment.comparison.first, firstSheet⟩ ⟨segment.comparison.last, lastSheet⟩)
    (points : ∀ input : Coordinate, 0 ≤ input → input ≤ 1 →
      ContinuedInverseRoot.ContinuedNeighborhood.Point terminal.neighborhood.patch (coordinate.point input)) :
    Jets.UniformCellCertificate (HyperellipticReciprocalCurve.reciprocalCurve curve)
      preparation.2.1.differential lifted sample.1.pullback.model := by
  have later : paid.2.2.2.1.selection.stage ≤ paid.2.2.2.2.val :=
    Request.uniform_le (preparation := preparation) (data := data)
      (coordinate := coordinate) (positive := positive) paid
  exact Cell.certificate (curve := HyperellipticReciprocalCurve.reciprocalCurve curve)
    (patch := terminal.neighborhood.patch) (root := comparison.rootBounds)
    (residual := terminal.preparation.reciprocal) (primitive := preparation.1)
    (bounds := preparation.2.1) (uniform := preparation.2.2) (coordinate := coordinate)
    (first := ⟨segment.comparison.first, firstSheet⟩) (last := ⟨segment.comparison.last, lastSheet⟩)
    (depth := paid.2.2.2.2.val) (floor := floor) (allowance := target)
    (positive := positive) (request := paid.2.2.2.1) sample.1
    lifted segment.firstInside segment.lastInside points later

end Sample

end Segments

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison

end
