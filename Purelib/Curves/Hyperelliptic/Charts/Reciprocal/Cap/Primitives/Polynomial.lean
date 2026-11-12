module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
public import Purelib.Riemann.Normalization.InverseModelRootRequests.Weighted
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Parity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Tactic.Ring

/-! # Polynomial-numerator primitives on the retained ramified cap model

The original regular inverse model is refined once. Its product with the
full supplied numerator is integrated by the original finite parity pass.
The same primitive has its actual Taylor certificate and an operational
endpoint on the original quotient t, whose square names the rational w.
No rational reading is substituted for that operational coordinate.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse (Gaussian Polynomial Box)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Primitive
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Riemann.Normalization.InverseModelRootRequests (InverseRequest)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- Four exact retained caches for a full polynomial numerator on the original regular inverse model.

The primitive is the original parity primitive of N(w) times the cached
inverse polynomial under w=t². Its box certificate retains that same whole
polynomial. The exposed type permits the public whole-tuple factory law;
all runtime producers and readers remain opaque.
-/
@[expose] def PolynomialSample {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} (data : ReciprocalInnerInverse.Data curve collar)
    (numerator : Polynomial) (index : Nat) (box : Box) :=
  (inverse : { actual : Model data.polynomial collar.box //
    actual = data.model.refine index }) ×
  (regular : { actual : Polynomial // actual = numerator * inverse.val.value }) ×
  (integrated : { actual : Parity.Data regular.val true // actual = Parity.Data.build regular.val true }) ×
  { actual : Certificate.DensePrimitive (Substitution.Power.substitute regular.val 2) box //
    actual.value = integrated.val.value }

namespace PolynomialSample

/-- Retain the original inverse, full polynomial product, finite parity primitive and Taylor certificate once. -/
def build {genus : Nat} {curve : HyperellipticCurve genus} {collar : ReciprocalExteriorCollar.Data curve}
    (data : ReciprocalInnerInverse.Data curve collar) (numerator : Polynomial) (index : Nat) (box : Box) :
    PolynomialSample data numerator index box := by
  let inverse := data.model.refine index
  let regular := numerator * inverse.value
  let integrated := Parity.Data.build regular true
  let primitive : Certificate.DensePrimitive (Substitution.Power.substitute regular 2) box :=
    { value := integrated.value
      derivative_eq := fun point => (integrated.derivative_eq point).trans
        (Substitution.Power.eval_substitute regular 2 point).symm
      remainderBound := Bounds.Box.Taylor.denseTaylorRemainderBound integrated.value box
      remainderBound_nonnegative := (Bounds.Box.Taylor.denseTaylorRemainderBound_pos _ _).le
      increment_bound := fun {start finish} startInside finishInside => by
        have original := Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
          integrated.value finishInside startInside
        have derivative := (integrated.derivative_eq start).trans
          (Substitution.Power.eval_substitute regular 2 start).symm
        rewrite [GCD.derivative] at original
        rewrite [derivative] at original
        exact original }
  exact ⟨⟨inverse, rfl⟩, ⟨regular, rfl⟩, ⟨integrated, rfl⟩, ⟨primitive, rfl⟩⟩

/-- The whole retained result is the original complete once-only factory value, including all specification fields. -/
private theorem packaged_build_factory {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve}
    (data : ReciprocalInnerInverse.Data curve collar) (numerator : Polynomial) (index : Nat) (box : Box) :
    build data numerator index box =
  (
    by
      let inverse := data.model.refine index
      let regular := numerator * inverse.value
      let integrated := Parity.Data.build regular true
      let primitive : Certificate.DensePrimitive (Substitution.Power.substitute regular 2) box :=
        { value := integrated.value
          derivative_eq := fun point => (integrated.derivative_eq point).trans
            (Substitution.Power.eval_substitute regular 2 point).symm
          remainderBound := Bounds.Box.Taylor.denseTaylorRemainderBound integrated.value box
          remainderBound_nonnegative := (Bounds.Box.Taylor.denseTaylorRemainderBound_pos _ _).le
          increment_bound := fun {start finish} startInside finishInside => by
            have original := Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
              integrated.value finishInside startInside
            have derivative := (integrated.derivative_eq start).trans
              (Substitution.Power.eval_substitute regular 2 start).symm
            rewrite [GCD.derivative] at original
            rewrite [derivative] at original
            exact original }
      exact ⟨⟨inverse, rfl⟩, ⟨regular, rfl⟩, ⟨integrated, rfl⟩, ⟨primitive, rfl⟩⟩
    : PolynomialSample data numerator index box) := by rfl

/-- The whole retained result is the original complete once-only factory value, including all specification fields. -/
theorem build_factory {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve}
    (data : ReciprocalInnerInverse.Data curve collar) (numerator : Polynomial) (index : Nat) (box : Box) :
    build data numerator index box =
  (
    by
      let inverse := data.model.refine index
      let regular := numerator * inverse.value
      let integrated := Parity.Data.build regular true
      let primitive : Certificate.DensePrimitive (Substitution.Power.substitute regular 2) box :=
        { value := integrated.value
          derivative_eq := fun point => (integrated.derivative_eq point).trans
            (Substitution.Power.eval_substitute regular 2 point).symm
          remainderBound := Bounds.Box.Taylor.denseTaylorRemainderBound integrated.value box
          remainderBound_nonnegative := (Bounds.Box.Taylor.denseTaylorRemainderBound_pos _ _).le
          increment_bound := fun {start finish} startInside finishInside => by
            have original := Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
              integrated.value finishInside startInside
            have derivative := (integrated.derivative_eq start).trans
              (Substitution.Power.eval_substitute regular 2 start).symm
            rewrite [GCD.derivative] at original
            rewrite [derivative] at original
            exact original }
      exact ⟨⟨inverse, rfl⟩, ⟨regular, rfl⟩, ⟨integrated, rfl⟩, ⟨primitive, rfl⟩⟩
    : PolynomialSample data numerator index box) :=
  packaged_build_factory data numerator index box

/-- Read the same whole finite primitive and its actual box remainder certificate. -/
def primitive {genus : Nat} {curve : HyperellipticCurve genus} {collar : ReciprocalExteriorCollar.Data curve}
    {data : ReciprocalInnerInverse.Data curve collar} {numerator : Polynomial} {index : Nat} {box : Box}
    (sample : PolynomialSample data numerator index box) :
    Certificate.DensePrimitive (Substitution.Power.substitute sample.2.1.val 2) box := sample.2.2.2.val

/-- Read the same cached parity factor and its complete derivative/coefficient certificates. -/
def integrated {genus : Nat} {curve : HyperellipticCurve genus} {collar : ReciprocalExteriorCollar.Data curve}
    {data : ReciprocalInnerInverse.Data curve collar} {numerator : Polynomial} {index : Nat} {box : Box}
    (sample : PolynomialSample data numerator index box) : Parity.Data sample.2.1.val true := sample.2.2.1.val

/-- The Taylor primitive and parity primitive retain exactly the same polynomial value. -/
private theorem packaged_primitive_value {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} {index : Nat} {box : Box} (sample : PolynomialSample data numerator index box) :
    sample.primitive.value = sample.integrated.value := sample.2.2.2.property

/-- The Taylor primitive and parity primitive retain exactly the same polynomial value. -/
theorem primitive_value {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} {index : Nat} {box : Box} (sample : PolynomialSample data numerator index box) :
    sample.primitive.value = sample.integrated.value :=
  packaged_primitive_value (genus := genus) (curve := curve) (collar := collar) (data := data)
    (numerator := numerator) (index := index) (box := box) sample

/-- The original primitive derivative is the full numerator times the same inverse model at t². -/
private theorem packaged_derivative_eq {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} {index : Nat} {box : Box} (sample : PolynomialSample data numerator index box)
    (parameter : Gaussian) :
    (GCD.derivative sample.primitive.value).eval parameter =
      numerator.eval (parameter ^ 2) * (data.model.refine index).value.eval (parameter ^ 2) := by
  have original := (sample.primitive.derivative_eq parameter).trans
    (Substitution.Power.eval_substitute sample.2.1.val 2 parameter)
  have regular := congrArg (fun polynomial : Polynomial => polynomial.eval (parameter ^ 2)) sample.2.1.property
  have inverse := congrArg (fun actual : Model
      data.polynomial collar.box => actual.value.eval (parameter ^ 2)) sample.1.property
  exact original.trans (regular.trans (by rewrite [eval_mul, inverse]; rfl))

/-- The original primitive derivative is the full numerator times the same inverse model at t². -/
theorem derivative_eq {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {numerator : Polynomial} {index : Nat} {box : Box} (sample : PolynomialSample data numerator index box)
    (parameter : Gaussian) :
    (GCD.derivative sample.primitive.value).eval parameter =
      numerator.eval (parameter ^ 2) * (data.model.refine index).value.eval (parameter ^ 2) :=
  packaged_derivative_eq (genus := genus) (curve := curve) (collar := collar) (data := data)
    (numerator := numerator) (index := index) (box := box) sample parameter

/-- Request the full original numerator multiplication on the same supplied regular-factor root channel.

No Point or root channel is acquired here. The original request pays the
actual numerator at w before choosing its model and root comparison stages.
-/
def request {genus : Nat} {curve : HyperellipticCurve genus} {collar : ReciprocalExteriorCollar.Data curve}
    {data : ReciprocalInnerInverse.Data curve collar} {point : Gaussian} (owned : Owners.Point data point)
    (numerator : Polynomial) (target : Rational) (positive : 0 < target) (floor : Nat) :
    InverseRequest owned.channel (target / InverseRequest.weight (numerator.eval point)) floor :=
  InverseRequest.weighted (polynomial := data.polynomial) (box := collar.box) (model := data.model)
    (point := point) owned.channel (numerator.eval point) target positive floor

/-- Every independent later model/root reading pays the same cached polynomial coefficient at the actual w.

The estimate compares the retained inverse polynomial with the supplied
Point's original regular-root channel, not an independently chosen sign.
-/
private theorem packaged_accurate {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {point : Gaussian} {owned : Owners.Point data point} {numerator : Polynomial} {target : Rational}
    {floor index rootIndex : Nat} {box : Box}
    (paid : InverseRequest owned.channel (target / InverseRequest.weight (numerator.eval point)) floor)
    (sample : PolynomialSample data numerator index box) (later : paid.index ≤ index)
    (rootLater : paid.comparison.rightIndex ≤ rootIndex) :
    Norm.Basic.normSq (sample.2.1.val.eval point - numerator.eval point *
      Field.inv ((Sampling.approximation owned.certificate.value.name).sample rootIndex)) < target := by
  have bound := InverseRequest.weighted_accurate (polynomial := data.polynomial) (box := collar.box)
    (model := data.model) (point := point) (numerator := numerator.eval point) (target := target)
    (floor := floor) (index := index) (rootIndex := rootIndex) paid later rootLater
  have regular := congrArg (fun polynomial : Polynomial => polynomial.eval point) sample.2.1.property
  have inverse := congrArg (fun actual : Model
      data.polynomial collar.box => actual.value.eval point) sample.1.property
  have exactValue : sample.2.1.val.eval point = numerator.eval point * (data.model.refine index).value.eval point :=
    regular.trans (by rewrite [eval_mul, inverse]; rfl)
  exact Eq.mp (congrArg (fun value => Norm.Basic.normSq (value - numerator.eval point *
    Field.inv ((Sampling.approximation owned.certificate.value.name).sample rootIndex)) < target) exactValue.symm) bound

/-- Every independent later model/root reading pays the same cached polynomial coefficient at the actual w.

The estimate compares the retained inverse polynomial with the supplied
Point's original regular-root channel, not an independently chosen sign.
-/
theorem accurate {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {point : Gaussian} {owned : Owners.Point data point} {numerator : Polynomial} {target : Rational}
    {floor index rootIndex : Nat} {box : Box}
    (paid : InverseRequest owned.channel (target / InverseRequest.weight (numerator.eval point)) floor)
    (sample : PolynomialSample data numerator index box) (later : paid.index ≤ index)
    (rootLater : paid.comparison.rightIndex ≤ rootIndex) :
    Norm.Basic.normSq (sample.2.1.val.eval point - numerator.eval point *
      Field.inv ((Sampling.approximation owned.certificate.value.name).sample rootIndex)) < target :=
  packaged_accurate (genus := genus) (curve := curve) (collar := collar) (data := data)
    (point := point) (owned := owned) (numerator := numerator) (target := target)
    (floor := floor) (index := index) (rootIndex := rootIndex) (box := box) paid sample later rootLater

/-- The paid coefficient uses the exact regular-root certificate already stored in the same reciprocal overlap.

The whole certificate readback transports only its scalar reading. It does
not build another root channel or replace the retained quotient coordinate.
-/
private theorem packaged_overlap_accurate {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {point : Gaussian} {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : RootCoordinates.Overlap data point owner) {numerator : Polynomial} {target : Rational}
    {floor index rootIndex : Nat} {box : Box}
    (paid : InverseRequest overlap.regular.channel (target / InverseRequest.weight (numerator.eval point)) floor)
    (sample : PolynomialSample data numerator index box) (later : paid.index ≤ index)
    (rootLater : paid.comparison.rightIndex ≤ rootIndex) :
    Norm.Basic.normSq (sample.2.1.val.eval point - numerator.eval point *
      Field.inv ((Sampling.approximation overlap.regularRoot.value.name).sample rootIndex)) < target := by
  have original := accurate (genus := genus) (curve := curve) (collar := collar) (data := data)
    (point := point) (owned := overlap.regular) (numerator := numerator) (target := target)
    (floor := floor) (index := index) (rootIndex := rootIndex) (box := box) paid sample later rootLater
  have reading := congrArg (fun certificate : Riemann.RootContinuation.CertifiedSquareRoot.Certificate
      (data.polynomial.eval point) => (Sampling.approximation certificate.value.name).sample rootIndex)
    overlap.regularRoot_eq
  have inverse := congrArg Field.inv reading
  exact Eq.mp (congrArg (fun value => Norm.Basic.normSq (sample.2.1.val.eval point -
    numerator.eval point * value) < target) inverse.symm) original

/-- The paid coefficient uses the exact regular-root certificate already stored in the same reciprocal overlap.

The whole certificate readback transports only its scalar reading. It does
not build another root channel or replace the retained quotient coordinate.
-/
theorem overlap_accurate {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {point : Gaussian} {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : RootCoordinates.Overlap data point owner) {numerator : Polynomial} {target : Rational}
    {floor index rootIndex : Nat} {box : Box}
    (paid : InverseRequest overlap.regular.channel (target / InverseRequest.weight (numerator.eval point)) floor)
    (sample : PolynomialSample data numerator index box) (later : paid.index ≤ index)
    (rootLater : paid.comparison.rightIndex ≤ rootIndex) :
    Norm.Basic.normSq (sample.2.1.val.eval point - numerator.eval point *
      Field.inv ((Sampling.approximation overlap.regularRoot.value.name).sample rootIndex)) < target :=
  packaged_overlap_accurate (genus := genus) (curve := curve) (collar := collar) (data := data)
    (point := point) (owner := owner) (numerator := numerator) (target := target)
    (floor := floor) (index := index) (rootIndex := rootIndex) (box := box) overlap paid sample later rootLater

/-- The same finite primitive is operationally t times its retained factor at the actual reciprocal point.

The input is the actual prepared quotient v/r. Only its owned square law is
used: its displayed rational readings need not square to w at any stage.
-/
def endpointAgreement {genus : Nat} {curve : HyperellipticCurve genus} {collar : ReciprocalExteriorCollar.Data curve}
    {data : ReciprocalInnerInverse.Data curve collar} {point : Gaussian}
    {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : RootCoordinates.Overlap data point owner) (branch : HyperellipticReciprocal.originOrder curve = 1)
    {numerator : Polynomial} {index : Nat} {box : Box} (sample : PolynomialSample data numerator index box) :
    NamedEquivalent
      (Horner.polynomialEval sample.primitive.value overlap.coordinate.prepared.denominator).name
      (mul overlap.coordinate.prepared.denominator (Coherence.exact (sample.integrated.factor.eval point))).name := by
  have actualSquare := overlap.coordinate.square
  have scalar : point ^ HyperellipticReciprocal.originOrder curve = point := by rewrite [branch, pow_one]; rfl
  have square := NamedEquivalent.transport rfl (congrArg (fun value => (Coherence.exact value).name) scalar)
    actualSquare
  have original := Parity.square sample.integrated.value_coeffs overlap.coordinate.prepared.denominator point square
  exact NamedEquivalent.transport
    (congrArg (fun polynomial : Polynomial =>
      (Horner.polynomialEval polynomial overlap.coordinate.prepared.denominator).name) sample.primitive_value).symm
    rfl original

/-- The same quotient endpoint retains its actual factor, product value and derived primitive agreement.

The exposed exact type permits cache projections and its whole factory
readback. The sample and overlap remain the original indexed inputs.
-/
@[expose] def Endpoint {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {point : Gaussian} {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : RootCoordinates.Overlap data point owner) {numerator : Polynomial} {index : Nat} {box : Box}
    (sample : PolynomialSample data numerator index box) :=
  (factor : { actual : Gaussian // actual = sample.integrated.factor.eval point }) ×
  (value : { actual : CoherentNamed // actual = mul overlap.coordinate.prepared.denominator
    (Coherence.exact factor.val) }) ×
  NamedEquivalent (Horner.polynomialEval sample.primitive.value overlap.coordinate.prepared.denominator).name
    value.val.name

/-- Cache the actual polynomial factor and quotient endpoint once, deriving their original parity agreement.

The same supplied sample and original overlap supply every cache and
certificate. The comparison witness uses the original parity evaluator;
its independent numerical callbacks retain their original execution rules.
-/
def endpoint {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {point : Gaussian} {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : RootCoordinates.Overlap data point owner) (branch : HyperellipticReciprocal.originOrder curve = 1)
    {numerator : Polynomial} {index : Nat} {box : Box} (sample : PolynomialSample data numerator index box) :
    Endpoint overlap sample :=
  let factor := sample.integrated.factor.eval point
  let value := mul overlap.coordinate.prepared.denominator (Coherence.exact factor)
  let agreement := endpointAgreement (genus := genus) (curve := curve) (collar := collar) (data := data)
    (point := point) (owner := owner) overlap branch (numerator := numerator) (index := index) (box := box) sample
  ⟨⟨factor, rfl⟩, ⟨value, rfl⟩, agreement⟩

/-- The whole endpoint is the same retained factor, product value and original comparison factory. -/
private theorem packaged_endpoint_factory {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {point : Gaussian} {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : RootCoordinates.Overlap data point owner) (branch : HyperellipticReciprocal.originOrder curve = 1)
    {numerator : Polynomial} {index : Nat} {box : Box} (sample : PolynomialSample data numerator index box) :
    endpoint overlap branch sample =
    let factor := sample.integrated.factor.eval point
    let value := mul overlap.coordinate.prepared.denominator (Coherence.exact factor)
    let agreement := endpointAgreement (genus := genus) (curve := curve) (collar := collar) (data := data)
      (point := point) (owner := owner) overlap branch (numerator := numerator) (index := index) (box := box) sample
    ⟨⟨factor, rfl⟩, ⟨value, rfl⟩, agreement⟩ := by rfl

/-- The whole endpoint is the same retained factor, product value and original comparison factory. -/
theorem endpoint_factory {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {point : Gaussian} {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : RootCoordinates.Overlap data point owner) (branch : HyperellipticReciprocal.originOrder curve = 1)
    {numerator : Polynomial} {index : Nat} {box : Box} (sample : PolynomialSample data numerator index box) :
    endpoint overlap branch sample =
    let factor := sample.integrated.factor.eval point
    let value := mul overlap.coordinate.prepared.denominator (Coherence.exact factor)
    let agreement := endpointAgreement (genus := genus) (curve := curve) (collar := collar) (data := data)
      (point := point) (owner := owner) overlap branch (numerator := numerator) (index := index) (box := box) sample
    ⟨⟨factor, rfl⟩, ⟨value, rfl⟩, agreement⟩ :=
  packaged_endpoint_factory (genus := genus) (curve := curve) (collar := collar) (data := data)
    (point := point) (owner := owner) overlap branch (numerator := numerator) (index := index) (box := box) sample

/-- Select an actual endpoint comparison from the same retained quotient endpoint and parity primitive.

Both selected stages and every later reading belong to those same two
original names. The positive target and separate floors are paid by the
stored operational equivalence. No endpoint or acquisition is replayed.
-/
def endpointComparison {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {point : Gaussian} {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : RootCoordinates.Overlap data point owner)
    {numerator : Polynomial} {index : Nat} {box : Box} (sample : PolynomialSample data numerator index box)
    (retained : Endpoint overlap sample) (leftFloor rightFloor : Nat) (target : Rational) (positive : 0 < target) :
    Approximation.Gaussian.Equivalence.Comparison
      (Sampling.approximation
        (Horner.polynomialEval sample.primitive.value overlap.coordinate.prepared.denominator).name)
      (Sampling.approximation retained.2.1.val.name) leftFloor rightFloor target :=
  retained.2.2.compare leftFloor rightFloor target positive

/-- One paid endpoint retains its original request, primitive sample at that selected model stage and actual endpoint.

Each subtype identifies its complete factory value. The model stage is
computed by the original request, and all three later operations consume
that same request, sample and quotient endpoint without replay.
-/
@[expose] def PaidEndpoint {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {point : Gaussian} {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : RootCoordinates.Overlap data point owner) (branch : HyperellipticReciprocal.originOrder curve = 1)
    (numerator : Polynomial) (target : Rational) (positive : 0 < target) (floor : Nat) (box : Box) :=
  (paid : { actual : InverseRequest overlap.regular.channel
      (target / InverseRequest.weight (numerator.eval point)) floor //
    actual = request overlap.regular numerator target positive floor }) ×
  (sample : { actual : PolynomialSample data numerator paid.val.index box //
    actual = build data numerator paid.val.index box }) ×
  { actual : Endpoint overlap sample.val // actual = endpoint overlap branch sample.val }

/-- Select the original paid model stage, then retain one actual sample and its same quotient endpoint.

The request, full numerator model, finite primitive and endpoint are
constructed in that order. Existing endpoint-comparison callbacks remain
independent computations; no cross-callback memoization is asserted.
-/
def paidEndpoint {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {point : Gaussian} {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    (overlap : RootCoordinates.Overlap data point owner) (branch : HyperellipticReciprocal.originOrder curve = 1)
    (numerator : Polynomial) (target : Rational) (positive : 0 < target) (floor : Nat) (box : Box) :
    PaidEndpoint overlap branch numerator target positive floor box :=
  let paid := request overlap.regular numerator target positive floor
  let sample := build (genus := genus) (curve := curve) (collar := collar) data numerator paid.index box
  let actual := endpoint (genus := genus) (curve := curve) (collar := collar) (data := data)
    (point := point) (owner := owner) overlap branch (numerator := numerator) (index := paid.index) (box := box) sample
  ⟨⟨paid, rfl⟩, ⟨sample, rfl⟩, ⟨actual, rfl⟩⟩

/-- The same paid endpoint already meets its model-stage requirement and pays every later retained root reading. -/
private theorem packaged_paidEndpoint_accurate {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {point : Gaussian} {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    {overlap : RootCoordinates.Overlap data point owner} {branch : HyperellipticReciprocal.originOrder curve = 1}
    {numerator : Polynomial} {target : Rational} {positive : 0 < target} {floor : Nat} {box : Box}
    (retained : PaidEndpoint overlap branch numerator target positive floor box) {rootIndex : Nat}
    (later : retained.1.val.comparison.rightIndex ≤ rootIndex) :
    Norm.Basic.normSq (retained.2.1.val.2.1.val.eval point - numerator.eval point *
      Field.inv ((Sampling.approximation overlap.regularRoot.value.name).sample rootIndex)) < target :=
  overlap_accurate (genus := genus) (curve := curve) (collar := collar) (data := data)
    (point := point) (owner := owner) overlap (numerator := numerator) (target := target)
    (floor := floor) (index := retained.1.val.index) (rootIndex := rootIndex) (box := box)
    retained.1.val retained.2.1.val (Nat.le_refl _) later

/-- The same paid endpoint already meets its model-stage requirement and pays every later retained root reading. -/
theorem paidEndpoint_accurate {genus : Nat} {curve : HyperellipticCurve genus}
    {collar : ReciprocalExteriorCollar.Data curve} {data : ReciprocalInnerInverse.Data curve collar}
    {point : Gaussian} {owner : Owner ((HyperellipticReciprocal.polynomial curve).eval point)}
    {overlap : RootCoordinates.Overlap data point owner} {branch : HyperellipticReciprocal.originOrder curve = 1}
    {numerator : Polynomial} {target : Rational} {positive : 0 < target} {floor : Nat} {box : Box}
    (retained : PaidEndpoint overlap branch numerator target positive floor box) {rootIndex : Nat}
    (later : retained.1.val.comparison.rightIndex ≤ rootIndex) :
    Norm.Basic.normSq (retained.2.1.val.2.1.val.eval point - numerator.eval point *
      Field.inv ((Sampling.approximation overlap.regularRoot.value.name).sample rootIndex)) < target :=
  packaged_paidEndpoint_accurate (genus := genus) (curve := curve) (collar := collar) (data := data)
    (point := point) (owner := owner) (overlap := overlap) (branch := branch) (numerator := numerator)
    (target := target) (positive := positive) (floor := floor) (box := box) (rootIndex := rootIndex) retained later

end PolynomialSample

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives

end
