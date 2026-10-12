module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner
public import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Parity
import Purelib.Riemann.Topology.SquareRootContinuationChain

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Polynomial.Dense.Gaussian.Primitive.Parity
import Purelib.Riemann.RootContinuation.SquareRootProvenance
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.DifferentialTransport
import Init.ByCases
import Init.Core
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership

public section

/-!
# Cap primitive values on the actual reciprocal collar coordinates

In odd degree the retained root ratio is the coordinate t, with t²=w.
In even degree it is the sheet sign, and the coordinate is the rational w.
The endpoint caches its rational polynomial factor and evaluates just the
retained ratio times that factor. An operational certificate identifies this
value with the actual cached cap primitive, including the even sheet sign.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Polynomial.Approximation.Gaussian.Evaluation

open Purelib.Polynomial.Dense.Gaussian.Primitive

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames (Gaussian)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates (Overlap)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence (coherentMul_respects)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner (polynomialEval)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {point :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames.Gaussian}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat} {box :
    Purelib.Geometry.Rational.Box}

/-- Evaluate a cap primitive in its intrinsic coordinate chart.

The even chart retains the quotient as its sheet sign, while the odd chart
uses that same channel as its coordinate for the cached primitive polynomial. -/
@[expose] def chartPrimitive (overlap : RootCoordinates.Overlap cap point owner)
    (sample : Primitives.Sample cap differential index box) : CoherentNamed :=
  if HyperellipticReciprocal.originOrder curve = 0 then
    CoherentNamed.mul overlap.coordinate.prepared.denominator
      (Horner.polynomialEval sample.primitive.value (Coherence.exact point))
  else Horner.polynomialEval sample.primitive.value overlap.coordinate.prepared.denominator

set_option genInjectivity false in
/-- Cache a cap endpoint value and its exact coefficient provenance.

The factor, parity-dependent coefficient and operational value retain the
supplied primitive sample and quotient-coordinate occurrence. Their readbacks
identify that same cached value with the intrinsic cap chart evaluation. -/
structure Endpoint (overlap : RootCoordinates.Overlap cap point owner)
    (sample : Primitives.Sample cap differential index box) where
  /-- The cached rational factor of the original cap primitive at the retained collar point. -/ factor :
    ReciprocalRootNames.Gaussian
  /-- The cached factor equals the original retained sample factor polynomial evaluation. -/ factor_eq : factor =
    sample.factor.eval point
  /-- The cached rational endpoint coefficient including the original reciprocal parity power. -/ coefficient :
    ReciprocalRootNames.Gaussian
  /-- The coefficient is exactly the original point parity power times the cached primitive factor. -/ coefficient_eq :
    coefficient = point ^
    (1 - HyperellipticReciprocal.originOrder curve) * factor
  /-- The cached operational endpoint value on the original retained coordinate channel. -/ value :
    Coherent.CoherentNamed
  /-- The endpoint value is exactly the retained coordinate channel times its cached exact coefficient. -/ value_eq :
    value = CoherentNamed.mul overlap.coordinate.prepared.denominator (Coherence.exact coefficient)
  /-- The actual original cap primitive evaluator is operationally equivalent to the cached endpoint value. -/ agrees :
    Gaussian.Equivalence.NamedEquivalent (overlap.chartPrimitive sample).name value.name

constructive_injectivity Endpoint

namespace Endpoint

/-- Cache the original primitive factor and endpoint coefficient and certify their actual cap-coordinate evaluation.

The degree branch preserves the original quotient root coordinate, using its square law in the ramified case. -/
@[expose] def build (overlap : RootCoordinates.Overlap cap point owner)
    (sample : Primitives.Sample cap differential index box) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Endpoint overlap sample := by
  let factor := sample.factor.eval point
  let coefficient := point ^ (1 - HyperellipticReciprocal.originOrder curve) * factor
  let value := CoherentNamed.mul overlap.coordinate.prepared.denominator (Coherence.exact coefficient)
  refine ⟨factor, rfl, coefficient, rfl, value, rfl, ?_⟩
  by_cases regular : HyperellipticReciprocal.originOrder curve = 0
  · have primitiveAt : sample.primitive.value.eval point =
        point * factor := by
      have retained := sample.primitive_factor point
      rw [Primitives.point, Primitives.degree, regular, Nat.zero_add, pow_one] at retained
      exact retained
    have coefficient_eq : coefficient = sample.primitive.value.eval point := by
      dsimp only [coefficient]
      rw [regular, Nat.sub_zero, pow_one, primitiveAt]
    rw [chartPrimitive, if_pos regular]
    change Gaussian.Equivalence.NamedEquivalent
      (CoherentNamed.mul overlap.coordinate.prepared.denominator
        (Horner.polynomialEval sample.primitive.value (Coherence.exact point))).name
      (CoherentNamed.mul overlap.coordinate.prepared.denominator (Coherence.exact coefficient)).name
    rw [coefficient_eq]
    exact Congruence.coherentMul_respects _ _ _ _ (NamedEquivalent.refl _)
      (Horner.polynomialEval_exact sample.primitive.value point)
  · have branch := (HyperellipticReciprocal.origin_factor curve).2.resolve_left regular
    have coefficients : sample.primitive.value.coeffs =
        Parity.valueCoefficients sample.factor true := by
      have retained := sample.primitive_coeffs
      rw [branch] at retained
      exact retained
    have square : Gaussian.Equivalence.NamedEquivalent
        (CoherentNamed.mul overlap.coordinate.prepared.denominator overlap.coordinate.prepared.denominator).name
        (Coherence.exact point).name := by
      have retained := overlap.coordinate.square
      change Gaussian.Equivalence.NamedEquivalent
        (CoherentNamed.mul overlap.coordinate.prepared.denominator overlap.coordinate.prepared.denominator).name
        (Coherence.exact (point ^ HyperellipticReciprocal.originOrder curve)).name at retained
      have parameter : point ^ HyperellipticReciprocal.originOrder curve = point := by
        rw [branch, pow_one]
      have names := congrArg (fun scalar => (Coherence.exact scalar).name) parameter
      exact names ▸ retained
    have evaluated := Parity.square coefficients
      overlap.coordinate.prepared.denominator point square
    rw [chartPrimitive, if_neg regular]
    dsimp only [value, coefficient, factor]
    have scalar : point ^ (1 - HyperellipticReciprocal.originOrder curve) *
        sample.factor.eval point = sample.factor.eval point := by
      rw [branch, Nat.sub_self, pow_zero, Data.Gaussian.Basic.one_mul]
    rw [scalar]
    exact evaluated

/-- Transport the endpoint value through its attached winding-owner presentation.

The supplied owner keeps the same root occurrence and cached coefficient;
its operational comparison identifies the two coordinate presentations. -/
@[expose] def attached_value {overlap : RootCoordinates.Overlap cap point owner}
    {sample : Primitives.Sample cap differential index box} (endpoint :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Endpoint overlap sample) :
    let root := overlap.attached.owner.certificate overlap.attached.owner.parameterNonzero
    Gaussian.Equivalence.NamedEquivalent (CoherentNamed.mul root.value (Coherence.exact endpoint.coefficient)).name
      endpoint.value.name := by
  rw [endpoint.value_eq]
  exact Congruence.coherentMul_respects _ _ _ _ overlap.attached.equivalent.symm (NamedEquivalent.refl _)

variable {overlap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap cap point owner}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Read the retained coordinate and multiply by its cached coefficient.

The approximation uses the supplied coordinate channel and endpoint cache,
without evaluating the polynomial or preparing another root. -/
@[expose] def approximation (endpoint : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Endpoint
  overlap sample) : Gaussian.Sequence.ApproximationData :=
  Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation
    overlap.coordinate.prepared.denominator.name (Coherence.exact endpoint.coefficient).name

/-- Every endpoint approximation sample is the original retained coordinate reading times the cached exact coefficient.
-/
theorem sample_eq (endpoint : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Endpoint overlap
  sample) (stage : Nat) :
    endpoint.approximation.sample stage =
      (Sampling.approximation overlap.coordinate.prepared.denominator.name).sample stage *
        endpoint.coefficient := rfl

/-- Compare the direct endpoint readings with the cap primitive evaluator.

The operational endpoint identity transports the retained coefficient program
through the sampled-product bridge, preserving independent reading indices. -/
@[expose] def sampled_agreement (endpoint : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Endpoint
  overlap sample) :
    Gaussian.Equivalence.Equivalent
      (Sampling.approximation (overlap.chartPrimitive sample).name) endpoint.approximation := by
  have bridge : Gaussian.Equivalence.NamedEquivalent endpoint.value.name endpoint.approximation.toNamed := by
    rw [endpoint.value_eq]
    exact Bridge.coherentMul_toNamed
      overlap.coordinate.prepared.denominator (Coherence.exact endpoint.coefficient)
  exact Equivalent.trans (endpoint.agrees.trans bridge)
    (Equivalent.toNamed_sampling endpoint.approximation)

end Endpoint
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap
