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
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Parity
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Polynomial.Dense.Gaussian.Primitive.Parity
import Purelib.Riemann.RootContinuation.SquareRootProvenance
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Init.ByCases
import Init.Core
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Normalization.InverseRootPolynomial

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates

open Purelib.Polynomial.Approximation.Gaussian.Evaluation

open Purelib.Polynomial.Dense.Gaussian.Primitive

open Purelib.Riemann.RootContinuation

/-!
# Cached primitive readings at actual reciprocal disk points

Both degree parities use the retained quotient coordinate and a cached
polynomial factor. The finite square law identifies these direct readings
with the actual cap primitive throughout the certified reciprocal disk.
-/

open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames (Gaussian)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates (Overlap)
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

set_option genInjectivity false in
/-- Cache a disk endpoint value and its exact coefficient provenance.

The original primitive sample and quotient-coordinate occurrence determine the
factor, parity-dependent coefficient and named value. Their readbacks identify
that same cache with the intrinsic chart's operational evaluation. -/
structure Endpoint (overlap : Coordinates.Overlap cap point owner)
    (sample : Primitives.Sample cap differential index box) where
  /-- The cached original primitive factor evaluated at the disk point. -/ factor : ReciprocalRootNames.Gaussian
  /-- The cached factor equals the retained sample factor at the actual disk point. -/ factor_eq : factor =
    sample.factor.eval point
  /-- The cached coordinate-power factor multiplying the retained quotient channel. -/ coefficient :
    ReciprocalRootNames.Gaussian
  /-- The cached coefficient equals the reciprocal-origin coordinate power times the retained primitive factor. -/
    coefficient_eq : coefficient = point ^
    (1 - HyperellipticReciprocal.originOrder curve) * factor
  /-- The cached named endpoint value on the retained quotient coordinate channel. -/ value : Coherent.CoherentNamed
  /-- The cached value multiplies the original prepared coordinate by the exact cached coefficient. -/ value_eq : value
    = CoherentNamed.mul overlap.coordinate.prepared.denominator (Coherence.exact coefficient)
  /-- The cached endpoint value is operationally equivalent to the original chart primitive evaluator. -/ agrees :
    Gaussian.Equivalence.NamedEquivalent (overlap.chartPrimitive sample).name value.name

constructive_injectivity Endpoint

namespace Endpoint

/-- Cache the original primitive factor and named disk endpoint value.

The degree branch retains its coordinate-power coefficient and original square
comparison, certifying operational agreement with the supplied cap primitive. -/
@[expose] def build (overlap : Coordinates.Overlap cap point owner)
    (sample : Primitives.Sample cap differential index box) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint overlap sample := by
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

variable {overlap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap point owner}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Read the retained disk coordinate with its cached rational coefficient.

The readings use the existing coordinate channel and endpoint cache without
re-evaluating the polynomial or preparing another root. -/
@[expose] def approximation (endpoint : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint overlap
  sample) : Gaussian.Sequence.ApproximationData :=
  Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation
    overlap.coordinate.prepared.denominator.name (Coherence.exact endpoint.coefficient).name

/-- Every direct endpoint sample multiplies the retained coordinate reading by the cached rational coefficient. -/
theorem sample_eq (endpoint : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint overlap sample)
  (stage : Nat) :
    endpoint.approximation.sample stage =
      (Sampling.approximation overlap.coordinate.prepared.denominator.name).sample stage *
        endpoint.coefficient := rfl

/-- Compare direct disk endpoint readings with the original cap primitive.

The endpoint's operational agreement and the sampled-product bridge retain
both approximation owners and their independent later reading indices. -/
@[expose] def sampled_agreement (endpoint : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint
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
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap
