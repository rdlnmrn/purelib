module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Semiring.Normalization
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Apart.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Bridge
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
public import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Value
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Boundary

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
public import Purelib.Riemann.RootContinuation.SquareRootProvenance
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Apart
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Apart

open Purelib.Approximation.Gaussian.Name.Basic

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry.Rational.Box

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Topology

@[expose] public section

/-!
# Reciprocal roots from the actual original root channel

The reciprocal root name multiplies the supplied source channel by the exact
coordinate factor. Its square equation and division safety are constructed,
not supplied as gluing hypotheses. Its explicit equivalence to that product
retains the original root occurrence. Attaching a reciprocal winding track
to this channel remains a separate finite ownership construction.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames

/-- Exact Gaussian rational reciprocal coordinates and scale factors. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- Exact rational parameters of original prepared edges. -/
abbrev Coordinate := Fraction.Rational
/-- A Gaussian name retaining its coherent approximation sequence. -/
abbrev CoherentNamed := Coherent.CoherentNamed
/-- Operational equivalence of retained Gaussian names. -/
abbrev NamedEquivalent := Gaussian.Equivalence.NamedEquivalent
/-- A retained quantitative certificate that the original Gaussian name is apart from zero. -/
abbrev Apart := Named.Apart
/-- A division-ready presentation equivalent to the original Gaussian name. -/
abbrev Prepared := Approximation.Gaussian.Division.Prepared

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence (coherentMul_respects)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws (coherentMul_assoc coherentMul_comm)
open Purelib.Riemann.RootContinuation.SquareRootProvenance (SquareIdentity)

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
/-- The arithmetic expression whose root occurrence must be preserved. -/
def scaled (factor : Gaussian) (source : CoherentNamed) : CoherentNamed := CoherentNamed.mul (Coherence.exact factor)
  source

/-- Transport the original sampled denominator lower bound through multiplication by a nonzero exact Gaussian factor.

The original sampled denominator lower bound is multiplied by the exact factor quadrance. The nonzero factor supplies
positivity, and each retained synchronized product sample satisfies the same computed bound. -/
def scaledPossibleApart (factor : Gaussian) (nonzero : factor ≠ 0)
    (source : CoherentNamed) (apart : Apart source.name) :
    Possible.PossibleApart
      (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation (Coherence.exact factor).name
        source.name).toProcess where
  lowerSq := Data.Gaussian.Norm.Basic.normSq factor * apart.certificate.lowerSq
  positive := Fraction.Order.Arithmetic.mul_pos_direct (Data.Gaussian.Norm.Basic.normSq_pos nonzero)
    apart.certificate.positive
  lower := by
    intro state value possible
    rcases possible with ⟨later, _order, rfl⟩
    rw [Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation_sample]
    change Data.Gaussian.Norm.Basic.normSq factor * apart.certificate.lowerSq ≤
      Data.Gaussian.Norm.Basic.normSq (factor * (Sampling.approximation source.name).sample later)
    rw [Data.Gaussian.Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Sampling.sampled_lower source apart later) (Data.Gaussian.Norm.Basic.normSq_nonneg factor)

/-- Product samples inherit the displayed source lower bound. Apartification uses this direct certificate, without a
fresh square-root isolation or a search through the square-identity comparison tree.

The product approximation retains the original source samples and exact factor. Its transported lower certificate
prepares that same product channel, with explicit equivalence to the original coherent multiplication. -/
def prepareScaled (factor : Gaussian) (nonzero : factor ≠ 0)
    (source : CoherentNamed) (apart : Apart source.name) : Prepared (scaled factor source) :=
  let product := CoherentNamed.ofApproximation
    (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation (Coherence.exact factor).name source.name)
  let lower := scaledPossibleApart factor nonzero source apart
  { denominator := product.apartify lower
    apart := ⟨Preparation.apartifyApart lower⟩
    equivalent := (Bridge.coherentMul_toNamed (Coherence.exact factor) source).trans
      (product.apartifyEquivalent lower) }

/-- Operational multiplication transports the square identity; no rational reading is asserted to be an exact square
root. -/
def scaled_square {source : CoherentNamed} {parameter : Gaussian}
    (square : SquareRootProvenance.SquareIdentity source parameter) (factor : Gaussian) :
    SquareRootProvenance.SquareIdentity (scaled factor source) (factor * factor * parameter) :=
  (Laws.coherentMul_squares_interchange (Coherence.exact factor) source).symm.trans
    ((Congruence.coherentMul_respects (CoherentNamed.mul (Coherence.exact factor) (Coherence.exact factor))
      (Coherence.exact (factor * factor))
      (CoherentNamed.mul source source) (Coherence.exact parameter) (Exact.Arithmetic.exact_mul factor factor)
        square).trans
      (Exact.Arithmetic.exact_mul (factor * factor) parameter))

end

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames in
set_option genInjectivity false in
/-- A division-ready reciprocal root presentation of the original scaled root channel.

Its square identity uses the retained prepared denominator and exact target parameter. -/
structure ScaledRoot (source : CertifiedSquareRoot.Certificate parameter) (factor target : Gaussian) where
  /-- The retained division-ready presentation equivalent to the original root channel multiplied by the exact factor.
  -/
  prepared : Prepared (scaled factor source.value)
  /-- The retained denominator squared is operationally equivalent to the exact target parameter. -/ square :
    SquareRootProvenance.SquareIdentity prepared.denominator target

constructive_injectivity ScaledRoot

namespace ScaledRoot

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
/-- Prepare the original scaled root channel and transport its square identity using the retained exact parameter
equation. -/
def build (source : CertifiedSquareRoot.Certificate parameter) (factor : Gaussian) (nonzero : factor ≠ 0)
    (target : Gaussian) (identity : factor * factor * parameter = target) : ScaledRoot source factor target := by
  let prepared := prepareScaled factor nonzero source.value source.apart
  refine ⟨prepared, ?_⟩
  have square : SquareRootProvenance.SquareIdentity (scaled factor source.value) target := by
    rw [← identity]
    exact scaled_square source.square factor
  exact (Congruence.coherentMul_respects prepared.denominator (scaled factor source.value)
    prepared.denominator (scaled factor source.value) prepared.equivalent.symm prepared.equivalent.symm).trans square

/-- Read the square-root certificate from the retained division-ready denominator and its exact square identity. -/
def certificate (root : ScaledRoot source factor target) : CertifiedSquareRoot.Certificate target :=
  ⟨root.prepared.denominator, root.prepared.apart, root.square⟩

end ScaledRoot

/-- Inverting a nonzero Gaussian rational twice returns the original value. -/
private theorem inverse_inverse (source : Gaussian) (nonzero : source ≠ 0) : (source⁻¹)⁻¹ = source := by
  apply Data.Gaussian.Field.mul_right_cancel_of_ne (Algebra.Field.ExplicitField.inv_ne_zero nonzero)
  calc
    _ = source⁻¹ * (source⁻¹)⁻¹ := Data.Gaussian.Basic.mul_comm _ _
    _ = 1 := Algebra.Field.ExplicitField.mul_inv_cancel _ (Algebra.Field.ExplicitField.inv_ne_zero nonzero)
    _ = _ := (Algebra.Field.ExplicitField.mul_inv_cancel source nonzero).symm

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.PreparedModels (rootAtCached)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)

/-- The reciprocal root scale is the inverse original coordinate raised to genus plus one. -/
def factor (genus : Nat) (source : Gaussian) : Gaussian := (source⁻¹) ^ (genus + 1)

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
/-- A nonzero original coordinate gives a nonzero reciprocal root scale. -/
theorem factor_nonzero (genus : Nat) {source : Gaussian} (nonzero : source ≠ 0) : factor genus source ≠ 0 :=
  Power.pow_ne_zero_direct _ (Algebra.Field.ExplicitField.inv_ne_zero nonzero) _

/-- The squared reciprocal root scale transforms the original curve radicand to the reciprocal radicand. -/
theorem factor_identity {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (source : Gaussian)
  (nonzero : source ≠ 0) :
    factor genus source * factor genus source * curve.polynomial.eval source =
      (HyperellipticReciprocal.polynomial curve).eval source⁻¹ := by
  rw [HyperellipticReciprocal.polynomial_identity curve source⁻¹ (Algebra.Field.ExplicitField.inv_ne_zero nonzero),
    inverse_inverse source nonzero, factor, ← pow_add, show genus + 1 + (genus + 1) = 2 * genus + 2 by omega]

/-- Consume the original retained owner's existing operational certificate. The result is a division-ready reciprocal
root channel, not an independently numbered reciprocal root. -/
def ofOwner {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (source : Gaussian) (nonzero : source ≠
  0)
    (owner : SquareRootContinuationChain.Owner (curve.polynomial.eval source)) :
    ScaledRoot (owner.certificate owner.parameterNonzero) (factor genus source)
      ((HyperellipticReciprocal.polynomial curve).eval source⁻¹) :=
  ScaledRoot.build (owner.certificate owner.parameterNonzero) (factor genus source) (factor_nonzero genus nonzero)
    _ (factor_identity curve source nonzero)

/-- Scale the retained original boundary root owner into its division-ready reciprocal root channel. -/
def ofBoundaryOwner {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (source : Gaussian)
    (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) source)
    (owner : SquareRootContinuationChain.Owner (curve.polynomial.eval source)) :
    ScaledRoot (owner.certificate owner.parameterNonzero) (factor genus source)
      ((HyperellipticReciprocal.polynomial curve).eval source⁻¹) :=
  ofOwner curve source (PreparedExteriorReciprocal.boundary_nonzero boundary) owner

/-- Multiplying a scaled original denominator by its quotient cancels that same denominator operationally.

The supplied denominator is apart from zero. Original synchronized quotient cancellation and product association
identify the retained product with the exact scaled numerator. -/
def scaled_mul_quotient (factor numerator : Gaussian) (denominator : CoherentNamed) (apart : Apart denominator.name) :
    NamedEquivalent (CoherentNamed.mul (scaled factor denominator)
      (CoherentNamed.div (Coherence.exact numerator) denominator apart)).name
      (Coherence.exact (factor * numerator)).name := by
  exact (Laws.coherentMul_assoc (Coherence.exact factor) denominator
    (CoherentNamed.div (Coherence.exact numerator) denominator apart)).trans
    ((Congruence.coherentMul_respects (Coherence.exact factor) (Coherence.exact factor)
      (CoherentNamed.mul denominator (CoherentNamed.div (Coherence.exact numerator) denominator apart)) (Coherence.exact
        numerator)
      (NamedEquivalent.refl _)
      ((Laws.coherentMul_comm denominator (CoherentNamed.div (Coherence.exact numerator) denominator apart)).trans
        (Cancellation.coherentDiv_mul_cancel (Coherence.exact numerator) denominator apart))).trans
      (Exact.Arithmetic.exact_mul factor numerator))

/-- An exact numerator scaling identity identifies division by the prepared scaled denominator with division by the
original denominator.

The prepared denominator remains equivalent to the scaled original denominator, and the supplied exact numerator
identity aligns their quotients. Cancellation uses those same retained apartness certificates and quotient programs. -/
def quotient_scaled (source : CoherentNamed) (apart : Apart source.name)
    (factor first second : Gaussian) (prepared : Prepared (scaled factor source))
    (identity : factor * second = first) :
    NamedEquivalent
      (CoherentNamed.div (Coherence.exact first) prepared.denominator prepared.apart).name
      (CoherentNamed.div (Coherence.exact second) source apart).name := by
  let left := CoherentNamed.div (Coherence.exact first) prepared.denominator prepared.apart
  let right := CoherentNamed.div (Coherence.exact second) source apart
  have leftCancel : NamedEquivalent (CoherentNamed.mul prepared.denominator left).name (Coherence.exact first).name :=
    (Laws.coherentMul_comm prepared.denominator left).trans
      (Cancellation.coherentDiv_mul_cancel (Coherence.exact first) prepared.denominator prepared.apart)
  have rightCancel : NamedEquivalent (CoherentNamed.mul prepared.denominator right).name (Coherence.exact first).name :=
    by
    have cancel := (Congruence.coherentMul_respects prepared.denominator (scaled factor source)
      right right prepared.equivalent.symm (NamedEquivalent.refl _)).trans
      (scaled_mul_quotient factor second source apart)
    rw [identity] at cancel
    exact cancel
  exact Cancellation.coherentMul_cancel_left prepared.denominator left right prepared.apart
    (leftCancel.trans rightCancel.symm)

end

/-- An exact constant factor can move into the numerator of the retained operational quotient.

The original denominator and its apartness certificate are retained in both quotients. Product association and exact
scalar multiplication move the constant into the numerator without selecting new samples. -/
def constant_mul_quotient (constant numerator : Gaussian) (source : CoherentNamed)
    (apart : Apart source.name) :
    NamedEquivalent
      (CoherentNamed.mul (Coherence.exact constant) (CoherentNamed.div (Coherence.exact numerator) source apart)).name
      (CoherentNamed.div (Coherence.exact (constant * numerator)) source apart).name := by
  let quotient := CoherentNamed.div (Coherence.exact numerator) source apart
  let left := CoherentNamed.mul (Coherence.exact constant) quotient
  let right := CoherentNamed.div (Coherence.exact (constant * numerator)) source apart
  have leftCancel : NamedEquivalent (CoherentNamed.mul source left).name (Coherence.exact (constant * numerator)).name
    :=
    (Laws.coherentMul_comm source left).trans
      ((Laws.coherentMul_assoc (Coherence.exact constant) quotient source).trans
        ((Congruence.coherentMul_respects (Coherence.exact constant) (Coherence.exact constant) (CoherentNamed.mul
          quotient source) (Coherence.exact numerator)
          (NamedEquivalent.refl _) (Cancellation.coherentDiv_mul_cancel (Coherence.exact numerator) source apart)).trans
          (Exact.Arithmetic.exact_mul constant numerator)))
  have rightCancel : NamedEquivalent (CoherentNamed.mul source right).name (Coherence.exact (constant * numerator)).name
    :=
    (Laws.coherentMul_comm source right).trans
      (Cancellation.coherentDiv_mul_cancel (Coherence.exact (constant * numerator)) source apart)
  exact Cancellation.coherentMul_cancel_left source left right apart
    (leftCancel.trans rightCancel.symm)

/-- The finite named power of an exact Gaussian value is operationally equivalent to its exact scalar power.

The same coherent exact Gaussian value supplies every multiplication in the finite named power. Natural induction
identifies that program with the original scalar power at the same exponent. -/
def exact_power (point : Gaussian) (exponent : Nat) :
    NamedEquivalent (Power.namedPower (Coherence.exact point) exponent).name
      (Coherence.exact (point ^ exponent)).name := by
  induction exponent with
  | zero => exact NamedEquivalent.refl _
  | succ exponent inductionHypothesis =>
      exact (Congruence.coherentMul_respects (Power.namedPower (Coherence.exact point) exponent)
        (Coherence.exact (point ^ exponent)) (Coherence.exact point) (Coherence.exact point) inductionHypothesis
        (NamedEquivalent.refl _)).trans
        (by
            simpa only [pow_succ, CoherentNamed.mul]
              using Exact.Arithmetic.exact_mul (point ^ exponent) point)

/-- The original differential value is operationally equivalent to its exact coordinate-power numerator divided by the
same retained root.

The supplied coherent root and its original apartness certificate are retained as the denominator. The finite named
coordinate power is compared with its exact scalar numerator through the original quotient congruence. -/
def differential_quotient {genus : Nat} (differential : Differentials.Basic.Differential genus) (point : Gaussian)
    (source : CoherentNamed) (apart : Apart source.name) :
    NamedEquivalent (Value.differentialValue differential point source apart).name
      (CoherentNamed.div (Coherence.exact (point ^ differential.exponent)) source apart).name :=
  Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence.coherentDiv_respects
    (Power.namedPower (Coherence.exact point) differential.exponent) (Coherence.exact (point ^ differential.exponent))
    source source apart apart (exact_power point differential.exponent) (NamedEquivalent.refl _)

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
/-- The reciprocal root scale and inverse-coordinate Jacobian transform the original differential numerator to the
negative reversed-exponent numerator.

The differential exponent and genus satisfy the original finite balance equation. At a nonzero coordinate, inverse
powers cancel and leave the negative reversed-exponent numerator. -/
theorem numerator_identity {genus : Nat} (differential : Differentials.Basic.Differential genus)
    (source : Gaussian) (nonzero : source ≠ 0) :
    factor genus source * (-(source ^ 2) * source ^ differential.exponent) =
      -((source⁻¹) ^ (HyperellipticReciprocal.reversedDifferential differential).exponent) := by
  have powers : source ^ (differential.exponent + 2) * factor genus source =
      (source⁻¹) ^ (HyperellipticReciprocal.reversedDifferential differential).exponent := by
    rw [factor, ← HyperellipticReciprocal.differential_balance differential, pow_add]
    calc
      _ = (source ^ (differential.exponent + 2) * (source⁻¹) ^ (differential.exponent + 2)) *
          (source⁻¹) ^ (HyperellipticReciprocal.reversedDifferential differential).exponent := by ring1
      _ = _ := by
        rw [← Algebra.Semiring.Normalization.product_pow, Algebra.Field.ExplicitField.mul_inv_cancel source nonzero,
          one_pow, Data.Gaussian.Basic.one_mul]
  calc
    _ = -(source ^ (differential.exponent + 2) * factor genus source) := by rw [pow_add]; ring1
    _ = _ := congrArg Neg.neg powers

/-- The reciprocal integrand uses the minus sign from inversion and the reversed basis exponent. It consumes the cached,
division-safe presentation of the scaled original root and the existing named-power differential program. -/
def coefficient {genus : Nat} (differential : Differentials.Basic.Differential genus) (source : Gaussian)
    {parameter target : Gaussian} {original : CertifiedSquareRoot.Certificate parameter}
    (root : ScaledRoot original (factor genus source) target) : CoherentNamed :=
  CoherentNamed.mul (Coherence.exact (-1)) (Value.differentialValue
    (HyperellipticReciprocal.reversedDifferential differential) source⁻¹
    root.prepared.denominator root.prepared.apart)

/-- Operational change of differential coefficient, preserving the actual original root channel. This is an equality of
finite approximation programs, not an assertion that their rational readings are exact roots. The factor `-z²` is
`dz/dw`; finite path substitution remains a separate obligation.

The supplied scaled root retains the original root channel and its prepared apart denominator. Exact coordinate powers
and quotient cancellation relate the same two finite differential programs, including the inverse-coordinate Jacobian
sign. -/
def coefficient_transport {genus : Nat} (differential : Differentials.Basic.Differential genus) (source : Gaussian)
    (nonzero : source ≠ 0) {parameter target : Gaussian}
    {original : CertifiedSquareRoot.Certificate parameter}
    (root : ScaledRoot original (factor genus source) target) :
    NamedEquivalent (coefficient differential source root).name
      (CoherentNamed.mul (Coherence.exact (-(source ^ 2)))
        (Value.differentialValue differential source original.value original.apart)).name := by
  let exponent := (HyperellipticReciprocal.reversedDifferential differential).exponent
  have reciprocal : NamedEquivalent (coefficient differential source root).name
      (CoherentNamed.div (Coherence.exact (-((source⁻¹) ^ exponent)))
        root.prepared.denominator root.prepared.apart).name := by
    have replace := (Congruence.coherentMul_respects (Coherence.exact (-1)) (Coherence.exact (-1)) _ _
      (NamedEquivalent.refl _)
      (differential_quotient (HyperellipticReciprocal.reversedDifferential differential) source⁻¹
        root.prepared.denominator root.prepared.apart)).trans
      (constant_mul_quotient (-1) ((source⁻¹) ^ exponent) root.prepared.denominator root.prepared.apart)
    have scalar : (-1 : Gaussian) * ((source⁻¹) ^ exponent) = -((source⁻¹) ^ exponent) := by ring1
    rw [scalar] at replace
    exact replace
  exact reciprocal.trans
    ((quotient_scaled original.value original.apart (factor genus source) _ _ root.prepared
      (numerator_identity differential source nonzero)).trans
      ((constant_mul_quotient (-(source ^ 2)) (source ^ differential.exponent) original.value original.apart).symm.trans
        (Congruence.coherentMul_respects (Coherence.exact (-(source ^ 2))) (Coherence.exact (-(source ^ 2))) _ _
          (NamedEquivalent.refl _)
          (differential_quotient differential source original.value original.apart).symm)))

end

/-- At each actual affine outer-boundary owner, both the reciprocal square equation and the coefficient transport are
obtained from curve data. No new root choice or caller differential identity is accepted. -/
def boundary_coefficient_transport {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Differentials.Basic.Differential genus) (source : Gaussian)
    (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) source)
    (owner : SquareRootContinuationChain.Owner (curve.polynomial.eval source)) :
    NamedEquivalent (coefficient differential source (ofBoundaryOwner curve source boundary owner)).name
      (CoherentNamed.mul (Coherence.exact (-(source ^ 2)))
        (Value.differentialValue differential source
          (owner.certificate owner.parameterNonzero).value
          (owner.certificate owner.parameterNonzero).apart)).name :=
  coefficient_transport differential source (PreparedExteriorReciprocal.boundary_nonzero boundary)
    (ofBoundaryOwner curve source boundary owner)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames in
/-- Reuse the cached point-query root of an actual integration edge. The point equality is the existing prepared-edge
parameterization theorem, not an assumed identification of two independently prepared paths. -/
def ofPreparedEdge {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    (prepared : PreparedConstantModels.PreparedEdge curve differential) (fraction : Coordinate)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) (nonzero : prepared.point fraction ≠ 0) :
    let original := PreparedModels.rootAtCached curve prepared.segment prepared.within
      prepared.left prepared.owner prepared.request prepared.cached prepared.ordered prepared.small fraction inside
    ScaledRoot original (factor genus (prepared.point fraction))
      ((HyperellipticReciprocal.polynomial curve).eval (prepared.point fraction)⁻¹) := by
  apply ScaledRoot.build _ _ (factor_nonzero genus nonzero)
  rw [PreparedSheetContinuation.pointAt_parameterAt
    prepared.segment prepared.within prepared.left prepared.request fraction]
  exact factor_identity curve (prepared.point fraction) nonzero

/-- The chart law for the exact coefficient program queried by the existing prepared integrator, with its cached root
source unchanged. -/
def prepared_coefficient_transport {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
    (prepared : PreparedConstantModels.PreparedEdge curve differential) (fraction : Coordinate)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) (nonzero : prepared.point fraction ≠ 0) :
    NamedEquivalent
      (coefficient differential (prepared.point fraction) (ofPreparedEdge prepared fraction inside nonzero)).name
      (CoherentNamed.mul (Coherence.exact (-(prepared.point fraction ^ 2))) (prepared.coefficient fraction inside)).name
        :=
  coefficient_transport differential (prepared.point fraction) nonzero (ofPreparedEdge prepared fraction inside nonzero)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
