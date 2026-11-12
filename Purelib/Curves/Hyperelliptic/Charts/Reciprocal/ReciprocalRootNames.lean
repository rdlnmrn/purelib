module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Semiring.Normalization
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Approximation.Gaussian.Division.Cancellation
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Readback
import Purelib.Approximation.Gaussian.Provenance.Power.Nonzero
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

open Purelib.Algebra.Field
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)

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
abbrev Gaussian := Basic.Canonical
/-- Exact rational parameters of original prepared edges. -/
abbrev Coordinate := Fraction.Rational
/-- A Gaussian name retaining its coherent approximation sequence. -/
abbrev CoherentNamed := Coherent.CoherentNamed
/-- Operational equivalence of retained Gaussian names. -/
abbrev NamedEquivalent := Gaussian.Equivalence.NamedEquivalent
/-- A retained quantitative certificate that the original Gaussian name is apart from zero. -/
abbrev Apart := Named.Apart
/-- A division-ready presentation equivalent to the original Gaussian name. -/
abbrev Prepared := Gaussian.Division.Prepared

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed (mul)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence (coherentMul_respects)
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws (coherentMul_assoc coherentMul_comm)
open Purelib.Riemann.RootContinuation.SquareRootProvenance (SquareIdentity)
open Purelib.Algebra.Quadratic.Pair.Polynomial (Expression)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Algebra.Quadratic
open Purelib.Algebra.Field
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
/-- The arithmetic expression whose root occurrence must be preserved. -/
def scaled (factor : Gaussian) (source : CoherentNamed) : CoherentNamed := mul (exact factor)
  source

/-- Transport the original sampled denominator lower bound through multiplication by a nonzero exact Gaussian factor.

The original sampled denominator lower bound is multiplied by the exact factor quadrance. The nonzero factor supplies
positivity, and each retained synchronized product sample satisfies the same computed bound. -/
def scaledPossibleApart (factor : Gaussian) (nonzero : factor ≠ 0)
    (source : CoherentNamed) (apart : Apart source.name) :
    Possible.PossibleApart
      (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation (exact factor).name
        source.name).toProcess where
  lowerSq := Norm.Basic.normSq factor * apart.certificate.lowerSq
  positive := Fraction.Order.Arithmetic.mul_pos_direct (Norm.Basic.normSq_pos nonzero)
    apart.certificate.positive
  lower := by
    intro state value possible
    rcases possible with ⟨later, _order, rfl⟩
    rw [Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation_sample]
    change Norm.Basic.normSq factor * apart.certificate.lowerSq ≤
      Norm.Basic.normSq (factor * (Sampling.approximation source.name).sample later)
    rw [Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Sampling.sampled_lower source apart later) (Norm.Basic.normSq_nonneg factor)

/-- Product samples inherit the displayed source lower bound. Apartification uses this direct certificate, without a
fresh square-root isolation or a search through the square-identity comparison tree.

The product approximation retains the original source samples and exact factor. Its transported lower certificate
prepares that same product channel, with explicit equivalence to the original coherent multiplication. -/
def prepareScaled (factor : Gaussian) (nonzero : factor ≠ 0)
    (source : CoherentNamed) (apart : Apart source.name) : Prepared (scaled factor source) :=
  let product := ofApproximation
    (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation (exact factor).name source.name)
  let lower := scaledPossibleApart factor nonzero source apart
  { denominator := product.apartify lower
    apart := ⟨Preparation.apartifyApart lower⟩
    equivalent := (Bridge.coherentMul_toNamed (exact factor) source).trans
      (product.apartifyEquivalent lower) }

/-- Operational multiplication transports the square identity; no rational reading is asserted to be an exact square
root. -/
def scaled_square {source : CoherentNamed} {parameter : Gaussian}
    (square : SquareIdentity source parameter) (factor : Gaussian) :
    SquareIdentity (scaled factor source) (factor * factor * parameter) :=
  (Laws.coherentMul_squares_interchange (exact factor) source).symm.trans
    ((coherentMul_respects (mul (exact factor) (exact factor))
      (exact (factor * factor))
      (mul source source) (exact parameter) (Exact.Arithmetic.exact_mul factor factor)
        square).trans
      (Exact.Arithmetic.exact_mul (factor * factor) parameter))

end

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames in
set_option genInjectivity false in
/-- A division-ready reciprocal root presentation of the original scaled root channel.

Its square identity uses the retained prepared denominator and exact target parameter. -/
structure ScaledRoot (source : CertifiedSquareRoot.Certificate parameter) (factor : Gaussian)
    (radicand : HyperellipticReciprocal.GaussianPolynomial) (point : Gaussian) where
  /-- The cached radicand value computed from the original parameter and coordinate factor. -/
  targetValue : Gaussian
  /-- The cached value retains the exact original source-factor equation. -/
  targetValue_eq : targetValue = factor * factor * parameter
  /-- The same cached value reads back the actual chart radicand at its retained coordinate. -/
  radicand_eq : targetValue = radicand.eval point
  /-- The retained division-ready presentation of the same scaled original root. -/
  prepared : Prepared (scaled factor source.value)
  /-- The retained square equation belongs to this actual radicand and coordinate. -/
  square : SquareIdentity prepared.denominator (radicand.eval point)
  /-- The cached exact inverse-root coefficients use this same prepared original root. -/
  algebraic : Expression.Denotation (Expression.inverseRoot radicand) point prepared.denominator
  /-- The original reciprocal program at the retained prepared denominator. -/
  inverse : CoherentNamed
  /-- The cached reciprocal uses the same original prepared root and apartness. -/
  inverse_eq : inverse = CoherentNamed.div (exact 1) prepared.denominator prepared.apart
  /-- The actual reciprocal realizes the same cached exact inverse-root coefficients. -/
  inverse_equivalent : NamedEquivalent inverse.name algebraic.channel.name

constructive_injectivity ScaledRoot

namespace ScaledRoot

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
/-- Prepare the original scaled root once and retain its actual chart radicand, inverse coefficients and reciprocal.

The radicand readback comes from the original source-factor equation. The
inverse pair uses that retained value, without reevaluating the chart table
or selecting a different root occurrence.
-/
def build (source : CertifiedSquareRoot.Certificate parameter) (factor : Gaussian) (nonzero : factor ≠ 0)
    (radicand : HyperellipticReciprocal.GaussianPolynomial) (point : Gaussian)
    (identity : factor * factor * parameter = radicand.eval point) : ScaledRoot source factor radicand point := by
  let target := factor * factor * parameter
  let prepared := prepareScaled factor nonzero source.value source.apart
  have square : SquareIdentity prepared.denominator (radicand.eval point) := by
    have scaledSquare : SquareIdentity (scaled factor source.value) (radicand.eval point) := by
      rewrite [← identity]
      exact scaled_square source.square factor
    exact (coherentMul_respects prepared.denominator (scaled factor source.value)
      prepared.denominator (scaled factor source.value) prepared.equivalent.symm prepared.equivalent.symm).trans
      scaledSquare
  have radicandNonzero := (PowerIdentity.ofSquare square).square_coefficient_nonzero prepared.apart
  have defined : (Expression.inverseRoot radicand).Defined point := by
    change (Polynomial.Dense.Power.power radicand 1).eval point ≠ 0
    rewrite [Polynomial.Dense.Power.eval_power, pow_one]
    exact radicandNonzero
  let expression := Expression.inverseRoot radicand
  let value : Pair Gaussian (-radicand.eval point) := ⟨0, target⁻¹⟩
  have valueEq : value = expression.evaluate point := by
    apply Pair.ext
    · change 0 = (0 : HyperellipticReciprocal.GaussianPolynomial).eval point / _
      rewrite [DensePolynomial.eval_zero, ExplicitField.zero_div]
      rfl
    · change target⁻¹ = (DensePolynomial.constant (1 : Gaussian)).eval point /
        (Polynomial.Dense.Power.power radicand 1).eval point
      rewrite [DensePolynomial.eval_constant, Polynomial.Dense.Power.eval_power, pow_one,
        ExplicitField.div_eq_mul_inv, Data.Gaussian.Basic.one_mul, ← identity]
      rfl
  let algebraic := Expression.retainValue expression point prepared.denominator defined
    (PowerIdentity.ofSquare square) value valueEq
  let inverse := CoherentNamed.div (exact 1) prepared.denominator prepared.apart
  exact ⟨target, rfl, identity, prepared, square, algebraic, inverse, rfl,
    algebraic.inverseRoot_reciprocal prepared.apart⟩

/-- Read the original cached prepared root and its square equation at the actual chart radicand. -/
def certificate (root : ScaledRoot source factor radicand point) :
    CertifiedSquareRoot.Certificate (radicand.eval point) :=
  ⟨root.prepared.denominator, root.prepared.apart, root.square⟩

set_option genInjectivity false in
/-- Exact reciprocal coefficients and the original guarded affine pullback at one retained scaled root.

The input root, scalar factor readback and both coefficient tables are cached.
The constructor derives the finite coefficient check and uses it to interpret
the original pullback with the same retained pair and channel.
-/
structure Coefficients (root : ScaledRoot source factor radicand point) (differential : Differential genus) where
  /-- The exact original scaled root retained by the coefficient construction. -/
  retainedRoot : ScaledRoot source factor radicand point
  /-- The retained root belongs to this original input. -/
  retainedRoot_eq : retainedRoot = root
  /-- The original inverse-coordinate denominator guard is retained. -/
  pointNonzero : point ≠ 0
  /-- The numerator scaling consumes the same cached original inverse-root pair. -/
  scaling : retainedRoot.algebraic.Scaling (HyperellipticReciprocal.numerator differential)
  /-- The cached original affine-pullback table, before coordinate-factor cancellation. -/
  pullback : Expression radicand
  /-- The retained pullback uses the exact original exponent and denominator. -/
  pullback_eq : pullback = HyperellipticReciprocal.pullbackExpression radicand differential
  /-- The two actual cached coefficient tables pass the finite cleared check. -/
  equal : pullback.Equal scaling.target.source
  /-- The original pullback is interpreted using the same cached pair and channel. -/
  pulled : Expression.Denotation pullback point retainedRoot.prepared.denominator
  /-- The pullback reuses the cached reduced pair instead of reevaluating its table. -/
  pulled_value_eq : pulled.value = scaling.target.value
  /-- The pullback retains that same cached numerical channel. -/
  pulled_channel_eq : pulled.channel = scaling.target.channel

constructive_injectivity Coefficients

namespace Coefficients

variable {parameter factor point : Gaussian} {source : CertifiedSquareRoot.Certificate parameter}
  {radicand : HyperellipticReciprocal.GaussianPolynomial} {root : ScaledRoot source factor radicand point}
  {genus : Nat} {differential : Differential genus}

/-- Construct one reciprocal coefficient from the original inverse pair and guarded finite pullback identity. -/
def build (root : ScaledRoot source factor radicand point) (differential : Differential genus)
    (pointNonzero : point ≠ 0) : Coefficients root differential := by
  let scaling := root.algebraic.scale (HyperellipticReciprocal.numerator differential)
  let pullback := HyperellipticReciprocal.pullbackExpression radicand differential
  have equal : pullback.Equal scaling.target.source := by
    rewrite [scaling.target.source_eq]
    exact HyperellipticReciprocal.pullback_equal radicand differential
  have radicandNonzero : radicand.eval point ≠ 0 := by
    have defined := root.algebraic.defined
    change (Polynomial.Dense.Power.power radicand 1).eval point ≠ 0 at defined
    rewrite [Polynomial.Dense.Power.eval_power, pow_one] at defined
    exact defined
  have originalDefined := HyperellipticReciprocal.defined_pullback radicand differential point
    pointNonzero radicandNonzero
  let pulled := scaling.target.reinterpret pullback equal originalDefined
  exact ⟨root, rfl, pointNonzero, scaling, pullback, rfl, equal, pulled, rfl, rfl⟩

/-- Read the original pullback at the same original prepared root, retaining the cached coefficients and channel. -/
def denotation (cache : Coefficients root differential) :
    Expression.Denotation cache.pullback point root.prepared.denominator :=
  Eq.ndrec (motive := fun target => Expression.Denotation cache.pullback point target.prepared.denominator)
    cache.pulled cache.retainedRoot_eq

end Coefficients

end ScaledRoot

/-- Inverting a nonzero Gaussian rational twice returns the original value. -/
private theorem inverse_inverse (source : Gaussian) (nonzero : source ≠ 0) : (source⁻¹)⁻¹ = source := by
  apply Field.mul_right_cancel_of_ne (ExplicitField.inv_ne_zero nonzero)
  calc
    _ = source⁻¹ * (source⁻¹)⁻¹ := Basic.mul_comm _ _
    _ = 1 := ExplicitField.mul_inv_cancel _ (ExplicitField.inv_ne_zero nonzero)
    _ = _ := (ExplicitField.mul_inv_cancel source nonzero).symm

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.PreparedModels (rootAtCached)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)

/-- The reciprocal root scale is the inverse original coordinate raised to genus plus one. -/
def factor (genus : Nat) (source : Gaussian) : Gaussian := (source⁻¹) ^ (genus + 1)

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
/-- A nonzero original coordinate gives a nonzero reciprocal root scale. -/
theorem factor_nonzero (genus : Nat) {source : Gaussian} (nonzero : source ≠ 0) : factor genus source ≠ 0 :=
  Power.pow_ne_zero_direct _ (ExplicitField.inv_ne_zero nonzero) _

/-- The squared reciprocal root scale transforms the original curve radicand to the reciprocal radicand. -/
theorem factor_identity {genus : Nat} (curve : HyperellipticCurve genus) (source : Gaussian)
  (nonzero : source ≠ 0) :
    factor genus source * factor genus source * curve.polynomial.eval source =
      (HyperellipticReciprocal.polynomial curve).eval source⁻¹ := by
  rw [HyperellipticReciprocal.polynomial_identity curve source⁻¹ (ExplicitField.inv_ne_zero nonzero),
    inverse_inverse source nonzero, factor, ← pow_add, show genus + 1 + (genus + 1) = 2 * genus + 2 by omega]

/-- Consume the original retained owner's existing operational certificate. The result is a division-ready reciprocal
root channel, not an independently numbered reciprocal root. -/
def ofOwner {genus : Nat} (curve : HyperellipticCurve genus) (source : Gaussian) (nonzero : source ≠
  0)
    (owner : SquareRootContinuationChain.Owner (curve.polynomial.eval source)) :
    ScaledRoot (owner.certificate owner.parameterNonzero) (factor genus source)
      (HyperellipticReciprocal.polynomial curve) source⁻¹ :=
  ScaledRoot.build (owner.certificate owner.parameterNonzero) (factor genus source) (factor_nonzero genus nonzero)
    (HyperellipticReciprocal.polynomial curve) source⁻¹ (factor_identity curve source nonzero)

/-- Scale the retained original boundary root owner into its division-ready reciprocal root channel. -/
def ofBoundaryOwner {genus : Nat} (curve : HyperellipticCurve genus) (source : Gaussian)
    (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) source)
    (owner : SquareRootContinuationChain.Owner (curve.polynomial.eval source)) :
    ScaledRoot (owner.certificate owner.parameterNonzero) (factor genus source)
      (HyperellipticReciprocal.polynomial curve) source⁻¹ :=
  ofOwner curve source (PreparedExteriorReciprocal.boundary_nonzero boundary) owner

/-- Multiplying a scaled original denominator by its quotient cancels that same denominator operationally.

The supplied denominator is apart from zero. Original synchronized quotient cancellation and product association
identify the retained product with the exact scaled numerator. -/
def scaled_mul_quotient (factor numerator : Gaussian) (denominator : CoherentNamed) (apart : Apart denominator.name) :
    NamedEquivalent (mul (scaled factor denominator)
      (div (exact numerator) denominator apart)).name
      (exact (factor * numerator)).name := by
  exact (coherentMul_assoc (exact factor) denominator
    (div (exact numerator) denominator apart)).trans
    ((coherentMul_respects (exact factor) (exact factor)
      (mul denominator (div (exact numerator) denominator apart)) (exact
        numerator)
      (NamedEquivalent.refl _)
      ((coherentMul_comm denominator (div (exact numerator) denominator apart)).trans
        (Cancellation.coherentDiv_mul_cancel (exact numerator) denominator apart))).trans
      (Exact.Arithmetic.exact_mul factor numerator))

/-- An exact numerator scaling identity identifies division by the prepared scaled denominator with division by the
original denominator.

The prepared denominator remains equivalent to the scaled original denominator, and the supplied exact numerator
identity aligns their quotients. Cancellation uses those same retained apartness certificates and quotient programs. -/
def quotient_scaled (source : CoherentNamed) (apart : Apart source.name)
    (factor first second : Gaussian) (prepared : Prepared (scaled factor source))
    (identity : factor * second = first) :
    NamedEquivalent
      (div (exact first) prepared.denominator prepared.apart).name
      (div (exact second) source apart).name := by
  let left := div (exact first) prepared.denominator prepared.apart
  let right := div (exact second) source apart
  have leftCancel : NamedEquivalent (mul prepared.denominator left).name (exact first).name :=
    (coherentMul_comm prepared.denominator left).trans
      (Cancellation.coherentDiv_mul_cancel (exact first) prepared.denominator prepared.apart)
  have rightCancel : NamedEquivalent (mul prepared.denominator right).name (exact first).name :=
    by
    have cancel := (coherentMul_respects prepared.denominator (scaled factor source)
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
      (mul (exact constant) (div (exact numerator) source apart)).name
      (div (exact (constant * numerator)) source apart).name := by
  let quotient := div (exact numerator) source apart
  let left := mul (exact constant) quotient
  let right := div (exact (constant * numerator)) source apart
  have leftCancel : NamedEquivalent (mul source left).name (exact (constant * numerator)).name
    :=
    (coherentMul_comm source left).trans
      ((coherentMul_assoc (exact constant) quotient source).trans
        ((coherentMul_respects (exact constant) (exact constant) (mul
          quotient source) (exact numerator)
          (NamedEquivalent.refl _) (Cancellation.coherentDiv_mul_cancel (exact numerator) source apart)).trans
          (Exact.Arithmetic.exact_mul constant numerator)))
  have rightCancel : NamedEquivalent (mul source right).name (exact (constant * numerator)).name
    :=
    (coherentMul_comm source right).trans
      (Cancellation.coherentDiv_mul_cancel (exact (constant * numerator)) source apart)
  exact Cancellation.coherentMul_cancel_left source left right apart
    (leftCancel.trans rightCancel.symm)

namespace ScaledRoot.Coefficients

variable {parameter factor point : Gaussian} {source : CertifiedSquareRoot.Certificate parameter}
  {radicand : HyperellipticReciprocal.GaussianPolynomial} {root : ScaledRoot source factor radicand point}
  {genus : Nat} {differential : Differential genus}

/-- The original guarded pullback channel agrees with the reciprocal of the same retained scaled root.

The comparison consumes the cached numerator value and inverse pair. The
finite pullback certificate has already identified the actual stored pair;
no chart table or root preparation is repeated here.
-/
def quotient_equivalent (cache : ScaledRoot.Coefficients root differential) :
    NamedEquivalent cache.denotation.channel.name
      (CoherentNamed.div (exact (-point ^ (HyperellipticReciprocal.reversedDifferential differential).exponent))
        root.prepared.denominator root.prepared.apart).name := by
  cases cache with
  | mk retainedRoot rootEq pointNonzero scaling pullback pullbackEq equal pulled valueEq channelEq =>
    cases rootEq
    change NamedEquivalent pulled.channel.name _
    rewrite [channelEq]
    have comparison := scaling.equivalent.symm
    rewrite [scaling.output_eq, scaling.retainedSource_eq] at comparison
    have inverse := coherentMul_respects (exact scaling.factorValue) (exact scaling.factorValue)
      root.algebraic.channel root.inverse (NamedEquivalent.refl _)
      root.inverse_equivalent.symm
    rewrite [root.inverse_eq] at inverse
    have quotient := constant_mul_quotient scaling.factorValue 1 root.prepared.denominator
      root.prepared.apart
    have result := comparison.trans (inverse.trans quotient)
    rewrite [Data.Gaussian.Basic.mul_one, scaling.factorValue_eq, scaling.retainedFactor_eq,
      HyperellipticReciprocal.numerator_eval] at result
    exact result

end ScaledRoot.Coefficients

/-- The finite named power of an exact Gaussian value is operationally equivalent to its exact scalar power.

The same coherent exact Gaussian value supplies every multiplication in the finite named power. Natural induction
identifies that program with the original scalar power at the same exponent. -/
def exact_power (point : Gaussian) (exponent : Nat) :
    NamedEquivalent (Power.namedPower (exact point) exponent).name
      (exact (point ^ exponent)).name := by
  induction exponent with
  | zero => exact NamedEquivalent.refl _
  | succ exponent inductionHypothesis =>
      exact (coherentMul_respects (Power.namedPower (exact point) exponent)
        (exact (point ^ exponent)) (exact point) (exact point) inductionHypothesis
        (NamedEquivalent.refl _)).trans
        (by
            simpa only [pow_succ, mul]
              using Exact.Arithmetic.exact_mul (point ^ exponent) point)

/-- The original differential value is operationally equivalent to its exact coordinate-power numerator divided by the
same retained root.

The supplied coherent root and its original apartness certificate are retained as the denominator. The finite named
coordinate power is compared with its exact scalar numerator through the original quotient congruence. -/
def differential_quotient {genus : Nat} (differential : Differential genus) (point : Gaussian)
    (source : CoherentNamed) (apart : Apart source.name) :
    NamedEquivalent (Value.differentialValue differential point source apart).name
      (div (exact (point ^ differential.exponent)) source apart).name :=
  Division.Equivalence.coherentDiv_respects
    (Power.namedPower (exact point) differential.exponent) (exact (point ^ differential.exponent))
    source source apart apart (exact_power point differential.exponent) (NamedEquivalent.refl _)

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
/-- The reciprocal root scale and inverse-coordinate Jacobian transform the original differential numerator to the
negative reversed-exponent numerator.

The differential exponent and genus satisfy the original finite balance equation. At a nonzero coordinate, inverse
powers cancel and leave the negative reversed-exponent numerator. -/
theorem numerator_identity {genus : Nat} (differential : Differential genus)
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
        rw [← Algebra.Semiring.Normalization.product_pow, ExplicitField.mul_inv_cancel source nonzero,
          one_pow, Basic.one_mul]
  calc
    _ = -(source ^ (differential.exponent + 2) * factor genus source) := by rw [pow_add]; ring1
    _ = _ := congrArg Neg.neg powers

/-- Read the already retained exact reciprocal coefficient at the original scaled root. -/
def coefficient {genus : Nat} {differential : Differential genus}
    {parameter factor point : Gaussian} {radicand : HyperellipticReciprocal.GaussianPolynomial}
    {original : CertifiedSquareRoot.Certificate parameter}
    {root : ScaledRoot original factor radicand point}
    (cache : ScaledRoot.Coefficients root differential) : CoherentNamed := cache.denotation.channel

/-- The cached guarded pullback realizes the original differential with the inverse-coordinate Jacobian.

The comparison consumes the finite coefficient check, cached numerator and
inverse-root pair at the same original prepared root. Quotient cancellation
then transports that program to the original affine differential.
-/
def coefficient_transport {genus : Nat} (differential : Differential genus) (source : Gaussian)
    (nonzero : source ≠ 0) {parameter : Gaussian} {radicand : HyperellipticReciprocal.GaussianPolynomial}
    {original : CertifiedSquareRoot.Certificate parameter}
    {root : ScaledRoot original (factor genus source) radicand source⁻¹}
    (cache : ScaledRoot.Coefficients root differential) :
    NamedEquivalent (coefficient cache).name
      (mul (exact (-(source ^ 2)))
        (Value.differentialValue differential source original.value original.apart)).name :=
  cache.quotient_equivalent.trans
    ((quotient_scaled original.value original.apart (factor genus source) _ _ root.prepared
      (numerator_identity differential source nonzero)).trans
      ((constant_mul_quotient (-(source ^ 2)) (source ^ differential.exponent) original.value original.apart).symm.trans
        (coherentMul_respects (exact (-(source ^ 2))) (exact (-(source ^ 2))) _ _
          (NamedEquivalent.refl _)
          (differential_quotient differential source original.value original.apart).symm)))

end

/-- At each actual affine outer-boundary owner, both the reciprocal square equation and the coefficient transport are
obtained from curve data. No new root choice or caller differential identity is accepted. -/
def boundary_coefficient_transport {genus : Nat} (curve : HyperellipticCurve genus)
    (differential : Differential genus) (source : Gaussian)
    (boundary : Boundary.OnBoxBoundary (Cuts.Ambient curve) source)
    (owner : SquareRootContinuationChain.Owner (curve.polynomial.eval source))
    (cache : ScaledRoot.Coefficients (ofBoundaryOwner curve source boundary owner) differential) :
    NamedEquivalent (coefficient cache).name
      (mul (exact (-(source ^ 2)))
        (Value.differentialValue differential source
          (owner.certificate owner.parameterNonzero).value
          (owner.certificate owner.parameterNonzero).apart)).name :=
  coefficient_transport differential source (PreparedExteriorReciprocal.boundary_nonzero boundary) cache

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames in
/-- Reuse the cached point-query root of an actual integration edge. The point equality is the existing prepared-edge
parameterization theorem, not an assumed identification of two independently prepared paths. -/
def ofPreparedEdge {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) (nonzero : prepared.point fraction ≠ 0) :
    let original := rootAtCached curve prepared.segment prepared.within
      prepared.left prepared.owner prepared.request prepared.cached prepared.ordered prepared.small fraction inside
    ScaledRoot original (factor genus (prepared.point fraction))
      (HyperellipticReciprocal.polynomial curve) (prepared.point fraction)⁻¹ := by
  apply ScaledRoot.build _ _ (factor_nonzero genus nonzero)
  rw [PreparedSheetContinuation.pointAt_parameterAt
    prepared.segment prepared.within prepared.left prepared.request fraction]
  exact factor_identity curve (prepared.point fraction) nonzero

/-- The chart law for the exact coefficient program queried by the existing prepared integrator, with its cached root
source unchanged. -/
def prepared_coefficient_transport {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) (nonzero : prepared.point fraction ≠ 0)
    (cache : ScaledRoot.Coefficients (ofPreparedEdge prepared fraction inside nonzero) differential) :
    NamedEquivalent (coefficient cache).name
      (mul (exact (-(prepared.point fraction ^ 2))) (prepared.coefficient fraction inside)).name :=
  coefficient_transport differential (prepared.point fraction) nonzero cache

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames

end

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames.ScaledRoot

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)

/-- The exact factor of a retained division-ready scaled root is nonzero.

The actual square and denominator apartness make the cached target
nonzero. Its two original scalar readbacks then exclude a zero factor;
no constructor or root occurrence is reconstructed.
-/
theorem factor_nonzero {parameter factor point : Gaussian}
    {source : CertifiedSquareRoot.Certificate parameter}
    {radicand : HyperellipticReciprocal.GaussianPolynomial}
    (root : ScaledRoot source factor radicand point) : factor ≠ 0 := by
  intro zero
  have nonzero := (PowerIdentity.ofSquare root.square).square_coefficient_nonzero root.prepared.apart
  apply nonzero
  calc
    radicand.eval point = root.targetValue := root.radicand_eq.symm
    _ = factor * factor * parameter := root.targetValue_eq
    _ = 0 := by
      rewrite [zero, Data.Gaussian.Basic.zero_mul, Data.Gaussian.Basic.zero_mul]
      rfl

/-- Scale the supplied original reciprocal root into its guarded affine chart presentation.

The same reciprocal polynomial identity certifies the target at `1/w`.
Both numerical clients consume this one original scaled-root construction;
its input certificate and nonzero coordinate remain exact retained indices.
-/
def affine {genus : Nat} {curve : HyperellipticCurve genus} {point : Gaussian}
    (source : CertifiedSquareRoot.Certificate ((HyperellipticReciprocal.polynomial curve).eval point))
    (nonzero : point ≠ 0) :
    ScaledRoot source ((point⁻¹) ^ (genus + 1)) curve.polynomial point⁻¹ := by
  have inverseNonzero := Algebra.Field.ExplicitField.inv_ne_zero nonzero
  have factorNonzero := Algebra.Field.ExplicitField.pow_ne_zero_of_ne_zero inverseNonzero (genus + 1)
  have identity : (point⁻¹) ^ (genus + 1) * (point⁻¹) ^ (genus + 1) *
      (HyperellipticReciprocal.polynomial curve).eval point = curve.polynomial.eval point⁻¹ := by
    rewrite [HyperellipticReciprocal.polynomial_identity curve point nonzero,
      ← pow_add, show genus + 1 + (genus + 1) = 2 * genus + 2 by omega0]
    calc
      _ = ((point⁻¹) ^ (2 * genus + 2) * point ^ (2 * genus + 2)) *
          curve.polynomial.eval point⁻¹ := by ring1
      _ = (point⁻¹ * point) ^ (2 * genus + 2) * curve.polynomial.eval point⁻¹ := by
        rewrite [Algebra.Semiring.Normalization.product_pow]
        rfl
      _ = _ := by
        rewrite [Data.Gaussian.Basic.Canonical.inv_mul_cancel point nonzero, one_pow, Data.Gaussian.Basic.one_mul]
        rfl
  exact ReciprocalRootNames.ScaledRoot.build source ((point⁻¹) ^ (genus + 1)) factorNonzero
    curve.polynomial point⁻¹ identity

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames.ScaledRoot

end
