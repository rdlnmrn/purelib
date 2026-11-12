module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Primitives
public import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Scaling
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.DifferentialTransport.Numerator
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Polynomial.Dense.Power
import Purelib.Tactic.Ring

/-! # The weighted coefficient at the actual reciprocal w and retained regular root

The formal denominator is w times the regular-root parameter. Its generator
is the same signed regular root already used by the original quotient t.
The exact second-kind slope and polynomial remainder split the coefficient
at w; no rational reading is identified with t and no cycle integral is
assumed to vanish.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Regular

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- The full regular-root expression -2/(w*r), retaining the original reciprocal coordinate denominator. -/
@[expose] def weighted (parameter : Canonical) : Expression (regularAt parameter) :=
  Expression.scaleFraction (constant (-2)) coordinate (Expression.inverseRoot (regularAt parameter))

/-- The exact slope coefficient (-1+λw²)/(w*r), expressed at w without differentiating with respect to w. -/
def slope (parameter : Canonical) : Expression (regularAt parameter) :=
  Expression.scaleFraction ((Power.power coordinate 2).scale parameter - constant 1) coordinate
    (Expression.inverseRoot (regularAt parameter))

/-- The slope retains its complete original full numerator and coordinate divisor. -/
private theorem packaged_slope_eq (parameter : Canonical) :
    slope parameter = Expression.scaleFraction ((Power.power coordinate 2).scale parameter - constant 1) coordinate
      (Expression.inverseRoot (regularAt parameter)) := by rfl

/-- The slope retains its complete original full numerator and coordinate divisor. -/
theorem slope_eq (parameter : Canonical) :
    slope parameter = Expression.scaleFraction ((Power.power coordinate 2).scale parameter - constant 1) coordinate
      (Expression.inverseRoot (regularAt parameter)) := packaged_slope_eq parameter

/-- The same full polynomial numerator -2λw is the actual regular second-kind remainder. -/
def remainder (parameter : Canonical) : Expression (regularAt parameter) :=
  Expression.scale (remainderNumerator parameter) (Expression.inverseRoot (regularAt parameter))

/-- The full coefficient after the finite regular-w split into twice the slope and the actual polynomial remainder. -/
def reduced (parameter : Canonical) : Expression (regularAt parameter) :=
  (Expression.scale (constant 2) (slope parameter)).add (remainder parameter)

/-- Both denominator-cleared coefficient tables satisfy the exact regular-w second-kind split. -/
private theorem packaged_reduction (parameter : Canonical) : (weighted parameter).Equal (reduced parameter) := by
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [-eq_self, -iff_self, weighted, reduced, slope, remainder,
      Expression.scaleFraction, Expression.scale, Expression.add, Expression.inverseRoot,
      Expression.oddReciprocal, Algebra.Quadratic.Pair.scale, Algebra.Quadratic.Pair.add_re,
      eval_mul, eval_add, eval_sub, eval_scale, eval_zero, eval_constant, Power.eval_power]
    ring1
  · intro point
    simp only [-eq_self, -iff_self, weighted, reduced, slope, remainder,
      Expression.scaleFraction, Expression.scale, Expression.add, Expression.inverseRoot,
      Expression.oddReciprocal, Algebra.Quadratic.Pair.scale, Algebra.Quadratic.Pair.add_im,
      eval_mul, eval_add, eval_sub, eval_scale, eval_constant, Power.eval_power,
      coordinate_eval, remainderNumerator_eval]
    ring1

/-- Both denominator-cleared coefficient tables satisfy the exact regular-w second-kind split. -/
theorem reduction (parameter : Canonical) : (weighted parameter).Equal (reduced parameter) :=
  packaged_reduction parameter

/-- The actual model polynomial reads the regular reversed cubic at the same retained reciprocal coordinate. -/
private theorem packaged_polynomial_eq {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    (cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar) (point : Canonical) :
    cap.polynomial.eval point = (regularAt parameter).eval point :=
  (congrArg (fun polynomial : Coefficients => polynomial.eval point) cap.polynomial_eq).trans
    ((congrArg (fun polynomial : Coefficients => (Gaussian.Reciprocal.reversed polynomial).eval point)
      (Fibre.frameCurve_polynomial frame)).trans (original_regular_eval parameter point))

/-- The actual model polynomial reads the regular reversed cubic at the same retained reciprocal coordinate. -/
theorem polynomial_eq {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    (cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar) (point : Canonical) :
    cap.polynomial.eval point = (regularAt parameter).eval point :=
  packaged_polynomial_eq (parameter := parameter) (frame := frame) cap point

/-- Retain the inverse-root coefficients at w using the same original regular-root certificate.

The original polynomial equality changes only the exact square parameter.
Its actual channel, apartness, source observations and signed root owner
remain unchanged; no root or denominator observation is acquired.
-/
def inverse {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    (overlap : Cap.RootCoordinates.Overlap cap point owner) :
    Expression.Denotation (Expression.inverseRoot (regularAt parameter)) point overlap.regularRoot.value := by
  have original := polynomial_eq (parameter := parameter) (frame := frame) cap point
  have nonzero : (regularAt parameter).eval point ≠ 0 := fun zero =>
    Riemann.RootContinuation.SquareRootChannelOwnership.parameter_nonzero overlap.regularRoot (original.trans zero)
  have defined : (Expression.inverseRoot (regularAt parameter)).Defined point := by
    change (Power.power (regularAt parameter) 1).eval point ≠ 0
    rewrite [Power.eval_power, pow_one]
    exact nonzero
  have identity : PowerIdentity overlap.regularRoot.value 2 ((regularAt parameter).eval point) :=
    NamedEquivalent.transport rfl (congrArg (fun value => (Coherence.exact value).name) original)
      (PowerIdentity.ofSquare overlap.regularRoot.square)
  exact Expression.retain (Expression.inverseRoot (regularAt parameter)) point
    overlap.regularRoot.value defined identity

/-- The reduced expression retains genuine denominator guards at the same actual point. -/
private theorem packaged_reduced_defined {parameter point : Canonical}
    (defined : (weighted parameter).Defined point) : (reduced parameter).Defined point := by
  have product : point * (regularAt parameter).eval point ≠ 0 := by
    change (coordinate * Power.power (regularAt parameter) (0 + 1)).eval point ≠ 0 at defined
    rewrite [eval_mul, Power.eval_power, pow_one, coordinate_eval] at defined
    exact defined
  have pointNonzero : point ≠ 0 := by
    intro zero
    exact product (by rewrite [zero]; ring1)
  have rootNonzero : (regularAt parameter).eval point ≠ 0 := by
    intro zero
    exact product (by rewrite [zero]; ring1)
  have rootDefined : (Expression.inverseRoot (regularAt parameter)).Defined point := by
    change (Power.power (regularAt parameter) (0 + 1)).eval point ≠ 0
    rewrite [Power.eval_power, pow_one]
    exact rootNonzero
  have coordinateNonzero : coordinate.eval point ≠ 0 := fun zero =>
    pointNonzero ((coordinate_eval point).symm.trans zero)
  have slopeDefined := Expression.defined_scaleFraction
    ((Power.power coordinate 2).scale parameter - constant 1) coordinate
    (Expression.inverseRoot (regularAt parameter)) point rootDefined coordinateNonzero
  exact Expression.defined_add _ _ point
    (Expression.defined_scale (constant 2) (slope parameter) point slopeDefined)
    (Expression.defined_scale (remainderNumerator parameter) (Expression.inverseRoot (regularAt parameter))
      point rootDefined)

/-- The reduced expression retains genuine denominator guards at the same actual point. -/
theorem reduced_defined {parameter point : Canonical}
    (defined : (weighted parameter).Defined point) : (reduced parameter).Defined point :=
  packaged_reduced_defined defined

/-- Reuse the same complete coefficients and actual channel for the internally derived regular-w split. -/
def reduce {parameter point : Canonical} {generator : CoherentNamed}
    (source : Expression.Denotation (weighted parameter) point generator) :
    Expression.Denotation (reduced parameter) point generator :=
  source.reinterpret (reduced parameter)
    (by rewrite [source.source_eq]; exact (reduction parameter).symm) (reduced_defined source.defined)

/-- The coefficient reduction retains the same cached divided pair. -/
private theorem packaged_reduce_value {parameter point : Canonical} {generator : CoherentNamed}
    (source : Expression.Denotation (weighted parameter) point generator) :
    (reduce source).value = source.value := by rfl

/-- The coefficient reduction retains the same cached divided pair. -/
theorem reduce_value {parameter point : Canonical} {generator : CoherentNamed}
    (source : Expression.Denotation (weighted parameter) point generator) :
    (reduce source).value = source.value := packaged_reduce_value source

/-- The coefficient reduction retains the same original channel. -/
private theorem packaged_reduce_channel {parameter point : Canonical} {generator : CoherentNamed}
    (source : Expression.Denotation (weighted parameter) point generator) :
    (reduce source).channel = source.channel := by rfl

/-- The coefficient reduction retains the same original channel. -/
theorem reduce_channel {parameter point : Canonical} {generator : CoherentNamed}
    (source : Expression.Denotation (weighted parameter) point generator) :
    (reduce source).channel = source.channel := packaged_reduce_channel source

/-- Retain the same inverse-root source, original Scaling cache and full fractional target.

The exact scaling factor is computed at the actual reciprocal coordinate.
The complete polynomial numerator and divisor remain in the target's source;
its divided pair and channel are those of the same original Scaling target.
-/
@[expose] def Weighted {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    (overlap : Cap.RootCoordinates.Overlap cap point owner) : Type _ :=
  (base : Expression.Denotation (Expression.inverseRoot (regularAt parameter)) point overlap.regularRoot.value) ×
  (scaled : base.Scaling (constant ((constant (-2)).eval point / coordinate.eval point))) ×
  { target : Expression.Denotation (weighted parameter) point overlap.regularRoot.value //
    target.value = scaled.target.value ∧ target.channel = scaled.target.channel }

/-- Construct the coefficient -2/(w*r) using the actual retained reciprocal coordinate and regular root.

The inverse-root readback is retained once; the existing Scaling operation
then computes its actual quotient factor, pair and channel. No new root,
reciprocal preparation or denominator observation is acquired.
-/
def build {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    (overlap : Cap.RootCoordinates.Overlap cap point owner) : Weighted overlap := by
  let base := inverse (parameter := parameter) (frame := frame) overlap
  have nonzero : coordinate.eval point ≠ 0 := fun zero =>
    overlap.point_nonzero (frame_originOrder frame) ((coordinate_eval point).symm.trans zero)
  let fraction := base.scaleFraction (constant (-2)) coordinate nonzero
  exact ⟨base, fraction⟩

/-- The regular coefficient builder retains its whole original inverse and fractional-scaling factory value. -/
private theorem packaged_build_factory {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    (overlap : Cap.RootCoordinates.Overlap cap point owner) :
    build (parameter := parameter) (frame := frame) overlap =
(
  by
    let base := inverse (parameter := parameter) (frame := frame) overlap
    have nonzero : coordinate.eval point ≠ 0 := fun zero =>
      overlap.point_nonzero (frame_originOrder frame) ((coordinate_eval point).symm.trans zero)
    let fraction := base.scaleFraction (constant (-2)) coordinate nonzero
    exact ⟨base, fraction⟩
  : Weighted overlap) := by rfl

/-- The regular coefficient builder retains its whole original inverse and fractional-scaling factory value. -/
theorem build_factory {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    (overlap : Cap.RootCoordinates.Overlap cap point owner) :
    build (parameter := parameter) (frame := frame) overlap =
(
  by
    let base := inverse (parameter := parameter) (frame := frame) overlap
    have nonzero : coordinate.eval point ≠ 0 := fun zero =>
      overlap.point_nonzero (frame_originOrder frame) ((coordinate_eval point).symm.trans zero)
    let fraction := base.scaleFraction (constant (-2)) coordinate nonzero
    exact ⟨base, fraction⟩
  : Weighted overlap) := packaged_build_factory (parameter := parameter) (frame := frame) overlap

/-- The actual original weighted pullback compares to the same retained fractional coefficient cache.

The original quotient transport uses both original root certificates and the
same operational t. Exact scalar association and the original Scaling
comparison supply the regular-w coefficient; no sample or name comparison
is supplied as an additional premise.
-/
def compare {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    (overlap : Cap.RootCoordinates.Overlap cap point owner) (retained : Weighted overlap) :
    NamedEquivalent
      (mul (mul (Coherence.exact 2) overlap.coordinate.prepared.denominator)
        (mul (Coherence.exact (-1))
          (div (Coherence.exact point⁻¹) overlap.reciprocal.value overlap.reciprocal.apart))).name
      retained.2.2.val.channel.name := by
  have factor : (constant (-2)).eval point / coordinate.eval point = -2 * point⁻¹ := by
    rewrite [eval_constant, coordinate_eval, ExplicitField.div_eq_mul_inv]
    rfl
  have factorValue : retained.2.1.factorValue = -2 * point⁻¹ :=
    retained.2.1.factorValue_eq.trans
      ((congrArg (fun polynomial : Coefficients => polynomial.eval point)
        retained.2.1.retainedFactor_eq).trans
        ((eval_constant _ point).trans factor))
  have inputChannel : retained.2.1.retainedSource.channel = retained.1.channel :=
    congrArg (fun source : Expression.Denotation (Expression.inverseRoot (regularAt parameter))
      point overlap.regularRoot.value => source.channel) retained.2.1.retainedSource_eq
  have output : retained.2.1.output = mul (Coherence.exact (-2 * point⁻¹)) retained.1.channel :=
    retained.2.1.output_eq.trans
      (congrArg₂ mul (congrArg Coherence.exact factorValue) inputChannel)
  have move : NamedEquivalent
      (mul (Coherence.exact (-2 * point⁻¹))
        (div (Coherence.exact 1) overlap.regularRoot.value overlap.regularRoot.apart)).name
      (div (Coherence.exact (-2 * point⁻¹)) overlap.regularRoot.value overlap.regularRoot.apart).name :=
    NamedEquivalent.transport rfl
      (congrArg (fun scalar : Canonical =>
        (div (Coherence.exact scalar) overlap.regularRoot.value overlap.regularRoot.apart).name)
        (Basic.mul_one (-2 * point⁻¹)))
      (ReciprocalRootNames.constant_mul_quotient (-2 * point⁻¹) 1
        overlap.regularRoot.value overlap.regularRoot.apart)
  have scaled : NamedEquivalent
      (mul (Coherence.exact (-2 * point⁻¹))
        (div (Coherence.exact 1) overlap.regularRoot.value overlap.regularRoot.apart)).name
      retained.2.1.output.name :=
    NamedEquivalent.transport rfl (congrArg CoherentNamed.name output.symm)
      (Congruence.coherentMul_respects
        (Coherence.exact (-2 * point⁻¹)) (Coherence.exact (-2 * point⁻¹))
        (div (Coherence.exact 1) overlap.regularRoot.value overlap.regularRoot.apart)
        retained.1.channel (NamedEquivalent.refl _)
        (retained.1.inverseRoot_reciprocal overlap.regularRoot.apart))
  exact overlap.coordinateTransport.trans
    ((ReciprocalRootNames.constant_mul_quotient (-2) point⁻¹
      overlap.regularRoot.value overlap.regularRoot.apart).trans
      (move.symm.trans (scaled.trans
        (retained.1.scaleFraction_equivalent (constant (-2)) coordinate retained.2))))

/-- Construct the actual weighted coefficient and its finite regular-w split from the same whole caches.

The returned comparison concerns the original operational quotient, with its
actual t and root observations. The split reuses the computed divided pair
and channel; it does not yet integrate or cancel the potential r/t along an
oriented path.
-/
def ofOverlap {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    (overlap : Cap.RootCoordinates.Overlap cap point owner) :
    (retained : Weighted overlap) ×
    (target : { value : Expression.Denotation (reduced parameter) point overlap.regularRoot.value //
      value = reduce retained.2.2.val }) ×
    NamedEquivalent
      (mul (mul (Coherence.exact 2) overlap.coordinate.prepared.denominator)
        (mul (Coherence.exact (-1))
          (div (Coherence.exact point⁻¹) overlap.reciprocal.value overlap.reciprocal.apart))).name
      target.val.channel.name := by
  let retained := build (parameter := parameter) (frame := frame) overlap
  let target := reduce retained.2.2.val
  let equivalent := NamedEquivalent.transport rfl
    (congrArg CoherentNamed.name (reduce_channel retained.2.2.val).symm)
    (compare (parameter := parameter) (frame := frame) overlap retained)
  exact ⟨retained, ⟨target, rfl⟩, equivalent⟩

/-- The actual overlap comparison retains the complete one-build and one-reduction factory value. -/
private theorem packaged_ofOverlap_factory {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    (overlap : Cap.RootCoordinates.Overlap cap point owner) :
    ofOverlap (parameter := parameter) (frame := frame) overlap =
(
  by
    let retained := build (parameter := parameter) (frame := frame) overlap
    let target := reduce retained.2.2.val
    let equivalent := NamedEquivalent.transport rfl
      (congrArg CoherentNamed.name (reduce_channel retained.2.2.val).symm)
      (compare (parameter := parameter) (frame := frame) overlap retained)
    exact ⟨retained, ⟨target, rfl⟩, equivalent⟩
  : (retained : Weighted overlap) ×
    (target : { value : Expression.Denotation (reduced parameter) point overlap.regularRoot.value //
      value = reduce retained.2.2.val }) ×
    NamedEquivalent
      (mul (mul (Coherence.exact 2) overlap.coordinate.prepared.denominator)
        (mul (Coherence.exact (-1))
          (div (Coherence.exact point⁻¹) overlap.reciprocal.value overlap.reciprocal.apart))).name
      target.val.channel.name) := by rfl

/-- The actual overlap comparison retains the complete one-build and one-reduction factory value. -/
theorem ofOverlap_factory {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    (overlap : Cap.RootCoordinates.Overlap cap point owner) :
    ofOverlap (parameter := parameter) (frame := frame) overlap =
(
  by
    let retained := build (parameter := parameter) (frame := frame) overlap
    let target := reduce retained.2.2.val
    let equivalent := NamedEquivalent.transport rfl
      (congrArg CoherentNamed.name (reduce_channel retained.2.2.val).symm)
      (compare (parameter := parameter) (frame := frame) overlap retained)
    exact ⟨retained, ⟨target, rfl⟩, equivalent⟩
  : (retained : Weighted overlap) ×
    (target : { value : Expression.Denotation (reduced parameter) point overlap.regularRoot.value //
      value = reduce retained.2.2.val }) ×
    NamedEquivalent
      (mul (mul (Coherence.exact 2) overlap.coordinate.prepared.denominator)
        (mul (Coherence.exact (-1))
          (div (Coherence.exact point⁻¹) overlap.reciprocal.value overlap.reciprocal.apart))).name
      target.val.channel.name) := packaged_ofOverlap_factory (parameter := parameter) (frame := frame) overlap

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Regular

end
