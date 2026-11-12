module

public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Regular
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Potential
import Purelib.Curves.Legendre.Polynomial.Reciprocal
import Purelib.Curves.Legendre.Polynomial.Reciprocal.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Algebra.Quadratic.Pair.Gaussian
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Scaling
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Dense.Power
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Arithmetic.Mul
import Purelib.Approximation.Gaussian.Division.Cancellation
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Exact.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Derivative
import Purelib.Tactic.Ring

/-! # The actual ramified endpoint potential and its finite coefficient

The actual quotient r/t is compared to t F(w), where F(w)=r/w and the
original prepared channel t squares operationally to w. The finite
coefficient F+2wF' is computed in the original regular quadratic expression
and compared to its exact slope. This is a finite coefficient identity, not
an assertion that a rational sample of t is its exact operational value.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential

open Purelib.Algebra.Quadratic

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Approximation.Gaussian.Arithmetic
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- The full regular expression r/w whose actual ramified endpoint is t times this factor. -/
def factor (parameter : Canonical) : Expression (regularAt parameter) :=
  ⟨⟨0, constant 1⟩, coordinate⟩

/-- The original finite chain coefficient of t F(t²), represented at the actual regular coordinate w. -/
def derivative (parameter : Canonical) : Expression (regularAt parameter) :=
  (factor parameter).add (Expression.scale (coordinate.scale 2) (factor parameter).derivative)

/-- Multiplying the same inverse-root expression by its full regular polynomial over w gives r/w. -/
private theorem packaged_factor_fraction (parameter : Canonical) :
    (factor parameter).Equal
      (Expression.scaleFraction (regularAt parameter) coordinate
        (Expression.inverseRoot (regularAt parameter))) := by
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [-eq_self, -iff_self, factor, Expression.scaleFraction, Expression.inverseRoot,
      Expression.oddReciprocal, Algebra.Quadratic.Pair.scale, eval_mul, eval_zero,
      Power.eval_power]
    ring1
  · intro point
    simp only [-eq_self, -iff_self, factor, Expression.scaleFraction, Expression.inverseRoot,
      Expression.oddReciprocal, Algebra.Quadratic.Pair.scale, eval_mul, eval_constant,
      Power.eval_power]
    ring1

/-- Multiplying the same inverse-root expression by its full regular polynomial over w gives r/w. -/
theorem factor_fraction (parameter : Canonical) :
    (factor parameter).Equal
      (Expression.scaleFraction (regularAt parameter) coordinate
        (Expression.inverseRoot (regularAt parameter))) := packaged_factor_fraction parameter

/-- The finite ramified chain coefficient is the original regular-w slope (-1+λw²)/(w*r). -/
private theorem packaged_derivative_eq (parameter : Canonical) :
    (derivative parameter).Equal (Regular.slope parameter) := by
  rewrite [Regular.slope_eq]
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [-eq_self, -iff_self, derivative, factor,
      Expression.derivative, Expression.directionalDerivative, Expression.add, Expression.scale,
      Expression.scaleFraction, Expression.inverseRoot, Expression.oddReciprocal,
      Algebra.Quadratic.Pair.scale, Algebra.Quadratic.Pair.add_re,
      eval_add, eval_mul, eval_sub, eval_scale, eval_zero, eval_constant, Power.eval_power,
      Power.eval_derivative_zero]
    ring1
  · intro point
    simp only [-eq_self, -iff_self, derivative, factor,
      Expression.derivative, Expression.directionalDerivative, Expression.add, Expression.scale,
      Expression.scaleFraction, Expression.inverseRoot, Expression.oddReciprocal,
      Algebra.Quadratic.Pair.scale, Algebra.Quadratic.Pair.add_im,
      eval_mul, eval_add, eval_sub, eval_scale, eval_constant, Power.eval_power,
      Power.eval_derivative_constant, coordinate_eval, coordinate_derivative_eval,
      regularAt_eval, regularAt_derivative_eval]
    ring1

/-- The finite ramified chain coefficient is the original regular-w slope (-1+λw²)/(w*r). -/
theorem derivative_eq (parameter : Canonical) :
    (derivative parameter).Equal (Regular.slope parameter) := packaged_derivative_eq parameter

/-- The same factor has a genuine denominator guard at a nonzero actual reciprocal coordinate. -/
private theorem packaged_factor_defined {parameter point : Canonical} (nonzero : point ≠ 0) :
    (factor parameter).Defined point := by
  change coordinate.eval point ≠ 0
  exact fun zero => nonzero ((coordinate_eval point).symm.trans zero)

/-- The same factor has a genuine denominator guard at a nonzero actual reciprocal coordinate. -/
theorem factor_defined {parameter point : Canonical} (nonzero : point ≠ 0) :
    (factor parameter).Defined point := packaged_factor_defined nonzero

/-- The finite pullback coefficient keeps precisely the factor and regular-root domain guards. -/
private theorem packaged_derivative_defined {parameter point : Canonical}
    (defined : (factor parameter).Defined point) (regular : (regularAt parameter).eval point ≠ 0) :
    (derivative parameter).Defined point :=
  Expression.defined_add _ _ point defined
    (Expression.defined_scale (coordinate.scale 2) (factor parameter).derivative point
      (Expression.defined_derivative (factor parameter) point defined regular))

/-- The finite pullback coefficient keeps precisely the factor and regular-root domain guards. -/
theorem derivative_defined {parameter point : Canonical}
    (defined : (factor parameter).Defined point) (regular : (regularAt parameter).eval point ≠ 0) :
    (derivative parameter).Defined point := packaged_derivative_defined defined regular

/-- The complete finite pullback coefficient evaluates to the original pair sum on its genuine domain. -/
private theorem packaged_derivative_evaluate {parameter point : Canonical}
    (defined : (factor parameter).Defined point) (regular : (regularAt parameter).eval point ≠ 0) :
    (derivative parameter).evaluate point = (factor parameter).evaluate point +
      ((factor parameter).derivative.scale (coordinate.scale 2)).evaluate point :=
  Expression.evaluate_add _ _ point defined
    (Expression.defined_scale (coordinate.scale 2) (factor parameter).derivative point
      (Expression.defined_derivative (factor parameter) point defined regular))

/-- The complete finite pullback coefficient evaluates to the original pair sum on its genuine domain. -/
theorem derivative_evaluate {parameter point : Canonical}
    (defined : (factor parameter).Defined point) (regular : (regularAt parameter).eval point ≠ 0) :
    (derivative parameter).evaluate point = (factor parameter).evaluate point +
      ((factor parameter).derivative.scale (coordinate.scale 2)).evaluate point :=
  packaged_derivative_evaluate defined regular

/-- A factor readback uses the original generator scaled by the exact reciprocal of w. -/
def factor_channel {parameter point : Canonical} {generator : CoherentNamed}
    (retained : Expression.Denotation (factor parameter) point generator) :
    NamedEquivalent retained.channel.name (mul (Coherence.exact point⁻¹) generator).name := by
  have pair : retained.value = ⟨0, point⁻¹⟩ := retained.value_eq.trans (by
    apply Algebra.Quadratic.Pair.ext
    · change (0 : Coefficients).eval point / coordinate.eval point = 0
      rewrite [eval_zero, ExplicitField.zero_div]
      rfl
    · change (constant 1).eval point / coordinate.eval point = point⁻¹
      rewrite [eval_constant, coordinate_eval, ExplicitField.div_eq_mul_inv]
      exact Basic.one_mul _)
  have interpreted : Pair.Gaussian.denote id generator retained.value =
      Pair.Gaussian.denote id generator
        (⟨0, point⁻¹⟩ : Algebra.Quadratic.Pair Canonical (-((regularAt parameter).eval point))) :=
    congrArg (fun original : Algebra.Quadratic.Pair Canonical (-((regularAt parameter).eval point)) =>
      Pair.Gaussian.denote id generator original) pair
  have reduced : Pair.Gaussian.denote id generator
      (⟨0, point⁻¹⟩ : Algebra.Quadratic.Pair Canonical (-((regularAt parameter).eval point))) =
      add (Coherence.exact 0) (mul (Coherence.exact point⁻¹) generator) := rfl
  have channel : retained.channel = add (Coherence.exact 0) (mul (Coherence.exact point⁻¹) generator) :=
    (retained.channel_eq.trans interpreted).trans reduced
  exact NamedEquivalent.transport (congrArg CoherentNamed.name channel.symm) rfl
    (Add.coherentAdd_zero_left (mul (Coherence.exact point⁻¹) generator))

/-- The actual r/t quotient compares to t times the retained F(w), using the same original t²=w certificate. -/
def endpoint {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    (overlap : Cap.RootCoordinates.Overlap cap point owner)
    (cached : overlap.Potential)
    (value : Expression.Denotation (factor parameter) point overlap.regularRoot.value) :
    NamedEquivalent cached.val.output.name
      (mul overlap.coordinate.prepared.denominator value.channel).name := by
  let t := overlap.coordinate.prepared.denominator
  let r := overlap.regularRoot.value
  have square : NamedEquivalent (mul t t).name (Coherence.exact point).name := by
    have actual : NamedEquivalent (mul t t).name
        (Coherence.exact (point ^ HyperellipticReciprocal.originOrder (Fibre.frameCurve frame))).name :=
      overlap.coordinate.square
    have power : point ^ HyperellipticReciprocal.originOrder (Fibre.frameCurve frame) = point := by
      rewrite [frame_originOrder frame, pow_one]
      rfl
    exact NamedEquivalent.transport rfl
      (congrArg (fun scalar : Canonical => (Coherence.exact scalar).name) power) actual
  have inverse : NamedEquivalent
      (mul (Coherence.exact point) (Coherence.exact point⁻¹)).name (Coherence.exact 1).name :=
    NamedEquivalent.transport rfl
      (congrArg (fun scalar : Canonical => (Coherence.exact scalar).name)
        (ExplicitField.mul_inv_cancel point (overlap.point_nonzero (frame_originOrder frame))))
      (Exact.Arithmetic.exact_mul point point⁻¹)
  have candidate : NamedEquivalent (mul t (mul t value.channel)).name r.name :=
    (Product.Laws.coherentMul_assoc t t value.channel).symm.trans
      ((Product.Congruence.coherentMul_respects (mul t t) (Coherence.exact point)
        value.channel (mul (Coherence.exact point⁻¹) r) square (factor_channel value)).trans
        ((Product.Laws.coherentMul_assoc (Coherence.exact point) (Coherence.exact point⁻¹) r).symm.trans
          ((Product.Congruence.coherentMul_respects
            (mul (Coherence.exact point) (Coherence.exact point⁻¹)) (Coherence.exact 1)
            r r inverse (NamedEquivalent.refl _)).trans (Mul.coherentMul_one_left r))))
  have actual : NamedEquivalent (mul t cached.val.output).name r.name :=
    (Product.Laws.coherentMul_comm t cached.val.output).trans (Cap.RootCoordinates.Overlap.Potential.cancel cached)
  exact Cancellation.coherentMul_cancel_left t cached.val.output (mul t value.channel)
    overlap.coordinate.prepared.apart (actual.trans candidate.symm)

/-- Retain the full original fractional Scaling and its same-pair interpretation as F(w)=r/w. -/
@[expose] def Factor {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    {overlap : Cap.RootCoordinates.Overlap cap point owner}
    (retained : Regular.Weighted overlap) : Type _ :=
  (fraction :
    (scaled : retained.1.Scaling (constant ((regularAt parameter).eval point / coordinate.eval point))) ×
    { value : Expression.Denotation
        (Expression.scaleFraction (regularAt parameter) coordinate
          (Expression.inverseRoot (regularAt parameter))) point overlap.regularRoot.value //
      value.value = scaled.target.value ∧ value.channel = scaled.target.channel }) ×
  { value : Expression.Denotation (factor parameter) point overlap.regularRoot.value //
    value.value = fraction.2.val.value ∧ value.channel = fraction.2.val.channel }

/-- Compute the actual potential factor using the supplied inverse-root cache and one original fractional Scaling. -/
def buildFactor {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    {overlap : Cap.RootCoordinates.Overlap cap point owner}
    (retained : Regular.Weighted overlap) : Factor retained := by
  have nonzero := overlap.point_nonzero (frame_originOrder frame)
  have divisor : coordinate.eval point ≠ 0 := fun zero => nonzero ((coordinate_eval point).symm.trans zero)
  let fraction := retained.1.scaleFraction (regularAt parameter) coordinate divisor
  let value := fraction.2.val.reinterpret (factor parameter)
    (by rewrite [fraction.2.val.source_eq]; exact factor_fraction parameter) (factor_defined nonzero)
  exact ⟨fraction, ⟨value, ⟨rfl, rfl⟩⟩⟩

/-- The complete original buildFactor factory retains every supplied cache and computed value. -/
private theorem packaged_buildFactor_factory {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    {overlap : Cap.RootCoordinates.Overlap cap point owner}
    (retained : Regular.Weighted overlap) :
    buildFactor (parameter := parameter) (frame := frame) retained =
  (
    by
      have nonzero := overlap.point_nonzero (frame_originOrder frame)
      have divisor : coordinate.eval point ≠ 0 := fun zero => nonzero ((coordinate_eval point).symm.trans zero)
      let fraction := retained.1.scaleFraction (regularAt parameter) coordinate divisor
      let value := fraction.2.val.reinterpret (factor parameter)
        (by rewrite [fraction.2.val.source_eq]; exact factor_fraction parameter) (factor_defined nonzero)
      exact ⟨fraction, ⟨value, ⟨rfl, rfl⟩⟩⟩
    : Factor retained) := by rfl

/-- The complete original buildFactor factory retains every supplied cache and computed value. -/
theorem buildFactor_factory {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    {overlap : Cap.RootCoordinates.Overlap cap point owner}
    (retained : Regular.Weighted overlap) :
    buildFactor (parameter := parameter) (frame := frame) retained =
  (
    by
      have nonzero := overlap.point_nonzero (frame_originOrder frame)
      have divisor : coordinate.eval point ≠ 0 := fun zero => nonzero ((coordinate_eval point).symm.trans zero)
      let fraction := retained.1.scaleFraction (regularAt parameter) coordinate divisor
      let value := fraction.2.val.reinterpret (factor parameter)
        (by rewrite [fraction.2.val.source_eq]; exact factor_fraction parameter) (factor_defined nonzero)
      exact ⟨fraction, ⟨value, ⟨rfl, rfl⟩⟩⟩
    : Factor retained) :=
  packaged_buildFactor_factory (parameter := parameter) (frame := frame) retained

/-- The complete finite pullback coefficient retains its derivative, original Scaling and same-pair slope reduction. -/
@[expose] def Slope {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    {overlap : Cap.RootCoordinates.Overlap cap point owner}
    {retained : Regular.Weighted overlap} (values : Factor retained) : Type _ :=
  (first : Expression.Denotation (factor parameter).derivative point overlap.regularRoot.value) ×
  (scaled : first.Scaling (coordinate.scale 2)) ×
  (combined : { value : Expression.Denotation (derivative parameter) point overlap.regularRoot.value //
    value.value = values.2.val.value + scaled.target.value }) ×
  (target : { value : Expression.Denotation (Regular.slope parameter) point overlap.regularRoot.value //
    value.value = combined.val.value ∧ value.channel = combined.val.channel }) ×
  NamedEquivalent (add values.2.val.channel scaled.output).name target.val.channel.name

/-- Construct F+2wF' from the same retained factor, root and actual full coefficient tables.

The finite derivative is the original quadratic quotient rule at w. Its
Scaling uses the full polynomial 2w. The pair sum consumes both cached
pairs, and the slope reduction retains that same computed pair/channel.
-/
def buildSlope {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    {overlap : Cap.RootCoordinates.Overlap cap point owner}
    {retained : Regular.Weighted overlap} (values : Factor retained) : Slope values := by
  have regular : (regularAt parameter).eval point ≠ 0 := by
    have guarded := retained.1.defined
    change (Power.power (regularAt parameter) 1).eval point ≠ 0 at guarded
    rewrite [Power.eval_power, pow_one] at guarded
    exact guarded
  have firstDefined := Expression.defined_derivative (factor parameter) point values.2.val.defined regular
  let first := Expression.retain (factor parameter).derivative point overlap.regularRoot.value
    firstDefined values.2.val.identity
  let scaled := first.scale (coordinate.scale 2)
  have combinedDefined : (derivative parameter).Defined point :=
    derivative_defined values.2.val.defined regular
  let pair := values.2.val.value + scaled.target.value
  have pairEq : pair = (derivative parameter).evaluate point :=
    (congrArg₂
      (fun left right : Algebra.Quadratic.Pair Canonical (-((regularAt parameter).eval point)) => left + right)
      values.2.val.value_eq scaled.target.value_eq).trans
      (derivative_evaluate values.2.val.defined regular).symm
  let combined : Expression.Denotation (derivative parameter) point overlap.regularRoot.value :=
    ⟨derivative parameter, rfl, combinedDefined, values.2.val.identity, pair, pairEq,
      Pair.Gaussian.denote id overlap.regularRoot.value pair, rfl⟩
  have coordinateNonzero : coordinate.eval point ≠ 0 := fun zero =>
    overlap.point_nonzero (frame_originOrder frame) ((coordinate_eval point).symm.trans zero)
  have targetDefined : (Regular.slope parameter).Defined point := by
    rewrite [Regular.slope_eq]
    exact Expression.defined_scaleFraction _ coordinate (Expression.inverseRoot (regularAt parameter)) point
      retained.1.defined coordinateNonzero
  let target := combined.reinterpret (Regular.slope parameter)
    (by rewrite [combined.source_eq]; exact (derivative_eq parameter).symm) targetDefined
  have summed : NamedEquivalent (add values.2.val.channel scaled.target.channel).name combined.channel.name :=
    NamedEquivalent.transport
      (congrArg CoherentNamed.name
        (congrArg₂ add values.2.val.channel_eq.symm scaled.target.channel_eq.symm))
      (congrArg CoherentNamed.name combined.channel_eq.symm)
      (Pair.Gaussian.denote_add id (fun _ _ => rfl) overlap.regularRoot.value
        values.2.val.value scaled.target.value)
  have targetChannel : target.channel = combined.channel := rfl
  have equivalent : NamedEquivalent (add values.2.val.channel scaled.output).name target.channel.name :=
    NamedEquivalent.transport rfl (congrArg CoherentNamed.name targetChannel.symm)
      ((Sum.Congruence.coherentAdd_respects values.2.val.channel values.2.val.channel
        scaled.output scaled.target.channel (NamedEquivalent.refl _) scaled.equivalent).trans summed)
  exact ⟨first, scaled, ⟨combined, rfl⟩, ⟨target, ⟨rfl, rfl⟩⟩, equivalent⟩

/-- The complete original buildSlope factory retains every supplied cache and computed value. -/
private theorem packaged_buildSlope_factory {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    {overlap : Cap.RootCoordinates.Overlap cap point owner}
    {retained : Regular.Weighted overlap} (values : Factor retained) :
    buildSlope (parameter := parameter) (frame := frame) values =
  (
    by
      have regular : (regularAt parameter).eval point ≠ 0 := by
        have guarded := retained.1.defined
        change (Power.power (regularAt parameter) 1).eval point ≠ 0 at guarded
        rewrite [Power.eval_power, pow_one] at guarded
        exact guarded
      have firstDefined := Expression.defined_derivative (factor parameter) point values.2.val.defined regular
      let first := Expression.retain (factor parameter).derivative point overlap.regularRoot.value
        firstDefined values.2.val.identity
      let scaled := first.scale (coordinate.scale 2)
      have combinedDefined : (derivative parameter).Defined point :=
        derivative_defined values.2.val.defined regular
      let pair := values.2.val.value + scaled.target.value
      have pairEq : pair = (derivative parameter).evaluate point :=
        (congrArg₂
          (fun left right : Algebra.Quadratic.Pair Canonical (-((regularAt parameter).eval point)) => left + right)
          values.2.val.value_eq scaled.target.value_eq).trans
          (derivative_evaluate values.2.val.defined regular).symm
      let combined : Expression.Denotation (derivative parameter) point overlap.regularRoot.value :=
        ⟨derivative parameter, rfl, combinedDefined, values.2.val.identity, pair, pairEq,
          Pair.Gaussian.denote id overlap.regularRoot.value pair, rfl⟩
      have coordinateNonzero : coordinate.eval point ≠ 0 := fun zero =>
        overlap.point_nonzero (frame_originOrder frame) ((coordinate_eval point).symm.trans zero)
      have targetDefined : (Regular.slope parameter).Defined point := by
        rewrite [Regular.slope_eq]
        exact Expression.defined_scaleFraction _ coordinate (Expression.inverseRoot (regularAt parameter)) point
          retained.1.defined coordinateNonzero
      let target := combined.reinterpret (Regular.slope parameter)
        (by rewrite [combined.source_eq]; exact (derivative_eq parameter).symm) targetDefined
      have summed : NamedEquivalent (add values.2.val.channel scaled.target.channel).name combined.channel.name :=
        NamedEquivalent.transport
          (congrArg CoherentNamed.name
            (congrArg₂ add values.2.val.channel_eq.symm scaled.target.channel_eq.symm))
          (congrArg CoherentNamed.name combined.channel_eq.symm)
          (Pair.Gaussian.denote_add id (fun _ _ => rfl) overlap.regularRoot.value
            values.2.val.value scaled.target.value)
      have targetChannel : target.channel = combined.channel := rfl
      have equivalent : NamedEquivalent (add values.2.val.channel scaled.output).name target.channel.name :=
        NamedEquivalent.transport rfl (congrArg CoherentNamed.name targetChannel.symm)
          ((Sum.Congruence.coherentAdd_respects values.2.val.channel values.2.val.channel
            scaled.output scaled.target.channel (NamedEquivalent.refl _) scaled.equivalent).trans summed)
      exact ⟨first, scaled, ⟨combined, rfl⟩, ⟨target, ⟨rfl, rfl⟩⟩, equivalent⟩
    : Slope values) := by rfl

/-- The complete original buildSlope factory retains every supplied cache and computed value. -/
theorem buildSlope_factory {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    {overlap : Cap.RootCoordinates.Overlap cap point owner}
    {retained : Regular.Weighted overlap} (values : Factor retained) :
    buildSlope (parameter := parameter) (frame := frame) values =
  (
    by
      have regular : (regularAt parameter).eval point ≠ 0 := by
        have guarded := retained.1.defined
        change (Power.power (regularAt parameter) 1).eval point ≠ 0 at guarded
        rewrite [Power.eval_power, pow_one] at guarded
        exact guarded
      have firstDefined := Expression.defined_derivative (factor parameter) point values.2.val.defined regular
      let first := Expression.retain (factor parameter).derivative point overlap.regularRoot.value
        firstDefined values.2.val.identity
      let scaled := first.scale (coordinate.scale 2)
      have combinedDefined : (derivative parameter).Defined point :=
        derivative_defined values.2.val.defined regular
      let pair := values.2.val.value + scaled.target.value
      have pairEq : pair = (derivative parameter).evaluate point :=
        (congrArg₂
          (fun left right : Algebra.Quadratic.Pair Canonical (-((regularAt parameter).eval point)) => left + right)
          values.2.val.value_eq scaled.target.value_eq).trans
          (derivative_evaluate values.2.val.defined regular).symm
      let combined : Expression.Denotation (derivative parameter) point overlap.regularRoot.value :=
        ⟨derivative parameter, rfl, combinedDefined, values.2.val.identity, pair, pairEq,
          Pair.Gaussian.denote id overlap.regularRoot.value pair, rfl⟩
      have coordinateNonzero : coordinate.eval point ≠ 0 := fun zero =>
        overlap.point_nonzero (frame_originOrder frame) ((coordinate_eval point).symm.trans zero)
      have targetDefined : (Regular.slope parameter).Defined point := by
        rewrite [Regular.slope_eq]
        exact Expression.defined_scaleFraction _ coordinate (Expression.inverseRoot (regularAt parameter)) point
          retained.1.defined coordinateNonzero
      let target := combined.reinterpret (Regular.slope parameter)
        (by rewrite [combined.source_eq]; exact (derivative_eq parameter).symm) targetDefined
      have summed : NamedEquivalent (add values.2.val.channel scaled.target.channel).name combined.channel.name :=
        NamedEquivalent.transport
          (congrArg CoherentNamed.name
            (congrArg₂ add values.2.val.channel_eq.symm scaled.target.channel_eq.symm))
          (congrArg CoherentNamed.name combined.channel_eq.symm)
          (Pair.Gaussian.denote_add id (fun _ _ => rfl) overlap.regularRoot.value
            values.2.val.value scaled.target.value)
      have targetChannel : target.channel = combined.channel := rfl
      have equivalent : NamedEquivalent (add values.2.val.channel scaled.output).name target.channel.name :=
        NamedEquivalent.transport rfl (congrArg CoherentNamed.name targetChannel.symm)
          ((Sum.Congruence.coherentAdd_respects values.2.val.channel values.2.val.channel
            scaled.output scaled.target.channel (NamedEquivalent.refl _) scaled.equivalent).trans summed)
      exact ⟨first, scaled, ⟨combined, rfl⟩, ⟨target, ⟨rfl, rfl⟩⟩, equivalent⟩
    : Slope values) :=
  packaged_buildSlope_factory (parameter := parameter) (frame := frame) values

/-- Build the actual quotient potential and finite slope from the same supplied weighted coefficient cache.

The original t preparation is reused once. Both new finite factors consume
the existing inverse-root and power certificate; the actual endpoint
comparison uses the same quotient and factor returned here. No earlier
weighted builder or root observation is replayed.
-/
def ofWeighted {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    {overlap : Cap.RootCoordinates.Overlap cap point owner}
    (retained : Regular.Weighted overlap) :
    (cached : overlap.Potential) ×
    (values : Factor retained) ×
    (_slope : Slope values) ×
    NamedEquivalent cached.val.output.name
      (mul overlap.coordinate.prepared.denominator values.2.val.channel).name := by
  let cached := overlap.potential
  let values := buildFactor (parameter := parameter) (frame := frame) retained
  let slope := buildSlope (parameter := parameter) (frame := frame) values
  let equivalent := endpoint (parameter := parameter) (frame := frame) overlap cached values.2.val
  exact ⟨cached, values, slope, equivalent⟩

/-- The complete original ofWeighted factory retains every supplied cache and computed value. -/
private theorem packaged_ofWeighted_factory {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    {overlap : Cap.RootCoordinates.Overlap cap point owner}
    (retained : Regular.Weighted overlap) :
    ofWeighted (parameter := parameter) (frame := frame) retained =
  (
    by
      let cached := overlap.potential
      let values := buildFactor (parameter := parameter) (frame := frame) retained
      let slope := buildSlope (parameter := parameter) (frame := frame) values
      let equivalent := endpoint (parameter := parameter) (frame := frame) overlap cached values.2.val
      exact ⟨cached, values, slope, equivalent⟩
    : (cached : overlap.Potential) ×
    (values : Factor retained) ×
    (_slope : Slope values) ×
    NamedEquivalent cached.val.output.name
      (mul overlap.coordinate.prepared.denominator values.2.val.channel).name) := by rfl

/-- The complete original ofWeighted factory retains every supplied cache and computed value. -/
theorem ofWeighted_factory {parameter : Canonical} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar} {point : Canonical}
    {owner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    {overlap : Cap.RootCoordinates.Overlap cap point owner}
    (retained : Regular.Weighted overlap) :
    ofWeighted (parameter := parameter) (frame := frame) retained =
  (
    by
      let cached := overlap.potential
      let values := buildFactor (parameter := parameter) (frame := frame) retained
      let slope := buildSlope (parameter := parameter) (frame := frame) values
      let equivalent := endpoint (parameter := parameter) (frame := frame) overlap cached values.2.val
      exact ⟨cached, values, slope, equivalent⟩
    : (cached : overlap.Potential) ×
    (values : Factor retained) ×
    (_slope : Slope values) ×
    NamedEquivalent cached.val.output.name
      (mul overlap.coordinate.prepared.denominator values.2.val.channel).name) :=
  packaged_ofWeighted_factory (parameter := parameter) (frame := frame) retained

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential

end
