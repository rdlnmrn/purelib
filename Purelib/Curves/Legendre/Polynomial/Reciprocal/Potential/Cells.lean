module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PotentialComparison
public import Purelib.Curves.Legendre.Polynomial.Reciprocal.Regular
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Polynomial.Reciprocal.Primitives
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Bounds
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Denotation
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Comparison
import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.Cells
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian
import Purelib.Algebra.Quadratic.Pair.Gaussian.Power
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Scaling
import Purelib.Approximation.Gaussian.Name.Coherent.Division.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Laws
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Polynomial.Dense.Gaussian.Reciprocal
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Power
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring

/-! # The weighted reciprocal coefficient on the retained potential cell

The original Legendre radicand is w times its retained regular factor P.
Clearing the same denominator gives the finite coefficient identity for the
weighted differential. Both new tables use the cube already stored in the
original potential cell; a finite Newton inverse is never treated as exact.
-/

public section

namespace Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate half)
open Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds (Cell)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product
open Purelib.Polynomial
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Algebra.Quadratic.Pair.Gaussian (ReadingPrecision)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Gaussian} {frame : Paths.Frame parameter}
    {collar : ReciprocalExteriorCollar.Data (Fibre.frameCurve frame)}
    {cap : ReciprocalInnerInverse.Data (Fibre.frameCurve frame) collar}

/-- The actual frame-selected reciprocal radicand is the retained coordinate shift of its same regular factor. -/
theorem radicand_eq : HyperellipticReciprocal.polynomial (Fibre.frameCurve frame) = shift 1 cap.polynomial := by
  rewrite [HyperellipticReciprocal.polynomial, frame_originOrder frame, cap.polynomial_eq]
  rfl

/-- The finite derivative of the actual retained regular factor reads the original Legendre quadratic derivative. -/
theorem polynomial_derivative (point : Gaussian) :
    (Derivative.derivative cap.polynomial).eval point = 2 * parameter * point - (1 + parameter) := by
  have original := congrArg (fun polynomial : Coefficients =>
    (Derivative.derivative polynomial).eval point) cap.polynomial_eq
  have framed := congrArg (fun polynomial : Coefficients =>
    (Derivative.derivative (Dense.Gaussian.Reciprocal.reversed polynomial)).eval point)
      (Fibre.frameCurve_polynomial frame)
  have readback := original.trans framed
  rewrite [Dense.Gaussian.Reciprocal.reversed_derivative_eval] at readback
  apply readback.trans
  change (Dense.Gaussian.Reciprocal.lowJet point [1, -(1 + parameter), parameter, 0]).2 = _
  unfold Dense.Gaussian.Reciprocal.lowJet
  simp only [List.foldr_cons, List.foldr_nil]
  ring1

/-- The same original radicand and regular factor satisfy the denominator-cleared weighted coefficient identity. -/
theorem coefficient_identity (point : Gaussian) :
    2 * ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point *
      (Derivative.derivative cap.polynomial).eval point - half * cap.polynomial.eval point *
        (Derivative.derivative (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))).eval point) -
      parameter * point * (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point =
        -cap.polynomial.eval point := by
  have shifted := congrArg (fun polynomial : Coefficients => (Derivative.derivative polynomial).eval point)
    (radicand_eq (frame := frame) (cap := cap))
  rewrite [Derivative.eval_derivative_shift_one] at shifted
  rewrite [shifted, radicand_eq (frame := frame) (cap := cap), eval_shift, pow_one,
    polynomial_derivative (frame := frame) (cap := cap),
    Regular.polynomial_eq (parameter := parameter) (frame := frame) cap point, regularAt_eval]
  have twiceHalf : (2 : Gaussian) * half = 1 := by decide +kernel
  calc
    _ = -((1 - point) * (1 - parameter * point)) +
      (1 - 2 * half) * ((1 - point) * (1 - parameter * point)) *
      ((2 * parameter * point - (1 + parameter)) * point + (1 - point) * (1 - parameter * point)) := by ring1
    _ = _ := by rewrite [twiceHalf]; ring1

/-- The regular w-remainder uses the original polynomial numerator -λw before denominator lifting. -/
def wRemainder : Coefficients := shift 1 (constant (-parameter))

/-- The actual regular w-remainder numerator keeps its full original signed scalar. -/
private theorem packaged_wRemainder_eval (point : Gaussian) :
    (wRemainder (parameter := parameter)).eval point = -parameter * point := by
  unfold wRemainder
  rewrite [eval_shift, eval_constant, pow_one]
  rfl

/-- The actual regular w-remainder numerator keeps its full original signed scalar. -/
theorem wRemainder_eval (point : Gaussian) :
    (wRemainder (parameter := parameter)).eval point = -parameter * point :=
  packaged_wRemainder_eval point

section Cells

variable {count : Nat} {center : Gaussian}
    {centerOwner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval center)}
    {terminal : TerminalModels.Terminal cap centerOwner count}
    {differential : Curves.Hyperelliptic.Differentials.Basic.Differential 1}
    {comparison : TerminalComparison.Data terminal differential}
    {preparation : PotentialComparison.Preparation comparison}
    {start finish : Gaussian} {coordinate : Spatial.Coordinate start finish}
    {stage : Nat} {allowance : Coordinate} {nonnegative : 0 ≤ allowance}

/-- The cleared cubic density already stored by the same potential preparation has the weighted numerator identity. -/
theorem density_identity (point : Gaussian) :
    2 * (preparation.2.1.coefficient.scale half).eval point +
      ((wRemainder (parameter := parameter)) *
        HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point = -cap.polynomial.eval point := by
  have actual := PotentialComparison.Preparation.density_numerator preparation point
  have coefficient := coefficient_identity (frame := frame) (cap := cap) point
  rewrite [actual, eval_mul, wRemainder_eval]
  calc
    _ = 2 * ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point *
      (Derivative.derivative cap.polynomial).eval point - half * cap.polynomial.eval point *
        (Derivative.derivative (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))).eval point) -
          parameter * point * (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point := by ring1
    _ = _ := coefficient

/-- The weighted and denominator-lifted regular remainder tables use exactly the retained original inverse cube. -/
@[expose] def Tables (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) : Type _ :=
  { value : Coefficients // value = (-cap.polynomial) * retained.powers.cube } ×
  { value : Coefficients // value = ((wRemainder (parameter := parameter)) *
      HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) * retained.powers.cube }

namespace Tables

/-- Build only the two numerator products, retaining the same supplied cell and original cube without refinement. -/
def build (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) : Tables retained :=
  let weighted := (-cap.polynomial) * retained.powers.cube
  let remainder := ((wRemainder (parameter := parameter)) *
    HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) * retained.powers.cube
  ⟨⟨weighted, rfl⟩, ⟨remainder, rfl⟩⟩

/-- The whole table factory retains precisely the original two products on the same cached cube. -/
private theorem packaged_build_factory (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) :
    build retained =
      (let weighted := (-cap.polynomial) * retained.powers.cube
       let remainder := ((wRemainder (parameter := parameter)) *
         HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) * retained.powers.cube
       ⟨⟨weighted, rfl⟩, ⟨remainder, rfl⟩⟩ : Tables retained) := by rfl

/-- The whole table factory retains precisely the original two products on the same cached cube. -/
theorem build_factory (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) :
    build retained =
      (let weighted := (-cap.polynomial) * retained.powers.cube
       let remainder := ((wRemainder (parameter := parameter)) *
         HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) * retained.powers.cube
       ⟨⟨weighted, rfl⟩, ⟨remainder, rfl⟩⟩ : Tables retained) := packaged_build_factory retained

/-- The same finite tables realize the weighted split exactly after denominator clearing. -/
theorem split (retained : Cell preparation.2.1 coordinate stage allowance nonnegative)
    (tables : Tables retained) (point : Gaussian) :
    tables.1.val.eval point = 2 * retained.density.eval point + tables.2.val.eval point := by
  have actual := congrArg (fun value : Gaussian => value * retained.powers.cube.eval point)
    (density_identity (preparation := preparation) point)
  simp only [eval_mul, eval_scale] at actual
  simp only [tables.1.property, tables.2.property, retained.density_eq, eval_mul, eval_neg, eval_scale]
  exact actual.symm.trans (by ring1)

/-- The retained weighted table reads the exact original cubic numerator at the same supplied Point. -/
theorem weighted_compiled (retained : Cell preparation.2.1 coordinate stage allowance nonnegative)
    (tables : Tables retained) (point : Gaussian) :
    tables.1.val.eval point = (-cap.polynomial).eval point * (primitivePolynomial retained.powers 1).eval point := by
  rewrite [tables.1.property, eval_mul]
  rfl

/-- The lifted remainder table reads the exact same original cube with its full numerator. -/
theorem remainder_compiled (retained : Cell preparation.2.1 coordinate stage allowance nonnegative)
    (tables : Tables retained) (point : Gaussian) :
    tables.2.val.eval point = ((wRemainder (parameter := parameter)) *
      HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point *
        (primitivePolynomial retained.powers 1).eval point := by
  rewrite [tables.2.property, eval_mul]
  rfl

/-- The independent inverse-table remainder differs by the retained Newton square residual, rather than being equal. -/
theorem inverse_remainder_residual (retained : Cell preparation.2.1 coordinate stage allowance nonnegative)
    (tables : Tables retained) (point : Gaussian) :
    tables.2.val.eval point -
        (wRemainder (parameter := parameter)).eval point * retained.inverse.value.eval point =
      (wRemainder (parameter := parameter)).eval point * retained.inverse.value.eval point *
        ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point *
          retained.inverse.value.eval point ^ 2 - 1) := by
  simp only [tables.2.property, eval_mul, retained.powers.cube_eval]
  ring1

end Tables

section Endpoints

variable {point : Gaussian}
    {pointOwner : Owner ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)}
    {overlap : Cap.RootCoordinates.Overlap cap point pointOwner}

/-- The original weighted reciprocal w-channel, before the separate operational 2t Jacobian. -/
def weightedChannel (overlap : Cap.RootCoordinates.Overlap cap point pointOwner) : CoherentNamed :=
  mul (Coherence.exact (-1)) (div (Coherence.exact point⁻¹) overlap.reciprocal.value overlap.reciprocal.apart)

/-- The ordinary regular w-remainder uses the same actual reciprocal-root owner and full signed numerator. -/
def remainderChannel (overlap : Cap.RootCoordinates.Overlap cap point pointOwner) : CoherentNamed :=
  div (Coherence.exact ((wRemainder (parameter := parameter)).eval point))
    overlap.reciprocal.value overlap.reciprocal.apart

/-- Read any original ordinary numerator denotation as the same actual source-root quotient. -/
private def inverseEquivalent (source : Point terminal.neighborhood.patch point) (numerator : Coefficients)
    (original : PrimitiveDenotation source 0 numerator) :
    NamedEquivalent original.channel.name
      (div (Coherence.exact (numerator.eval point)) source.certificate.value source.certificate.apart).name := by
  have equation : Approximation.Gaussian.Provenance.Power.PowerIdentity source.certificate.value 2
      (-(-(HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point)) := by
    rewrite [_root_.neg_neg]
    exact original.identity
  have nonzero : -(-(HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point) ≠ 0 := by
    rewrite [_root_.neg_neg]
    exact source.owner.parameterNonzero
  have normalized := Algebra.Quadratic.Pair.Gaussian.reciprocal_odd_power
    (numerator.eval point) source.certificate.value equation nonzero source.certificate.apart 0
  have readback : original.value = ⟨0, numerator.eval point /
      ((HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point ^ 1)⟩ := by
    rewrite [original.value_eq]
    apply Algebra.Quadratic.Pair.ext
    · rewrite [Expression.evaluate_re]
      change (0 : Gaussian) / _ = 0
      exact ExplicitField.zero_div _
    · rewrite [Expression.evaluate_im]
      change numerator.eval point /
        (Power.power (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) 1).eval point = _
      rewrite [Power.eval_power]
      rfl
  have actual : NamedEquivalent
      (mul (Coherence.exact (numerator.eval point))
        (Power.namedPower (div (Coherence.exact 1) source.certificate.value source.certificate.apart) 1)).name
      original.channel.name := by
    rewrite [original.channel_eq, readback]
    simpa only [_root_.neg_neg] using normalized
  have quotient := (Congruence.coherentMul_respects
    (Coherence.exact (numerator.eval point)) (Coherence.exact (numerator.eval point))
    (Power.namedPower (div (Coherence.exact 1) source.certificate.value source.certificate.apart) 1)
    (div (Coherence.exact 1) source.certificate.value source.certificate.apart)
    (NamedEquivalent.refl _) (Power.namedPower_one _)).trans
      (ReciprocalRootNames.constant_mul_quotient (numerator.eval point) 1
        source.certificate.value source.certificate.apart)
  have unit : numerator.eval point * 1 = numerator.eval point := Basic.mul_one _
  rewrite [unit] at quotient
  exact actual.symm.trans quotient

/-- The lifted numerator qN over v cubed is the same guarded quadratic expression as N over v. -/
private theorem lift_equal (numerator : Coefficients) :
    (Expression.oddReciprocal (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) 1
      (numerator * HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))).Equal
    (Expression.oddReciprocal (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) 0 numerator) := by
  apply Expression.equal_of_cross_eval
  · intro point
    simp only [-eq_self, -iff_self, Expression.oddReciprocal, eval_zero, Power.eval_power]
    ring1
  · intro point
    simp only [-eq_self, -iff_self, Expression.oddReciprocal, eval_mul, Power.eval_power]
    ring1

/-- Keep the complete same-Point remainder pair and channel under its ordinary inverse-root presentation. -/
private def remainderInverse (source : Point terminal.neighborhood.patch point)
    (original : PrimitiveDenotation source 1 ((wRemainder (parameter := parameter)) *
      HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))) :
    PrimitiveDenotation source 0 (wRemainder (parameter := parameter)) :=
  original.reinterpret
    (Expression.oddReciprocal (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) 0
      (wRemainder (parameter := parameter)))
    (by rewrite [original.source_eq]; exact (lift_equal (frame := frame) (wRemainder (parameter := parameter))).symm)
    (by
      change (Power.power (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) 1).eval point ≠ 0
      rewrite [Power.eval_power, pow_one]
      exact source.owner.parameterNonzero)

/-- Reinterpretation preserves the actual original remainder channel. -/
private theorem remainderInverse_channel (source : Point terminal.neighborhood.patch point)
    (original : PrimitiveDenotation source 1 ((wRemainder (parameter := parameter)) *
      HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))) :
    (remainderInverse source original).channel = original.channel := by rfl

/-- Keep the complete same-Point weighted pair under its exact pointwise ordinary quotient presentation. -/
private def weightedInverse (data : EndpointComparison.Data comparison overlap)
    (original : PrimitiveDenotation data.owner.point 1 (-cap.polynomial)) :
    PrimitiveDenotation data.owner.point 0 (constant (-point⁻¹)) := by
  have pointNonzero := overlap.point_nonzero (frame_originOrder frame)
  have qNonzero := data.owner.point.owner.parameterNonzero
  have qValue : (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point =
      cap.polynomial.eval point * point := by
    rewrite [radicand_eq (frame := frame) (cap := cap), eval_shift, pow_one]
    rfl
  have readback :
      (Expression.oddReciprocal (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) 0
        (constant (-point⁻¹))).evaluate point =
      (Expression.oddReciprocal (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) 1
        (-cap.polynomial)).evaluate point := by
    apply Algebra.Quadratic.Pair.ext
    · rewrite [Expression.evaluate_re, Expression.evaluate_re]
      change (0 : Gaussian) / _ = (0 : Gaussian) / _
      exact (ExplicitField.zero_div _).trans (ExplicitField.zero_div _).symm
    · rewrite [Expression.evaluate_im, Expression.evaluate_im]
      change (constant (-point⁻¹) : Coefficients).eval point /
        (Power.power (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) 1).eval point =
        (-cap.polynomial).eval point /
          (Power.power (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) 2).eval point
      rewrite [eval_constant, eval_neg, Power.eval_power, Power.eval_power, pow_one]
      apply ExplicitField.eq_of_mul_eq_mul_right (ExplicitField.pow_ne_zero_of_ne_zero qNonzero 2)
      calc
        _ = ((-point⁻¹) /
            (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point *
              (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point) *
                (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point := by ring1
        _ = (-point⁻¹) * (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)).eval point := by
          rewrite [ExplicitField.div_mul_cancel _ qNonzero]
          rfl
        _ = -(cap.polynomial.eval point * (point * point⁻¹)) := by rewrite [qValue]; ring1
        _ = -cap.polynomial.eval point := by
          rewrite [ExplicitField.mul_inv_cancel point pointNonzero]
          ring1
        _ = _ := (ExplicitField.div_mul_cancel _ (ExplicitField.pow_ne_zero_of_ne_zero qNonzero 2)).symm
  exact original.reinterpretAt
    (Expression.oddReciprocal (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) 0
      (constant (-point⁻¹))) readback (by
        change (Power.power (HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) 1).eval point ≠ 0
        rewrite [Power.eval_power, pow_one]
        exact qNonzero)

/-- Pointwise reinterpretation preserves the actual original weighted channel. -/
private theorem weightedInverse_channel (data : EndpointComparison.Data comparison overlap)
    (original : PrimitiveDenotation data.owner.point 1 (-cap.polynomial)) :
    (weightedInverse data original).channel = original.channel := by rfl

/-- Derive the weighted source-channel comparison from its actual denominator identity and retained root ownership. -/
def weightedEquivalent (data : EndpointComparison.Data comparison overlap)
    (original : PrimitiveDenotation data.owner.point 1 (-cap.polynomial)) :
    NamedEquivalent original.channel.name (weightedChannel overlap).name := by
  let inverse := weightedInverse data original
  have same : inverse.channel = original.channel := weightedInverse_channel data original
  have quotient := inverseEquivalent data.owner.point (constant (-point⁻¹)) inverse
  have numerator : (constant (-point⁻¹) : Coefficients).eval point = -point⁻¹ := eval_constant _ _
  have source := NamedEquivalent.transport (congrArg CoherentNamed.name same) rfl quotient
  have roots := Approximation.Gaussian.Name.Coherent.Division.Equivalence.coherentDiv_respects
    (Coherence.exact ((constant (-point⁻¹) : Coefficients).eval point)) (Coherence.exact (-point⁻¹))
    data.owner.point.certificate.value overlap.reciprocal.value
    data.owner.point.certificate.apart overlap.reciprocal.apart
    (NamedEquivalent.transport (congrArg (fun value : Gaussian => (Coherence.exact value).name) numerator).symm
      rfl (NamedEquivalent.refl _)) data.owner.equivalent.symm
  have signed := ReciprocalRootNames.constant_mul_quotient (-1) point⁻¹
    overlap.reciprocal.value overlap.reciprocal.apart
  have factor : (-1 : Gaussian) * point⁻¹ = -point⁻¹ := by ring1
  have weighted : NamedEquivalent (weightedChannel overlap).name
      (div (Coherence.exact (-point⁻¹)) overlap.reciprocal.value overlap.reciprocal.apart).name := by
    change NamedEquivalent
      (mul (Coherence.exact (-1))
        (div (Coherence.exact point⁻¹) overlap.reciprocal.value overlap.reciprocal.apart)).name _
    exact NamedEquivalent.transport rfl
      (congrArg (fun value : Gaussian =>
        (div (Coherence.exact value) overlap.reciprocal.value overlap.reciprocal.apart).name) factor) signed
  exact source.trans (roots.trans weighted.symm)

/-- Derive the ordinary remainder channel comparison without replacing either original Point or root owner. -/
def remainderEquivalent (data : EndpointComparison.Data comparison overlap)
    (original : PrimitiveDenotation data.owner.point 1 ((wRemainder (parameter := parameter)) *
      HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))) :
    NamedEquivalent original.channel.name (remainderChannel overlap).name := by
  let inverse := remainderInverse data.owner.point original
  have same : inverse.channel = original.channel := remainderInverse_channel data.owner.point original
  have source := NamedEquivalent.transport (congrArg CoherentNamed.name same) rfl
    (inverseEquivalent data.owner.point (wRemainder (parameter := parameter)) inverse)
  exact source.trans (Approximation.Gaussian.Name.Coherent.Division.Equivalence.coherentDiv_respects
    (Coherence.exact ((wRemainder (parameter := parameter)).eval point))
    (Coherence.exact ((wRemainder (parameter := parameter)).eval point))
    data.owner.point.certificate.value overlap.reciprocal.value
    data.owner.point.certificate.apart overlap.reciprocal.apart
    (NamedEquivalent.refl _) data.owner.equivalent.symm)

/-- The actual old ramified coefficient transport consumes the independently retained regular-w Scaling cache. -/
def weightedTransport (data : EndpointComparison.Data comparison overlap)
    (original : PrimitiveDenotation data.owner.point 1 (-cap.polynomial))
    (regular : Regular.Weighted overlap) :
    NamedEquivalent
      (mul (mul (Coherence.exact 2) overlap.coordinate.prepared.denominator) original.channel).name
      regular.2.2.val.channel.name := by
  let factor := mul (Coherence.exact 2) overlap.coordinate.prepared.denominator
  have source := Congruence.coherentMul_respects factor factor original.channel (weightedChannel overlap)
    (NamedEquivalent.refl _) (weightedEquivalent data original)
  exact source.trans (Regular.compare (parameter := parameter) (frame := frame) overlap regular)

/-- The source request, retained cubic denotation, visible precision and independent original-channel request. -/
@[expose] def CubicRequest (source : Point terminal.neighborhood.patch point)
    (numerator : Coefficients) (original : CoherentNamed) (target : Coordinate) (floor : Nat) : Type _ :=
  (_source : PrimitiveRequest source 1 numerator floor (target / 4)) ×
  (denotation : PrimitiveDenotation source 1 numerator) ×
  (_precision : ReadingPrecision
    (Norm.Basic.normSq denotation.value.im) (target / 16)) ×
  Observation.Request original (target / 256)

namespace CubicRequest

/-- Select actual source and observation precisions without constructing another inverse model or power cache. -/
def build {source : Point terminal.neighborhood.patch point} (bounds : PrimitiveBounds source)
    (numerator : Coefficients)
    (original : CoherentNamed) (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    CubicRequest source numerator original target floor :=
  let requested := bounds.request 1 numerator floor (target / 4)
    (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
  let denotation := retainPrimitiveDenotation source bounds 1 numerator ⟨requested.factor, requested.factor_eq⟩
  let precision := ReadingPrecision.build
    (Norm.Basic.normSq denotation.value.im) (target / 16)
    (Norm.Basic.normSq_nonneg _)
    (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
  let bank := Observation.Request.build original (target / 256)
    (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
  ⟨requested, denotation, precision, bank⟩

/-- The actual request retains each original precision factory and its same-Point denotation cache. -/
private theorem packaged_build_factory {source : Point terminal.neighborhood.patch point}
    (bounds : PrimitiveBounds source) (numerator : Coefficients)
    (original : CoherentNamed) (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    build bounds numerator original target positive floor =
      (let requested := bounds.request 1 numerator floor (target / 4)
         (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
       let denotation := retainPrimitiveDenotation source bounds 1 numerator ⟨requested.factor, requested.factor_eq⟩
       let precision := ReadingPrecision.build
         (Norm.Basic.normSq denotation.value.im) (target / 16)
         (Norm.Basic.normSq_nonneg _)
         (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
       let bank := Observation.Request.build original (target / 256)
         (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
       ⟨requested, denotation, precision, bank⟩ : CubicRequest source numerator original target floor) := by rfl

/-- The actual request retains each original precision factory and its same-Point denotation cache. -/
theorem build_factory {source : Point terminal.neighborhood.patch point}
    (bounds : PrimitiveBounds source) (numerator : Coefficients)
    (original : CoherentNamed) (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    build bounds numerator original target positive floor =
      (let requested := bounds.request 1 numerator floor (target / 4)
         (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
       let denotation := retainPrimitiveDenotation source bounds 1 numerator ⟨requested.factor, requested.factor_eq⟩
       let precision := ReadingPrecision.build
         (Norm.Basic.normSq denotation.value.im) (target / 16)
         (Norm.Basic.normSq_nonneg _)
         (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
       let bank := Observation.Request.build original (target / 256)
         (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
       ⟨requested, denotation, precision, bank⟩ : CubicRequest source numerator original target floor) :=
  packaged_build_factory bounds numerator original target positive floor

end CubicRequest

/-- An actual source root reading and polynomial comparison on the same supplied inverse/cube cache. -/
@[expose] def CubicSample {source : Point terminal.neighborhood.patch point} {numerator : Coefficients}
    {original : CoherentNamed} {target : Coordinate} {floor : Nat}
    (paid : CubicRequest source numerator original target floor)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (table : Coefficients)
    (compiled : table.eval point = numerator.eval point * (primitivePolynomial retained.powers 1).eval point) :
    Type _ :=
  (root : PrimitiveRoot source stage paid.2.2.1.target) ×
  (reading : { value : PrimitiveReading source stage retained.inverse retained.powers //
    value = root.readModel retained.inverse retained.inverse_eq retained.powers }) ×
  (value : { value : PrimitiveValue reading.val 1 numerator paid.2.1 table //
    value = retainPrimitiveValue reading.val 1 numerator paid.2.1 table compiled
      ⟨paid.1.factor, paid.1.factor_eq⟩ }) × PrimitiveValue.Comparison value.val paid.2.2.2

namespace CubicSample

/-- Compare the same model table with an independently retained original reading after its genuine requested floor.

The original channel relation is mathematical data from the source owners.
The concrete weighted and regular-remainder constructors below derive it
from their same-Point denominator and root identities, rather than accept a
sample error or final period estimate.
-/
def build {source : Point terminal.neighborhood.patch point} {numerator : Coefficients}
    {original : CoherentNamed} {target : Coordinate} {floor : Nat}
    (paid : CubicRequest source numerator original target floor)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (table : Coefficients)
    (compiled : table.eval point = numerator.eval point * (primitivePolynomial retained.powers 1).eval point)
    (equivalent : NamedEquivalent paid.2.1.channel.name original.name)
    (later : paid.1.stage ≤ stage) (inside : terminal.neighborhood.patch.box.Contains point)
    (positive : 0 < target) : CubicSample paid retained table compiled :=
  let root := selectPrimitiveRoot source stage paid.2.2.1.target paid.2.2.1.target_positive
  let reading := root.readModel retained.inverse retained.inverse_eq retained.powers
  let value := retainPrimitiveValue reading 1 numerator paid.2.1 table compiled ⟨paid.1.factor, paid.1.factor_eq⟩
  let compared := value.compare paid.2.2.2 paid.2.2.1 root rfl
    (Fraction.Order.Basic.le_refl _) paid.1 inside later equivalent positive
  ⟨root, ⟨reading, rfl⟩, ⟨value, rfl⟩, compared⟩

/-- The complete sample retains one requested root, its reading of the supplied model, and the actual comparison. -/
private theorem packaged_build_factory {source : Point terminal.neighborhood.patch point} {numerator : Coefficients}
    {original : CoherentNamed} {target : Coordinate} {floor : Nat}
    (paid : CubicRequest source numerator original target floor)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (table : Coefficients)
    (compiled : table.eval point = numerator.eval point * (primitivePolynomial retained.powers 1).eval point)
    (equivalent : NamedEquivalent paid.2.1.channel.name original.name)
    (later : paid.1.stage ≤ stage) (inside : terminal.neighborhood.patch.box.Contains point)
    (positive : 0 < target) :
    build paid retained table compiled equivalent later inside positive =
      (let root := selectPrimitiveRoot source stage paid.2.2.1.target paid.2.2.1.target_positive
       let reading := root.readModel retained.inverse retained.inverse_eq retained.powers
       let value := retainPrimitiveValue reading 1 numerator paid.2.1 table compiled ⟨paid.1.factor, paid.1.factor_eq⟩
       let compared := value.compare paid.2.2.2 paid.2.2.1 root rfl
         (Fraction.Order.Basic.le_refl _) paid.1 inside later equivalent positive
       ⟨root, ⟨reading, rfl⟩, ⟨value, rfl⟩, compared⟩ : CubicSample paid retained table compiled) := by rfl

/-- The complete sample retains one requested root, its reading of the supplied model, and the actual comparison. -/
theorem build_factory {source : Point terminal.neighborhood.patch point} {numerator : Coefficients}
    {original : CoherentNamed} {target : Coordinate} {floor : Nat}
    (paid : CubicRequest source numerator original target floor)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (table : Coefficients)
    (compiled : table.eval point = numerator.eval point * (primitivePolynomial retained.powers 1).eval point)
    (equivalent : NamedEquivalent paid.2.1.channel.name original.name)
    (later : paid.1.stage ≤ stage) (inside : terminal.neighborhood.patch.box.Contains point)
    (positive : 0 < target) :
    build paid retained table compiled equivalent later inside positive =
      (let root := selectPrimitiveRoot source stage paid.2.2.1.target paid.2.2.1.target_positive
       let reading := root.readModel retained.inverse retained.inverse_eq retained.powers
       let value := retainPrimitiveValue reading 1 numerator paid.2.1 table compiled ⟨paid.1.factor, paid.1.factor_eq⟩
       let compared := value.compare paid.2.2.2 paid.2.2.1 root rfl
         (Fraction.Order.Basic.le_refl _) paid.1 inside later equivalent positive
       ⟨root, ⟨reading, rfl⟩, ⟨value, rfl⟩, compared⟩ : CubicSample paid retained table compiled) :=
  packaged_build_factory paid retained table compiled equivalent later inside positive

/-- Read the actual already computed source scalar from its retained original PrimitiveValue. -/
def value {source : Point terminal.neighborhood.patch point} {numerator : Coefficients}
    {original : CoherentNamed} {target : Coordinate} {floor : Nat}
    (paid : CubicRequest source numerator original target floor)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (table : Coefficients)
    (compiled : table.eval point = numerator.eval point * (primitivePolynomial retained.powers 1).eval point)
    (sample : CubicSample paid retained table compiled) : Gaussian := sample.2.2.1.val.value

/-- The retained scalar reads the same original compiled table without executing its evaluation again. -/
private theorem packaged_value_eq {source : Point terminal.neighborhood.patch point} {numerator : Coefficients}
    {original : CoherentNamed} {target : Coordinate} {floor : Nat}
    (paid : CubicRequest source numerator original target floor)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (table : Coefficients)
    (compiled : table.eval point = numerator.eval point * (primitivePolynomial retained.powers 1).eval point)
    (sample : CubicSample paid retained table compiled) :
    value paid retained table compiled sample = table.eval point := by
  exact sample.2.2.1.val.value_eq.trans
    (congrArg (fun polynomial : Coefficients => polynomial.eval point) sample.2.2.1.val.polynomial_eq)

/-- The retained scalar reads the same original compiled table without executing its evaluation again. -/
theorem value_eq {source : Point terminal.neighborhood.patch point} {numerator : Coefficients}
    {original : CoherentNamed} {target : Coordinate} {floor : Nat}
    (paid : CubicRequest source numerator original target floor)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (table : Coefficients)
    (compiled : table.eval point = numerator.eval point * (primitivePolynomial retained.powers 1).eval point)
    (sample : CubicSample paid retained table compiled) :
    value paid retained table compiled sample = table.eval point :=
  packaged_value_eq paid retained table compiled sample

/-- The actual root precision and old-state comparison pay the original table-to-reading residual. -/
theorem error_le {source : Point terminal.neighborhood.patch point} {numerator : Coefficients}
    {original : CoherentNamed} {target : Coordinate} {floor : Nat}
    (paid : CubicRequest source numerator original target floor)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (table : Coefficients)
    (compiled : table.eval point = numerator.eval point * (primitivePolynomial retained.powers 1).eval point)
    (sample : CubicSample paid retained table compiled) :
    Norm.Basic.normSq (table.eval point - paid.2.2.2.reading.value) ≤ target := by
  have actual := sample.2.2.2.residual_le
  have scalar := sample.2.2.2.source_residual
  exact (congrArg Norm.Basic.normSq scalar).symm.trans_le actual

end CubicSample

/-- Select weighted precision on the same actual source Point and original weighted reciprocal channel. -/
def weightedRequest (data : EndpointComparison.Data comparison overlap)
    (bounds : PrimitiveBounds data.owner.point) (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    CubicRequest data.owner.point (-cap.polynomial) (weightedChannel overlap) target floor :=
  CubicRequest.build (parameter := parameter) (frame := frame) (cap := cap) (terminal := terminal)
    bounds (-cap.polynomial) (weightedChannel overlap) target positive floor

/-- Select regular-remainder precision on that same Point, using the denominator-lifted numerator. -/
def remainderRequest (data : EndpointComparison.Data comparison overlap)
    (bounds : PrimitiveBounds data.owner.point) (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    CubicRequest data.owner.point ((wRemainder (parameter := parameter)) *
      HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) (remainderChannel overlap) target floor :=
  CubicRequest.build (parameter := parameter) (frame := frame) (cap := cap) (terminal := terminal)
    bounds ((wRemainder (parameter := parameter)) *
    HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) (remainderChannel overlap) target positive floor

/-- Both independent reading requests share the one actual source-bound cache and retain their genuine common floor. -/
@[expose] def Requests (data : EndpointComparison.Data comparison overlap)
    (weightedTarget remainderTarget : Coordinate) (floor : Nat) : Type _ :=
  (_bounds : PrimitiveBounds data.owner.point) ×
  (weighted : CubicRequest data.owner.point (-cap.polynomial) (weightedChannel overlap) weightedTarget floor) ×
  (regular : CubicRequest data.owner.point ((wRemainder (parameter := parameter)) *
    HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) (remainderChannel overlap) remainderTarget floor) ×
  { stage : Nat // stage = max weighted.1.stage regular.1.stage }

/-- Construct both actual requests from one retained source-bound cache, before choosing the shared model stage. -/
def requests (data : EndpointComparison.Data comparison overlap)
    (weightedTarget remainderTarget : Coordinate) (weightedPositive : 0 < weightedTarget)
    (remainderPositive : 0 < remainderTarget) (floor : Nat) : Requests data weightedTarget remainderTarget floor :=
  let bounds := data.owner.point.primitiveBounds
  let weighted := weightedRequest data bounds weightedTarget weightedPositive floor
  let regular := remainderRequest data bounds remainderTarget remainderPositive floor
  let stage := max weighted.1.stage regular.1.stage
  ⟨bounds, weighted, regular, ⟨stage, rfl⟩⟩

/-- The complete paired request keeps the same bound cache, both original selections and their actual maximum. -/
private theorem packaged_requests_factory (data : EndpointComparison.Data comparison overlap)
    (weightedTarget remainderTarget : Coordinate) (weightedPositive : 0 < weightedTarget)
    (remainderPositive : 0 < remainderTarget) (floor : Nat) :
    requests data weightedTarget remainderTarget weightedPositive remainderPositive floor =
      (let bounds := data.owner.point.primitiveBounds
       let weighted := weightedRequest data bounds weightedTarget weightedPositive floor
       let regular := remainderRequest data bounds remainderTarget remainderPositive floor
       let stage := max weighted.1.stage regular.1.stage
       ⟨bounds, weighted, regular, ⟨stage, rfl⟩⟩ : Requests data weightedTarget remainderTarget floor) := by rfl

/-- The complete paired request keeps the same bound cache, both original selections and their actual maximum. -/
theorem requests_factory (data : EndpointComparison.Data comparison overlap)
    (weightedTarget remainderTarget : Coordinate) (weightedPositive : 0 < weightedTarget)
    (remainderPositive : 0 < remainderTarget) (floor : Nat) :
    requests data weightedTarget remainderTarget weightedPositive remainderPositive floor =
      (let bounds := data.owner.point.primitiveBounds
       let weighted := weightedRequest data bounds weightedTarget weightedPositive floor
       let regular := remainderRequest data bounds remainderTarget remainderPositive floor
       let stage := max weighted.1.stage regular.1.stage
       ⟨bounds, weighted, regular, ⟨stage, rfl⟩⟩ : Requests data weightedTarget remainderTarget floor) :=
  packaged_requests_factory data weightedTarget remainderTarget weightedPositive remainderPositive floor

/-- Compare the actual stored weighted table with its independently selected original observation.

The existing cell is consumed without refinement or power reconstruction.
Its stage must pay the actual new source request. That floor condition is
not inferred for a previously fixed cell whose stage is too early.
-/
def weightedSample (data : EndpointComparison.Data comparison overlap)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (tables : Tables retained)
    {target : Coordinate} {floor : Nat}
    (paid : CubicRequest data.owner.point (-cap.polynomial) (weightedChannel overlap) target floor)
    (later : paid.1.stage ≤ stage) (positive : 0 < target) :
    CubicSample paid retained tables.1.val (Tables.weighted_compiled retained tables point) :=
  CubicSample.build (parameter := parameter) (frame := frame) (cap := cap) (terminal := terminal)
    (preparation := preparation) (coordinate := coordinate) (stage := stage)
    paid retained tables.1.val (Tables.weighted_compiled retained tables point)
    (weightedEquivalent data paid.2.1) later data.inside positive

/-- Compare the actual stored lifted remainder to the independently retained ordinary remainder observation. -/
def remainderSample (data : EndpointComparison.Data comparison overlap)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (tables : Tables retained)
    {target : Coordinate} {floor : Nat}
    (paid : CubicRequest data.owner.point ((wRemainder (parameter := parameter)) *
      HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) (remainderChannel overlap) target floor)
    (later : paid.1.stage ≤ stage) (positive : 0 < target) :
    CubicSample paid retained tables.2.val (Tables.remainder_compiled retained tables point) :=
  CubicSample.build (parameter := parameter) (frame := frame) (cap := cap) (terminal := terminal)
    (preparation := preparation) (coordinate := coordinate) (stage := stage)
    paid retained tables.2.val (Tables.remainder_compiled retained tables point)
    (remainderEquivalent data paid.2.1) later data.inside positive

/-- The original weighted request and internally derived channel relation pay the actual finite weighted sample. -/
theorem weighted_error_le (data : EndpointComparison.Data comparison overlap)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (tables : Tables retained)
    {target : Coordinate} {floor : Nat}
    (paid : CubicRequest data.owner.point (-cap.polynomial) (weightedChannel overlap) target floor)
    (sample : CubicSample paid retained tables.1.val (Tables.weighted_compiled retained tables point)) :
    Norm.Basic.normSq (tables.1.val.eval point - paid.2.2.2.reading.value) ≤ target :=
  CubicSample.error_le paid retained tables.1.val (Tables.weighted_compiled retained tables point) sample

/-- The same retained cubic remainder table pays the actual independently observed ordinary regular remainder. -/
theorem remainder_error_le (data : EndpointComparison.Data comparison overlap)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (tables : Tables retained)
    {target : Coordinate} {floor : Nat}
    (paid : CubicRequest data.owner.point ((wRemainder (parameter := parameter)) *
      HyperellipticReciprocal.polynomial (Fibre.frameCurve frame)) (remainderChannel overlap) target floor)
    (sample : CubicSample paid retained tables.2.val (Tables.remainder_compiled retained tables point)) :
    Norm.Basic.normSq (tables.2.val.eval point - paid.2.2.2.reading.value) ≤ target :=
  CubicSample.error_le paid retained tables.2.val (Tables.remainder_compiled retained tables point) sample

/-- Actual weighted and remainder observations retain the finite density split with both independent errors paid. -/
theorem split_error_le (data : EndpointComparison.Data comparison overlap)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (tables : Tables retained)
    {weightedTarget remainderTarget : Coordinate} {weightedFloor remainderFloor : Nat}
    (weighted : CubicRequest data.owner.point (-cap.polynomial) (weightedChannel overlap) weightedTarget weightedFloor)
    (regular : CubicRequest data.owner.point ((wRemainder (parameter := parameter)) *
      HyperellipticReciprocal.polynomial (Fibre.frameCurve frame))
        (remainderChannel overlap) remainderTarget remainderFloor)
    (weightedSample : CubicSample weighted retained tables.1.val (Tables.weighted_compiled retained tables point))
    (regularSample : CubicSample regular retained tables.2.val (Tables.remainder_compiled retained tables point)) :
    Norm.Basic.normSq (2 * retained.density.eval point + regular.2.2.2.reading.value -
      weighted.2.2.2.reading.value) ≤ 2 * (weightedTarget + remainderTarget) := by
  have weightedBound := weighted_error_le data retained tables weighted weightedSample
  have remainderBound := remainder_error_le data retained tables regular regularSample
  have decomposition : 2 * retained.density.eval point + regular.2.2.2.reading.value -
      weighted.2.2.2.reading.value =
        (tables.1.val.eval point - weighted.2.2.2.reading.value) -
          (tables.2.val.eval point - regular.2.2.2.reading.value) := by
    have finiteSplit := Tables.split retained tables point
    rewrite [finiteSplit]
    ring1
  rewrite [decomposition]
  exact (Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct weightedBound remainderBound) (by decide +kernel))

/-- Both actual independently observed channels consume one and the same original retained model and cube. -/
@[expose] def Samples (data : EndpointComparison.Data comparison overlap)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (tables : Tables retained)
    {weightedTarget remainderTarget : Coordinate} {floor : Nat}
    (paid : Requests data weightedTarget remainderTarget floor) : Type _ :=
  CubicSample paid.2.1 retained tables.1.val (Tables.weighted_compiled retained tables point) ×
  CubicSample paid.2.2.1 retained tables.2.val (Tables.remainder_compiled retained tables point)

/-- Execute both requested original-root readings on the supplied unchanged shared inverse and cube caches. -/
def samples (data : EndpointComparison.Data comparison overlap)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (tables : Tables retained)
    {weightedTarget remainderTarget : Coordinate} {floor : Nat}
    (paid : Requests data weightedTarget remainderTarget floor) (later : paid.2.2.2.val ≤ stage)
    (weightedPositive : 0 < weightedTarget) (remainderPositive : 0 < remainderTarget) :
    Samples data retained tables paid :=
  let weighted := weightedSample data retained tables paid.2.1
    ((Data.Nat.Order.le_max_left _ _).trans (paid.2.2.2.property ▸ later)) weightedPositive
  let regular := remainderSample data retained tables paid.2.2.1
    ((Data.Nat.Order.le_max_right _ _).trans (paid.2.2.2.property ▸ later)) remainderPositive
  ⟨weighted, regular⟩

/-- Both actual sample factories consume the same retained cell, table cache and original requested floors. -/
private theorem packaged_samples_factory (data : EndpointComparison.Data comparison overlap)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (tables : Tables retained)
    {weightedTarget remainderTarget : Coordinate} {floor : Nat}
    (paid : Requests data weightedTarget remainderTarget floor) (later : paid.2.2.2.val ≤ stage)
    (weightedPositive : 0 < weightedTarget) (remainderPositive : 0 < remainderTarget) :
    samples data retained tables paid later weightedPositive remainderPositive =
      (let weighted := weightedSample data retained tables paid.2.1
         ((Data.Nat.Order.le_max_left _ _).trans (paid.2.2.2.property ▸ later)) weightedPositive
       let regular := remainderSample data retained tables paid.2.2.1
         ((Data.Nat.Order.le_max_right _ _).trans (paid.2.2.2.property ▸ later)) remainderPositive
       ⟨weighted, regular⟩ : Samples data retained tables paid) := by rfl

/-- Both actual sample factories consume the same retained cell, table cache and original requested floors. -/
theorem samples_factory (data : EndpointComparison.Data comparison overlap)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (tables : Tables retained)
    {weightedTarget remainderTarget : Coordinate} {floor : Nat}
    (paid : Requests data weightedTarget remainderTarget floor) (later : paid.2.2.2.val ≤ stage)
    (weightedPositive : 0 < weightedTarget) (remainderPositive : 0 < remainderTarget) :
    samples data retained tables paid later weightedPositive remainderPositive =
      (let weighted := weightedSample data retained tables paid.2.1
         ((Data.Nat.Order.le_max_left _ _).trans (paid.2.2.2.property ▸ later)) weightedPositive
       let regular := remainderSample data retained tables paid.2.2.1
         ((Data.Nat.Order.le_max_right _ _).trans (paid.2.2.2.property ▸ later)) remainderPositive
       ⟨weighted, regular⟩ : Samples data retained tables paid) :=
  packaged_samples_factory data retained tables paid later weightedPositive remainderPositive

/-- Choose the two actual independent payments before the shared original cell stage is fixed. -/
def splitRequest (data : EndpointComparison.Data comparison overlap)
    (target : Coordinate) (positive : 0 < target) (floor : Nat) :
    Requests data (target / 8) (target / 8) floor :=
  requests data (target / 8) (target / 8)
    (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
    (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) floor

/-- Actual original weighted and remainder readings pay the requested density split internally. -/
theorem accurate (data : EndpointComparison.Data comparison overlap)
    (retained : Cell preparation.2.1 coordinate stage allowance nonnegative) (tables : Tables retained)
    (target : Coordinate) (positive : 0 < target) (floor : Nat)
    (paid : Requests data (target / 8) (target / 8) floor) (observed : Samples data retained tables paid) :
    Norm.Basic.normSq (2 * retained.density.eval point + paid.2.2.1.2.2.2.reading.value -
      paid.2.1.2.2.2.reading.value) < target := by
  have bound := split_error_le data retained tables paid.2.1 paid.2.2.1 observed.1 observed.2
  have scalar : 2 * (target / 8 + target / 8) = target / 2 := by
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    have constant : 4 * (8 : Coordinate)⁻¹ = (2 : Coordinate)⁻¹ := by decide +kernel
    calc
      _ = target * (4 * (8 : Coordinate)⁻¹) := by ring1
      _ = _ := by rewrite [constant]; rfl
  have strict : target / 2 < target :=
    (Fraction.Order.Field.div_lt_iff_pos (by decide +kernel : (0 : Coordinate) < 2)).mpr (by
      have translated := Fraction.Order.Arithmetic.add_lt_add_right_direct positive target
      rewrite [Fraction.Field.zero_add] at translated
      exact translated.trans_eq (by ring1))
  exact (bound.trans_eq scalar).trans_lt strict

end Endpoints

end Cells

end Purelib.Curves.Legendre.Polynomial.Reciprocal.Potential

end
