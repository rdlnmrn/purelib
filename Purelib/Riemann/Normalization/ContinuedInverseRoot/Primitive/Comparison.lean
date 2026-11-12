module

public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Request
public import Purelib.Approximation.Gaussian.Equivalence.Observation
public import Purelib.Algebra.Quadratic.Pair.Gaussian.Observation.Precision
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Observation
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original primitive readings compared with retained bank readings

The actual source polynomial, its selected-root linear reading and the
original bank reading remain distinct. A finite operational comparison
between their original channels and the actual state radii pays the final
endpoint error; no polynomial-to-bank estimate is an input.
-/

public section

namespace Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Algebra.Quadratic.Pair.Gaussian (ReadingPrecision)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)

attribute [local irreducible] Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

variable {polynomial : Coefficients} {count : Nat} {patch : ContinuedNeighborhood polynomial count}
    {point : Canonical} {sample : Point patch point} {depth : Nat} {model : Model polynomial patch.base.box}
    {powers : OddPowers model.value} {reading : PrimitiveReading sample depth model powers}
    {pairs : Fin 3} {numerator : Coefficients} {original : PrimitiveDenotation sample pairs numerator}
    {source : Coefficients} {bankOwner : CoherentNamed} {target : Rational}

namespace PrimitiveValue

set_option genInjectivity false in
/-- A paid comparison of an actual source primitive polynomial with an original bank-channel reading.

The original polynomial cache, source point and linear denotation reading
are retained. The bank keeps its own original channel and actual requested
state; a finite operational comparison supplies both original tail indices. -/
structure Comparison (value : PrimitiveValue reading pairs numerator original source)
    (bank : Observation.Request bankOwner (target / 256)) where
  /-- The actual original source primitive value cache. -/
  sourceValue : PrimitiveValue reading pairs numerator original source
  /-- The retained value is the exact original source input. -/
  sourceValue_eq : sourceValue = value
  /-- The actual original bank-channel request and state. -/
  bankRequest : Observation.Request bankOwner (target / 256)
  /-- The retained bank request is the original input request. -/
  bankRequest_eq : bankRequest = bank
  /-- The original primitive channel's actual linear reading at the source's selected root state. -/
  localReading : Observation.Reading original.channel
  /-- The local observation reads the exact cached linear source value. -/
  localValue_eq : localReading.value = value.linear
  /-- The actual operational comparison between these two original possible readings. -/
  operational : Observation.Comparison localReading bank.reading (target / 64)
  /-- The cached polynomial-to-bank endpoint residual. -/
  residual : Canonical
  /-- The endpoint residual belongs to these exact original source and bank readings. -/
  residual_eq : residual = value.value - bank.reading.value
  /-- The actual cached polynomial-to-bank residual pays the original endpoint allocation. -/
  residual_le : Norm.Basic.normSq residual ≤ target

constructive_injectivity Comparison

/-- The original shared generator request controls the visible radius of a cached quadratic coefficient reading. -/
private theorem local_radius_payment {ceiling : Rational} (precision : ReadingPrecision ceiling (target / 16))
    (coefficient : Canonical) (coefficient_le : Norm.Basic.normSq coefficient ≤ ceiling) :
    8 * Norm.Basic.normSq coefficient * precision.target ≤ target / 256 := by
  have paid := precision.payment coefficient coefficient_le
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid
    (by decide +kernel : (0 : Rational) ≤ 1 / 8)
  calc
    _ = (1 / 8) * (64 * Norm.Basic.normSq coefficient * precision.target) := by
      have scalar : (1 / 8 : Rational) * 64 = 8 := by decide +kernel
      calc
        _ = ((1 / 8 : Rational) * 64) * Norm.Basic.normSq coefficient * precision.target := by
          rewrite [scalar]
          rfl
        _ = _ := by ring1
    _ ≤ (1 / 8) * ((target / 16) / 2) := scaled
    _ = _ := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
        Fraction.Field.div_eq_mul_inv_direct]
      have scalar : (8 : Rational)⁻¹ * (16 : Rational)⁻¹ * (2 : Rational)⁻¹ =
          (256 : Rational)⁻¹ := by decide +kernel
      calc
        _ = target * ((8 : Rational)⁻¹ * (16 : Rational)⁻¹ * (2 : Rational)⁻¹) := by
          rewrite [Fraction.Field.one_mul]
          ring1
        _ = _ := by rewrite [scalar]; rfl

/-- The two actual original state radii and retained tail target pay one quarter of the endpoint allocation. -/
private theorem operational_payment {left right : CoherentNamed}
    {leftReading : Observation.Reading left} {rightReading : Observation.Reading right}
    (comparison : Observation.Comparison leftReading rightReading (target / 64))
    (left_le : leftReading.radius ≤ target / 256) (right_le : rightReading.radius ≤ target / 256)
    (positive : 0 < target) : comparison.bound ≤ target / 4 := by
  rewrite [comparison.bound_eq]
  have summed := Order.Arithmetic.add_le_add_direct left_le right_le
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct summed (by decide +kernel : (0 : Rational) ≤ 16)
  calc
    _ ≤ 16 * (target / 256 + target / 256) + 4 * (target / 64) :=
      Order.Arithmetic.add_le_add_direct scaled (Order.Basic.le_refl _)
    _ = (3 / 16) * target := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
      have scalar : 32 * (256 : Rational)⁻¹ + 4 * (64 : Rational)⁻¹ = (3 / 16 : Rational) := by
        decide +kernel
      calc
        _ = (32 * (256 : Rational)⁻¹ + 4 * (64 : Rational)⁻¹) * target := by ring1
        _ = _ := by rewrite [scalar]; rfl
    _ ≤ (1 / 4) * target := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide +kernel) positive.le
    _ = _ := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
        Fraction.Field.one_mul]
      exact Fraction.Field.mul_comm _ _

/-- The actual source and original finite reading residuals control the original polynomial-to-bank residual. -/
private theorem endpoint_payment (value : PrimitiveValue reading pairs numerator original source)
    (bank : Observation.Request bankOwner (target / 256))
    {localReading : Observation.Reading original.channel}
    (same : localReading.value = value.linear)
    (comparison : Observation.Comparison localReading bank.reading (target / 64))
    (source_le : Norm.Basic.normSq value.residual ≤ target / 4)
    (comparison_le : comparison.bound ≤ target / 4) :
    Norm.Basic.normSq (value.value - bank.reading.value) ≤ target := by
  have readingBound := comparison.residual_le
  rewrite [comparison.residual_eq, same] at readingBound
  have originalBound := readingBound.trans comparison_le
  rewrite [value.residual_eq] at source_le
  have decomposition : value.value - bank.reading.value =
      (value.value - value.linear) + (value.linear - bank.reading.value) := by ring1
  rewrite [decomposition]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct source_le originalBound) (by decide)).trans_eq (by
        rewrite [Fraction.Field.div_eq_mul_inv_direct]
        have scalar : 4 * (4 : Rational)⁻¹ = 1 := by decide +kernel
        calc
          _ = target * (4 * (4 : Rational)⁻¹) := by ring1
          _ = _ := by rewrite [scalar, Fraction.Field.mul_one_direct]; rfl))

/-- Compare an actual source primitive with an original requested bank reading using the same selected root.

The source depth pays its original primitive request. The shared generator
precision pays the actual local visible radius, while the bank's retained
request pays its own radius. The supplied channel relation is interpreted
by its finite procedure; production branch admissions derive that relation
from original common-owner geometry. -/
def compare (value : PrimitiveValue reading pairs numerator original source)
    (bank : Observation.Request bankOwner (target / 256)) {ceiling : Rational}
    (precision : ReadingPrecision ceiling (target / 16))
    (root : PrimitiveRoot sample depth precision.target)
    (reading_eq : reading = root.readModel model reading.model_eq powers)
    (coefficient_le : Norm.Basic.normSq original.value.im ≤ ceiling)
    {floor : Nat} (request : PrimitiveRequest sample pairs numerator floor (target / 4))
    (inside : patch.box.Contains point) (stage : request.stage ≤ depth)
    (equivalent : NamedEquivalent original.channel.name bankOwner.name) (positive : 0 < target) :
    Comparison value bank := by
  have possible := original.reading_possible reading.state reading.root reading.possible
  rewrite [← value.linear_readback] at possible
  let localReading := Observation.Reading.retain original.channel
    (original.readingState reading.state) value.linear possible
  have state_eq : reading.state = root.state := by
    rewrite [reading_eq]
    exact root.readModel_state model reading.model_eq powers
  have radius := original.reading_radius reading.state
  have rootRadius := congrArg (fun state => 8 * Norm.Basic.normSq original.value.im *
    (sample.certificate.value.name.process.ball state).radiusSq) state_eq
  have radius_eq : localReading.radius = 8 * Norm.Basic.normSq original.value.im *
      (sample.certificate.value.name.process.ball root.state).radiusSq := radius.trans rootRadius
  have localBound : localReading.radius ≤ target / 256 := by
    rewrite [radius_eq]
    exact (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct root.radius_lt.le
      (Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _))).trans
      (local_radius_payment precision original.value.im coefficient_le)
  let tolerance := target / 64
  have tolerancePositive : 0 < tolerance := Order.Field.div_pos_direct positive (by decide +kernel)
  let operational := Observation.Comparison.build localReading bank.reading equivalent tolerance tolerancePositive
  have operationalBound := operational_payment operational localBound bank.radius_lt.le positive
  have sourceBound := (request.residual_lt value inside stage).le
  let residual := value.value - bank.reading.value
  exact ⟨value, rfl, bank, rfl, localReading, rfl, operational, residual, rfl,
    endpoint_payment value bank rfl operational sourceBound operationalBound⟩

/-- The paid original endpoint comparison reads the literal retained source polynomial and actual bank witness. -/
theorem Comparison.source_residual {value : PrimitiveValue reading pairs numerator original source}
    {bank : Observation.Request bankOwner (target / 256)} (comparison : Comparison value bank) :
    comparison.residual = source.eval point - bank.reading.value := by
  rewrite [comparison.residual_eq, value.value_eq, value.polynomial_eq]
  rfl

end PrimitiveValue

end Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

end
