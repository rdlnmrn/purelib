module

public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Comparison
public import Purelib.Approximation.AccuracyRequest
import Purelib.Algebra.Quadratic.Pair.Polynomial.Gaussian.Comparison
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Requested primitive endpoints on their original continued Points

The source request, exact denotation, generator precision and channel reading
are selected before a model depth is fixed. An actual later model supplies
its original inverse and power caches. Endpoint comparison uses the general
retained-expression comparison at the actual original root generators.
-/

public section

namespace Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Algebra.Quadratic.Pair.Gaussian (ReadingPrecision)
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Equivalence

variable {polynomial : Coefficients} {count : Nat}
    {patch : ContinuedNeighborhood polynomial count} {point : Canonical}

/-- A primitive source request, its original denotation, root precision and one requested reading of that channel.

The request is independent of any finite inverse-model depth. Its original
Point, numerator factor and exact denotation remain together, so later
sampling can consume the same caches without evaluating the numerator again.
-/
@[expose] def PrimitiveEndpoint (sample : Point patch point) (pairs : Fin 3)
    (numerator : Coefficients) (floor : Nat) (target : Rational) : Type _ :=
  (_source : PrimitiveRequest sample pairs numerator floor (target / 4)) ×
  (original : PrimitiveDenotation sample pairs numerator) ×
  (_precision : ReadingPrecision (Norm.Basic.normSq original.value.im) (target / 16)) ×
  Observation.Request original.channel (target / 256)

namespace PrimitiveEndpoint

/-- Request one primitive endpoint from the actual Point and its cached original numerator factor.

All four original values precede any later model or power construction.
The bank observation reads this retained denotation's own channel, without
acquiring another Point or selecting another source owner.
-/
def build (sample : Point patch point) (pairs : Fin 3) (numerator : Coefficients)
    (floor : Nat) (target : Rational) (positive : 0 < target) :
    PrimitiveEndpoint sample pairs numerator floor target :=
  let bounds := sample.primitiveBounds
  let source := bounds.request pairs numerator floor (target / 4)
    (Field.div_pos_direct positive (by decide +kernel))
  let original := retainPrimitiveDenotation sample bounds pairs numerator ⟨source.factor, source.factor_eq⟩
  let precision := ReadingPrecision.build (Norm.Basic.normSq original.value.im) (target / 16)
    (Norm.Basic.normSq_nonneg _) (Field.div_pos_direct positive (by decide +kernel))
  let observed := Observation.Request.build original.channel (target / 256)
    (Field.div_pos_direct positive (by decide +kernel))
  ⟨source, original, precision, observed⟩

variable {sample : Point patch point} {pairs : Fin 3} {numerator : Coefficients}
    {floor : Nat} {target : Rational}

/-- Read the original source request and its actual stage floor. -/
abbrev source (paid : PrimitiveEndpoint sample pairs numerator floor target) :
    PrimitiveRequest sample pairs numerator floor (target / 4) := paid.1

/-- Read the retained exact denotation without interpreting its expression again. -/
abbrev denotation (paid : PrimitiveEndpoint sample pairs numerator floor target) :
    PrimitiveDenotation sample pairs numerator := paid.2.1

/-- Read the original requested channel observation and its own state and radius. -/
abbrev observation (paid : PrimitiveEndpoint sample pairs numerator floor target) :
    Observation.Request paid.denotation.channel (target / 256) := paid.2.2.2

/-- The original shared root, same-model reading, actual polynomial value and its internally paid endpoint comparison.

The supplied compilation equation ties the original source polynomial to
the selected odd power of this exact model. The returned comparison retains
the original requested channel reading and charges the model's actual stage.
-/
@[expose] def Sample (paid : PrimitiveEndpoint sample pairs numerator floor target)
    {depth : Nat} (model : Model polynomial patch.base.box)
    (sameModel : model = patch.base.refine depth) (powers : OddPowers model.value)
    (source : Coefficients)
    (compiled : source.eval point = numerator.eval point * (primitivePolynomial powers pairs).eval point) : Type _ :=
  (root : PrimitiveRoot sample depth paid.2.2.1.target) ×
  (reading : { value : PrimitiveReading sample depth model powers //
    value = root.readModel model sameModel powers }) ×
  (value : { value : PrimitiveValue reading.val pairs numerator paid.denotation source //
    value = retainPrimitiveValue reading.val pairs numerator paid.denotation source compiled
      ⟨paid.source.factor, paid.source.factor_eq⟩ }) ×
  PrimitiveValue.Comparison value.val paid.observation

namespace Sample

/-- Retain abstract reading caches and their paid comparison on the same original endpoint request. -/
private def ofParts (paid : PrimitiveEndpoint sample pairs numerator floor target)
    {depth : Nat} (model : Model polynomial patch.base.box)
    (sameModel : model = patch.base.refine depth) (powers : OddPowers model.value)
    (source : Coefficients)
    (compiled : source.eval point = numerator.eval point * (primitivePolynomial powers pairs).eval point)
    (root : PrimitiveRoot sample depth paid.2.2.1.target)
    (reading : PrimitiveReading sample depth model powers)
    (readingEq : reading = root.readModel model sameModel powers)
    (value : PrimitiveValue reading pairs numerator paid.denotation source)
    (valueEq : value = retainPrimitiveValue reading pairs numerator paid.denotation source compiled
      ⟨paid.source.factor, paid.source.factor_eq⟩)
    (compared : PrimitiveValue.Comparison value paid.observation) :
    paid.Sample model sameModel powers source compiled :=
  ⟨root, ⟨reading, readingEq⟩, ⟨value, valueEq⟩, compared⟩

/-- Read one original root witness and compare the actual retained source polynomial at its sufficient model depth.

The model and its powers are supplied complete caches. The numerator factor,
denotation and requested bank reading are reused from the original request;
the original generic primitive comparison derives the endpoint error bound.
-/
def build (paid : PrimitiveEndpoint sample pairs numerator floor target)
    {depth : Nat} (model : Model polynomial patch.base.box)
    (sameModel : model = patch.base.refine depth) (powers : OddPowers model.value)
    (source : Coefficients)
    (compiled : source.eval point = numerator.eval point * (primitivePolynomial powers pairs).eval point)
    (inside : patch.box.Contains point) (later : paid.source.stage ≤ depth)
    (positive : 0 < target) :
    paid.Sample model sameModel powers source compiled :=
  let root := selectPrimitiveRoot sample depth paid.2.2.1.target paid.2.2.1.target_positive
  let reading := root.readModel model sameModel powers
  let value := retainPrimitiveValue reading pairs numerator paid.denotation source compiled
    ⟨paid.source.factor, paid.source.factor_eq⟩
  let compared := value.compare paid.observation paid.2.2.1 root rfl
    (Basic.le_refl _) paid.source inside later (NamedEquivalent.refl _) positive
  ofParts paid model sameModel powers source compiled root reading rfl value rfl compared

/-- The paid sample bounds the actual source polynomial against the unchanged requested observation. -/
theorem error_le (paid : PrimitiveEndpoint sample pairs numerator floor target)
    {depth : Nat} {model : Model polynomial patch.base.box}
    {sameModel : model = patch.base.refine depth} {powers : OddPowers model.value}
    {source : Coefficients}
    {compiled : source.eval point = numerator.eval point * (primitivePolynomial powers pairs).eval point}
    (retained : paid.Sample model sameModel powers source compiled) :
    Norm.Basic.normSq (source.eval point - paid.observation.reading.value) ≤ target := by
  have estimate := retained.2.2.2.residual_le
  rewrite [retained.2.2.2.source_residual] at estimate
  exact estimate

/-- Read the actual cached primitive scalar without evaluating the source polynomial again. -/
def value
    {paid : PrimitiveEndpoint sample pairs numerator floor target}
    {depth : Nat} {model : Model polynomial patch.base.box}
    {sameModel : model = patch.base.refine depth} {powers : OddPowers model.value}
    {source : Coefficients}
    {compiled : source.eval point = numerator.eval point * (primitivePolynomial powers pairs).eval point}
    (retained : paid.Sample model sameModel powers source compiled) : Canonical := retained.2.2.1.val.value

/-- The cached endpoint scalar is the original source polynomial evaluation at this same Point. -/
private theorem packaged_value_eq
    {paid : PrimitiveEndpoint sample pairs numerator floor target}
    {depth : Nat} {model : Model polynomial patch.base.box}
    {sameModel : model = patch.base.refine depth} {powers : OddPowers model.value}
    {source : Coefficients}
    {compiled : source.eval point = numerator.eval point * (primitivePolynomial powers pairs).eval point}
    (retained : paid.Sample model sameModel powers source compiled) :
    retained.value = source.eval point :=
  retained.2.2.1.val.value_eq.trans
    (congrArg (fun polynomial : Coefficients => polynomial.eval point) retained.2.2.1.val.polynomial_eq)

/-- The cached endpoint scalar is the original source polynomial evaluation at this same Point. -/
theorem value_eq
    {paid : PrimitiveEndpoint sample pairs numerator floor target}
    {depth : Nat} {model : Model polynomial patch.base.box}
    {sameModel : model = patch.base.refine depth} {powers : OddPowers model.value}
    {source : Coefficients}
    {compiled : source.eval point = numerator.eval point * (primitivePolynomial powers pairs).eval point}
    (retained : paid.Sample model sameModel powers source compiled) :
    retained.value = source.eval point := packaged_value_eq retained

variable {depth : Nat} {model : Model polynomial patch.base.box}
    {sameModel : model = patch.base.refine depth} {powers : OddPowers model.value}
    {source : Coefficients}
    {compiled : source.eval point = numerator.eval point * (primitivePolynomial powers pairs).eval point}
    {otherCount : Nat} {otherPatch : ContinuedNeighborhood polynomial otherCount}
    {otherSample : Point otherPatch point} {otherFloor otherDepth : Nat}
    {otherModel : Model polynomial otherPatch.base.box}
    {otherSameModel : otherModel = otherPatch.base.refine otherDepth}
    {otherPowers : OddPowers otherModel.value} {otherSource : Coefficients}
    {otherCompiled : otherSource.eval point =
      numerator.eval point * (primitivePolynomial otherPowers pairs).eval point}

/-- Both actual endpoint residuals and the retained observation comparison bound the original polynomial difference.

Each requested observation keeps its own Point, channel and radius. The
finite comparison target is one sixty-fourth of the common endpoint budget;
the original generic reading estimate pays the middle discrepancy.
-/
theorem difference_le (paid : PrimitiveEndpoint sample pairs numerator floor target)
    (other : PrimitiveEndpoint otherSample pairs numerator otherFloor target)
    (first : paid.Sample model sameModel powers source compiled)
    (last : other.Sample otherModel otherSameModel otherPowers otherSource otherCompiled)
    (compared : Observation.Comparison paid.observation.reading other.observation.reading (target / 64))
    (nonnegative : 0 ≤ target) :
    Norm.Basic.normSq (source.eval point - otherSource.eval point) ≤ 7 * target := by
  have observations := compared.requested_error_lt paid.observation other.observation
  have scalar : 16 * (target / 256 + target / 256) + 4 * (target / 64) = (3 / 16) * target := by
    repeat rewrite [Fraction.Field.div_eq_mul_inv_direct]
    have coefficient : 16 * ((256 : Rational)⁻¹ + (256 : Rational)⁻¹) +
        4 * (64 : Rational)⁻¹ = 3 * (16 : Rational)⁻¹ := by decide +kernel
    calc
      _ = (16 * ((256 : Rational)⁻¹ + (256 : Rational)⁻¹) + 4 * (64 : Rational)⁻¹) * target := by
        ring1
      _ = _ := by rewrite [coefficient]; rfl
  have middleBound : Norm.Basic.normSq
      (paid.observation.reading.value - other.observation.reading.value) ≤ target / 4 := by
    have ordered := Arithmetic.mul_le_mul_of_nonneg_right_direct
      (by decide +kernel : (3 / 16 : Rational) ≤ 1 / 4) nonnegative
    have quarter : (1 / 4 : Rational) * target = target / 4 := by
      repeat rewrite [Fraction.Field.div_eq_mul_inv_direct]
      rewrite [Fraction.Field.one_mul]
      exact Fraction.Field.mul_comm _ _
    exact observations.le.trans (scalar.trans_le (ordered.trans_eq quarter))
  have lastBound := (Norm.Bounds.normSq_sub_symm other.observation.reading.value
    (otherSource.eval point)).trans_le (error_le other last)
  have tailBound := (Norm.Bounds.normSq_sub_le_via paid.observation.reading.value
    other.observation.reading.value (otherSource.eval point)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct middleBound lastBound) (by decide +kernel))
  have bound := (Norm.Bounds.normSq_sub_le_via (source.eval point)
    paid.observation.reading.value (otherSource.eval point)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct (error_le paid first) tailBound) (by decide +kernel))
  apply bound.trans_eq
  rewrite [Fraction.Field.div_eq_mul_inv_direct]
  have coefficient : 4 * (4 : Rational)⁻¹ + 6 = 7 := by decide +kernel
  calc
    _ = (4 * (4 : Rational)⁻¹ + 6) * target := by ring1
    _ = _ := by rewrite [coefficient]; rfl

/-- Compare the actual endpoint observations and internally pay the original potential-polynomial difference.

The only supplied relation is agreement of the two original root
generators. Both endpoint residuals and the new finite observation
comparison are charged, yielding a strict eight-budget bound.
-/
def compare (paid : PrimitiveEndpoint sample pairs numerator floor target)
    (other : PrimitiveEndpoint otherSample pairs numerator otherFloor target)
    (first : paid.Sample model sameModel powers source compiled)
    (last : other.Sample otherModel otherSameModel otherPowers otherSource otherCompiled)
    (generators : NamedEquivalent sample.certificate.value.name otherSample.certificate.value.name)
    (positive : 0 < target) :
    { _compared : Observation.Comparison paid.observation.reading other.observation.reading (target / 64) //
      Norm.Basic.normSq (source.eval point - otherSource.eval point) < 8 * target } :=
  let request : AccuracyRequest := ⟨target / 64, Field.div_pos_direct positive (by decide +kernel)⟩
  let compared := paid.denotation.compare other.denotation generators
    paid.observation.reading other.observation.reading request
  ⟨compared, (difference_le paid other first last compared positive.le).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_right_direct (by decide +kernel : (7 : Rational) < 8) positive)⟩

end Sample

/-- Compare both unchanged endpoint observations through the actual original generator agreement.

The endpoints may belong to different continued neighborhoods and have
different model floors and target allocations. The common expression and
coordinate, together with the supplied root relation, are the exact inputs
to the existing general retained-denotation comparison.
-/
def compare {otherCount : Nat} {otherPatch : ContinuedNeighborhood polynomial otherCount}
    {otherSample : Point otherPatch point} {otherFloor : Nat} {otherTarget : Rational}
    (first : PrimitiveEndpoint sample pairs numerator floor target)
    (last : PrimitiveEndpoint otherSample pairs numerator otherFloor otherTarget)
    (generators : NamedEquivalent sample.certificate.value.name otherSample.certificate.value.name)
    (request : AccuracyRequest) :
    Observation.Comparison first.observation.reading last.observation.reading request.tolerance :=
  first.denotation.compare last.denotation generators first.observation.reading last.observation.reading request

end PrimitiveEndpoint

end Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

end
