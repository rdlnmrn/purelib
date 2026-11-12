module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices
public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Comparison
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Gaussian.Norm.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original source endpoint plans and bank comparisons

The primitive requests and shared root precision are selected before the
inverse model. Attaching them reads the actual source tables once, and a
common-owner branch admission derives their finite bank comparisons.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point
open Purelib.Algebra.Quadratic.Pair.Gaussian (ReadingPrecision)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)

attribute [local irreducible] Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

variable {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {point : Canonical}

namespace EndpointRequests

/-- Select the three original endpoint depths using the retained vertex's exact bounds, factors and quadrances.

The actual parameter reciprocal, primitive scales, numerator values and
their norms are consumed directly from the original vertex cache. Only
the new finite request scales and depth selections are constructed. -/
@[expose] def ofVertex {vertexPoint : LiftedPoint 2} (original : Vertex parameter vertexPoint)
    (floor : Nat) (target : Rational) (positive : 0 < target) :
    EndpointRequests original.sample floor target :=
  let zero := original.bounds.requestFromFactor 0 PicardFuchs.Polynomials.firstPrimitivePolynomial
    ⟨original.zeroFactor, original.zeroFactor_eq⟩ ⟨original.zeroNorm, original.zeroNorm_eq⟩ floor target positive
  let one := original.bounds.requestFromFactor 0 (PicardFuchs.Polynomials.secondPrimitivePolynomial parameter)
    ⟨original.oneFactor, original.oneFactor_eq⟩ ⟨original.oneNorm, original.oneNorm_eq⟩ floor target positive
  let scalar := original.bounds.requestFromFactor 1 PicardFuchs.Polynomials.picardFuchsPrimitivePolynomial
    ⟨original.scalarFactor, original.scalarFactor_eq⟩
    ⟨original.scalarNorm, original.scalarNorm_eq⟩ floor target positive
  let stage := max zero.stage (max one.stage scalar.stage)
  ⟨original.bounds, zero, rfl, one, rfl, scalar, rfl, stage, rfl⟩

end EndpointRequests

set_option genInjectivity false in
/-- The original three primitive requests and one shared root precision at a source endpoint.

The numerator requests retain their actual factors and chosen depth floors
before any refined inverse polynomial is constructed. The three original
denotations determine one cached imaginary-coefficient ceiling for the
same selected generator's finite root request. -/
structure EndpointPlan (sample : ContinuedNeighborhood.Point patch point) (floor : Nat) (allocation : Rational) where
  /-- The first primitive at the original source point and selected generator. -/
  zero : ZeroDenotation sample
  /-- The second primitive at that same original point and generator. -/
  one : OneDenotation sample
  /-- The scalar primitive at that same original point and generator. -/
  scalar : ScalarDenotation sample
  /-- The cached sum of the three actual imaginary-coefficient quadrances. -/
  ceiling : Rational
  /-- The ceiling consumes the actual retained original divided coefficient caches. -/
  ceiling_eq : ceiling = Norm.Basic.normSq zero.value.im +
    (Norm.Basic.normSq one.value.im + Norm.Basic.normSq scalar.value.im)
  /-- The actual primitive depth requests at one quarter of the endpoint allocation. -/
  requests : EndpointRequests sample floor (allocation / 4)
  /-- The single original generator request at one sixteenth of the endpoint allocation. -/
  precision : ReadingPrecision ceiling (allocation / 16)

namespace Vertex

/-- The first original divided coefficient's norm reads the actual retained factor and reciprocal norm caches. -/
private theorem zero_norm {vertexPoint : LiftedPoint 2} (original : Vertex parameter vertexPoint) :
    Norm.Basic.normSq original.zero.value.im = original.zeroNorm * original.bounds.inverseNorm := by
  have norm := original.zero.imaginary_norm original.bounds
  change Norm.Basic.normSq original.zero.value.im =
    Norm.Basic.normSq (PicardFuchs.Polynomials.firstPrimitivePolynomial.eval vertexPoint.coordinate) *
      original.bounds.inverseNorm ^ 1 at norm
  rewrite [pow_one, ← original.zeroFactor_eq, ← original.zeroNorm_eq] at norm
  exact norm

/-- The second original divided coefficient's norm reads the same original reciprocal cache. -/
private theorem one_norm {vertexPoint : LiftedPoint 2} (original : Vertex parameter vertexPoint) :
    Norm.Basic.normSq original.one.value.im = original.oneNorm * original.bounds.inverseNorm := by
  have norm := original.one.imaginary_norm original.bounds
  change Norm.Basic.normSq original.one.value.im =
    Norm.Basic.normSq ((PicardFuchs.Polynomials.secondPrimitivePolynomial parameter).eval vertexPoint.coordinate) *
      original.bounds.inverseNorm ^ 1 at norm
  rewrite [pow_one, ← original.oneFactor_eq, ← original.oneNorm_eq] at norm
  exact norm

/-- The original cubic coefficient's norm reads the retained numerator norm and reciprocal square. -/
private theorem scalar_norm {vertexPoint : LiftedPoint 2} (original : Vertex parameter vertexPoint) :
    Norm.Basic.normSq original.scalar.value.im = original.scalarNorm *
      (original.bounds.inverseNorm * original.bounds.inverseNorm) := by
  have norm := original.scalar.imaginary_norm original.bounds
  change Norm.Basic.normSq original.scalar.value.im =
    Norm.Basic.normSq (PicardFuchs.Polynomials.picardFuchsPrimitivePolynomial.eval vertexPoint.coordinate) *
      original.bounds.inverseNorm ^ 2 at norm
  rewrite [pow_two, ← original.scalarFactor_eq, ← original.scalarNorm_eq] at norm
  exact norm

end Vertex

namespace EndpointPlan

variable {sample : ContinuedNeighborhood.Point patch point} {floor : Nat} {allocation : Rational}

/-- Prepare paid endpoint depths and one root precision from the exact retained original vertex caches. -/
def ofVertex {vertexPoint : LiftedPoint 2} (original : Vertex parameter vertexPoint)
    (floor : Nat) (allocation : Rational) (positive : 0 < allocation) :
    EndpointPlan original.sample floor allocation :=
  let inverseSquare := original.bounds.inverseNorm * original.bounds.inverseNorm
  let ceiling := original.zeroNorm * original.bounds.inverseNorm +
    (original.oneNorm * original.bounds.inverseNorm + original.scalarNorm * inverseSquare)
  have ceiling_eq : ceiling = Norm.Basic.normSq original.zero.value.im +
      (Norm.Basic.normSq original.one.value.im + Norm.Basic.normSq original.scalar.value.im) := by
    rewrite [original.zero_norm, original.one_norm, original.scalar_norm]
    rfl
  have nonnegative : 0 ≤ ceiling := by
    rewrite [ceiling_eq]
    exact add_nonneg (Norm.Basic.normSq_nonneg _)
      (add_nonneg (Norm.Basic.normSq_nonneg _) (Norm.Basic.normSq_nonneg _))
  let requests := EndpointRequests.ofVertex original floor (allocation / 4)
    (Order.Field.div_pos_direct positive (by decide))
  let precision := ReadingPrecision.build ceiling (allocation / 16) nonnegative
    (Order.Field.div_pos_direct positive (by decide))
  ⟨original.zero, original.one, original.scalar, ceiling, ceiling_eq, requests, precision⟩

/-- The vertex plan retains the exact original first primitive denotation cache. -/
theorem ofVertex_zero {vertexPoint : LiftedPoint 2} (original : Vertex parameter vertexPoint)
    (floor : Nat) (allocation : Rational) (positive : 0 < allocation) :
    (ofVertex original floor allocation positive).zero = original.zero := by
  unfold ofVertex
  rfl

/-- The vertex plan retains the exact original second primitive denotation cache. -/
theorem ofVertex_one {vertexPoint : LiftedPoint 2} (original : Vertex parameter vertexPoint)
    (floor : Nat) (allocation : Rational) (positive : 0 < allocation) :
    (ofVertex original floor allocation positive).one = original.one := by
  unfold ofVertex
  rfl

/-- The vertex plan retains the exact original scalar primitive denotation cache. -/
theorem ofVertex_scalar {vertexPoint : LiftedPoint 2} (original : Vertex parameter vertexPoint)
    (floor : Nat) (allocation : Rational) (positive : 0 < allocation) :
    (ofVertex original floor allocation positive).scalar = original.scalar := by
  unfold ofVertex
  rfl

/-- The vertex plan's three requests consume the actual original scalar bound cache. -/
theorem ofVertex_bounds {vertexPoint : LiftedPoint 2} (original : Vertex parameter vertexPoint)
    (floor : Nat) (allocation : Rational) (positive : 0 < allocation) :
    (ofVertex original floor allocation positive).requests.bounds = original.bounds := by
  unfold ofVertex
  rfl

/-- The first actual imaginary coefficient lies below the retained shared ceiling. -/
theorem zero_le (plan : EndpointPlan sample floor allocation) :
    Norm.Basic.normSq plan.zero.value.im ≤ plan.ceiling := by
  rewrite [plan.ceiling_eq]
  exact le_add_of_nonneg_right (add_nonneg (Norm.Basic.normSq_nonneg _) (Norm.Basic.normSq_nonneg _))

/-- The second actual imaginary coefficient lies below that same retained shared ceiling. -/
theorem one_le (plan : EndpointPlan sample floor allocation) : Norm.Basic.normSq plan.one.value.im ≤ plan.ceiling := by
  rewrite [plan.ceiling_eq]
  exact (le_add_of_nonneg_right (Norm.Basic.normSq_nonneg _)).trans
    (le_add_of_nonneg_left (Norm.Basic.normSq_nonneg _))

/-- The scalar primitive's actual imaginary coefficient lies below that same retained shared ceiling. -/
theorem scalar_le (plan : EndpointPlan sample floor allocation) :
    Norm.Basic.normSq plan.scalar.value.im ≤ plan.ceiling := by
  rewrite [plan.ceiling_eq]
  exact (le_add_of_nonneg_left (Norm.Basic.normSq_nonneg _)).trans
    (le_add_of_nonneg_left (Norm.Basic.normSq_nonneg _))

set_option genInjectivity false in
/-- A prepared endpoint on one actual source model, retaining one original root witness for all primitives. -/
structure Attachment (plan : EndpointPlan sample floor allocation) {cache : Cache patch}
    {current : Nat} {target : Rational} (request : Request cache current target) where
  /-- The actual original root request at this common model's selected depth. -/
  root : PrimitiveRoot sample request.selection.stage plan.precision.target
  /-- The original three primitive values on the same model and root caches. -/
  endpoint : Request.Endpoint request sample plan.requests root plan.zero plan.one plan.scalar

/-- Attach a prepared original endpoint to the actual common model and compute one requested shared root witness. -/
def attach (plan : EndpointPlan sample floor allocation) {cache : Cache patch}
    {current : Nat} {target : Rational} (request : Request cache current target)
    (stage : plan.requests.stage ≤ request.selection.stage) : Attachment plan request :=
  let retained := selectPrimitiveRoot plan.requests.bounds.owner request.selection.stage
    plan.precision.target plan.precision.target_positive
  let root := retained.castOwner plan.requests.bounds.owner_eq
  let endpoint := request.attachEndpoint sample plan.requests root plan.zero plan.one plan.scalar stage
  ⟨root, endpoint⟩

namespace Attachment

variable {plan : EndpointPlan sample floor allocation} {cache : Cache patch} {current : Nat} {target : Rational}
    {request : Request cache current target} {vertex : LiftedPoint 2}

set_option genInjectivity false in
/-- The original three source primitive values compared with one retained bank vertex's actual readings. -/
structure Comparison (attached : Attachment plan request) (bank : Vertex parameter vertex)
    (readings : Vertex.Readings bank allocation) where
  /-- The first actual source-table comparison with the first bank-channel reading. -/
  zero : PrimitiveValue.Comparison attached.endpoint.zero readings.zero
  /-- The second actual source-table comparison with the second bank-channel reading. -/
  one : PrimitiveValue.Comparison attached.endpoint.one readings.one
  /-- The actual cubic source-table comparison with the scalar bank-channel reading. -/
  scalar : PrimitiveValue.Comparison attached.endpoint.scalar readings.scalar

/-- Derive all three literal source endpoint errors from a common-owner geometric branch admission. -/
def compare {vertex : LiftedPoint 2} {sample : ContinuedNeighborhood.Point patch vertex.coordinate}
    {plan : EndpointPlan sample floor allocation} (attached : Attachment plan request)
    (bank : Vertex parameter vertex) (readings : Vertex.Readings bank allocation)
    (branch : RootBranch sample bank.sample) (inside : patch.box.Contains vertex.coordinate)
    (positive : 0 < allocation) : Comparison attached bank readings := by
  let endpoint := attached.endpoint
  let zero := endpoint.zero.compare readings.zero plan.precision attached.root endpoint.reading_eq plan.zero_le
    plan.requests.zero inside (plan.requests.zero_stage_le.trans endpoint.stage_ge)
    (branch.denotationEquivalent _ plan.zero bank.zero) positive
  let one := endpoint.one.compare readings.one plan.precision attached.root endpoint.reading_eq plan.one_le
    plan.requests.one inside (plan.requests.one_stage_le.trans endpoint.stage_ge)
    (branch.denotationEquivalent _ plan.one bank.one) positive
  let scalar := endpoint.scalar.compare readings.scalar plan.precision attached.root endpoint.reading_eq plan.scalar_le
    plan.requests.scalar inside (plan.requests.scalar_stage_le.trans endpoint.stage_ge)
    (branch.denotationEquivalent _ plan.scalar bank.scalar) positive
  exact ⟨zero, one, scalar⟩

/-- The first comparison pays the literal original first primitive table's endpoint error. -/
theorem Comparison.zero_le {attached : Attachment plan request} {bank : Vertex parameter vertex}
    {readings : Vertex.Readings bank allocation} (comparison : Comparison attached bank readings) :
    Norm.Basic.normSq (request.models.primitiveZero.eval point - readings.zero.reading.value) ≤ allocation := by
  have bound := comparison.zero.residual_le
  rewrite [comparison.zero.source_residual] at bound
  exact bound

/-- The second comparison pays the literal original second primitive table's endpoint error. -/
theorem Comparison.one_le {attached : Attachment plan request} {bank : Vertex parameter vertex}
    {readings : Vertex.Readings bank allocation} (comparison : Comparison attached bank readings) :
    Norm.Basic.normSq (request.models.primitiveOne.eval point - readings.one.reading.value) ≤ allocation := by
  have bound := comparison.one.residual_le
  rewrite [comparison.one.source_residual] at bound
  exact bound

/-- The scalar comparison pays the literal original cubic primitive table's endpoint error. -/
theorem Comparison.scalar_le {attached : Attachment plan request} {bank : Vertex parameter vertex}
    {readings : Vertex.Readings bank allocation} (comparison : Comparison attached bank readings) :
    Norm.Basic.normSq (request.models.scalarPrimitive.eval point - readings.scalar.reading.value) ≤ allocation := by
  have bound := comparison.scalar.residual_le
  rewrite [comparison.scalar.source_residual] at bound
  exact bound

end Attachment

end EndpointPlan

end Purelib.Curves.Legendre.Periods.Jets.Source

end
