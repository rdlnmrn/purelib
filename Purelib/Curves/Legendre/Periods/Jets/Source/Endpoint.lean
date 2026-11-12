module

public import Purelib.Curves.Legendre.Periods.Jets.Source
public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Request
import Purelib.Curves.Legendre.PicardFuchs.Polynomials
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original Legendre source endpoint attachments

The three exact primitive endpoint requests are chosen before the common
Newton model. Their actual numerator factors, denotations and shared root
witness attach to the same source model's retained primitive tables.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data.Nat

variable {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {point : Canonical}

/-- The original first connection primitive denotation at the same continued point and selected root. -/
abbrev ZeroDenotation (sample : ContinuedNeighborhood.Point patch point) :=
  PrimitiveDenotation sample 0 Polynomials.firstPrimitivePolynomial

/-- The original second connection primitive denotation at that same point and selected root. -/
abbrev OneDenotation (sample : ContinuedNeighborhood.Point patch point) :=
  PrimitiveDenotation sample 0 (Polynomials.secondPrimitivePolynomial parameter)

/-- The original scalar Picard–Fuchs primitive denotation at that same point and selected root. -/
abbrev ScalarDenotation (sample : ContinuedNeighborhood.Point patch point) :=
  PrimitiveDenotation sample 1 Polynomials.picardFuchsPrimitivePolynomial

set_option genInjectivity false in
/-- The three paid primitive endpoint requests on one original Legendre continued point.

All three requests consume the same retained scalar bound cache. Their
original numerator factors and exact target payments remain separate;
the maximum stage is selected before building a common Newton model. -/
structure EndpointRequests (sample : ContinuedNeighborhood.Point patch point) (floor : Nat) (target : Rational) where
  /-- The shared original point's cached scalar primitive bound factors. -/
  bounds : PrimitiveBounds sample
  /-- The first original connection primitive's retained numerator and payment. -/
  zero : PrimitiveRequest sample 0 Polynomials.firstPrimitivePolynomial floor target
  /-- The first request consumes the same retained original bound cache. -/
  zero_bounds : zero.bounds = bounds
  /-- The second original connection primitive's retained numerator and payment. -/
  one : PrimitiveRequest sample 0 (Polynomials.secondPrimitivePolynomial parameter) floor target
  /-- The second request consumes the same actual cached factors. -/
  one_bounds : one.bounds = bounds
  /-- The original scalar primitive's retained numerator and cubic reading payment. -/
  scalar : PrimitiveRequest sample 1 Polynomials.picardFuchsPrimitivePolynomial floor target
  /-- The scalar request consumes the same actual cached bound factors. -/
  scalar_bounds : scalar.bounds = bounds
  /-- The maximum required original endpoint stage retained as executable data. -/
  stage : Nat
  /-- The common endpoint stage is exactly the maximum of these three original request stages. -/
  stage_eq : stage = max zero.stage (max one.stage scalar.stage)

constructive_injectivity EndpointRequests

/-- Cache the three original primitive endpoint requests and their common finite floor before refining any model. -/
@[expose] def endpointRequests (sample : ContinuedNeighborhood.Point patch point) (floor : Nat)
    (target : Rational) (positive : 0 < target) : EndpointRequests sample floor target :=
  let bounds := sample.primitiveBounds
  let zero := bounds.request 0 Polynomials.firstPrimitivePolynomial floor target positive
  let one := bounds.request 0 (Polynomials.secondPrimitivePolynomial parameter) floor target positive
  let scalar := bounds.request 1 Polynomials.picardFuchsPrimitivePolynomial floor target positive
  let stage := max zero.stage (max one.stage scalar.stage)
  ⟨bounds, zero, rfl, one, rfl, scalar, rfl, stage, rfl⟩

namespace EndpointRequests

/-- The first actual primitive request is paid above the retained common endpoint stage. -/
theorem zero_stage_le {sample : ContinuedNeighborhood.Point patch point} {floor : Nat} {target : Rational}
    (requests : EndpointRequests sample floor target) : requests.zero.stage ≤ requests.stage := by
  rewrite [requests.stage_eq]
  exact Order.le_max_left _ _

/-- The second actual primitive request is paid above that same common endpoint stage. -/
theorem one_stage_le {sample : ContinuedNeighborhood.Point patch point} {floor : Nat} {target : Rational}
    (requests : EndpointRequests sample floor target) : requests.one.stage ≤ requests.stage := by
  rewrite [requests.stage_eq]
  exact (Order.le_max_left _ _).trans (Order.le_max_right _ _)

/-- The original scalar request is paid above the retained common endpoint stage. -/
theorem scalar_stage_le {sample : ContinuedNeighborhood.Point patch point} {floor : Nat} {target : Rational}
    (requests : EndpointRequests sample floor target) : requests.scalar.stage ≤ requests.stage := by
  rewrite [requests.stage_eq]
  exact (Order.le_max_right _ _).trans (Order.le_max_right _ _)

end EndpointRequests

namespace Request

variable {current : Nat} {target : Rational} {cache : Cache patch}

/-- The source-owned first primitive endpoint value type on the actual shared source model and point witness. -/
abbrev ZeroValue (request : Request cache current target) {sample : ContinuedNeighborhood.Point patch point}
    (reading : PrimitiveReading sample request.selection.stage request.model request.models.powers)
    (original : ZeroDenotation sample) :=
  PrimitiveValue reading 0 Polynomials.firstPrimitivePolynomial original request.models.primitiveZero

/-- The source-owned second primitive endpoint value type on that same actual shared model. -/
abbrev OneValue (request : Request cache current target) {sample : ContinuedNeighborhood.Point patch point}
    (reading : PrimitiveReading sample request.selection.stage request.model request.models.powers)
    (original : OneDenotation sample) :=
  PrimitiveValue reading 0 (Polynomials.secondPrimitivePolynomial parameter) original request.models.primitiveOne

/-- The original scalar endpoint value type consuming this exact source model's retained cube. -/
abbrev ScalarValue (request : Request cache current target) {sample : ContinuedNeighborhood.Point patch point}
    (reading : PrimitiveReading sample request.selection.stage request.model request.models.powers)
    (original : ScalarDenotation sample) :=
  PrimitiveValue reading 1 Polynomials.picardFuchsPrimitivePolynomial original request.models.scalarPrimitive

set_option genInjectivity false in
/-- The original source model's three primitive endpoint observations at one externally shared actual root witness.

The original request, point, root state and three denotations remain retained.
The original compiled primitive tables are reused; their scalar observations
consume the one shared inverse-model power reading and cached request factors. -/
structure Endpoint (request : Request cache current target) (sample : ContinuedNeighborhood.Point patch point)
    {floor : Nat} {endpointTarget semanticTarget : Rational}
    (requests : EndpointRequests sample floor endpointTarget)
    (root : PrimitiveRoot sample request.selection.stage semanticTarget)
    (zeroOriginal : ZeroDenotation sample) (oneOriginal : OneDenotation sample)
    (scalarOriginal : ScalarDenotation sample) where
  /-- The actual original common source request retained as executable data. -/
  owner : Request cache current target
  /-- The retained source request is the original source owner. -/
  owner_eq : owner = request
  /-- The actual externally shared original root witness and semantic request cache. -/
  sharedRoot : PrimitiveRoot sample request.selection.stage semanticTarget
  /-- The retained root witness is the original supplied shared witness. -/
  sharedRoot_eq : sharedRoot = root
  /-- The one retained scalar readback of the actual original model and shared odd-power cache. -/
  reading : PrimitiveReading sample request.selection.stage request.model request.models.powers
  /-- The retained model reading consumes that exact original root witness and source cache. -/
  reading_eq : reading = root.readModel request.model request.model_eq request.models.powers
  /-- The original common model stage pays all retained primitive endpoint requests. -/
  stage_ge : requests.stage ≤ request.selection.stage
  /-- The first original primitive's cached scalar observations and denotation comparison residual. -/
  zero : ZeroValue request reading zeroOriginal
  /-- The second original primitive's cached observations on that same shared root witness. -/
  one : OneValue request reading oneOriginal
  /-- The original scalar primitive's cached cubic observations on that same shared witness. -/
  scalar : ScalarValue request reading scalarOriginal

constructive_injectivity Endpoint

/-- Attach the original three primitive tables to the same shared root and source-model caches.

All three scalar numerator factors come from the original paid requests.
No primitive polynomial is reevaluated, and no independent root or model is
constructed for another row. -/
@[noinline, nospecialize] def attachEndpoint (request : Request cache current target)
    (sample : ContinuedNeighborhood.Point patch point) {floor : Nat} {endpointTarget semanticTarget : Rational}
    (requests : EndpointRequests sample floor endpointTarget)
    (root : PrimitiveRoot sample request.selection.stage semanticTarget)
    (zeroOriginal : ZeroDenotation sample) (oneOriginal : OneDenotation sample)
    (scalarOriginal : ScalarDenotation sample) (stage : requests.stage ≤ request.selection.stage) :
    Endpoint request sample requests root zeroOriginal oneOriginal scalarOriginal :=
  let reading := root.readModel request.model request.model_eq request.models.powers
  let zero := retainPrimitiveValue reading 0 Polynomials.firstPrimitivePolynomial zeroOriginal
    request.models.primitiveZero
    (by rewrite [request.models.primitiveZero_eq,
      Polynomial.Dense.Basic.DensePolynomial.eval_mul]; rfl) ⟨requests.zero.factor, requests.zero.factor_eq⟩
  let one := retainPrimitiveValue reading 0 (Polynomials.secondPrimitivePolynomial parameter) oneOriginal
    request.models.primitiveOne
    (by rewrite [request.models.primitiveOne_eq,
      Polynomial.Dense.Basic.DensePolynomial.eval_mul]; rfl) ⟨requests.one.factor, requests.one.factor_eq⟩
  let scalar := retainPrimitiveValue reading 1 Polynomials.picardFuchsPrimitivePolynomial scalarOriginal
    request.models.scalarPrimitive
    (by rewrite [request.models.scalarPrimitive_eq,
      Polynomial.Dense.Basic.DensePolynomial.eval_mul]; rfl) ⟨requests.scalar.factor, requests.scalar.factor_eq⟩
  ⟨request, rfl, root, rfl, reading, rfl, stage, zero, one, scalar⟩

namespace Endpoint

variable {request : Request cache current target} {sample : ContinuedNeighborhood.Point patch point}
    {floor : Nat} {endpointTarget semanticTarget : Rational}
    {requests : EndpointRequests sample floor endpointTarget}
    {root : PrimitiveRoot sample request.selection.stage semanticTarget}
    {zeroOriginal : ZeroDenotation sample} {oneOriginal : OneDenotation sample}
    {scalarOriginal : ScalarDenotation sample}

/-- The shared source-model observation retains the actual supplied endpoint root witness. -/
theorem root_readback (endpoint : Endpoint request sample requests root zeroOriginal oneOriginal scalarOriginal) :
    endpoint.reading.root = root.root :=
  (congrArg (fun reading => reading.root) endpoint.reading_eq).trans
    (root.readModel_root request.model request.model_eq request.models.powers)

/-- The first original denotation is read at the one supplied root witness. -/
theorem zero_linear (endpoint : Endpoint request sample requests root zeroOriginal oneOriginal scalarOriginal) :
    endpoint.zero.linear = zeroOriginal.value.re + zeroOriginal.value.im * root.root := by
  have reading := endpoint.zero.linear_readback
  rewrite [endpoint.root_readback] at reading
  exact reading

/-- The second original denotation is read at that same supplied root witness. -/
theorem one_linear (endpoint : Endpoint request sample requests root zeroOriginal oneOriginal scalarOriginal) :
    endpoint.one.linear = oneOriginal.value.re + oneOriginal.value.im * root.root := by
  have reading := endpoint.one.linear_readback
  rewrite [endpoint.root_readback] at reading
  exact reading

/-- The original cubic primitive denotation is read at the same actual endpoint root witness. -/
theorem scalar_linear (endpoint : Endpoint request sample requests root zeroOriginal oneOriginal scalarOriginal) :
    endpoint.scalar.linear = scalarOriginal.value.re + scalarOriginal.value.im * root.root := by
  have reading := endpoint.scalar.linear_readback
  rewrite [endpoint.root_readback] at reading
  exact reading

/-- The first cached endpoint value reads the original source model's actual first primitive table. -/
theorem zero_value (endpoint : Endpoint request sample requests root zeroOriginal oneOriginal scalarOriginal) :
    endpoint.zero.value = request.models.primitiveZero.eval point :=
  endpoint.zero.value_eq.trans
    (congrArg (fun polynomial => polynomial.eval point) endpoint.zero.polynomial_eq)

/-- The second cached endpoint value reads that same source model's actual second primitive table. -/
theorem one_value (endpoint : Endpoint request sample requests root zeroOriginal oneOriginal scalarOriginal) :
    endpoint.one.value = request.models.primitiveOne.eval point :=
  endpoint.one.value_eq.trans
    (congrArg (fun polynomial => polynomial.eval point) endpoint.one.polynomial_eq)

/-- The cached cubic endpoint value reads the original source model's scalar primitive table. -/
theorem scalar_value (endpoint : Endpoint request sample requests root zeroOriginal oneOriginal scalarOriginal) :
    endpoint.scalar.value = request.models.scalarPrimitive.eval point :=
  endpoint.scalar.value_eq.trans
    (congrArg (fun polynomial => polynomial.eval point) endpoint.scalar.polynomial_eq)

/-- The first comparison residual retains the literal source primitive and shared-root linear endpoint reading. -/
theorem zero_residual (endpoint : Endpoint request sample requests root zeroOriginal oneOriginal scalarOriginal) :
    endpoint.zero.residual = request.models.primitiveZero.eval point - endpoint.zero.linear := by
  rewrite [endpoint.zero.residual_eq, endpoint.zero_value]
  rfl

/-- The second comparison residual retains its literal source primitive and the same selected-root reading. -/
theorem one_residual (endpoint : Endpoint request sample requests root zeroOriginal oneOriginal scalarOriginal) :
    endpoint.one.residual = request.models.primitiveOne.eval point - endpoint.one.linear := by
  rewrite [endpoint.one.residual_eq, endpoint.one_value]
  rfl

/-- The cubic comparison residual reads the literal original scalar primitive and its shared-root linear value. -/
theorem scalar_residual (endpoint : Endpoint request sample requests root zeroOriginal oneOriginal scalarOriginal) :
    endpoint.scalar.residual = request.models.scalarPrimitive.eval point - endpoint.scalar.linear := by
  rewrite [endpoint.scalar.residual_eq, endpoint.scalar_value]
  rfl

/-- The first original source primitive endpoint residual pays its original retained target. -/
theorem zero_lt (endpoint : Endpoint request sample requests root zeroOriginal oneOriginal scalarOriginal)
    (inside : patch.box.Contains point) : Data.Gaussian.Norm.Basic.normSq endpoint.zero.residual < endpointTarget :=
  requests.zero.residual_lt endpoint.zero inside (requests.zero_stage_le.trans endpoint.stage_ge)

/-- The second original primitive endpoint residual pays that same retained endpoint target. -/
theorem one_lt (endpoint : Endpoint request sample requests root zeroOriginal oneOriginal scalarOriginal)
    (inside : patch.box.Contains point) : Data.Gaussian.Norm.Basic.normSq endpoint.one.residual < endpointTarget :=
  requests.one.residual_lt endpoint.one inside (requests.one_stage_le.trans endpoint.stage_ge)

/-- The actual retained scalar cubic primitive endpoint residual pays the same original target. -/
theorem scalar_lt (endpoint : Endpoint request sample requests root zeroOriginal oneOriginal scalarOriginal)
    (inside : patch.box.Contains point) : Data.Gaussian.Norm.Basic.normSq endpoint.scalar.residual < endpointTarget :=
  requests.scalar.residual_lt endpoint.scalar inside (requests.scalar_stage_le.trans endpoint.stage_ge)

end Endpoint
end Request

end Purelib.Curves.Legendre.Periods.Jets.Source

end
