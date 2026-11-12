module

public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Denotation
public import Purelib.Approximation.Rational.Geometric.Search
public import Purelib.Approximation.Gaussian.Name.Coherent.Request
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Source-owned precision requests for continued primitive endpoints

A request computes its finite depth floor from original scalar data before
building any later inverse polynomial. Reading caches at the final common
stage retain the same original point, root state and selected witness.
-/

public section

namespace Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Approximation.Rational
open Purelib.Approximation.Gaussian.Name.Coherent

attribute [local irreducible] Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

variable {polynomial : Coefficients} {count : Nat}
    {patch : ContinuedNeighborhood polynomial count} {point : Canonical}

set_option genInjectivity false in
/-- A retained finite precision request on one original continued primitive source.

The source point, original numerator, power and scalar cache determine the
geometric scale. The original floor and target determine the first paid stage;
no inverse-model coefficient table is built to make that selection. -/
structure PrimitiveRequest (sample : Point patch point) (pairs : Fin 3) (numerator : Coefficients)
    (floor : Nat) (target : Fraction.Rational) where
  /-- The actual original scalar factor and reading-bound cache. -/
  bounds : PrimitiveBounds sample
  /-- The cached original source numerator evaluation at the same actual point. -/
  factor : Canonical
  /-- The retained factor belongs to the original numerator and coordinate. -/
  factor_eq : factor = numerator.eval point
  /-- The cached quadrance of the actual retained source factor. -/
  factorNorm : Fraction.Rational
  /-- The scalar norm consumes that exact cached original numerator reading. -/
  factorNorm_eq : factorNorm = Norm.Basic.normSq factor
  /-- The cached geometric scale for this original primitive numerator and power. -/
  scale : Fraction.Rational
  /-- The scale multiplies the same retained numerator norm by the same retained original odd-reading scale. -/
  scale_eq : scale = factorNorm * bounds.scale pairs
  /-- The actual retained primitive comparison scale is nonnegative. -/
  scale_nonnegative : 0 ≤ scale
  /-- The original requested target is strictly positive. -/
  positive : 0 < target
  /-- The first finite depth paying this actual original request above its original stage floor. -/
  stage : Nat
  /-- The retained stage is the result of the actual original finite geometric search. -/
  stage_eq : stage = Geometric.Search.firstQuarterBelow scale floor target
  /-- The selected stage retains the original floor. -/
  stage_ge : floor ≤ stage
  /-- The actual selected quarter-radius allowance pays the original requested target. -/
  payment : Geometric.Basic.quarterRadius scale stage < target

constructive_injectivity PrimitiveRequest

/-- Select a primitive depth from the retained original numerator factor and its cached scalar quadrance.

The original point, numerator and bound cache determine the same comparison
scale. This constructor consumes the actual retained factor and norm rather
than evaluating the numerator or recomputing its quadrance.
-/
@[expose] def PrimitiveBounds.requestFromFactor {sample : Point patch point} (bounds : PrimitiveBounds sample)
    (pairs : Fin 3) (numerator : Coefficients) (factor : {value : Canonical // value = numerator.eval point})
    (factorNorm : {value : Fraction.Rational // value = Norm.Basic.normSq factor.val})
    (floor : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    PrimitiveRequest sample pairs numerator floor target :=
  let scale := factorNorm.val * bounds.scale pairs
  have normNonnegative : 0 ≤ factorNorm.val := by
    rewrite [factorNorm.property]
    exact Norm.Basic.normSq_nonneg factor.val
  have scaleNonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
    normNonnegative (bounds.scale_nonnegative pairs)
  let stage := Geometric.Search.firstQuarterBelow scale floor target
  ⟨bounds, factor.val, factor.property, factorNorm.val, factorNorm.property, scale, rfl,
    scaleNonnegative, positive, stage, rfl, Geometric.Search.firstQuarterBelow_ge scale floor target,
    Geometric.Search.firstQuarterBelow_accurate scale scaleNonnegative floor target positive⟩

/-- Select a primitive source's first paid stage from its retained exact scalar bounds and original request. -/
@[expose] def PrimitiveBounds.request {sample : Point patch point} (bounds : PrimitiveBounds sample)
    (pairs : Fin 3) (numerator : Coefficients) (floor : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    PrimitiveRequest sample pairs numerator floor target :=
  let factor := numerator.eval point
  let factorNorm := Norm.Basic.normSq factor
  bounds.requestFromFactor pairs numerator ⟨factor, rfl⟩ ⟨factorNorm, rfl⟩ floor target positive

/-- The retained primitive request pays the source residual at any final common stage above its selected floor. -/
theorem PrimitiveRequest.residual_lt {sample : Point patch point} {pairs : Fin 3} {numerator : Coefficients}
    {floor : Nat} {target : Fraction.Rational} (request : PrimitiveRequest sample pairs numerator floor target)
    {depth : Nat} {model : Model polynomial patch.base.box} {powers : OddPowers model.value}
    {reading : PrimitiveReading sample depth model powers} {original : PrimitiveDenotation sample pairs numerator}
    {source : Coefficients} (value : PrimitiveValue reading pairs numerator original source)
    (inside : patch.box.Contains point) (stage : request.stage ≤ depth) :
    Norm.Basic.normSq value.residual < target := by
  have estimate := value.residual_le request.bounds inside
  rewrite [← request.factor_eq, ← request.factorNorm_eq, ← request.scale_eq] at estimate
  exact estimate.trans_lt
    ((Geometric.Basic.quarterRadius_antitone request.scale_nonnegative stage).trans_lt request.payment)

set_option genInjectivity false in
/-- An actual requested shared root witness on the original continued point's selected process.

The original residual-reading state is cached first, then refined for the
same semantic target. Its actual finite witness remains possible at both
states and can be reused by the incident source cells. -/
structure PrimitiveRoot (sample : Point patch point) (depth : Nat) (target : Fraction.Rational) where
  /-- The actual retained original continued point. -/
  owner : Point patch point
  /-- The retained point is the original source owner. -/
  owner_eq : owner = sample
  /-- The original positive semantic accuracy target. -/
  positive : 0 < target
  /-- The cached original source residual-reading state at the actual common model depth. -/
  sourceState : RootState sample
  /-- The source state belongs to the original scheduled point reading. -/
  sourceState_eq : sourceState = sample.readingState depth
  /-- The cached semantic refinement request computed for that same original root process. -/
  request : Fraction.Rational
  /-- The request uses the original channel's actual visible and semantic accuracy owner. -/
  request_eq : request = Request.channelTarget sample.certificate.value target
  /-- The actual retained request is strictly positive. -/
  request_positive : 0 < request
  /-- The cached actual requested root state. -/
  state : RootState sample
  /-- The root state is the exact original process refinement of the retained original source state. -/
  state_eq : state = sample.certificate.value.name.process.refine sourceState request request_positive
  /-- The cached actual root witness at the original requested state. -/
  root : Canonical
  /-- The root is the finite witness supplied by that exact original process and retained state. -/
  root_eq : root = (sample.certificate.value.name.process.witness state).val
  /-- The actual retained root witness is possible at its actual retained state. -/
  possible : RootPossible sample state root
  /-- That same root witness persists at the original source model's residual-reading state. -/
  atReading : RootPossible sample (sample.readingState depth) root
  /-- The retained requested state has semantic allowance below the original target. -/
  allowance_lt : sample.certificate.value.coherent.allowance state < target

constructive_injectivity PrimitiveRoot

/-- The actual retained root state has visible squared radius below its original semantic target. -/
theorem PrimitiveRoot.radius_lt {sample : Point patch point} {depth : Nat} {target : Fraction.Rational}
    (root : PrimitiveRoot sample depth target) :
    (sample.certificate.value.name.process.ball root.state).radiusSq < target := by
  rewrite [root.state_eq]
  have accurate := sample.certificate.value.name.process.accurate root.sourceState root.request root.request_positive
  have request := Request.channelTarget_lt_target sample.certificate.value root.positive
  rewrite [← root.request_eq] at request
  exact accurate.trans request

/-- Request and retain one original root witness at the actual chosen common model depth. -/
@[noinline, nospecialize] def selectPrimitiveRoot (sample : Point patch point) (depth : Nat)
    (target : Fraction.Rational) (positive : 0 < target) : PrimitiveRoot sample depth target := by
  let sourceState := sample.readingState depth
  let request := Request.channelTarget sample.certificate.value target
  have requestPositive := Request.channelTarget_pos sample.certificate.value positive
  let state := sample.certificate.value.name.process.refine sourceState request requestPositive
  let witness := sample.certificate.value.name.process.witness state
  have atReading : RootPossible sample (sample.readingState depth) witness.val :=
    sample.certificate.value.name.process.refine_persists sourceState request requestPositive witness.property
  have allowance := sample.certificate.value.coherent.refine_accurate sourceState target positive
    request requestPositive (Request.channelTarget_lt_allowanceRequest sample.certificate.value positive)
  exact ⟨sample, rfl, positive, sourceState, rfl, request, rfl, requestPositive, state, rfl,
    witness.val, rfl, witness.property, atReading, allowance⟩

/-- Transport only the original point index of the same retained primitive-root request. -/
@[expose] def PrimitiveRoot.castOwner {sample replacement : Point patch point} {depth : Nat}
    {target : Fraction.Rational} (root : PrimitiveRoot sample depth target) (equal : sample = replacement) :
    PrimitiveRoot replacement depth target := by
  cases equal
  exact root

/-- A point-index transport preserves the exact retained original root reading. -/
theorem PrimitiveRoot.castOwner_root {sample replacement : Point patch point} {depth : Nat}
    {target : Fraction.Rational} (root : PrimitiveRoot sample depth target) (equal : sample = replacement) :
    (root.castOwner equal).root = root.root := by
  cases equal
  rfl

/-- Retain the same requested root witness while reading the final original shared inverse-model and power caches. -/
@[expose] def PrimitiveRoot.readModel {sample : Point patch point} {depth : Nat} {target : Fraction.Rational}
    (root : PrimitiveRoot sample depth target) (model : Model polynomial patch.base.box)
    (sameModel : model = patch.base.refine depth) (powers : OddPowers model.value) :
    PrimitiveReading sample depth model powers :=
  let actual := root.castOwner root.owner_eq.symm
  let reading := retainPrimitiveReading root.owner depth model sameModel powers
    actual.state actual.root actual.possible actual.atReading
  root.owner_eq ▸ reading

/-- Reading an actual retained source model preserves the original externally shared root witness. -/
theorem PrimitiveRoot.readModel_root {sample : Point patch point} {depth : Nat} {target : Fraction.Rational}
    (root : PrimitiveRoot sample depth target) (model : Model polynomial patch.base.box)
    (sameModel : model = patch.base.refine depth) (powers : OddPowers model.value) :
    (root.readModel model sameModel powers).root = root.root := by
  cases root with
  | mk owner owner_eq positive sourceState sourceState_eq request request_eq request_positive state state_eq
      value value_eq possible atReading allowance =>
      cases owner_eq
      rfl

/-- Reading the actual retained model preserves the same original requested root state. -/
theorem PrimitiveRoot.readModel_state {sample : Point patch point} {depth : Nat} {target : Fraction.Rational}
    (root : PrimitiveRoot sample depth target) (model : Model polynomial patch.base.box)
    (sameModel : model = patch.base.refine depth) (powers : OddPowers model.value) :
    (root.readModel model sameModel powers).state = root.state := by
  cases root with
  | mk owner owner_eq positive sourceState sourceState_eq request request_eq request_positive state state_eq
      value value_eq possible atReading allowance =>
      cases owner_eq
      rfl

/-- The same requested root witness pays the visible radius of its actual retained primitive-reading view.

The original readModel_state equation and exact Reading radius readback
transfer the already paid request. No root is refined or sampled to prove
this statement, and the supplied model and power cache remain unchanged.
-/
theorem PrimitiveRoot.readModel_radius_lt {sample : Point patch point} {depth : Nat}
    {target : Fraction.Rational} (root : PrimitiveRoot sample depth target)
    (model : Model polynomial patch.base.box) (sameModel : model = patch.base.refine depth)
    (powers : OddPowers model.value) :
    (root.readModel model sameModel powers).rootReading.radius < target := by
  rewrite [PrimitiveReading.rootReading_radius, root.readModel_state model sameModel powers]
  exact root.radius_lt

end Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point

end
