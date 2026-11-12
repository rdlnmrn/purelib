module

public import Purelib.Curves.Legendre.Periods.Jets.Source
public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Uniform
import Purelib.Polynomial.Dense.Gaussian.Evaluation
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Fixed source requests for all six original Legendre integrands

Uniform coefficient requests use the same retained chart clearance and odd
reading bounds. The four original weighted numerators are cached once. All
six finite stages are selected before the original model and its shared odd
powers are constructed, independently of later unit-parameter queries.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds UniformRequest)
open Purelib.Riemann.Normalization.InverseRootPolynomial (half)
open Purelib.Riemann.Normalization
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Basic.DensePolynomial (eval_scale)
open Purelib.Data.Nat

variable {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}

set_option genInjectivity false in
/-- The six original integrand requests and shared source caches selected before constructing a later Newton model.

The uniform bound owner remains indexed. The four original differentiated
numerators retain their actual scalar factors before box-bound evaluation.
Each request retains its individual paid stage, and their cached maximum
supplies a common model-depth floor for all later source observations. -/
structure IntegrandRequests (bounds : UniformBounds patch) (floor : Nat) (target : Rational) where
  /-- The actual first unweighted differentiated numerator. -/
  firstNumeratorZero : Coefficients
  /-- The numerator retains the original half factor and base polynomial. -/
  firstNumeratorZero_eq : firstNumeratorZero = Polynomials.basePolynomial.scale half
  /-- The actual first coordinate-weighted differentiated numerator. -/
  firstNumeratorOne : Coefficients
  /-- The numerator retains the original half factor and weighted base polynomial. -/
  firstNumeratorOne_eq : firstNumeratorOne = Polynomials.weightedBasePolynomial.scale half
  /-- The actual second unweighted differentiated numerator. -/
  secondNumeratorZero : Coefficients
  /-- The numerator retains the original three-quarter factor and squared base polynomial. -/
  secondNumeratorZero_eq : secondNumeratorZero = Polynomials.squaredBasePolynomial.scale (⟨3 / 4, 0⟩ : Canonical)
  /-- The actual second coordinate-weighted differentiated numerator. -/
  secondNumeratorOne : Coefficients
  /-- The numerator retains the original three-quarter factor and weighted squared base polynomial. -/
  secondNumeratorOne_eq : secondNumeratorOne =
    Polynomials.weightedSquaredBasePolynomial.scale (⟨3 / 4, 0⟩ : Canonical)
  /-- The first original value-channel request. -/
  valueZero : UniformRequest bounds 0 Basic.constantOnePolynomial floor target
  /-- The second original value-channel request. -/
  valueOne : UniformRequest bounds 0 Basic.coordinatePolynomial floor target
  /-- The first original differentiated-channel request. -/
  firstZero : UniformRequest bounds 1 firstNumeratorZero floor target
  /-- The second original differentiated-channel request. -/
  firstOne : UniformRequest bounds 1 firstNumeratorOne floor target
  /-- The first original second-differentiated-channel request. -/
  secondZero : UniformRequest bounds 2 secondNumeratorZero floor target
  /-- The second original second-differentiated-channel request. -/
  secondOne : UniformRequest bounds 2 secondNumeratorOne floor target
  /-- The cached maximum of the six actual individual selected depths. -/
  stage : Nat
  /-- This floor is the actual maximum of the retained original request stages. -/
  stage_eq : stage = max valueZero.selection.stage (max valueOne.selection.stage
    (max firstZero.selection.stage (max firstOne.selection.stage
      (max secondZero.selection.stage secondOne.selection.stage))))

constructive_injectivity IntegrandRequests

namespace IntegrandRequests

/-- Cache all six fixed original source requests before refining a Newton model or querying a segment point. -/
@[expose] def build (bounds : UniformBounds patch) (floor : Nat) (target : Rational) (positive : 0 < target) :
    IntegrandRequests bounds floor target :=
  let firstNumeratorZero := Polynomials.basePolynomial.scale half
  let firstNumeratorOne := Polynomials.weightedBasePolynomial.scale half
  let secondNumeratorZero := Polynomials.squaredBasePolynomial.scale (⟨3 / 4, 0⟩ : Canonical)
  let secondNumeratorOne := Polynomials.weightedSquaredBasePolynomial.scale (⟨3 / 4, 0⟩ : Canonical)
  let valueZero := bounds.request 0 Basic.constantOnePolynomial floor target positive
  let valueOne := bounds.request 0 Basic.coordinatePolynomial floor target positive
  let firstZero := bounds.request 1 firstNumeratorZero floor target positive
  let firstOne := bounds.request 1 firstNumeratorOne floor target positive
  let secondZero := bounds.request 2 secondNumeratorZero floor target positive
  let secondOne := bounds.request 2 secondNumeratorOne floor target positive
  let stage := max valueZero.selection.stage (max valueOne.selection.stage
    (max firstZero.selection.stage (max firstOne.selection.stage
      (max secondZero.selection.stage secondOne.selection.stage))))
  ⟨firstNumeratorZero, rfl, firstNumeratorOne, rfl, secondNumeratorZero, rfl, secondNumeratorOne, rfl,
    valueZero, valueOne, firstZero, firstOne, secondZero, secondOne, stage, rfl⟩

variable {bounds : UniformBounds patch} {floor : Nat} {target : Rational}
  {box : InverseRootPolynomial.Box} {model : InverseRootPolynomial.Model (Paths.polynomial parameter) box}

/-- The original unweighted value table reads the same cached unit numerator and inverse model. -/
theorem valueZero_readback (models : Models.Shared model) (point : Canonical) :
    models.valueZero.eval point = Basic.constantOnePolynomial.eval point * model.value.eval point := by
  rw [models.valueZero_eval, Evaluation.constantOnePolynomial_eval, Data.Gaussian.Basic.one_mul]

/-- The original weighted value table reads the same coordinate numerator and inverse model. -/
theorem valueOne_readback (models : Models.Shared model) (point : Canonical) :
    models.valueOne.eval point = Basic.coordinatePolynomial.eval point * model.value.eval point := by
  rw [models.valueOne_eval, Evaluation.coordinatePolynomial_eval]

/-- The literal first original differentiated table reads its cached scaled numerator and retained cube. -/
theorem firstZero_readback (requests : IntegrandRequests bounds floor target) (models : Models.Shared model)
    (point : Canonical) : models.firstZero.eval point =
      requests.firstNumeratorZero.eval point * models.powers.cube.eval point := by
  rw [models.firstZero_eval, requests.firstNumeratorZero_eq, eval_scale, models.powers.cube_eval]
  ring1

/-- The literal weighted first differentiated table reads its cached scaled numerator and that same cube. -/
theorem firstOne_readback (requests : IntegrandRequests bounds floor target) (models : Models.Shared model)
    (point : Canonical) : models.firstOne.eval point =
      requests.firstNumeratorOne.eval point * models.powers.cube.eval point := by
  rw [models.firstOne_eval, requests.firstNumeratorOne_eq, eval_scale, models.powers.cube_eval]
  ring1

/-- The literal second original differentiated table reads its cached scaled numerator and retained fifth power. -/
theorem secondZero_readback (requests : IntegrandRequests bounds floor target) (models : Models.Shared model)
    (point : Canonical) : models.secondZero.eval point =
      requests.secondNumeratorZero.eval point * models.powers.fifth.eval point := by
  rw [models.secondZero_eval, requests.secondNumeratorZero_eq, eval_scale, models.powers.fifth_eval]
  ring1

/-- The literal weighted second differentiated table reads its cached scaled numerator and that same fifth power. -/
theorem secondOne_readback (requests : IntegrandRequests bounds floor target) (models : Models.Shared model)
    (point : Canonical) : models.secondOne.eval point =
      requests.secondNumeratorOne.eval point * models.powers.fifth.eval point := by
  rw [models.secondOne_eval, requests.secondNumeratorOne_eq, eval_scale, models.powers.fifth_eval]
  ring1

/-- The first value request is paid above the actual common integrand floor. -/
theorem valueZero_stage_le (requests : IntegrandRequests bounds floor target) :
    requests.valueZero.selection.stage ≤ requests.stage := by
  rewrite [requests.stage_eq]
  exact Order.le_max_left _ _

/-- The original six-channel maximum does not precede its retained construction floor. -/
theorem floor_le (requests : IntegrandRequests bounds floor target) : floor ≤ requests.stage :=
  requests.valueZero.selection.lower.trans requests.valueZero_stage_le

/-- The second value request is paid above that same actual integrand floor. -/
theorem valueOne_stage_le (requests : IntegrandRequests bounds floor target) :
    requests.valueOne.selection.stage ≤ requests.stage := by
  rewrite [requests.stage_eq]
  exact (Order.le_max_left _ _).trans (Order.le_max_right _ _)

/-- The first derivative request is paid above that same actual integrand floor. -/
theorem firstZero_stage_le (requests : IntegrandRequests bounds floor target) :
    requests.firstZero.selection.stage ≤ requests.stage := by
  rewrite [requests.stage_eq]
  exact (Order.le_max_left _ _).trans ((Order.le_max_right _ _).trans (Order.le_max_right _ _))

/-- The second derivative request is paid above that same actual integrand floor. -/
theorem firstOne_stage_le (requests : IntegrandRequests bounds floor target) :
    requests.firstOne.selection.stage ≤ requests.stage := by
  rewrite [requests.stage_eq]
  exact (Order.le_max_left _ _).trans
    ((Order.le_max_right _ _).trans ((Order.le_max_right _ _).trans (Order.le_max_right _ _)))

/-- The first second-derivative request is paid above that same actual integrand floor. -/
theorem secondZero_stage_le (requests : IntegrandRequests bounds floor target) :
    requests.secondZero.selection.stage ≤ requests.stage := by
  rewrite [requests.stage_eq]
  exact (Order.le_max_left _ _).trans
    ((Order.le_max_right _ _).trans ((Order.le_max_right _ _).trans
      ((Order.le_max_right _ _).trans (Order.le_max_right _ _))))

/-- The second second-derivative request is paid above that same actual integrand floor. -/
theorem secondOne_stage_le (requests : IntegrandRequests bounds floor target) :
    requests.secondOne.selection.stage ≤ requests.stage := by
  rewrite [requests.stage_eq]
  exact (Order.le_max_right _ _).trans
    ((Order.le_max_right _ _).trans ((Order.le_max_right _ _).trans
      ((Order.le_max_right _ _).trans (Order.le_max_right _ _))))

/-- Select the original model after paying all six uniform integrands and the retained endpoint floor. -/
def modelRequest (requests : IntegrandRequests bounds floor target) (cache : Cache patch)
    (endpointFloor : Nat) (relationTarget : Rational) (positive : 0 < relationTarget) :
    Request cache (max requests.stage endpointFloor) relationTarget :=
  cache.request (max requests.stage endpointFloor) relationTarget positive

/-- The chosen original model depth pays the retained maximum of all six original integrand requests. -/
theorem stage_le_modelRequest (requests : IntegrandRequests bounds floor target) (cache : Cache patch)
    (endpointFloor : Nat) (relationTarget : Rational) (positive : 0 < relationTarget) :
    requests.stage ≤ (requests.modelRequest cache endpointFloor relationTarget positive).selection.stage :=
  (Order.le_max_left _ _).trans
    (requests.modelRequest cache endpointFloor relationTarget positive).selection.lower

/-- The chosen original model depth pays the same retained original endpoint floor. -/
theorem endpointFloor_le_modelRequest (requests : IntegrandRequests bounds floor target) (cache : Cache patch)
    (endpointFloor : Nat) (relationTarget : Rational) (positive : 0 < relationTarget) :
    endpointFloor ≤ (requests.modelRequest cache endpointFloor relationTarget positive).selection.stage :=
  (Order.le_max_right _ _).trans
    (requests.modelRequest cache endpointFloor relationTarget positive).selection.lower

end IntegrandRequests

end Purelib.Curves.Legendre.Periods.Jets.Source

end
