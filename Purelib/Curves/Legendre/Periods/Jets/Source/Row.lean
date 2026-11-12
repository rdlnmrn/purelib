module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Primitives
public import Purelib.Curves.Legendre.Periods.Jets.Source.Endpoint.Bank
import Purelib.Algebra.Quadratic.Pair.Polynomial.Derivative
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Legendre.PicardFuchs.Polynomials
import Purelib.Data.Fin.Two
import Purelib.Polynomial.Dense.Power

/-! # The three original retained Legendre primitive rows

A connection row keeps its basis coordinate; the scalar equation is a
separate row. Selection reads the existing original cells, inverse/cubic
primitive tables, requests, denotations and endpoint values. It does not
construct a source or another root/observation cache. The shared source
ceiling and actual selected integral-error laws remain those of the inputs.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients Expression)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- One of the original two connection rows or the original scalar Picard–Fuchs row.

The sum retains the original basis coordinate for a connection row. It is
a selector of existing owners, not a new differential, model or certificate.
-/
abbrev Row := Sum (Fin 2) Unit

namespace Row

/-- Select the original connection row at its unchanged original basis coordinate. -/
abbrev connection (coordinate : Fin 2) : Row := .inl coordinate

/-- Select the original scalar equation, distinct from both connection coordinates. -/
abbrev scalar : Row := .inr ()

/-- Connection primitives use the original inverse power; the scalar primitive uses the original cube. -/
@[expose] def pairs : Row → Fin 3
  | .inl _ => 0
  | .inr _ => 1

/-- Read the exact original displayed primitive numerator belonging to the selected row. -/
@[expose] def numerator (parameter : Canonical) : Row → Coefficients
  | .inl coordinate => Fin.cases Polynomials.firstPrimitivePolynomial
      (fun _ => Polynomials.secondPrimitivePolynomial parameter) coordinate
  | .inr _ => Polynomials.picardFuchsPrimitivePolynomial

/-- The selected original primitive expression retains its actual Legendre radicand and denominator power. -/
@[expose] def expression (parameter : Canonical) (row : Row) : Expression (Paths.polynomial parameter) :=
  Expression.oddReciprocal (Paths.polynomial parameter) row.pairs.val (row.numerator parameter)

/-- The two original connection rows both retain the inverse-sheet primitive exponent. -/
theorem pairs_connection (coordinate : Fin 2) : (connection coordinate).pairs = 0 := rfl

/-- The original scalar row retains the cubic inverse-sheet primitive exponent. -/
theorem pairs_scalar : scalar.pairs = 1 := rfl

section Models

variable {parameter : Canonical} {box : Geometry.Rational.Box}
variable {model : Model (Paths.polynomial parameter) box}

/-- Read the SAME selected original inverse-model primitive or its retained cubic primitive table. -/
@[expose] def spatial (row : Row) (models : Models.Shared model) : Coefficients :=
  match row with
  | .inl coordinate => Fin.cases models.primitiveZero (fun _ => models.primitiveOne) coordinate
  | .inr _ => models.scalarPrimitive

/-- The connection selector agrees with the original two-coordinate primitive cache operation. -/
theorem spatial_connection (models : Models.Shared model) (coordinate : Fin 2) :
    spatial (connection coordinate) models = models.primitive coordinate := by
  rcases Data.Fin.Two.finTwo_cases coordinate with zero | one
  · subst coordinate
    rfl
  · subst coordinate
    rfl

/-- The scalar selector reads the actual stored cubic table, including its original coefficient and power cache. -/
theorem spatial_scalar (models : Models.Shared model) : spatial scalar models = models.scalarPrimitive := rfl

/-- The selected primitive uses the SAME original numerator and original inverse/cubic polynomial cache. -/
theorem spatial_eq {count : Nat} {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {retainedModel : Model (Paths.polynomial parameter) patch.base.box}
    (row : Row) (models : Models.Shared retainedModel) :
    row.spatial models = row.numerator parameter *
      primitivePolynomial (model := retainedModel) models.powers row.pairs := by
  cases row with
  | inl coordinate => exact Fin.cases models.primitiveZero_eq (fun _ => models.primitiveOne_eq) coordinate
  | inr _ => exact models.scalarPrimitive_eq

end Models

section Sources

variable {parameter : Canonical} {count : Nat}
variable {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {cache : Cache patch}
variable {floor : Nat} {target : Rational} {request : Request cache floor target}
variable {start finish : Canonical} {allowance : Rational}

/-- Read the original actual relation cell from the SAME retained six-channel source. -/
@[expose] def cell (row : Row) (models : CellModels request start finish allowance) :
    Integration.Polynomial.Gaussian.Cell.Basic.CellModel :=
  match row with
  | .inl coordinate => Fin.cases models.zero (fun _ => models.one) coordinate
  | .inr _ => models.scalar

/-- Select the whole original primitive-comparison cache at that exact retained row cell. -/
@[expose] def primitive (row : Row) {models : CellModels request start finish allowance}
    (primitives : PrimitiveModels models) : Primitive.Comparison (row.cell models) :=
  match row with
  | .inl coordinate => Fin.cases primitives.zero (fun _ => primitives.one) coordinate
  | .inr _ => primitives.scalar

/-- Selecting the first connection row preserves the whole actual first original comparison cache. -/
theorem primitive_zero {models : CellModels request start finish allowance} (primitives : PrimitiveModels models) :
    (connection 0).primitive primitives = primitives.zero := rfl

/-- Selecting the second connection row preserves the whole actual second original comparison cache. -/
theorem primitive_one {models : CellModels request start finish allowance} (primitives : PrimitiveModels models) :
    (connection 1).primitive primitives = primitives.one := rfl

/-- Selecting the scalar row preserves the whole actual cubic primitive comparison cache. -/
theorem primitive_scalar {models : CellModels request start finish allowance} (primitives : PrimitiveModels models) :
    scalar.primitive primitives = primitives.scalar := rfl

/-- The selected original comparison retains the original shared source ceiling. -/
theorem bound_eq (row : Row) {models : CellModels request start finish allowance}
    (primitives : PrimitiveModels models) : (row.primitive primitives).bound = primitives.bound := by
  cases row with
  | inl coordinate => exact Fin.cases primitives.zero_bound_eq (fun _ => primitives.one_bound_eq) coordinate
  | inr _ => exact primitives.scalar_bound_eq

/-- The selected original spatial primitive increment pays its SAME retained row-cell integral. -/
theorem integral_error_le (row : Row) {models : CellModels request start finish allowance}
    (primitives : PrimitiveModels models) :
    Norm.Basic.normSq ((row.spatial request.models).eval finish - (row.spatial request.models).eval start -
      (row.cell models).integralSample) ≤ 2 * primitives.bound := by
  cases row with
  | inl coordinate =>
      exact Fin.cases primitives.zero_integral_error_le (fun _ => primitives.one_integral_error_le) coordinate
  | inr _ => exact primitives.scalar_integral_error_le

end Sources

section Endpoints

variable {parameter : Canonical} {count : Nat} {point : Canonical}
variable {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
variable {sample : ContinuedNeighborhood.Point patch point} {floor : Nat} {allocation : Rational}

/-- Read the original selected request with its actual numerator factor, root-power bound and finite stage. -/
@[expose] def request (row : Row) {target : Rational} (requests : EndpointRequests sample floor target) :
    PrimitiveRequest sample row.pairs (row.numerator parameter) floor target :=
  match row with
  | .inl coordinate => Fin.cases requests.zero (fun _ => requests.one) coordinate
  | .inr _ => requests.scalar

/-- The selected original primitive request is paid at the SAME stored common endpoint stage. -/
theorem stage_le (row : Row) {target : Rational} (requests : EndpointRequests sample floor target) :
    (row.request requests).stage ≤ requests.stage := by
  cases row with
  | inl coordinate => exact Fin.cases requests.zero_stage_le (fun _ => requests.one_stage_le) coordinate
  | inr _ => exact requests.scalar_stage_le

/-- Read the original selected primitive denotation from the unchanged complete endpoint plan. -/
@[expose] def denotation (row : Row) (plan : EndpointPlan sample floor allocation) :
    PrimitiveDenotation sample row.pairs (row.numerator parameter) :=
  match row with
  | .inl coordinate => Fin.cases plan.zero (fun _ => plan.one) coordinate
  | .inr _ => plan.scalar

/-- The selected actual divided coefficient consumes the SAME original shared root-precision ceiling. -/
theorem coefficient_le (row : Row) (plan : EndpointPlan sample floor allocation) :
    Norm.Basic.normSq (row.denotation plan).value.im ≤ plan.ceiling := by
  cases row with
  | inl coordinate => exact Fin.cases plan.zero_le (fun _ => plan.one_le) coordinate
  | inr _ => exact plan.scalar_le

/-- Read the complete selected primitive value on the identical original attachment and shared root reading. -/
@[expose] def value (row : Row) {plan : EndpointPlan sample floor allocation} {cache : Cache patch}
    {current : Nat} {target : Rational} {source : Request cache current target}
    (attached : EndpointPlan.Attachment plan source) :
    PrimitiveValue attached.endpoint.reading row.pairs (row.numerator parameter)
      (row.denotation plan) (row.spatial source.models) :=
  match row with
  | .inl coordinate => Fin.cases attached.endpoint.zero (fun _ => attached.endpoint.one) coordinate
  | .inr _ => attached.endpoint.scalar

/-- The first endpoint selector preserves the whole actual first original primitive-value cache. -/
theorem value_zero {plan : EndpointPlan sample floor allocation} {cache : Cache patch}
    {current : Nat} {target : Rational} {source : Request cache current target}
    (attached : EndpointPlan.Attachment plan source) : (connection 0).value attached = attached.endpoint.zero := rfl

/-- The second endpoint selector preserves the whole actual second original primitive-value cache. -/
theorem value_one {plan : EndpointPlan sample floor allocation} {cache : Cache patch}
    {current : Nat} {target : Rational} {source : Request cache current target}
    (attached : EndpointPlan.Attachment plan source) : (connection 1).value attached = attached.endpoint.one := rfl

/-- The scalar endpoint selector preserves the whole actual original cubic primitive-value cache. -/
theorem value_scalar {plan : EndpointPlan sample floor allocation} {cache : Cache patch}
    {current : Nat} {target : Rational} {source : Request cache current target}
    (attached : EndpointPlan.Attachment plan source) : scalar.value attached = attached.endpoint.scalar := rfl

/-- The actual selected endpoint value belongs to the SAME retained original spatial primitive table. -/
theorem value_eq (row : Row) {plan : EndpointPlan sample floor allocation} {cache : Cache patch}
    {current : Nat} {target : Rational} {source : Request cache current target}
    (attached : EndpointPlan.Attachment plan source) :
    (row.value attached).value = (row.spatial source.models).eval point := by
  cases row with
  | inl coordinate => exact Fin.cases attached.endpoint.zero_value (fun _ => attached.endpoint.one_value) coordinate
  | inr _ => exact attached.endpoint.scalar_value

end Endpoints

/-- The selected primitive's original denominator is admitted by the SAME full-root Owner.

The scalar row uses the original polynomial square; the connection rows
use the original polynomial itself. No sheet selection or denominator-power
substitution is involved in deriving these genuine nonzero guards.
-/
theorem defined (parameter point : Canonical) (row : Row)
    (owner : Owner ((Paths.polynomial parameter).eval point)) : (row.expression parameter).Defined point := by
  change (Polynomial.Dense.Power.power (Paths.polynomial parameter) (row.pairs.val + 1)).eval point ≠ 0
  rewrite [Polynomial.Dense.Power.eval_power]
  exact Algebra.Field.ExplicitField.pow_ne_zero_of_ne_zero owner.parameterNonzero _

end Row

end Purelib.Curves.Legendre.Periods.Jets.Source

end
