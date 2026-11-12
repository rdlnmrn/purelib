module

public import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.Cells
public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Endpoints

/-! # Original primitive-cell endpoints at retained Point requests

The actual cell supplies its complete inverse, power and potential caches.
The endpoint request was selected on the original continued Point before
the cell stage. Its paid sample compares the original potential polynomial
to that same requested denotation reading, without another model or Point.
-/

public section

namespace Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds.Cell

open Purelib
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate Polynomial)
open Purelib.Riemann.Normalization.InverseModelDerivativeBounds (DerivativeBounds)
open Purelib.Riemann.Normalization.InverseModelDifferentialResidual (DifferentialResidualBounds)
open Purelib.Riemann.Normalization.InverseModelPrimitiveBounds (PrimitiveDerivativeBounds)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (Point)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Data.Gaussian

variable {polynomial numerator : Polynomial} {count : Nat}
    {patch : ContinuedNeighborhood polynomial count}
    {clearance : RegionClearance polynomial patch.base.box}
    {root : DerivativeBounds clearance patch.base.model}
    {residual : DifferentialResidualBounds patch.base.model}
    {primitive : PrimitiveDerivativeBounds root numerator}
    {bounds : PrimitiveResidualBounds root residual primitive 0}
    {start finish point : Gaussian} {coordinate : Spatial.Coordinate start finish}
    {stage : Nat} {allowance : Coordinate} {nonnegative : 0 ≤ allowance}
    {sample : Point patch point} {floor : Nat} {target : Coordinate}

/-- The actual potential polynomial uses the zero-pair inverse from this cell's retained power cache. -/
theorem endpoint_compiled (retained : Cell bounds coordinate stage allowance nonnegative) :
    retained.value.eval point = numerator.eval point * (primitivePolynomial retained.powers 0).eval point := by
  rewrite [retained.value_eq, eval_mul]
  rfl

/-- Equal numerator polynomials give the same scalar endpoint compilation on the unchanged cell caches. -/
theorem endpoint_compiled_of_numerator_eq (retained : Cell bounds coordinate stage allowance nonnegative)
    {otherNumerator : Polynomial} (numeratorEq : numerator = otherNumerator) :
    retained.value.eval point =
      otherNumerator.eval point * (primitivePolynomial retained.powers 0).eval point :=
  (retained.endpoint_compiled (point := point)).trans
    (congrArg (fun value : Polynomial => value.eval point *
      (primitivePolynomial retained.powers 0).eval point) numeratorEq)

/-- A same-cell endpoint sample on the original preselected Point request and actual potential polynomial. -/
abbrev Endpoint (retained : Cell bounds coordinate stage allowance nonnegative)
    (paid : PrimitiveEndpoint sample 0 numerator floor target) :=
  paid.Sample retained.inverse retained.inverse_eq retained.powers retained.value retained.endpoint_compiled

/-- Observe one original primitive endpoint using this cell's same inverse, powers and potential.

Only the requested root witness, scalar reading and finite comparison are
new. The source stage payment concerns this actual cell; the Point, source
request, exact denotation and original requested channel reading are reused.
-/
def observeEndpoint (retained : Cell bounds coordinate stage allowance nonnegative)
    (paid : PrimitiveEndpoint sample 0 numerator floor target)
    (inside : patch.box.Contains point) (later : paid.source.stage ≤ stage) (positive : 0 < target) :
    retained.Endpoint paid :=
  PrimitiveEndpoint.Sample.build paid retained.inverse retained.inverse_eq retained.powers retained.value
    retained.endpoint_compiled inside later positive

/-- The endpoint comparison bounds this exact cell's potential against the unchanged requested observation. -/
theorem endpoint_error_le (retained : Cell bounds coordinate stage allowance nonnegative)
    (paid : PrimitiveEndpoint sample 0 numerator floor target) (observed : retained.Endpoint paid) :
    Norm.Basic.normSq (retained.value.eval point - paid.observation.reading.value) ≤ target :=
  PrimitiveEndpoint.Sample.error_le paid observed

end Purelib.Riemann.Normalization.InverseModelPrimitiveResidual.PrimitiveResidualBounds.Cell

end
