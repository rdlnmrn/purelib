module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Endpoint.Bank

/-! # Endpoint plans on complete retained vertex caches

The original vertex factory equality transports the entire actual plan
back to its original typed continued point. The primitive coefficients,
root precision and three stage requests are those of the retained vertex;
the point and vertex are not queried again.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.EndpointPlan

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {parameter : Canonical} {count : Nat} {point : LiftedPoint 2}
variable {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}

/-- Construct a plan from the complete retained vertex and transport only its exact original point index. -/
def ofVertexCache (sample : ContinuedNeighborhood.Point patch point.coordinate)
    (original : { vertex : Vertex parameter point // vertex = Vertex.ofPoint sample })
    (floor : Nat) (allocation : Rational) (positive : 0 < allocation) :
    EndpointPlan sample floor allocation :=
  let plan := ofVertex original.val floor allocation positive
  let sameType : EndpointPlan original.val.sample floor allocation = EndpointPlan sample floor allocation :=
    congrArg (fun vertex : Vertex parameter point => EndpointPlan vertex.sample floor allocation) original.property
  Eq.mp sameType plan

/-- Exact vertex-cache transport preserves the complete original endpoint plan and every retained request. -/
theorem ofVertexCache_heq (sample : ContinuedNeighborhood.Point patch point.coordinate)
    (original : { vertex : Vertex parameter point // vertex = Vertex.ofPoint sample })
    (floor : Nat) (allocation : Rational) (positive : 0 < allocation) :
    HEq (ofVertexCache sample original floor allocation positive)
      (ofVertex original.val floor allocation positive) := by
  rcases original with ⟨vertex, equal⟩
  cases equal
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Source.EndpointPlan

end
