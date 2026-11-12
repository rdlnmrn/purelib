module

public import Purelib.Riemann.Readings.UniformPreparedRequests
public import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.Query
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Riemann.Paths.PreparedPrimitivePaths

/-! # Local primitive agreement consuming the actual retained direct query

The original request's neighborhood equation transports the whole supplied
sample to its own patch. The retained Query supplies its actual Owner and
refinement, without another point observation or query transport.
-/

public section

namespace Purelib.Riemann.Readings.UniformPreparedRequests

namespace LocalRequest

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.PreparedPrimitivePaths (point_inside_of_endpoints)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {parent : CenteredEdge curve differential} {target : Rational} {point : Canonical}

/-- Every bounded parent query belongs to the same retained request neighborhood.

The original patch start and stored finish bound contain the affine edge.
No mesh, source, query or point preparation is executed by this proof.
-/
theorem point_inside (request : LocalRequest parent count target) {fraction : Rational}
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    request.neighborhood.box.Contains (parent.edge.point fraction) := by
  have firstInside : request.neighborhood.box.Contains (parent.edge.point 0) := by
    rewrite [request.neighborhood_eq]
    exact request.patch.start_inside count
  exact point_inside_of_endpoints parent request.neighborhood.box firstInside request.finishInside inside

/-- Derive the signed original request-sample relation from the same retained query and whole sample.

The request equality changes only dependent indices of the supplied Point.
The original patch comparison consumes that Point and Query, including
their two actual refinement witnesses. It runs neither original producer.
-/
def retainedQueryEquivalent (request : LocalRequest parent count target) (fraction : Rational)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) (query : PreparedEdge.Query parent.edge fraction inside)
    (pointEq : parent.edge.point fraction = point) (pointInside : request.neighborhood.box.Contains point)
    (sample : ContinuedNeighborhood.Point request.neighborhood point) :
    NamedEquivalent (parent.edge.rootName fraction inside) sample.certificate.value.name := by
  rcases request with ⟨patch, neighborhood, neighborhoodEq, _requested, _finishInside⟩
  subst neighborhood
  exact patch.retainedQueryEquivalent count fraction inside query pointEq pointInside sample

end LocalRequest

end Purelib.Riemann.Readings.UniformPreparedRequests

end
