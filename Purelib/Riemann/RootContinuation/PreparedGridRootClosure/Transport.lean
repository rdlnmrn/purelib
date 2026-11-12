module

public import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-! # Joint base and Owner transport of an original prepared closed grid walk

The actual preparation, primitive cover, cached names and operational return
move together along genuine scalar/Owner readbacks. There is no new source,
root selection, trace, name comparison or period-program construction.
-/

public section

namespace Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid.RootClosedWalk

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Polynomial.Geometry.Grid (ClearGrid)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {polynomial : GaussianPolynomial} {ambient : Box} {grid : ClearGrid polynomial ambient}

/-- Reindex the SAME complete closed preparation along actual base equality and whole heterogeneous Owner identity.

Both inputs are ownership transports, not a root-value or period comparison.
The original walk, traced preparation, cover, cached root names and returned
comparison are retained jointly without another producer invocation.
-/
def castBase {first last : Canonical} (pointEq : first = last)
    {firstOwner : Owner (polynomial.eval first)} {lastOwner : Owner (polynomial.eval last)}
    (ownerEq : HEq firstOwner lastOwner) (closed : RootClosedWalk grid first firstOwner) :
    RootClosedWalk grid last lastOwner := by
  cases pointEq
  cases ownerEq
  exact closed

/-- Joint endpoint transport retains the SAME whole original closed preparation heterogeneously. -/
theorem castBase_heq {first last : Canonical} (pointEq : first = last)
    {firstOwner : Owner (polynomial.eval first)} {lastOwner : Owner (polynomial.eval last)}
    (ownerEq : HEq firstOwner lastOwner) (closed : RootClosedWalk grid first firstOwner) :
    HEq (closed.castBase pointEq ownerEq) closed := by
  cases pointEq
  cases ownerEq
  rfl

/-- The projected walk is the SAME original walk with only its scalar endpoint indices transported. -/
theorem castBase_walk {first last : Canonical} (pointEq : first = last)
    {firstOwner : Owner (polynomial.eval first)} {lastOwner : Owner (polynomial.eval last)}
    (ownerEq : HEq firstOwner lastOwner) (closed : RootClosedWalk grid first firstOwner) :
    (closed.castBase pointEq ownerEq).walk = closed.walk.castEndpoints pointEq pointEq := by
  cases pointEq
  cases ownerEq
  rfl

end Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid.RootClosedWalk

end
