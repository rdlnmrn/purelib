module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
public import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

/-! Equality transport of the original prepared subdivision owner. -/

@[expose] public section
namespace Purelib.RootIsolation.SquareRoot.Subdivision.OwnerTransport

/-- Transport a retained subdivision along equality of its initial square-root owners.

Equality elimination preserves the original segment, ambient containment, left endpoint and all retained subdivision
data. -/
public def castSubdivisionOwner
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish}
    {within : segment.WithinAmbient}
    {left : Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint}
    {source target : Riemann.Topology.SquareRootContinuationChain.Owner
      (polynomial.eval (segment.pointAt left.parameter))}
    (equal : source = target)
    (data : Riemann.Branches.PreparedSheetContinuation.Subdivision segment within
      left source) :
    Riemann.Branches.PreparedSheetContinuation.Subdivision segment within left target :=
  equal ▸ data

end Purelib.RootIsolation.SquareRoot.Subdivision.OwnerTransport
