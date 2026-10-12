module
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Init.Prelude
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Geometry

open Purelib.Polynomial.Geometry

@[expose] public section

/-!
Focused native-code consumer of the centered-data projection used by the
canonical period observation.  No branch isolation, numerical observation or
generated certificate is evaluated by compiling this harness.  The call must
select the direct stored-data implementation rather than replay owners.
-/

namespace PreparedModelProjectionHarness

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Owner Subdivision)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain

/-- Read the centered segment data directly from its retained canonical subdivision.

The result keeps the original curve, differential, sheet, endpoint owner and exact subdivision endpoints. -/
@[noinline] def centeredData {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential : Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish)
    (within : segment.WithinAmbient) {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) (subdivision : Subdivision segment within left owner) :
    PreparedSegmentCenteredData curve differential sheet (segment.pointAt left.parameter)
      (segment.pointAt subdivision.endpoint.parameter) :=
  dataOfCanonicalSubdivision curve differential segment within sheet subdivision

end PreparedModelProjectionHarness
