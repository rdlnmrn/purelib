module
import Purelib.Data.List.Membership
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
public import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
public import Purelib.Polynomial.Geometry.Grid.Boundary.Segments

/-!
# Boundary geometry of retained whole-path parent caches

Read the original segment spine and its cached parents. Repeated boundary
occurrences and owner transitions retain their original preparation.
-/

namespace Purelib.Riemann.Paths.PreparedPathBoundaryGeometry
public section
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)
open Purelib.Polynomial.Geometry.Grid.Boundary.Segments.PreparedBoundarySegments (OnBoundary)
open Purelib.Riemann.Paths.PreparedClearPathModels (Owner PreparedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments (ParentCaches)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {sheet : Fin 2} {ambient box :
    Purelib.Geometry.Rational.Box}

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
/-- Transfer a clear path's boundary geometry to every parent in its retained segment caches.

The proof follows the original prepared segment spine, preserving repeated boundary occurrences and owner transitions
through the exact cached parent lists. -/
theorem onPathBoundary :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Owner (curve.polynomial.eval start)} {prepared : PreparedPath path owner}
      {pieces : CoveredSegments prepared} (cache : ParentCaches differential sheet pieces),
      Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box path → ∀ parent ∈ cache.parents,
        ParentOnBoundary parent box
  | _, _, _, _, _, .nil _ _, _, _, _, member => by cases member
  | _, _, _, _, _, .cons _ _, cache, boundary, parent, member => by
      rcases Membership.mem_append.mp member with member | member
      · exact Paths.PreparedSegmentBoundaryGeometry.segment_parent_boundary cache.1 boundary.1 boundary.2.1
          boundary.2.2.1 member
      · exact onPathBoundary cache.2 boundary.2.2.2 parent member

end
end Purelib.Riemann.Paths.PreparedPathBoundaryGeometry
