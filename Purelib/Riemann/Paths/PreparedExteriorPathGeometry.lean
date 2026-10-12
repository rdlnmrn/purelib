module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Paths.PreparedSegmentParentBanks
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain

public import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
public import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Riemann.Paths.PreparedPathDecomposition
public import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Data.List.Membership

public section

/-!
# Ambient-side geometry of the actual retained exterior programs

The frame's complete adjacent-axis walks, including reversed top and left
sides, supply every segment's side certificate. These certificates descend
to the existing cached period parents without repeating their preparation.
-/

open _root_.Purelib.Polynomial.Geometry (ClearPath)
namespace Purelib.Riemann.Paths.PreparedExteriorPathGeometry.ClearPath

open Purelib.Data.List

open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- Every segment of the finite clear path joins two points on a common displayed box side.

The predicate follows the original segment spine and permits either orientation on each side, including stationary
segments. -/
@[expose] def OnBoxSides {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Rational.Box}
  (box : Rational.Box) :
    {start finish : Gaussian.Basic.Canonical} → Polynomial.Geometry.ClearPath polynomial ambient start finish → Prop
  | _, _, .nil _ => True
  | start, _, .cons (middle := middle) _ tail => SameSide box start middle ∧ OnBoxSides box tail

end Purelib.Riemann.Paths.PreparedExteriorPathGeometry.ClearPath

namespace Purelib.Riemann.Paths.PreparedExteriorPathGeometry.Grid

open Purelib.Data.List

open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (HorizontalLine VerticalLine)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk lookup)
open _root_.Purelib.Polynomial.Geometry.Grid.FramedClearGrid (AmbientFrame)
open _root_.Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame (Axes)
open Purelib.Polynomial.Geometry.Grid.Walks.Walk (horizontalIncreasing verticalIncreasing)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)

variable {polynomial : GaussianPolynomial}
  {ambient : Box}
  {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient}

namespace Walk

open Purelib.Data in
open Purelib.Geometry in
/-- Reversing the two endpoints preserves membership in a common box side. -/
private theorem side_reverse {box : Rational.Box} {first last : Gaussian.Basic.Canonical} (same :
  SameSide box first last) : SameSide box last first := by
  rcases same with same | same | same | same
  · exact Or.inl ⟨same.2, same.1⟩
  · exact Or.inr (Or.inl ⟨same.2, same.1⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨same.2, same.1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨same.2, same.1⟩))

section
open Purelib.Riemann
open Purelib.Data
open Purelib.Polynomial
section
open Purelib.Geometry
/-- Append two grid walks whose segments lie on displayed sides of the same box. -/
theorem onBoxSides_append {box : Rational.Box} : {start middle finish : Gaussian.Basic.Canonical} →
    (left : Geometry.Grid.Walks.Walk grid start middle) → (right : Geometry.Grid.Walks.Walk grid middle finish) →
    Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides box left.path →
      Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides box right.path →
      Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides box (left.append right).path
  | _, _, _, .nil _, _, _, after => after
  | _, _, _, .cons _ tail, right, before, after =>
      ⟨before.1, onBoxSides_append tail right before.2
        after⟩

/-- Reverse the first side-supported walk onto a side-supported continuation. -/
private theorem onBoxSides_reverseOnto {box : Rational.Box} : {start middle finish :
  Gaussian.Basic.Canonical} →
    (left : Geometry.Grid.Walks.Walk grid start middle) → (right : Geometry.Grid.Walks.Walk grid start finish) →
    Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides box left.path →
      Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides box right.path →
      Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides box (left.reverseOnto right).path
  | _, _, _, .nil _, _, _, after => after
  | _, _, _, .cons edge tail, right, before, after =>
      onBoxSides_reverseOnto
        tail (.cons (.reverse edge) right) before.2
        ⟨side_reverse before.1, after⟩

/-- Reversing a grid walk preserves its displayed box-side support. -/
theorem onBoxSides_reverse {box : Rational.Box} {start finish : Gaussian.Basic.Canonical} (walk :
  Geometry.Grid.Walks.Walk grid start finish)
    (sides : Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides box walk.path) :
    Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides box walk.reverse.path :=
  Paths.PreparedExteriorPathGeometry.Grid.Walk.onBoxSides_reverseOnto
    walk (.nil _) sides trivial

/-- Transporting walk endpoints preserves its displayed box-side support. -/
theorem onBoxSides_castEndpoints {box : Rational.Box} {start finish first last :
  Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid start finish)
    (startEq : start = first) (finishEq : finish = last)
    (sides : Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides box walk.path) :
    Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides box
      (walk.castEndpoints startEq finishEq).path := by
  cases startEq
  cases finishEq
  exact sides

end

/-- An increasing horizontal grid walk on the lower or upper ambient line stays on that side. -/
theorem horizontalIncreasing_onBoxSides (line : Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) (member :
  line ∈ grid.horizontal)
    (side : line.coordinate = ambient.yLower ∨ line.coordinate = ambient.yUpper) :
    {start finish : Rat.Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals start
      finish) →
    Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides ambient
      (Geometry.Grid.Walks.Walk.horizontalIncreasing line member walk).path
  | _, _, .nil _ => trivial
  | _, _, .cons _ _ tail => by
      refine ⟨?_, horizontalIncreasing_onBoxSides line member side tail⟩
      cases side with
      | inl equal => exact Or.inr (Or.inr (Or.inl ⟨equal, equal⟩))
      | inr equal => exact Or.inr (Or.inr (Or.inr ⟨equal, equal⟩))

/-- An increasing vertical grid walk on the left or right ambient line stays on that side. -/
theorem verticalIncreasing_onBoxSides (line : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (member : line ∈
  grid.vertical)
    (side : line.coordinate = ambient.xLower ∨ line.coordinate = ambient.xUpper) :
    {start finish : Rat.Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals start
      finish) →
    Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides ambient
      (Geometry.Grid.Walks.Walk.verticalIncreasing line member walk).path
  | _, _, .nil _ => trivial
  | _, _, .cons _ _ tail => by
      refine ⟨?_, verticalIncreasing_onBoxSides line member side tail⟩
      cases side with
      | inl equal => exact Or.inl ⟨equal, equal⟩
      | inr equal => exact Or.inr (Or.inl ⟨equal, equal⟩)

end

end Walk

namespace AmbientFrame

section
open Purelib.Riemann
open Purelib.Data
open Purelib.Polynomial
/-- The retained horizontal axis walk lies on the specified lower or upper ambient side. -/
private theorem horizontal_sides (axes : Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame.Axes grid) (y :
  Rat.Fraction.Rational) (member : y ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    (side : y = ambient.yLower ∨ y = ambient.yUpper) :
    Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides ambient
      (axes.horizontal y member).path := by
  apply Paths.PreparedExteriorPathGeometry.Grid.Walk.onBoxSides_castEndpoints
  apply Paths.PreparedExteriorPathGeometry.Grid.Walk.horizontalIncreasing_onBoxSides
  rcases side with side | side
  · subst y
    exact Or.inl (Geometry.Grid.AxisWalks.lookup ambient.yLower grid.horizontal member).coordinate_eq
  · subst y
    exact Or.inr (Geometry.Grid.AxisWalks.lookup ambient.yUpper grid.horizontal member).coordinate_eq

/-- The retained vertical axis walk lies on the specified left or right ambient side. -/
private theorem vertical_sides (axes : Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame.Axes grid) (x :
  Rat.Fraction.Rational) (member : x ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (side : x = ambient.xLower ∨ x = ambient.xUpper) :
    Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides ambient
      (axes.vertical x member).path := by
  apply Paths.PreparedExteriorPathGeometry.Grid.Walk.onBoxSides_castEndpoints
  apply Paths.PreparedExteriorPathGeometry.Grid.Walk.verticalIncreasing_onBoxSides
  rcases side with side | side
  · subst x
    exact Or.inl (Geometry.Grid.AxisWalks.lookup ambient.xLower grid.vertical member).coordinate_eq
  · subst x
    exact Or.inr (Geometry.Grid.AxisWalks.lookup ambient.xUpper grid.vertical member).coordinate_eq

end

open Purelib.Riemann in
open Purelib.Polynomial in
/-- Every segment of the retained ambient-frame boundary lies on its displayed side.

The proof follows all original adjacent-axis intervals, including the reversed top and left walks, preserving their
exact concatenation and endpoint transports. -/
theorem boundary_onBoxSides (frame : Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame grid) :
    Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides ambient frame.boundary.path := by
  exact Paths.PreparedExteriorPathGeometry.Grid.Walk.onBoxSides_append _ _ (horizontal_sides frame.axes _ frame.yLower
    (Or.inl rfl))
    (Paths.PreparedExteriorPathGeometry.Grid.Walk.onBoxSides_append _ _ (vertical_sides frame.axes _ frame.xUpper
      (Or.inr rfl))
      (Paths.PreparedExteriorPathGeometry.Grid.Walk.onBoxSides_append _ _
        (Paths.PreparedExteriorPathGeometry.Grid.Walk.onBoxSides_reverse _ (horizontal_sides frame.axes _ frame.yUpper
          (Or.inr rfl)))
        (Paths.PreparedExteriorPathGeometry.Grid.Walk.onBoxSides_reverse _ (vertical_sides frame.axes _ frame.xLower
          (Or.inl rfl)))))

end AmbientFrame
end Purelib.Riemann.Paths.PreparedExteriorPathGeometry.Grid

namespace Purelib.Riemann.Paths.PreparedExteriorPathGeometry.ParentCaches

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Geometry.Rational (Box)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments
  (ParentCaches)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments.ParentCaches
  (parents)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)

variable {genus : Nat} {curve : HyperellipticCurve genus} {ambient :
  Box} {differential :
  Differential genus} {sheet : Fin 2}

section
open Purelib.Data
open Purelib.Polynomial
/-- The first endpoint of a retained covered segment lies in its original ambient box. -/
private theorem first_inside {start finish : Gaussian.Basic.Canonical} {segment : Geometry.ClearPath.ClearSegment
  curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)} (piece : CoveredSegment segment owner) : ambient.Contains start := by
  simpa only [Geometry.ClearPath.ClearSegment.pointAt_zero] using segment.pointAt_contains piece.within 0 (by decide)

/-- The last endpoint of a retained covered segment lies in its original ambient box. -/
private theorem last_inside {start finish : Gaussian.Basic.Canonical} {segment : Geometry.ClearPath.ClearSegment
  curve.polynomial ambient start finish}
    {owner : Owner (curve.polynomial.eval start)} (piece : CoveredSegment segment owner) : ambient.Contains finish := by
  simpa only [Geometry.ClearPath.ClearSegment.pointAt_one] using segment.pointAt_contains piece.within 1 (by decide)

end

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
/-- Every cached segment parent inherits the original path's ambient-side geometry.

The proof follows the existing segment caches and uses their retained provenance equations; it does not repeat
polynomial or root preparation. -/
theorem onBoundary : ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial
  ambient start finish}
    {owner : Owner (curve.polynomial.eval start)} {prepared : PreparedPath path owner} {pieces : CoveredSegments
      prepared}
    (cache : Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments.ParentCaches
      differential sheet pieces),
    Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides ambient path →
      ∀ parent ∈ parents cache, ParentOnBoundary parent ambient
  | _, _, _, _, _, .nil _ _, _, _, _, member => False.elim (List.not_mem_nil member)
  | _, _, _, _, _, .cons first tail, cache, sides, parent, member => by
      rcases Membership.mem_append.mp member with member | member
      · exact Paths.PreparedSegmentBoundaryGeometry.segment_parent_boundary
          cache.1 (first_inside first) (last_inside first) sides.1 member
      · exact onBoundary cache.2 sides.2 parent member

end Purelib.Riemann.Paths.PreparedExteriorPathGeometry.ParentCaches

namespace Purelib.Riemann.Paths.PreparedExteriorPathGeometry.ParentCache

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Geometry.Rational (Box)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathDecomposition.CoveredTracedPath (segments)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- The complete materialized parent cache inherits its original path's ambient-side support.

The exact parent-list provenance supplies a segment decomposition, whose boundary certificates are transported back to
the retained cache. -/
theorem onBoundary {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {ambient :
  Rational.Box}
    {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {covered : CoveredTracedPath path
      owner}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus} {sheet : Fin 2}
    (cache : ParentCache covered differential sheet)
    (sides : Paths.PreparedExteriorPathGeometry.ClearPath.OnBoxSides ambient path) :
    ∀ parent ∈ cache.parents, PreparedBoundarySegments.ParentOnBoundary parent ambient := by
  let pieces := segments covered
  have equal : cache.parents =
      Paths.PreparedSegmentParentBanks.PreparedPath.CoveredSegments.parents
        differential sheet pieces :=
    cache.parents_eq.trans
      (Paths.PreparedSegmentParentBanks.PreparedPath.CoveredSegments.parents_eq
        differential sheet pieces).symm
  let split :=
    Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments.ParentCaches.build
      differential sheet pieces cache.parents equal cache.covered
  have bounded :=
    Paths.PreparedExteriorPathGeometry.ParentCaches.onBoundary split sides
  rw [Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath.CoveredSegments.ParentCaches.build_parents
    pieces cache.parents equal cache.covered] at bounded
  exact bounded

end Purelib.Riemann.Paths.PreparedExteriorPathGeometry.ParentCache
