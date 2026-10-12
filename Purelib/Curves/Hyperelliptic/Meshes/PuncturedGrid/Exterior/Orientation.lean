module
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.PreparedExteriorPathGeometry
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry.Rational.Box

open Purelib.Integration.Energy

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

open Purelib.Polynomial.Geometry.Grid.FramedClearGrid

open Purelib.Polynomial.Geometry.Grid.FramedClearGrid

open Purelib.Polynomial.Geometry.Grid.Walks

open Purelib.Riemann.Paths.PreparedExteriorPathGeometry

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

@[expose] public section

/-!
# Orientation of the actual reciprocal exterior edges

Every retained adjacent interval has positive angular orientation about the
ambient origin. Inversion reverses that orientation, so the opposite cap
edge has positive coordinate area. These are reciprocal w-coordinates; in
odd degree their later lift to the t² = w chart is a separate obligation.
-/

namespace Purelib.Polynomial.Geometry.Grid.Walks.Walk

open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (VerticalLine HorizontalLine)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk lookup)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : ClearGrid polynomial
  ambient}

/-- The supplied endpoint relation holds on every actual directed edge of the original grid walk. -/
def Edgewise (relation : Data.Gaussian.Basic.Canonical → Data.Gaussian.Basic.Canonical → Prop) : {start finish :
  Data.Gaussian.Basic.Canonical} → Walks.Walk grid start finish → Prop
  | _, _, .nil _ => True
  | start, _, .cons (middle := middle) _ tail => relation start middle ∧
    Edgewise relation tail

namespace Edgewise

variable {relation : Purelib.Data.Gaussian.Basic.Canonical → Purelib.Data.Gaussian.Basic.Canonical → Prop}

/-- Concatenating actual grid walks preserves their common edgewise endpoint relation. -/
theorem append : {start middle finish : Data.Gaussian.Basic.Canonical} → (first : Walks.Walk grid start middle) → (last
  : Walks.Walk grid middle finish) →
    first.Edgewise relation → last.Edgewise relation → (first.append last).Edgewise relation
  | _, _, _, .nil _, _, _, after => after
  | _, _, _, .cons _ tail, last, before, after => ⟨before.1, append
    tail last before.2 after⟩

/-- Reversing one actual walk onto another preserves the supplied reversed and forward edgewise relations. -/
private theorem reverseOnto : {start middle finish : Data.Gaussian.Basic.Canonical} → (first : Walks.Walk grid start
  middle) → (last : Walks.Walk grid start finish) →
    first.Edgewise (fun first last => relation last first) → last.Edgewise relation → (first.reverseOnto last).Edgewise
      relation
  | _, _, _, .nil _, _, _, after => after
  | _, _, _, .cons edge tail, last, before, after => reverseOnto
    tail (.cons (.reverse edge) last) before.2 ⟨before.1, after⟩

/-- Reversing an actual grid walk reverses its edgewise endpoint relation. -/
theorem reverse {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk grid start finish)
    (oriented : walk.Edgewise (fun first last => relation last first)) : walk.reverse.Edgewise relation :=
  Polynomial.Geometry.Grid.Walks.Walk.Edgewise.reverseOnto walk (.nil _) oriented trivial

/-- Transporting the endpoint indices preserves the original walk's edgewise relation. -/
theorem castEndpoints {start finish first last : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk grid start finish)
    (startEq : start = first) (finishEq : finish = last) (oriented : walk.Edgewise relation) :
    (walk.castEndpoints startEq finishEq).Edgewise relation := by
  cases startEq; cases finishEq; exact oriented

/-- A relation on increasing horizontal endpoints holds on every actual edge of the retained horizontal grid walk. -/
theorem horizontalIncreasing (line : ClearGrid.HorizontalLine polynomial ambient) (member : line ∈ grid.horizontal)
    (oriented : ∀ first last : Fraction.Rational, first < last → relation (Components.Basic.point first line.coordinate)
      (Components.Basic.point last line.coordinate)) :
    {start finish : Fraction.Rational} → (walk : AxisWalks.IncreasingWalk grid.xIntervals start finish) →
      (Walk.horizontalIncreasing line member walk).Edgewise relation
  | _, _, .nil _ => trivial
  | _, _, .cons interval _ tail => ⟨oriented _ _ interval.ordered,
    horizontalIncreasing line member oriented tail⟩

/-- A relation on increasing vertical endpoints holds on every actual edge of the retained vertical grid walk. -/
theorem verticalIncreasing (line : ClearGrid.VerticalLine polynomial ambient) (member : line ∈ grid.vertical)
    (oriented : ∀ first last : Fraction.Rational, first < last → relation (Components.Basic.point line.coordinate first)
      (Components.Basic.point line.coordinate last)) :
    {start finish : Fraction.Rational} → (walk : AxisWalks.IncreasingWalk grid.yIntervals start finish) →
      (Walk.verticalIncreasing line member walk).Edgewise relation
  | _, _, .nil _ => trivial
  | _, _, .cons interval _ tail => ⟨oriented _ _ interval.ordered,
    verticalIncreasing line member oriented tail⟩

open Purelib.Polynomial.Geometry.Grid.Walks.Walk in
/-- The original walk's edgewise relation holds on the actual lifted indexed edges under the retained vertex
coordinates.

Structural membership retains the actual head edge or original indexed tail.
Their cached endpoint coordinates satisfy the same supplied edge relation. -/
theorem indexed {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges : RootEdgeBank frames) (vertices :
  LiftedVertices.VertexBank grid) :
    {start finish : Data.Gaussian.Basic.Canonical} → (walk : Walks.Walk grid start finish) → walk.Edgewise relation →
      (sheet : Fin 2) →
    ∀ edge ∈ edges.indexedEdges vertices walk sheet,
      relation (vertices.coordinate edge.start) (vertices.coordinate edge.finish)
  | _, _, .nil _, _, _, _, member => (List.not_mem_nil member).elim
  | _, _, .cons edge tail, oriented, sheet, selected, member => by
      rcases Membership.mem_cons.mp member with rfl | member
      · simp only [RootEdgeBank.indexedEdge, vertices.coordinate_index]
        exact oriented.1
      · exact indexed edges vertices tail oriented.2 _ selected
          member

/-- Every actual edge endpoint of the retained box-side walk lies on the original ambient boundary. -/
theorem onBoxBoundary : {start finish : Data.Gaussian.Basic.Canonical} → (walk : Walks.Walk grid start finish) →
  ClearPath.OnBoxSides ambient walk.path →
    walk.Edgewise (fun first last => Boundary.OnBoxBoundary ambient first ∧ Boundary.OnBoxBoundary ambient last)
  | _, _, .nil _, _ => trivial
  | start, _, .cons (middle := middle) edge tail, sides => by
      have firstInside : ambient.Contains start := by
        simpa only [ClearSegment.pointAt_zero] using edge.segment.pointAt_contains edge.withinAmbient 0 (by decide)
      have lastInside : ambient.Contains middle := by
        simpa only [ClearSegment.pointAt_one] using edge.segment.pointAt_contains edge.withinAmbient 1 (by decide)
      refine ⟨?_, onBoxBoundary tail sides.2⟩
      rcases sides.1 with side | side | side | side
      · exact ⟨⟨firstInside, Or.inl side.1⟩, ⟨lastInside, Or.inl side.2⟩⟩
      · exact ⟨⟨firstInside, Or.inr (Or.inl side.1)⟩, ⟨lastInside, Or.inr (Or.inl side.2)⟩⟩
      · exact ⟨⟨firstInside, Or.inr (Or.inr (Or.inl side.1))⟩, ⟨lastInside, Or.inr (Or.inr (Or.inl side.2))⟩⟩
      · exact ⟨⟨firstInside, Or.inr (Or.inr (Or.inr side.1))⟩, ⟨lastInside, Or.inr (Or.inr (Or.inr side.2))⟩⟩

end Edgewise
end Purelib.Polynomial.Geometry.Grid.Walks.Walk

namespace Purelib.Riemann.Topology.PreparedEnergySurface

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Field (inv)
open Purelib.Data.Gaussian.Norm.Basic (normSq_pos)
open Purelib.Data.Gaussian.Field (inv_eq)
open Purelib.Data.Gaussian.Basic (zero_re zero_im)

/-- The origin-based signed area of a horizontal edge is its negative height times its horizontal displacement, divided
by two.

The original two endpoint coordinates share the displayed height. Expanding
the origin-based determinant preserves its signed displacement and exact
rational factor one half. -/
theorem origin_area_horizontal (first last y : Fraction.Rational) :
    Purelib.Integration.Energy.AffineTriangle.coordinateTriangleArea 0 (Purelib.Data.Gaussian.Components.Basic.point
      first y) (Purelib.Data.Gaussian.Components.Basic.point last y) = -y * (last - first) / 2 := by
  unfold AffineTriangle.coordinateTriangleArea Components.Basic.point
  simp only [Basic.zero_re, Basic.zero_im, Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- The origin-based signed area of a vertical edge is its horizontal coordinate times its vertical displacement,
divided by two.

The original two endpoint coordinates share the displayed horizontal value.
Their signed vertical displacement retains the exact determinant orientation
and rational factor one half. -/
theorem origin_area_vertical (x first last : Fraction.Rational) :
    Purelib.Integration.Energy.AffineTriangle.coordinateTriangleArea 0 (Purelib.Data.Gaussian.Components.Basic.point x
      first) (Purelib.Data.Gaussian.Components.Basic.point x last) = x * (last - first) / 2 := by
  unfold AffineTriangle.coordinateTriangleArea Components.Basic.point
  simp only [Basic.zero_re, Basic.zero_im, Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- Exact denominator-cleared orientation of the reciprocal fan.

Both retained inverse endpoints use their original norm-square denominators.
Scalar field identities preserve the reversed reciprocal orientation and the
exact product of those denominators. -/
theorem reciprocal_origin_area (first last : Data.Gaussian.Basic.Canonical) :
    AffineTriangle.coordinateTriangleArea 0 last⁻¹ first⁻¹ = AffineTriangle.coordinateTriangleArea 0 first last /
      (Data.Gaussian.Norm.Basic.normSq first * Data.Gaussian.Norm.Basic.normSq last) := by
  simp only [AffineTriangle.coordinateTriangleArea, Data.Gaussian.Field.inv_eq, Data.Gaussian.Field.inv, Basic.zero_re,
    Basic.zero_im,
    Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.inv_mul_direct]
  ring1

/-- Inverting and reversing an original positively oriented edge preserves positive origin-based coordinate area. -/
theorem reciprocal_origin_positive {first last : Data.Gaussian.Basic.Canonical}
    (oriented : 0 < Purelib.Integration.Energy.AffineTriangle.coordinateTriangleArea 0 first last) : 0 <
      Purelib.Integration.Energy.AffineTriangle.coordinateTriangleArea 0 last⁻¹ first⁻¹ := by
  have firstNonzero : first ≠ 0 := by
    intro equal
    rw [equal] at oriented
    have zeroArea : AffineTriangle.coordinateTriangleArea 0 0 last = 0 := by
      unfold AffineTriangle.coordinateTriangleArea
      simp only [Basic.zero_re, Basic.zero_im, Fraction.Field.div_eq_mul_inv_direct]
      ring1
    exact (ne_of_gt oriented) zeroArea
  have lastNonzero : last ≠ 0 := by
    intro equal
    rw [equal] at oriented
    have zeroArea : AffineTriangle.coordinateTriangleArea 0 first 0 = 0 := by
      unfold AffineTriangle.coordinateTriangleArea
      simp only [Basic.zero_re, Basic.zero_im, Fraction.Field.div_eq_mul_inv_direct]
      ring1
    exact (ne_of_gt oriented) zeroArea
  rw [reciprocal_origin_area]
  exact Fraction.Order.Field.div_pos_direct oriented
    (Fraction.Order.Arithmetic.mul_pos_direct (Data.Gaussian.Norm.Basic.normSq_pos firstNonzero)
      (Data.Gaussian.Norm.Basic.normSq_pos lastNonzero))

end Purelib.Riemann.Topology.PreparedEnergySurface

namespace Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame

open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (VerticalLine HorizontalLine)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk lookup)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Integration.Energy.AffineTriangle (coordinateTriangleArea)
open Purelib.Riemann.Topology.PreparedEnergySurface (origin_area_horizontal origin_area_vertical)
open _root_.Purelib.Polynomial.Geometry.Grid.FramedClearGrid (AmbientFrame)
open _root_.Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame (Axes)

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : ClearGrid polynomial
  ambient}

section
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame
/-- The selected retained horizontal grid walk inherits the supplied relation on increasing endpoints. -/
private theorem horizontal_oriented (axes : AmbientFrame.Axes grid) (y : Fraction.Rational) (member : y ∈
  grid.horizontal.map HorizontalLine.coordinate)
    (relation : Data.Gaussian.Basic.Canonical → Data.Gaussian.Basic.Canonical → Prop)
    (oriented : ∀ first last : Fraction.Rational, first < last → relation (Components.Basic.point first y)
      (Components.Basic.point last y)) :
    (axes.horizontal y member).Edgewise relation := by
  apply Polynomial.Geometry.Grid.Walks.Walk.Edgewise.castEndpoints
  apply Polynomial.Geometry.Grid.Walks.Walk.Edgewise.horizontalIncreasing
  rw [(AxisWalks.lookup y grid.horizontal member).coordinate_eq]
  exact oriented

/-- The selected retained vertical grid walk inherits the supplied relation on increasing endpoints. -/
private theorem vertical_oriented (axes : AmbientFrame.Axes grid) (x : Fraction.Rational) (member : x ∈
  grid.vertical.map VerticalLine.coordinate)
    (relation : Data.Gaussian.Basic.Canonical → Data.Gaussian.Basic.Canonical → Prop)
    (oriented : ∀ first last : Fraction.Rational, first < last → relation (Components.Basic.point x first)
      (Components.Basic.point x last)) :
    (axes.vertical x member).Edgewise relation := by
  apply Polynomial.Geometry.Grid.Walks.Walk.Edgewise.castEndpoints
  apply Polynomial.Geometry.Grid.Walks.Walk.Edgewise.verticalIncreasing
  rw [(AxisWalks.lookup x grid.vertical member).coordinate_eq]
  exact oriented

end

/-- Every actual retained ambient-frame boundary edge has positive origin-based coordinate area when the box contains
the origin strictly. -/
theorem boundary_oriented (frame : AmbientFrame grid)
    (left : ambient.xLower < 0) (right : 0 < ambient.xUpper) (bottom : ambient.yLower < 0) (top : 0 < ambient.yUpper) :
    frame.boundary.Edgewise (fun first last => 0 < AffineTriangle.coordinateTriangleArea 0 first last) := by
  apply Polynomial.Geometry.Grid.Walks.Walk.Edgewise.append
  · apply horizontal_oriented
    intro first last increasing
    rw [Riemann.Topology.PreparedEnergySurface.origin_area_horizontal]
    exact Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.mul_pos_direct ((Fraction.Order.Arithmetic.sub_pos_direct bottom).trans_eq (by ring1))
        (Fraction.Order.Arithmetic.sub_pos_direct increasing)) (by decide)
  · apply Polynomial.Geometry.Grid.Walks.Walk.Edgewise.append
    · apply vertical_oriented
      intro first last increasing
      rw [Riemann.Topology.PreparedEnergySurface.origin_area_vertical]
      exact Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Arithmetic.mul_pos_direct right (Fraction.Order.Arithmetic.sub_pos_direct increasing)) (by
          decide)
    · apply Polynomial.Geometry.Grid.Walks.Walk.Edgewise.append
      · apply Polynomial.Geometry.Grid.Walks.Walk.Edgewise.reverse
        apply horizontal_oriented
        intro first last increasing
        rw [Riemann.Topology.PreparedEnergySurface.origin_area_horizontal]
        have equal : -ambient.yUpper * (first - last) = ambient.yUpper * (last - first) := by ring1
        rw [equal]
        exact Fraction.Order.Field.div_pos_direct
          (Fraction.Order.Arithmetic.mul_pos_direct top (Fraction.Order.Arithmetic.sub_pos_direct increasing)) (by
            decide)
      · apply Polynomial.Geometry.Grid.Walks.Walk.Edgewise.reverse
        apply vertical_oriented
        intro first last increasing
        rw [Riemann.Topology.PreparedEnergySurface.origin_area_vertical]
        have equal : ambient.xLower * (first - last) = -ambient.xLower * (last - first) := by ring1
        rw [equal]
        exact Fraction.Order.Field.div_pos_direct
          (Fraction.Order.Arithmetic.mul_pos_direct ((Fraction.Order.Arithmetic.sub_pos_direct left).trans_eq (by
            ring1)) (Fraction.Order.Arithmetic.sub_pos_direct increasing)) (by decide)

end Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Integration.Energy.AffineTriangle (coordinateTriangleArea)
open Purelib.Riemann.Topology.PreparedEnergySurface (reciprocal_origin_positive)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram exteriorWalk
  exteriorWalk_sides)
open _root_.Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame (boundary_oriented)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential :
    Differential genus}

/-- Every actual original exterior-program edge has positive origin-based coordinate area.

The original ambient frame has negative lower and positive upper sides. Its
retained exterior walk follows the original parity branch, preserving every
ordered boundary edge and its positive coordinate area. -/
theorem walk_oriented (program : PeriodPrograms.ExteriorProgram lifted differential) :
    program.period.closed.walk.Edgewise (fun first last => 0 < AffineTriangle.coordinateTriangleArea 0 first last) := by
  have positive := ReciprocalExteriorCollar.radius_positive curve
  have frame := base.bank.frame.boundary_oriented ((Fraction.Order.Arithmetic.neg_lt_neg_direct positive).trans_eq (by
    ring1)) positive ((Fraction.Order.Arithmetic.neg_lt_neg_direct positive).trans_eq (by ring1)) positive
  have oriented : program.period.closed.walk.Edgewise (fun first last => 0 < AffineTriangle.coordinateTriangleArea 0
    first last) := by
    rw [program.walk_eq]
    cases shape : curve.degreeShape with
    | odd _ =>
        simp only [PeriodPrograms.exteriorWalk, shape]
        exact Polynomial.Geometry.Grid.Walks.Walk.Edgewise.append _ _ frame frame
    | even _ =>
        simp only [PeriodPrograms.exteriorWalk, shape]
        exact frame
  exact oriented

/-- Every actual indexed exterior edge retains positive origin-based coordinate area. -/
theorem indexed_oriented (program : PeriodPrograms.ExteriorProgram lifted differential) : ∀ edge ∈ program.indexed,
    0 < AffineTriangle.coordinateTriangleArea 0 (lifted.vertices.coordinate edge.start) (lifted.vertices.coordinate
      edge.finish) :=
  Polynomial.Geometry.Grid.Walks.Walk.Edgewise.indexed lifted.edges lifted.vertices program.period.closed.walk
    program.walk_oriented program.sheet

/-- Every actual reversed reciprocal exterior edge has positive origin-based coordinate area. -/
theorem indexed_reciprocal_oriented (program : PeriodPrograms.ExteriorProgram lifted differential) : ∀ edge ∈
  program.indexed,
    0 < AffineTriangle.coordinateTriangleArea 0 (lifted.vertices.coordinate edge.finish)⁻¹ (lifted.vertices.coordinate
      edge.start)⁻¹ :=
  fun edge member => Riemann.Topology.PreparedEnergySurface.reciprocal_origin_positive (program.indexed_oriented edge
    member)

/-- Both actual endpoints of every indexed exterior-program edge lie on the original curve ambient boundary. -/
theorem indexed_boundary (program : PeriodPrograms.ExteriorProgram lifted differential) : ∀ edge ∈ program.indexed,
    Boundary.OnBoxBoundary (Cuts.Ambient curve) (lifted.vertices.coordinate edge.start) ∧
      Boundary.OnBoxBoundary (Cuts.Ambient curve) (lifted.vertices.coordinate edge.finish) :=
  Polynomial.Geometry.Grid.Walks.Walk.Edgewise.indexed lifted.edges lifted.vertices program.period.closed.walk
    (Polynomial.Geometry.Grid.Walks.Walk.Edgewise.onBoxBoundary _ (by
        rw [program.walk_eq];
        exact PeriodPrograms.exteriorWalk_sides base)) program.sheet

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram
