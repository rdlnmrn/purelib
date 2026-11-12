module

public import Purelib.Riemann.Paths.ClearBoxPaths
public import Purelib.Polynomial.Geometry.Grid.FromPartition
public import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Topology.Surface.Sewing.PolygonSewing

/-!
# Oriented interior chords and their cleared axis routes

The original closed-box clearance certifies the two axis legs through the
actual mixed-coordinate corner. Both leg occurrences remain in the clear
path, including stationary legs. A local cut grid is built from the same
endpoints; no full-ambient line clearance is inferred.

The physical chord and the axis route bound one explicit oriented triangle.
The retained EdgeRoute states the exact signed correction for arbitrary
antisymmetric readings. It neither discards that correction nor identifies
independently acquired roots, primitive constants or period programmes.
-/

public section

namespace Purelib.Riemann.Paths.ClearBoxPaths

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial ClearSegment)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.PolygonSewing.PolygonStokes (BoundarySplit)

universe u

namespace Route

variable {polynomial : GaussianPolynomial} {box : Box}

/-- Retain both original axis-leg occurrences through the mixed-coordinate corner.

Unlike the normalized connector, this path always has two segments. Equal
coordinates and coincident endpoints retain their actual stationary legs.
Both line certificates reuse the supplied whole-box clearance bound.
-/
def throughCorner (clearance : RegionClearance polynomial box) (start finish : Canonical)
    (first : box.Contains start) (last : box.Contains finish) : Route polynomial box start finish :=
  let horizontalLeg : ClearSegment polynomial box start (point finish.re start.im) :=
    .horizontal start.re finish.re start.im first.1 first.2.1 last.1 last.2.1
      (horizontal clearance start.im first.2.2)
  let verticalLeg : ClearSegment polynomial box (point finish.re start.im) finish :=
    .vertical finish.re start.im finish.im first.2.2.1 first.2.2.2 last.2.2.1 last.2.2.2
      (vertical clearance finish.re ⟨last.1, last.2.1⟩)
  ⟨.cons horizontalLeg (.cons verticalLeg (.nil finish)),
    .cons first.2.2 (.cons ⟨last.1, last.2.1⟩ (.nil finish)), by change 2 ≤ 2; exact Nat.le_refl _⟩

/-- The retained connector has two segment occurrences even at repeated coordinates. -/
theorem throughCorner_count (clearance : RegionClearance polynomial box) (start finish : Canonical)
    (first : box.Contains start) (last : box.Contains finish) :
    (throughCorner clearance start finish first last).path.segmentCount = 2 := by
  unfold throughCorner
  rfl

/-- Both endpoint vertices also place the mixed-coordinate corner on the same grid. -/
theorem throughCorner_vertices (clearance : RegionClearance polynomial box)
    (start finish : Canonical) (first : box.Contains start) (last : box.Contains finish)
    {ambient : Box} (grid : ClearGrid polynomial ambient)
    (a : FromStates.ContainsVertex grid start) (b : FromStates.ContainsVertex grid finish) :
    FromStates.ContainsPathVertices grid (throughCorner clearance start finish first last).path :=
by
  change FromStates.ContainsVertex grid start ∧
    FromStates.ContainsVertex grid (point finish.re start.im) ∧ FromStates.ContainsVertex grid finish
  exact ⟨a, ⟨b.1, a.2⟩, b⟩

end Route

namespace Chord

variable {polynomial : GaussianPolynomial} {box : Box}

/-- The actual corner uses the finish's real coordinate and start's imaginary coordinate. -/
def corner (start finish : Canonical) : Canonical := point finish.re start.im

/-- The complete original corner is the finish-real/start-imaginary Gaussian pair. -/
theorem corner_eq (start finish : Canonical) : corner start finish = (⟨finish.re, start.im⟩ : Canonical) := by
  unfold corner
  rfl

/-- The mixed-coordinate corner lies in the same original endpoint box. -/
theorem corner_inside {start finish : Canonical} (first : box.Contains start) (last : box.Contains finish) :
    box.Contains (corner start finish) := ⟨last.1, last.2.1, first.2.2.1, first.2.2.2⟩

/-- Every point of the actual physical chord remains in its original endpoint box. -/
theorem inside {start finish : Canonical} (first : box.Contains start) (last : box.Contains finish)
    {parameter : Rational} (unit : 0 ≤ parameter ∧ parameter ≤ 1) :
    box.Contains (Geometry.Rational.Affine.line start (finish - start) parameter) :=
  Box.contains_line first last unit

/-- The three literal slots retain corner, start and finish independently of coordinate repetitions. -/
def coordinate (start finish : Canonical) : Fin 3 → Canonical :=
  Fin.cases (corner start finish) (Fin.cases start (Fin.cases finish Fin.elim0))

/-- The three actual slot readbacks preserve corner, start and finish in that order. -/
theorem coordinate_values (start finish : Canonical) :
    coordinate start finish 0 = corner start finish ∧
      coordinate start finish 1 = start ∧ coordinate start finish 2 = finish :=
  ⟨rfl, rfl, rfl⟩

/-- Every slot of the oriented correction triangle belongs to the original cleared box. -/
theorem coordinate_inside {start finish : Canonical} (first : box.Contains start) (last : box.Contains finish)
    (slot : Fin 3) : box.Contains (coordinate start finish slot) :=
  Fin.cases (corner_inside first last) (Fin.cases first (Fin.cases last (fun index => Fin.elim0 index))) slot

/-- The correction triangle retains the cyclic corner/start/finish order on three distinct slots. -/
def faces (_ : Fin 1) : OrientedTriangle 3 := ⟨0, 1, 2⟩

/-- The original oriented correction face reads the same three literal slots. -/
theorem faces_zero : faces 0 = (⟨0, 1, 2⟩ : OrientedTriangle 3) := by
  unfold faces
  rfl

/-- The two axis sides are retained in the original triangle's cyclic order. -/
def boundary : List (OrientedEdge 3) := [⟨2, 0⟩, ⟨0, 1⟩]

/-- Replace the oriented physical chord by the two reversed axis sides and its full triangle correction.

The original triangle retraction removes only the chord occurrence. Its
reverse yields start-to-corner-to-finish, with one positive triangle term.
The incidence statement requires no primitive or period equality.
-/
def incidence : SewingRetraction.EdgeRoute faces boundary (⟨1, 2⟩ : OrientedEdge 3) :=
  let original := SewingRetraction.Retraction.triangle faces 0
  let selected : BoundarySplit (faces 0).boundary := ⟨[⟨0, 1⟩], ⟨1, 2⟩, [⟨2, 0⟩], rfl⟩
  let backwards : SewingRetraction.EdgeRoute faces boundary (⟨2, 1⟩ : OrientedEdge 3) :=
    original.across selected ⟨2, 1⟩ rfl (fun _ member => member)
  backwards.reverse

/-- The actual route visits start, corner and finish in that order without deleting stationary occurrences. -/
theorem incidence_path : incidence.path = [⟨1, 0⟩, ⟨0, 2⟩] := by
  unfold incidence
  rfl

/-- The full correction contains one positive occurrence of the retained oriented triangle. -/
theorem incidence_correction : incidence.correction = [(1, 0)] := by
  unfold incidence
  rfl

/-- A chord preparation retains the original local cuts, whole cleared grid and two-leg route.

The exact constructor equalities preserve all three caches. The axis grid
may identify equal coordinates, while the original route and triangle
slots continue to retain both ordered segment occurrences.
-/
abbrev Prepared (clearance : RegionClearance polynomial box) (proper : box.Proper)
    (start finish : Canonical) (first : box.Contains start) (last : box.Contains finish) :=
  (cuts : { value : CutPartition box [start, finish] // value = CutPartition.build box proper [start, finish] }) ×
  { value : ClearGrid polynomial box // value = ClearGrid.ofPartition cuts.val clearance } ×
  { value : Route polynomial box start finish // value = Route.throughCorner clearance start finish first last }

/-- Build the two endpoint cuts, their cleared local grid and the occurrence-preserving route once. -/
def prepare (clearance : RegionClearance polynomial box) (proper : box.Proper)
    (start finish : Canonical) (first : box.Contains start) (last : box.Contains finish) :
    Prepared clearance proper start finish first last :=
  let cuts := CutPartition.build box proper [start, finish]
  let grid := ClearGrid.ofPartition cuts clearance
  let route := Route.throughCorner clearance start finish first last
  ⟨⟨cuts, rfl⟩, ⟨grid, rfl⟩, ⟨route, rfl⟩⟩

namespace Prepared

variable {clearance : RegionClearance polynomial box} {proper : box.Proper} {start finish : Canonical}
    {first : box.Contains start} {last : box.Contains finish}
    (cached : Prepared clearance proper start finish first last)

/-- Read the SAME original endpoint-cut partition. -/
abbrev cuts := cached.1.val

/-- Read the SAME once-certified local coordinate grid. -/
abbrev grid := cached.2.1.val

/-- Read the SAME two-leg route, including stationary leg occurrences. -/
abbrev route := cached.2.2.val

/-- The whole partition is the original finite endpoint-cut factory. -/
theorem cuts_eq : cached.cuts = CutPartition.build box proper [start, finish] := cached.1.property

/-- The whole grid is the original construction on the retained cuts and clearance. -/
theorem grid_eq : cached.grid = ClearGrid.ofPartition cached.cuts clearance := cached.2.1.property

/-- The whole route is the original two-leg factory at the actual rational endpoints. -/
theorem route_eq : cached.route = Route.throughCorner clearance start finish first last := cached.2.2.property

/-- Every original route slot lies on the SAME retained local coordinate grid. -/
theorem vertices : FromStates.ContainsPathVertices cached.grid cached.route.path := by
  have a := ClearGrid.ofPartition_contains_of_eq cached.cuts clearance cached.grid_eq
    start List.mem_cons_self first
  have b := ClearGrid.ofPartition_contains_of_eq cached.cuts clearance cached.grid_eq
    finish (List.mem_cons_of_mem _ List.mem_cons_self) last
  exact Eq.mpr (congrArg (fun value : Route polynomial box start finish =>
    FromStates.ContainsPathVertices cached.grid value.path) cached.route_eq)
    (Route.throughCorner_vertices clearance start finish first last cached.grid a b)

/-- The retained route keeps exactly two original occurrences, independently of adjacent-grid simplification. -/
theorem segmentCount : cached.route.path.segmentCount = 2 :=
  (congrArg (fun value : Route polynomial box start finish => value.path.segmentCount) cached.route_eq).trans
    (Route.throughCorner_count clearance start finish first last)

end Prepared

/-- Consume one retained chord preparation and one actual adjacent-grid subdivision.

The original two-leg route is forwarded alongside its subdivided walk, so
stationary or repeated source occurrences are not confused with the walk's
normalized edge spine. The subdivision uses the SAME retained grid/path
and its actual vertex certificate; it acquires no roots or observations.
-/
def withWalk {Result : Type u} (clearance : RegionClearance polynomial box) (proper : box.Proper)
    (start finish : Canonical) (first : box.Contains start) (last : box.Contains finish)
    (consume : (cached : Prepared clearance proper start finish first last) →
      (walk : Walks.Walk cached.grid start finish) →
      walk = Walks.splitPath cached.grid cached.route.path cached.vertices → Result) : Result :=
  let cached := prepare clearance proper start finish first last
  let walk := Walks.splitPath cached.grid cached.route.path cached.vertices
  consume cached walk rfl

end Chord

end Purelib.Riemann.Paths.ClearBoxPaths

end
