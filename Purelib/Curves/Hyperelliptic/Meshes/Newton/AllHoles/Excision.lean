module
import Purelib.Data.List.Filter
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Pairwise

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.GridLiftedFaceSelection
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Init.Data.List.Lemmas
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.Boundary.Values
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Tactic.Ring
import Purelib.Riemann.Meshes.GridLiftedBoundary

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid

open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-!
# Simultaneous excision of every retained Newton annulus

The entries follow the actual classified hole list, not a new enumeration
or root lookup. Separated bands select disjoint original face occurrences.
Their exact signed triangle partition cancels every original inward hole
tour, leaving the fixed exterior and the actual two-lap Newton-band tours.
No analytic primitive gluing or small-area assertion is assumed here.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint edgeListArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace BranchHole)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (triangleArea)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_congr sumValues_map sumValues_add)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
    {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid grid.punctured}

set_option genInjectivity false in
/-- A band region attached to the literal cached hole payload. -/
structure AnnularEntry (grid : BranchCellBank.NewtonGrid preparation target radius) (lifted : Meshes.LiftedPuncturedGrid
  grid.punctured) where
  /-- The exact original classified branch-hole payload retained by this annular entry. -/ hole :
    PuncturedGridFaces.BranchHole grid.shrunk.prepared.toBranchCellBank
  /-- The original Newton-band annulus indexed by the retained hole's branch label. -/ annulus : Faces.AnnularFaces grid
    hole.index
  /-- The cached lifted annular region on the same original complete lifted mesh. -/ region : LiftedBoundary.Lifted
    annulus lifted
  /-- The lifted region retains exactly this original hole payload. -/ hole_eq : region.hole = hole
  /-- The retained region triangles are exactly the original lifted faces selected by this hole's Newton band. -/
    selection_eq : region.triangles =
    (GridLiftedFaceSelection.select
      (fun face => decide (face.cell.box.Refines (grid.bands.box hole.index))) lifted.mesh.lifts).selected.triangles

constructive_injectivity AnnularEntry

namespace AnnularEntry

/-- Construct the annular entry from the supplied original classified hole without reacquiring its branch owner. -/
def ofHole (lifted : Meshes.LiftedPuncturedGrid grid.punctured)
    (hole : PuncturedGridFaces.BranchHole grid.shrunk.prepared.toBranchCellBank) (member : hole ∈ grid.faces.holes) :
      Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted :=
  let annulus := AnnularFaces.build grid hole.index
  { hole := hole
    annulus := annulus
    region := Lifted.ofHole annulus lifted hole member rfl
    hole_eq := rfl
    selection_eq := Lifted.ofHole_triangles annulus lifted hole member rfl }

/-- Decide whether the original regular face lies inside this retained hole's Newton band. -/
def keep (entry : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted) (face :
  PuncturedGridFaces.RegularFace grid.shrunk.prepared.toBranchCellBank) : Bool :=
  decide (face.cell.box.Refines (grid.bands.box entry.hole.index))

/-- Distinct original branch labels have disjoint retained Newton-band face selections. -/
theorem disjoint (first second : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted)
  (different : first.hole.index ≠ second.hole.index)
    (face : PuncturedGridFaces.RegularFace grid.shrunk.prepared.toBranchCellBank) (left : first.keep face = true)
    (right : second.keep face = true) : False :=
  (grid.bands.separated first.hole.index second.hole.index different).points_ne
    ((of_decide_eq_true left).contains face.cell.box.contains_anchor)
    ((of_decide_eq_true right).contains face.cell.box.contains_anchor) rfl

/-- Construct annular entries following the exact original classified hole list. -/
public def fromHoles (lifted : Meshes.LiftedPuncturedGrid grid.punctured) :
    (holes : List (PuncturedGridFaces.BranchHole grid.shrunk.prepared.toBranchCellBank)) →
      (∀ hole ∈ holes, hole ∈ grid.faces.holes) → List
        (Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted)
  | [], _ => []
  | hole :: tail, member => Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry.ofHole lifted hole (member
    hole List.mem_cons_self) ::
      Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry.fromHoles lifted tail (fun other belongs
        => member other (List.mem_cons_of_mem _ belongs))

/-- The retained annular entries read back exactly the original hole payload list. -/
public theorem fromHoles_holes (lifted : Meshes.LiftedPuncturedGrid grid.punctured) :
    (holes : List (PuncturedGridFaces.BranchHole grid.shrunk.prepared.toBranchCellBank)) →
      (member : ∀ hole ∈ holes, hole ∈ grid.faces.holes) →
      (Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry.fromHoles lifted holes member).map
        Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry.hole = holes
  | [], _ => rfl
  | hole :: tail, member => congrArg (List.cons hole)
      (Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry.fromHoles_holes lifted tail (fun other
        belongs => member other (List.mem_cons_of_mem _ belongs)))

end AnnularEntry

set_option genInjectivity false in
/-- The complement keeps the original lifted quadrilaterals and caches its triangle list. Its readbacks accept
independently checked data as well as the automatic constructor below. -/
structure AllHoleExcision (grid : BranchCellBank.NewtonGrid preparation target radius) (lifted :
  Meshes.LiftedPuncturedGrid grid.punctured) where
  /-- The cached annular entries following the original complete classified hole list. -/ entries : List
    (Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted)
  /-- The annular entries retain exactly the original grid's hole payloads and order. -/ holes_eq : entries.map
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry.hole = grid.faces.holes
  /-- The cached original regular faces outside all retained Newton bands. -/ remainingFaces : List
    (PuncturedGridFaces.RegularFace grid.shrunk.prepared.toBranchCellBank)
  /-- The remaining face list is exactly the original regular list filtered by all retained band selections. -/
    remainingFaces_eq : remainingFaces = grid.faces.regulars.filter
    (fun face => !(entries.any (fun entry => entry.keep face)))
  /-- The retained original lifts of precisely the surviving regular faces. -/ remaining : GridLiftedMesh.LiftedFaces
    lifted.vertices lifted.edges remainingFaces
  /-- The surviving lifted triangle list equals the original combined selection's rejected triangle list. -/ retained_eq
    : remaining.triangles =
    (GridLiftedFaceSelection.select
      (fun face => entries.any (fun entry => entry.keep face)) lifted.mesh.lifts).rejected.triangles
  /-- The cached original lifted triangle complement after every selected annulus is removed. -/ complement : List
    (Stokes.OrientedTriangle lifted.vertices.count)
  /-- The cached complement is exactly the retained surviving lifts' triangle list. -/ complement_eq : complement =
    remaining.triangles

constructive_injectivity AllHoleExcision

namespace AllHoleExcision

/-- Construct all original hole annuli and cache the surviving original lifted faces and triangles.

The entries preserve literal hole payloads and their exact list order; the complement is selected from the same original
mesh. -/
def build (grid : BranchCellBank.NewtonGrid preparation target radius) (lifted : Meshes.LiftedPuncturedGrid
  grid.punctured) :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted :=
  let entries := Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry.fromHoles lifted
    grid.faces.holes (fun _ member => member)
  let selection := GridLiftedFaceSelection.select
    (fun face => entries.any (fun entry => entry.keep face)) lifted.mesh.lifts
  { entries := entries
    holes_eq := Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry.fromHoles_holes lifted
      grid.faces.holes (fun _ member => member)
    remainingFaces := selection.discarded
    remainingFaces_eq := selection.discarded_eq
    remaining := selection.rejected
    retained_eq := rfl
    complement := selection.rejected.triangles
    complement_eq := rfl }

/-- The retained annular entries select pairwise disjoint original regular faces. -/
theorem disjoint (excision : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) :
    excision.entries.Pairwise (fun first second => ∀ face,
      first.keep face = true → second.keep face = true → False) := by
  have unique := grid.faces.holes_pairwise
  rw [← excision.holes_eq] at unique
  exact (Pairwise.pairwise_map.mp unique).imp (fun different =>
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry.disjoint _ _ different)

/-- Exact partition for arbitrary readings; no positivity hypothesis can hide a duplicate face or discard a negative
contribution. -/
theorem partition (excision : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (value :
  Stokes.OrientedTriangle lifted.vertices.count → Data.Gaussian.Basic.Canonical) :
    CellBoundary.sumValues (fun entry => CellBoundary.sumValues value entry.region.triangles) excision.entries +
      CellBoundary.sumValues value excision.complement = CellBoundary.sumValues value lifted.mesh.triangles := by
  have selected := CellBoundary.sumValues_congr _ (fun entry => CellBoundary.sumValues value
    (GridLiftedFaceSelection.select entry.keep lifted.mesh.lifts).selected.triangles)
    excision.entries (fun entry _ => congrArg (CellBoundary.sumValues value) entry.selection_eq)
  have family := GridLiftedFaceSelection.select_family_sum
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry.keep value excision.entries excision.disjoint
      lifted.mesh.lifts
  exact (congrArg₂ (· + ·) (selected.trans family.symm)
    (congrArg (CellBoundary.sumValues value) (excision.complement_eq.trans excision.retained_eq))).trans
      ((GridLiftedFaceSelection.select_sum _ value lifted.mesh.lifts).trans
        (congrArg (CellBoundary.sumValues value) lifted.mesh.triangles_eq.symm))

/-- Every retained complement triangle preserves its strictly positive original geometric area. -/
theorem triangle_positive (excision : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
  (triangle : Stokes.OrientedTriangle lifted.vertices.count)
    (member : triangle ∈ excision.complement) : 0 < LiftedFaces.triangleArea lifted.vertices triangle := by
  rw [excision.complement_eq] at member
  exact excision.remaining.triangle_positive triangle member

/-- A retained face with a point outside every closed band survives the selection. This will be consumed by the
observation-bank containment proof. -/
theorem face_survives (excision : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
    (face : PuncturedGridFaces.RegularFace grid.shrunk.prepared.toBranchCellBank) (member : face ∈ grid.faces.regulars)
    (point : Data.Gaussian.Basic.Canonical) (inside : face.cell.box.Contains point)
    (outside : ∀ index, ¬(grid.bands.box index).Contains point) : face ∈ excision.remainingFaces := by
  rw [excision.remainingFaces_eq]
  refine Filter.mem_filter.mpr ⟨member, ?_⟩
  have absent : excision.entries.any (fun entry => entry.keep face) = false := by
    induction excision.entries with
    | nil => rfl
    | cons entry tail ih =>
        have no : entry.keep face = false := Bool.eq_false_iff.mpr (fun kept =>
          outside entry.hole.index ((of_decide_eq_true kept).contains inside))
        change (entry.keep face || tail.any (fun entry => entry.keep face)) = false
        rw [no, ih]
        rfl
  rw [absent]
  rfl

/-- The retained annular inner tours sum to exactly the original complete hole-boundary area. -/
theorem inner_area (excision : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
  (primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    CellBoundary.sumValues (fun entry => Stokes.edgeListArea primitive entry.region.inner) excision.entries =
      CellBoundary.sumValues (fun hole => lifted.edges.twoSheetArea lifted.vertices primitive hole.inwardBoundary)
        grid.faces.holes := by
  rw [← excision.holes_eq, CellBoundary.sumValues_map]
  exact CellBoundary.sumValues_congr _ _ _ (fun entry _ => by rw [Lifted.inner_area entry.region, entry.hole_eq])

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision in
/-- The original mesh boundary area equals the surviving triangle area plus all retained outer and inner annular tours.
-/
theorem complement_area (excision : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
  (primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive (excision.complement.flatMap OrientedTriangle.boundary) +
      CellBoundary.sumValues (fun entry => Stokes.edgeListArea primitive entry.region.outer) excision.entries +
      CellBoundary.sumValues (fun entry => Stokes.edgeListArea primitive entry.region.inner) excision.entries =
        Stokes.edgeListArea primitive lifted.mesh.triangulation.boundary := by
  have partition := excision.partition (fun triangle => Stokes.edgeListArea primitive triangle.boundary)
  have selected : CellBoundary.sumValues (fun entry => CellBoundary.sumValues (fun triangle => Stokes.edgeListArea
    primitive triangle.boundary)
      entry.region.triangles) excision.entries =
      CellBoundary.sumValues (fun entry => Stokes.edgeListArea primitive entry.region.outer) excision.entries +
        CellBoundary.sumValues (fun entry => Stokes.edgeListArea primitive entry.region.inner) excision.entries := by
    rw [← CellBoundary.sumValues_add]
    exact CellBoundary.sumValues_congr _ _ _ (fun entry _ => by
      rw [← Lifted.triangleEdges_sum, Lifted.triangleEdges_area entry.region])
  rw [selected, ← Lifted.triangleEdges_sum primitive excision.complement,
    ← Lifted.triangleEdges_sum primitive lifted.mesh.triangles,
    lifted.mesh.triangles_eq, lifted.mesh.lifts.triangleEdges_area primitive,
    ← lifted.mesh.boundary_eq_faceWalks primitive] at partition
  exact (show _ = (CellBoundary.sumValues (fun entry => Stokes.edgeListArea primitive entry.region.outer)
    excision.entries +
    CellBoundary.sumValues (fun entry => Stokes.edgeListArea primitive entry.region.inner) excision.entries) +
      Stokes.edgeListArea primitive (excision.complement.flatMap OrientedTriangle.boundary) by ring1).trans partition

/-- Every original inward hole term cancels. The complement and the actual two-lap band tours account for the fixed
exterior, with sheet-aware primitive values on the same retained vertex bank. -/
theorem exterior_area (excision : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
  (primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive (excision.complement.flatMap OrientedTriangle.boundary) +
      CellBoundary.sumValues (fun entry => Stokes.edgeListArea primitive entry.region.outer) excision.entries =
        lifted.edges.twoSheetArea lifted.vertices primitive grid.punctured.bank.exterior := by
  have balance := excision.complement_area primitive
  rw [excision.inner_area primitive, lifted.boundary_eq_exterior_and_holes] at balance
  exact add_right_cancel balance

/-- The automatic simultaneous excision for the Newton grid built from the checked branch cell bank. Every grid and lift
component is constructed here, so no caller preparation, grid, lift or excision remains. -/
def ofCurve (original : Branches.BranchCellBank curve branches higher)
    {target radius : Fraction.Rational} (positive : 0 < target) (radiusPositive : 0 < radius) :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision
      (NewtonGrid.build (NewtonPreparation.build original) positive radiusPositive)
      (LiftedPuncturedGrid.build
        (NewtonGrid.build (NewtonPreparation.build original) positive radiusPositive).punctured) :=
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision.build _ _

/-- The exact exterior-area partition for the curve-only excision: the retained complement triangles plus the actual
two-lap band tours account for the fixed exterior, with sheet-aware primitive values on the same retained vertex bank.
-/
theorem exterior_area_ofCurve (original : Branches.BranchCellBank curve branches higher)
    {target radius : Fraction.Rational} (positive : 0 < target) (radiusPositive : 0 < radius)
    (primitive : Fin (LiftedPuncturedGrid.build
      (NewtonGrid.build (NewtonPreparation.build original) positive radiusPositive).punctured).vertices.count →
        Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive
        ((Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision.ofCurve original positive
          radiusPositive).complement.flatMap OrientedTriangle.boundary) +
      CellBoundary.sumValues (fun entry => Stokes.edgeListArea primitive entry.region.outer)
        (Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision.ofCurve original positive
          radiusPositive).entries =
      (LiftedPuncturedGrid.build
        (NewtonGrid.build (NewtonPreparation.build original) positive radiusPositive).punctured).edges.twoSheetArea
        (LiftedPuncturedGrid.build
          (NewtonGrid.build (NewtonPreparation.build original) positive radiusPositive).punctured).vertices
        primitive
        (NewtonGrid.build (NewtonPreparation.build original) positive radiusPositive).punctured.bank.exterior :=
  (Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision.ofCurve original positive
    radiusPositive).exterior_area primitive

/-- The exact inner-area aggregation for the curve-only excision. -/
theorem inner_area_ofCurve (original : Branches.BranchCellBank curve branches higher)
    {target radius : Fraction.Rational} (positive : 0 < target) (radiusPositive : 0 < radius)
    (primitive : Fin (LiftedPuncturedGrid.build
      (NewtonGrid.build (NewtonPreparation.build original) positive radiusPositive).punctured).vertices.count →
        Stokes.PrimitivePoint) :
    CellBoundary.sumValues (fun entry => Stokes.edgeListArea primitive entry.region.inner)
        (Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision.ofCurve original positive
          radiusPositive).entries =
      CellBoundary.sumValues (fun hole => (LiftedPuncturedGrid.build
          (NewtonGrid.build (NewtonPreparation.build original) positive radiusPositive).punctured).edges.twoSheetArea
          (LiftedPuncturedGrid.build
            (NewtonGrid.build (NewtonPreparation.build original) positive radiusPositive).punctured).vertices
          primitive hole.inwardBoundary)
        (NewtonGrid.build (NewtonPreparation.build original) positive radiusPositive).faces.holes :=
  (Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision.ofCurve original positive
    radiusPositive).inner_area primitive

/-- The exact complement-area partition for the curve-only excision. -/
theorem complement_area_ofCurve (original : Branches.BranchCellBank curve branches higher)
    {target radius : Fraction.Rational} (positive : 0 < target) (radiusPositive : 0 < radius)
    (primitive : Fin (LiftedPuncturedGrid.build
      (NewtonGrid.build (NewtonPreparation.build original) positive radiusPositive).punctured).vertices.count →
        Stokes.PrimitivePoint) :
    Stokes.edgeListArea primitive
        ((Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision.ofCurve original positive
          radiusPositive).complement.flatMap OrientedTriangle.boundary) +
      CellBoundary.sumValues (fun entry => Stokes.edgeListArea primitive entry.region.outer)
        (Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision.ofCurve original positive
          radiusPositive).entries +
      CellBoundary.sumValues (fun entry => Stokes.edgeListArea primitive entry.region.inner)
        (Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision.ofCurve original positive
          radiusPositive).entries =
      Stokes.edgeListArea primitive (LiftedPuncturedGrid.build
        (NewtonGrid.build (NewtonPreparation.build original) positive
          radiusPositive).punctured).mesh.triangulation.boundary :=
  (Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision.ofCurve original positive
    radiusPositive).complement_area primitive

end AllHoleExcision
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
