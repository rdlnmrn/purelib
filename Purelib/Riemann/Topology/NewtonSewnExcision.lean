module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Filter
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Pairwise

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Integration.Surface.Sewn.Selection.Basic
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnFaceAreaComparison

import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Newton excision on the actual sewn primitive bank

Each of the four triangle occurrences of an original regular face uses the
same retained annular mask. The selected triangles remain in the cut vertex
bank, so their areas include actual sewing offsets. This is an exact signed
partition, not an identification with the independently prepared Newton tour.
-/

namespace Purelib.Riemann.Topology.NewtonSewnExcision

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceTrace)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (triangleIndex)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AnnularEntry)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {lifted : LiftedPuncturedGrid grid.punctured}

namespace AllHoleExcision

/-- The original regular-face position underlying a retained lifted triangle index. -/
@[expose] def sourcePosition (lifted : LiftedPuncturedGrid grid.punctured)
    (source : Fin lifted.mesh.triangles.length) : Fin grid.faces.regulars.length :=
  ⟨source.val / 4, by
    have bound : source.val < 4 * grid.faces.regulars.length := source.isLt.trans_eq lifted.mesh.faceCount
    omega⟩

/-- The exact triangle index formed from a face, sheet and half reads back its original face position. -/
theorem sourcePosition_triangleIndex (lifted : LiftedPuncturedGrid grid.punctured)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (upper : Bool) :
    sourcePosition lifted (lifted.mesh.triangleIndex position sheet upper) = position := by
  apply Fin.ext
  have := sheet.isLt
  cases upper with
  | false =>
      dsimp only [sourcePosition, LiftedMesh.triangleIndex]
      rw [if_neg (show ¬ (false = true) from fun impossible => nomatch impossible)]
      omega0
  | true =>
      dsimp only [sourcePosition, LiftedMesh.triangleIndex]
      rw [if_pos rfl]
      omega0

/-- The original regular face underlying the retained source triangle. -/
@[expose] def sourceFace (lifted : LiftedPuncturedGrid grid.punctured) (source : Fin lifted.mesh.triangles.length) :
    RegularFace grid.shrunk.prepared.toBranchCellBank := grid.faces.regulars[(sourcePosition lifted source).val]

section
open Purelib.Curves.Hyperelliptic
/-- Whether the original source face lies in the retained annular entry's selected region. -/
@[expose] def sourceMask (entry : Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted) (source : Fin
  lifted.mesh.triangles.length) : Bool :=
  entry.keep (sourceFace lifted source)

/-- The retained source-triangle mask equals its original face predicate at the exact face index. -/
theorem sourceMask_triangleIndex (entry : Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (upper : Bool) :
    sourceMask entry (lifted.mesh.triangleIndex position sheet upper) = entry.keep grid.faces.regulars[position.val] :=
      by
  exact congrArg (fun index : Fin grid.faces.regulars.length => entry.keep grid.faces.regulars[index.val])
    (sourcePosition_triangleIndex lifted position sheet upper)

end

variable {localValues : Fin lifted.mesh.triangles.length →
  Purelib.Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration in
open Purelib.Topology.Surface in
set_option genInjectivity false in
/-- An original annular excision entry together with its retained selection from a sewn primitive sample.

The selection mask is defined by the exact original source face of each retained sewn triangle. -/
structure SewnAnnulus (sample : Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch localValues) where
  /-- The original retained annular excision entry. -/ source : Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted
  /-- The retained original sewn-face selection using the entry's exact source mask. -/ selected :
    Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection
    sample (sourceMask source)

constructive_injectivity SewnAnnulus

namespace SewnAnnulus

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration in
open Purelib.Topology.Surface in
/-- Select the original annulus's sewn primitive faces using its exact retained source-face mask. -/
@[expose] def build (sample : Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch localValues) (source :
  Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted) :
    SewnAnnulus sample := ⟨source,
      Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection.build
        sample (sourceMask source)⟩

open Purelib.Topology.Surface in
/-- Every selected sewn trace originates from a face of the retained original annulus. -/
theorem source_face_mem {sample : Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch localValues} (annulus
  : SewnAnnulus sample)
    (trace : Sewing.SewnPrimitiveFaces.FaceTrace localValues sample.sewn.values) (member : trace ∈
      annulus.selected.traces) :
    sourceFace lifted trace.source ∈ annulus.source.annulus.faces := by
  rw [annulus.source.annulus.faces_eq]
  exact Purelib.Data.List.Filter.mem_filter.mpr ⟨List.getElem_mem _, annulus.selected.trace_kept trace member⟩

end SewnAnnulus

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.Polynomial in
open Purelib.Topology.Surface in
set_option genInjectivity false in
/-- A sewn all-hole excision retaining each original annular source, the remaining sample and the annular area cache.

The annulus list maps exactly to the original excision entries, and the remainder uses the complement of their original
source masks. -/
structure Sewn (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (sample :
  Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch localValues) where
  /-- The ordered retained sewn selections of the original annular entries. -/ annuli : List (SewnAnnulus sample)
  /-- The stored annuli project to exactly the original excision entry list. -/ sources_eq : annuli.map
    SewnAnnulus.source = excision.entries
  /-- The retained original sample faces outside all annular source masks. -/ remaining :
    Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection
    sample (fun index => !(excision.entries.any (fun entry => sourceMask entry index)))
  /-- The cached Gaussian area sum of the retained annular selections. -/ annularArea : Basic.Canonical
  /-- The annular area cache equals the exact stored annulus area sum. -/ annularArea_eq : annularArea =
    Geometry.Grid.CellBoundary.sumValues (fun annulus => annulus.selected.area) annuli

constructive_injectivity Sewn

namespace Sewn

variable {excision : Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted} {sample :
  Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch localValues}

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration in
open Purelib.Polynomial in
open Purelib.Topology.Surface in
/-- Construct sewn annular selections and their exact remaining sample from the original all-hole excision.

The original entry order determines the stored annuli and cached area sum; the complement mask retains all other
original sample traces. -/
@[expose] def build (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted) (sample :
  Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch localValues) :
    Sewn excision sample :=
  let annuli := excision.entries.map (SewnAnnulus.build sample)
  { annuli := annuli
    sources_eq := by
      dsimp only [annuli]
      induction excision.entries with
      | nil => rfl
      | cons entry tail ih => exact congrArg (List.cons entry) ih
    remaining := Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection.build
      sample (fun index => !(excision.entries.any (fun entry => sourceMask entry index)))
    annularArea := Geometry.Grid.CellBoundary.sumValues (fun annulus => annulus.selected.area) annuli
    annularArea_eq := rfl }

/-- A Boolean search over an original mapped list equals the search using the composed test. -/
private theorem any_map {Item Label : Type} (map : Item → Label) (test : Label → Bool) (items : List Item) :
    (items.map map).any test = items.any (fun item => test (map item)) := by
  induction items with
  | nil => rfl
  | cons head tail ih => change (test (map head) || _) = (test (map head) || _); rw [ih]

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.List in
open Purelib.Integration in
open Purelib.Topology.Surface in
/-- The retained sewn annular area and remaining area sum to the original sample boundary area.

Original annular disjointness transfers through the exact source-list equation, preserving the cached trace selections
and their area sums. -/
theorem partition (sewn : Sewn excision sample) :
    sewn.annularArea + sewn.remaining.area = sample.boundaryArea := by
  have separate := excision.disjoint
  rw [← sewn.sources_eq] at separate
  have disjoint := Pairwise.pairwise_map.mp separate
  have masks : sewn.annuli.Pairwise (fun first second => ∀ index,
      sourceMask first.source index = true → sourceMask second.source index = true → False) :=
    disjoint.imp (fun separated index => separated (sourceFace lifted index))
  let remaining : Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection
      sample (fun index => !(sewn.annuli.any (fun annulus => sourceMask annulus.source index))) :=
    { traces := sewn.remaining.traces
      traces_eq := sewn.remaining.traces_eq.trans
        (Purelib.Data.List.Filter.filter_congr (Item := Sewing.SewnPrimitiveFaces.FaceTrace localValues
          sample.sewn.values) _ _ (fun trace => congrArg Bool.not
          ((congrArg (fun entries : List (Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted) =>
            entries.any (fun entry => sourceMask entry trace.source)) sewn.sources_eq.symm).trans
              (any_map (Item := SewnAnnulus sample) (Label := Meshes.Newton.AllHoles.Excision.AnnularEntry grid lifted)
                (fun annulus : SewnAnnulus sample => annulus.source)
                (fun entry => sourceMask entry trace.source) sewn.annuli))) sample.faces.entries)
      triangles := sewn.remaining.triangles
      triangles_eq := sewn.remaining.triangles_eq
      area := sewn.remaining.area
      area_eq := sewn.remaining.area_eq }
  exact (congrArg (fun value => value + sewn.remaining.area) sewn.annularArea_eq).trans
    (Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.FaceSelection.family_partition
      sewn.annuli (fun annulus => sourceMask annulus.source)
      masks (fun annulus => annulus.selected) remaining)

/-- The retained remaining sewn area equals the original sample boundary area minus the annular cache. -/
theorem remaining_area (sewn : Sewn excision sample) :
    sewn.remaining.area = sample.boundaryArea - sewn.annularArea := by
  rw [← sewn.partition]
  ring1

open Purelib.Integration in
/-- Package the original retained remainder and annular area as an exact sewn area-excision certificate. -/
@[expose] def areaExcision (sewn : Sewn excision sample) :
    Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample.AreaExcision sample :=
  ⟨_, sewn.remaining, sewn.annularArea, sewn.partition⟩

open Purelib.Data.Gaussian in
open Purelib.Topology.Surface in
/-- A retained source trace containing a point outside every original Newton band survives annular excision.

The original annular membership masks would force that point into one of the excluded bands, so every such mask is
false. -/
theorem trace_survives (sewn : Sewn excision sample)
    (trace : Sewing.SewnPrimitiveFaces.FaceTrace localValues sample.sewn.values) (member : trace ∈ sample.faces.entries)
    (point : Basic.Canonical) (inside : (sourceFace lifted trace.source).cell.box.Contains point)
    (outside : ∀ index, ¬(grid.bands.box index).Contains point) : trace ∈ sewn.remaining.traces := by
  rw [sewn.remaining.traces_eq]
  refine Purelib.Data.List.Filter.mem_filter.mpr ⟨member, ?_⟩
  have absent : excision.entries.any (fun entry => sourceMask entry trace.source) = false := by
    induction excision.entries with
    | nil => rfl
    | cons entry tail ih =>
        have no : sourceMask entry trace.source = false := Bool.eq_false_iff.mpr (fun kept =>
          outside entry.hole.index ((of_decide_eq_true kept).contains inside))
        change (sourceMask entry trace.source || _) = false
        rw [no, ih]
        rfl
  rw [absent]
  rfl

end Sewn
end AllHoleExcision
end Purelib.Riemann.Topology.NewtonSewnExcision
