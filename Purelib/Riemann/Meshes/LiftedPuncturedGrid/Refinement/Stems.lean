module

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Annulus
public import Purelib.Polynomial.Geometry.Grid.WindowBoundary.CornerPaths
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.SingleHole.Canonical
import Purelib.Polynomial.Geometry.Grid.CircuitStemGeometry
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.AxisSpines
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Connectors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowBranchWinding
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction

/-! # Actual finite strips between old and new canonical branch stems

Shrinking a hole can move its bottom coordinate past other branch holes
on the exterior-left route. The real strip is therefore classified and
retained, together with both original stem caches. No equality of these
stems, ordered bases or periods is postulated.
-/

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (ClearancePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.Window (OrderedBranches prepareBranches)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowBranchWinding
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Integration.Path
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.WindowBoundary (Window)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
open Purelib.RootIsolation.SquareRoot.Grid.Inclusion
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Mesh.RetracingWords (wordArea AreaTerm)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

namespace Purelib.Riemann.Meshes.FramedPuncturedGrid

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree}

/-- The original exterior-corner rectangle ending at the old hole anchor. -/
@[expose] def cornerBox (base : FramedPuncturedGrid curve branches higher) (index : Data.Index branches) : Box :=
  ⟨(Cuts.Ambient curve).xLower, (base.bank.toBranchCellBank.cell index).box.xLower,
    (Cuts.Ambient curve).yLower, (base.bank.toBranchCellBank.cell index).box.yLower,
    (base.bank.holesInterior index).left.le, (base.bank.holesInterior index).bottom.le⟩

/-- Retain the original-grid corner window of the original cached branch stem. -/
def cornerWindow (base : FramedPuncturedGrid curve branches higher) (index : Data.Index branches) :
    Window base.bank.grid (base.cornerBox index) :=
  let oldMember := ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)
  Window.build base.bank.grid (base.cornerBox index)
    base.bank.frame.xLower oldMember.1 base.bank.frame.yLower oldMember.2

end Purelib.Riemann.Meshes.FramedPuncturedGrid

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {original : LiftedPuncturedGrid base}
    {patches : List (ContinuedNeighborhood curve.polynomial count)}
    {prepared : ClearancePreparation base.bank.toBranchCellBank patches}
    (retained : ClearanceRefinement original prepared)

/-- The actual strip swept when the canonical left/exterior stem rises to the new hole's bottom coordinate.

Both horizontal bounds and both vertical bounds come from the GIVEN old
and new bank cells. Original hole interiority and genuine new-hole nesting
supply their orders; no geometric search or extra radius is admitted.
-/
@[expose] def stemStripBox (index : Data.Index branches) : Box :=
  ⟨(Cuts.Ambient curve).xLower, (base.bank.toBranchCellBank.cell index).box.xLower,
    (base.bank.toBranchCellBank.cell index).box.yLower,
    (retained.fineBase.bank.toBranchCellBank.cell index).box.yLower,
    (base.bank.holesInterior index).left.le, (retained.inner_cell_inside index).bottom.le⟩

/-- The actual stem strip has positive width and height, by the original two strict geometric certificates. -/
theorem stemStripBox_proper (index : Data.Index branches) : (retained.stemStripBox index).Proper :=
  ⟨(base.bank.holesInterior index).left, (retained.inner_cell_inside index).bottom⟩

/-- Build the strip window using the SAME four actual old/fine grid line certificates. -/
def stemStripWindow (index : Data.Index branches) :
    Window retained.fineBase.bank.grid (retained.stemStripBox index) :=
  let oldMember := ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)
  let fineMember := ClearGrid.Cell.anchor_mem _ (retained.fineBase.bank.toBranchCellBank.cell_mem index)
  Window.build retained.fineBase.bank.grid (retained.stemStripBox index)
    retained.fineBase.bank.frame.xLower
    (retained.included.vertical _ oldMember.1)
    (retained.included.horizontal _ oldMember.2) fineMember.2

/-- The actual monotone corner rectangle between the old and new hole anchors. -/
@[expose] def innerCornerBox (index : Data.Index branches) : Box :=
  ⟨(base.bank.toBranchCellBank.cell index).box.xLower,
    (retained.fineBase.bank.toBranchCellBank.cell index).box.xLower,
    (base.bank.toBranchCellBank.cell index).box.yLower,
    (retained.fineBase.bank.toBranchCellBank.cell index).box.yLower,
    (retained.inner_cell_inside index).left.le, (retained.inner_cell_inside index).bottom.le⟩

/-- The fresh exterior-corner rectangle ending at the SAME new hole anchor. -/
@[expose] def freshCornerBox (index : Data.Index branches) : Box :=
  ⟨(Cuts.Ambient curve).xLower, (retained.fineBase.bank.toBranchCellBank.cell index).box.xLower,
    (Cuts.Ambient curve).yLower, (retained.fineBase.bank.toBranchCellBank.cell index).box.yLower,
    (retained.fineBase.bank.holesInterior index).left.le, (retained.fineBase.bank.holesInterior index).bottom.le⟩

/-- Retain the SAME old physical corner window on the given fine grid. -/
def oldFineCornerWindow (index : Data.Index branches) :
    Window retained.fineBase.bank.grid (base.cornerBox index) :=
  let oldMember := ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)
  Window.build retained.fineBase.bank.grid (base.cornerBox index)
    (retained.included.vertical _ base.bank.frame.xLower) (retained.included.vertical _ oldMember.1)
    (retained.included.horizontal _ base.bank.frame.yLower) (retained.included.horizontal _ oldMember.2)

/-- Retain the actual fine-grid corner window between the original and new hole anchors. -/
def innerCornerWindow (index : Data.Index branches) :
    Window retained.fineBase.bank.grid (retained.innerCornerBox index) :=
  let oldMember := retained.included.vertex
    (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))
  let fineMember := ClearGrid.Cell.anchor_mem _ (retained.fineBase.bank.toBranchCellBank.cell_mem index)
  Window.build retained.fineBase.bank.grid (retained.innerCornerBox index)
    oldMember.1 fineMember.1 oldMember.2 fineMember.2

/-- Retain the fresh fine-grid corner window of the GIVEN new bank stem. -/
def freshCornerWindow (index : Data.Index branches) :
    Window retained.fineBase.bank.grid (retained.freshCornerBox index) :=
  let fineMember := ClearGrid.Cell.anchor_mem _ (retained.fineBase.bank.toBranchCellBank.cell_mem index)
  Window.build retained.fineBase.bank.grid (retained.freshCornerBox index)
    retained.fineBase.bank.frame.xLower fineMember.1 retained.fineBase.bank.frame.yLower fineMember.2

/-- Given old/new banks and one actual annulus retain the strip classification and all three actual stem views.

The old and fresh banks remain distinct arguments. The intermediate stem
uses that SAME retained annulus connector. Its sheet and the strip's input
sheet remain independent indices; no root alignment is inferred from labels.
The strip may contain other holes: its BranchCount and ordered signed corrections are actual results,
not a trivial-return or unchanged-basis premise.
-/
@[expose] def StemStrip (oldBank : BasedBranchBank original) (newBank : BasedBranchBank retained.fine)
    {index : Data.Index branches} {annulusSheet : Fin 2} (annular : retained.Annulus index annulusSheet)
    (stripSheet : Fin 2) : Type _ :=
  (window : {value : Window retained.fineBase.bank.grid (retained.stemStripBox index) //
    value = retained.stemStripWindow index}) ×
  (_count : {value : Window.BranchCount retained.fineBase.faces window.val //
    value = Window.BranchCount.build retained.fineBase.faces window.val}) ×
  (_ordered : {value : OrderedBranches retained.fineBase.faces window.val
      retained.fine.edges retained.fine.vertices stripSheet //
    value = prepareBranches retained.fineBase.faces window.val retained.fine.edges retained.fine.vertices stripSheet}) ×
  (oldStem : {value : Walk retained.fineBase.bank.grid (Cuts.Ambient curve).anchor
      (base.bank.toBranchCellBank.cell index).box.anchor //
    value = retained.included.resplit (oldBank.rows.get index).stem
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))}) ×
  (_throughHole : {value : Walk retained.fineBase.bank.grid (Cuts.Ambient curve).anchor
      (retained.fineBase.bank.toBranchCellBank.cell index).box.anchor //
    value = oldStem.val.append annular.selected.val}) ×
  (_freshStem : {value : Walk retained.fineBase.bank.grid (Cuts.Ambient curve).anchor
      (retained.fineBase.bank.toBranchCellBank.cell index).box.anchor //
    value = (newBank.rows.get index).stem}) ×
  (_oldCorner : {value : Window base.bank.grid (base.cornerBox index) //
    value = base.cornerWindow index}) ×
  (_oldFineCorner : {value : Window retained.fineBase.bank.grid (base.cornerBox index) //
    value = retained.oldFineCornerWindow index}) ×
  (_innerCorner : {value : Window retained.fineBase.bank.grid (retained.innerCornerBox index) //
    value = retained.innerCornerWindow index}) ×
  {value : Window retained.fineBase.bank.grid (retained.freshCornerBox index) //
    value = retained.freshCornerWindow index}

/-- Retain the real strip and the original old, continued and fresh stems without running either bank producer again. -/
def stemStrip (oldBank : BasedBranchBank original) (newBank : BasedBranchBank retained.fine)
    {index : Data.Index branches} {annulusSheet : Fin 2} (annular : retained.Annulus index annulusSheet)
    (stripSheet : Fin 2) : retained.StemStrip oldBank newBank annular stripSheet :=
  let window := retained.stemStripWindow index
  let count := Window.BranchCount.build retained.fineBase.faces window
  let ordered := prepareBranches retained.fineBase.faces window retained.fine.edges retained.fine.vertices stripSheet
  let oldStem := retained.included.resplit (oldBank.rows.get index).stem
    (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))
  let throughHole := oldStem.append annular.selected.val
  let freshStem := (newBank.rows.get index).stem
  let oldCorner := base.cornerWindow index
  let oldFineCorner := retained.oldFineCornerWindow index
  let innerCorner := retained.innerCornerWindow index
  let freshCorner := retained.freshCornerWindow index
  ⟨⟨window, rfl⟩, ⟨count, rfl⟩, ⟨ordered, rfl⟩, ⟨oldStem, rfl⟩, ⟨throughHole, rfl⟩, ⟨freshStem, rfl⟩,
    ⟨oldCorner, rfl⟩, ⟨oldFineCorner, rfl⟩, ⟨innerCorner, rfl⟩, ⟨freshCorner, rfl⟩⟩

namespace StemStrip

variable {retained} {oldBank : BasedBranchBank original} {newBank : BasedBranchBank retained.fine}
    {index : Data.Index branches} {annulusSheet stripSheet : Fin 2}
    {annular : retained.Annulus index annulusSheet}
    (strip : retained.StemStrip oldBank newBank annular stripSheet)

/-- Read the SAME actual stem-strip window and its four retained side lookups. -/
@[expose] def window : Window retained.fineBase.bank.grid (retained.stemStripBox index) := strip.1.val

/-- Read the original finite branch count/parity certificate, without requiring this strip to be clear of holes. -/
@[expose] def branchCount : Window.BranchCount retained.fineBase.faces strip.window := strip.2.1.val

/-- Read the original complete strip branch product and regular-face corrections at the given actual sheet. -/
@[expose] def ordered : OrderedBranches retained.fineBase.faces strip.window
    retained.fine.edges retained.fine.vertices stripSheet := strip.2.2.1.val

/-- Read the actual resplit original bank stem, retaining the original row and source walk. -/
@[expose] def oldStem : Walk retained.fineBase.bank.grid (Cuts.Ambient curve).anchor
    (base.bank.toBranchCellBank.cell index).box.anchor := strip.2.2.2.1.val

/-- Read the original resplit stem followed by the SAME actual390 inner connector. -/
@[expose] def continuedStem : Walk retained.fineBase.bank.grid (Cuts.Ambient curve).anchor
    (retained.fineBase.bank.toBranchCellBank.cell index).box.anchor := strip.2.2.2.2.1.val

/-- Read the SAME independently given fresh bank's canonical stem. -/
@[expose] def freshStem : Walk retained.fineBase.bank.grid (Cuts.Ambient curve).anchor
    (retained.fineBase.bank.toBranchCellBank.cell index).box.anchor := strip.2.2.2.2.2.1.val

/-- The old stem is exactly the original coordinate resplit of the given old row. -/
theorem oldStem_eq : strip.oldStem = retained.included.resplit (oldBank.rows.get index).stem
    (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)) := strip.2.2.2.1.property

/-- The continued stem uses exactly the SAME bound old stem and390 connector. -/
theorem continuedStem_eq : strip.continuedStem = strip.oldStem.append annular.selected.val :=
  strip.2.2.2.2.1.property

/-- The fresh stem is the whole original given new-bank row's cache, without another bank construction. -/
theorem freshStem_eq : strip.freshStem = (newBank.rows.get index).stem := strip.2.2.2.2.2.1.property

/-- Read the original old-grid corner window. -/
@[expose] def oldCorner : Window base.bank.grid (base.cornerBox index) := strip.2.2.2.2.2.2.1.val

/-- Read the SAME physical old corner on the fine grid. -/
@[expose] def oldFineCorner : Window retained.fineBase.bank.grid (base.cornerBox index) :=
  strip.2.2.2.2.2.2.2.1.val

/-- Read the actual retained corner from old hole anchor to new hole anchor. -/
@[expose] def innerCorner : Window retained.fineBase.bank.grid (retained.innerCornerBox index) :=
  strip.2.2.2.2.2.2.2.2.1.val

/-- Read the actual retained fresh-bank exterior corner. -/
@[expose] def freshCorner : Window retained.fineBase.bank.grid (retained.freshCornerBox index) :=
  strip.2.2.2.2.2.2.2.2.2.val

/-- The SAME retained initial vertical axis prefix, ending at the strip's southwest corner. -/
@[expose] def «prefix» : Walk retained.fineBase.bank.grid (Cuts.Ambient curve).anchor
    (Data.Gaussian.Components.Basic.point (Cuts.Ambient curve).xLower
      (base.bank.toBranchCellBank.cell index).box.yLower) := strip.oldFineCorner.vertical strip.oldFineCorner.left

/-- The SAME retained final horizontal axis suffix, leaving the strip's northeast corner. -/
@[expose] def suffix : Walk retained.fineBase.bank.grid
    (Data.Gaussian.Components.Basic.point (base.bank.toBranchCellBank.cell index).box.xLower
      (retained.fineBase.bank.toBranchCellBank.cell index).box.yLower)
    (retained.fineBase.bank.toBranchCellBank.cell index).box.anchor :=
  strip.innerCorner.horizontal strip.innerCorner.top

/-- The two actual ascending old/inner corners factor through the retained southeast strip route. -/
theorem old_corners_factor : strip.oldFineCorner.northEast.append strip.innerCorner.northEast =
    strip.prefix.append (strip.window.southEast.append strip.suffix) := by
  have xs := AxisChainCoherence.IncreasingWalk.unique
    (ClearGrid.Interval.adjacent_pairwise _ retained.fineBase.bank.grid.vertical_ordered)
    strip.oldFineCorner.x strip.window.x
  have ys := AxisChainCoherence.IncreasingWalk.unique
    (ClearGrid.Interval.adjacent_pairwise _ retained.fineBase.bank.grid.horizontal_ordered)
    strip.innerCorner.y strip.window.y
  have bottom := WindowCircuitOrder.WindowCircuits.lookup_unique retained.fineBase.bank.grid.horizontal_ordered
    strip.oldFineCorner.top strip.window.bottom
  have right := WindowCircuitOrder.WindowCircuits.lookup_unique retained.fineBase.bank.grid.vertical_ordered
    strip.innerCorner.left strip.window.right
  have horizontal : strip.oldFineCorner.horizontal strip.oldFineCorner.top =
      strip.window.horizontal strip.window.bottom :=
    congrArg₂ (fun axis line => WindowCircuits.horizontal (grid := retained.fineBase.bank.grid) axis line) xs bottom
  have vertical : strip.innerCorner.vertical strip.innerCorner.left = strip.window.vertical strip.window.right :=
    congrArg₂ (fun line axis => WindowCircuits.vertical (grid := retained.fineBase.bank.grid) line axis) right ys
  change (strip.prefix.append (strip.oldFineCorner.horizontal strip.oldFineCorner.top)).append
    ((strip.innerCorner.vertical strip.innerCorner.left).append strip.suffix) = _
  calc
    _ = (strip.prefix.append (strip.window.horizontal strip.window.bottom)).append
        ((strip.window.vertical strip.window.right).append strip.suffix) :=
      congrArg₂ (fun first last => (strip.prefix.append first).append (last.append strip.suffix)) horizontal vertical
    _ = _ := by
      simp only [WindowBoundary.Window.southEast, Walk.append_assoc, -eq_self, -iff_self]
      rfl

/-- The actual fresh ascending corner factors through the retained northwest strip route. -/
theorem fresh_corner_factor : strip.freshCorner.northEast =
    strip.prefix.append (strip.window.northEast.append strip.suffix) := by
  have ys := AxisChainCoherence.IncreasingWalk.unique
    (ClearGrid.Interval.adjacent_pairwise _ retained.fineBase.bank.grid.horizontal_ordered)
    strip.freshCorner.y (strip.oldFineCorner.y.append strip.window.y)
  have xs := AxisChainCoherence.IncreasingWalk.unique
    (ClearGrid.Interval.adjacent_pairwise _ retained.fineBase.bank.grid.vertical_ordered)
    strip.freshCorner.x (strip.window.x.append strip.innerCorner.x)
  have left := WindowCircuits.lookup_unique retained.fineBase.bank.grid.vertical_ordered
    strip.freshCorner.left strip.oldFineCorner.left
  have upper := WindowCircuits.lookup_unique retained.fineBase.bank.grid.horizontal_ordered
    strip.freshCorner.top strip.innerCorner.top
  have stripLeft := WindowCircuits.lookup_unique retained.fineBase.bank.grid.vertical_ordered
    strip.oldFineCorner.left strip.window.left
  have stripTop := WindowCircuits.lookup_unique retained.fineBase.bank.grid.horizontal_ordered
    strip.innerCorner.top strip.window.top
  have vertical : strip.freshCorner.vertical strip.freshCorner.left =
      strip.prefix.append (strip.window.vertical strip.window.left) :=
    (congrArg₂ (fun line axis => WindowCircuits.vertical (grid := retained.fineBase.bank.grid) line axis) left ys).trans
      ((AxisChainCoherence.WindowCircuits.vertical_append _ _ strip.oldFineCorner.left).trans
        (congrArg (fun tail => strip.prefix.append tail)
          (congrArg (fun line => WindowCircuits.vertical line strip.window.y) stripLeft)))
  have horizontal : strip.freshCorner.horizontal strip.freshCorner.top =
      (strip.window.horizontal strip.window.top).append strip.suffix :=
    (congrArg₂ (fun axis line => WindowCircuits.horizontal (grid := retained.fineBase.bank.grid) axis line)
      xs upper).trans
      ((AxisChainCoherence.WindowCircuits.horizontal_append _ _ strip.innerCorner.top).trans
        (congrArg (fun head => head.append strip.suffix)
          (congrArg (fun line => WindowCircuits.horizontal strip.window.x line) stripTop)))
  change (strip.freshCorner.vertical strip.freshCorner.left).append
    (strip.freshCorner.horizontal strip.freshCorner.top) = _
  exact (congrArg₂ Walk.append vertical horizontal).trans (by
    simp only [WindowBoundary.Window.northEast, Walk.append_assoc, -eq_self, -iff_self]
    exact Walk.append_assoc _ _ _)

/-- The actual old retained corner resplits to the SAME fine corner by its original axis factories. -/
theorem resplit_old_corner : retained.included.resplit strip.oldCorner.northEast
      (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)) = strip.oldFineCorner.northEast := by
  let last := ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)
  let middle : FromStates.ContainsVertex base.bank.grid
      (Data.Gaussian.Components.Basic.point (Cuts.Ambient curve).xLower
        (base.bank.toBranchCellBank.cell index).box.yLower) := ⟨base.bank.frame.xLower, last.2⟩
  have joined := retained.included.resplit_append (strip.oldCorner.vertical strip.oldCorner.left)
    (strip.oldCorner.horizontal strip.oldCorner.top) middle last
  have vertical := retained.included.resplit_vertical strip.oldCorner.y strip.oldCorner.left last.2
    strip.oldFineCorner.y strip.oldFineCorner.left
  have horizontal := retained.included.resplit_horizontal strip.oldCorner.x strip.oldCorner.top last.1
    strip.oldFineCorner.x strip.oldFineCorner.top
  exact joined.trans (congrArg₂ Walk.append vertical horizontal)

/-- The GIVEN old bank's actual resplit stem compares to the retained fine old-corner route. -/
theorem old_stem_comparison : RootEdgeBank.ChainComparison retained.fine.edges retained.fine.vertices
    strip.oldStem strip.oldFineCorner.northEast := by
  have first := BasedBranchTours.FramedBranchCellBank.baseMember base.bank
  have last := ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)
  have oldEq := strip.oldStem_eq.trans (congrArg (fun walk => retained.included.resplit walk last)
    (oldBank.rows.get index).stem_eq)
  have compared := Connectors.Window.resplit_reverse_connect_comparison retained.included
    retained.fine.edges retained.fine.vertices
    (fun point member => (LoopMonodromy.BranchCellBank.referenceAt
      retained.fineBase.bank.toBranchCellBank point member).toLoop) strip.oldCorner first last
  exact (RootEdgeBank.ChainComparison.of_eq oldEq).trans
    (compared.trans (RootEdgeBank.ChainComparison.of_eq strip.resplit_old_corner))

/-- The GIVEN fresh bank stem compares to its actual retained fresh-corner route. -/
theorem fresh_stem_comparison : RootEdgeBank.ChainComparison retained.fine.edges retained.fine.vertices
    strip.freshStem strip.freshCorner.northEast :=
  (RootEdgeBank.ChainComparison.of_eq (strip.freshStem_eq.trans (newBank.rows.get index).stem_eq)).trans
    (AxisChainCoherence.Window.reverse_connect_comparison strip.freshCorner
      (fun point member => (LoopMonodromy.BranchCellBank.referenceAt
        retained.fineBase.bank.toBranchCellBank point member).toLoop)
      (BasedBranchTours.FramedBranchCellBank.baseMember retained.fineBase.bank)
      (ClearGrid.Cell.anchor_mem _ (retained.fineBase.bank.toBranchCellBank.cell_mem index)))

/-- The SAME390 based inner loop compares to the actual retained monotone inner corner around the new hole.

Only its based circuit is canonicalized. No equality of the bare390
connector with a different geometric path is inferred from this loop
comparison, and its true terminal sheet remains allowed to change.
-/
theorem inner_loop_comparison : RootEdgeBank.ChainComparison retained.fine.edges retained.fine.vertices
    annular.innerWalk (strip.innerCorner.northEast.based
      (CellBoundary.Cell.boundaryWalk (retained.fineBase.bank.toBranchCellBank.cell index)
        (retained.fineBase.bank.toBranchCellBank.cell_mem index))) := by
  let member := retained.included.vertex
    (ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index))
  let last := ClearGrid.Cell.anchor_mem _ (retained.fineBase.bank.toBranchCellBank.cell_mem index)
  let reference := fun point member => (LoopMonodromy.BranchCellBank.referenceAt
    retained.fineBase.bank.toBranchCellBank point member).toLoop
  have stems : RowCircuitOrder.CellCircuits.AscendingStems retained.fine.edges retained.fine.vertices
      annular.ordered.ordered.tree := by
    rewrite [annular.ordered.ordered.tree_eq]
    exact annular.window.ascending_stems
  have keptStems := CircuitStemGeometry.CircuitPartition.kept_stems annular.ordered.partition stems
  have kept := keptStems.canonicalize_comparison reference member
  have labels := annular.ordered.labels_eq.symm.trans
    (retained.labels_singleton index annular.window annulusSheet annular.ordered)
  have canonical := annular.ordered.partition.canonicalize_single member index labels
  have toPartition := congrArg RowCircuitOrder.CellCircuits.product annular.ordered.kept_eq
  have inner := annular.inner_comparison.symm.trans
    ((RootEdgeBank.ChainComparison.of_eq toPartition).trans
      (kept.trans (RootEdgeBank.ChainComparison.of_eq canonical)))
  have corner := AxisChainCoherence.Window.reverse_connect_comparison
    (edges := retained.fine.edges) (vertices := retained.fine.vertices) strip.innerCorner reference member last
  exact inner.trans (AxisChainCoherence.RootEdgeBank.ChainComparison.based_stem reference corner
    (CellBoundary.Cell.boundaryWalk (retained.fineBase.bank.toBranchCellBank.cell index)
      (retained.fineBase.bank.toBranchCellBank.cell_mem index)))

/-- The real old stem and390 inner loop compare to the two actual old/inner monotone corners around that SAME hole. -/
theorem continued_loop_comparison : RootEdgeBank.ChainComparison retained.fine.edges retained.fine.vertices
    (strip.oldStem.based annular.innerWalk)
    ((strip.oldFineCorner.northEast.append strip.innerCorner.northEast).based
      (CellBoundary.Cell.boundaryWalk (retained.fineBase.bank.toBranchCellBank.cell index)
        (retained.fineBase.bank.toBranchCellBank.cell_mem index))) := by
  let reference := fun point member => (LoopMonodromy.BranchCellBank.referenceAt
    retained.fineBase.bank.toBranchCellBank point member).toLoop
  have stem := AxisChainCoherence.RootEdgeBank.ChainComparison.based_stem reference
    strip.old_stem_comparison annular.innerWalk
  have basedInner := strip.inner_loop_comparison.based strip.oldFineCorner.northEast
  have joined := stem.trans basedInner
  exact joined.trans (RootEdgeBank.ChainComparison.of_eq (by
    simp only [Walk.based, Walk.reverse_append, Walk.append_assoc, -eq_self, -iff_self]
    let first := strip.oldFineCorner.northEast
    let middle := strip.innerCorner.northEast
    let boundary := CellBoundary.Cell.boundaryWalk (retained.fineBase.bank.toBranchCellBank.cell index)
      (retained.fineBase.bank.toBranchCellBank.cell_mem index)
    exact congrArg (fun walk => first.append walk)
      ((Walk.append_assoc middle (boundary.append middle.reverse) first.reverse).trans
        (congrArg (fun walk => middle.append walk) (Walk.append_assoc boundary middle.reverse first.reverse)))))

/-- The actual southeast route includes the boundary excursion before the northwest route, by literal retracing. -/
theorem corner_comparison : RootEdgeBank.ChainComparison retained.fine.edges retained.fine.vertices
    (strip.window.boundary.append strip.window.northEast) strip.window.southEast :=
  strip.window.boundary_prefix_comparison retained.fine.edges retained.fine.vertices
    (fun point member => (LoopMonodromy.BranchCellBank.referenceAt
      retained.fineBase.bank.toBranchCellBank point member).toLoop)

/-- The actual boundary excursion starts the opposite corner route at its computed arriving sheet. -/
theorem corner_target : RootEdgeBank.target retained.fine.edges strip.window.southEast stripSheet =
    RootEdgeBank.target retained.fine.edges strip.window.northEast (strip.branchCount.action stripSheet) :=
  (strip.corner_comparison.targets stripSheet).symm.trans
    ((RootEdgeBank.target_append retained.fine.edges strip.window.boundary strip.window.northEast stripSheet).trans
      (congrArg (RootEdgeBank.target retained.fine.edges strip.window.northEast)
        (strip.branchCount.target retained.fine.edges stripSheet)))

/-- The actual strip boundary based at the original exterior anchor, with its original reverse prefix retained. -/
@[expose] def excursion : Walk retained.fineBase.bank.grid (Cuts.Ambient curve).anchor (Cuts.Ambient curve).anchor :=
  strip.prefix.based strip.window.boundary

/-- The fresh bank's whole original branch walk uses its SAME retained fresh stem and boundary. -/
theorem fresh_loop_eq : (newBank.rows.get index).reference.walk = strip.freshStem.based
    (CellBoundary.Cell.boundaryWalk (retained.fineBase.bank.toBranchCellBank.cell index)
      (retained.fineBase.bank.toBranchCellBank.cell_mem index)) :=
  (newBank.rows.get index).reference_eq.trans
    ((congrArg (fun boundary => (newBank.rows.get index).stem.append
        (boundary.append (newBank.rows.get index).stem.reverse)) (newBank.rows.get index).boundary_eq).trans
      (congrArg (fun stem => stem.based
        (CellBoundary.Cell.boundaryWalk (retained.fineBase.bank.toBranchCellBank.cell index)
          (retained.fineBase.bank.toBranchCellBank.cell_mem index))) strip.freshStem_eq.symm))

/-- The original stem and SAME390 inner loop compare to the true southeast strip factor around the new hole. -/
theorem continued_factor_comparison : RootEdgeBank.ChainComparison retained.fine.edges retained.fine.vertices
    (strip.oldStem.based annular.innerWalk)
    ((strip.prefix.append (strip.window.southEast.append strip.suffix)).based
      (CellBoundary.Cell.boundaryWalk (retained.fineBase.bank.toBranchCellBank.cell index)
        (retained.fineBase.bank.toBranchCellBank.cell_mem index))) :=
  strip.continued_loop_comparison.trans (RootEdgeBank.ChainComparison.of_eq
    (congrArg (fun stem => stem.based
      (CellBoundary.Cell.boundaryWalk (retained.fineBase.bank.toBranchCellBank.cell index)
        (retained.fineBase.bank.toBranchCellBank.cell_mem index))) strip.old_corners_factor))

/-- Following the actual excursion and fresh stem cancels only its literal prefix retracing.

The retained boundary excursion remains present. Its possibly changed
arriving sheet starts the true fresh-corner suffix; no trivial-action
hypothesis is used.
-/
theorem excursion_stem_comparison : RootEdgeBank.ChainComparison retained.fine.edges retained.fine.vertices
    (strip.excursion.append strip.freshStem)
    (strip.prefix.append (strip.window.boundary.append (strip.window.northEast.append strip.suffix))) := by
  let reference := fun point member => (LoopMonodromy.BranchCellBank.referenceAt
    retained.fineBase.bank.toBranchCellBank point member).toLoop
  have fresh := (RootEdgeBank.ChainComparison.refl (edges := retained.fine.edges)
    (vertices := retained.fine.vertices) strip.excursion).append strip.fresh_stem_comparison
  have factor := RootEdgeBank.ChainComparison.of_eq
    (edges := retained.fine.edges) (vertices := retained.fine.vertices)
    (congrArg (fun walk => strip.excursion.append walk) strip.fresh_corner_factor)
  have cancel := RootEdgeBank.ChainComparison.erase_reverse_retrace
    (edges := retained.fine.edges) (vertices := retained.fine.vertices) reference
    (strip.prefix.append strip.window.boundary) strip.prefix (strip.window.northEast.append strip.suffix)
  have before : strip.excursion.append
      (strip.prefix.append (strip.window.northEast.append strip.suffix)) =
      (strip.prefix.append strip.window.boundary).append
        (strip.prefix.reverse.append (strip.prefix.append (strip.window.northEast.append strip.suffix))) := by
    simp only [excursion, Walk.based, Walk.append_assoc, -eq_self, -iff_self]
    rfl
  exact fresh.trans (factor.trans ((RootEdgeBank.ChainComparison.of_eq before).trans
    (cancel.trans (RootEdgeBank.ChainComparison.of_eq
      (Walk.append_assoc strip.prefix strip.window.boundary (strip.window.northEast.append strip.suffix))))))

/-- The actual390 inner replacement is the fresh GIVEN branch generator conjugated by the real strip excursion.

All statements concern the retained fine edge bank and every incoming
sheet. The excursion may itself exchange sheets and retain other branch
labels. This is an actual rooted word comparison, not a basis matrix or
period/homology equality.
-/
theorem generator_comparison : RootEdgeBank.ChainComparison retained.fine.edges retained.fine.vertices
    (strip.oldStem.based annular.innerWalk)
    (strip.excursion.based (newBank.rows.get index).reference.walk) := by
  let reference := fun point member => (LoopMonodromy.BranchCellBank.referenceAt
    retained.fineBase.bank.toBranchCellBank point member).toLoop
  let boundary := CellBoundary.Cell.boundaryWalk (retained.fineBase.bank.toBranchCellBank.cell index)
    (retained.fineBase.bank.toBranchCellBank.cell_mem index)
  have corner := (RootEdgeBank.ChainComparison.refl (edges := retained.fine.edges)
    (vertices := retained.fine.vertices) strip.prefix).append
    (strip.corner_comparison.symm.append (RootEdgeBank.ChainComparison.refl strip.suffix))
  have reordered := corner.trans (RootEdgeBank.ChainComparison.of_eq
    (congrArg (fun suffix => strip.prefix.append suffix)
      (Walk.append_assoc strip.window.boundary strip.window.northEast strip.suffix)))
  have basedCorner := AxisChainCoherence.RootEdgeBank.ChainComparison.based_stem reference reordered boundary
  have first := strip.continued_factor_comparison.trans basedCorner
  have second := AxisChainCoherence.RootEdgeBank.ChainComparison.based_stem reference
    strip.excursion_stem_comparison boundary
  have nested : (strip.excursion.append strip.freshStem).based boundary =
      strip.excursion.based (strip.freshStem.based boundary) := by
    simp only [Walk.based, Walk.reverse_append, Walk.append_assoc, -eq_self, -iff_self]
    rfl
  exact first.trans (second.symm.trans ((RootEdgeBank.ChainComparison.of_eq nested).trans
    (RootEdgeBank.ChainComparison.of_eq (congrArg (fun walk => strip.excursion.based walk)
      strip.fresh_loop_eq.symm))))

/-- The actual corner-value difference retains the computed branch excursion and signed regular corrections. -/
theorem corner_values (value : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    retained.fine.edges.chainValue retained.fine.vertices value strip.window.southEast stripSheet =
      wordValue value strip.ordered.compiled.word +
        CellBoundary.sumValues (fun occurrence => wordValue value occurrence.word) strip.ordered.compiled.regulars +
        retained.fine.edges.chainValue retained.fine.vertices value strip.window.northEast
          (strip.branchCount.action stripSheet) := by
  have expanded := (strip.corner_comparison.values value anti stripSheet).symm.trans
    (RootEdgeBank.chainValue_append (edges := retained.fine.edges) (vertices := retained.fine.vertices)
      value strip.window.boundary strip.window.northEast stripSheet)
  have boundary := strip.ordered.values value anti
  have after := congrArg (retained.fine.edges.chainValue retained.fine.vertices value strip.window.northEast)
    (strip.branchCount.target retained.fine.edges stripSheet)
  exact expanded.trans (congrArg₂ (fun first last => first + last) boundary after)

/-- The exact corner polygon retains the branch excursion, regular corrections and their full cross-ribbon term. -/
theorem corner_areas (value : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    retained.fine.edges.chainArea retained.fine.vertices value strip.window.southEast stripSheet =
      wordArea value strip.ordered.compiled.word + AreaTerm.total value strip.ordered.compiled.areaTerms +
        retained.fine.edges.chainArea retained.fine.vertices value strip.window.northEast
          (strip.branchCount.action stripSheet) +
        BoundaryRibbon.area
          (wordValue value strip.ordered.compiled.word + CellBoundary.sumValues
            (fun occurrence => wordValue value occurrence.word) strip.ordered.compiled.regulars)
          (retained.fine.edges.chainValue retained.fine.vertices value strip.window.northEast
            (strip.branchCount.action stripSheet)) := by
  have expanded := (strip.corner_comparison.areas value anti stripSheet).symm.trans
    (RootEdgeBank.chainArea_append (edges := retained.fine.edges) (vertices := retained.fine.vertices)
      value strip.window.boundary strip.window.northEast stripSheet)
  have boundaryArea := strip.ordered.areas value anti
  have boundaryValue := strip.ordered.values value anti
  have afterArea := congrArg (retained.fine.edges.chainArea retained.fine.vertices value strip.window.northEast)
    (strip.branchCount.target retained.fine.edges stripSheet)
  have afterValue := congrArg (retained.fine.edges.chainValue retained.fine.vertices value strip.window.northEast)
    (strip.branchCount.target retained.fine.edges stripSheet)
  exact expanded.trans (congrArg₂ (fun first last => first + last)
    (congrArg₂ (fun first last => first + last) boundaryArea afterArea)
    (congrArg₂ BoundaryRibbon.area boundaryValue afterValue))

end StemStrip

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement

end
