module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowBranchWinding
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowRootTransport
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.WindowBoundary

open Purelib.Polynomial.Geometry.Grid.WindowBoundary

open Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

public section

/-!
# The actual sheet difference between the two branch-stem routes

The shared exterior stem goes up the left side and then right. The other
L-shaped connector goes right along the bottom and then up. Their relative
sheet is the parity of the retained branch cells in the southwest rectangle.
Every report retains that rectangle, its selected holes and the actual paths.
-/

section

open Purelib.Geometry.Rational (Box)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Branches (FramedBranchCellBank)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

section

namespace Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank

/-- The rectangle between the original ambient anchor and the selected branch cell's anchor. -/
@[expose] def southwestBox
    (bank : Branches.FramedBranchCellBank curve branches higher) (index : BranchIsolation.Data.Index branches) : Box :=
  ⟨(Cuts.Ambient curve).xLower, (bank.cell index).box.xLower,
    (Cuts.Ambient curve).yLower, (bank.cell index).box.yLower,
    (bank.cell index).horizontal.lower.inside.1, (bank.cell index).vertical.lower.inside.1⟩

/-- The exact framed-grid window on the retained southwest branch rectangle. -/
@[expose] def southwestWindow
    (bank : Branches.FramedBranchCellBank curve branches higher) (index : BranchIsolation.Data.Index branches) :
    Polynomial.Geometry.Grid.WindowBoundary.Window bank.grid (bank.southwestBox index) :=
  Polynomial.Geometry.Grid.WindowBoundary.Window.build bank.grid (bank.southwestBox index)
    bank.frame.xLower ((bank.cell index).anchor_mem (bank.cell_mem index)).1
    bank.frame.yLower ((bank.cell index).anchor_mem (bank.cell_mem index)).2

end Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank

end

section

variable {base : FramedPuncturedGrid curve branches higher} {lifted :
  LiftedPuncturedGrid base}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedStemTransport.LiftedPuncturedGrid.BasedBranchBank

set_option genInjectivity false in
/-- The actual direct connector and retained exterior stem, together with their southwest branch selection.

Both paths retain their original grid endpoints; the cached finite branch count determines their relative sheet action.
-/
structure StemComparison (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (index : BranchIsolation.Data.Index
  branches) where
  /-- The actual southwest grid window associated with the retained branch index. -/ window :
    Polynomial.Geometry.Grid.WindowBoundary.Window base.bank.grid
    (base.bank.southwestBox index)
  /-- The cached finite branch selection and parity action on this exact window. -/ branches :
    Polynomial.Geometry.Grid.WindowBoundary.Window.BranchCount
    base.faces window
  /-- The retained rightward-then-upward connector from the original base to the selected branch anchor. -/ direct :
    Walks.Walk base.bank.grid (Cuts.Ambient curve).anchor (base.bank.cell index).box.anchor
  /-- The direct connector is exactly the original grid connection on these retained endpoints. -/ direct_eq : direct =
    Grid.connect base.bank.grid _ _
    (FramedBranchCellBank.baseMember base.bank)
    ((base.bank.cell index).anchor_mem (base.bank.cell_mem index))
  /-- The original cached exterior stem to the selected branch anchor. -/ stem : Walks.Walk base.bank.grid (Cuts.Ambient
    curve).anchor (base.bank.cell index).box.anchor
  /-- The retained stem is exactly the selected row of the original branch bank. -/ stem_eq : stem = (bank.rows.get
    index).stem

constructive_injectivity StemComparison

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedStemTransport.LiftedPuncturedGrid.BasedBranchBank

section

variable {bank : BasedBranchBank
  lifted} {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedStemTransport
namespace LiftedPuncturedGrid.BasedBranchBank.StemComparison

/-- Cache the southwest branch window and its parity together with both actual connector paths. -/
@[expose] def build (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (index : BranchIsolation.Data.Index branches) :
  BasedBranchBank.StemComparison bank
  index :=
  let window := base.bank.southwestWindow index
  let branches := Polynomial.Geometry.Grid.WindowBoundary.Window.BranchCount.build base.faces window
  let direct := Grid.connect base.bank.grid _ _
    (FramedBranchCellBank.baseMember base.bank)
    ((base.bank.cell index).anchor_mem (base.bank.cell_mem index))
  ⟨window, branches, direct, rfl, (bank.rows.get index).stem, rfl⟩

/-- Both sides read the same retained root-edge bank. The sheet correction comes from the complete finite southwest
branch selection. -/
theorem target (comparison :
  BasedBranchBank.StemComparison bank
  index) (sheet : Fin 2) :
    RootEdgeBank.target lifted.edges comparison.direct sheet =
      RootEdgeBank.target lifted.edges comparison.stem (comparison.branches.action sheet) := by
  rw [comparison.direct_eq, comparison.stem_eq, (bank.rows.get index).stem_eq]
  exact WindowRootTransport.corner_target
    comparison.branches lifted.edges
    (FramedBranchCellBank.baseMember base.bank)
    ((base.bank.cell index).anchor_mem (base.bank.cell_mem index)) sheet

/-- Endpoint coordinates permit a same-sheet substitution exactly when the cached southwest branch count is even. -/
theorem same_sheet_iff (comparison :
  BasedBranchBank.StemComparison bank
  index) (sheet : Fin 2) :
    RootEdgeBank.target lifted.edges comparison.direct sheet = RootEdgeBank.target lifted.edges comparison.stem sheet ↔
      comparison.branches.flip = false := by
  rw [comparison.target]
  constructor
  · intro equal
    have same := lifted.edges.target_injective
      (fun point member =>
        (BranchCellBank.referenceAt
          base.bank.toBranchCellBank point member).toLoop) comparison.stem equal
    cases flip : comparison.branches.flip with
    | false => rfl
    | true =>
        change (if comparison.branches.flip then BranchCutLifts.otherSheet sheet else sheet) = sheet at same
        rw [flip] at same
        have values := congrArg Fin.val same
        have bound := sheet.isLt
        change 1 - sheet.val = sheet.val at values
        omega
  · intro even
    rw [Polynomial.Geometry.Grid.WindowBoundary.Window.BranchCount.action, even]
    rfl

end BasedBranchBank.StemComparison
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedStemTransport.LiftedPuncturedGrid

end
end
end
