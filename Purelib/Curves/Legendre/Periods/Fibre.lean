module
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Legendre.Paths.Preparation
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
import Purelib.Data.List.Pairwise
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Data.Fin.Cases
import Purelib.Polynomial.Geometry.Grid.CellBoundary
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Vector.Operational.Basic
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Integration.Program.Gaussian.Basic
public import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Legendre.Paths
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coefficient.Progressive.Table
import Purelib.RootIsolation.Progressive.Chamber.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Legendre.FactorGeometry
import Purelib.Data.Fin.Bijection.Search
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Vector.Dependent

open Purelib

open Purelib.Approximation.Gaussian.Vector

open Purelib.Curves

open Purelib.Curves.Legendre

open Purelib.Integration

open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

open Purelib.Riemann.Periods

section
@[expose] public section

/-!
# Finite Gauss--Manin continuation for the Legendre family

Finite root and homology continuation along an open parameter path produces
endpoint periods by the *dual* (transposed) homology action on actual
target-fibre programs.  It does not equate periods on different Legendre
curves.  Shrinking comparisons remain available below as a generic way to
prove that two refinement programs name the same value, without attaching
that stronger statement to changing-fibre continuation.
-/

namespace Purelib.Curves.Legendre.Periods.Fibre

/-! ## Exact endpoint fibres -/

/-- The genus-one curve carried by one Legendre root frame. Its finite squarefree certificate is reused from the
displayed simple-root chamber. -/
def frameCurve {parameter : Data.Gaussian.Basic.Canonical} (frame :
  Paths.Frame parameter) :
    Hyperelliptic.Basic.HyperellipticCurve 1 where
  polynomial := Paths.polynomial parameter
  nonzero := Paths.polynomial_isZero parameter
  squarefree := by
    have certificate := frame.chamber.chamber.squarefree
    change Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate
      frame.chamber.polynomial at certificate
    rw [frame.polynomial_eq] at certificate
    exact certificate
  degreeShape := .odd (Paths.polynomial_natDegree parameter)

/-- The genus-one curve constructed from the retained root frame has its exact displayed Legendre polynomial. -/
@[simp] theorem frameCurve_polynomial {parameter :
  Data.Gaussian.Basic.Canonical}
    (frame : Paths.Frame parameter) :
    (frameCurve frame).polynomial = Paths.polynomial parameter := rfl

set_option genInjectivity false in
/-- Certified raw periods on the exact fibre selected by one frame. -/
structure FibreData {parameter : Data.Gaussian.Basic.Canonical} (frame :
  Paths.Frame parameter) where
  /-- The certified period programs on this exact frame-selected genus-one curve. -/ periods : PeriodMatrix.PeriodData
    (frameCurve frame)

constructive_injectivity Purelib.Curves.Legendre.Periods.Fibre.FibreData

namespace FibreData

/-- The `a` and `b` refinement programs in locked column-vector order. -/
def rawRefinement {parameter : Data.Gaussian.Basic.Canonical}
  {frame : Paths.Frame parameter}
    (data : Curves.Legendre.Periods.Fibre.FibreData frame) (coordinate : Fin 2) :
      Program.Gaussian.Basic.RefinementProgram :=
  if coordinate = 0 then
    (data.periods.aProgram 0 0).integral
  else
    (data.periods.bProgram 0 0).integral

/-- The productive raw period vector in the same order. -/
def rawPeriods {parameter : Data.Gaussian.Basic.Canonical} {frame
  : Paths.Frame parameter}
    (data : Curves.Legendre.Periods.Fibre.FibreData frame) : Operational.Basic.RawPeriodVector :=
  fun coordinate => (data.rawRefinement coordinate).output

/-- Each retained raw period coordinate is the output of its original refinement program. -/
@[simp] theorem rawPeriods_apply {parameter :
  Data.Gaussian.Basic.Canonical}
    {frame : Paths.Frame parameter} (data : Curves.Legendre.Periods.Fibre.FibreData frame) (coordinate : Fin 2) :
    data.rawPeriods coordinate = (data.rawRefinement coordinate).output := rfl

/-- The first raw coordinate is exactly the certified genus-one `a` period. -/
theorem rawRefinement_zero {parameter :
  Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (data : Curves.Legendre.Periods.Fibre.FibreData frame) :
    data.rawRefinement 0 = (data.periods.aProgram 0 0).integral := rfl

/-- The second raw coordinate is exactly the certified genus-one `b` period. -/
theorem rawRefinement_one {parameter :
  Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    (data : Curves.Legendre.Periods.Fibre.FibreData frame) :
    data.rawRefinement 1 = (data.periods.bProgram 0 0).integral := by
  unfold Periods.Fibre.FibreData.rawRefinement
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

end FibreData
end Purelib.Curves.Legendre.Periods.Fibre

end

public section

namespace Purelib.Curves.Legendre.Periods.Fibre

open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Data.Fin (Bijection)
open Purelib.Data.Vector (DependentVector)
open Purelib.Polynomial.Geometry.Grid.WindowBoundary (Window)

/-- An original finite bijection whose logical points belong to their actual retained branch cells. -/
abbrev BranchLabels {parameter : Data.Gaussian.Basic.Canonical} (frame : Paths.Frame parameter)
    {branches : BranchIsolation.Data (frameCurve frame)} {higher : 1 < (frameCurve frame).polynomial.natDegree}
    (bank : BranchCellBank (frameCurve frame) branches higher) :=
  { labels : Bijection branches.siteCount 3 // ∀ index,
    (bank.cell index).box.Contains (Paths.branchPoint parameter (labels.forward index)) }

/-- Match the actual retained branch-bank cells to the original three logical Legendre points.

Each original selected cell supplies its own winding-four certificate.
The three exact membership selections are materialized once. Separated
original cells make that finite map injective, and the original bounded
inverse-search constructor supplies both inverse laws. No successful
matching, root equality or different canonical period bank is an input.
-/
def branchLabels {parameter : Data.Gaussian.Basic.Canonical} (frame : Paths.Frame parameter)
    {branches : BranchIsolation.Data (frameCurve frame)} {higher : 1 < (frameCurve frame).polynomial.natDegree}
    (bank : BranchCellBank (frameCurve frame) branches higher) : BranchLabels frame bank := by
  have countEq : branches.siteCount = 3 := branches.count_eq.trans (Paths.polynomial_natDegree parameter)
  let selected := DependentVector.ofFn fun position : Fin 3 =>
    let index := Fin.cast countEq.symm position
    let cell := bank.cell index
    have winding : Polynomial.Winding.Box.Basic.quadrupledBoxWinding
        (Paths.polynomial parameter) cell.box = 4 :=
      Hyperelliptic.Branches.BranchCellWinding.selected_winding_four bank index
    FactorGeometry.branchInBox cell.box_proper
      (fun zero => (by decide +kernel : (4 : Int) ≠ 0) (winding.symm.trans zero))
  let map := fun position : Fin 3 => (selected.get position).val
  have injective : Function.Injective map := by
    intro first last same
    by_cases equal : first = last
    · exact equal
    have different : Fin.cast countEq.symm first ≠ Fin.cast countEq.symm last := by
      intro identical
      have scalar := congrArg (fun index : Fin branches.siteCount => index.val) identical
      exact equal (Fin.ext scalar)
    exact ((bank.cells_separated _ _ different).points_ne
      (selected.get first).property (selected.get last).property
      (congrArg (Paths.branchPoint parameter) same)).elim
  let labels := Bijection.comp (Bijection.ofInjectiveEndomap map injective) (Bijection.cast countEq)
  refine ⟨labels, ?_⟩
  intro index
  have forward : labels.forward index = map (Fin.cast countEq index) := by
    calc
      labels.forward index = (Bijection.ofInjectiveEndomap map injective).forward
          ((Bijection.cast countEq).forward index) := Bijection.comp_forward _ _ index
      _ = (Bijection.ofInjectiveEndomap map injective).forward (Fin.cast countEq index) :=
        congrArg (Bijection.ofInjectiveEndomap map injective).forward (Bijection.cast_forward countEq index)
      _ = map (Fin.cast countEq index) :=
        Bijection.ofInjectiveEndomap_forward map injective (Fin.cast countEq index)
  have returned : Fin.cast countEq.symm (Fin.cast countEq index) = index := by
    exact Fin.ext rfl
  have inside := (selected.get (Fin.cast countEq index)).property
  have originalInside : (bank.cell index).box.Contains
      (Paths.branchPoint parameter (map (Fin.cast countEq index))) :=
    Eq.mp (congrArg (fun source => (bank.cell source).box.Contains
      (Paths.branchPoint parameter (map (Fin.cast countEq index)))) returned) inside
  rewrite [forward]
  exact originalInside

/-- Refining the same labelled branch cells preserves their checked logical matching pointwise.

Both supplied bijections retain their actual cell-membership receipts.
The old inverse locates each new logical point in the old family; positive
separation of the old cells identifies that original index. No equality
of root channels, new branch order or numerical observation is inferred.
-/
theorem branchLabels_refines {parameter : Data.Gaussian.Basic.Canonical} (frame : Paths.Frame parameter)
    {branches : BranchIsolation.Data (frameCurve frame)} {higher : 1 < (frameCurve frame).polynomial.natDegree}
    (old current : BranchCellBank (frameCurve frame) branches higher)
    (oldLabels : BranchLabels frame old) (currentLabels : BranchLabels frame current)
    (refines : ∀ index, (current.cell index).box.Refines (old.cell index).box)
    (index : BranchIsolation.Data.Index branches) :
    oldLabels.val.forward index = currentLabels.val.forward index := by
  let logical := currentLabels.val.forward index
  let previous := oldLabels.val.backward logical
  have inPrevious := oldLabels.property previous
  rw [oldLabels.val.forward_backward logical] at inPrevious
  have inOriginal := (refines index).contains (currentLabels.property index)
  have same : previous = index := by
    by_cases equal : previous = index
    · exact equal
    exact ((old.cells_separated previous index equal).points_ne inPrevious inOriginal rfl).elim
  exact (congrArg oldLabels.val.forward same).symm.trans (oldLabels.val.forward_backward logical)

namespace BranchLabels

variable {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (frameCurve frame)} {higher : 1 < (frameCurve frame).polynomial.natDegree}
    {bank : BranchCellBank (frameCurve frame) branches higher}

/-- The actual matched branch cells follow the strict horizontal order of two points on the same ordinate.

The original branch-family separation excludes vertical separation at the
common ordinate. Reversed horizontal separation would reverse the given
point order. The retained bijection identifies both original cell indices.
-/
theorem left_of (labels : BranchLabels frame bank) {first last : Fin 3} (different : first ≠ last)
    (ordinate : (Paths.branchPoint parameter first).im = (Paths.branchPoint parameter last).im)
    (ordered : (Paths.branchPoint parameter first).re < (Paths.branchPoint parameter last).re) :
    (bank.cell (labels.val.backward first)).box.xUpper < (bank.cell (labels.val.backward last)).box.xLower := by
  have distinct : labels.val.backward first ≠ labels.val.backward last := by
    intro equal
    exact different ((labels.val.forward_backward first).symm.trans
      ((congrArg labels.val.forward equal).trans (labels.val.forward_backward last)))
  have inFirst := labels.property (labels.val.backward first)
  have inLast := labels.property (labels.val.backward last)
  rw [labels.val.forward_backward first] at inFirst
  rw [labels.val.forward_backward last] at inLast
  rcases bank.cells_separated _ _ distinct with before | after | below | above
  · exact before
  · exact (lt_irrefl _ (ordered.trans (inLast.2.1.trans_lt (after.trans_le inFirst.1)))).elim
  · have impossible := inFirst.2.2.2.trans_lt (below.trans_le inLast.2.2.1)
    rw [ordinate] at impossible
    exact (lt_irrefl _ impossible).elim
  · have impossible := inLast.2.2.2.trans_lt (above.trans_le inFirst.2.2.1)
    rw [ordinate] at impossible
    exact (lt_irrefl _ impossible).elim

end BranchLabels

/-- The original ambient rectangle cut at the left side of one actually matched branch cell.

Three sides remain the original ambient frame. The fourth is an existing
clear grid coordinate of that exact cell, so no line, frame or branch
producer is run to choose the rectangle.
-/
@[expose] def branchWindowBox {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (frameCurve frame)} {higher : 1 < (frameCurve frame).polynomial.natDegree}
    (bank : FramedBranchCellBank (frameCurve frame) branches higher)
    (labels : BranchLabels frame bank.toBranchCellBank) (index : Fin 3) : Geometry.Rational.Box :=
  let cell := bank.toBranchCellBank.cell (labels.val.backward index)
  { xLower := cell.box.xLower
    xUpper := (Cuts.Ambient (frameCurve frame)).xUpper
    yLower := (Cuts.Ambient (frameCurve frame)).yLower
    yUpper := (Cuts.Ambient (frameCurve frame)).yUpper
    x_valid := cell.box.x_valid.trans cell.box_refines.2.1
    y_valid := (Cuts.Ambient (frameCurve frame)).y_valid }

/-- Build the existing grid window from the actual matched cell side and retained ambient frame.

All four lookups read the same supplied branch bank. The original window
constructor keeps its axis walks and original filtered cells; it performs
no branch matching, isolation or canonical period preparation.
-/
def branchWindow {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (frameCurve frame)} {higher : 1 < (frameCurve frame).polynomial.natDegree}
    (bank : FramedBranchCellBank (frameCurve frame) branches higher)
    (labels : BranchLabels frame bank.toBranchCellBank) (index : Fin 3) :
    Window bank.grid (branchWindowBox bank labels index) :=
  let cell := bank.toBranchCellBank.cell (labels.val.backward index)
  let present := cell.anchor_mem (bank.toBranchCellBank.cell_mem (labels.val.backward index))
  Window.build bank.grid (branchWindowBox bank labels index)
    present.1 bank.frame.xUpper bank.frame.yLower bank.frame.yUpper

/-- The real right-hand branch window contains exactly the actual matched moving and unit branch cells.

For a real parameter strictly between zero and one, original cell
separation orders the three matched holes. The window starts at the
actual moving cell's clear left side and keeps the original ambient
frame, so the zero cell is excluded and the other two are retained.
This is cell incidence, independent of a chosen root sheet or period.
-/
theorem branchWindow_selected {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (frameCurve frame)} {higher : 1 < (frameCurve frame).polynomial.natDegree}
    (bank : FramedBranchCellBank (frameCurve frame) branches higher)
    (labels : BranchLabels frame bank.toBranchCellBank) (real : parameter.im = 0)
    (positive : 0 < parameter.re) (unit : parameter.re < 1) (index : BranchIsolation.Data.Index branches) :
    (bank.toBranchCellBank.cell index).box.Refines (branchWindowBox bank labels 1) ↔
      labels.val.forward index ≠ 0 := by
  have beforeZero := labels.left_of (first := 0) (last := 1) (by decide +kernel)
    (show (Paths.branchPoint parameter 0).im = (Paths.branchPoint parameter 1).im from real.symm)
    (show (Paths.branchPoint parameter 0).re < (Paths.branchPoint parameter 1).re from positive)
  have beforeUnit := labels.left_of (first := 1) (last := 2) (by decide +kernel)
    (show (Paths.branchPoint parameter 1).im = (Paths.branchPoint parameter 2).im from real)
    (show (Paths.branchPoint parameter 1).re < (Paths.branchPoint parameter 2).re from unit)
  constructor
  · intro contained zero
    have original : labels.val.backward 0 = index :=
      (congrArg labels.val.backward zero.symm).trans (labels.val.backward_forward index)
    have lower := contained.1
    change (bank.toBranchCellBank.cell (labels.val.backward 1)).box.xLower ≤
      (bank.toBranchCellBank.cell index).box.xLower at lower
    rw [← original] at lower
    exact (lt_irrefl _ (((bank.toBranchCellBank.cell (labels.val.backward 0)).box.x_valid.trans_lt
      beforeZero).trans_le lower)).elim
  · intro nonzero
    have lower : (bank.toBranchCellBank.cell (labels.val.backward 1)).box.xLower ≤
        (bank.toBranchCellBank.cell index).box.xLower := by
      rcases Data.Fin.Cases.three (labels.val.forward index) with zero | moving | one
      · exact (nonzero zero).elim
      · have original : index = labels.val.backward 1 :=
          (labels.val.backward_forward index).symm.trans (congrArg labels.val.backward moving)
        rewrite [original]
        exact Data.Rat.Fraction.Order.Basic.le_refl _
      · have original : index = labels.val.backward 2 :=
          (labels.val.backward_forward index).symm.trans (congrArg labels.val.backward one)
        rw [original]
        exact (bank.toBranchCellBank.cell (labels.val.backward 1)).box.x_valid.trans beforeUnit.le
    have ambient := (bank.toBranchCellBank.cell index).box_refines
    exact ⟨lower, ambient.2.1, ambient.2.2.1, ambient.2.2.2⟩

open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Coordinates
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.Window (OrderedBranches)

namespace BranchLabels

variable {parameter : Data.Gaussian.Basic.Canonical} {frame : Paths.Frame parameter}
    {branches : BranchIsolation.Data (frameCurve frame)} {higher : 1 < (frameCurve frame).polynomial.natDegree}
    {bank : BranchCellBank (frameCurve frame) branches higher}

/-- Three decreasing finite branch indices have their literal reverse logical order.

The original list length fixes the three occurrences. Their strict index
relations and retained finite bounds identify each coordinate separately.
-/
private theorem descending_three (values : List (Fin 3))
    (ordered : values.Pairwise (fun first last => last.val < first.val))
    (count : values.length = 3) : values = [2, 1, 0] := by
  cases values with
  | nil => nomatch count
  | cons first rest =>
      cases rest with
      | nil => nomatch count
      | cons second rest =>
          cases rest with
          | nil => nomatch count
          | cons third rest =>
              have empty : rest.length = 0 := Nat.succ.inj (Nat.succ.inj (Nat.succ.inj count))
              cases rest with
              | cons next rest => nomatch empty
              | nil =>
                  have firstNext := (List.pairwise_cons.mp ordered).1 second List.mem_cons_self
                  have secondNext := (List.pairwise_cons.mp (List.pairwise_cons.mp ordered).2).1 third
                    List.mem_cons_self
                  have firstBound := first.isLt
                  have secondBound := second.isLt
                  have thirdBound := third.isLt
                  have firstEq : first = 2 := Fin.ext (by omega0)
                  have secondEq : second = 1 := Fin.ext (by omega0)
                  have thirdEq : third = 0 := Fin.ext (by omega0)
                  cases firstEq
                  cases secondEq
                  cases thirdEq
                  rfl

/-- A full ambient window reads the actual retained real Legendre holes in reverse logical order.

All three original winding-four cells strictly cross the real axis. The
cached circuit partition retains upward rows and right-to-left columns,
so its actual branch occurrences are unit, moving and zero. The original
logical bijection and every original window/root owner remain unchanged.
-/
theorem window_labels (labels : BranchLabels frame bank) (real : parameter.im = 0)
    (positive : 0 < parameter.re) (unit : parameter.re < 1)
    {faces : PuncturedFaces bank}
    {window : Window bank.grid (Cuts.Ambient (frameCurve frame))}
    {frames : RootFrames bank.grid} {vertices : VertexBank bank.grid} {edges : RootEdgeBank frames}
    {sheet : Fin 2} (prepared : OrderedBranches faces window edges vertices sheet) :
    prepared.labels.map labels.val.forward = [2, 1, 0] := by
  have projected (index : Fin 3) : (Paths.branchProjection parameter index 0).re =
      (Paths.branchPoint parameter index).re := by
    rewrite [Paths.branchProjection, Rotation.rotate_real, Fraction.Field.zero_mul_direct]
    exact (Fraction.Field.add_comm _ 0).trans (Fraction.Field.zero_add _)
  have moving : (Paths.branchProjection parameter 1 0).re = parameter.re := projected 1
  have identity := Paths.branchOrder_of_between parameter 0 (moving.symm ▸ positive) (moving.symm ▸ unit)
  have separated : parameter.re + 0 * parameter.im ≠ 0 ∧ parameter.re + 0 * parameter.im ≠ 1 := by
    rewrite [Fraction.Field.zero_mul_direct,
      show parameter.re + 0 = parameter.re from
        (Fraction.Field.add_comm _ 0).trans (Fraction.Field.zero_add _)]
    exact ⟨ne_of_gt positive, ne_of_lt unit⟩
  have increasing (first last : Fin 3) (order : first.val < last.val) :
      (Paths.branchPoint parameter first).re < (Paths.branchPoint parameter last).re := by
    have actual := Paths.branchOrder_real_lt parameter 0 separated first last order
    rewrite [identity, Bijection.identity_forward, Bijection.identity_forward] at actual
    rewrite [projected first, projected last] at actual
    exact actual
  have axis (index : BranchIsolation.Data.Index branches) :
      (bank.cell index).box.yLower < 0 ∧ 0 < (bank.cell index).box.yUpper := by
    have winding := BranchCellWinding.selected_winding_four bank index
    exact FactorGeometry.real_axis_of_winding real (bank.cell index).box_proper (bank.cell index).boundaryClearance
      (fun zero => (by decide +kernel : (4 : Int) ≠ 0) (winding.symm.trans zero))
  have ordinate (index : Fin 3) : (Paths.branchPoint parameter index).im = 0 := by
    rcases Data.Fin.Cases.three index with zero | moving | one <;> subst index
    · rfl
    · exact real
    · rfl
  have treeOrder : prepared.ordered.tree.cells.Pairwise
      (fun first last => ClearGrid.Interval.Before first.vertical last.vertical ∨
        first.vertical = last.vertical ∧ ClearGrid.Interval.Before last.horizontal first.horizontal) := by
    rewrite [prepared.ordered.tree_eq]
    exact window.circuits_pairwise
  have selectedOrder := prepared.partition.labels_pairwise treeOrder
  have labelOrder : prepared.labels.Pairwise (fun first last =>
      (labels.val.forward last).val < (labels.val.forward first).val) := by
    rewrite [prepared.labels_eq]
    refine List.Pairwise.imp ?_ selectedOrder
    intro first last relation
    rcases relation with rows | ⟨_, columns⟩
    · have impossible := (axis last).1.trans ((axis first).2.trans_le rows)
      exact (lt_irrefl _ impossible).elim
    · apply Nat.lt_of_not_ge
      intro before
      rcases Nat.lt_or_eq_of_le before with strict | same
      · have actual := labels.left_of
          (first := labels.val.forward first) (last := labels.val.forward last)
          (fun equal => Nat.ne_of_lt strict (congrArg Fin.val equal))
          ((ordinate _).trans (ordinate _).symm) (increasing _ _ strict)
        rewrite [labels.val.backward_forward first, labels.val.backward_forward last] at actual
        have impossible := (bank.cell first).box_proper.1.trans
          (actual.trans ((bank.cell last).box_proper.1.trans_le columns))
        exact lt_irrefl _ impossible
      · have equal : first = last :=
          (labels.val.backward_forward first).symm.trans
            ((congrArg labels.val.backward (Fin.ext same)).trans (labels.val.backward_forward last))
        cases equal
        exact not_lt_of_ge columns (bank.cell first).horizontal.ordered
  let values := prepared.labels.map labels.val.forward
  have sorted : values.Pairwise (fun first last => last.val < first.val) :=
    Pairwise.pairwise_map.mpr labelOrder
  have unique : values.Nodup := Nodup.nodup_map_of_injective (fun first last equal =>
    (labels.val.backward_forward first).symm.trans
      ((congrArg labels.val.backward equal).trans (labels.val.backward_forward last))) prepared.unique
  have complete (index : Fin 3) : index ∈ values := by
    have member := (prepared.selected (labels.val.backward index)).mpr
      (bank.cell (labels.val.backward index)).box_refines
    exact Map.mem_map.mpr ⟨labels.val.backward index, member, labels.val.forward_backward index⟩
  have allUnique : ([0, 1, 2] : List (Fin 3)).Nodup := by decide +kernel
  have count : values.length = 3 := Nat.le_antisymm
    (Nodup.nodup_length_le_of_mem unique allUnique (by
      intro index _
      rcases Data.Fin.Cases.three index with zero | moving | one <;> subst index <;> decide +kernel))
    (Nodup.nodup_length_le_of_mem allUnique unique (fun index _ => complete index))
  exact descending_three values sorted count

end BranchLabels

end Purelib.Curves.Legendre.Periods.Fibre
