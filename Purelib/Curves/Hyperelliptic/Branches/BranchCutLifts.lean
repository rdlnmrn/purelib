module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Closed
public import Purelib.Geometry.Path.Gaussian.Lifted.Family
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Topology.Surface.CellularHomology
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.Site

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

open Purelib.Data.Fin

open Purelib.Data.Fin.Bijection.Basic

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Path.Gaussian

open Purelib.Geometry.Path.Gaussian.Lifted

open Purelib.Geometry.Path.Gaussian.Lifted.Basic

open Purelib.Geometry.Path.Gaussian.Lifted.Closed

open Purelib.Polynomial

open Purelib.Polynomial.Clearance.Box.Boundary

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.RootIsolation.State

open Purelib.Topology.Surface

@[expose] public section

/-!
# Two-sheet lifts of the certified branch cuts

Each clear base segment lifts on a fixed labelled sheet with identity sheet
transport.  At either end of a cut a zero-length cell carries the explicit
two-sheet transposition.  Traversing one bank forward, switching sheets,
traversing the other bank backward, and switching again therefore gives a
finite closed lifted path around the cut.
-/

namespace Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

open Purelib.Riemann.Curves.AlgebraicDifferentials

/-- Exact Gaussian rational coordinates for the retained clear paths. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- The finite dense Gaussian polynomial defining the retained clearance problem. -/
abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- A finite rational rectangular ambient or root owner. -/
abbrev Box := Rational.Box
/-- An executable bijection between the retained finite sheet sets. -/
abbrev Bijection := Data.Fin.Bijection
/-- A retained root owner with polynomial clearance and certified winding one. -/
abbrev WindingOneState := WindingOne.Basic.WindingOneState

/-- The other label in the explicitly finite two-sheet set. -/
def otherSheet (sheet : Fin 2) : Fin 2 :=
  ⟨1 - sheet.val, by
    have bound := sheet.isLt
    omega0⟩

/-- The other label of sheet zero is sheet one. -/
@[simp] theorem otherSheet_zero : otherSheet (0 : Fin 2) = 1 := rfl

/-- The other label of sheet one is sheet zero. -/
@[simp] theorem otherSheet_one : otherSheet (1 : Fin 2) = 0 := rfl

/-- Switching the finite two-sheet label twice returns the original label. -/
@[simp] theorem otherSheet_other (sheet : Fin 2) :
    otherSheet (otherSheet
      sheet) = sheet := by
  apply Fin.ext
  have bound := sheet.isLt
  simp only [otherSheet]
  omega0

/-- The local monodromy of a simple hyperelliptic branch point. -/
def sheetSwap : Bijection 2 2 where
  forward := otherSheet
  backward := otherSheet
  backward_forward := otherSheet_other
  forward_backward := otherSheet_other

/-- The forward sheet permutation is the explicit other-sheet operation. -/
@[simp] theorem sheetSwap_forward (sheet : Fin 2) :
    Curves.Hyperelliptic.Branches.BranchCutLifts.sheetSwap.forward sheet =
      otherSheet sheet := rfl

namespace ClearSegment

/-- Reverse a certified segment without changing its clearance line. -/
def reverse {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
  Curves.Hyperelliptic.Branches.BranchCutLifts.Box}
    {start finish : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) :
    ClearPath.ClearSegment polynomial ambient finish start := by
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper
      clearance =>
      exact .horizontal xFinish xStart y finishLower finishUpper
        startLower startUpper clearance
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper
      clearance =>
      exact .vertical x yFinish yStart finishLower finishUpper
        startLower startUpper clearance

/-- Reversing a segment retains the certified line-clearance cache. -/
@[simp] theorem reverse_clearanceBound
    {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
      Curves.Hyperelliptic.Branches.BranchCutLifts.Box}
    {start finish : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish) :
    (reverse segment).clearanceBound = segment.clearanceBound
      := by
  cases segment <;> rfl

/-- Reversal complements the affine segment parameter. -/
theorem reverse_pointAt
    {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
      Curves.Hyperelliptic.Branches.BranchCutLifts.Box}
    {start finish : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Fraction.Rational) :
    (reverse segment).pointAt parameter = segment.pointAt (1 -
      parameter) := by
  cases segment <;>
    apply Data.Gaussian.Basic.ext <;>
    simp only [ClearSegment.pointAt,
      Scale.scale_re, Scale.scale_im,
      Basic.add_re,
      Basic.add_im,
      Basic.sub_re,
      Basic.sub_im, Components.Basic.point] <;>
    ring1

/-- Reversing the retained clear geometry preserves containment in its original ambient. -/
theorem reverse_withinAmbient {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
  Curves.Hyperelliptic.Branches.BranchCutLifts.Box}
    {start finish : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian}
    (segment : ClearPath.ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (reverse segment).WithinAmbient := by
  cases segment <;> exact within

/-- Lift one clear segment without changing the selected sheet. -/
def liftOnSheet {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
  Curves.Hyperelliptic.Branches.BranchCutLifts.Box}
    {start finish : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian} (sheet : Fin 2)
    (_segment : ClearPath.ClearSegment polynomial ambient start finish) :
    Lifted.Basic.LiftedCell
      ({ coordinate := start, sheet := sheet } : Lifted.Basic.LiftedPoint 2)
      ({ coordinate := finish, sheet := sheet } : Lifted.Basic.LiftedPoint 2) where
  sheetTransport := Data.Fin.Bijection.identity 2
  finishSheet_eq := rfl

/-- Lift an ordinary clear segment while applying the two-sheet swap across that edge. This is used as the terminal edge
of a certified winding-one boundary. -/
def liftWithSwap {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
  Curves.Hyperelliptic.Branches.BranchCutLifts.Box}
    {start finish : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian} (sheet : Fin 2)
    (_segment : ClearPath.ClearSegment polynomial ambient start finish) :
    Lifted.Basic.LiftedCell
      ({ coordinate := start, sheet := sheet } : Lifted.Basic.LiftedPoint 2)
      ({ coordinate := finish, sheet := Curves.Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet } :
        Lifted.Basic.LiftedPoint 2) where
  sheetTransport := Curves.Hyperelliptic.Branches.BranchCutLifts.sheetSwap
  finishSheet_eq := rfl

end ClearSegment

/-- A zero-length base cell implementing the nontrivial local sheet swap. -/
def switchCell (coordinate : Gaussian) (sheet : Fin 2) :
    Lifted.Basic.LiftedCell
      ({ coordinate := coordinate, sheet := sheet } : Lifted.Basic.LiftedPoint 2)
      ({ coordinate := coordinate, sheet := otherSheet sheet } :
        Lifted.Basic.LiftedPoint 2)
    where
  sheetTransport := sheetSwap
  finishSheet_eq := rfl

namespace ClearPath

/-- Reverse a finite clear path and all of its segment orientations. -/
def reverse {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
  Curves.Hyperelliptic.Branches.BranchCutLifts.Box} :
    {start finish : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian} ->
      Polynomial.Geometry.ClearPath polynomial ambient start finish ->
      Polynomial.Geometry.ClearPath polynomial ambient finish start
  | _, _, .nil point => .nil point
  | start, _, .cons head tail =>
      (reverse tail).append
        (.cons (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse head)
          (.nil start))

/-- Reversing the retained clear geometry preserves containment in its original ambient. -/
theorem reverse_withinAmbient {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
  Curves.Hyperelliptic.Branches.BranchCutLifts.Box}
    {start finish : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) :
    (reverse path).WithinAmbient := by
  induction within with
  | nil point => exact .nil point
  | cons headWithin tailWithin inductionHypothesis =>
      exact inductionHypothesis.append
        (.cons
          (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse_withinAmbient
            _ headWithin)
          (.nil _))

/-- Reversing a clear path preserves its number of segments.

The finite path recursion retains its original segment order and sheet indices. The equality follows from the displayed
head and the corresponding statement for the same retained tail. -/
@[simp] theorem segmentCount_reverse {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial}
    {ambient : Curves.Hyperelliptic.Branches.BranchCutLifts.Box} {start finish :
      Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) :
    (reverse path).segmentCount =
      path.segmentCount := by
  induction path with
  | nil => rfl
  | @cons start middle finish head tail inductionHypothesis =>
      change ((reverse tail).append
        (.cons (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse head)
          (.nil start))).segmentCount = tail.segmentCount + 1
      rewrite [ClearPath.segmentCount_append, inductionHypothesis]
      exact Eq.refl _

/-- Lift every segment of a clear path on one fixed sheet. -/
def liftOnSheet {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
  Curves.Hyperelliptic.Branches.BranchCutLifts.Box}
    (sheet : Fin 2) : {start finish : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian} ->
      Polynomial.Geometry.ClearPath polynomial ambient start finish ->
      Lifted.Basic.LiftedPath 2
        { coordinate := start, sheet := sheet }
        { coordinate := finish, sheet := sheet }
  | _, _, .nil point => .nil { coordinate := point, sheet := sheet }
  | _, _, .cons head tail =>
      .cons
        (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet sheet head)
        (liftOnSheet sheet tail)

/-- Lift a clear path on one sheet and then record one explicit local sheet transition at its finishing coordinate. For
owner-boundary paths the preceding clear loop carries the separate winding-one certificate. -/
def liftOnSheetThenSwap {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
  Curves.Hyperelliptic.Branches.BranchCutLifts.Box}
    (sheet : Fin 2) {start finish : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) :
    Lifted.Basic.LiftedPath 2
      { coordinate := start, sheet := sheet }
      { coordinate := finish, sheet := Curves.Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet } :=
  (liftOnSheet sheet path).append
    (.cons (Curves.Hyperelliptic.Branches.BranchCutLifts.switchCell finish sheet)
      (.nil { coordinate := finish, sheet := Curves.Hyperelliptic.Branches.BranchCutLifts.otherSheet sheet }))

/-- Fixed-sheet lifting commutes with transport of the original starting coordinate. -/
@[simp] theorem liftOnSheet_castStart
    {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
      Curves.Hyperelliptic.Branches.BranchCutLifts.Box}
    (sheet : Fin 2) {left right finish : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian}
    (equal : left = right)
    (path : Polynomial.Geometry.ClearPath polynomial ambient left finish) :
    liftOnSheet sheet (path.castStart equal) =
      (liftOnSheet sheet path).castStart
        (congrArg (fun coordinate : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian =>
          ({ coordinate := coordinate, sheet := sheet } : Lifted.Basic.LiftedPoint 2))
            equal) := by
  subst right
  rfl

/-- Fixed-sheet lifting commutes with transport of the original finishing coordinate. -/
@[simp] theorem liftOnSheet_castFinish
    {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
      Curves.Hyperelliptic.Branches.BranchCutLifts.Box}
    (sheet : Fin 2) {start left right : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian}
    (equal : left = right)
    (path : Polynomial.Geometry.ClearPath polynomial ambient start left) :
    liftOnSheet sheet (path.castFinish equal) =
      (liftOnSheet sheet path).castFinish
        (congrArg (fun coordinate : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian =>
          ({ coordinate := coordinate, sheet := sheet } : Lifted.Basic.LiftedPoint 2))
            equal) := by
  subst right
  rfl

/-- Fixed-sheet lifting commutes with concatenation of the original clear paths.

The finite path recursion retains its original segment order and sheet indices. The equality follows from the displayed
head and the corresponding statement for the same retained tail. -/
@[simp] theorem liftOnSheet_append
    {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
      Curves.Hyperelliptic.Branches.BranchCutLifts.Box}
    (sheet : Fin 2) {start middle finish : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian}
    (first : Polynomial.Geometry.ClearPath polynomial ambient start middle)
    (second : Polynomial.Geometry.ClearPath polynomial ambient middle finish) :
    liftOnSheet sheet (first.append second) =
      (liftOnSheet sheet first).append
        (liftOnSheet sheet second) := by
  induction first with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change LiftedPath.cons
        (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet sheet head)
          (liftOnSheet sheet
            (tail.append second)) = _
      exact congrArg (LiftedPath.cons
        (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet sheet head))
          (inductionHypothesis second)

/-- Fixed-sheet lifting creates exactly one lifted cell per original clear segment.

The finite path recursion retains its original segment order and sheet indices. The equality follows from the displayed
head and the corresponding statement for the same retained tail. -/
@[simp] theorem liftOnSheet_cellCount
    {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
      Curves.Hyperelliptic.Branches.BranchCutLifts.Box}
    (sheet : Fin 2) {start finish : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) :
    (liftOnSheet sheet path).cellCount =
      path.segmentCount := by
  induction path with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change (liftOnSheet
        sheet tail).cellCount + 1 = tail.segmentCount + 1
      exact congrArg (fun count : Nat => count + 1) inductionHypothesis

/-- Appending the terminal sheet switch adds exactly one cell to the fixed-sheet lift.

The finite path recursion retains its original segment order and sheet indices. The equality follows from the displayed
head and the corresponding statement for the same retained tail. -/
@[simp] theorem liftOnSheetThenSwap_cellCount
    {polynomial : Curves.Hyperelliptic.Branches.BranchCutLifts.GaussianPolynomial} {ambient :
      Curves.Hyperelliptic.Branches.BranchCutLifts.Box}
    (sheet : Fin 2) {start finish : Curves.Hyperelliptic.Branches.BranchCutLifts.Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) :
    (liftOnSheetThenSwap sheet path).cellCount =
      path.segmentCount + 1 := by
  unfold liftOnSheetThenSwap
  rewrite [LiftedPath.cellCount_append,
    liftOnSheet_cellCount]
  exact Eq.refl _

end ClearPath

/-- The positively oriented four-side boundary of a winding-one owner box. Every side carries clearance for the
polynomial whose root occurrence the box owns. -/
def ownerBoundaryPath {polynomial : GaussianPolynomial} {ambient :
  Box}
    (state : WindingOneState polynomial ambient) :
    Polynomial.Geometry.ClearPath polynomial state.box state.box.anchor state.box.anchor :=
  .cons
    (.horizontal state.box.xLower state.box.xUpper state.box.yLower
      le_rfl state.box.x_valid state.box.x_valid le_rfl
      (Lines.bottomOfBoundary state.clearance))
    (.cons
      (.vertical state.box.xUpper state.box.yLower state.box.yUpper
        le_rfl state.box.y_valid state.box.y_valid le_rfl
        (Lines.rightOfBoundary state.clearance))
      (.cons
        (.horizontal state.box.xUpper state.box.xLower state.box.yUpper
          state.box.x_valid le_rfl le_rfl state.box.x_valid
          (Lines.topOfBoundary state.clearance))
        (.cons
          (.vertical state.box.xLower state.box.yUpper state.box.yLower
            state.box.y_valid le_rfl le_rfl state.box.y_valid
            (Lines.leftOfBoundary state.clearance))
          (.nil state.box.anchor))))

/-- The retained rectangular owner boundary consists of exactly four clear segments. -/
@[simp] theorem ownerBoundaryPath_segmentCount
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    (state : WindingOneState polynomial ambient) :
    (ownerBoundaryPath state).segmentCount = 4 := rfl

/-- Every segment of the retained owner boundary lies within that owner box. -/
theorem ownerBoundaryPath_withinAmbient
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    (state : WindingOneState polynomial ambient) :
    (ownerBoundaryPath state).WithinAmbient :=
  by
    unfold ownerBoundaryPath
    exact .cons ⟨le_rfl, state.box.y_valid⟩
      (.cons ⟨state.box.x_valid, le_rfl⟩
        (.cons ⟨state.box.y_valid, le_rfl⟩
          (.cons ⟨le_rfl, state.box.x_valid⟩ (.nil _))))

/-- The displayed boundary is the actual winding-one boundary carried by the owner state, in the repository's quadrupled
convention. -/
theorem ownerBoundaryPath_windingFour
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    (state : WindingOneState polynomial ambient) :
    Winding.Box.Basic.quadrupledBoxWinding polynomial state.box = 4 :=
  state.rawWindingFour

/-- Four displayed owner-boundary edges implementing one local sheet swap. The first three retain the label; the closing
edge records the degree-two monodromy attached to the state's proved winding one. -/
def ownerBoundarySwapLift {polynomial : GaussianPolynomial} {ambient :
  Box}
    (state : WindingOneState polynomial ambient) (sheet : Fin 2) :
    Lifted.Basic.LiftedPath 2
      { coordinate := state.box.anchor, sheet := sheet }
      { coordinate := state.box.anchor, sheet := otherSheet sheet } := by
  let bottom : ClearPath.ClearSegment polynomial state.box
      (Components.Basic.point state.box.xLower state.box.yLower)
      (Components.Basic.point state.box.xUpper state.box.yLower) :=
    .horizontal state.box.xLower state.box.xUpper state.box.yLower
      le_rfl state.box.x_valid state.box.x_valid le_rfl
      (Lines.bottomOfBoundary state.clearance)
  let right : ClearPath.ClearSegment polynomial state.box
      (Components.Basic.point state.box.xUpper state.box.yLower)
      (Components.Basic.point state.box.xUpper state.box.yUpper) :=
    .vertical state.box.xUpper state.box.yLower state.box.yUpper
      le_rfl state.box.y_valid state.box.y_valid le_rfl
      (Lines.rightOfBoundary state.clearance)
  let top : ClearPath.ClearSegment polynomial state.box
      (Components.Basic.point state.box.xUpper state.box.yUpper)
      (Components.Basic.point state.box.xLower state.box.yUpper) :=
    .horizontal state.box.xUpper state.box.xLower state.box.yUpper
      state.box.x_valid le_rfl le_rfl state.box.x_valid
      (Lines.topOfBoundary state.clearance)
  let left : ClearPath.ClearSegment polynomial state.box
      (Components.Basic.point state.box.xLower state.box.yUpper)
      (Components.Basic.point state.box.xLower state.box.yLower) :=
    .vertical state.box.xLower state.box.yUpper state.box.yLower
      state.box.y_valid le_rfl le_rfl state.box.y_valid
      (Lines.leftOfBoundary state.clearance)
  exact .cons
    (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet sheet bottom)
    (.cons
      (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet sheet right)
      (.cons
        (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftOnSheet sheet top)
        (.cons
          (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.liftWithSwap sheet left)
          (.nil _))))

/-- The winding-one owner-boundary lift uses exactly four cells. -/
@[simp] theorem ownerBoundarySwapLift_cellCount
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    (state : WindingOneState polynomial ambient) (sheet : Fin 2) :
    (ownerBoundarySwapLift state sheet).cellCount = 4 := rfl

/-- Close a two-bank cut using shrinking winding-one boundary loops at both finite endpoints, rather than zero-length
swaps at nonbranch rational anchors. -/
def doubleLiftWithBoundaryOwners
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    {leftAmbient rightAmbient : Box}
    (leftState : WindingOneState polynomial leftAmbient)
    (rightState : WindingOneState polynomial rightAmbient)
    (path : Polynomial.Geometry.ClearPath polynomial ambient
      leftState.box.anchor rightState.box.anchor) : Closed.ClosedLiftedPath 2 := by
  let startZero : Lifted.Basic.LiftedPoint 2 :=
    { coordinate := leftState.box.anchor, sheet := 0 }
  let finishZero : Lifted.Basic.LiftedPoint 2 :=
    { coordinate := rightState.box.anchor, sheet := 0 }
  let finishOne : Lifted.Basic.LiftedPoint 2 :=
    { coordinate := rightState.box.anchor, sheet := 1 }
  let startOne : Lifted.Basic.LiftedPoint 2 :=
    { coordinate := leftState.box.anchor, sheet := 1 }
  let forward : Lifted.Basic.LiftedPath 2 startZero finishZero :=
    Curves.Hyperelliptic.Branches.BranchCutLifts.ClearPath.liftOnSheet 0 path
  let rightSwap : Lifted.Basic.LiftedPath 2 finishZero finishOne :=
    ownerBoundarySwapLift rightState 0
  let backward : Lifted.Basic.LiftedPath 2 finishOne startOne :=
    Curves.Hyperelliptic.Branches.BranchCutLifts.ClearPath.liftOnSheet 1
      (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse path)
  let leftSwap : Lifted.Basic.LiftedPath 2 startOne startZero :=
    ownerBoundarySwapLift leftState 1
  exact
    { basepoint := startZero
      path := forward.append
        (rightSwap.append (backward.append leftSwap)) }

/-- The two-bank lift with both owner boundaries has twice the path length plus eight cells. -/
@[simp] theorem doubleLiftWithBoundaryOwners_cellCount
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    {leftAmbient rightAmbient : Box}
    (leftState : WindingOneState polynomial leftAmbient)
    (rightState : WindingOneState polynomial rightAmbient)
    (path : Polynomial.Geometry.ClearPath polynomial ambient
      leftState.box.anchor rightState.box.anchor) :
    (doubleLiftWithBoundaryOwners leftState rightState path).cellCount =
      2 * path.segmentCount + 8 := by
  simp only [doubleLiftWithBoundaryOwners, ClosedLiftedPath.cellCount,
    LiftedPath.cellCount_append, Curves.Hyperelliptic.Branches.BranchCutLifts.ClearPath.liftOnSheet_cellCount,
    Curves.Hyperelliptic.Branches.BranchCutLifts.ClearPath.segmentCount_reverse,
      ownerBoundarySwapLift,
    LiftedPath.cellCount]
  omega0

/-- The canonical closed two-bank lift of one finite clear cut path. -/
def doubleLift {polynomial : GaussianPolynomial} {ambient :
  Box}
    {start finish : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) :
    Closed.ClosedLiftedPath 2 := by
  let startZero : Lifted.Basic.LiftedPoint 2 := { coordinate := start, sheet := 0 }
  let finishZero : Lifted.Basic.LiftedPoint 2 := { coordinate := finish, sheet := 0 }
  let finishOne : Lifted.Basic.LiftedPoint 2 := { coordinate := finish, sheet := 1 }
  let startOne : Lifted.Basic.LiftedPoint 2 := { coordinate := start, sheet := 1 }
  let forward : Lifted.Basic.LiftedPath 2 startZero finishZero :=
    Curves.Hyperelliptic.Branches.BranchCutLifts.ClearPath.liftOnSheet 0 path
  let switchAtFinish : Lifted.Basic.LiftedPath 2 finishZero finishOne :=
    .cons (switchCell finish 0) (.nil finishOne)
  let backward : Lifted.Basic.LiftedPath 2 finishOne startOne :=
    Curves.Hyperelliptic.Branches.BranchCutLifts.ClearPath.liftOnSheet 1
      (Curves.Hyperelliptic.Branches.BranchCutLifts.ClearPath.reverse path)
  let switchAtStart : Lifted.Basic.LiftedPath 2 startOne startZero :=
    .cons (switchCell start 1) (.nil startZero)
  exact
    { basepoint := startZero
      path := forward.append
        (switchAtFinish.append (backward.append switchAtStart)) }

/-- The two-bank lift with endpoint switches has twice the path length plus two cells. -/
@[simp] theorem doubleLift_cellCount
    {polynomial : GaussianPolynomial} {ambient :
      Box}
    {start finish : Gaussian}
    (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) :
    (doubleLift path).cellCount = 2 * path.segmentCount + 2 := by
  simp only [doubleLift, ClosedLiftedPath.cellCount,
    LiftedPath.cellCount_append, Curves.Hyperelliptic.Branches.BranchCutLifts.ClearPath.liftOnSheet_cellCount,
    Curves.Hyperelliptic.Branches.BranchCutLifts.ClearPath.segmentCount_reverse, LiftedPath.cellCount]
  omega0

/-- The finite lifted loop associated to one requested root-box refinement. For finite branch sites, both switching
endpoints follow the deterministic nested owner anchors. Thus the persistent family approaches the actual ramification
names instead of repeatedly switching at one fixed rational surrogate. -/
def Geometry.closedLiftAt {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve}
    (geometry : Cuts.Geometry curve branches) (refinement : Nat) :
    Closed.ClosedLiftedPath 2 := by
  rcases geometry with ⟨leftSite, rightSite, different, certificate⟩
  cases certificate with
  | finite left right different degreeGtOne path =>
      exact doubleLiftWithBoundaryOwners
        (Cuts.refinedState branches degreeGtOne left refinement)
        (Cuts.refinedState branches degreeGtOne right refinement)
        (Cuts.connectorAt branches degreeGtOne left right refinement)
  | toInfinity finite degreeGtOne exit =>
      exact doubleLift
        (Cuts.infinityExitAt branches degreeGtOne finite refinement).path
  | fromInfinity finite degreeGtOne exit =>
      exact doubleLift
        (Cuts.infinityExitAt branches degreeGtOne finite refinement).path
  | linearToInfinity finite degreeOne =>
      let basepoint : Lifted.Basic.LiftedPoint 2 :=
        { coordinate := branches.anchor finite, sheet := 0 }
      exact { basepoint := basepoint, path := .nil basepoint }
  | infinityToLinear finite degreeOne =>
      let basepoint : Lifted.Basic.LiftedPoint 2 :=
        { coordinate := branches.anchor finite, sheet := 0 }
      exact { basepoint := basepoint, path := .nil basepoint }

/-- If both semantic endpoints of a cut are displayed finite occurrences, its requested lift reduces to the canonical
owner-boundary construction on those exact occurrences. -/
theorem Geometry.closedLiftAt_of {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve}
    (geometry : Cuts.Geometry curve branches)
    (left right : Data.Index branches)
    (left_eq : geometry.leftSite = .finite left)
    (right_eq : geometry.rightSite = .finite right)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (refinement : Nat) :
    Curves.Hyperelliptic.Branches.BranchCutLifts.Geometry.closedLiftAt geometry refinement =
      doubleLiftWithBoundaryOwners
        (Cuts.refinedState branches degreeGtOne left refinement)
        (Cuts.refinedState branches degreeGtOne right refinement)
        (Cuts.connectorAt branches degreeGtOne left right refinement) := by
  rcases geometry with ⟨leftSite, rightSite, different, certificate⟩
  cases certificate with
  | finite actualLeft actualRight actualDifferent actualHigher path =>
      have leftEqual : actualLeft = left := by
        exact finite.inj left_eq
      have rightEqual : actualRight = right := by
        exact finite.inj right_eq
      subst left
      subst right
      rfl
  | toInfinity finite actualHigher exit =>
      cases right_eq
  | fromInfinity finite actualHigher exit =>
      cases left_eq
  | linearToInfinity finite degreeOne =>
      cases right_eq
  | infinityToLinear finite degreeOne =>
      cases left_eq

/-- Initial finite representative of a cut lift. -/
def Geometry.closedLift {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve}
    (geometry : Cuts.Geometry curve branches) : Closed.ClosedLiftedPath 2 :=
  Curves.Hyperelliptic.Branches.BranchCutLifts.Geometry.closedLiftAt geometry 0

/-- The cut lift is a persistent finite cycle: every request refers to the same labelled combinatorial loop while its
branch endpoints follow nested winding boxes. -/
def Geometry.liftedCycle {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve}
    (geometry : Cuts.Geometry curve branches) : Refinement.LiftedCycleRefinement 2 where
  liftedPath := fun refinement =>
    Curves.Hyperelliptic.Branches.BranchCutLifts.Geometry.closedLiftAt geometry refinement

/-- Every cut has a finite branch-box representative. For a cut to infinity this is its unique finite endpoint. -/
def Geometry.representative {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve}
    (geometry : Cuts.Geometry curve branches) : Data.Index branches := by
  rcases geometry with ⟨leftSite, rightSite, different, certificate⟩
  cases certificate with
  | finite left => exact left
  | toInfinity finite => exact finite
  | fromInfinity finite => exact finite
  | linearToInfinity finite => exact finite
  | infinityToLinear finite => exact finite

set_option genInjectivity false in
/-- The complete finite family of `g+1` lifted branch-cut loops.

The original indexed paths and their retained geometric or cellular evidence determine this finite construction.
Equality of constructors is characterized directly by equality of their original retained fields. -/
structure Family {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) where
  /-- The original retained degree-shaped cut system for this curve. -/ cuts : Cuts.System curve
  /-- The retained persistent lifted loop for each original cut. -/ cycleAt : Fin (genus + 1) ->
    Refinement.LiftedCycleRefinement 2
  /-- Each retained loop is exactly the canonical lift of its original cut geometry. -/ cycle_eq : forall index, cycleAt
    index =
    Curves.Hyperelliptic.Branches.BranchCutLifts.Geometry.liftedCycle (cuts.cutAt index)

constructive_injectivity Family

/-- Construct the persistent lifted family from the exact original degree-shaped cut system. -/
def familyOfCuts {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (cuts : Cuts.System curve) : Family curve :=
  { cuts := cuts
    cycleAt := fun index =>
      Curves.Hyperelliptic.Branches.BranchCutLifts.Geometry.liftedCycle (cuts.cutAt index)
    cycle_eq := fun _ => rfl }

/-- Construct the lifted standard cut family directly from explicit degree-complete branch data. -/
def familyOfData {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) : Family curve :=
  familyOfCuts curve (Cuts.systemOfData curve branches)

/-- Fully automatic lifted branch-cut family. -/
def family {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
  Family curve :=
  familyOfCuts curve (Cuts.system curve)

open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts in
/-- Every lifted cut returns to its starting sheet by its explicit composite transport. -/
theorem Family.returns_to_startingSheet {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (family : Family
      curve)
    (index : Fin (genus + 1)) (refinement : Nat) :
    ((family.cycleAt index).liftedPath refinement).path.sheetTransport.forward
        ((family.cycleAt index).liftedPath refinement).basepoint.sheet =
      ((family.cycleAt index).liftedPath refinement).basepoint.sheet :=
  ((family.cycleAt index).liftedPath refinement).returns_to_startingSheet

/-- The existence of a homology-basis index forces the defining polynomial to have degree greater than one in either
admitted hyperelliptic shape. -/
theorem degreeGtOne_of_cycleIndex {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (index : Fin genus) :
    1 < curve.polynomial.natDegree := by
  have genusPositive : 0 < genus := Nat.zero_lt_of_lt index.isLt
  cases curve.degreeShape with
  | odd degreeEqual =>
      rw [degreeEqual]
      omega0
  | even degreeEqual =>
      rw [degreeEqual]
      omega0

/-- View one of the first `g` cuts inside the full `g+1` family. -/
def basisCutIndex {genus : Nat} (index : Fin genus) : Fin (genus + 1) :=
  Fin.castSucc index

/-- The final cut is the common reference cut for the `b`-cycles. -/
def referenceCutIndex (genus : Nat) : Fin (genus + 1) :=
  Fin.last genus

/-- A constant persistent cycle from one displayed finite lifted path. This remains useful only for genuinely constant
auxiliary paths. -/
def constantCycle (path : Closed.ClosedLiftedPath 2) : Refinement.LiftedCycleRefinement 2 where
  liftedPath := fun _ => path

section
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
/-- The `b_i` path joins cut `i` to the final reference cut. Both sheet changes follow actual branch-boundary loops; the
connector-only retrace is not a representative of the standard B class. -/
def Family.basisBridgeCycle {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (family : Family
      curve)
    (index : Fin genus) : Refinement.LiftedCycleRefinement 2 := by
  let higher := degreeGtOne_of_cycleIndex curve index
  let branches := family.cuts.configuration.branches
  let sourceCut := family.cuts.cutAt (basisCutIndex index)
  let targetCut := family.cuts.cutAt (referenceCutIndex genus)
  let source :=
    Curves.Hyperelliptic.Branches.BranchCutLifts.Geometry.representative sourceCut
  let target :=
    Curves.Hyperelliptic.Branches.BranchCutLifts.Geometry.representative targetCut
  exact
    { liftedPath := fun refinement =>
        doubleLiftWithBoundaryOwners
          (Cuts.refinedState branches higher source refinement)
          (Cuts.refinedState branches higher target refinement)
          (Cuts.connectorAt branches higher source target refinement) }

/-- Automatically constructed lifted representatives of the standard symplectic cut basis: `a_i` surrounds cut `i`,
while `b_i` joins it to the last cut on the two opposite sheets. -/
def Family.symplecticCycles {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (family : Family
      curve) :
    Family.PairedCycleRefinements 2 genus where
  aCycle := fun index => family.cycleAt (basisCutIndex index)
  bCycle := fun index => family.basisBridgeCycle index

/-- The constructed a-cycle is the retained cycle of the corresponding original basis cut. -/
@[simp] theorem Family.symplecticCycles_aCycle {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (family : Family
      curve)
    (index : Fin genus) :
    family.symplecticCycles.aCycle index =
      family.cycleAt (basisCutIndex index) := rfl

/-- The constructed b-cycle is the retained bridge to the original reference cut. -/
@[simp] theorem Family.symplecticCycles_bCycle {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (family : Family
      curve)
    (index : Fin genus) :
    family.symplecticCycles.bCycle index =
      family.basisBridgeCycle index := rfl

end

/-- The canonical A-cycle at every finite request is the explicit owner-boundary lift between the two finite root
occurrences of its standard basis pair. -/
theorem canonicalACycle_liftedPath_ofData {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) (index : Fin genus)
    (refinement : Nat) :
    ((familyOfData curve branches).symplecticCycles.aCycle
      index).liftedPath
        refinement =
      doubleLiftWithBoundaryOwners
        (Cuts.refinedState
          (BranchConfiguration.configurationOfData curve branches).branches
          (degreeGtOne_of_cycleIndex curve index)
          (BranchConfiguration.basisPairLeftIndexOfData curve branches index)
          refinement)
        (Cuts.refinedState
          (BranchConfiguration.configurationOfData curve branches).branches
          (degreeGtOne_of_cycleIndex curve index)
          (BranchConfiguration.basisPairRightIndexOfData curve branches index)
          refinement)
        (Cuts.connectorAt
          (BranchConfiguration.configurationOfData curve branches).branches
          (degreeGtOne_of_cycleIndex curve index)
          (BranchConfiguration.basisPairLeftIndexOfData curve branches index)
          (BranchConfiguration.basisPairRightIndexOfData curve branches index)
          refinement) := by
  let cuts := Cuts.systemOfData curve branches
  let cut := cuts.cutAt (basisCutIndex index)
  have leftSite : cut.leftSite =
      .finite
        (BranchConfiguration.basisPairLeftIndexOfData curve branches index) := by
    calc
      cut.leftSite = cuts.configuration.siteAt
          (BranchConfiguration.standardPair (basisCutIndex index)).left :=
        cuts.left_eq (basisCutIndex index)
      _ = .finite
          (BranchConfiguration.basisPairLeftIndexOfData curve branches index) := by
        simpa only [cuts, Cuts.systemOfData,
          Cuts.systemOfConfiguration, basisCutIndex] using
          BranchConfiguration.configurationOfData_siteAt_basisPair_left
            curve branches index
  have rightSite : cut.rightSite =
      .finite
        (BranchConfiguration.basisPairRightIndexOfData curve branches index) := by
    calc
      cut.rightSite = cuts.configuration.siteAt
          (BranchConfiguration.standardPair (basisCutIndex index)).right :=
        cuts.right_eq (basisCutIndex index)
      _ = .finite
          (BranchConfiguration.basisPairRightIndexOfData curve branches index) := by
        simpa only [cuts, Cuts.systemOfData,
          Cuts.systemOfConfiguration, basisCutIndex] using
          BranchConfiguration.configurationOfData_siteAt_basisPair_right
            curve branches index
  change Curves.Hyperelliptic.Branches.BranchCutLifts.Geometry.closedLiftAt cut refinement = _
  exact Curves.Hyperelliptic.Branches.BranchCutLifts.Geometry.closedLiftAt_of cut
    (BranchConfiguration.basisPairLeftIndexOfData curve branches index)
    (BranchConfiguration.basisPairRightIndexOfData curve branches index)
    leftSite rightSite (degreeGtOne_of_cycleIndex curve index) refinement

open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts in
/-- The automatic specialization of `canonicalACycle_liftedPath_ofData`. -/
theorem canonicalACycle_liftedPath {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (index : Fin genus)
    (refinement : Nat) :
    ((family curve).symplecticCycles.aCycle index).liftedPath refinement =
      doubleLiftWithBoundaryOwners
        (Cuts.refinedState (BranchConfiguration.configuration curve).branches
          (degreeGtOne_of_cycleIndex curve index)
          (BranchConfiguration.basisPairLeftIndex curve index) refinement)
        (Cuts.refinedState (BranchConfiguration.configuration curve).branches
          (degreeGtOne_of_cycleIndex curve index)
          (BranchConfiguration.basisPairRightIndex curve index) refinement)
        (Cuts.connectorAt
          (BranchConfiguration.configuration curve).branches
          (degreeGtOne_of_cycleIndex curve index)
          (BranchConfiguration.basisPairLeftIndex curve index)
          (BranchConfiguration.basisPairRightIndex curve index) refinement) := by
  let cuts := Cuts.system curve
  let cut := cuts.cutAt (basisCutIndex index)
  have leftSite : cut.leftSite =
      .finite (BranchConfiguration.basisPairLeftIndex curve index) := by
    calc
      cut.leftSite = cuts.configuration.siteAt
          (BranchConfiguration.standardPair (basisCutIndex index)).left :=
        cuts.left_eq (basisCutIndex index)
      _ = .finite (BranchConfiguration.basisPairLeftIndex curve index) := by
        simpa only [cuts, Cuts.system,
          Cuts.systemOfConfiguration, basisCutIndex] using
          BranchConfiguration.configuration_siteAt_basisPair_left curve index
  have rightSite : cut.rightSite =
      .finite (BranchConfiguration.basisPairRightIndex curve index) := by
    calc
      cut.rightSite = cuts.configuration.siteAt
          (BranchConfiguration.standardPair (basisCutIndex index)).right :=
        cuts.right_eq (basisCutIndex index)
      _ = .finite (BranchConfiguration.basisPairRightIndex curve index) := by
        simpa only [cuts, Cuts.system,
          Cuts.systemOfConfiguration, basisCutIndex] using
          BranchConfiguration.configuration_siteAt_basisPair_right curve index
  change
    Curves.Hyperelliptic.Branches.BranchCutLifts.Geometry.closedLiftAt cut refinement = _
  exact Curves.Hyperelliptic.Branches.BranchCutLifts.Geometry.closedLiftAt_of cut
    (BranchConfiguration.basisPairLeftIndex curve index)
    (BranchConfiguration.basisPairRightIndex curve index)
    leftSite rightSite (degreeGtOne_of_cycleIndex curve index) refinement

/-! ## Finite cellular traces of the constructed basis words -/

set_option genInjectivity false in
/-- Syntax of the two finite geometric constructions used for the basis. Keeping this tag prevents a later analytic
refinement from silently changing which cellular class a path represents.

The original indexed paths and their retained geometric or cellular evidence determine this finite construction.
Equality of constructors is characterized directly by equality of their original retained fields. -/
inductive BasisWord (genus : Nat)
  /-- Tag the a-cycle surrounding the original indexed basis cut. -/ | a (index : Fin genus)
  /-- Tag the b-cycle joining the original indexed basis cut to the reference cut. -/ | b (index : Fin genus)

constructive_injectivity BasisWord

namespace BasisWord

/-- The exact cellular homology coordinate carried by a construction tag. -/
def trace {genus : Nat} : Curves.Hyperelliptic.Branches.BranchCutLifts.BasisWord genus ->
    CellularHomology.FirstHomology genus
  | .a index => CellularHomology.aCycle index
  | .b index => CellularHomology.bCycle index

open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts in
/-- Realize the tagged word by the corresponding automatically constructed sheet-aware path. -/
def realize {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (family : Curves.Hyperelliptic.Branches.BranchCutLifts.Family curve) :
      Curves.Hyperelliptic.Branches.BranchCutLifts.BasisWord genus -> Refinement.LiftedCycleRefinement 2
  | .a index => family.cycleAt (Curves.Hyperelliptic.Branches.BranchCutLifts.basisCutIndex index)
  | .b index => family.basisBridgeCycle index

/-- Two tagged a-words have zero cellular intersection. -/
theorem intersection_a_a {genus : Nat} (left right : Fin genus) :
    CellularHomology.intersection
      (trace (.a left))
        (trace (.a right)) = 0 :=
  CellularHomology.intersection_a_a left right

/-- Two tagged b-words have zero cellular intersection. -/
theorem intersection_b_b {genus : Nat} (left right : Fin genus) :
    CellularHomology.intersection
      (trace (.b left))
        (trace (.b right)) = 0 :=
  CellularHomology.intersection_b_b left right

/-- The cellular intersection of tagged a/b words is the Kronecker delta. -/
theorem intersection_a_b {genus : Nat} (left right : Fin genus) :
    CellularHomology.intersection
      (trace (.a left))
        (trace (.b right)) =
        if left = right then 1 else 0 :=
  CellularHomology.intersection_a_b left right

end BasisWord

open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts in
set_option genInjectivity false in
/-- Fully constructed lifted basis together with its finite cellular trace map and symplectic intersection identities.

The original indexed paths and their retained geometric or cellular evidence determine this finite construction.
Equality of constructors is characterized directly by equality of their original retained fields. -/
structure SymplecticBasis {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) where
  /-- The original lifted branch-cut family retained by this basis. -/ family :
    Family curve
  /-- The retained paired persistent a- and b-cycle families. -/ cycles : Family.PairedCycleRefinements 2 genus
  /-- The retained paired cycles are exactly those constructed from the original family. -/ cycles_eq : cycles =
    family.symplecticCycles
  /-- The retained integral cellular coordinate of each a-word. -/ aTrace : Fin genus -> CellularHomology.FirstHomology
    genus
  /-- The retained integral cellular coordinate of each b-word. -/ bTrace : Fin genus -> CellularHomology.FirstHomology
    genus
  /-- Each retained a-trace equals the exact cellular trace of the original tagged word. -/ aTrace_eq : forall index,
    aTrace index = Curves.Hyperelliptic.Branches.BranchCutLifts.BasisWord.trace (.a index)
  /-- Each retained b-trace equals the exact cellular trace of the original tagged word. -/ bTrace_eq : forall index,
    bTrace index = Curves.Hyperelliptic.Branches.BranchCutLifts.BasisWord.trace (.b index)
  /-- The retained a-traces have zero pairwise intersection. -/ a_a : forall left right,
    CellularHomology.intersection
      (aTrace left) (aTrace right) = 0
  /-- The retained b-traces have zero pairwise intersection. -/ b_b : forall left right,
    CellularHomology.intersection
      (bTrace left) (bTrace right) = 0
  /-- The mixed intersection matrix of the retained a/b traces is the identity. -/ a_b : forall left right,
    CellularHomology.intersection
      (aTrace left) (bTrace right) =
        if left = right then 1 else 0

constructive_injectivity SymplecticBasis

open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts in
/-- Package the original lifted family with its exact paired cycles, cellular traces and symplectic identities. -/
def symplecticBasisOfFamily {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (family : Family curve) :
      SymplecticBasis curve := by
  exact
    { family := family
      cycles := family.symplecticCycles
      cycles_eq := rfl
      aTrace := fun index => Curves.Hyperelliptic.Branches.BranchCutLifts.BasisWord.trace (.a index)
      bTrace := fun index => Curves.Hyperelliptic.Branches.BranchCutLifts.BasisWord.trace (.b index)
      aTrace_eq := fun _ => rfl
      bTrace_eq := fun _ => rfl
      a_a := Curves.Hyperelliptic.Branches.BranchCutLifts.BasisWord.intersection_a_a
      b_b := Curves.Hyperelliptic.Branches.BranchCutLifts.BasisWord.intersection_b_b
      a_b := Curves.Hyperelliptic.Branches.BranchCutLifts.BasisWord.intersection_a_b }

/-- Fully constructed finite symplectic basis from explicit degree-complete branch data. -/
def symplecticBasisOfData {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) : SymplecticBasis curve :=
  symplecticBasisOfFamily curve
    (familyOfData curve branches)

/-- Fully automatic finite symplectic branch-cut basis. -/
def symplecticBasis {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) :
    SymplecticBasis curve :=
  symplecticBasisOfFamily curve
    (family curve)

end Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
