module

public import Purelib.RootIsolation.Subdivision.Raw.Grid.Elimination
public import Purelib.RootIsolation.Subdivision.Raw.Selection
import Purelib.RootIsolation.Subdivision.Raw.Selection.Replay
public import Purelib.RootIsolation.State.WindingOne.Raw
public import Purelib.RootIsolation.FTA.Squarefree.Input
public import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
public import Purelib.RootIsolation.Refinement.Basic
public import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Purelib.Polynomial.Elimination.Axis.Cuts
import Purelib.Polynomial.Winding.Box.Nonnegative.Squarefree
import Purelib.Polynomial.Winding.Box.Region
import Purelib.Polynomial.Winding.Box.ProtectedBoundary
public import Purelib.Polynomial.Clearance.Box.ProtectedRadius
public import Purelib.Approximation.Rational.Contraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Int.Order
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Winding-one subdivision with retained ambient lines

Central eliminant-safe cuts preserve exact winding four by finite additivity
and nonnegative child windings. Each selected child retains the original
ambient line certificates on inherited sides and the two newly constructed
cut certificates. Bounded refinement stops as soon as strict containment and
requested accuracy hold; protected-boundary separation supplies its finite
terminal guarantee. No Newton center is part of the executable construction.
-/

public section

namespace Purelib.RootIsolation.Subdivision.WindingOne

open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Basic (VerticalLineClearance HorizontalLineClearance)

open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Data.Rat.Fraction.Order

variable {p : CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}

/-- The original first nonzero child of a winding-one grid has winding exactly four.

Nonnegativity and four-child additivity bound its winding above by four.
Positive-region counting supplies the lower bound using the same child as
both displayed regions. All extraction in that counting argument is proof data.
-/
private theorem selected_winding_four (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient) (grid : Raw.Grid.RawFourGrid current.raw) :
    Winding.Box.Basic.quadrupledBoxWinding p (Raw.Selection.firstNonzeroChild grid).box = 4 := by
  have lowerLeft := Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
    input.degreeAtLeastTwo input.squarefree elimination
    grid.lowerLeft.refinesAmbient grid.lowerLeft.proper grid.lowerLeft.clearance
  have upperLeft := Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
    input.degreeAtLeastTwo input.squarefree elimination
    grid.upperLeft.refinesAmbient grid.upperLeft.proper grid.upperLeft.clearance
  have lowerRight := Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
    input.degreeAtLeastTwo input.squarefree elimination
    grid.lowerRight.refinesAmbient grid.lowerRight.proper grid.lowerRight.clearance
  have upperRight := Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
    input.degreeAtLeastTwo input.squarefree elimination
    grid.upperRight.refinesAmbient grid.upperRight.proper grid.upperRight.clearance
  have total := grid.additive
  change Winding.Box.Basic.quadrupledBoxWinding p current.box = _ at total
  rewrite [current.rawWindingFour] at total
  have lowerLeftUpper : Winding.Box.Basic.quadrupledBoxWinding p grid.lowerLeft.box ≤ 4 := by omega0
  have upperLeftUpper : Winding.Box.Basic.quadrupledBoxWinding p grid.upperLeft.box ≤ 4 := by omega0
  have lowerRightUpper : Winding.Box.Basic.quadrupledBoxWinding p grid.lowerRight.box ≤ 4 := by omega0
  have upperRightUpper : Winding.Box.Basic.quadrupledBoxWinding p grid.upperRight.box ≤ 4 := by omega0
  have upper : Winding.Box.Basic.quadrupledBoxWinding p
      (Raw.Selection.firstNonzeroChild grid).box ≤ 4 := by
    by_cases first : Winding.Box.Basic.quadrupledBoxWinding p grid.lowerLeft.box ≠ 0
    · rewrite [Raw.Selection.firstNonzeroChild, if_pos first]
      exact lowerLeftUpper
    by_cases second : Winding.Box.Basic.quadrupledBoxWinding p grid.upperLeft.box ≠ 0
    · rewrite [Raw.Selection.firstNonzeroChild, if_neg first, if_pos second]
      exact upperLeftUpper
    by_cases third : Winding.Box.Basic.quadrupledBoxWinding p grid.lowerRight.box ≠ 0
    · rewrite [Raw.Selection.firstNonzeroChild, if_neg first, if_neg second, if_pos third]
      exact lowerRightUpper
    · rewrite [Raw.Selection.firstNonzeroChild, if_neg first, if_neg second, if_neg third]
      exact upperRightUpper
  let child := Raw.Selection.firstNonzeroChild grid
  have nonnegative := Winding.Box.Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative
    input.degreeAtLeastTwo input.squarefree elimination child.refinesAmbient child.proper child.clearance
  have nonzero := Raw.Selection.firstNonzeroChild_rawWinding_ne grid
  have positive : 0 < Winding.Box.Basic.quadrupledBoxWinding p child.box := by
    change Winding.Box.Basic.quadrupledBoxWinding p child.box ≠ 0 at nonzero
    omega0
  let region : Clearance.Box.Region.ClearRegion p ambient :=
    ⟨child.box, child.refinesAmbient, child.proper, child.clearance⟩
  have lower := Winding.Box.Region.winding_ge_four_of_positive_region input region region positive
    (Box.refines_refl child.box)
  change 4 ≤ Winding.Box.Basic.quadrupledBoxWinding p child.box at lower
  change Winding.Box.Basic.quadrupledBoxWinding p child.box ≤ 4 at upper
  change Winding.Box.Basic.quadrupledBoxWinding p child.box = 4
  omega0

set_option genInjectivity false in
/-- One ordered subdivision step with its actual grid, selected child and ambient-line cache.

The original winding-one parent indexes the retained four-grid. The chosen
state has the exact first-nonzero child's box, preserves the fixed ambient,
and carries the same four-ninths contraction as that actual grid child.
-/
structure Step (current : WindingOneState p ambient) where
  /-- The actual clear, contracting four-child grid consumed by this step. -/ grid : Raw.Grid.RawFourGrid current.raw
  /-- The retained first-nonzero winding-one child with full ambient-line certificates. -/ state :
    WindingOneState p ambient
  /-- The selected state's box is the original ordered first-nonzero grid child. -/ selected :
    state.box = (Raw.Selection.firstNonzeroChild grid).box
  /-- The retained child refines its original immediate parent. -/ nested : state.box.Refines current.box
  /-- The selected child's squared diagonal contracts by four ninths. -/ contracts :
    state.box.diagonalSq ≤ (4 / 9 : Fraction.Rational) * current.box.diagonalSq

constructive_injectivity Step

/-- Assemble the selected child using its original retained ambient-side certificates. -/
private def assemble (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound) (current : WindingOneState p ambient)
    (grid : Raw.Grid.RawFourGrid current.raw)
    (child : Clearance.Box.Refinement.Contracting.RawChild p ambient current.box)
    (same : child = Raw.Selection.firstNonzeroChild grid)
    (left : VerticalLineClearance p ambient child.box.xLower)
    (right : VerticalLineClearance p ambient child.box.xUpper)
    (bottom : HorizontalLineClearance p ambient child.box.yLower)
    (top : HorizontalLineClearance p ambient child.box.yUpper) : Step current :=
  { grid := grid
    state :=
      { box := child.box
        refinesAmbient := child.refinesAmbient
        proper := child.proper
        clearance := child.clearance
        rawWindingFour := by
          rewrite [same]
          exact selected_winding_four input elimination current grid
        ambientLeftClearance := left
        ambientRightClearance := right
        ambientBottomClearance := bottom
        ambientTopClearance := top }
    selected := congrArg (fun value => value.box) same
    nested := child.refinesParent
    contracts := child.contracts }

set_option genInjectivity false in
/-- The two retained canonical safe coordinates on the original parent and elimination certificate.

Only the coordinate values are executable data. Their readbacks identify the
original ordered safe-cut searches, allowing the same values to index retained
full-ambient line certificates without repeating either search.
-/
structure Coordinates (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient) where
  /-- The actual retained vertical cut coordinate. -/ x : Fraction.Rational
  /-- The actual retained horizontal cut coordinate. -/ y : Fraction.Rational
  /-- The vertical value is the original canonical safe coordinate. -/ x_eq :
    x = Elimination.Axis.Cuts.verticalSafeCoordinate elimination current.box current.proper
  /-- The horizontal value is the original canonical safe coordinate. -/ y_eq :
    y = Elimination.Axis.Cuts.horizontalSafeCoordinate elimination current.box current.proper

constructive_injectivity Coordinates

/-- Compute and retain the original vertical and horizontal safe coordinates once. -/
@[expose] def coordinates (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient) : Coordinates elimination current :=
  ⟨Elimination.Axis.Cuts.verticalSafeCoordinate elimination current.box current.proper,
    Elimination.Axis.Cuts.horizontalSafeCoordinate elimination current.box current.proper, rfl, rfl⟩

/-- Exact readback of the retained original vertical safe-coordinate search. -/
theorem coordinates_x (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient) :
    (coordinates elimination current).x =
      Elimination.Axis.Cuts.verticalSafeCoordinate elimination current.box current.proper := rfl

/-- Exact readback of the retained original horizontal safe-coordinate search. -/
theorem coordinates_y (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient) :
    (coordinates elimination current).y =
      Elimination.Axis.Cuts.horizontalSafeCoordinate elimination current.box current.proper := rfl

/-- The retained vertical coordinate is clear and strictly inside the original parent. -/
theorem Coordinates.vertical_spec {elimination : AxisEliminationCertificate p degreeBound}
    {current : WindingOneState p ambient} (cuts : Coordinates elimination current) :
    elimination.vertical.eval cuts.x ≠ 0 ∧
      current.box.xLower < cuts.x ∧ cuts.x < current.box.xUpper := by
  rewrite [cuts.x_eq]
  exact Elimination.Axis.Cuts.verticalSafeCoordinate_spec elimination current.box current.proper

/-- The retained horizontal coordinate is clear and strictly inside the original parent. -/
theorem Coordinates.horizontal_spec {elimination : AxisEliminationCertificate p degreeBound}
    {current : WindingOneState p ambient} (cuts : Coordinates elimination current) :
    elimination.horizontal.eval cuts.y ≠ 0 ∧
      current.box.yLower < cuts.y ∧ cuts.y < current.box.yUpper := by
  rewrite [cuts.y_eq]
  exact Elimination.Axis.Cuts.horizontalSafeCoordinate_spec elimination current.box current.proper

/-- Every retained canonical coordinate pair equals the original computed pair completely. -/
theorem Coordinates.eq_coordinates {elimination : AxisEliminationCertificate p degreeBound}
    {current : WindingOneState p ambient} (cuts : Coordinates elimination current) :
    cuts = coordinates elimination current := by
  rcases cuts with ⟨x, y, xEq, yEq⟩
  cases xEq
  cases yEq
  rfl

/-- Assemble the retained four-child grid from canonical coordinates and full ambient lines.

Only restrictions of the supplied line certificates enter the child boundaries.
The actual grid can be retained while its three winding readbacks are loaded.
-/
def gridFromLines (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOneState p ambient) (coordinates : Coordinates elimination current)
    (vertical : VerticalLineClearance p ambient coordinates.x)
    (horizontal : HorizontalLineClearance p ambient coordinates.y) : Raw.Grid.RawFourGrid current.raw := by
  have xSpec := coordinates.vertical_spec
  have ySpec := coordinates.horizontal_spec
  let cuts : Clearance.Box.Grid.Four.Basic.ClearFourGrid p current.box :=
    { xCut := coordinates.x
      yCut := coordinates.y
      xInside := ⟨xSpec.2.1.le, xSpec.2.2.le⟩
      yInside := ⟨ySpec.2.1.le, ySpec.2.2.le⟩
      verticalClearance := vertical.restrict current.refinesAmbient
      horizontalClearance := horizontal.restrict current.refinesAmbient }
  exact Raw.Grid.Elimination.ofClearFourGrid elimination current.raw cuts
    coordinates.x_eq coordinates.y_eq

/-- Assemble the ordered subdivision step from retained coordinates and full ambient line certificates.

The supplied certificates remain indexed by the fixed original ambient.
Their restrictions feed the same four-grid; selected inherited sides retain
the original parent caches and the new sides retain these exact supplied lines.
No safe-coordinate search or line-clearance producer executes in this assembly.
-/
def fromLines (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound) (current : WindingOneState p ambient)
    (coordinates : Coordinates elimination current)
    (vertical : VerticalLineClearance p ambient coordinates.x)
    (horizontal : HorizontalLineClearance p ambient coordinates.y) : Step current := by
  let grid := gridFromLines elimination current coordinates vertical horizontal
  if lowerLeft : Winding.Box.Basic.quadrupledBoxWinding p grid.lowerLeft.box ≠ 0 then
    exact assemble input elimination current grid grid.lowerLeft
      (by unfold Raw.Selection.firstNonzeroChild; rewrite [if_pos lowerLeft]; rfl)
      current.ambientLeftClearance vertical current.ambientBottomClearance horizontal
  else if upperLeft : Winding.Box.Basic.quadrupledBoxWinding p grid.upperLeft.box ≠ 0 then
    exact assemble input elimination current grid grid.upperLeft
      (by unfold Raw.Selection.firstNonzeroChild; rewrite [if_neg lowerLeft, if_pos upperLeft]; rfl)
      current.ambientLeftClearance vertical horizontal current.ambientTopClearance
  else if lowerRight : Winding.Box.Basic.quadrupledBoxWinding p grid.lowerRight.box ≠ 0 then
    exact assemble input elimination current grid grid.lowerRight
      (by unfold Raw.Selection.firstNonzeroChild
          rewrite [if_neg lowerLeft, if_neg upperLeft, if_pos lowerRight]; rfl)
      vertical current.ambientRightClearance current.ambientBottomClearance horizontal
  else
    exact assemble input elimination current grid grid.upperRight
      (by unfold Raw.Selection.firstNonzeroChild
          rewrite [if_neg lowerLeft, if_neg upperLeft, if_neg lowerRight]; rfl)
      vertical current.ambientRightClearance horizontal current.ambientTopClearance

/-- Restore the selected winding-one step from three exact retained scalar readings of one actual grid.

The original replay selector identifies the ordered supplied-reading branch. The same grid,
full ambient cut lines and inherited parent-side caches supply the resulting
state; no winding, coordinate or clearance producer executes here.
-/
def fromReadings (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound) (current : WindingOneState p ambient)
    (coordinates : Coordinates elimination current)
    (vertical : VerticalLineClearance p ambient coordinates.x)
    (horizontal : HorizontalLineClearance p ambient coordinates.y)
    (grid : Raw.Grid.RawFourGrid current.raw)
    (same : grid = gridFromLines elimination current coordinates vertical horizontal)
    (lowerLeft : {value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.lowerLeft.box})
    (upperLeft : {value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.upperLeft.box})
    (lowerRight : {value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.lowerRight.box}) :
    Step current := by
  if first : lowerLeft.val ≠ 0 then
    exact assemble input elimination current grid grid.lowerLeft
      (by
        have selected := Raw.Selection.Replay.choose_eq grid lowerLeft upperLeft lowerRight
        unfold Raw.Selection.Replay.choose at selected
        rewrite [if_pos first] at selected
        exact selected)
      ((show grid.lowerLeft.box.xLower = current.box.xLower by rewrite [same]; rfl).symm ▸ current.ambientLeftClearance)
      ((show grid.lowerLeft.box.xUpper = coordinates.x by rewrite [same]; rfl).symm ▸ vertical)
      ((show grid.lowerLeft.box.yLower = current.box.yLower by rewrite [same]; rfl).symm ▸
        current.ambientBottomClearance)
      ((show grid.lowerLeft.box.yUpper = coordinates.y by rewrite [same]; rfl).symm ▸ horizontal)
  else if second : upperLeft.val ≠ 0 then
    exact assemble input elimination current grid grid.upperLeft
      (by
        have selected := Raw.Selection.Replay.choose_eq grid lowerLeft upperLeft lowerRight
        unfold Raw.Selection.Replay.choose at selected
        rewrite [if_neg first, if_pos second] at selected
        exact selected)
      ((show grid.upperLeft.box.xLower = current.box.xLower by rewrite [same]; rfl).symm ▸ current.ambientLeftClearance)
      ((show grid.upperLeft.box.xUpper = coordinates.x by rewrite [same]; rfl).symm ▸ vertical)
      ((show grid.upperLeft.box.yLower = coordinates.y by rewrite [same]; rfl).symm ▸ horizontal)
      ((show grid.upperLeft.box.yUpper = current.box.yUpper by rewrite [same]; rfl).symm ▸ current.ambientTopClearance)
  else if third : lowerRight.val ≠ 0 then
    exact assemble input elimination current grid grid.lowerRight
      (by
        have selected := Raw.Selection.Replay.choose_eq grid lowerLeft upperLeft lowerRight
        unfold Raw.Selection.Replay.choose at selected
        rewrite [if_neg first, if_neg second, if_pos third] at selected
        exact selected)
      ((show grid.lowerRight.box.xLower = coordinates.x by rewrite [same]; rfl).symm ▸ vertical)
      ((show grid.lowerRight.box.xUpper = current.box.xUpper by rewrite [same]; rfl).symm ▸
        current.ambientRightClearance)
      ((show grid.lowerRight.box.yLower = current.box.yLower by rewrite [same]; rfl).symm ▸
        current.ambientBottomClearance)
      ((show grid.lowerRight.box.yUpper = coordinates.y by rewrite [same]; rfl).symm ▸ horizontal)
  else
    exact assemble input elimination current grid grid.upperRight
      (by
        have selected := Raw.Selection.Replay.choose_eq grid lowerLeft upperLeft lowerRight
        unfold Raw.Selection.Replay.choose at selected
        rewrite [if_neg first, if_neg second, if_neg third] at selected
        exact selected)
      ((show grid.upperRight.box.xLower = coordinates.x by rewrite [same]; rfl).symm ▸ vertical)
      ((show grid.upperRight.box.xUpper = current.box.xUpper by rewrite [same]; rfl).symm ▸
        current.ambientRightClearance)
      ((show grid.upperRight.box.yLower = coordinates.y by rewrite [same]; rfl).symm ▸ horizontal)
      ((show grid.upperRight.box.yUpper = current.box.yUpper by rewrite [same]; rfl).symm ▸ current.ambientTopClearance)

/-- Exact retained readings recover the complete original supplied-line step. -/
theorem fromReadings_eq_fromLines (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound) (current : WindingOneState p ambient)
    (coordinates : Coordinates elimination current)
    (vertical : VerticalLineClearance p ambient coordinates.x)
    (horizontal : HorizontalLineClearance p ambient coordinates.y)
    (grid : Raw.Grid.RawFourGrid current.raw)
    (same : grid = gridFromLines elimination current coordinates vertical horizontal)
    (lowerLeft : {value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.lowerLeft.box})
    (upperLeft : {value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.upperLeft.box})
    (lowerRight : {value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p grid.lowerRight.box}) :
    fromReadings input elimination current coordinates vertical horizontal grid same lowerLeft upperLeft lowerRight =
      fromLines input elimination current coordinates vertical horizontal := by
  cases same
  rcases lowerLeft with ⟨first, firstEq⟩
  rcases upperLeft with ⟨second, secondEq⟩
  rcases lowerRight with ⟨third, thirdEq⟩
  cases firstEq
  cases secondEq
  cases thirdEq
  rfl

/-- Execute one central safe-cut step while preserving the original full ambient-line caches.

The two cut coordinates and their two full ambient clearances are computed
once. Assembly consumes those same values and certificates, preserving the
original ordered first-nonzero selection and the complete returned step.
-/
def refineOnce (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound) (current : WindingOneState p ambient)
    (clearances : AxisClearances elimination := .canonical elimination) :
    Step current :=
  let cuts := coordinates elimination current
  let vertical := clearances.vertical ambient cuts.x cuts.vertical_spec.1
  let horizontal := clearances.horizontal ambient cuts.y cuts.horizontal_spec.1
  fromLines input elimination current cuts vertical horizontal

/-- Provider-equal supplied ambient lines reproduce the complete original ordered step.

The equality retains its actual four-grid, chosen state, boundary values and
all ambient-side caches. It applies to every retained canonical coordinate
view; no equality of bounds alone substitutes for equality of line certificates.
-/
theorem fromLines_eq_refineOnce (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound) (current : WindingOneState p ambient)
    (cuts : Coordinates elimination current)
    (clearances : AxisClearances elimination)
    (vertical : VerticalLineClearance p ambient cuts.x)
    (horizontal : HorizontalLineClearance p ambient cuts.y)
    (verticalEq : vertical = clearances.vertical ambient cuts.x cuts.vertical_spec.1)
    (horizontalEq : horizontal = clearances.horizontal ambient cuts.y cuts.horizontal_spec.1) :
    fromLines input elimination current cuts vertical horizontal = refineOnce input elimination current clearances := by
  have same := cuts.eq_coordinates
  cases same
  cases verticalEq
  cases horizontalEq
  rfl

/-- Provider-equal retained ambient lines preserve the full selected winding-one state. -/
theorem fromLines_state_eq_refineOnce (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound) (current : WindingOneState p ambient)
    (cuts : Coordinates elimination current)
    (clearances : AxisClearances elimination)
    (vertical : VerticalLineClearance p ambient cuts.x)
    (horizontal : HorizontalLineClearance p ambient cuts.y)
    (verticalEq : vertical = clearances.vertical ambient cuts.x cuts.vertical_spec.1)
    (horizontalEq : horizontal = clearances.horizontal ambient cuts.y cuts.horizontal_spec.1) :
    (fromLines input elimination current cuts vertical horizontal).state =
      (refineOnce input elimination current clearances).state :=
  congrArg (fun step => step.state)
    (fromLines_eq_refineOnce input elimination current cuts clearances vertical horizontal verticalEq horizontalEq)

/-- Both original stopping obligations for the actual displayed subdivision state. -/
@[expose] def Accepted (origin : WindingOneState p ambient) (epsilon : Fraction.Rational)
    (current : WindingOneState p ambient) : Prop :=
  current.box.StrictInterior origin.box ∧ current.box.diagonalSq ≤ epsilon ^ 2

/-- Decide the same strict-interior and squared-diagonal predicates used by the track contract. -/
instance (origin : WindingOneState p ambient) (epsilon : Fraction.Rational)
    (current : WindingOneState p ambient) : Decidable (Accepted origin epsilon current) := by
  unfold Accepted
  infer_instance

set_option genInjectivity false in
/-- The actual finite ordered subdivision history before the first accepted state.

Each edge retains its four-child grid, selected winding-one state and inherited
ambient-line certificates. Every preceding state fails the original combined
strictness and accuracy condition; no rejected state is treated as an obstruction.
-/
inductive Trace (origin : WindingOneState p ambient) (epsilon : Fraction.Rational) :
    WindingOneState p ambient → WindingOneState p ambient → Type where
  /-- Stop at the current displayed state without performing another subdivision. -/
  | done (current : WindingOneState p ambient) : Trace origin epsilon current current
  /-- Retain one actual ordered step after the current state failed the stopping condition. -/
  | advance {current final : WindingOneState p ambient} (step : Step current)
      (missed : ¬ Accepted origin epsilon current)
      (tail : Trace origin epsilon step.state final) : Trace origin epsilon current final

constructive_injectivity Trace

/-- Count the actual retained subdivision edges in a completed history. -/
@[expose] def Trace.length {origin : WindingOneState p ambient} {epsilon : Fraction.Rational}
    {start final : WindingOneState p ambient} : Trace origin epsilon start final → Nat
  | .done _ => 0
  | .advance _ _ tail => tail.length + 1

set_option genInjectivity false in
/-- An accepted subdivision state with its actual ordered history and finite step bound.

The result keeps the fixed original parent and accuracy request. Its trace starts
at the supplied current state, every preceding state failed acceptance, and the
actual edge count is bounded by the displayed remaining fuel.
-/
structure Result (origin : WindingOneState p ambient) (epsilon : Fraction.Rational)
    (start : WindingOneState p ambient) (fuel : Nat) where
  /-- The actual accepted winding-one state on the original polynomial and ambient. -/ state :
    WindingOneState p ambient
  /-- The accepted state is strictly inside the original parent. -/ strict : state.box.StrictInterior origin.box
  /-- Its squared diagonal meets the original accuracy request. -/ accurate : state.box.diagonalSq ≤ epsilon ^ 2
  /-- The retained finite subdivision history from the supplied starting state. -/ trace :
    Trace origin epsilon start state
  /-- The actual number of executed subdivision edges, computed once by the scan. -/ steps : Nat
  /-- The computed count is the length of the same retained actual history. -/ steps_eq : steps = trace.length
  /-- The executed subdivision count fits the remaining finite fuel. -/ bounded : steps ≤ fuel

constructive_injectivity Result

/-- The sufficient diagonal threshold retains both the original accuracy and protected-boundary budgets. -/
@[expose] def threshold (origin : WindingOneState p ambient) (epsilon : Fraction.Rational) :
    Fraction.Rational :=
  min (epsilon ^ 2)
    (Clearance.Box.ProtectedRadius.protectedBoundaryRadius p origin.box origin.clearance ^ 2)

/-- A positive original accuracy makes the sufficient threshold positive. -/
theorem threshold_pos (origin : WindingOneState p ambient) {epsilon : Fraction.Rational}
    (positive : 0 < epsilon) : 0 < threshold origin epsilon :=
  Fraction.Order.Basic.lt_min
    (Arithmetic.pow_pos_direct positive 2)
    (Arithmetic.pow_pos_direct
      (Clearance.Box.ProtectedRadius.protectedBoundaryRadius_pos p origin.clearance origin.proper) 2)

/-- Sufficiently small retained winding-one children satisfy the actual strictness and accuracy tests. -/
theorem accepted_of_threshold (input : FTA.Squarefree.Input p)
    (origin current : WindingOneState p ambient) {epsilon : Fraction.Rational}
    (nested : current.box.Refines origin.box)
    (small : current.box.diagonalSq ≤ threshold origin epsilon) : Accepted origin epsilon current := by
  let rho := Clearance.Box.ProtectedRadius.protectedBoundaryRadius p origin.box origin.clearance
  have rhoPositive : 0 < rho :=
    Clearance.Box.ProtectedRadius.protectedBoundaryRadius_pos p origin.clearance origin.proper
  have margins := Winding.Box.ProtectedBoundary.strictly_inside_protectedBoundary
    input.degreePositive origin.clearance origin.proper current.proper nested current.raw.rawWinding_ne
    (small.trans (Fraction.Order.Basic.min_le_right _ _))
  have fourPositive : (0 : Fraction.Rational) < 4 * rho :=
    Arithmetic.mul_pos_direct (by decide) rhoPositive
  have addMargin (value : Fraction.Rational) : value < value + 4 * rho := by
    have shifted := Arithmetic.add_lt_add_right_direct fourPositive value
    calc
      value = 0 + value := by ring1
      _ < 4 * rho + value := shifted
      _ = value + 4 * rho := by ring1
  have subMargin (value : Fraction.Rational) : value - 4 * rho < value := by
    calc
      value - 4 * rho < value - 0 :=
        Arithmetic.sub_lt_sub_left_direct fourPositive value
      _ = value := by ring1
  refine ⟨⟨?_, ?_, ?_, ?_⟩, small.trans (Fraction.Order.Basic.min_le_left _ _)⟩
  · exact (addMargin origin.box.xLower).trans margins.1
  · exact margins.2.1.trans (subMargin origin.box.xUpper)
  · exact (addMargin origin.box.yLower).trans margins.2.2.1
  · exact margins.2.2.2.trans (subMargin origin.box.yUpper)

/-- One retained step transfers the sufficient remaining-fuel inequality to its actual child. -/
theorem Step.remaining_bound {current : WindingOneState p ambient} (step : Step current)
    (fuel : Nat) {target : Fraction.Rational}
    (terminal : (4 / 9 : Fraction.Rational) ^ (fuel + 1) * current.box.diagonalSq ≤ target) :
    (4 / 9 : Fraction.Rational) ^ fuel * step.state.box.diagonalSq ≤ target := by
  calc
    (4 / 9 : Fraction.Rational) ^ fuel * step.state.box.diagonalSq ≤
        (4 / 9 : Fraction.Rational) ^ fuel * ((4 / 9 : Fraction.Rational) * current.box.diagonalSq) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct step.contracts
        (Arithmetic.pow_nonneg_direct (by decide) fuel)
    _ = (4 / 9 : Fraction.Rational) ^ (fuel + 1) * current.box.diagonalSq := by
      rewrite [pow_succ]
      ring1
    _ ≤ target := terminal

/-- Scan actual subdivisions, stopping at the first accepted state within the sufficient finite bound.

The starting state refines the fixed origin. The retained diagonal inequality
proves that the displayed remaining fuel reaches both original stopping budgets.
-/
@[expose] def scan (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (clearances : AxisClearances elimination)
    (origin : WindingOneState p ambient) (epsilon : Fraction.Rational) :
    (fuel : Nat) → (current : WindingOneState p ambient) → current.box.Refines origin.box →
    (4 / 9 : Fraction.Rational) ^ fuel * current.box.diagonalSq ≤ threshold origin epsilon →
    Result origin epsilon current fuel
  | 0, current, nested, terminal =>
      let accepted := accepted_of_threshold input origin current nested (by
        rewrite [pow_zero, one_mul] at terminal
        exact terminal)
      ⟨current, accepted.1, accepted.2, .done current, 0, rfl, Nat.le_refl 0⟩
  | fuel + 1, current, nested, terminal =>
      if accepted : Accepted origin epsilon current then
        ⟨current, accepted.1, accepted.2, .done current, 0, rfl, Nat.zero_le _⟩
      else
        let next := refineOnce input elimination current clearances
        have nextTerminal := next.remaining_bound fuel terminal
        let following := scan input elimination clearances origin epsilon fuel next.state
          (next.nested.trans nested) nextTerminal
        ⟨following.state, following.strict, following.accurate,
          .advance next accepted following.trace, following.steps + 1,
          congrArg (fun count => count + 1) following.steps_eq,
          Nat.succ_le_succ following.bounded⟩

/-- Read one successor-fuel scan equation at its original concrete state and bounds.

This pointwise equality is kernel reflexivity. It does not use the generated
whole-function equation, so consumers need no function-extensionality rule.
-/
theorem scan_succ (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (clearances : AxisClearances elimination)
    (origin : WindingOneState p ambient) (epsilon : Fraction.Rational) (fuel : Nat)
    (current : WindingOneState p ambient) (nested : current.box.Refines origin.box)
    (terminal : (4 / 9 : Fraction.Rational) ^ (fuel + 1) * current.box.diagonalSq ≤ threshold origin epsilon) :
    scan input elimination clearances origin epsilon (fuel + 1) current nested terminal =
      if accepted : Accepted origin epsilon current then
        ⟨current, accepted.1, accepted.2, .done current, 0, rfl, Nat.zero_le _⟩
      else
        let next := refineOnce input elimination current clearances
        let following := scan input elimination clearances origin epsilon fuel next.state
          (next.nested.trans nested) (next.remaining_bound fuel terminal)
        ⟨following.state, following.strict, following.accurate,
          .advance next accepted following.trace, following.steps + 1,
          congrArg (fun count => count + 1) following.steps_eq,
          Nat.succ_le_succ following.bounded⟩ := rfl

/-- The computed ceiling is sufficient fuel for strict, accurate subdivision of the original parent.

The ceiling is an upper bound, not the executed step count. The actual scan
checks each intermediate state and can stop before this bound without computing
an entire worst-case subdivision or a Newton extraction.
-/
@[expose] def depthBound (origin : WindingOneState p ambient) (epsilon : Fraction.Rational) : Nat :=
  Purelib.Approximation.Rational.Contraction.geometricDepthBound origin.box.diagonalSq
    (threshold origin epsilon)

/-- The displayed finite fuel contracts the original diagonal below both stopping budgets. -/
theorem depthBound_sufficient (origin : WindingOneState p ambient) {epsilon : Fraction.Rational}
    (positive : 0 < epsilon) :
    (4 / 9 : Fraction.Rational) ^ depthBound origin epsilon * origin.box.diagonalSq ≤
      threshold origin epsilon := by
  let bound := depthBound origin epsilon
  have powerBound : (4 / 9 : Fraction.Rational) ^ bound ≤ (2 / 3 : Fraction.Rational) ^ bound :=
    Arithmetic.pow_le_pow_direct (by decide) (by decide) bound
  exact (Arithmetic.mul_le_mul_of_nonneg_right_direct powerBound
    origin.box.diagonalSq_nonneg).trans
    (Purelib.Approximation.Rational.Contraction.geometricDepthBound_sufficient
      origin.box.diagonalSq_nonneg (threshold_pos origin positive))

/-- Refine the original winding-one state by bounded early-stopping safe subdivision.

The supplied squarefree and elimination certificates retain their original
polynomial, degree and ambient owners. Positive accuracy gives a sufficient
finite bound internally; no successful attempt or external stopping witness is
required. The result retains the actual raw-grid trace and executed step count.
-/
def request (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound) (origin : WindingOneState p ambient)
    {epsilon : Fraction.Rational} (positive : 0 < epsilon)
    (clearances : AxisClearances elimination := .canonical elimination) :
    Result origin epsilon origin (depthBound origin epsilon) := by
  exact scan input elimination clearances origin epsilon (depthBound origin epsilon) origin
    (Box.refines_refl _) (depthBound_sufficient origin (epsilon := epsilon) positive)

attribute [local irreducible] scan depthBound request in
/-- The complete request is the original finite scan at its internally computed sufficient bound. -/
theorem request_eq_scan (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound) (origin : WindingOneState p ambient)
    {epsilon : Fraction.Rational} (positive : 0 < epsilon)
    (clearances : AxisClearances elimination := .canonical elimination) :
    request input elimination origin (epsilon := epsilon) positive clearances =
      scan input elimination clearances origin epsilon (depthBound origin epsilon) origin
        (Box.refines_refl _) (depthBound_sufficient origin (epsilon := epsilon) positive) := by
  unfold request
  rfl

/-- Install total strict, accurate subdivision with the supplied original initial state and line provider. -/
@[expose] def ofInitial (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound) (initial : WindingOneState p ambient)
    (clearances : AxisClearances elimination := .canonical elimination) :
    Track.Basic.WindingOneTrack p ambient where
  initial := initial
  refine current epsilon positive := (request input elimination current (epsilon := epsilon) positive clearances).state
  nested current epsilon positive :=
    Box.Refinement.StrictInterior.refines
      (request input elimination current (epsilon := epsilon) positive clearances).strict
  strict current epsilon positive := (request input elimination current (epsilon := epsilon) positive clearances).strict
  accurate current epsilon positive :=
    (request input elimination current (epsilon := epsilon) positive clearances).accurate

/-- The subdivision track keeps the supplied initial winding-one state literally. -/
theorem ofInitial_initial (input : FTA.Squarefree.Input p)
    (elimination : AxisEliminationCertificate p degreeBound) (initial : WindingOneState p ambient)
    (clearances : AxisClearances elimination := .canonical elimination) :
    (ofInitial input elimination initial clearances).initial = initial := rfl

end Purelib.RootIsolation.Subdivision.WindingOne

end
