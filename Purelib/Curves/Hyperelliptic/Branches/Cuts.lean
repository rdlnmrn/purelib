module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
public import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.CoherentRoot
public import Init.Data.Fin.Lemmas
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

open Purelib.Data.Gaussian

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Riemann.RootContinuation

section
@[expose] public section

/-!
# Certified rational branch cuts

The initial isolation boxes come with polynomial-clear coordinate lines across
the one finite ambient square.  Consequently two finite branch boxes can be
joined by a rational L-shaped path: first along the lower edge line of the
left box, then along the left edge line of the right box.  An odd-degree
infinity cut exits along the same clear horizontal line to the right boundary
of the ambient square.  Every segment below stores its finite line-clearance
certificate; there is no appeal to a complement of an infinite point set.
-/

namespace Purelib.Curves.Hyperelliptic.Branches.Cuts

/-- The original finite ambient square selected from the curve polynomial root-radius bound. -/
abbrev Ambient {genus : Nat} (curve :
  Hyperelliptic.Basic.HyperellipticCurve genus) :=
  RootRadius.Box.largeSquareBox curve.polynomial

/-- The lower-left anchor of the actual initial track box. -/
def trackAnchor {genus : Nat} {curve :
  Hyperelliptic.Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (index : Data.Index branches) : Data.Gaussian.Basic.Canonical :=
  (branches.track degreeGtOne index).initial.box.anchor

/-- The initial retained root-track anchor equals the original branch-family anchor. -/
theorem trackAnchor_eq_branchAnchor {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (index : Data.Index branches) :
    trackAnchor branches degreeGtOne index = branches.anchor index :=
  branches.track_initial_anchor degreeGtOne index

/-- The deterministic nested winding state used at one finite path refinement. -/
def refinedState {genus : Nat} {curve :
  Hyperelliptic.Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (index : Data.Index branches) (refinement : Nat) :=
  CoherentRoot.state (branches.track degreeGtOne index) refinement

/-- The rational endpoint at one finite refinement of a branch cut. These anchors remain nested around the same
winding-one owner. -/
def refinedTrackAnchor {genus : Nat} {curve :
  Hyperelliptic.Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (index : Data.Index branches) (refinement : Nat) : Data.Gaussian.Basic.Canonical :=
  (refinedState branches degreeGtOne index refinement).box.anchor

/-- Zero refinement retains the original initial root-track anchor. -/
@[simp] theorem refinedTrackAnchor_zero {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (index : Data.Index branches) :
    refinedTrackAnchor branches degreeGtOne index 0 =
      trackAnchor branches degreeGtOne index := rfl

/-- The automatic two-segment connector at an arbitrary deterministic root refinement. Unlike `connector`, its endpoints
converge coherently to the two branch occurrences while every finite segment stays on a certified polynomial-clear
ambient line. -/
def connectorAt {genus : Nat} {curve :
  Hyperelliptic.Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : Data.Index branches) (refinement : Nat) :
    Polynomial.Geometry.ClearPath curve.polynomial (Ambient curve)
      (refinedTrackAnchor branches degreeGtOne left refinement)
      (refinedTrackAnchor branches degreeGtOne right refinement) := by
  let leftState := refinedState branches degreeGtOne left refinement
  let rightState := refinedState branches degreeGtOne right refinement
  exact .cons
    (.horizontal leftState.box.xLower rightState.box.xLower
      leftState.box.yLower
      leftState.refinesAmbient.1
      (leftState.box.x_valid.trans leftState.refinesAmbient.2.1)
      rightState.refinesAmbient.1
      (rightState.box.x_valid.trans rightState.refinesAmbient.2.1)
      leftState.ambientBottomClearance)
    (.cons
      (.vertical rightState.box.xLower leftState.box.yLower
        rightState.box.yLower
        leftState.refinesAmbient.2.2.1
        (leftState.box.y_valid.trans leftState.refinesAmbient.2.2.2)
        rightState.refinesAmbient.2.2.1
        (rightState.box.y_valid.trans rightState.refinesAmbient.2.2.2)
        rightState.ambientLeftClearance)
      (.nil (refinedTrackAnchor branches degreeGtOne right refinement)))

/-- Each refined finite connector has exactly two certified segments. -/
@[simp] theorem connectorAt_segmentCount {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : Data.Index branches) (refinement : Nat) :
    (connectorAt branches degreeGtOne left right refinement).segmentCount =
      2 := by
  rfl

/-- Every refined connector segment stays in the original finite ambient square. -/
theorem connectorAt_withinAmbient {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : Data.Index branches) (refinement : Nat) :
    (connectorAt branches degreeGtOne left right refinement).WithinAmbient := by
  let leftState := refinedState branches degreeGtOne left refinement
  let rightState := refinedState branches degreeGtOne right refinement
  exact .cons
    ⟨leftState.refinesAmbient.2.2.1,
      leftState.box.y_valid.trans leftState.refinesAmbient.2.2.2⟩
    (.cons
      ⟨rightState.refinesAmbient.1,
        rightState.box.x_valid.trans rightState.refinesAmbient.2.1⟩
      (.nil _))

/-- The left endpoint of the automatic finite connector is never a root. This is witnessed directly by the certified
horizontal clearance line. -/
theorem connectorAt_start_eval_ne_zero {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left _right : Data.Index branches) (refinement : Nat) :
    curve.polynomial.eval
        (refinedTrackAnchor branches degreeGtOne left refinement) ≠ 0 := by
  let state := refinedState branches degreeGtOne left refinement
  exact ClearSegment.horizontal_eval_ne_zero state.ambientBottomClearance
    state.box.xLower state.refinesAmbient.1
      (state.box.x_valid.trans state.refinesAmbient.2.1)

/-- The right endpoint of the automatic finite connector is never a root. This is witnessed directly by the certified
vertical clearance line. -/
theorem connectorAt_finish_eval_ne_zero {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (_left right : Data.Index branches) (refinement : Nat) :
    curve.polynomial.eval
        (refinedTrackAnchor branches degreeGtOne right refinement) ≠ 0 := by
  let state := refinedState branches degreeGtOne right refinement
  exact ClearSegment.vertical_eval_ne_zero state.ambientLeftClearance
    state.box.yLower state.refinesAmbient.2.2.1
      (state.box.y_valid.trans state.refinesAmbient.2.2.2)

/-- The polynomial residual at a retained refined anchor satisfies its geometric quarter-radius bound. -/
theorem refinedTrackAnchor_residual_le {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (index : Data.Index branches) (refinement : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        (curve.polynomial.eval
          (refinedTrackAnchor branches degreeGtOne index refinement)) <=
      Geometric.Basic.quarterRadius
        (CoherentRoot.residualScale curve.polynomial
          (Ambient curve) (branches.track degreeGtOne index)) refinement := by
  simpa only [CoherentRoot.approximation_sample,
    refinedTrackAnchor, refinedState,
      Ambient] using
    CoherentRoot.sample_residual_le
      (branches.track degreeGtOne index)
      (BranchIsolation.degreePositive curve) refinement

/-- The automatic two-segment connector between two higher-degree branch boxes. -/
def connector {genus : Nat} {curve :
  Hyperelliptic.Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : Data.Index branches) :
    Polynomial.Geometry.ClearPath curve.polynomial (Ambient curve)
      (trackAnchor branches degreeGtOne left)
      (trackAnchor branches degreeGtOne right) := by
  let leftState := (branches.track degreeGtOne left).initial
  let rightState := (branches.track degreeGtOne right).initial
  let corner : Data.Gaussian.Basic.Canonical :=
    Components.Basic.point rightState.box.xLower leftState.box.yLower
  exact .cons
    (.horizontal leftState.box.xLower rightState.box.xLower
      leftState.box.yLower
      leftState.refinesAmbient.1
      (leftState.box.x_valid.trans leftState.refinesAmbient.2.1)
      rightState.refinesAmbient.1
      (rightState.box.x_valid.trans rightState.refinesAmbient.2.1)
      leftState.ambientBottomClearance)
    (.cons
      (.vertical rightState.box.xLower leftState.box.yLower
        rightState.box.yLower
        leftState.refinesAmbient.2.2.1
        (leftState.box.y_valid.trans leftState.refinesAmbient.2.2.2)
        rightState.refinesAmbient.2.2.1
        (rightState.box.y_valid.trans rightState.refinesAmbient.2.2.2)
        rightState.ambientLeftClearance)
      (.nil (trackAnchor branches degreeGtOne right)))

/-- The initial finite connector has exactly two certified segments. -/
@[simp] theorem connector_segmentCount {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (left right : Data.Index branches) :
    (connector branches degreeGtOne left right).segmentCount = 2 := by
  rfl

set_option genInjectivity false in
/-- A finite representative of a cut to infinity: it reaches the right edge of the isolator's ambient square along a
certified polynomial-clear line.

The retained boundary coordinate and clear path remain tied to the original finite root occurrence. The endpoint
equation fixes the exact right boundary of the original ambient square. -/
structure InfinityExit {genus : Nat} {curve :
  Hyperelliptic.Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (finite : Data.Index branches) where
  /-- The retained finite endpoint on the original ambient right boundary. -/ boundaryPoint :
    Data.Gaussian.Basic.Canonical
  /-- The retained exit point has exactly the ambient right-edge real coordinate. -/ onRightBoundary : boundaryPoint.re
    = (Ambient curve).xUpper
  /-- The retained polynomial-clear path from the original or refined branch anchor to this boundary point. -/ path :
    Polynomial.Geometry.ClearPath curve.polynomial (Ambient curve)
    (trackAnchor branches degreeGtOne finite) boundaryPoint

constructive_injectivity Purelib.Curves.Hyperelliptic.Branches.Cuts.InfinityExit

/-- Automatically exit one finite branch box to the ambient right boundary. -/
def infinityExit {genus : Nat} {curve :
  Hyperelliptic.Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (finite : Data.Index branches) :
    InfinityExit branches degreeGtOne finite := by
  let state := (branches.track degreeGtOne finite).initial
  let boundary := Components.Basic.point (Ambient curve).xUpper state.box.yLower
  exact
    { boundaryPoint := boundary
      onRightBoundary := rfl
      path := .cons
        (.horizontal state.box.xLower (Ambient curve).xUpper state.box.yLower
          state.refinesAmbient.1
          (state.box.x_valid.trans state.refinesAmbient.2.1)
          (Ambient curve).x_valid
          le_rfl
          state.ambientBottomClearance)
        (.nil boundary) }

/-- The initial infinity exit has exactly one certified horizontal segment. -/
@[simp] theorem infinityExit_segmentCount {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (finite : Data.Index branches) :
    (infinityExit branches degreeGtOne finite).path.segmentCount = 1 := by
  rfl

set_option genInjectivity false in
/-- Refined version of an infinity exit whose finite endpoint follows the nested owner track.

The clear path begins at the exact selected refinement of the original root track. Its retained endpoint lies on the
original ambient square's right boundary. -/
structure RefinedInfinityExit {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (finite : Data.Index branches) (refinement : Nat) where
  /-- The retained finite endpoint on the original ambient right boundary. -/ boundaryPoint :
    Data.Gaussian.Basic.Canonical
  /-- The retained exit point has exactly the ambient right-edge real coordinate. -/ onRightBoundary : boundaryPoint.re
    = (Ambient curve).xUpper
  /-- The retained polynomial-clear path from the original or refined branch anchor to this boundary point. -/ path :
    Polynomial.Geometry.ClearPath curve.polynomial (Ambient curve)
    (refinedTrackAnchor branches degreeGtOne finite refinement) boundaryPoint

constructive_injectivity Purelib.Curves.Hyperelliptic.Branches.Cuts.RefinedInfinityExit

/-- At every finite refinement, exit the refined owner anchor along its fresh certified lower line. -/
def infinityExitAt {genus : Nat} {curve :
  Hyperelliptic.Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve) (degreeGtOne : 1 < curve.polynomial.natDegree)
    (finite : Data.Index branches) (refinement : Nat) :
    RefinedInfinityExit branches degreeGtOne finite refinement := by
  let state := refinedState branches degreeGtOne finite refinement
  let boundary := Components.Basic.point (Ambient curve).xUpper state.box.yLower
  exact
    { boundaryPoint := boundary
      onRightBoundary := rfl
      path := .cons
        (.horizontal state.box.xLower (Ambient curve).xUpper state.box.yLower
          state.refinesAmbient.1
          (state.box.x_valid.trans state.refinesAmbient.2.1)
          (Ambient curve).x_valid le_rfl state.ambientBottomClearance)
        (.nil boundary) }

/-- Every refined infinity exit has exactly one certified horizontal segment. -/
@[simp] theorem infinityExitAt_segmentCount {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (finite : Data.Index branches) (refinement : Nat) :
    (infinityExitAt branches degreeGtOne finite refinement).path.segmentCount =
      1 := by
  rfl

/-- The refined infinity exit remains within the original finite ambient square. -/
theorem infinityExitAt_withinAmbient {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus} (branches : BranchIsolation.Data curve)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (finite : Data.Index branches) (refinement : Nat) :
    (infinityExitAt branches degreeGtOne finite refinement).path.WithinAmbient := by
  let state := refinedState branches degreeGtOne finite refinement
  exact .cons
    ⟨state.refinesAmbient.2.2.1,
      state.box.y_valid.trans state.refinesAmbient.2.2.2⟩
    (.nil _)

set_option genInjectivity false in
/-- Certified content of one branch cut with fixed semantic endpoints.

Each constructor keeps its original ordered semantic endpoints and retained clear path or infinity exit. The degree
evidence distinguishes higher-degree transport from the exact degree-one case. -/
inductive Certificate {genus : Nat} (curve :
  Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) :
    BranchConfiguration.Site curve branches -> BranchConfiguration.Site curve branches -> Type
  /-- Retain a certified clear connector between two distinct original finite root occurrences. -/ | finite (left right
    : Data.Index branches)
      (different : left ≠ right)
      (degreeGtOne : 1 < curve.polynomial.natDegree)
      (path : Polynomial.Geometry.ClearPath curve.polynomial (Ambient curve)
        (trackAnchor branches degreeGtOne left)
        (trackAnchor branches degreeGtOne right)) :
      Certificate curve branches (.finite left) (.finite right)
  /-- Retain a higher-degree clear exit from the original finite root occurrence to infinity. -/ | toInfinity (finite :
    Data.Index branches)
      (degreeGtOne : 1 < curve.polynomial.natDegree)
      (exit : InfinityExit branches degreeGtOne finite) :
      Certificate curve branches (.finite finite) .infinity
  /-- Retain the same certified higher-degree exit with infinity as the first semantic endpoint. -/ | fromInfinity
    (finite : Data.Index branches)
      (degreeGtOne : 1 < curve.polynomial.natDegree)
      (exit : InfinityExit branches degreeGtOne finite) :
      Certificate curve branches .infinity (.finite finite)
  /-- The unique finite root of a degree-one curve is paired with infinity. -/ | linearToInfinity (finite : Data.Index
    branches)
      (degreeOne : curve.polynomial.natDegree = 1) :
      Certificate curve branches (.finite finite) .infinity
  /-- Infinity is paired with the unique finite root of a degree-one curve. -/ | infinityToLinear (finite : Data.Index
    branches)
      (degreeOne : curve.polynomial.natDegree = 1) :
      Certificate curve branches .infinity (.finite finite)

constructive_injectivity Purelib.Curves.Hyperelliptic.Branches.Cuts.Certificate

set_option genInjectivity false in
/-- Geometry of one branch cut. Its endpoints are stored explicitly, so a cut system can state exact agreement with the
branch enumeration.

Both semantic endpoints retain their original branch-family parent. The indexed certificate and endpoint inequality
describe that exact ordered cut. -/
structure Geometry {genus : Nat} (curve :
  Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) : Type where
  /-- The retained first semantic ramification site of this cut. -/ leftSite : BranchConfiguration.Site curve branches
  /-- The retained second semantic ramification site of this cut. -/ rightSite : BranchConfiguration.Site curve branches
  /-- The two retained semantic cut endpoints are distinct. -/ different : leftSite ≠ rightSite
  /-- The certified cut geometry indexed by these exact original semantic endpoints. -/ certificate :
    Certificate curve branches leftSite rightSite

constructive_injectivity Purelib.Curves.Hyperelliptic.Branches.Cuts.Geometry

/-- Construct the certified content of a cut between two distinct ramification sites. -/
def certificateBetween {genus : Nat} {curve :
  Hyperelliptic.Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve) (left right : BranchConfiguration.Site curve branches)
    (different : left ≠ right) : Certificate curve branches left right := by
  by_cases higher : 1 < curve.polynomial.natDegree
  · cases left with
    | finite leftIndex =>
        cases right with
        | finite rightIndex =>
            have indexDifferent : leftIndex ≠ rightIndex := by
              intro equal
              apply different
              rw [equal]
            exact .finite leftIndex rightIndex indexDifferent higher
              (connector branches higher leftIndex rightIndex)
        | infinity =>
            exact .toInfinity leftIndex higher
              (infinityExit branches higher leftIndex)
    | infinity =>
        cases right with
        | finite rightIndex =>
            exact .fromInfinity rightIndex higher
              (infinityExit branches higher rightIndex)
        | infinity => exact (different rfl).elim
  · have degreeOne : curve.polynomial.natDegree = 1 := by
      have positive := BranchIsolation.degreePositive curve
      omega0
    cases left with
    | finite leftIndex =>
        cases right with
        | finite rightIndex =>
            have equalIndex : leftIndex = rightIndex := by
              apply Fin.ext
              have leftBound := leftIndex.isLt
              have rightBound := rightIndex.isLt
              have countOne : branches.siteCount = 1 :=
                branches.count_eq.trans degreeOne
              have leftBoundOne : leftIndex.val < 1 :=
                leftBound.trans_eq countOne
              have rightBoundOne : rightIndex.val < 1 :=
                rightBound.trans_eq countOne
              omega0
            exact (different (by rw [equalIndex])).elim
        | infinity =>
            exact .linearToInfinity leftIndex degreeOne
    | infinity =>
        cases right with
        | finite rightIndex =>
            exact .infinityToLinear rightIndex degreeOne
        | infinity => exact (different rfl).elim

/-- Construct a cut for any two distinct ramification sites. -/
def geometryBetween {genus : Nat} {curve :
  Hyperelliptic.Basic.HyperellipticCurve genus}
    (branches : BranchIsolation.Data curve) (left right : BranchConfiguration.Site curve branches)
    (different : left ≠ right) : Geometry curve branches where
  leftSite := left
  rightSite := right
  different := different
  certificate := certificateBetween branches left right different

open Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration in
set_option genInjectivity false in
/-- All `g+1` standard cuts constructed from the one persistent branch configuration.

Every finite cut retains the original branch configuration. The endpoint equations link each selected geometry to the
corresponding consecutive source labels. -/
structure System {genus : Nat} (curve :
  Hyperelliptic.Basic.HyperellipticCurve genus) where
  /-- The original retained degree-shaped branch configuration. -/ configuration : BranchConfiguration.Configuration
    curve
  /-- The retained finite cut geometry for each consecutive branch pair. -/ cutAt : Fin (genus + 1) ->
    Geometry curve configuration.branches
  /-- Each retained cut begins at the exact first site of its original standard pair. -/ left_eq : forall index,
    (cutAt index).leftSite =
      configuration.siteAt (BranchConfiguration.standardPair index).left
  /-- Each retained cut ends at the exact second site of its original standard pair. -/ right_eq : forall index,
    (cutAt index).rightSite =
      configuration.siteAt (BranchConfiguration.standardPair index).right

constructive_injectivity Purelib.Curves.Hyperelliptic.Branches.Cuts.System

open Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration in
/-- Construct the standard consecutive branch-cut system from any audited finite branch configuration. -/
def systemOfConfiguration {genus : Nat} (curve :
  Hyperelliptic.Basic.HyperellipticCurve genus)
    (configuration : BranchConfiguration.Configuration curve) : System curve := by
  let cutAt := fun index : Fin (genus + 1) =>
    geometryBetween configuration.branches
      (configuration.siteAt (BranchConfiguration.standardPair index).left)
      (configuration.siteAt (BranchConfiguration.standardPair index).right)
      (BranchConfiguration.cutEndpoints_different configuration index)
  exact
    { configuration := configuration
      cutAt := cutAt
      left_eq := fun index => rfl
      right_eq := fun index => rfl }

/-- Construct the standard consecutive cut system directly from explicit degree-complete branch data. -/
def systemOfData {genus : Nat} (curve :
  Hyperelliptic.Basic.HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) : System curve :=
  systemOfConfiguration curve
    (BranchConfiguration.configurationOfData curve branches)

/-- Fully automatic finite branch-cut system. -/
def system {genus : Nat} (curve :
  Hyperelliptic.Basic.HyperellipticCurve genus) : System curve :=
  systemOfConfiguration curve (BranchConfiguration.configuration curve)

open Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration in
/-- The automatically constructed cuts cover every branch label through the standard consecutive pairing. -/
theorem System.covers {genus : Nat} {curve :
  Hyperelliptic.Basic.HyperellipticCurve genus}
    (system : System curve) (position : Fin (2 * genus + 2)) :
    system.configuration.siteAt position =
        (system.cutAt (BranchConfiguration.pairOf position)).leftSite \/
      system.configuration.siteAt position =
        (system.cutAt (BranchConfiguration.pairOf position)).rightSite := by
  rcases standardPair_covers position with left | right
  · left
    exact (congrArg system.configuration.siteAt left).trans
      (system.left_eq (BranchConfiguration.pairOf position)).symm
  · right
    exact (congrArg system.configuration.siteAt right).trans
      (system.right_eq (BranchConfiguration.pairOf position)).symm

end Purelib.Curves.Hyperelliptic.Branches.Cuts

end
