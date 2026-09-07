import CCL.Riemann.BranchCuts

/-!
# Two-sheet lifts of the certified branch cuts

Each clear base segment lifts on a fixed labelled sheet with identity sheet
transport.  At either end of a cut a zero-length cell carries the explicit
two-sheet transposition.  Traversing one bank forward, switching sheets,
traversing the other bank backward, and switching again therefore gives a
finite closed lifted path around the cut.
-/

namespace CCL.Riemann.BranchCutLifts

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.BranchCuts
open CCL.Riemann.LiftedPaths

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev FiniteBijection := CCL.FiniteMonodromy.FiniteBijection
abbrev WindingOneState := RFAP.ShrinkingTrack.WindingOneState

/-- The other label in the explicitly finite two-sheet set. -/
def otherSheet (sheet : Fin 2) : Fin 2 :=
  ⟨1 - sheet.val, by
    have bound := sheet.isLt
    omega0⟩

@[simp] theorem otherSheet_zero : otherSheet (0 : Fin 2) = 1 := rfl

@[simp] theorem otherSheet_one : otherSheet (1 : Fin 2) = 0 := rfl

@[simp] theorem otherSheet_other (sheet : Fin 2) :
    otherSheet (otherSheet sheet) = sheet := by
  apply Fin.ext
  have bound := sheet.isLt
  simp only [otherSheet]
  omega0

/-- The local monodromy of a simple hyperelliptic branch point. -/
def sheetSwap : FiniteBijection 2 2 where
  forward := otherSheet
  backward := otherSheet
  backward_forward := otherSheet_other
  forward_backward := otherSheet_other

@[simp] theorem sheetSwap_forward (sheet : Fin 2) :
    sheetSwap.forward sheet = otherSheet sheet := rfl

namespace ClearSegment

/-- Reverse a certified segment without changing its clearance line. -/
def reverse {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish) :
    ClearSegment polynomial ambient finish start := by
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper
      clearance =>
      exact .horizontal xFinish xStart y finishLower finishUpper
        startLower startUpper clearance
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper
      clearance =>
      exact .vertical x yFinish yStart finishLower finishUpper
        startLower startUpper clearance

theorem reverse_withinAmbient {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient) :
    (reverse segment).WithinAmbient := by
  cases segment <;> exact within

/-- Lift one clear segment without changing the selected sheet. -/
def liftOnSheet {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (sheet : Fin 2)
    (_segment : ClearSegment polynomial ambient start finish) :
    LiftedCell
      ({ coordinate := start, sheet := sheet } : LiftedPoint 2)
      ({ coordinate := finish, sheet := sheet } : LiftedPoint 2) where
  sheetTransport := CCL.FiniteMonodromy.FiniteBijection.identity 2
  finishSheet_eq := rfl

/-- Lift an ordinary clear segment while applying the two-sheet swap across
that edge.  This is used as the terminal edge of a certified winding-one
boundary. -/
def liftWithSwap {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian} (sheet : Fin 2)
    (_segment : ClearSegment polynomial ambient start finish) :
    LiftedCell
      ({ coordinate := start, sheet := sheet } : LiftedPoint 2)
      ({ coordinate := finish, sheet := otherSheet sheet } : LiftedPoint 2) where
  sheetTransport := sheetSwap
  finishSheet_eq := rfl

end ClearSegment

/-- A zero-length base cell implementing the nontrivial local sheet swap. -/
def switchCell (coordinate : Gaussian) (sheet : Fin 2) :
    LiftedCell
      ({ coordinate := coordinate, sheet := sheet } : LiftedPoint 2)
      ({ coordinate := coordinate, sheet := otherSheet sheet } : LiftedPoint 2)
    where
  sheetTransport := sheetSwap
  finishSheet_eq := rfl

namespace ClearPath

/-- Reverse a finite clear path and all of its segment orientations. -/
def reverse {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian} ->
      ClearPath polynomial ambient start finish ->
      ClearPath polynomial ambient finish start
  | _, _, .nil point => .nil point
  | start, _, .cons head tail =>
      (reverse tail).append
        (.cons (CCL.Riemann.BranchCutLifts.ClearSegment.reverse head)
          (.nil start))

theorem reverse_withinAmbient {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish)
    (within : path.WithinAmbient) :
    (reverse path).WithinAmbient := by
  induction within with
  | nil point => exact .nil point
  | cons headWithin tailWithin inductionHypothesis =>
      exact inductionHypothesis.append
        (.cons
          (CCL.Riemann.BranchCutLifts.ClearSegment.reverse_withinAmbient
            _ headWithin)
          (.nil _))

@[simp] theorem segmentCount_reverse {polynomial : GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish) :
    (CCL.Riemann.BranchCutLifts.ClearPath.reverse path).segmentCount =
      path.segmentCount := by
  induction path with
  | nil => rfl
  | @cons start middle finish head tail inductionHypothesis =>
      simp only [reverse, CCL.Riemann.BranchCuts.ClearPath.segmentCount_append,
        inductionHypothesis, CCL.Riemann.BranchCuts.ClearPath.segmentCount]

/-- Lift every segment of a clear path on one fixed sheet. -/
def liftOnSheet {polynomial : GaussianPolynomial} {ambient : Box}
    (sheet : Fin 2) : {start finish : Gaussian} ->
      ClearPath polynomial ambient start finish ->
      LiftedPath 2
        { coordinate := start, sheet := sheet }
        { coordinate := finish, sheet := sheet }
  | _, _, .nil point => .nil { coordinate := point, sheet := sheet }
  | _, _, .cons head tail =>
      .cons
        (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet sheet head)
        (liftOnSheet sheet tail)

/-- Lift a clear path on one sheet and then record one explicit local sheet
transition at its finishing coordinate.  For owner-boundary paths the
preceding clear loop carries the separate winding-one certificate. -/
def liftOnSheetThenSwap {polynomial : GaussianPolynomial} {ambient : Box}
    (sheet : Fin 2) {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish) :
    LiftedPath 2
      { coordinate := start, sheet := sheet }
      { coordinate := finish, sheet := otherSheet sheet } :=
  (liftOnSheet sheet path).append
    (.cons (switchCell finish sheet)
      (.nil { coordinate := finish, sheet := otherSheet sheet }))

@[simp] theorem liftOnSheet_castStart
    {polynomial : GaussianPolynomial} {ambient : Box}
    (sheet : Fin 2) {left right finish : Gaussian}
    (equal : left = right)
    (path : ClearPath polynomial ambient left finish) :
    liftOnSheet sheet (path.castStart equal) =
      (liftOnSheet sheet path).castStart
        (congrArg (fun coordinate : Gaussian =>
          ({ coordinate := coordinate, sheet := sheet } : LiftedPoint 2))
            equal) := by
  subst right
  rfl

@[simp] theorem liftOnSheet_castFinish
    {polynomial : GaussianPolynomial} {ambient : Box}
    (sheet : Fin 2) {start left right : Gaussian}
    (equal : left = right)
    (path : ClearPath polynomial ambient start left) :
    liftOnSheet sheet (path.castFinish equal) =
      (liftOnSheet sheet path).castFinish
        (congrArg (fun coordinate : Gaussian =>
          ({ coordinate := coordinate, sheet := sheet } : LiftedPoint 2))
            equal) := by
  subst right
  rfl

@[simp] theorem liftOnSheet_append
    {polynomial : GaussianPolynomial} {ambient : Box}
    (sheet : Fin 2) {start middle finish : Gaussian}
    (first : ClearPath polynomial ambient start middle)
    (second : ClearPath polynomial ambient middle finish) :
    liftOnSheet sheet (first.append second) =
      (liftOnSheet sheet first).append (liftOnSheet sheet second) := by
  induction first with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [CCL.Riemann.BranchCuts.ClearPath.append, liftOnSheet,
        LiftedPath.append, inductionHypothesis]

@[simp] theorem liftOnSheet_cellCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    (sheet : Fin 2) {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish) :
    (CCL.Riemann.BranchCutLifts.ClearPath.liftOnSheet sheet path).cellCount =
      path.segmentCount := by
  induction path with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [liftOnSheet, LiftedPath.cellCount,
        CCL.Riemann.BranchCuts.ClearPath.segmentCount, inductionHypothesis]

@[simp] theorem liftOnSheetThenSwap_cellCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    (sheet : Fin 2) {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish) :
    (liftOnSheetThenSwap sheet path).cellCount = path.segmentCount + 1 := by
  simp only [liftOnSheetThenSwap, LiftedPath.cellCount_append,
    liftOnSheet_cellCount, LiftedPath.cellCount]

end ClearPath

/-- The positively oriented four-side boundary of a winding-one owner box.
Every side carries clearance for the polynomial whose root occurrence the box
owns. -/
def ownerBoundaryPath {polynomial : GaussianPolynomial} {ambient : Box}
    (state : WindingOneState polynomial ambient) :
    ClearPath polynomial state.box state.box.anchor state.box.anchor :=
  .cons
    (.horizontal state.box.xLower state.box.xUpper state.box.yLower
      le_rfl state.box.x_valid state.box.x_valid le_rfl
      (RFAP.BoxClearance.bottomOfBoundary state.clearance))
    (.cons
      (.vertical state.box.xUpper state.box.yLower state.box.yUpper
        le_rfl state.box.y_valid state.box.y_valid le_rfl
        (RFAP.BoxClearance.rightOfBoundary state.clearance))
      (.cons
        (.horizontal state.box.xUpper state.box.xLower state.box.yUpper
          state.box.x_valid le_rfl le_rfl state.box.x_valid
          (RFAP.BoxClearance.topOfBoundary state.clearance))
        (.cons
          (.vertical state.box.xLower state.box.yUpper state.box.yLower
            state.box.y_valid le_rfl le_rfl state.box.y_valid
            (RFAP.BoxClearance.leftOfBoundary state.clearance))
          (.nil state.box.anchor))))

@[simp] theorem ownerBoundaryPath_segmentCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    (state : WindingOneState polynomial ambient) :
    (ownerBoundaryPath state).segmentCount = 4 := rfl

theorem ownerBoundaryPath_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    (state : WindingOneState polynomial ambient) :
    (ownerBoundaryPath state).WithinAmbient :=
  by
    unfold ownerBoundaryPath
    exact .cons ⟨le_rfl, state.box.y_valid⟩
      (.cons ⟨state.box.x_valid, le_rfl⟩
        (.cons ⟨state.box.y_valid, le_rfl⟩
          (.cons ⟨le_rfl, state.box.x_valid⟩ (.nil _))))

/-- The displayed boundary is the actual winding-one boundary carried by the
owner state, in the repository's quadrupled convention. -/
theorem ownerBoundaryPath_windingFour
    {polynomial : GaussianPolynomial} {ambient : Box}
    (state : WindingOneState polynomial ambient) :
    RFAP.Winding.quadrupledBoxWinding polynomial state.box = 4 :=
  state.rawWindingFour

/-- Four displayed owner-boundary edges implementing one local sheet swap.
The first three retain the label; the closing edge records the degree-two
monodromy attached to the state's proved winding one. -/
def ownerBoundarySwapLift {polynomial : GaussianPolynomial} {ambient : Box}
    (state : WindingOneState polynomial ambient) (sheet : Fin 2) :
    LiftedPath 2
      { coordinate := state.box.anchor, sheet := sheet }
      { coordinate := state.box.anchor, sheet := otherSheet sheet } := by
  let bottom : ClearSegment polynomial state.box
      (RFAP.Winding.point state.box.xLower state.box.yLower)
      (RFAP.Winding.point state.box.xUpper state.box.yLower) :=
    .horizontal state.box.xLower state.box.xUpper state.box.yLower
      le_rfl state.box.x_valid state.box.x_valid le_rfl
      (RFAP.BoxClearance.bottomOfBoundary state.clearance)
  let right : ClearSegment polynomial state.box
      (RFAP.Winding.point state.box.xUpper state.box.yLower)
      (RFAP.Winding.point state.box.xUpper state.box.yUpper) :=
    .vertical state.box.xUpper state.box.yLower state.box.yUpper
      le_rfl state.box.y_valid state.box.y_valid le_rfl
      (RFAP.BoxClearance.rightOfBoundary state.clearance)
  let top : ClearSegment polynomial state.box
      (RFAP.Winding.point state.box.xUpper state.box.yUpper)
      (RFAP.Winding.point state.box.xLower state.box.yUpper) :=
    .horizontal state.box.xUpper state.box.xLower state.box.yUpper
      state.box.x_valid le_rfl le_rfl state.box.x_valid
      (RFAP.BoxClearance.topOfBoundary state.clearance)
  let left : ClearSegment polynomial state.box
      (RFAP.Winding.point state.box.xLower state.box.yUpper)
      (RFAP.Winding.point state.box.xLower state.box.yLower) :=
    .vertical state.box.xLower state.box.yUpper state.box.yLower
      state.box.y_valid le_rfl le_rfl state.box.y_valid
      (RFAP.BoxClearance.leftOfBoundary state.clearance)
  exact .cons
    (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet sheet bottom)
    (.cons
      (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet sheet right)
      (.cons
        (CCL.Riemann.BranchCutLifts.ClearSegment.liftOnSheet sheet top)
        (.cons
          (CCL.Riemann.BranchCutLifts.ClearSegment.liftWithSwap sheet left)
          (.nil _))))

@[simp] theorem ownerBoundarySwapLift_cellCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    (state : WindingOneState polynomial ambient) (sheet : Fin 2) :
    (ownerBoundarySwapLift state sheet).cellCount = 4 := rfl

/-- Close a two-bank cut using shrinking winding-one boundary loops at both
finite endpoints, rather than zero-length swaps at nonbranch rational
anchors. -/
def doubleLiftWithBoundaryOwners
    {polynomial : GaussianPolynomial} {ambient : Box}
    {leftAmbient rightAmbient : Box}
    (leftState : WindingOneState polynomial leftAmbient)
    (rightState : WindingOneState polynomial rightAmbient)
    (path : ClearPath polynomial ambient
      leftState.box.anchor rightState.box.anchor) : ClosedLiftedPath 2 := by
  let startZero : LiftedPoint 2 :=
    { coordinate := leftState.box.anchor, sheet := 0 }
  let finishZero : LiftedPoint 2 :=
    { coordinate := rightState.box.anchor, sheet := 0 }
  let finishOne : LiftedPoint 2 :=
    { coordinate := rightState.box.anchor, sheet := 1 }
  let startOne : LiftedPoint 2 :=
    { coordinate := leftState.box.anchor, sheet := 1 }
  let forward : LiftedPath 2 startZero finishZero :=
    CCL.Riemann.BranchCutLifts.ClearPath.liftOnSheet 0 path
  let rightSwap : LiftedPath 2 finishZero finishOne :=
    ownerBoundarySwapLift rightState 0
  let backward : LiftedPath 2 finishOne startOne :=
    CCL.Riemann.BranchCutLifts.ClearPath.liftOnSheet 1
      (CCL.Riemann.BranchCutLifts.ClearPath.reverse path)
  let leftSwap : LiftedPath 2 startOne startZero :=
    ownerBoundarySwapLift leftState 1
  exact
    { basepoint := startZero
      path := forward.append
        (rightSwap.append (backward.append leftSwap)) }

@[simp] theorem doubleLiftWithBoundaryOwners_cellCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {leftAmbient rightAmbient : Box}
    (leftState : WindingOneState polynomial leftAmbient)
    (rightState : WindingOneState polynomial rightAmbient)
    (path : ClearPath polynomial ambient
      leftState.box.anchor rightState.box.anchor) :
    (doubleLiftWithBoundaryOwners leftState rightState path).cellCount =
      2 * path.segmentCount + 8 := by
  simp only [doubleLiftWithBoundaryOwners, ClosedLiftedPath.cellCount,
    LiftedPath.cellCount_append, ClearPath.liftOnSheet_cellCount,
    ClearPath.segmentCount_reverse, ownerBoundarySwapLift,
    LiftedPath.cellCount]
  omega0

/-- The canonical closed two-bank lift of one finite clear cut path. -/
def doubleLift {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish) :
    ClosedLiftedPath 2 := by
  let startZero : LiftedPoint 2 := { coordinate := start, sheet := 0 }
  let finishZero : LiftedPoint 2 := { coordinate := finish, sheet := 0 }
  let finishOne : LiftedPoint 2 := { coordinate := finish, sheet := 1 }
  let startOne : LiftedPoint 2 := { coordinate := start, sheet := 1 }
  let forward : LiftedPath 2 startZero finishZero :=
    CCL.Riemann.BranchCutLifts.ClearPath.liftOnSheet 0 path
  let switchAtFinish : LiftedPath 2 finishZero finishOne :=
    .cons (switchCell finish 0) (.nil finishOne)
  let backward : LiftedPath 2 finishOne startOne :=
    CCL.Riemann.BranchCutLifts.ClearPath.liftOnSheet 1
      (CCL.Riemann.BranchCutLifts.ClearPath.reverse path)
  let switchAtStart : LiftedPath 2 startOne startZero :=
    .cons (switchCell start 1) (.nil startZero)
  exact
    { basepoint := startZero
      path := forward.append
        (switchAtFinish.append (backward.append switchAtStart)) }

@[simp] theorem doubleLift_cellCount
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (path : ClearPath polynomial ambient start finish) :
    (doubleLift path).cellCount = 2 * path.segmentCount + 2 := by
  simp only [doubleLift, ClosedLiftedPath.cellCount,
    LiftedPath.cellCount_append, ClearPath.liftOnSheet_cellCount,
    ClearPath.segmentCount_reverse, LiftedPath.cellCount]
  omega0

/-- The finite lifted loop associated to one requested root-box refinement.
For finite branch sites, both switching endpoints follow the deterministic
nested owner anchors.  Thus the persistent family approaches the actual
ramification names instead of repeatedly switching at one fixed rational
surrogate. -/
def Geometry.closedLiftAt {genus : Nat}
    {curve : HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve}
    (geometry : Geometry curve branches) (refinement : Nat) :
    ClosedLiftedPath 2 := by
  rcases geometry with ⟨leftSite, rightSite, different, certificate⟩
  cases certificate with
  | finite left right different degreeGtOne path =>
      exact doubleLiftWithBoundaryOwners
        (refinedState branches degreeGtOne left refinement)
        (refinedState branches degreeGtOne right refinement)
        (finiteConnectorAt branches degreeGtOne left right refinement)
  | toInfinity finite degreeGtOne exit =>
      exact doubleLift
        (infinityExitAt branches degreeGtOne finite refinement).path
  | fromInfinity finite degreeGtOne exit =>
      exact doubleLift
        (infinityExitAt branches degreeGtOne finite refinement).path
  | linearToInfinity finite degreeOne =>
      let basepoint : LiftedPoint 2 :=
        { coordinate := branches.anchor finite, sheet := 0 }
      exact { basepoint := basepoint, path := .nil basepoint }
  | infinityToLinear finite degreeOne =>
      let basepoint : LiftedPoint 2 :=
        { coordinate := branches.anchor finite, sheet := 0 }
      exact { basepoint := basepoint, path := .nil basepoint }

/-- If both semantic endpoints of a cut are displayed finite occurrences,
its requested lift reduces to the canonical owner-boundary construction on
those exact occurrences. -/
theorem Geometry.closedLiftAt_of_finite {genus : Nat}
    {curve : HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve}
    (geometry : Geometry curve branches)
    (left right : BranchIsolation.Data.Index branches)
    (left_eq : geometry.leftSite = .finite left)
    (right_eq : geometry.rightSite = .finite right)
    (degreeGtOne : 1 < curve.polynomial.natDegree)
    (refinement : Nat) :
    CCL.Riemann.BranchCutLifts.Geometry.closedLiftAt geometry refinement =
      doubleLiftWithBoundaryOwners
        (refinedState branches degreeGtOne left refinement)
        (refinedState branches degreeGtOne right refinement)
        (finiteConnectorAt branches degreeGtOne left right refinement) := by
  rcases geometry with ⟨leftSite, rightSite, different, certificate⟩
  cases certificate with
  | finite actualLeft actualRight actualDifferent actualHigher path =>
      have leftEqual : actualLeft = left := by
        exact BranchConfiguration.Site.finite.inj left_eq
      have rightEqual : actualRight = right := by
        exact BranchConfiguration.Site.finite.inj right_eq
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
    {curve : HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve}
    (geometry : Geometry curve branches) : ClosedLiftedPath 2 :=
  CCL.Riemann.BranchCutLifts.Geometry.closedLiftAt geometry 0

/-- The cut lift is a persistent finite cycle: every request refers to the
same labelled combinatorial loop while its branch endpoints follow nested
winding boxes. -/
def Geometry.liftedCycle {genus : Nat}
    {curve : HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve}
    (geometry : Geometry curve branches) : LiftedCycleRefinement 2 where
  liftedPath := fun refinement =>
    CCL.Riemann.BranchCutLifts.Geometry.closedLiftAt geometry refinement

/-- Every cut has a finite branch-box representative.  For a cut to
infinity this is its unique finite endpoint. -/
def Geometry.finiteRepresentative {genus : Nat}
    {curve : HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve}
    (geometry : Geometry curve branches) : BranchIsolation.Data.Index branches := by
  rcases geometry with ⟨leftSite, rightSite, different, certificate⟩
  cases certificate with
  | finite left => exact left
  | toInfinity finite => exact finite
  | fromInfinity finite => exact finite
  | linearToInfinity finite => exact finite
  | infinityToLinear finite => exact finite

/-- The complete finite family of `g+1` lifted branch-cut loops. -/
structure Family {genus : Nat} (curve : HyperellipticCurve genus) where
  cuts : System curve
  cycleAt : Fin (genus + 1) -> LiftedCycleRefinement 2
  cycle_eq : forall index, cycleAt index =
    CCL.Riemann.BranchCutLifts.Geometry.liftedCycle (cuts.cutAt index)

def familyOfCuts {genus : Nat} (curve : HyperellipticCurve genus)
    (cuts : BranchCuts.System curve) : Family curve :=
  { cuts := cuts
    cycleAt := fun index =>
      CCL.Riemann.BranchCutLifts.Geometry.liftedCycle (cuts.cutAt index)
    cycle_eq := fun _ => rfl }

/-- Construct the lifted standard cut family directly from explicit
degree-complete branch data. -/
def familyOfData {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) : Family curve :=
  familyOfCuts curve (BranchCuts.systemOfData curve branches)

/-- Fully automatic lifted branch-cut family. -/
def family {genus : Nat} (curve : HyperellipticCurve genus) : Family curve :=
  familyOfCuts curve (BranchCuts.system curve)

/-- Every lifted cut returns to its starting sheet by its explicit composite
transport. -/
theorem Family.returns_to_startingSheet {genus : Nat}
    {curve : HyperellipticCurve genus} (family : Family curve)
    (index : Fin (genus + 1)) (refinement : Nat) :
    ((family.cycleAt index).liftedPath refinement).path.sheetTransport.forward
        ((family.cycleAt index).liftedPath refinement).basepoint.sheet =
      ((family.cycleAt index).liftedPath refinement).basepoint.sheet :=
  ((family.cycleAt index).liftedPath refinement).returns_to_startingSheet

/-- The existence of a homology-basis index forces the defining polynomial
to have degree greater than one in either admitted hyperelliptic shape. -/
theorem degreeGtOne_of_cycleIndex {genus : Nat}
    (curve : HyperellipticCurve genus) (index : Fin genus) :
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

/-- A constant persistent cycle from one displayed finite lifted path.  This
remains useful only for genuinely constant auxiliary paths. -/
def constantCycle (path : ClosedLiftedPath 2) : LiftedCycleRefinement 2 where
  liftedPath := fun _ => path

/-- The `b_i` path joins cut `i` to the final reference cut, travels on the
other sheet on its return, and closes by the two local sheet swaps. -/
def Family.basisBridgeCycle {genus : Nat}
    {curve : HyperellipticCurve genus} (family : Family curve)
    (index : Fin genus) : LiftedCycleRefinement 2 := by
  let higher := degreeGtOne_of_cycleIndex curve index
  let branches := family.cuts.configuration.branches
  let sourceCut := family.cuts.cutAt (basisCutIndex index)
  let targetCut := family.cuts.cutAt (referenceCutIndex genus)
  let source :=
    CCL.Riemann.BranchCutLifts.Geometry.finiteRepresentative sourceCut
  let target :=
    CCL.Riemann.BranchCutLifts.Geometry.finiteRepresentative targetCut
  exact
    { liftedPath := fun refinement =>
        doubleLift
          (finiteConnectorAt branches higher source target refinement) }

/-- Automatically constructed lifted representatives of the standard
symplectic cut basis: `a_i` surrounds cut `i`, while `b_i` joins it to the
last cut on the two opposite sheets. -/
def Family.symplecticCycles {genus : Nat}
    {curve : HyperellipticCurve genus} (family : Family curve) :
    LiftedSymplecticCycles 2 genus where
  aCycle := fun index => family.cycleAt (basisCutIndex index)
  bCycle := fun index => family.basisBridgeCycle index

@[simp] theorem Family.symplecticCycles_aCycle {genus : Nat}
    {curve : HyperellipticCurve genus} (family : Family curve)
    (index : Fin genus) :
    family.symplecticCycles.aCycle index =
      family.cycleAt (basisCutIndex index) := rfl

@[simp] theorem Family.symplecticCycles_bCycle {genus : Nat}
    {curve : HyperellipticCurve genus} (family : Family curve)
    (index : Fin genus) :
    family.symplecticCycles.bCycle index =
      family.basisBridgeCycle index := rfl

/-- The canonical A-cycle at every finite request is the explicit
owner-boundary lift between the two finite root occurrences of its standard
basis pair. -/
theorem canonicalACycle_liftedPath_ofData {genus : Nat}
    (curve : HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) (index : Fin genus)
    (refinement : Nat) :
    ((familyOfData curve branches).symplecticCycles.aCycle index).liftedPath
        refinement =
      doubleLiftWithBoundaryOwners
        (refinedState
          (BranchConfiguration.configurationOfData curve branches).branches
          (degreeGtOne_of_cycleIndex curve index)
          (BranchConfiguration.basisPairLeftIndexOfData curve branches index)
          refinement)
        (refinedState
          (BranchConfiguration.configurationOfData curve branches).branches
          (degreeGtOne_of_cycleIndex curve index)
          (BranchConfiguration.basisPairRightIndexOfData curve branches index)
          refinement)
        (finiteConnectorAt
          (BranchConfiguration.configurationOfData curve branches).branches
          (degreeGtOne_of_cycleIndex curve index)
          (BranchConfiguration.basisPairLeftIndexOfData curve branches index)
          (BranchConfiguration.basisPairRightIndexOfData curve branches index)
          refinement) := by
  let cuts := BranchCuts.systemOfData curve branches
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
        simpa only [cuts, BranchCuts.systemOfData,
          BranchCuts.systemOfConfiguration, basisCutIndex] using
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
        simpa only [cuts, BranchCuts.systemOfData,
          BranchCuts.systemOfConfiguration, basisCutIndex] using
          BranchConfiguration.configurationOfData_siteAt_basisPair_right
            curve branches index
  change CCL.Riemann.BranchCutLifts.Geometry.closedLiftAt cut refinement = _
  exact Geometry.closedLiftAt_of_finite cut
    (BranchConfiguration.basisPairLeftIndexOfData curve branches index)
    (BranchConfiguration.basisPairRightIndexOfData curve branches index)
    leftSite rightSite (degreeGtOne_of_cycleIndex curve index) refinement

/-- The automatic specialization of
`canonicalACycle_liftedPath_ofData`. -/
theorem canonicalACycle_liftedPath {genus : Nat}
    (curve : HyperellipticCurve genus) (index : Fin genus)
    (refinement : Nat) :
    ((family curve).symplecticCycles.aCycle index).liftedPath refinement =
      doubleLiftWithBoundaryOwners
        (refinedState (BranchConfiguration.configuration curve).branches
          (degreeGtOne_of_cycleIndex curve index)
          (BranchConfiguration.basisPairLeftIndex curve index) refinement)
        (refinedState (BranchConfiguration.configuration curve).branches
          (degreeGtOne_of_cycleIndex curve index)
          (BranchConfiguration.basisPairRightIndex curve index) refinement)
        (finiteConnectorAt
          (BranchConfiguration.configuration curve).branches
          (degreeGtOne_of_cycleIndex curve index)
          (BranchConfiguration.basisPairLeftIndex curve index)
          (BranchConfiguration.basisPairRightIndex curve index) refinement) := by
  let cuts := BranchCuts.system curve
  let cut := cuts.cutAt (basisCutIndex index)
  have leftSite : cut.leftSite =
      .finite (BranchConfiguration.basisPairLeftIndex curve index) := by
    calc
      cut.leftSite = cuts.configuration.siteAt
          (BranchConfiguration.standardPair (basisCutIndex index)).left :=
        cuts.left_eq (basisCutIndex index)
      _ = .finite (BranchConfiguration.basisPairLeftIndex curve index) := by
        simpa only [cuts, BranchCuts.system,
          BranchCuts.systemOfConfiguration, basisCutIndex] using
          BranchConfiguration.configuration_siteAt_basisPair_left curve index
  have rightSite : cut.rightSite =
      .finite (BranchConfiguration.basisPairRightIndex curve index) := by
    calc
      cut.rightSite = cuts.configuration.siteAt
          (BranchConfiguration.standardPair (basisCutIndex index)).right :=
        cuts.right_eq (basisCutIndex index)
      _ = .finite (BranchConfiguration.basisPairRightIndex curve index) := by
        simpa only [cuts, BranchCuts.system,
          BranchCuts.systemOfConfiguration, basisCutIndex] using
          BranchConfiguration.configuration_siteAt_basisPair_right curve index
  change
    CCL.Riemann.BranchCutLifts.Geometry.closedLiftAt cut refinement = _
  exact Geometry.closedLiftAt_of_finite cut
    (BranchConfiguration.basisPairLeftIndex curve index)
    (BranchConfiguration.basisPairRightIndex curve index)
    leftSite rightSite (degreeGtOne_of_cycleIndex curve index) refinement

/-! ## Finite cellular traces of the constructed basis words -/

/-- Syntax of the two finite geometric constructions used for the basis.
Keeping this tag prevents a later analytic refinement from silently changing
which cellular class a path represents. -/
inductive BasisWord (genus : Nat)
  | a (index : Fin genus)
  | b (index : Fin genus)

namespace BasisWord

/-- The exact cellular homology coordinate carried by a construction tag. -/
def trace {genus : Nat} : BasisWord genus ->
    CCL.Riemann.CellularHomology.FirstHomology genus
  | .a index => CCL.Riemann.CellularHomology.aCycle index
  | .b index => CCL.Riemann.CellularHomology.bCycle index

/-- Realize the tagged word by the corresponding automatically constructed
sheet-aware path. -/
def realize {genus : Nat} {curve : HyperellipticCurve genus}
    (family : Family curve) : BasisWord genus -> LiftedCycleRefinement 2
  | .a index => family.cycleAt (basisCutIndex index)
  | .b index => family.basisBridgeCycle index

theorem intersection_a_a {genus : Nat} (left right : Fin genus) :
    CCL.Riemann.CellularHomology.intersection
      (trace (.a left)) (trace (.a right)) = 0 :=
  CCL.Riemann.CellularHomology.intersection_a_a left right

theorem intersection_b_b {genus : Nat} (left right : Fin genus) :
    CCL.Riemann.CellularHomology.intersection
      (trace (.b left)) (trace (.b right)) = 0 :=
  CCL.Riemann.CellularHomology.intersection_b_b left right

theorem intersection_a_b {genus : Nat} (left right : Fin genus) :
    CCL.Riemann.CellularHomology.intersection
      (trace (.a left)) (trace (.b right)) =
        if left = right then 1 else 0 :=
  CCL.Riemann.CellularHomology.intersection_a_b left right

end BasisWord

/-- Fully constructed lifted basis together with its finite cellular trace
map and symplectic intersection identities. -/
structure SymplecticBasis {genus : Nat}
    (curve : HyperellipticCurve genus) where
  family : Family curve
  cycles : LiftedSymplecticCycles 2 genus
  cycles_eq : cycles = family.symplecticCycles
  aTrace : Fin genus -> CCL.Riemann.CellularHomology.FirstHomology genus
  bTrace : Fin genus -> CCL.Riemann.CellularHomology.FirstHomology genus
  aTrace_eq : forall index, aTrace index = BasisWord.trace (.a index)
  bTrace_eq : forall index, bTrace index = BasisWord.trace (.b index)
  a_a : forall left right,
    CCL.Riemann.CellularHomology.intersection
      (aTrace left) (aTrace right) = 0
  b_b : forall left right,
    CCL.Riemann.CellularHomology.intersection
      (bTrace left) (bTrace right) = 0
  a_b : forall left right,
    CCL.Riemann.CellularHomology.intersection
      (aTrace left) (bTrace right) =
        if left = right then 1 else 0

def symplecticBasisOfFamily {genus : Nat} (curve : HyperellipticCurve genus)
    (family : Family curve) : SymplecticBasis curve := by
  exact
    { family := family
      cycles := family.symplecticCycles
      cycles_eq := rfl
      aTrace := fun index => BasisWord.trace (.a index)
      bTrace := fun index => BasisWord.trace (.b index)
      aTrace_eq := fun _ => rfl
      bTrace_eq := fun _ => rfl
      a_a := BasisWord.intersection_a_a
      b_b := BasisWord.intersection_b_b
      a_b := BasisWord.intersection_a_b }

/-- Fully constructed finite symplectic basis from explicit degree-complete
branch data. -/
def symplecticBasisOfData {genus : Nat} (curve : HyperellipticCurve genus)
    (branches : BranchIsolation.Data curve) : SymplecticBasis curve :=
  symplecticBasisOfFamily curve (familyOfData curve branches)

/-- Fully automatic finite symplectic branch-cut basis. -/
def symplecticBasis {genus : Nat} (curve : HyperellipticCurve genus) :
    SymplecticBasis curve :=
  symplecticBasisOfFamily curve (BranchCutLifts.family curve)

end CCL.Riemann.BranchCutLifts
