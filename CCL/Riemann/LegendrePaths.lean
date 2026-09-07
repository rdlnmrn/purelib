import CCL.Knot.ProjectedCrossings
import CCL.Progressive.FiniteMonodromy

/-!
# Certified finite paths in the Legendre parameter plane

The Legendre family is represented by the exact dense polynomial
`x * (x - 1) * (x - lambda)`.  Axis-aligned parameter segments carry finite
rational clearances from the singular parameters zero and one.  A certified
segment then adds the existing simple-root chamber overlap, an extracted
three-strand braid word, and a common lower bound for all bridge clearances.
-/

namespace CCL.Riemann.LegendrePaths

open CCL.Knot.FiniteBraid

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev ChamberFrame := CCL.FiniteMonodromy.ChamberFrame
abbrev ChamberOverlap := CCL.FiniteMonodromy.ChamberOverlap
abbrev FiniteBijection := CCL.FiniteMonodromy.FiniteBijection
abbrev ProjectedFrame := CCL.Knot.ProjectedCrossings.ProjectedFrame
abbrev ProjectedOverlap {strands : Nat}
    (start finish : ProjectedFrame strands) :=
  CCL.Knot.ProjectedCrossings.ProjectedOverlap start finish

def gaussian (real imaginary : Coordinate) : Gaussian :=
  ⟨real, imaginary⟩

/-- Exact high-to-low coefficient representation of
`x * (x - 1) * (x - lambda)`. -/
def polynomial (lambda : Gaussian) : GaussianPolynomial :=
  ⟨[1, -(1 + lambda), lambda, 0]⟩

@[simp] theorem polynomial_isZero (lambda : Gaussian) :
    (polynomial lambda).isZero = false := rfl

@[simp] theorem polynomial_natDegree (lambda : Gaussian) :
    (polynomial lambda).natDegree = 3 := rfl

theorem polynomial_eval (lambda point : Gaussian) :
    (polynomial lambda).eval point =
      point * (point - 1) * (point - lambda) := by
  unfold polynomial RFAP.ComputablePolynomial.DensePolynomial.eval
    RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs
  simp only [List.foldl_cons, List.foldl_nil]
  ring1

@[simp] theorem polynomial_zero (lambda : Gaussian) :
    (polynomial lambda).eval 0 = 0 := by
  rw [polynomial_eval]
  ring1

@[simp] theorem polynomial_one (lambda : Gaussian) :
    (polynomial lambda).eval 1 = 0 := by
  rw [polynomial_eval]
  ring1

@[simp] theorem polynomial_lambda (lambda : Gaussian) :
    (polynomial lambda).eval lambda = 0 := by
  rw [polynomial_eval]
  ring1

/-- Logical order of the finite branch points.  At a real base parameter
between zero and one this is their geometric order `0, lambda, 1`. -/
def branchPoint (lambda : Gaussian) (label : Fin 3) : Gaussian :=
  if label = 0 then 0 else if label = 1 then lambda else 1

@[simp] theorem branchPoint_zero (lambda : Gaussian) :
    branchPoint lambda 0 = 0 := rfl

@[simp] theorem branchPoint_one (lambda : Gaussian) :
    branchPoint lambda 1 = lambda := rfl

@[simp] theorem branchPoint_two (lambda : Gaussian) :
    branchPoint lambda 2 = 1 := rfl

/-! ## Exact axis-aligned parameter geometry -/

inductive AxisSegment : Gaussian -> Gaussian -> Type
  | horizontal (xStart xFinish y : Coordinate) :
      AxisSegment (gaussian xStart y) (gaussian xFinish y)
  | vertical (x yStart yFinish : Coordinate) :
      AxisSegment (gaussian x yStart) (gaussian x yFinish)

namespace AxisSegment

def pointAt {start finish : Gaussian}
    (segment : AxisSegment start finish) (parameter : Coordinate) : Gaussian :=
  match segment with
  | .horizontal xStart xFinish y =>
      gaussian (xStart + (xFinish - xStart) * parameter) y
  | .vertical x yStart yFinish =>
      gaussian x (yStart + (yFinish - yStart) * parameter)

@[simp] theorem pointAt_zero {start finish : Gaussian}
    (segment : AxisSegment start finish) : segment.pointAt 0 = start := by
  cases segment with
  | horizontal xStart xFinish y =>
      apply RFAP.ConstructiveGaussian.Gaussian.ext
      · change xStart + (xFinish - xStart) * 0 = xStart
        ring1
      · rfl
  | vertical x yStart yFinish =>
      apply RFAP.ConstructiveGaussian.Gaussian.ext
      · rfl
      · change yStart + (yFinish - yStart) * 0 = yStart
        ring1

@[simp] theorem pointAt_one {start finish : Gaussian}
    (segment : AxisSegment start finish) : segment.pointAt 1 = finish := by
  cases segment with
  | horizontal xStart xFinish y =>
      apply RFAP.ConstructiveGaussian.Gaussian.ext
      · change xStart + (xFinish - xStart) * 1 = xFinish
        ring1
      · rfl
  | vertical x yStart yFinish =>
      apply RFAP.ConstructiveGaussian.Gaussian.ext
      · rfl
      · change yStart + (yFinish - yStart) * 1 = yFinish
        ring1

def reverse {start finish : Gaussian}
    (segment : AxisSegment start finish) : AxisSegment finish start :=
  match segment with
  | .horizontal xStart xFinish y => .horizontal xFinish xStart y
  | .vertical x yStart yFinish => .vertical x yFinish yStart

@[simp] theorem reverse_reverse {start finish : Gaussian}
    (segment : AxisSegment start finish) : segment.reverse.reverse = segment := by
  cases segment <;> rfl

/-- Squared fixed-coordinate gap from an excluded point.  It is independent
of the segment parameter and hence certifies the entire segment. -/
def fixedGapSq {start finish : Gaussian}
    (segment : AxisSegment start finish) (excluded : Gaussian) : Coordinate :=
  match segment with
  | .horizontal _ _ y => (y - excluded.im) ^ 2
  | .vertical x _ _ => (x - excluded.re) ^ 2

@[simp] theorem fixedGapSq_reverse {start finish : Gaussian}
    (segment : AxisSegment start finish) (excluded : Gaussian) :
    segment.reverse.fixedGapSq excluded = segment.fixedGapSq excluded := by
  cases segment <;> rfl

/-- A positive rational lower bound obtained from the coordinate fixed along
an axis-aligned segment. -/
structure Clearance {start finish : Gaussian}
    (segment : AxisSegment start finish) (excluded : Gaussian) where
  bound : Coordinate
  positive : 0 < bound
  lower : bound <= segment.fixedGapSq excluded

theorem Clearance.normSq_lower {start finish : Gaussian}
    {segment : AxisSegment start finish} {excluded : Gaussian}
    (clearance : Clearance segment excluded) (parameter : Coordinate) :
    clearance.bound <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
        (segment.pointAt parameter - excluded) := by
  cases segment with
  | horizontal xStart xFinish y =>
      change clearance.bound <=
        (xStart + (xFinish - xStart) * parameter - excluded.re) ^ 2 +
          (y - excluded.im) ^ 2
      exact clearance.lower.trans
        (le_add_of_nonneg_left
          (RFAP.ConstructiveFraction.sq_nonneg_direct
            (xStart + (xFinish - xStart) * parameter - excluded.re)))
  | vertical x yStart yFinish =>
      change clearance.bound <=
        (x - excluded.re) ^ 2 +
          (yStart + (yFinish - yStart) * parameter - excluded.im) ^ 2
      exact clearance.lower.trans
        (le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.sq_nonneg_direct
            (yStart + (yFinish - yStart) * parameter - excluded.im)))

def Clearance.reverse {start finish : Gaussian}
    {segment : AxisSegment start finish} {excluded : Gaussian}
    (clearance : Clearance segment excluded) :
    Clearance segment.reverse excluded where
  bound := clearance.bound
  positive := clearance.positive
  lower := by rw [fixedGapSq_reverse]; exact clearance.lower

/-- The exact geometric portion of a Legendre segment. -/
structure Safe {start finish : Gaussian}
    (segment : AxisSegment start finish) where
  avoidsZero : Clearance segment 0
  avoidsOne : Clearance segment 1

def Safe.reverse {start finish : Gaussian}
    {segment : AxisSegment start finish} (safe : Safe segment) :
    Safe segment.reverse where
  avoidsZero := safe.avoidsZero.reverse
  avoidsOne := safe.avoidsOne.reverse

end AxisSegment

/-- A finite geometric path whose every segment carries exact avoidance of
both singular parameters. -/
inductive SafePath : (start finish : Gaussian) -> Type
  | nil (point : Gaussian) : SafePath point point
  | cons {start middle finish : Gaussian}
      (segment : AxisSegment start middle)
      (safe : AxisSegment.Safe segment)
      (remaining : SafePath middle finish) : SafePath start finish

namespace SafePath

def stepCount : {start finish : Gaussian} -> SafePath start finish -> Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ _ remaining => remaining.stepCount + 1

def append {first middle last : Gaussian}
    (initial : SafePath first middle) (remaining : SafePath middle last) :
    SafePath first last :=
  match initial with
  | .nil _ => remaining
  | .cons segment safe tail => .cons segment safe (tail.append remaining)

def reverse : {start finish : Gaussian} ->
    SafePath start finish -> SafePath finish start
  | _, _, .nil point => .nil point
  | start, _, .cons segment safe remaining =>
      remaining.reverse.append
        (.cons segment.reverse safe.reverse (.nil start))

end SafePath

/-! ## Executable rational rectangle examples -/

namespace RectangleExamples

def quarter : Coordinate := 1 / 4
def threeQuarters : Coordinate := 3 / 4
def fiveQuarters : Coordinate := 5 / 4
def negativeQuarter : Coordinate := -(1 / 4)
def sixteenth : Coordinate := 1 / 16

def zeroNorthEast : Gaussian := gaussian quarter quarter
def zeroNorthWest : Gaussian := gaussian negativeQuarter quarter
def zeroSouthWest : Gaussian := gaussian negativeQuarter negativeQuarter
def zeroSouthEast : Gaussian := gaussian quarter negativeQuarter

def zeroTop : AxisSegment zeroNorthEast zeroNorthWest :=
  .horizontal quarter negativeQuarter quarter

def zeroLeft : AxisSegment zeroNorthWest zeroSouthWest :=
  .vertical negativeQuarter quarter negativeQuarter

def zeroBottom : AxisSegment zeroSouthWest zeroSouthEast :=
  .horizontal negativeQuarter quarter negativeQuarter

def zeroRight : AxisSegment zeroSouthEast zeroNorthEast :=
  .vertical quarter negativeQuarter quarter

def clearanceSixteenth {start finish excluded : Gaussian}
    (segment : AxisSegment start finish)
    (lower : sixteenth <= segment.fixedGapSq excluded) :
    AxisSegment.Clearance segment excluded where
  bound := sixteenth
  positive := by decide
  lower := lower

def zeroTopSafe : AxisSegment.Safe zeroTop where
  avoidsZero := clearanceSixteenth zeroTop (by decide)
  avoidsOne := clearanceSixteenth zeroTop (by decide)

def zeroLeftSafe : AxisSegment.Safe zeroLeft where
  avoidsZero := clearanceSixteenth zeroLeft (by decide)
  avoidsOne := clearanceSixteenth zeroLeft (by decide)

def zeroBottomSafe : AxisSegment.Safe zeroBottom where
  avoidsZero := clearanceSixteenth zeroBottom (by decide)
  avoidsOne := clearanceSixteenth zeroBottom (by decide)

def zeroRightSafe : AxisSegment.Safe zeroRight where
  avoidsZero := clearanceSixteenth zeroRight (by decide)
  avoidsOne := clearanceSixteenth zeroRight (by decide)

def zeroRectangle : SafePath zeroNorthEast zeroNorthEast :=
  .cons zeroTop zeroTopSafe
    (.cons zeroLeft zeroLeftSafe
      (.cons zeroBottom zeroBottomSafe
        (.cons zeroRight zeroRightSafe (.nil zeroNorthEast))))

@[simp] theorem zeroRectangle_stepCount : zeroRectangle.stepCount = 4 := rfl

def oneNorthEast : Gaussian := gaussian fiveQuarters quarter
def oneNorthWest : Gaussian := gaussian threeQuarters quarter
def oneSouthWest : Gaussian := gaussian threeQuarters negativeQuarter
def oneSouthEast : Gaussian := gaussian fiveQuarters negativeQuarter

def oneTop : AxisSegment oneNorthEast oneNorthWest :=
  .horizontal fiveQuarters threeQuarters quarter

def oneLeft : AxisSegment oneNorthWest oneSouthWest :=
  .vertical threeQuarters quarter negativeQuarter

def oneBottom : AxisSegment oneSouthWest oneSouthEast :=
  .horizontal threeQuarters fiveQuarters negativeQuarter

def oneRight : AxisSegment oneSouthEast oneNorthEast :=
  .vertical fiveQuarters negativeQuarter quarter

def oneTopSafe : AxisSegment.Safe oneTop where
  avoidsZero := clearanceSixteenth oneTop (by decide)
  avoidsOne := clearanceSixteenth oneTop (by decide)

def oneLeftSafe : AxisSegment.Safe oneLeft where
  avoidsZero := clearanceSixteenth oneLeft (by decide)
  avoidsOne := clearanceSixteenth oneLeft (by decide)

def oneBottomSafe : AxisSegment.Safe oneBottom where
  avoidsZero := clearanceSixteenth oneBottom (by decide)
  avoidsOne := clearanceSixteenth oneBottom (by decide)

def oneRightSafe : AxisSegment.Safe oneRight where
  avoidsZero := clearanceSixteenth oneRight (by decide)
  avoidsOne := clearanceSixteenth oneRight (by decide)

def oneRectangle : SafePath oneNorthEast oneNorthEast :=
  .cons oneTop oneTopSafe
    (.cons oneLeft oneLeftSafe
      (.cons oneBottom oneBottomSafe
        (.cons oneRight oneRightSafe (.nil oneNorthEast))))

@[simp] theorem oneRectangle_stepCount : oneRectangle.stepCount = 4 := rfl

example (parameter : Coordinate) :
    zeroTopSafe.avoidsZero.bound <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
      (zeroTop.pointAt parameter) :=
  by
    simpa only [RFAP.ConstructiveGaussian.Gaussian.sub_zero] using
      zeroTopSafe.avoidsZero.normSq_lower parameter

example (parameter : Coordinate) :
    oneLeftSafe.avoidsOne.bound <=
      RFAP.ConstructiveGaussian.Gaussian.normSq
      (oneLeft.pointAt parameter - 1) :=
  oneLeftSafe.avoidsOne.normSq_lower parameter

end RectangleExamples

/-! ## Root frames and certified coefficient segments -/

/-- A Legendre chamber frame with a displayed logical identification of its
three finite roots as `0`, `lambda`, and `1`. -/
structure Frame (lambda : Gaussian) where
  chamber : ChamberFrame
  polynomial_eq : chamber.polynomial = polynomial lambda
  labels : FiniteBijection 3 chamber.degree
  owner_contains : forall label : Fin 3,
    (chamber.owner (labels.forward label)).box.Contains
      (branchPoint lambda label)
  projectionOrder : FiniteBijection 3 chamber.degree
  projectionOwner : Fin 3 -> CCL.ProgressivePolynomialRoots.LocalOwner
    chamber.polynomial
  projection_refines : forall position : Fin 3,
    (projectionOwner position).box.Refines
      (chamber.owner (projectionOrder.forward position)).box
  projection_xOrdered : forall left right : Fin 3, left.val < right.val ->
    (projectionOwner left).box.xUpper < (projectionOwner right).box.xLower

namespace Frame

/-- The chamber degree is exactly the displayed Legendre cubic degree. -/
theorem degree_eq_three {lambda : Gaussian} (frame : Frame lambda) :
    frame.chamber.degree = 3 := by
  calc
    frame.chamber.degree = frame.chamber.polynomial.natDegree :=
      frame.chamber.reference.polynomial_natDegree.symm
    _ = (polynomial lambda).natDegree :=
      congrArg RFAP.ComputablePolynomial.DensePolynomial.natDegree
        frame.polynomial_eq
    _ = 3 := polynomial_natDegree lambda

/-- The independently certified left-to-right projection order on this
Legendre root frame. -/
def projected {lambda : Gaussian} (frame : Frame lambda) : ProjectedFrame 3 where
  chamber := frame.chamber
  degree_eq := frame.degree_eq_three
  orderToOwner := frame.projectionOrder
  sampleOwner := frame.projectionOwner
  sample_refines_owner := frame.projection_refines
  xOrdered := frame.projection_xOrdered

theorem rootSeparation {lambda : Gaussian} (frame : Frame lambda)
    (left right : Fin 3) (different : left ≠ right) :
    (frame.chamber.owner (frame.labels.forward left)).box.Separated
      (frame.chamber.owner (frame.labels.forward right)).box :=
  frame.chamber.pairwiseSeparated _ _
    (fun equal => different (frame.labels.forward_injective equal))

end Frame

/-- A common positive rational lower bound for every owner bridge at both
ends of one chamber overlap.  These are the finite square-root continuation
clearances retained by the segment. -/
structure BridgeClearance {start finish : Gaussian}
    (left : Frame start) (right : Frame finish)
    (overlap : ChamberOverlap left.chamber right.chamber) where
  bound : Coordinate
  positive : 0 < bound
  leftLower : forall index : left.chamber.Index,
    bound <= (overlap.bridge index).leftClearance.bound
  rightLower : forall index : left.chamber.Index,
    bound <= (overlap.bridge index).rightClearance.bound

/-- One fully certified Legendre parameter segment. -/
structure Segment {start finish : Gaussian}
    (left : Frame start) (right : Frame finish) where
  geometry : AxisSegment start finish
  safe : AxisSegment.Safe geometry
  projection : ProjectedOverlap left.projected right.projected
  sheetClearance : BridgeClearance left right projection.chamberOverlap

namespace Segment

/-- Construct a segment only from an atomic projected overlap.  Its braid
word is extracted from the certified stationary/crossing event rather than
accepted as an independent annotation. -/
def ofProjectedOverlap {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (geometry : AxisSegment start finish) (safe : AxisSegment.Safe geometry)
    (projection : ProjectedOverlap left.projected right.projected)
    (clearance : BridgeClearance left right projection.chamberOverlap) :
    Segment left right where
  geometry := geometry
  safe := safe
  projection := projection
  sheetClearance := clearance

/-- The root-owner overlap underlying the certified projected event. -/
def coefficientOverlap {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (segment : Segment left right) : ChamberOverlap left.chamber right.chamber :=
  segment.projection.chamberOverlap

/-- The segment word is the output of its finite projected crossing chart. -/
def crossings {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (segment : Segment left right) : Word 3 :=
  segment.projection.word

/-- The source owner at one certified projection position. -/
def startOwnerIndex {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (_segment : Segment left right) (position : Fin 3) :
    left.chamber.Index :=
  left.projected.ownerIndex position

def reverseBridgeClearance {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    {overlap : ChamberOverlap left.chamber right.chamber}
    (clearance : BridgeClearance left right overlap) :
    BridgeClearance right left overlap.reverse where
  bound := clearance.bound
  positive := clearance.positive
  leftLower := by
    intro index
    change clearance.bound <=
      (overlap.bridge (overlap.matching.backward index)).rightClearance.bound
    exact clearance.rightLower (overlap.matching.backward index)
  rightLower := by
    intro index
    change clearance.bound <=
      (overlap.bridge (overlap.matching.backward index)).leftClearance.bound
    exact clearance.leftLower (overlap.matching.backward index)

/-- Reverse every geometric, root, sheet, and braid certificate of a segment. -/
def reverse {start finish : Gaussian} {left : Frame start}
    {right : Frame finish} (segment : Segment left right) :
    Segment right left where
  geometry := segment.geometry.reverse
  safe := segment.safe.reverse
  projection := segment.projection.reverse
  sheetClearance := by
    rw [CCL.Knot.ProjectedCrossings.ProjectedOverlap.reverse_chamberOverlap]
    exact reverseBridgeClearance segment.sheetClearance

@[simp] theorem reverse_geometry {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (segment : Segment left right) :
    segment.reverse.geometry = segment.geometry.reverse := rfl

@[simp] theorem reverse_crossings {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (segment : Segment left right) :
    segment.reverse.crossings = segment.crossings.inverse := by
  exact CCL.Knot.ProjectedCrossings.ProjectedOverlap.reverse_word
    segment.projection

end Segment

/-! ## Finite folds of certified segments -/

inductive Path : {start finish : Gaussian} ->
    Frame start -> Frame finish -> Type 2
  | nil {parameter : Gaussian} (frame : Frame parameter) : Path frame frame
  | cons {start middle finish : Gaussian}
      {left : Frame start} {center : Frame middle} {right : Frame finish}
      (head : Segment left center) (remaining : Path center right) :
      Path left right

namespace Path

def stepCount : {start finish : Gaussian} ->
    {left : Frame start} -> {right : Frame finish} ->
    Path left right -> Nat
  | _, _, _, _, .nil _ => 0
  | _, _, _, _, .cons _ remaining => remaining.stepCount + 1

/-- Segment words in traversal order, retained before flattening. -/
def segmentWords : {start finish : Gaussian} ->
    {left : Frame start} -> {right : Frame finish} ->
    Path left right -> List (Word 3)
  | _, _, _, _, .nil _ => []
  | _, _, _, _, .cons head remaining =>
      head.crossings :: remaining.segmentWords

/-- Flatten the projected braid subdivisions in path order. -/
def word : {start finish : Gaussian} ->
    {left : Frame start} -> {right : Frame finish} ->
    Path left right -> Word 3
  | _, _, _, _, .nil _ => []
  | _, _, _, _, .cons head remaining =>
      head.crossings ++ remaining.word

/-- Fold the actual chamber-owner matchings, independently of the extracted
braid word. -/
def ownerTransport : {start finish : Gaussian} ->
    {left : Frame start} -> {right : Frame finish} ->
    Path left right -> FiniteBijection left.chamber.degree right.chamber.degree
  | _, _, _, _, .nil frame =>
      CCL.FiniteMonodromy.FiniteBijection.identity frame.chamber.degree
  | _, _, _, _, .cons head remaining =>
      CCL.FiniteMonodromy.FiniteBijection.comp remaining.ownerTransport
        head.projection.chamberOverlap.matching

/-- Every segment's exact bridge box followed by the boxes visited by the
remaining logical branch label. -/
def bridgeBoxes : {start finish : Gaussian} ->
    {left : Frame start} -> {right : Frame finish} ->
    (path : Path left right) -> Fin 3 -> List RFAP.Boxes.Box
  | _, _, _, _, .nil _, _ => []
  | _, _, _, _, .cons head remaining, position =>
      (head.projection.chamberOverlap.bridge
        (head.startOwnerIndex position)).box ::
        remaining.bridgeBoxes
          (head.projection.event.permutation.forward position)

@[simp] theorem bridgeBoxes_length {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (path : Path left right) (label : Fin 3) :
    (path.bridgeBoxes label).length = path.stepCount := by
  induction path generalizing label with
  | nil frame => rfl
  | cons head remaining inductionHypothesis =>
      simp only [bridgeBoxes, List.length_cons, stepCount,
        inductionHypothesis]

/-- The independently folded owner matching agrees pointwise with the word
extracted from the atomic projection charts, in the certified endpoint
projection orders. -/
theorem ownerTransport_agrees {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (path : Path left right) (position : Fin 3) :
    path.ownerTransport.forward (left.projected.ownerIndex position) =
      right.projected.ownerIndex (path.word.permutation.forward position) := by
  induction path generalizing position with
  | nil frame =>
      change frame.projected.ownerIndex position =
        frame.projected.ownerIndex position
      rfl
  | @cons pathStart pathMiddle pathFinish pathLeft pathCenter pathRight
      head remaining inductionHypothesis =>
      change remaining.ownerTransport.forward
          (head.projection.chamberOverlap.matching.forward
            (pathLeft.projected.ownerIndex position)) = _
      rw [head.projection.matching_order position]
      calc
        remaining.ownerTransport.forward
            (pathCenter.projected.ownerIndex
              (head.projection.event.permutation.forward position)) =
            pathRight.projected.ownerIndex
              (remaining.word.permutation.forward
                (head.projection.event.permutation.forward position)) :=
          inductionHypothesis
            (head.projection.event.permutation.forward position)
        _ = pathRight.projected.ownerIndex
              ((head.crossings ++ remaining.word).permutation.forward
                position) :=
          congrArg pathRight.projected.ownerIndex
            (CCL.Knot.FiniteBraid.Word.permutation_append
              head.crossings remaining.word position).symm

def append {first middle last : Gaussian}
    {left : Frame first} {center : Frame middle} {right : Frame last}
    (initial : Path left center) (remaining : Path center right) :
    Path left right :=
  match initial with
  | .nil _ => remaining
  | .cons head tail => .cons head (tail.append remaining)

@[simp] theorem word_append {first middle last : Gaussian}
    {left : Frame first} {center : Frame middle} {right : Frame last}
    (initial : Path left center) (remaining : Path center right) :
    (initial.append remaining).word = initial.word ++ remaining.word := by
  induction initial with
  | nil frame => rfl
  | cons head tail inductionHypothesis =>
      simp only [append, word, inductionHypothesis, List.append_assoc]

theorem ownerTransport_append {first middle last : Gaussian}
    {left : Frame first} {center : Frame middle} {right : Frame last}
    (initial : Path left center) (remaining : Path center right)
    (index : left.chamber.Index) :
    (initial.append remaining).ownerTransport.forward index =
      remaining.ownerTransport.forward
        (initial.ownerTransport.forward index) := by
  induction initial with
  | nil frame =>
      change remaining.ownerTransport.forward index =
        remaining.ownerTransport.forward index
      rfl
  | cons head tail inductionHypothesis =>
      exact inductionHypothesis remaining
        (head.projection.chamberOverlap.matching.forward index)

def reverse : {start finish : Gaussian} ->
    {left : Frame start} -> {right : Frame finish} ->
    Path left right -> Path right left
  | _, _, _, _, .nil frame => .nil frame
  | _, _, _, _, .cons head remaining =>
      remaining.reverse.append (.cons head.reverse (.nil _))

@[simp] theorem word_reverse {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (path : Path left right) : path.reverse.word = path.word.inverse := by
  induction path with
  | nil frame => rfl
  | cons head remaining inductionHypothesis =>
      rw [reverse, word_append, inductionHypothesis]
      simp only [word, head.reverse_crossings, List.append_nil]
      exact (CCL.Knot.FiniteBraid.Word.inverse_append
        head.crossings remaining.word).symm

theorem ownerTransport_reverse {start finish : Gaussian}
    {left : Frame start} {right : Frame finish}
    (path : Path left right) (index : right.chamber.Index) :
    path.reverse.ownerTransport.forward index =
      path.ownerTransport.backward index := by
  induction path with
  | nil frame =>
      change index = index
      rfl
  | cons head remaining inductionHypothesis =>
      rw [reverse, ownerTransport_append]
      simp only [ownerTransport, Segment.reverse]
      rw [inductionHypothesis index]
      cases head.projection <;> rfl

end Path

/-- The ramification label at infinity is kept separate from the three
finite-root labels, so its fixed transport is definitionally visible. -/
inductive RamificationLabel
  | finite (label : Fin 3)
  | infinity
deriving DecidableEq, Repr

def transportRamification (word : Word 3) :
    RamificationLabel -> RamificationLabel
  | .finite label => .finite (word.permutation.forward label)
  | .infinity => .infinity

@[simp] theorem transportRamification_infinity (word : Word 3) :
    transportRamification word .infinity = .infinity := rfl

@[simp] theorem transportRamification_inverse (word : Word 3)
    (label : RamificationLabel) :
    transportRamification word.inverse (transportRamification word label) =
      label := by
  cases label with
  | infinity => rfl
  | finite label =>
      apply congrArg RamificationLabel.finite
      calc
        word.inverse.permutation.forward (word.permutation.forward label) =
            word.permutation.reverse.forward
              (word.permutation.forward label) :=
          CCL.Knot.FiniteBraid.Word.permutation_inverse word _
        _ = word.permutation.backward (word.permutation.forward label) := rfl
        _ = label := word.permutation.backward_forward label

end CCL.Riemann.LegendrePaths
