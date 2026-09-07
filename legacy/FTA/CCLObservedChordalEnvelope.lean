import FTA.CCLPersistentBlockObservations
import FTA.CCLUnaryCylinder

/-!
# Word-tagged chordal envelopes from persistent block observations

The formal canonical truncation of a raw CCL word may lie on a projective
boundary and is not asserted to be a numerical point of its affine cylinder.
This module therefore keeps the finite word tag and the numerical envelope
center as separate data.  The center is a materialized compatible observation
trace; completed blocks and inverse-tail stability give its shrinking rational
squared-chordal radius.
-/

namespace FTA
namespace CCLObservedChordalEnvelope

open CCL
open FTA.CCLChordalEnvelope
open FTA.CCLCompletedBlockContraction
open FTA.CCLPersistentBlockObservations
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- A formal raw-word tag paired with a numerical observation envelope.  The
two projective coordinates are deliberately not identified. -/
structure TaggedObservationEnvelope where
  tag : TaggedTruncation
  box : RatBox
  linkError : ℚ
  stable : SampleChain.StableEnvelope box RawParser.identityMatrix
    (parserBlocks tag.word) linkError

namespace TaggedObservationEnvelope

def center (envelope : TaggedObservationEnvelope) : Proj QI :=
  envelope.stable.anchor.front

def radiusSq (envelope : TaggedObservationEnvelope) : ℚ :=
  envelope.stable.radiusSq

theorem center_hasNonzeroCoordinate (envelope : TaggedObservationEnvelope) :
    envelope.center.HasNonzeroCoordinate :=
  envelope.stable.anchor.front_hasNonzeroCoordinate

theorem radiusSq_nonneg (envelope : TaggedObservationEnvelope) :
    0 ≤ envelope.radiusSq :=
  envelope.stable.radiusSq_nonneg

def Contains (envelope : TaggedObservationEnvelope)
    (candidate : SampleChain envelope.box RawParser.identityMatrix
      (parserBlocks envelope.tag.word)) : Prop :=
  envelope.stable.Contains candidate

theorem contains_of_links (envelope : TaggedObservationEnvelope)
    (candidate : SampleChain envelope.box RawParser.identityMatrix
      (parserBlocks envelope.tag.word))
    (links : candidate.LinksBound envelope.linkError) :
    envelope.Contains candidate :=
  envelope.stable.contains_of_links candidate links

end TaggedObservationEnvelope

/-- A nonempty observed history couples its numerical projective center to
the rational point of the outermost observation, which lies in the winding
box.  The raw word remains a separate finite tag. -/
structure CoupledObservationEnvelope where
  tag : TaggedTruncation
  box : RatBox
  linkError : ℚ
  firstBlock : DecoderBlock
  remainingBlocks : List DecoderBlock
  blocksEq : parserBlocks tag.word = firstBlock :: remainingBlocks
  stable : SampleChain.StableEnvelope box RawParser.identityMatrix
    (firstBlock :: remainingBlocks) linkError

namespace CoupledObservationEnvelope

def center (envelope : CoupledObservationEnvelope) : Proj QI :=
  envelope.stable.anchor.front

def reference (envelope : CoupledObservationEnvelope) : QI :=
  envelope.stable.anchor.headPoint

def cylinderRadiusSq (envelope : CoupledObservationEnvelope) : ℚ :=
  envelope.stable.radiusSq

/-- Rational sum of the independently shrinking winding-box and observation
errors. -/
def radiusSq (envelope : CoupledObservationEnvelope) : ℚ :=
  2 * (envelope.box.diagonalSq + envelope.cylinderRadiusSq)

theorem center_hasNonzeroCoordinate (envelope : CoupledObservationEnvelope) :
    envelope.center.HasNonzeroCoordinate :=
  envelope.stable.anchor.front_hasNonzeroCoordinate

theorem referenceInside (envelope : CoupledObservationEnvelope) :
    envelope.box.Contains envelope.reference :=
  envelope.stable.anchor.headPoint_inside

theorem center_reference_chordalSq_eq_zero
    (envelope : CoupledObservationEnvelope) :
    chordalSq envelope.center (Proj.affine envelope.reference) = 0 :=
  envelope.stable.anchor.front_chordalSq_affine_headPoint_eq_zero

theorem reference_center_chordalSq_eq_zero
    (envelope : CoupledObservationEnvelope) :
    chordalSq (Proj.affine envelope.reference) envelope.center = 0 := by
  rw [chordalSq_comm]
  exact envelope.center_reference_chordalSq_eq_zero

theorem cylinderRadiusSq_nonneg (envelope : CoupledObservationEnvelope) :
    0 ≤ envelope.cylinderRadiusSq :=
  envelope.stable.radiusSq_nonneg

theorem radiusSq_nonneg (envelope : CoupledObservationEnvelope) :
    0 ≤ envelope.radiusSq := by
  exact mul_nonneg (by norm_num)
    (add_nonneg envelope.box.diagonalSq_nonneg
      envelope.cylinderRadiusSq_nonneg)

def Contains (envelope : CoupledObservationEnvelope) (point : QI) : Prop :=
  chordalSq (Proj.affine point) envelope.center ≤ envelope.radiusSq

/-- The rational box-to-envelope coupling inequality. -/
theorem contains_of_box_contains (envelope : CoupledObservationEnvelope)
    {point : QI} (inside : envelope.box.Contains point) :
    envelope.Contains point := by
  have triangle := chordalSq_triangle_two
    (Proj.affine_hasNonzeroCoordinate point)
    (Proj.affine_hasNonzeroCoordinate envelope.reference)
    envelope.center_hasNonzeroCoordinate
  have boxBound :
      chordalSq (Proj.affine point) (Proj.affine envelope.reference) ≤
        envelope.box.diagonalSq :=
    (CCLChordalEnvelope.chordalSq_affine_le_normSq point
      envelope.reference).trans
      (RatBox.normSq_sub_le_diagonalSq inside envelope.referenceInside)
  have referenceZero := envelope.reference_center_chordalSq_eq_zero
  have cylinderNonnegative := envelope.cylinderRadiusSq_nonneg
  dsimp only [Contains, radiusSq]
  linarith

theorem radiusSq_le
    {envelope : CoupledObservationEnvelope} {boxError cylinderError : ℚ}
    (boxBound : envelope.box.diagonalSq ≤ boxError)
    (cylinderBound : envelope.cylinderRadiusSq ≤ cylinderError) :
    envelope.radiusSq ≤ 2 * (boxError + cylinderError) := by
  dsimp only [radiusSq]
  linarith

/-- Any other stable independently sampled history lies in the numerical
cylinder around the chosen center. -/
theorem observation_chordalSq_le
    (envelope : CoupledObservationEnvelope)
    (candidate : SampleChain envelope.box RawParser.identityMatrix
      (envelope.firstBlock :: envelope.remainingBlocks))
    (links : candidate.LinksBound envelope.linkError) :
    chordalSq envelope.center candidate.front ≤
      envelope.cylinderRadiusSq :=
  envelope.stable.contains_of_links candidate links

end CoupledObservationEnvelope

/-- Construct the word-tagged coupling directly from the persistent provider
stored by the active controller after a sufficiently small box refinement. -/
def CoupledObservationEnvelope.ofPersistent
    {p : GaussianPolynomial} {ambient : RatBox}
    {word : Prefix.Word} {first : DecoderBlock}
    {remaining : List DecoderBlock}
    {current next : WindingOneState p ambient}
    (history : PersistentObservationChain RawParser.identityMatrix
      (parserBlocks word) current)
    (blocksEq : parserBlocks word = first :: remaining)
    (nextRefines : next.box.Refines current.box)
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    (boxBound : next.box.diagonalSq ≤
      SampleChain.stabilityRequest RawParser.identityMatrix
        (first :: remaining) epsilon ^ 2) :
    CoupledObservationEnvelope :=
  { tag := ⟨word⟩
    box := next.box
    linkError := epsilon
    firstBlock := first
    remainingBlocks := remaining
    blocksEq := blocksEq
    stable := (history.castBlocks blocksEq).stableEnvelope nextRefines
      (by simp [RawParser.identityMatrix, Mat2.det]) epsilon epsilonPositive
        boxBound }

/-! ## Explicit shrinking schedule -/

/-- Per-link error allocated to a requested total cylinder radius. -/
def observationLinkError (target : ℚ) : ℚ := target / 64

/-- Four completed blocks dominate one binary halving step because
`(3/4)^4 ≤ 1/2`. -/
def observationBlockDepth (target : ℚ) : ℕ :=
  4 * CCLUnaryCylinder.binaryDepth (target / 2)

theorem observationLinkError_pos {target : ℚ} (targetPositive : 0 < target) :
    0 < observationLinkError target := by
  dsimp [observationLinkError]
  positivity

theorem three_quarters_pow_four_mul_le_half_pow (count : ℕ) :
    (3 / 4 : ℚ) ^ (4 * count) ≤ (1 / 2 : ℚ) ^ count := by
  induction count with
  | zero => norm_num
  | succ count inductionHypothesis =>
      calc
        (3 / 4 : ℚ) ^ (4 * (count + 1)) =
            (3 / 4 : ℚ) ^ (4 * count) * (3 / 4 : ℚ) ^ 4 := by
          rw [Nat.mul_succ, pow_add]
        _ ≤ (1 / 2 : ℚ) ^ count * (3 / 4 : ℚ) ^ 4 :=
          mul_le_mul_of_nonneg_right inductionHypothesis (by positivity)
        _ ≤ (1 / 2 : ℚ) ^ count * (1 / 2 : ℚ) :=
          mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
        _ = (1 / 2 : ℚ) ^ (count + 1) := by rw [pow_succ]

theorem three_quarters_pow_observationBlockDepth_le
    {target : ℚ} (targetPositive : 0 < target) :
    (3 / 4 : ℚ) ^ observationBlockDepth target ≤ target / 2 := by
  let depth := CCLUnaryCylinder.binaryDepth (target / 2)
  have targetHalfPositive : 0 < target / 2 := by positivity
  have halfPowerBound :
      (1 / 2 : ℚ) ^ depth ≤ 4 / (2 : ℚ) ^ depth := by
    rw [div_pow]
    norm_num only [one_pow]
    exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  calc
    (3 / 4 : ℚ) ^ observationBlockDepth target =
        (3 / 4 : ℚ) ^ (4 * depth) := by rfl
    _ ≤ (1 / 2 : ℚ) ^ depth :=
      three_quarters_pow_four_mul_le_half_pow depth
    _ ≤ 4 / (2 : ℚ) ^ depth := halfPowerBound
    _ ≤ target / 2 :=
      CCLUnaryCylinder.binaryDepth_sufficient targetHalfPositive

/-- The displayed schedule makes the observation envelope no larger than the
requested positive rational radius. -/
theorem SampleChain.StableEnvelope.radiusSq_le_target
    {box : RatBox} {outer : Mat2 QI} {blocks : List DecoderBlock}
    {target : ℚ}
    (envelope : SampleChain.StableEnvelope box outer blocks
      (observationLinkError target))
    (targetPositive : 0 < target)
    (enoughBlocks : observationBlockDepth target ≤ blocks.length) :
    envelope.radiusSq ≤ target := by
  have exponentBound :
      (3 / 4 : ℚ) ^ blocks.length ≤
        (3 / 4 : ℚ) ^ observationBlockDepth target :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) enoughBlocks
  have geometricBound := exponentBound.trans
    (three_quarters_pow_observationBlockDepth_le targetPositive)
  change (3 / 4 : ℚ) ^ blocks.length + 32 * (target / 64) ≤ target
  linarith

/-- The joint inverse-tail box request used by the controller at the displayed
shrinking schedule. -/
def observationBoxRequest (word : Prefix.Word) (target : ℚ) : ℚ :=
  SampleChain.stabilityRequest RawParser.identityMatrix (parserBlocks word)
    (observationLinkError target)

theorem observationBoxRequest_pos (word : Prefix.Word)
    {target : ℚ} (targetPositive : 0 < target) :
    0 < observationBoxRequest word target := by
  apply SampleChain.stabilityRequest_pos
  · simp [RawParser.identityMatrix, Mat2.det]
  · exact observationLinkError_pos targetPositive

/-- Coordinate-separated winding regions have inequivalent numerical tagged
centers once their summed box and observation errors lie below the precomputed
projective gap. -/
theorem centers_not_equivalent_of_error_sum_lt_gap
    {B C : RatBox} {coordinateGap : ℚ}
    (gapPositive : 0 < coordinateGap)
    (coordinateSeparated :
      B.xUpper + coordinateGap ≤ C.xLower ∨
      C.xUpper + coordinateGap ≤ B.xLower ∨
      B.yUpper + coordinateGap ≤ C.yLower ∨
      C.yUpper + coordinateGap ≤ B.yLower)
    {left right : CoupledObservationEnvelope}
    (leftBox : left.box = B) (rightBox : right.box = C)
    (thin : 4 * (left.radiusSq + right.radiusSq) <
      chordalGapSq B C coordinateGap) :
    ¬left.center.Equivalent right.center := by
  intro equivalent
  have insideB : B.Contains left.reference := by
    simpa only [← leftBox] using left.referenceInside
  have insideC : C.Contains right.reference := by
    simpa only [← rightBox] using right.referenceInside
  have lower := chordalGapSq_le gapPositive coordinateSeparated insideB insideC
  have middleZero : chordalSq left.center right.center = 0 :=
    chordalSq_eq_zero_of_equivalent equivalent
  have rightTriangle := chordalSq_triangle_two
    left.center_hasNonzeroCoordinate right.center_hasNonzeroCoordinate
      (Proj.affine_hasNonzeroCoordinate right.reference)
  have rightBound := right.contains_of_box_contains right.referenceInside
  change chordalSq (Proj.affine right.reference) right.center ≤
    right.radiusSq at rightBound
  rw [chordalSq_comm] at rightBound
  have leftToRightReference :
      chordalSq left.center (Proj.affine right.reference) ≤
        2 * right.radiusSq := by
    linarith [rightTriangle, middleZero, rightBound]
  have leftTriangle := chordalSq_triangle_two
    (Proj.affine_hasNonzeroCoordinate left.reference)
    left.center_hasNonzeroCoordinate
    (Proj.affine_hasNonzeroCoordinate right.reference)
  have leftBound := left.contains_of_box_contains left.referenceInside
  change chordalSq (Proj.affine left.reference) left.center ≤
    left.radiusSq at leftBound
  have leftRadiusNonnegative := left.radiusSq_nonneg
  have rightRadiusNonnegative := right.radiusSq_nonneg
  have upper :
      chordalSq (Proj.affine left.reference)
          (Proj.affine right.reference) ≤
        4 * (left.radiusSq + right.radiusSq) := by
    linarith
  linarith

end CCLObservedChordalEnvelope
end FTA
