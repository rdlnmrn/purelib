import FTA.CCLProjectiveMatrixBounds
import FTA.CCLApproximateBlockContraction

/-!
# Independently sampled completed CCL blocks

One completed block is observed at a rational point of the current winding
box.  Different blocks may use different points.  The projective inverse of
the decoder prefix is recorded only up to its explicit nonzero homogeneous
scale, and consecutive observations are linked by the rational inverse-tail
stability estimate.
-/

namespace FTA
namespace CCLCompletedBlockObservation

open CCL CCL.GaussianRat
open FTA.CCLApproximateBlockContraction
open FTA.CCLCompletedBlockContraction
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLProjectiveMatrixBounds

abbrev QI := CCL.GaussianRat

/-- One completed block witnessed at one rational point.  `outer` is the
decoder matrix before the block and `outer * block.matrix` is the decoder
matrix immediately afterwards. -/
structure BlockObservationSample
    (outer : Mat2 QI) (block : DecoderBlock) (box : RatBox) where
  point : QI
  inside : box.Contains point
  tail : CompatibleTail block.kind block.exponent block.sector
  scale : QI
  scaleNonzero : scale ≠ 0
  inversePoint :
    tail.point.scale scale =
      Mat2.act (adjugate (Mat2.mul outer block.matrix)) (Proj.affine point)

namespace BlockObservationSample

/-- Projective output obtained by applying the observed inverse branch. -/
abbrev output
    {outer : Mat2 QI} {block : DecoderBlock} {box : RatBox}
    (sample : BlockObservationSample outer block box) : Proj QI :=
  Mat2.act block.matrix sample.tail.point

/-- The completed decoder prefix associated with an observation. -/
def fullMatrix {outer : Mat2 QI} {block : DecoderBlock} {box : RatBox}
    (_sample : BlockObservationSample outer block box) : Mat2 QI :=
  Mat2.mul outer block.matrix

/-- Removing the observed block from its inverse coordinate recovers the
inverse coordinate for the preceding decoder, up to two explicit nonzero
homogeneous scales. -/
theorem output_scaled_eq_inverse_scaled
    {outer : Mat2 QI} {block : DecoderBlock} {box : RatBox}
    (sample : BlockObservationSample outer block box) :
    (Mat2.act block.matrix sample.tail.point).scale sample.scale =
      (Mat2.act (adjugate outer) (Proj.affine sample.point)).scale
        (determinant block.matrix) := by
  calc
    (Mat2.act block.matrix sample.tail.point).scale sample.scale =
        Mat2.act block.matrix (sample.tail.point.scale sample.scale) := by
      rw [DecoderBlock.act_scale]
    _ = Mat2.act block.matrix
        (Mat2.act (adjugate (Mat2.mul outer block.matrix))
          (Proj.affine sample.point)) := by rw [sample.inversePoint]
    _ = (Mat2.act (adjugate outer) (Proj.affine sample.point)).scale
        (determinant block.matrix) :=
      act_right_adjugate_mul outer block.matrix (Proj.affine sample.point)

/-- Chordal distance is unchanged when the observed compatible tail is
replaced by the corresponding inverse decoder coordinate. -/
theorem tail_chordalSq_eq_inverse
    {outer : Mat2 QI} {block : DecoderBlock} {box : RatBox}
    (sample : BlockObservationSample outer block box) (other : Proj QI) :
    chordalSq sample.tail.point other =
      chordalSq
        (Mat2.act (adjugate (Mat2.mul outer block.matrix))
          (Proj.affine sample.point)) other := by
  calc
    chordalSq sample.tail.point other =
        chordalSq (sample.tail.point.scale sample.scale) other := by
      rw [chordalSq_scale_left sample.scale sample.scaleNonzero]
    _ = chordalSq
        (Mat2.act (adjugate (Mat2.mul outer block.matrix))
          (Proj.affine sample.point)) other := by rw [sample.inversePoint]

/-- The output of the observed block is projectively the inverse coordinate
for the preceding decoder matrix. -/
theorem output_chordalSq_eq_inverse
    {outer : Mat2 QI} {block : DecoderBlock} {box : RatBox}
    (sample : BlockObservationSample outer block box) (other : Proj QI) :
    chordalSq (Mat2.act block.matrix sample.tail.point) other =
      chordalSq (Mat2.act (adjugate outer) (Proj.affine sample.point))
        other := by
  calc
    chordalSq (Mat2.act block.matrix sample.tail.point) other =
        chordalSq
          ((Mat2.act block.matrix sample.tail.point).scale sample.scale)
          other := by
      rw [chordalSq_scale_left sample.scale sample.scaleNonzero]
    _ = chordalSq
        ((Mat2.act (adjugate outer) (Proj.affine sample.point)).scale
          (determinant block.matrix)) other := by
      rw [sample.output_scaled_eq_inverse_scaled]
    _ = chordalSq
        (Mat2.act (adjugate outer) (Proj.affine sample.point)) other := by
      rw [chordalSq_scale_left (determinant block.matrix)]
      change (RawParser.blockMatrix block.kind block.exponent block.sector).det ≠ 0
      exact RawParser.blockMatrix_det_ne block.kind block.exponent block.sector

/-- Consecutive independently sampled blocks have exactly the same link
distance as their two inverse coordinates under the shared decoder prefix. -/
theorem consecutive_link_eq
    {outer : Mat2 QI} {first second : DecoderBlock} {box : RatBox}
    (previous : BlockObservationSample outer first box)
    (next : BlockObservationSample
      (Mat2.mul outer first.matrix) second box) :
    chordalSq previous.tail.point
        (Mat2.act second.matrix next.tail.point) =
      chordalSq
        (Mat2.act (adjugate (Mat2.mul outer first.matrix))
          (Proj.affine previous.point))
        (Mat2.act (adjugate (Mat2.mul outer first.matrix))
          (Proj.affine next.point)) := by
  calc
    chordalSq previous.tail.point
        (Mat2.act second.matrix next.tail.point) =
      chordalSq
        (Mat2.act (adjugate (Mat2.mul outer first.matrix))
          (Proj.affine previous.point))
        (Mat2.act second.matrix next.tail.point) :=
      previous.tail_chordalSq_eq_inverse _
    _ = chordalSq (Mat2.act second.matrix next.tail.point)
        (Mat2.act (adjugate (Mat2.mul outer first.matrix))
          (Proj.affine previous.point)) := chordalSq_comm _ _
    _ = chordalSq
        (Mat2.act (adjugate (Mat2.mul outer first.matrix))
          (Proj.affine next.point))
        (Mat2.act (adjugate (Mat2.mul outer first.matrix))
          (Proj.affine previous.point)) :=
      next.output_chordalSq_eq_inverse _
    _ = chordalSq
        (Mat2.act (adjugate (Mat2.mul outer first.matrix))
          (Proj.affine previous.point))
        (Mat2.act (adjugate (Mat2.mul outer first.matrix))
          (Proj.affine next.point)) := chordalSq_comm _ _

/-- A sufficiently small common winding box makes the mismatch between two
consecutive block observations no larger than the requested rational error. -/
theorem consecutive_link_le_of_request
    {outer : Mat2 QI} {first second : DecoderBlock} {box : RatBox}
    (previous : BlockObservationSample outer first box)
    (next : BlockObservationSample
      (Mat2.mul outer first.matrix) second box)
    (outerDeterminantNonzero : outer.det ≠ 0)
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    (boxBound : box.diagonalSq ≤
      inverseTailBoxRequest (Mat2.mul outer first.matrix) epsilon ^ 2) :
    chordalSq previous.tail.point
        (Mat2.act second.matrix next.tail.point) ≤ epsilon := by
  rw [previous.consecutive_link_eq next]
  apply chordalSq_adjugate_affine_le_of_request
    (Mat2.mul outer first.matrix)
  · rw [RawParser.det_mul]
    exact mul_ne_zero outerDeterminantNonzero (by
      simpa only [DecoderBlock.matrix] using
        RawParser.blockMatrix_det_ne first.kind first.exponent first.sector)
  · exact epsilonPositive
  · exact boxBound
  · exact previous.inside
  · exact next.inside

/-- Package the third-bit incremental predicate as one completed-block
observation.  This is the constructor used at every controller transition:
it consumes only the two affine denominator certificates already produced by
denominator separation and never assumes the older parser history at the same
rational point. -/
def ofCompletedIncremental
    (matrix : Mat2 QI) (history : List RawParser.Constraint)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second bit : Bool)
    (box : RatBox) (point : QI) (inside : box.Contains point)
    (matrixDeterminantNonzero : determinant matrix ≠ 0)
    (oldInverseDenominator :
      (adjugate matrix).c * point + (adjugate matrix).d ≠ 0)
    (newInverseDenominator :
      let sector := RawParser.sectorOfBits first second bit
      let block := RawParser.blockMatrix kind exponent sector
      (adjugate (Mat2.mul matrix block)).c * point +
        (adjugate (Mat2.mul matrix block)).d ≠ 0)
    (incremental :
      (inputIncrementalAdvanceFormula
        ⟨.sector kind exponent (.two first second), matrix, history⟩ bit).Holds
          point) :
    BlockObservationSample matrix
      ⟨kind, exponent, RawParser.sectorOfBits first second bit⟩ box := by
  let state : RawParser.State :=
    ⟨.sector kind exponent (.two first second), matrix, history⟩
  let sector := RawParser.sectorOfBits first second bit
  let blockMatrix := RawParser.blockMatrix kind exponent sector
  let before := RatBox.homographic (adjugate matrix) point
  have completeFormula : (inputAdvanceFormula state bit).Holds point := by
    rw [← inputIncrementalAdvanceFormula_eq_inputAdvanceFormula_of_completedSector
      state bit (kind := kind) (exponent := exponent) (first := first)
        (second := second) (by rfl)]
    exact incremental
  have canAdvance : CCL.EncoderParserBridge.CanAdvanceAt state bit before :=
    (inputAdvanceFormula_iff state bit point oldInverseDenominator).1
      completeFormula
  have full : RawParser.fullBlockHolds kind exponent sector before := by
    simpa only [state, CCL.EncoderParserBridge.CanAdvanceAt, sector] using
      canAdvance.1
  have residual :
      RawParser.normalizedValue kind exponent before - sector.rep ≠ 0 := by
    simpa only [state, CCL.EncoderParserBridge.CanAdvanceAt, sector] using
      canAdvance.2
  let tail := inv (gamma *
    (RawParser.normalizedValue kind exponent before - sector.rep))
  have tailActive : RawParser.activeHolds (.loopUnary 0) tail := by
    exact CCL.EncoderParserBridge.inverse_selected_loop_active kind exponent
      sector before full residual
  have tailOutside : 1 < normSq tail := by
    simpa [RawParser.activeHolds] using tailActive
  have blockDenominator :
      RawParserSemantics.denominator blockMatrix tail ≠ 0 := by
    exact CCL.EncoderParserBridge.block_inverse_denominator_ne kind exponent
      sector before residual
  have blockForward : RatBox.homographic blockMatrix tail = before := by
    exact CCL.EncoderParserBridge.block_homographic_inverse kind exponent
      sector before residual
  have oldForwardDenominator :
      RawParserSemantics.denominator matrix before ≠ 0 := by
    exact denominator_inverse_tail_ne matrix point matrixDeterminantNonzero
      oldInverseDenominator
  have oldDecode : RatBox.homographic matrix before = point := by
    exact homographic_adjugate_inverse matrix point matrixDeterminantNonzero
      oldInverseDenominator
  have productDenominator :
      RawParserSemantics.denominator (Mat2.mul matrix blockMatrix) tail ≠ 0 := by
    apply (RawParserSemantics.denominator_mul_ne_iff matrix blockMatrix tail
      blockDenominator).2
    rw [blockForward]
    exact oldForwardDenominator
  have productDecode :
      RatBox.homographic (Mat2.mul matrix blockMatrix) tail = point := by
    calc
      RatBox.homographic (Mat2.mul matrix blockMatrix) tail =
          RatBox.homographic matrix
            (RatBox.homographic blockMatrix tail) :=
        RawParserSemantics.homographic_mul matrix blockMatrix tail
          blockDenominator (by rw [blockForward]; exact oldForwardDenominator)
      _ = RatBox.homographic matrix before := by rw [blockForward]
      _ = point := oldDecode
  have productDeterminantNonzero :
      determinant (Mat2.mul matrix blockMatrix) ≠ 0 := by
    change (Mat2.mul matrix blockMatrix).det ≠ 0
    rw [RawParser.det_mul]
    exact mul_ne_zero
      (by simpa only [determinant, Mat2.det] using matrixDeterminantNonzero)
      (by simpa only [blockMatrix] using
        RawParser.blockMatrix_det_ne kind exponent sector)
  have recovered :
      RatBox.homographic (adjugate (Mat2.mul matrix blockMatrix)) point =
        tail := by
    rw [← productDecode]
    exact homographic_adjugate_forward_inverse
      (Mat2.mul matrix blockMatrix) tail productDeterminantNonzero
        productDenominator
  let compatible : CompatibleTail kind exponent sector :=
    .affine tail blockDenominator (by rw [blockForward]; exact full)
      tailOutside
  let scale := RawParserSemantics.denominator
    (adjugate (Mat2.mul matrix blockMatrix)) point
  have scaleNonzero : scale ≠ 0 := by
    simpa only [scale, RawParserSemantics.denominator, sector, blockMatrix]
      using newInverseDenominator
  refine
    { point := point
      inside := inside
      tail := compatible
      scale := scale
      scaleNonzero := scaleNonzero
      inversePoint := ?_ }
  have acted := CCLHomographicCylinder.act_affine_eq_scale_homographic
    (adjugate (Mat2.mul matrix blockMatrix)) point scaleNonzero
  change (Proj.affine tail).scale scale =
    Mat2.act (adjugate (Mat2.mul matrix blockMatrix)) (Proj.affine point)
  rw [acted, recovered]

end BlockObservationSample

end CCLCompletedBlockObservation
end FTA
