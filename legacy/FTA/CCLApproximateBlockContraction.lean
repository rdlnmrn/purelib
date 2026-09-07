import FTA.CCLCompletedBlockContraction

/-!
# Completed-block contraction with finite perturbation errors

Historical CCL predicates may be witnessed by different rational points of
one shrinking winding box.  The exact completed-block theorem therefore has
to tolerate a small projective mismatch between successive witnesses.  This
file keeps the mismatch explicit and rational.  A weighted square-root-free
triangle inequality retains a strict `3/4` contraction per block, while every
finite mismatch is accumulated in a displayed geometric error budget.
-/

namespace FTA
namespace CCLApproximateBlockContraction

open CCL CCL.GaussianRat
open FTA.CCLCompletedBlockContraction
open FTA.CCLHomographicCylinder

abbrev QI := CCL.GaussianRat

/-- Rational Young inequality for the Gaussian norm.  The positive weight is
kept explicit so later projective triangle estimates can trade contraction
against a finite perturbation coefficient. -/
theorem normSq_add_le_weighted (left right : QI) {weight : ℚ}
    (weightPositive : 0 < weight) :
    normSq (left + right) ≤
      (1 + weight) * normSq left +
        (1 + 1 / weight) * normSq right := by
  have identity :
      weight *
          ((1 + weight) * normSq left +
            (1 + 1 / weight) * normSq right) -
        weight * normSq (left + right) =
      (weight * left.re - right.re) ^ 2 +
        (weight * left.im - right.im) ^ 2 := by
    unfold normSq
    field_simp [ne_of_gt weightPositive]
    simp only [GaussianRat.add_re, GaussianRat.add_im]
    ring
  have scaled :
      weight * normSq (left + right) ≤
        weight *
          ((1 + weight) * normSq left +
            (1 + 1 / weight) * normSq right) := by
    rw [← sub_nonneg, identity]
    exact add_nonneg (sq_nonneg _) (sq_nonneg _)
  exact le_of_mul_le_mul_left scaled weightPositive

/-- Weighted square-root-free triangle estimate for squared chordal distance.
For a large weight the second leg receives a coefficient close to one, at the
cost of a larger but still rational coefficient on the first leg. -/
theorem chordalSq_triangle_weighted
    {x y z : Proj QI} (hx : x.HasNonzeroCoordinate)
    (hy : y.HasNonzeroCoordinate) (hz : z.HasNonzeroCoordinate)
    {weight : ℚ} (weightPositive : 0 < weight) :
    chordalSq x z ≤
      (1 + weight) * chordalSq x y +
        (1 + 1 / weight) * chordalSq y z := by
  have hxWeight : 0 < x.weight := Proj.weight_pos hx
  have hyWeight : 0 < y.weight := Proj.weight_pos hy
  have hzWeight : 0 < z.weight := Proj.weight_pos hz
  have firstCoefficient : 0 ≤ 1 + weight := by linarith
  have secondCoefficient : 0 ≤ 1 + 1 / weight := by
    have inversePositive : 0 < 1 / weight := by positivity
    linarith
  have expansion := congrArg normSq (Proj.cross_mul_weight x y z)
  have sumBound := normSq_add_le_weighted
    (x.cross y * y.hermitian z) (y.cross z * y.hermitian x)
      weightPositive
  have crossBound :
      normSq (x.cross z) * y.weight ^ 2 ≤
        (1 + weight) *
            (normSq (x.cross y) * (y.weight * z.weight)) +
          (1 + 1 / weight) *
            (normSq (y.cross z) * (x.weight * y.weight)) := by
    calc
      normSq (x.cross z) * y.weight ^ 2 =
          normSq (x.cross z * ⟨y.weight, 0⟩) := by
            simp only [normSq, GaussianRat.mul_re, GaussianRat.mul_im]
            ring
      _ = normSq
          (x.cross y * y.hermitian z + y.cross z * y.hermitian x) := expansion
      _ ≤ (1 + weight) * normSq (x.cross y * y.hermitian z) +
          (1 + 1 / weight) * normSq (y.cross z * y.hermitian x) := sumBound
      _ = (1 + weight) *
            (normSq (x.cross y) * normSq (y.hermitian z)) +
          (1 + 1 / weight) *
            (normSq (y.cross z) * normSq (y.hermitian x)) := by
              rw [normSq_mul, normSq_mul]
      _ ≤ (1 + weight) *
            (normSq (x.cross y) * (y.weight * z.weight)) +
          (1 + 1 / weight) *
            (normSq (y.cross z) * (x.weight * y.weight)) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left
                  (Proj.normSq_hermitian_le_weight_mul y z)
                  (normSq_nonneg (x.cross y))) firstCoefficient
            · have bound := Proj.normSq_hermitian_le_weight_mul y x
              rw [_root_.mul_comm y.weight x.weight] at bound
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left bound
                  (normSq_nonneg (y.cross z))) secondCoefficient
  have cancelled :
      normSq (x.cross z) * y.weight ≤
        (1 + weight) * (normSq (x.cross y) * z.weight) +
          (1 + 1 / weight) * (normSq (y.cross z) * x.weight) := by
    have scaled :
        y.weight * (normSq (x.cross z) * y.weight) ≤
          y.weight *
            ((1 + weight) * (normSq (x.cross y) * z.weight) +
              (1 + 1 / weight) *
                (normSq (y.cross z) * x.weight)) := by
      calc
        y.weight * (normSq (x.cross z) * y.weight) =
            normSq (x.cross z) * y.weight ^ 2 := by ring
        _ ≤ (1 + weight) *
              (normSq (x.cross y) * (y.weight * z.weight)) +
            (1 + 1 / weight) *
              (normSq (y.cross z) * (x.weight * y.weight)) := crossBound
        _ = y.weight *
            ((1 + weight) * (normSq (x.cross y) * z.weight) +
              (1 + 1 / weight) *
                (normSq (y.cross z) * x.weight)) := by ring
    exact le_of_mul_le_mul_left scaled hyWeight
  rw [chordalSq_eq_cross, chordalSq_eq_cross, chordalSq_eq_cross]
  apply (div_le_iff₀ (mul_pos hxWeight hzWeight)).2
  have rhsIdentity :
      ((1 + weight) *
          (normSq (x.cross y) / (x.weight * y.weight)) +
        (1 + 1 / weight) *
          (normSq (y.cross z) / (y.weight * z.weight))) *
          (x.weight * z.weight) =
        ((1 + weight) * (normSq (x.cross y) * z.weight) +
          (1 + 1 / weight) * (normSq (y.cross z) * x.weight)) /
            y.weight := by
    field_simp [ne_of_gt hxWeight, ne_of_gt hyWeight, ne_of_gt hzWeight]
  rw [rhsIdentity]
  exact (le_div_iff₀ hyWeight).2 cancelled

/-- A finite compatible block chain whose successive rational witnesses need
not agree exactly.  Each constructor applies one genuine compatible inverse
branch, then records the squared-chordal mismatch to the output of the next
inner witness. -/
inductive ApproximateTrace :
    (blocks : List DecoderBlock) →
      (output terminal : Proj QI) → Type where
  | nil (terminal : Proj QI) : ApproximateTrace [] terminal terminal
  | cons {block : DecoderBlock} {blocks : List DecoderBlock}
      (compatible : CompatibleTail block.kind block.exponent block.sector)
      {innerOutput terminal : Proj QI}
      (inner : ApproximateTrace blocks innerOutput terminal)
      (linkError : ℚ) (linkErrorNonnegative : 0 ≤ linkError)
      (link : chordalSq compatible.point innerOutput ≤ linkError) :
      ApproximateTrace (block :: blocks)
        (Mat2.act block.matrix compatible.point) terminal

namespace ApproximateTrace

/-- Geometrically discounted sum of the finite witness mismatches. -/
def errorBudget
    {blocks : List DecoderBlock} {output terminal : Proj QI}
    (trace : ApproximateTrace blocks output terminal) : ℚ :=
  match trace with
  | .nil _ => 0
  | .cons _ inner linkError _ _ =>
      linkError + (3 / 4 : ℚ) * errorBudget inner

@[simp] theorem errorBudget_nil (terminal : Proj QI) :
    (ApproximateTrace.nil terminal).errorBudget = 0 := rfl

@[simp] theorem errorBudget_cons
    {block : DecoderBlock} {blocks : List DecoderBlock}
    (compatible : CompatibleTail block.kind block.exponent block.sector)
    {innerOutput terminal : Proj QI}
    (inner : ApproximateTrace blocks innerOutput terminal)
    (linkError : ℚ) (linkErrorNonnegative : 0 ≤ linkError)
    (link : chordalSq compatible.point innerOutput ≤ linkError) :
    (ApproximateTrace.cons compatible inner linkError linkErrorNonnegative
      link).errorBudget =
      linkError + (3 / 4 : ℚ) * inner.errorBudget := by
  rfl

theorem errorBudget_nonneg
    {blocks : List DecoderBlock} {output terminal : Proj QI}
    (trace : ApproximateTrace blocks output terminal) :
    0 ≤ trace.errorBudget := by
  induction trace with
  | nil => simp [errorBudget]
  | cons compatible inner linkError linkErrorNonnegative link
      inductionHypothesis =>
      simp only [errorBudget]
      exact add_nonneg linkErrorNonnegative
        (mul_nonneg (by norm_num) inductionHypothesis)

private theorem block_output_hasNonzeroCoordinate
    (block : DecoderBlock)
    (tail : CompatibleTail block.kind block.exponent block.sector) :
    (Mat2.act block.matrix tail.point).HasNonzeroCoordinate := by
  cases tail with
  | omega =>
      exact firstColumn_hasNonzeroCoordinate
        (RawParser.blockMatrix_det_ne block.kind block.exponent block.sector)
  | affine value denominator full outside =>
      exact act_affine_hasNonzeroCoordinate
        (RawParser.blockMatrix_det_ne block.kind block.exponent block.sector)
          value

theorem output_hasNonzeroCoordinate
    {blocks : List DecoderBlock} {output terminal : Proj QI}
    (trace : ApproximateTrace blocks output terminal)
    (terminalValid : terminal.HasNonzeroCoordinate) :
    output.HasNonzeroCoordinate := by
  cases trace with
  | nil => exact terminalValid
  | @cons block blocks compatible innerOutput terminal inner linkError
      linkErrorNonnegative link =>
      exact block_output_hasNonzeroCoordinate block compatible

/-- Two perturbed compatible traces still contract geometrically.  The
`3/4` factor is deliberately weaker than the exact `1/2`; it pays for keeping
all perturbation accounting rational and square-root-free. -/
theorem chordalSq_le_three_quarters_pow_add_error
    {blocks : List DecoderBlock}
    {leftOutput rightOutput leftTerminal rightTerminal : Proj QI}
    (left : ApproximateTrace blocks leftOutput leftTerminal)
    (right : ApproximateTrace blocks rightOutput rightTerminal)
    (leftTerminalValid : leftTerminal.HasNonzeroCoordinate)
    (rightTerminalValid : rightTerminal.HasNonzeroCoordinate) :
    chordalSq leftOutput rightOutput ≤
      (3 / 4 : ℚ) ^ blocks.length *
          chordalSq leftTerminal rightTerminal +
        4 * (left.errorBudget + right.errorBudget) := by
  induction blocks generalizing leftOutput rightOutput
      leftTerminal rightTerminal with
  | nil =>
      cases left
      cases right
      simp [errorBudget]
  | cons block blocks inductionHypothesis =>
      cases left with
      | @cons _ _ leftCompatible leftInnerOutput _ leftInner leftLinkError
          leftLinkErrorNonnegative leftLink =>
          cases right with
          | @cons _ _ rightCompatible rightInnerOutput _ rightInner
              rightLinkError rightLinkErrorNonnegative rightLink =>
              have innerBound := inductionHypothesis leftInner rightInner
                leftTerminalValid rightTerminalValid
              have leftCompatibleValid :=
                leftCompatible.point_hasNonzeroCoordinate
              have rightCompatibleValid :=
                rightCompatible.point_hasNonzeroCoordinate
              have leftInnerValid := leftInner.output_hasNonzeroCoordinate
                leftTerminalValid
              have rightInnerValid := rightInner.output_hasNonzeroCoordinate
                rightTerminalValid
              have firstTriangle := chordalSq_triangle_weighted
                leftCompatibleValid leftInnerValid rightCompatibleValid
                (weight := 4) (by norm_num)
              have secondTriangle := chordalSq_triangle_weighted
                leftInnerValid rightInnerValid rightCompatibleValid
                (weight := 1 / 5) (by norm_num)
              have compatibleDistance :
                  chordalSq leftCompatible.point rightCompatible.point ≤
                    5 * leftLinkError +
                      (3 / 2 : ℚ) *
                        chordalSq leftInnerOutput rightInnerOutput +
                      (15 / 2 : ℚ) * rightLinkError := by
                rw [show (1 + (4 : ℚ)) = 5 by norm_num,
                  show (1 + 1 / (4 : ℚ)) = 5 / 4 by norm_num]
                  at firstTriangle
                rw [show (1 + (1 / 5 : ℚ)) = 6 / 5 by norm_num,
                  show (1 + 1 / (1 / 5 : ℚ)) = 6 by norm_num]
                  at secondTriangle
                have rightLinkSymmetric :
                    chordalSq rightInnerOutput rightCompatible.point ≤
                      rightLinkError := by
                  rw [chordalSq_comm]
                  exact rightLink
                linarith
              have blockBound :
                  chordalSq
                      (Mat2.act block.matrix leftCompatible.point)
                      (Mat2.act block.matrix rightCompatible.point) ≤
                    (1 / 2 : ℚ) *
                      chordalSq leftCompatible.point rightCompatible.point := by
                simpa only [DecoderBlock.matrix] using
                  block_chordalSq_compatibleTail_le_half
                    block.kind block.exponent block.sector leftCompatible
                      rightCompatible
              have outerRecurrence :
                  chordalSq
                      (Mat2.act block.matrix leftCompatible.point)
                      (Mat2.act block.matrix rightCompatible.point) ≤
                    (3 / 4 : ℚ) *
                        chordalSq leftInnerOutput rightInnerOutput +
                      4 * (leftLinkError + rightLinkError) := by
                calc
                  chordalSq
                      (Mat2.act block.matrix leftCompatible.point)
                      (Mat2.act block.matrix rightCompatible.point) ≤
                      (1 / 2 : ℚ) *
                        chordalSq leftCompatible.point rightCompatible.point :=
                    blockBound
                  _ ≤ (1 / 2 : ℚ) *
                      (5 * leftLinkError +
                        (3 / 2 : ℚ) *
                          chordalSq leftInnerOutput rightInnerOutput +
                        (15 / 2 : ℚ) * rightLinkError) :=
                    mul_le_mul_of_nonneg_left compatibleDistance (by norm_num)
                  _ ≤ (3 / 4 : ℚ) *
                        chordalSq leftInnerOutput rightInnerOutput +
                      4 * (leftLinkError + rightLinkError) := by
                    linarith
              have scaledInner := mul_le_mul_of_nonneg_left innerBound
                (by norm_num : (0 : ℚ) ≤ 3 / 4)
              simp only [List.length_cons, pow_succ, errorBudget]
              calc
                chordalSq
                    (Mat2.act block.matrix leftCompatible.point)
                    (Mat2.act block.matrix rightCompatible.point) ≤
                    (3 / 4 : ℚ) *
                        chordalSq leftInnerOutput rightInnerOutput +
                      4 * (leftLinkError + rightLinkError) := outerRecurrence
                _ ≤ (3 / 4 : ℚ) *
                      ((3 / 4 : ℚ) ^ blocks.length *
                          chordalSq leftTerminal rightTerminal +
                        4 * (leftInner.errorBudget +
                          rightInner.errorBudget)) +
                    4 * (leftLinkError + rightLinkError) := by
                      linarith
                _ = ((3 / 4 : ℚ) ^ blocks.length * (3 / 4 : ℚ)) *
                      chordalSq leftTerminal rightTerminal +
                    4 *
                      ((leftLinkError +
                          (3 / 4 : ℚ) * leftInner.errorBudget) +
                        (rightLinkError +
                          (3 / 4 : ℚ) * rightInner.errorBudget)) := by
                      ring

/-- With valid terminal coordinates, the unresolved terminal pair contributes
at most one. -/
theorem chordalSq_le_three_quarters_pow_add_error_of_valid
    {blocks : List DecoderBlock}
    {leftOutput rightOutput leftTerminal rightTerminal : Proj QI}
    (left : ApproximateTrace blocks leftOutput leftTerminal)
    (right : ApproximateTrace blocks rightOutput rightTerminal)
    (leftTerminalValid : leftTerminal.HasNonzeroCoordinate)
    (rightTerminalValid : rightTerminal.HasNonzeroCoordinate) :
    chordalSq leftOutput rightOutput ≤
      (3 / 4 : ℚ) ^ blocks.length +
        4 * (left.errorBudget + right.errorBudget) := by
  have traceBound := chordalSq_le_three_quarters_pow_add_error left right
    leftTerminalValid rightTerminalValid
  have terminalBound := chordalSq_le_one leftTerminalValid rightTerminalValid
  have scaledTerminal := mul_le_mul_of_nonneg_left terminalBound
    (pow_nonneg (by norm_num : (0 : ℚ) ≤ 3 / 4) blocks.length)
  linarith

end ApproximateTrace

end CCLApproximateBlockContraction
end FTA
