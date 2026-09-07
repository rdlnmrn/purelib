import CCL.Encoding.RawParserSemantics
import FTA.CCLChordalEnvelope

/-!
# Chordal-diameter certificates for raw CCL cylinders

The tagged parser truncation and the metric cylinder are deliberately kept
distinct.  A partial unary or sector fragment can shrink the certified
cylinder diameter while leaving the canonical homogeneous pair unchanged.
All soundness statements quantify only over finite Gaussian-rational
realizations of the raw prefix.
-/

namespace FTA
namespace CCLRawCylinderEnvelope

open CCL
open FTA.CCLChordalEnvelope

abbrev QI := CCL.GaussianRat

/-- A tagged raw prefix with a rational upper bound for the squared chordal
diameter of all its affine rational realizations. -/
structure RawCylinderEnvelope where
  truncation : TaggedTruncation
  radiusSq : ℚ
  radiusSq_nonneg : 0 ≤ radiusSq
  diameter : ∀ {left right : QI},
    RawParserSemantics.Represented truncation.word left →
    RawParserSemantics.Represented truncation.word right →
      chordalSq (Proj.affine left) (Proj.affine right) ≤ radiusSq

namespace RawCylinderEnvelope

/-- The universal projective bound gives an initial certificate for every raw
prefix.  Later Sturm/CCL steps replace the unit radius by sharper bounds. -/
def unit (truncation : TaggedTruncation) : RawCylinderEnvelope where
  truncation := truncation
  radiusSq := 1
  radiusSq_nonneg := by norm_num
  diameter := by
    intro left right _ _
    exact chordalSq_le_one (Proj.affine_hasNonzeroCoordinate left)
      (Proj.affine_hasNonzeroCoordinate right)

/-- Prefix extension plus nonincreasing rational diameter. -/
def Refines (new old : RawCylinderEnvelope) : Prop :=
  old.truncation.word <+: new.truncation.word ∧ new.radiusSq ≤ old.radiusSq

theorem refines_refl (envelope : RawCylinderEnvelope) :
    envelope.Refines envelope := by
  exact ⟨List.prefix_refl _, le_rfl⟩

theorem Refines.trans {new middle old : RawCylinderEnvelope}
    (newMiddle : new.Refines middle) (middleOld : middle.Refines old) :
    new.Refines old := by
  exact ⟨middleOld.1.trans newMiddle.1, newMiddle.2.trans middleOld.2⟩

/-- Re-tag an existing diameter certificate by an arbitrary longer raw word.
This works uniformly inside unary runs and one- or two-bit sector fragments. -/
def restrict (old : RawCylinderEnvelope) (truncation : TaggedTruncation)
    (isPrefix : old.truncation.word <+: truncation.word) :
    RawCylinderEnvelope where
  truncation := truncation
  radiusSq := old.radiusSq
  radiusSq_nonneg := old.radiusSq_nonneg
  diameter := by
    intro left right leftRepresented rightRepresented
    exact old.diameter
      (RawParserSemantics.represented_of_prefix isPrefix leftRepresented)
      (RawParserSemantics.represented_of_prefix isPrefix rightRepresented)

theorem restrict_refines (old : RawCylinderEnvelope)
    (truncation : TaggedTruncation)
    (isPrefix : old.truncation.word <+: truncation.word) :
    (old.restrict truncation isPrefix).Refines old := by
  exact ⟨isPrefix, le_rfl⟩

/-- Replace a cylinder radius by any sharper certified rational bound. -/
def tighten (old : RawCylinderEnvelope) (radiusSq : ℚ)
    (radiusSq_nonneg : 0 ≤ radiusSq)
    (diameter : ∀ {left right : QI},
      RawParserSemantics.Represented old.truncation.word left →
      RawParserSemantics.Represented old.truncation.word right →
        chordalSq (Proj.affine left) (Proj.affine right) ≤ radiusSq) :
    RawCylinderEnvelope where
  truncation := old.truncation
  radiusSq := radiusSq
  radiusSq_nonneg := radiusSq_nonneg
  diameter := diameter

theorem tighten_refines (old : RawCylinderEnvelope) (radiusSq : ℚ)
    (radiusSq_nonneg : 0 ≤ radiusSq) (smaller : radiusSq ≤ old.radiusSq)
    (diameter : ∀ {left right : QI},
      RawParserSemantics.Represented old.truncation.word left →
      RawParserSemantics.Represented old.truncation.word right →
        chordalSq (Proj.affine left) (Proj.affine right) ≤ radiusSq) :
    (old.tighten radiusSq radiusSq_nonneg diameter).Refines old := by
  exact ⟨List.prefix_refl _, smaller⟩

end RawCylinderEnvelope

/-- A rational point shared by a winding box and a certified raw cylinder.
This is the finite coupling datum; no completed root point is introduced. -/
structure BoxCylinderCoupling where
  box : RatBox
  cylinder : RawCylinderEnvelope
  witness : QI
  witnessInside : box.Contains witness
  witnessRepresented :
    RawParserSemantics.Represented cylinder.truncation.word witness

namespace BoxCylinderCoupling

/-- Rational sum of the independent box and raw-cylinder error bounds. -/
def errorSq (coupling : BoxCylinderCoupling) : ℚ :=
  2 * (coupling.box.diagonalSq + coupling.cylinder.radiusSq)

theorem errorSq_nonneg (coupling : BoxCylinderCoupling) :
    0 ≤ coupling.errorSq := by
  exact mul_nonneg (by norm_num) (add_nonneg coupling.box.diagonalSq_nonneg
    coupling.cylinder.radiusSq_nonneg)

/-- The promised rational coupling inequality.  Any rational box point and
any rational realization of the tagged prefix are within the summed error. -/
theorem chordalSq_le_errorSq
    (coupling : BoxCylinderCoupling) {boxPoint cylinderPoint : QI}
    (boxInside : coupling.box.Contains boxPoint)
    (cylinderRepresented : RawParserSemantics.Represented
      coupling.cylinder.truncation.word cylinderPoint) :
    chordalSq (Proj.affine boxPoint) (Proj.affine cylinderPoint) ≤
      coupling.errorSq := by
  have triangle := chordalSq_triangle_two
    (Proj.affine_hasNonzeroCoordinate boxPoint)
    (Proj.affine_hasNonzeroCoordinate coupling.witness)
    (Proj.affine_hasNonzeroCoordinate cylinderPoint)
  have boxBound :
      chordalSq (Proj.affine boxPoint) (Proj.affine coupling.witness) ≤
        coupling.box.diagonalSq :=
    (CCLChordalEnvelope.chordalSq_affine_le_normSq
      boxPoint coupling.witness).trans
      (RatBox.normSq_sub_le_diagonalSq boxInside coupling.witnessInside)
  have cylinderBound :
      chordalSq (Proj.affine coupling.witness) (Proj.affine cylinderPoint) ≤
        coupling.cylinder.radiusSq :=
    coupling.cylinder.diameter coupling.witnessRepresented cylinderRepresented
  dsimp [errorSq]
  linarith

/-- Independent component bounds make the coupled error shrink. -/
theorem errorSq_le {coupling : BoxCylinderCoupling}
    {boxError cylinderError : ℚ}
    (boxBound : coupling.box.diagonalSq ≤ boxError)
    (cylinderBound : coupling.cylinder.radiusSq ≤ cylinderError) :
    coupling.errorSq ≤ 2 * (boxError + cylinderError) := by
  dsimp [errorSq]
  linarith

end BoxCylinderCoupling

/-- Two independently coupled root regions cannot share a projective
realization once their summed box/cylinder errors fall below the precomputed
coordinate gap. -/
theorem represented_points_not_equivalent_of_error_sum_lt_gap
    {B C : RatBox} {coordinateGap : ℚ}
    (gapPositive : 0 < coordinateGap)
    (coordinateSeparated :
      B.xUpper + coordinateGap ≤ C.xLower ∨
      C.xUpper + coordinateGap ≤ B.xLower ∨
      B.yUpper + coordinateGap ≤ C.yLower ∨
      C.yUpper + coordinateGap ≤ B.yLower)
    {left right : BoxCylinderCoupling}
    (leftBox : left.box = B) (rightBox : right.box = C)
    (thin : 4 * (left.errorSq + right.errorSq) <
      CCLChordalEnvelope.chordalGapSq B C coordinateGap)
    {leftPoint rightPoint : QI}
    (leftRepresented : RawParserSemantics.Represented
      left.cylinder.truncation.word leftPoint)
    (rightRepresented : RawParserSemantics.Represented
      right.cylinder.truncation.word rightPoint) :
    ¬(Proj.affine leftPoint).Equivalent (Proj.affine rightPoint) := by
  intro equivalent
  have insideB : B.Contains left.witness := by
    simpa only [← leftBox] using left.witnessInside
  have insideC : C.Contains right.witness := by
    simpa only [← rightBox] using right.witnessInside
  have lower := CCLChordalEnvelope.chordalGapSq_le gapPositive
    coordinateSeparated insideB insideC
  have middleZero :
      chordalSq (Proj.affine leftPoint) (Proj.affine rightPoint) = 0 :=
    chordalSq_eq_zero_of_equivalent equivalent
  have rightTriangle := chordalSq_triangle_two
    (Proj.affine_hasNonzeroCoordinate leftPoint)
    (Proj.affine_hasNonzeroCoordinate rightPoint)
    (Proj.affine_hasNonzeroCoordinate right.witness)
  have rightBound := right.chordalSq_le_errorSq right.witnessInside
    rightRepresented
  rw [chordalSq_comm] at rightBound
  have leftToRightWitness :
      chordalSq (Proj.affine leftPoint) (Proj.affine right.witness) ≤
        2 * right.errorSq := by
    linarith [rightTriangle, middleZero, rightBound]
  have leftTriangle := chordalSq_triangle_two
    (Proj.affine_hasNonzeroCoordinate left.witness)
    (Proj.affine_hasNonzeroCoordinate leftPoint)
    (Proj.affine_hasNonzeroCoordinate right.witness)
  have leftBound := left.chordalSq_le_errorSq left.witnessInside
    leftRepresented
  have upper :
      chordalSq (Proj.affine left.witness) (Proj.affine right.witness) ≤
        4 * (left.errorSq + right.errorSq) := by
    linarith [leftTriangle, leftBound, leftToRightWitness,
      left.errorSq_nonneg, right.errorSq_nonneg]
  linarith

end CCLRawCylinderEnvelope
end FTA
