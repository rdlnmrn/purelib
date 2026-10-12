module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Geometry.Rotations.Cayley.Cap
import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
import Purelib.Geometry.Rotations.Reflection
public import Purelib.Geometry.Rotations.FiniteField.Classification
import Purelib.Geometry.Rotations.Basic
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Geometry.Quadratic.Space3.NullTransport
import Purelib.Geometry.Quadratic.Space3.Perpendicular
import Purelib.Geometry.Rotations.Axis.Recovery
import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Algebra.Field.Finite.Odd

open Purelib.Geometry

open Purelib.Geometry.Quadratic.Space3

open Purelib.Geometry.Rotations

open Purelib.Geometry.Rotations.Axis

open Purelib.Geometry.Rotations.Basic

open Purelib.Geometry.Rotations.Cayley

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

section
public section

/-!
# Constructive conjugacy classification of finite-field parabolics

Problem 69 asks for the parabolic classes over the null directions.  The
counting layer gives unique null-direction and scalar coordinates.  This
module proves the stronger conjugacy-orbit interpretation: over every
displayed odd finite field, all nonidentity parabolic rotations form one
conjugacy class.  The conjugator is built from finitely selected reflections;
no quotient, basis extension, or choice principle is used.
-/

section

variable {K : Type*} [ExplicitField K]

namespace Purelib.Geometry.Rotations.FiniteField.Conjugacy

set_option genInjectivity false in
/-- A displayed special-orthogonal transformation carrying one nonzero null vector to another. -/
structure NullVectorTransport (source target :
  Coordinates3.Vector K) where
  /-- The retained special-orthogonal transport rotation. -/ rotation : Rotations.Basic.Rotation K
  /-- Right multiplication by the retained rotation sends the source vector to the target. -/ maps : Matrix3.rowMul
    source rotation.matrix = target

constructive_injectivity NullVectorTransport

/-- Construct a null-vector transport from two reflections. If the two null vectors have nonzero pairing, reflection in
their difference performs the move and a perpendicular reflection corrects orientation. If their pairing vanishes,
null-line rigidity gives the exact scale and a selected null partner supplies a non-null two-reflection route through
its negative. -/
@[expose] def nullVectorTransport [DecidableEq K]
    (source target : Coordinates3.Vector K)
    (sourceNull : source.quadrance = 0)
    (sourceNonzero : source ≠ Coordinates3.Vector.zero)
    (targetNull : target.quadrance = 0)
    (targetNonzero : target ≠ Coordinates3.Vector.zero)
    (twoNonzero : (2 : K) ≠ 0) :
    NullVectorTransport source target := by
  by_cases pairingNonzero : Coordinates3.Vector.dot source target ≠ 0
  · let difference := Coordinates3.Vector.sub source target
    have differenceQuadrance : difference.quadrance =
        -2 * Coordinates3.Vector.dot source target := by
      unfold difference
      rw [NullTransport.quadrance_sub_expansion, sourceNull, targetNull]
      ring1
    have differenceNonNull : difference.quadrance ≠ 0 := by
      rw [differenceQuadrance]
      exact ExplicitField.mul_ne_zero
        ((by intro negZero; have restored := congrArg (fun value : K => -value) negZero; rewrite [neg_neg,
          SubNegZeroMonoid.neg_zero] at restored; exact twoNonzero restored)) pairingNonzero
    let perpendicular := Perpendicular.perpendicularNonNullWitness target twoNonzero
    have targetPerpendicular :
        target.Perpendicular perpendicular.value := by
      unfold Coordinates3.Vector.Perpendicular at perpendicular ⊢
      rw [Coordinates3.Vector.dot_comm]
      exact perpendicular.perpendicular
    refine
      { rotation := Reflection.reflectionProductRotation difference perpendicular.value
          differenceNonNull perpendicular.nonNull
        maps := ?_ }
    change Matrix3.rowMul source
        (Matrix3.mul (Reflection.reflection difference differenceNonNull)
          (Reflection.reflection perpendicular.value perpendicular.nonNull)) = target
    rw [← Matrix3.rowMul_mul]
    change Matrix3.rowMul
        (Matrix3.rowMul source
          (Reflection.reflection (Coordinates3.Vector.sub source target) differenceNonNull))
        (Reflection.reflection perpendicular.value perpendicular.nonNull) = target
    rw [NullTransport.rowMul_reflection_difference source target
      (sourceNull.trans targetNull.symm) differenceNonNull]
    exact (Reflection.rowMul_reflection_eq_iff_perpendicular perpendicular.value
      perpendicular.nonNull twoNonzero target).2 targetPerpendicular
  · have pairingZero : Coordinates3.Vector.dot source target = 0 := by
      cases (inferInstance : DecidableEq K) (Coordinates3.Vector.dot source target) 0 with
      | isTrue equal => exact equal
      | isFalse different => exact False.elim (pairingNonzero different)
    let scaling := NullTransport.nullLineScaleOfPerpendicular source target sourceNull
      sourceNonzero targetNull pairingZero
    let factor := scaling.factor
    have targetScale : target = Coordinates3.Vector.scale factor source := scaling.target_eq
    have factorNonzero : factor ≠ 0 := by
      intro factorZero
      apply targetNonzero
      calc
        target = Coordinates3.Vector.scale factor source := targetScale
        _ = Coordinates3.Vector.scale 0 source := by rw [factorZero]
        _ = Coordinates3.Vector.zero := Coordinates3.Vector.zero_scale source
    let partner := NullTransport.nullPartner source sourceNull sourceNonzero twoNonzero
    let intermediate := Coordinates3.Vector.neg partner.value
    let firstMirror := Coordinates3.Vector.sub source intermediate
    let secondMirror := Coordinates3.Vector.sub intermediate target
    have intermediateNull : intermediate.quadrance = 0 := by
      unfold intermediate
      rw [Coordinates3.Vector.quadrance_neg, partner.valueNull]
    have intermediateNonzero : intermediate ≠ Coordinates3.Vector.zero := by
      intro intermediateZero
      apply partner.pairingNonzero
      calc
        Coordinates3.Vector.dot source partner.value =
            -Coordinates3.Vector.dot source intermediate := by
          unfold intermediate
          rw [Coordinates3.Vector.dot_neg_right]
          ring1
        _ = 0 := by rw [intermediateZero, Coordinates3.Vector.dot_zero_right]; ring1
    have sourceIntermediatePairing :
        Coordinates3.Vector.dot source intermediate =
          -Coordinates3.Vector.dot source partner.value := by
      unfold intermediate
      rw [Coordinates3.Vector.dot_neg_right]
    have intermediateTargetPairing :
        Coordinates3.Vector.dot intermediate target =
          -factor * Coordinates3.Vector.dot source partner.value := by
      rw [targetScale, Coordinates3.Vector.dot_scale_right]
      unfold intermediate
      rw [Coordinates3.Vector.dot_neg_left, Coordinates3.Vector.dot_comm partner.value source]
      ring1
    have firstMirrorQuadrance : firstMirror.quadrance =
        2 * Coordinates3.Vector.dot source partner.value := by
      unfold firstMirror
      rw [NullTransport.quadrance_sub_expansion, sourceNull, intermediateNull,
        sourceIntermediatePairing]
      ring1
    have firstMirrorNonNull : firstMirror.quadrance ≠ 0 := by
      rw [firstMirrorQuadrance]
      exact ExplicitField.mul_ne_zero twoNonzero
        partner.pairingNonzero
    have secondMirrorQuadrance : secondMirror.quadrance =
        2 * factor * Coordinates3.Vector.dot source partner.value := by
      unfold secondMirror
      rw [NullTransport.quadrance_sub_expansion, intermediateNull, targetNull,
        intermediateTargetPairing]
      ring1
    have secondMirrorNonNull : secondMirror.quadrance ≠ 0 := by
      rw [secondMirrorQuadrance]
      exact ExplicitField.mul_ne_zero
        (ExplicitField.mul_ne_zero twoNonzero factorNonzero)
        partner.pairingNonzero
    refine
      { rotation := Reflection.reflectionProductRotation firstMirror secondMirror
          firstMirrorNonNull secondMirrorNonNull
        maps := ?_ }
    change Matrix3.rowMul source
        (Matrix3.mul (Reflection.reflection firstMirror firstMirrorNonNull)
          (Reflection.reflection secondMirror secondMirrorNonNull)) = target
    rw [← Matrix3.rowMul_mul]
    change Matrix3.rowMul
        (Matrix3.rowMul source
          (Reflection.reflection (Coordinates3.Vector.sub source intermediate)
            firstMirrorNonNull))
        (Reflection.reflection (Coordinates3.Vector.sub intermediate target)
          secondMirrorNonNull) = target
    rw [NullTransport.rowMul_reflection_difference source intermediate
      (sourceNull.trans intermediateNull.symm) firstMirrorNonNull]
    exact NullTransport.rowMul_reflection_difference intermediate target
      (intermediateNull.trans targetNull.symm) secondMirrorNonNull

/-- The displayed cross-product transformation law for an arbitrary matrix. The adjugate transpose is the
denominator-free inverse-transpose factor. -/
theorem cross_rowMul_matrix (left right : Coordinates3.Vector K)
  (matrix : Coordinates3.Matrix3 K) :
    Coordinates3.Vector.cross (Matrix3.rowMul left matrix)
        (Matrix3.rowMul right matrix) =
      Matrix3.rowMul (Coordinates3.Vector.cross left right)
        (Matrix3.transpose (Matrix3.adjugate matrix)) := by
  ext <;> unfold Coordinates3.Vector.cross Matrix3.rowMul Matrix3.transpose
    Matrix3.adjugate <;> ring1

/-- Proper orthogonal matrices preserve the displayed cross product. -/
theorem cross_rowMul_rotation (rotation :
  Rotations.Basic.Rotation K)
    (left right : Coordinates3.Vector K) :
    Coordinates3.Vector.cross (Matrix3.rowMul left rotation.matrix)
        (Matrix3.rowMul right rotation.matrix) =
      Matrix3.rowMul (Coordinates3.Vector.cross left right) rotation.matrix := by
  rw [cross_rowMul_matrix, Spread.adjugate_rotation,
    Matrix3.transpose_transpose]

/-- Conjugating an anchor by a displayed rotation transports its vector by that rotation. -/
theorem anchor_conjugate_rotation (rotation :
  Rotations.Basic.Rotation K)
    (vector : Coordinates3.Vector K) :
    Matrix3.mul
        (Matrix3.mul (Matrix3.transpose rotation.matrix) (Antisymmetric.anchor vector))
        rotation.matrix =
      Antisymmetric.anchor (Matrix3.rowMul vector rotation.matrix) := by
  apply Matrix3.eq_of_rowMul_eq
  intro test
  calc
    Matrix3.rowMul test
        (Matrix3.mul
          (Matrix3.mul (Matrix3.transpose rotation.matrix) (Antisymmetric.anchor vector))
          rotation.matrix) =
      Matrix3.rowMul
        (Matrix3.rowMul
          (Matrix3.rowMul test (Matrix3.transpose rotation.matrix))
          (Antisymmetric.anchor vector)) rotation.matrix := by
      simp only [-eq_self, -iff_self, ← Matrix3.rowMul_mul]
      rfl
    _ = Matrix3.rowMul
        (Coordinates3.Vector.cross vector
          (Matrix3.rowMul test (Matrix3.transpose rotation.matrix)))
        rotation.matrix := by
      rw [Antisymmetric.rowMul_anchor]
    _ = Coordinates3.Vector.cross (Matrix3.rowMul vector rotation.matrix)
        (Matrix3.rowMul
          (Matrix3.rowMul test (Matrix3.transpose rotation.matrix))
          rotation.matrix) :=
      (cross_rowMul_rotation rotation vector
        (Matrix3.rowMul test (Matrix3.transpose rotation.matrix))).symm
    _ = Coordinates3.Vector.cross (Matrix3.rowMul vector rotation.matrix) test := by
      rw [Matrix3.rowMul_mul, Recovery.transpose_mul_rotation,
        Matrix3.rowMul_identity]
    _ = Matrix3.rowMul test
        (Antisymmetric.anchor (Matrix3.rowMul vector rotation.matrix)) :=
      (Antisymmetric.rowMul_anchor _ _).symm

/-- The cap denominator is invariant under a displayed rotation. -/
theorem capDenominator_rowMul_rotation (rotation :
  Rotations.Basic.Rotation K)
    (vector : Coordinates3.Vector K) :
    Cap.capDenominator (Matrix3.rowMul vector rotation.matrix) =
      Cap.capDenominator vector := by
  unfold Cap.capDenominator
  rw [Spread.quadrance_rowMul_rotation]

/-- Cayley caps are equivariant under displayed rotation conjugation. -/
theorem cap_conjugate_rotation (rotation :
  Rotations.Basic.Rotation K)
    (vector : Coordinates3.Vector K) (defined : Cap.capDenominator vector ≠ 0)
    (transformedDefined :
      Cap.capDenominator (Matrix3.rowMul vector rotation.matrix) ≠ 0) :
    Matrix3.mul
        (Matrix3.mul (Matrix3.transpose rotation.matrix)
          (Cap.cap vector defined)) rotation.matrix =
      Cap.cap (Matrix3.rowMul vector rotation.matrix) transformedDefined := by
  let matrix := rotation.matrix
  let inverse := Matrix3.transpose rotation.matrix
  let sourceAnchor := Antisymmetric.anchor vector
  let targetAnchor := Antisymmetric.anchor (Matrix3.rowMul vector rotation.matrix)
  have inverseMul : Matrix3.mul inverse matrix = Matrix3.identity := by
    unfold inverse matrix
    exact Recovery.transpose_mul_rotation rotation
  have matrixInverse : Matrix3.mul matrix inverse = Matrix3.identity := by
    unfold inverse matrix
    exact rotation.orthogonal
  have anchorConjugate :
      Matrix3.mul (Matrix3.mul inverse sourceAnchor) matrix =
        targetAnchor := by
    unfold inverse matrix sourceAnchor targetAnchor
    exact anchor_conjugate_rotation rotation vector
  have squareConjugate :
      Matrix3.mul
          (Matrix3.mul inverse
            (Matrix3.mul sourceAnchor sourceAnchor)) matrix =
        Matrix3.mul targetAnchor targetAnchor := by
    calc
      Matrix3.mul
          (Matrix3.mul inverse
            (Matrix3.mul sourceAnchor sourceAnchor)) matrix =
        Matrix3.mul (Matrix3.mul inverse sourceAnchor)
          (Matrix3.mul sourceAnchor matrix) := by
        simp only [-eq_self, -iff_self, Matrix3.mul_assoc]
        rfl
      _ = Matrix3.mul (Matrix3.mul inverse sourceAnchor)
          (Matrix3.mul Matrix3.identity
            (Matrix3.mul sourceAnchor matrix)) := by
        rw [Matrix3.identity_mul]
      _ = Matrix3.mul (Matrix3.mul inverse sourceAnchor)
          (Matrix3.mul (Matrix3.mul matrix inverse)
            (Matrix3.mul sourceAnchor matrix)) := by
        rw [matrixInverse]
      _ = Matrix3.mul
          (Matrix3.mul (Matrix3.mul inverse sourceAnchor) matrix)
          (Matrix3.mul inverse
            (Matrix3.mul sourceAnchor matrix)) := by
        simp only [-eq_self, -iff_self, Matrix3.mul_assoc]
        rfl
      _ = Matrix3.mul
          (Matrix3.mul (Matrix3.mul inverse sourceAnchor) matrix)
          (Matrix3.mul (Matrix3.mul inverse sourceAnchor) matrix) := by
        simp only [-eq_self, -iff_self, Matrix3.mul_assoc]
        rfl
      _ = Matrix3.mul targetAnchor targetAnchor := by
        rw [anchorConjugate]
  have denominatorEq :
      Cap.capDenominator (Matrix3.rowMul vector rotation.matrix) =
        Cap.capDenominator vector :=
    capDenominator_rowMul_rotation rotation vector
  unfold Cap.cap
  rw [denominatorEq]
  calc
    Matrix3.mul
        (Matrix3.mul inverse
          (Matrix3.add Matrix3.identity
            (Matrix3.scale (2 / Cap.capDenominator vector)
              (Matrix3.add sourceAnchor
                (Matrix3.mul sourceAnchor sourceAnchor))))) matrix =
      Matrix3.add
        (Matrix3.mul (Matrix3.mul inverse Matrix3.identity) matrix)
        (Matrix3.scale (2 / Cap.capDenominator vector)
          (Matrix3.add
            (Matrix3.mul (Matrix3.mul inverse sourceAnchor) matrix)
            (Matrix3.mul
              (Matrix3.mul inverse
                (Matrix3.mul sourceAnchor sourceAnchor)) matrix))) := by
      simp only [-eq_self, -iff_self, Matrix3.mul_add_left, Matrix3.mul_add_right,
        Matrix3.mul_scale_left, Matrix3.mul_scale_right]
      rfl
    _ = Matrix3.add Matrix3.identity
        (Matrix3.scale (2 / Cap.capDenominator vector)
          (Matrix3.add targetAnchor
            (Matrix3.mul targetAnchor targetAnchor))) := by
      rw [Matrix3.mul_identity, inverseMul, anchorConjugate,
        squareConjugate]

/-- Cap matrices ignore the proof object certifying a fixed vector's denominator once the vectors themselves are equal.
-/
theorem cap_eq_of_vector_eq {left right : Coordinates3.Vector K}
    (equal : left = right)
    (leftDefined : Cap.capDenominator left ≠ 0)
    (rightDefined : Cap.capDenominator right ≠ 0) :
    Cap.cap left leftDefined = Cap.cap right rightDefined := by
  subst right
  rfl

end Purelib.Geometry.Rotations.FiniteField.Conjugacy

section

variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

/-- One is nonzero in the displayed odd finite field. -/
private theorem oneNonzero
    (presentation : Presentation.FiniteOddFieldPresentation K) : (1 : K) ≠ 0 := by
  intro oneZero
  apply presentation.twoNonzero
  calc
    (2 : K) = 1 + 1 := by ring1
    _ = 0 := by rw [oneZero, zero_add]

/-- One is nonzero in the displayed odd finite field. -/
theorem oneNonzeroPublic
    (presentation : Presentation.FiniteOddFieldPresentation K) : (1 : K) ≠ 0 := by
  exact oneNonzero presentation

set_option genInjectivity false in
/-- Cached conjugator between two specified rotations. The equation uses the paper's row-vector convention, so the
displayed conjugate is `gᵀ * left * g`. -/
structure ParabolicConjugacyWitness
    (presentation : Presentation.FiniteOddFieldPresentation K)
    (left right : Rotations.Basic.Rotation K) where
  /-- The retained rotation implementing conjugacy. -/ conjugator : Rotations.Basic.Rotation K
  /-- Transposed-conjugator times left times conjugator equals the right rotation matrix. -/ conjugates :
    Matrix3.mul
        (Matrix3.mul (Matrix3.transpose conjugator.matrix) left.matrix)
        conjugator.matrix = right.matrix

constructive_injectivity ParabolicConjugacyWitness

/-- Every two nonidentity half-spread-zero rotations over a displayed odd finite field are constructively conjugate.
Their unique affine null anchors are recovered first; the two-reflection null-vector transport then supplies the
displayed conjugator. -/
@[expose] def parabolicConjugacyWitness
    (left right : Rotations.Basic.Rotation K)
    (leftSpreadZero : Spread.halfSpread left = 0)
    (leftNonidentity : left.matrix ≠ Matrix3.identity)
    (rightSpreadZero : Spread.halfSpread right = 0)
    (rightNonidentity : right.matrix ≠ Matrix3.identity) :
    presentation.ParabolicConjugacyWitness left right := by
  letI : DecidableEq K := presentation.eqDecidable
  let leftCoordinates := presentation.parabolicDirectionCoordinates left
    leftSpreadZero leftNonidentity
  let rightCoordinates := presentation.parabolicDirectionCoordinates right
    rightSpreadZero rightNonidentity
  let leftAnchor := Coordinates3.Vector.scale leftCoordinates.parameter
    leftCoordinates.direction
  let rightAnchor := Coordinates3.Vector.scale rightCoordinates.parameter
    rightCoordinates.direction
  have leftParameterNonzero : leftCoordinates.parameter ≠ 0 :=
    (presentation.mem_nonzeroScalars_iff leftCoordinates.parameter).1
      leftCoordinates.parameterMember |>.1
  have rightParameterNonzero : rightCoordinates.parameter ≠ 0 :=
    (presentation.mem_nonzeroScalars_iff rightCoordinates.parameter).1
      rightCoordinates.parameterMember |>.1
  have leftAnchorNonzero : leftAnchor ≠ Coordinates3.Vector.zero := by
    intro anchorZero
    apply leftParameterNonzero
    apply presentation.nullDirection_scale_injective
      leftCoordinates.directionMember
    calc
      Coordinates3.Vector.scale leftCoordinates.parameter leftCoordinates.direction =
          Coordinates3.Vector.zero := anchorZero
      _ = Coordinates3.Vector.scale 0 leftCoordinates.direction :=
        (Coordinates3.Vector.zero_scale leftCoordinates.direction).symm
  have rightAnchorNonzero : rightAnchor ≠ Coordinates3.Vector.zero := by
    intro anchorZero
    apply rightParameterNonzero
    apply presentation.nullDirection_scale_injective
      rightCoordinates.directionMember
    calc
      Coordinates3.Vector.scale rightCoordinates.parameter rightCoordinates.direction =
          Coordinates3.Vector.zero := anchorZero
      _ = Coordinates3.Vector.scale 0 rightCoordinates.direction :=
        (Coordinates3.Vector.zero_scale rightCoordinates.direction).symm
  let transport := Purelib.Geometry.Rotations.FiniteField.Conjugacy.nullVectorTransport leftAnchor rightAnchor
    leftCoordinates.scaledNull leftAnchorNonzero
    rightCoordinates.scaledNull rightAnchorNonzero presentation.twoNonzero
  have leftDefined : Purelib.Geometry.Rotations.Cayley.Cap.capDenominator leftAnchor ≠ 0 := by
    unfold Purelib.Geometry.Rotations.Cayley.Cap.capDenominator
    rw [leftCoordinates.scaledNull]
    simpa only [add_zero] using presentation.oneNonzeroPublic
  have rightDefined : Purelib.Geometry.Rotations.Cayley.Cap.capDenominator rightAnchor ≠ 0 := by
    unfold Purelib.Geometry.Rotations.Cayley.Cap.capDenominator
    rw [rightCoordinates.scaledNull]
    simpa only [add_zero] using presentation.oneNonzeroPublic
  have transportedDefined :
      Purelib.Geometry.Rotations.Cayley.Cap.capDenominator
        (Matrix3.rowMul leftAnchor transport.rotation.matrix) ≠ 0 := by
    rw [transport.maps]
    exact rightDefined
  refine
    { conjugator := transport.rotation
      conjugates := ?_ }
  have leftMatrix : left.matrix = Cap.cap leftAnchor leftDefined := by
    have rotationEqual := congrArg Rotation.matrix leftCoordinates.rotation_eq
    exact rotationEqual.trans (by rfl)
  have rightMatrix : right.matrix = Cap.cap rightAnchor rightDefined := by
    have rotationEqual := congrArg Rotation.matrix rightCoordinates.rotation_eq
    exact rotationEqual.trans (by rfl)
  rw [leftMatrix, rightMatrix]
  calc
    Matrix3.mul
        (Matrix3.mul (Matrix3.transpose transport.rotation.matrix)
          (Cap.cap leftAnchor leftDefined)) transport.rotation.matrix =
      Cap.cap (Matrix3.rowMul leftAnchor transport.rotation.matrix)
        transportedDefined :=
      Purelib.Geometry.Rotations.FiniteField.Conjugacy.cap_conjugate_rotation transport.rotation leftAnchor leftDefined
        transportedDefined
    _ = Cap.cap rightAnchor rightDefined :=
      FiniteField.Conjugacy.cap_eq_of_vector_eq transport.maps transportedDefined rightDefined

/-- The propositional conjugacy-orbit statement extracted from the executable classifier. -/
theorem
  all_nonidentity_parabolics_conjugate
    (presentation : Presentation.FiniteOddFieldPresentation K)
    (left right : Rotations.Basic.Rotation K)
    (leftSpreadZero : Spread.halfSpread left = 0)
    (leftNonidentity : left.matrix ≠ Matrix3.identity)
    (rightSpreadZero : Spread.halfSpread right = 0)
    (rightNonidentity : right.matrix ≠ Matrix3.identity) :
    ∃ conjugator : Rotations.Basic.Rotation K,
      Matrix3.mul
          (Matrix3.mul (Matrix3.transpose conjugator.matrix) left.matrix)
          conjugator.matrix = right.matrix := by
  let classification := presentation.parabolicConjugacyWitness left right
    leftSpreadZero leftNonidentity rightSpreadZero rightNonidentity
  exact ⟨classification.conjugator, classification.conjugates⟩

set_option genInjectivity false in
/-- The completed finite classification package: all count and fiber data from Problem 69 together with the stronger
single-conjugacy-class theorem for its nonidentity parabolic stratum. -/
structure
  ProblemSixtyNineClassificationSolution
  where
  /-- The complete retained finite rotation counting and fiber classification package. -/ counting :
    presentation.ProblemSixtyNineSolution
  /-- Construct a conjugator between any two nonidentity zero-half-spread rotations. -/ parabolicConjugacy : ∀ left
    right : Rotations.Basic.Rotation K,
    Spread.halfSpread left = 0 → left.matrix ≠ Matrix3.identity →
    Spread.halfSpread right = 0 → right.matrix ≠ Matrix3.identity →
      presentation.ParabolicConjugacyWitness left right

constructive_injectivity ProblemSixtyNineClassificationSolution

/-- Assemble the complete counting and conjugacy solution of Problem 69. -/
@[expose] def
  problemSixtyNineClassificationSolution
  :
    presentation.ProblemSixtyNineClassificationSolution where
  counting := presentation.problemSixtyNineSolution
  parabolicConjugacy := fun left right leftSpread leftNonidentity
      rightSpread rightNonidentity =>
    presentation.parabolicConjugacyWitness left right leftSpread
      leftNonidentity rightSpread rightNonidentity

end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

end

end

end
