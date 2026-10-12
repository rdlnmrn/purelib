module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.SquareClass.Basic
import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.Algebra.Quaternion.Projective.SquareClass
import Purelib.Geometry.Rotations.Projective.Correspondence
import Purelib.Geometry.Rotations.Projective.Action
import Purelib.Geometry.Rotations.Spread
public import Purelib.Geometry.Rotations.Projective.SquareClass
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Geometry.Rotations.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Algebra.Field.SquareClass.Basic

open Purelib.Algebra.Quaternion.Projective

open Purelib.Algebra.Quaternion.Projective.Basic

open Purelib.Algebra

open Purelib.Geometry.Rotations.Basic

open Purelib.Geometry.Rotations.Projective.Correspondence

open Purelib.Geometry
open Purelib.Geometry.Rotations.Projective

open Purelib.LinearAlgebra.Coordinates3

section
public section

/-!
# Rational rotations, Corollary 63 and Example 64

The finite obstruction is the existence of a norm-one representative in a
projective class.  The claims that the rational image or its index is
infinite are not used here; the two displayed nonsquare obstructions are
proved from canonical reduced fractions.
-/

namespace Purelib.Algebra.Quaternion.Projective.UnitObstruction

variable {K : Type*} [ExplicitField K]

namespace NonNullProportion

/-- A nonzero homogeneous scale takes the proportion to norm one.

The proposition retains an existential scale together with its nonzero and unit-norm certificates. -/
@[expose] def
  QuaternionObstruction.HasUnitRepresentative
  (proportion : Basic.NonNullProportion K) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧
    (Proportion.scale factor proportion.toProportion).norm = 1

set_option genInjectivity false in
/-- Retain an executable nonzero scale producing a unit-norm representative.

The factor is stored as data with its nonzero certificate and the exact norm-one equation. -/
structure UnitRepresentativeCertificate
    (proportion : Basic.NonNullProportion K) where
  /-- The retained homogeneous scale producing the unit norm. -/ factor : K
  /-- The retained normalizing scale is nonzero. -/ factorNonzero : factor ≠ 0
  /-- Scaling the original proportion by the retained factor gives norm one. -/ normOne : (Proportion.scale factor
    proportion.toProportion).norm = 1

constructive_injectivity UnitRepresentativeCertificate

open Purelib.Algebra.Quaternion.Projective.UnitObstruction.NonNullProportion in
/-- A retained unit-representative certificate witnesses existence of a unit representative. -/
theorem
  UnitRepresentativeCertificate.hasUnitRepresentative
    {proportion : Basic.NonNullProportion K}
    (certificate : UnitRepresentativeCertificate proportion) :
    (QuaternionObstruction.HasUnitRepresentative proportion) :=
  ⟨certificate.factor, certificate.factorNonzero, certificate.normOne⟩

/-- Construct the norm-one proportion using the certificate's original parent and retained normalizing factor. -/
@[expose] def UnitRepresentativeCertificate.unitProportion {proportion : Basic.NonNullProportion K}
    (certificate : UnitRepresentativeCertificate proportion) : Basic.NonNullProportion K :=
  Basic.NonNullProportion.scale certificate.factor certificate.factorNonzero proportion

/-- The retained normalizing certificate proves that its constructed proportion has norm one. -/
theorem UnitRepresentativeCertificate.unitProportion_normOne {proportion : Basic.NonNullProportion K}
    (certificate : UnitRepresentativeCertificate proportion) : certificate.unitProportion.toProportion.norm = 1 :=
  certificate.normOne

/-- The certificate's constructed norm-one proportion gives the same original rotation matrix. -/
theorem UnitRepresentativeCertificate.rotationMatrix_unitProportion {proportion : Basic.NonNullProportion K}
    (certificate : UnitRepresentativeCertificate proportion) :
    Action.NonNullProportion.rotationMatrix certificate.unitProportion =
      Action.NonNullProportion.rotationMatrix proportion :=
  Action.NonNullProportion.rotationMatrix_scale certificate.factor certificate.factorNonzero proportion

/-- The nonzero unit square-class representative certified by the input proportion. -/
@[expose] def unitSquareClass (proportion
  : Basic.NonNullProportion K) :
    SquareClassRepresentative K where
  value := 1
  nonzero := proportion.one_ne_zero

section
open Purelib.Algebra.Quaternion.Projective.UnitObstruction.NonNullProportion
/-- A proportion has a unit representative exactly when its quadrance class is trivial.

Both directions retain the same nonzero scale as the square-class factor. -/
theorem
  hasUnitRepresentative_iff_quadranceClass_trivial
    (proportion : Basic.NonNullProportion K) :
    (QuaternionObstruction.HasUnitRepresentative proportion) ↔
      (Quaternion.Projective.SquareClass.NonNullProportion.quadranceClass proportion).Equivalent
        (UnitObstruction.NonNullProportion.unitSquareClass proportion) := by
  constructor
  · rintro ⟨factor, factorNonzero, unitNorm⟩
    refine ⟨factor, factorNonzero, ?_⟩
    change (1 : K) = factor ^ 2 * proportion.toProportion.norm
    rw [← Proportion.norm_scale, unitNorm]
  · rintro ⟨factor, factorNonzero, unitValue⟩
    refine ⟨factor, factorNonzero, ?_⟩
    rw [Proportion.norm_scale]
    exact unitValue.symm

/-- Existence of a unit representative is invariant under projective equivalence.

The retained nonzero homogeneous equivalence factor transports the norm square class. -/
theorem
  QuaternionObstruction.hasUnitRepresentative_respects_equivalent
    {left right : Basic.NonNullProportion K} (equivalent : left.Equivalent right) :
    (QuaternionObstruction.HasUnitRepresentative left) ↔ (QuaternionObstruction.HasUnitRepresentative right) := by
  constructor
  · intro leftUnit
    have leftTrivial :=
      (UnitObstruction.NonNullProportion.hasUnitRepresentative_iff_quadranceClass_trivial left).1 leftUnit
    have classEquivalent := Quaternion.Projective.SquareClass.NonNullProportion.quadranceClass_respects_equivalent
      equivalent
    have rightToLeft := SquareClassRepresentative.equivalent_symm classEquivalent
    have rightTrivial := SquareClassRepresentative.equivalent_trans rightToLeft
      leftTrivial
    exact (UnitObstruction.NonNullProportion.hasUnitRepresentative_iff_quadranceClass_trivial right).2
      (SquareClassRepresentative.equivalent_trans rightTrivial (by
        refine ⟨1, right.one_ne_zero, ?_⟩
        change (1 : K) = 1 ^ 2 * 1
        ring1))
  · intro rightUnit
    have rightTrivial :=
      (UnitObstruction.NonNullProportion.hasUnitRepresentative_iff_quadranceClass_trivial right).1 rightUnit
    have classEquivalent := Quaternion.Projective.SquareClass.NonNullProportion.quadranceClass_respects_equivalent
      equivalent
    have leftTrivial := SquareClassRepresentative.equivalent_trans
      classEquivalent rightTrivial
    exact (UnitObstruction.NonNullProportion.hasUnitRepresentative_iff_quadranceClass_trivial left).2
      (SquareClassRepresentative.equivalent_trans leftTrivial (by
        refine ⟨1, left.one_ne_zero, ?_⟩
        change (1 : K) = 1 ^ 2 * 1
        ring1))

/-- The conjugate-left relative product admits a unit-norm representative.

This predicate keeps both displayed non-null inputs and uses their actual quaternion product. -/
@[expose] def InSameUnitKernelCoset (left
  right : Basic.NonNullProportion K) : Prop :=
  QuaternionObstruction.HasUnitRepresentative (Basic.NonNullProportion.mul (Basic.NonNullProportion.conjugate left)
    right)

end

/-- Two proportions share a unit-kernel coset exactly when their quadrance classes are equivalent.

Both directions construct the needed nonzero factor from the original norms and the supplied equivalence or unit
certificate. -/
theorem
  inSameUnitKernelCoset_iff_quadranceClass_equivalent
    (left right : Basic.NonNullProportion K) :
    UnitObstruction.NonNullProportion.InSameUnitKernelCoset left right ↔
      (Quaternion.Projective.SquareClass.NonNullProportion.quadranceClass left).Equivalent
        (Quaternion.Projective.SquareClass.NonNullProportion.quadranceClass right) := by
  have conjugateNorm :
      (Basic.NonNullProportion.conjugate left).toProportion.norm = left.toProportion.norm :=
    Proportion.norm_conjugate left.toProportion
  constructor
  · rintro ⟨unitFactor, unitFactorNonzero, unitNorm⟩
    have relativeNorm :
        unitFactor ^ 2 *
            (left.toProportion.norm * right.toProportion.norm) = 1 := by
      change Proportion.norm
          (Proportion.scale unitFactor
            (Basic.NonNullProportion.mul (Basic.NonNullProportion.conjugate left) right).toProportion) = 1 at unitNorm
      rw [Proportion.norm_scale, Basic.NonNullProportion.mul_norm, conjugateNorm] at unitNorm
      exact unitNorm
    refine ⟨unitFactor * right.toProportion.norm,
      ExplicitField.mul_ne_zero unitFactorNonzero right.normNonzero, ?_⟩
    change right.toProportion.norm =
      (unitFactor * right.toProportion.norm) ^ 2 *
        left.toProportion.norm
    calc
      right.toProportion.norm =
          1 * right.toProportion.norm := by ring1
      _ = (unitFactor ^ 2 *
            (left.toProportion.norm * right.toProportion.norm)) *
          right.toProportion.norm := by rw [relativeNorm]
      _ = (unitFactor * right.toProportion.norm) ^ 2 *
          left.toProportion.norm := by ring1
  · rintro ⟨classFactor, classFactorNonzero, classEquation⟩
    let normalizer := classFactor * left.toProportion.norm
    have normalizerNonzero : normalizer ≠ 0 :=
      ExplicitField.mul_ne_zero classFactorNonzero left.normNonzero
    refine ⟨normalizer⁻¹,
      ExplicitField.inv_ne_zero normalizerNonzero, ?_⟩
    rw [Proportion.norm_scale, Basic.NonNullProportion.mul_norm, conjugateNorm]
    change right.toProportion.norm =
      classFactor ^ 2 * left.toProportion.norm at classEquation
    have normalizerCancel :=
      ExplicitField.mul_inv_cancel normalizer normalizerNonzero
    calc
      normalizer⁻¹ ^ 2 *
          (left.toProportion.norm * right.toProportion.norm) =
        normalizer⁻¹ ^ 2 * normalizer ^ 2 := by
          rw [classEquation]
          unfold normalizer
          ring1
      _ = (normalizer * normalizer⁻¹) ^ 2 := by ring1
      _ = 1 := by rw [normalizerCancel]; ring1

end NonNullProportion

namespace RotationQuadranceClass

open Purelib.Algebra.Quaternion.Projective.UnitObstruction.NonNullProportion in
/-- The retained projective representative of a rotation admits a unit quaternion.

Decidable equality and nonzero two support the explicit rotation-to-proportion construction. -/
@[expose] def HasUnitQuaternion
  [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) : Prop :=
  (QuaternionObstruction.HasUnitRepresentative (RotationProportion.ofRotation rotation twoNonzero))

/-- A rotation has a unit quaternion exactly when its retained quadrance class is trivial.

The same explicit non-null projective representative is used on both sides. -/
theorem
  hasUnitQuaternion_iff_trivial
  [DecidableEq K]
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    UnitObstruction.RotationQuadranceClass.HasUnitQuaternion rotation twoNonzero ↔
      (Rotations.Projective.SquareClass.RotationQuadranceClass.ofRotation rotation twoNonzero).Equivalent
        (UnitObstruction.NonNullProportion.unitSquareClass (RotationProportion.ofRotation rotation twoNonzero)) :=
  UnitObstruction.NonNullProportion.hasUnitRepresentative_iff_quadranceClass_trivial _

/-- The stored unit-quaternion predicate is equivalent to an actual norm-one preimage of the original rotation.

The forward direction normalizes its same cached proportion with the retained factor. Projective faithfulness
transports any supplied unit preimage back to that cached proportion in the reverse direction. -/
theorem hasUnitQuaternion_iff_unitPreimage [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    HasUnitQuaternion rotation twoNonzero ↔
      ∃ value : Basic.NonNullProportion K, Action.NonNullProportion.rotation value = rotation ∧
        value.toProportion.norm = 1 := by
  let proportion := RotationProportion.ofRotation rotation twoNonzero
  constructor
  · rintro ⟨factor, factorNonzero, normOne⟩
    let certificate : NonNullProportion.UnitRepresentativeCertificate proportion :=
      ⟨factor, factorNonzero, normOne⟩
    refine ⟨certificate.unitProportion, ?_, certificate.unitProportion_normOne⟩
    apply Rotation.eq_of_matrix_eq
    exact certificate.rotationMatrix_unitProportion.trans
      (RotationProportion.ofRotation_rotationMatrix rotation twoNonzero)
  · rintro ⟨value, represents, normOne⟩
    have equivalent : proportion.Equivalent value :=
      Correspondence.NonNullProportion.equivalent_of_rotationMatrix_eq proportion value twoNonzero
        ((RotationProportion.ofRotation_rotationMatrix rotation twoNonzero).trans
          (congrArg Rotation.matrix represents).symm)
    apply (NonNullProportion.QuaternionObstruction.hasUnitRepresentative_respects_equivalent equivalent).mpr
    refine ⟨1, value.one_ne_zero, ?_⟩
    rw [Proportion.one_scale]
    exact normOne

/-- A represented rotation admits a unit quaternion exactly when its original proportion admits normalization.

The cached rotation preimage and supplied original proportion are related by their actual nonzero projective factor. -/
theorem hasUnitQuaternion_rotation_iff [DecidableEq K] (proportion : Basic.NonNullProportion K)
    (twoNonzero : (2 : K) ≠ 0) :
    HasUnitQuaternion (Action.NonNullProportion.rotation proportion) twoNonzero ↔
      NonNullProportion.QuaternionObstruction.HasUnitRepresentative proportion := by
  let canonical := RotationProportion.ofRotation (Action.NonNullProportion.rotation proportion) twoNonzero
  have equivalent : canonical.Equivalent proportion :=
    Correspondence.NonNullProportion.equivalent_of_rotationMatrix_eq canonical proportion twoNonzero
      (RotationProportion.ofRotation_rotationMatrix (Action.NonNullProportion.rotation proportion) twoNonzero)
  exact NonNullProportion.QuaternionObstruction.hasUnitRepresentative_respects_equivalent equivalent

/-- A rotation admits a unit quaternion exactly when its retained norm-class value has a square root. -/
theorem hasUnitQuaternion_iff_norm_square [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    HasUnitQuaternion rotation twoNonzero ↔
      ∃ root : K, root ^ 2 =
        (Rotations.Projective.SquareClass.RotationQuadranceClass.ofRotation rotation twoNonzero).value :=
  (hasUnitQuaternion_iff_trivial rotation twoNonzero).trans
    (SquareClassRepresentative.equivalent_one_iff_square _)

/-- Away from half turns, a unit quaternion exists exactly when one minus the half spread is a square. -/
theorem hasUnitQuaternion_iff_complement_square [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) (notHalfTurn : Rotations.Spread.halfSpread rotation ≠ 1) :
    HasUnitQuaternion rotation twoNonzero ↔ ∃ root : K, root ^ 2 = 1 - Rotations.Spread.halfSpread rotation :=
  (hasUnitQuaternion_iff_norm_square rotation twoNonzero).trans
    (SquareClassRepresentative.square_iff_of_equivalent
      (Rotations.Projective.SquareClass.RotationQuadranceClass.ofRotation_one_sub_halfSpread
        rotation twoNonzero notHalfTurn))

/-- A half turn admits a unit quaternion exactly when its original axis quadrance is a square. -/
theorem hasUnitQuaternion_halfTurn_iff_axis_square [DecidableEq K] (axis : Vector K)
    (axisNonNull : axis.quadrance ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    HasUnitQuaternion (Rotations.Reflection.halfTurnRotation axis axisNonNull) twoNonzero ↔
      ∃ root : K, root ^ 2 = axis.quadrance :=
  (hasUnitQuaternion_iff_norm_square (Rotations.Reflection.halfTurnRotation axis axisNonNull) twoNonzero).trans
    (SquareClassRepresentative.square_iff_of_equivalent
      (Rotations.Projective.SquareClass.RotationQuadranceClass.ofRotation_halfTurn axis axisNonNull twoNonzero))

end RotationQuadranceClass

end Purelib.Algebra.Quaternion.Projective.UnitObstruction

end

section
public section

/-!
# Section 13.3: open problems

Problem 68 is refuted as printed by the projection counterexample already
recorded for Conjecture 52; its hardened unital five-parameter replacement is
proved over the paper's primary rational field.  For Problem 69, the missing PDF glyph is the
quadrance-class homomorphism `chi`, represented here by
`RotationQuadranceClass.ofRotation`; the exact excluded affine quadric is
`Q = -1`.  The executable finite enumerators and small-field regression
tables live in `FiniteFieldCounting`.  Problems 70 and 71 retain the pointwise
finite data and algebraic parts that follow from the preceding development;
Problem 70's finitely generated subgroup clause is classified through exact
arbitrary finite-word queries and its complete finite `chi` quotient;
Problem 72 is completed by the constructive projective polarity in
`ProjectiveDuality`.
-/

namespace Purelib.Algebra.Quaternion.Projective.UnitObstruction

variable {K : Type*} [ExplicitField K]
section UnitQuaternionKernel

section
open Purelib.Algebra.Quaternion.Projective.UnitObstruction.NonNullProportion
/-- The non-null proportion belongs to the unit-representative kernel. -/
@[expose] def NonNullProportion.OpenProblems.Contains
  (proportion : Basic.NonNullProportion K) : Prop :=
  (QuaternionObstruction.HasUnitRepresentative proportion)

/-- Unit-representative kernel membership is invariant under projective equivalence. -/
theorem
  NonNullProportion.OpenProblems.contains_respects_equivalent
  {left right : Basic.NonNullProportion K}
    (equivalent : left.Equivalent right) :
    OpenProblems.Contains left ↔ OpenProblems.Contains right :=
  QuaternionObstruction.hasUnitRepresentative_respects_equivalent equivalent

end

section
open Purelib.Algebra.Quaternion.Projective.UnitObstruction.NonNullProportion
/-- The unit-representative kernel is closed under quaternion multiplication.

The product of the retained nonzero normalizing factors certifies the product norm. -/
theorem UnitQuaternionKernel.mul_closed {left right :
  Basic.NonNullProportion K}
    (leftUnit : OpenProblems.Contains left) (rightUnit : OpenProblems.Contains right) :
    OpenProblems.Contains (Basic.NonNullProportion.mul left right) := by
  rcases leftUnit with ⟨leftFactor, leftFactorNonzero, leftNorm⟩
  rcases rightUnit with ⟨rightFactor, rightFactorNonzero, rightNorm⟩
  refine ⟨leftFactor * rightFactor,
    ExplicitField.mul_ne_zero leftFactorNonzero rightFactorNonzero, ?_⟩
  change Proportion.norm
      (Proportion.scale (leftFactor * rightFactor)
        (Proportion.mul left.toProportion right.toProportion)) = 1
  rw [Proportion.norm_scale, Proportion.norm_mul]
  rw [Proportion.norm_scale] at leftNorm rightNorm
  calc
    (leftFactor * rightFactor) ^ 2 *
          (left.toProportion.norm * right.toProportion.norm) =
        (leftFactor ^ 2 * left.toProportion.norm) *
          (rightFactor ^ 2 * right.toProportion.norm) := by ring1
    _ = 1 := by rw [leftNorm, rightNorm, one_mul]

/-- The unit-representative kernel is closed under conjugation.

The original nonzero normalizing factor works because conjugation preserves norm. -/
theorem UnitQuaternionKernel.conjugate_closed {proportion :
  Basic.NonNullProportion K}
    (unit : OpenProblems.Contains proportion) :
    OpenProblems.Contains (Basic.NonNullProportion.conjugate proportion) := by
  rcases unit with ⟨factor, factorNonzero, unitNorm⟩
  refine ⟨factor, factorNonzero, ?_⟩
  change Proportion.norm
      (Proportion.scale factor
        (Proportion.conjugate proportion.toProportion)) = 1
  rw [Proportion.norm_scale, Proportion.norm_conjugate]
  rw [Proportion.norm_scale] at unitNorm
  exact unitNorm

/-- The certified unit quaternion proportion belongs to the unit-representative kernel. -/
theorem UnitQuaternionKernel.identity_contains (witness :
  Basic.NonNullProportion K) :
    OpenProblems.Contains (Basic.NonNullProportion.identity witness) := by
  refine ⟨1, witness.one_ne_zero, ?_⟩
  change Proportion.norm
      (Proportion.scale 1 Proportion.identity) = 1
  rw [Proportion.one_scale]
  unfold Proportion.norm Proportion.identity
  rw [Vector.quadrance_zero]
  ring1

/-- Retain the identity, product and conjugation closure laws of the unit kernel.

A non-null witness supplies the certified identity representative; no quotient group or carrier enumeration is
introduced. -/
structure UnitQuaternionKernel.Laws (witness :
  Basic.NonNullProportion K) where
  /-- The certified identity representative is in the kernel. -/ identity : OpenProblems.Contains
    (Basic.NonNullProportion.identity witness)
  /-- Products of two kernel representatives remain in the kernel. -/ product : ∀ {left right : Basic.NonNullProportion
    K},
    OpenProblems.Contains left → OpenProblems.Contains right → OpenProblems.Contains (Basic.NonNullProportion.mul left
      right)
  /-- Conjugation preserves kernel membership. -/ inverse : ∀ {proportion : Basic.NonNullProportion K},
    OpenProblems.Contains proportion → OpenProblems.Contains (Basic.NonNullProportion.conjugate proportion)

end

open Purelib.Algebra.Quaternion.Projective.UnitObstruction.UnitQuaternionKernel in
open Purelib.Algebra.Quaternion.Projective.UnitObstruction in
/-- Assemble the finite closure laws of the unit-representative kernel.

The supplied non-null witness determines the identity certificate. -/
theorem UnitQuaternionKernel.laws (witness :
  Basic.NonNullProportion K) : Laws witness where
  identity := UnitQuaternionKernel.identity_contains witness
  product := UnitQuaternionKernel.mul_closed
  inverse := UnitQuaternionKernel.conjugate_closed

open Purelib.Algebra.Quaternion.Projective.UnitObstruction.NonNullProportion in
/-- A pure-vector proportion of nonzero square quadrance lies in the unit kernel.

The supplied square root is necessarily nonzero, and its inverse normalizes the retained axis to unit norm. -/
theorem
  UnitQuaternionKernel.halfTurn_of_square_axis_contains
  (axis : Vector K)
    (axisNonNull : axis.quadrance ≠ 0) (root : K)
    (rootSquare : root ^ 2 = axis.quadrance) :
    OpenProblems.Contains (Basic.NonNullProportion.ofNonNullVector axis axisNonNull) := by
  have rootNonzero : root ≠ 0 := by
    intro rootZero
    apply axisNonNull
    calc
      axis.quadrance = root ^ 2 := rootSquare.symm
      _ = 0 := by rw [rootZero]; ring1
  refine ⟨root⁻¹, ExplicitField.inv_ne_zero rootNonzero, ?_⟩
  have cancel := ExplicitField.mul_inv_cancel root rootNonzero
  change Proportion.norm
      (Proportion.scale root⁻¹
        (Basic.NonNullProportion.ofNonNullVector axis axisNonNull).toProportion) = 1
  rw [Proportion.norm_scale]
  change root⁻¹ ^ 2 * (0 ^ 2 + axis.quadrance) = 1
  rw [show (0 : K) ^ 2 = 0 by ring1, zero_add]
  rw [← rootSquare]
  calc
    root⁻¹ ^ 2 * root ^ 2 = (root * root⁻¹) ^ 2 := by ring1
    _ = 1 := by rw [cancel]; ring1

end UnitQuaternionKernel
end Purelib.Algebra.Quaternion.Projective.UnitObstruction

end
