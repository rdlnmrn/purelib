import RationalRotations.CoefficientProducts
import RationalRotations.FiniteFieldCounting
import RationalRotations.FiniteGeneratedSubgroups
import RationalRotations.IntroductoryExample
import RationalRotations.ProjectiveDuality
import RationalRotations.TernaryClifford

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

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-! ## Problem 68 -/

/-- Problem 68 repeats Conjecture 52 and is false without additional
nondegeneracy hypotheses. -/
theorem problemSixtyEight_false (twoNonzero : (2 : K) ≠ 0) :
    ¬ (@CoefficientProductParameters.AssociativityConjecture K _) :=
  CoefficientProductParameters.associativityConjecture_false twoNonzero

/-- Problem 68 is already false in the exact denominator-constant-one,
four-coefficient family printed in the paper. -/
theorem problemSixtyEight_normalized_false (twoNonzero : (2 : K) ≠ 0) :
    ¬ (@NormalizedCoefficientProductParameters.AssociativityConjecture K _) :=
  NormalizedCoefficientProductParameters.associativityConjecture_false
    twoNonzero

/-- Corrected Problem 68 over the rationals: a homogeneous five-parameter
coefficient product has zero as a two-sided identity and is associative on
every defined bracketing exactly when `α = β = ι ≠ 0` and `ιδ = -γ²`. -/
theorem problemSixtyEight_corrected
    (parameters : CoefficientProductParameters
      RFAP.ConstructiveFraction.Rational) :
    (parameters.HasZeroIdentity ∧ parameters.AssociativeWhereDefined) ↔
      parameters.constantCoefficient ≠ 0 ∧
      parameters.leftCoefficient = parameters.constantCoefficient ∧
      parameters.rightCoefficient = parameters.constantCoefficient ∧
      parameters.constantCoefficient * parameters.dotCoefficient =
        -(parameters.crossCoefficient ^ 2) :=
  parameters.rational_hardenedAssociativityClassification

/-! ## Problem 69 -/

/-- Pointwise membership in a half-spread fiber.  This is the finite equation
whose global fiber sizes Problem 69 asks to determine. -/
def InHalfSpreadFiber (rotation : Rotation K) (value : K) : Prop :=
  halfSpread rotation = value

instance [DecidableEq K] (rotation : Rotation K) (value : K) :
    Decidable (InHalfSpreadFiber rotation value) :=
  inferInstanceAs (Decidable (halfSpread rotation = value))

/-- A checked certificate for the parabolic class singled out in Problem 69.
The characteristic-polynomial identity is pointwise finite algebra and does
not enumerate the ambient field. -/
structure ParabolicRotationCertificate (rotation : Rotation K) where
  nonidentityMatrix : rotation.matrix ≠ Matrix3.identity
  characteristicUnipotent : ∀ X : K,
    Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3

/-- Cached local invariants of one rotation.  The global finite solution in
`FiniteFieldCounting` complements this pointwise profile with executable
carriers, classifications, and closed counts. -/
structure RotationInvariantProfile [DecidableEq K]
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) where
  halfSpreadValue : K
  halfSpread_spec : halfSpreadValue = halfSpread rotation
  quadranceClass : SquareClassRepresentative K
  quadranceClass_spec : quadranceClass =
    RotationQuadranceClass.ofRotation rotation twoNonzero

/-- The canonical pointwise profile requires only the finite calculations
already formalized in Theorems 58 and 61. -/
def rotationInvariantProfile [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    RotationInvariantProfile rotation twoNonzero where
  halfSpreadValue := halfSpread rotation
  halfSpread_spec := rfl
  quadranceClass := RotationQuadranceClass.ofRotation rotation twoNonzero
  quadranceClass_spec := rfl

/-! ## Problem 70 -/

namespace UnitQuaternionKernel

/-- The finite representative-level kernel studied in Problem 70. -/
def Contains (proportion : NonNullProportion K) : Prop :=
  proportion.HasUnitRepresentative

/-- The counted finite square-norm list is exactly this kernel predicate on
the canonical projective carrier. -/
theorem mem_finiteKernel_iff_contains
    (presentation : FiniteOddFieldPresentation K)
    (proportion : NonNullProportion K) :
    proportion ∈ presentation.quadranceClassKernel ↔
      proportion ∈ presentation.nonNullProjectiveRepresentatives ∧
        Contains proportion :=
  presentation.mem_quadranceClassKernel_iff_hasUnitRepresentative proportion

/-- Kernel membership depends only on the projective proportion, not on its
displayed representative. -/
theorem contains_respects_equivalent {left right : NonNullProportion K}
    (equivalent : left.Equivalent right) :
    Contains left ↔ Contains right :=
  NonNullProportion.hasUnitRepresentative_respects_equivalent equivalent

theorem mul_closed {left right : NonNullProportion K}
    (leftUnit : Contains left) (rightUnit : Contains right) :
    Contains (NonNullProportion.mul left right) := by
  rcases leftUnit with ⟨leftFactor, leftFactorNonzero, leftNorm⟩
  rcases rightUnit with ⟨rightFactor, rightFactorNonzero, rightNorm⟩
  refine ⟨leftFactor * rightFactor,
    RFAP.ExplicitField.mul_ne_zero leftFactorNonzero rightFactorNonzero, ?_⟩
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

theorem conjugate_closed {proportion : NonNullProportion K}
    (unit : Contains proportion) :
    Contains (NonNullProportion.conjugate proportion) := by
  rcases unit with ⟨factor, factorNonzero, unitNorm⟩
  refine ⟨factor, factorNonzero, ?_⟩
  change Proportion.norm
      (Proportion.scale factor
        (Proportion.conjugate proportion.toProportion)) = 1
  rw [Proportion.norm_scale, Proportion.norm_conjugate]
  rw [Proportion.norm_scale] at unitNorm
  exact unitNorm

theorem identity_contains (witness : NonNullProportion K) :
    Contains (NonNullProportion.identity witness) := by
  refine ⟨1, witness.one_ne_zero, ?_⟩
  change Proportion.norm
      (Proportion.scale 1 Proportion.identity) = 1
  rw [Proportion.one_scale]
  unfold Proportion.norm Proportion.identity
  rw [Vector.quadrance_zero]
  ring1

/-- The kernel laws that are finite and constructive, separated from the
density and finitely-generated subgroup questions in Problem 70. -/
structure Laws (witness : NonNullProportion K) where
  identity : Contains (NonNullProportion.identity witness)
  product : ∀ {left right : NonNullProportion K},
    Contains left → Contains right → Contains (NonNullProportion.mul left right)
  inverse : ∀ {proportion : NonNullProportion K},
    Contains proportion → Contains (NonNullProportion.conjugate proportion)

theorem laws (witness : NonNullProportion K) : Laws witness where
  identity := identity_contains witness
  product := mul_closed
  inverse := conjugate_closed

/-- The projective representative of a half turn about a non-null axis. -/
def halfTurnProportion (axis : Vector K) (axisNonNull : axis.quadrance ≠ 0) :
    NonNullProportion K where
  scalar := 0
  vector := axis
  normNonzero := by
    unfold Proportion.norm
    simpa only [pow_two, zero_mul, zero_add] using axisNonNull

theorem halfTurnProportion_rotationMatrix (axis : Vector K)
    (axisNonNull : axis.quadrance ≠ 0) :
    (halfTurnProportion axis axisNonNull).rotationMatrix =
      halfTurn axis axisNonNull := by
  exact NonNullProportion.rotationMatrix_eq_halfTurn
    (halfTurnProportion axis axisNonNull) rfl

/-- Problem 70's stated finite inclusion: a half turn about an axis of
nonzero square quadrance has a unit representative. -/
theorem halfTurn_of_square_axis_contains (axis : Vector K)
    (axisNonNull : axis.quadrance ≠ 0) (root : K)
    (rootSquare : root ^ 2 = axis.quadrance) :
    Contains (halfTurnProportion axis axisNonNull) := by
  have rootNonzero : root ≠ 0 := by
    intro rootZero
    apply axisNonNull
    calc
      axis.quadrance = root ^ 2 := rootSquare.symm
      _ = 0 := by rw [rootZero]; ring1
  refine ⟨root⁻¹, RFAP.ExplicitField.inv_ne_zero rootNonzero, ?_⟩
  have cancel := RFAP.ExplicitField.mul_inv_cancel root rootNonzero
  change Proportion.norm
      (Proportion.scale root⁻¹
        (halfTurnProportion axis axisNonNull).toProportion) = 1
  rw [Proportion.norm_scale]
  change root⁻¹ ^ 2 * (0 ^ 2 + axis.quadrance) = 1
  rw [show (0 : K) ^ 2 = 0 by ring1, zero_add]
  rw [← rootSquare]
  calc
    root⁻¹ ^ 2 * root ^ 2 = (root * root⁻¹) ^ 2 := by ring1
    _ = 1 := by rw [cancel]; ring1

end UnitQuaternionKernel

/-- The strongest finite-only form of Problem 70's finitely generated
subgroup classification.  It computes the exact finite `chi` quotient and
answers arbitrary signed-word evaluation, equality, kernel-membership, and
kernel-coset queries without constructing the generally infinite subgroup. -/
abbrev ProblemSeventyFiniteGeneratedClassification
    (rotations : List
      (Rotation RFAP.ConstructiveFraction.Rational)) :=
  FiniteGeneratedSubgroups.Classification rotations

def problemSeventyFiniteGeneratedClassification
    (rotations : List
      (Rotation RFAP.ConstructiveFraction.Rational)) :
    ProblemSeventyFiniteGeneratedClassification rotations :=
  FiniteGeneratedSubgroups.classify rotations

end RationalRotations
