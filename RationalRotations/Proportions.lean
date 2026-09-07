import RationalRotations.Breakdowns

/-!
# Rational rotations, section 11: projective rotation proportions

Projective coordinates are kept as finite displayed representatives.  The
equivalence relation stores an explicit nonzero scale witness instead of
forming a quotient or selecting a normalized representative.  Non-null
representatives cache the norm certificate consumed by every executable
rotation and product below.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- Definition 54's displayed four coordinates `(x,v)=(x,t,r,s)`. -/
@[ext]
structure Proportion (K : Type*) where
  scalar : K
  vector : Vector K
deriving DecidableEq

namespace Proportion

/-- The excluded zero representative. -/
def zero : Proportion K := ⟨0, Vector.zero⟩

/-- The four-square quadrance `N(x,v)=x²+Q(v)`. -/
def norm (proportion : Proportion K) : K :=
  proportion.scalar ^ 2 + proportion.vector.quadrance

/-- A displayed representative is nonzero when it is not the zero quadruple. -/
def IsNonzero (proportion : Proportion K) : Prop := proportion ≠ zero

/-- Definition 54's null locus. -/
def IsNull (proportion : Proportion K) : Prop := proportion.norm = 0

/-- Coordinatewise homogeneous rescaling. -/
def scale (factor : K) (proportion : Proportion K) : Proportion K :=
  ⟨factor * proportion.scalar, Vector.scale factor proportion.vector⟩

/-- Equality of represented projective points by an explicit nonzero
homogeneous scale. -/
def Equivalent (left right : Proportion K) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧ right = scale factor left

@[simp] theorem one_scale (proportion : Proportion K) :
    scale 1 proportion = proportion := by
  apply Proportion.ext
  · unfold scale
    ring1
  · exact Vector.one_scale proportion.vector

theorem scale_scale (first second : K) (proportion : Proportion K) :
    scale first (scale second proportion) =
      scale (first * second) proportion := by
  apply Proportion.ext
  · unfold scale
    ring1
  · unfold scale
    rw [Vector.scale_scale]

theorem norm_zero : norm (zero : Proportion K) = 0 := by
  unfold norm zero
  rw [Vector.quadrance_zero]
  ring1

/-- Rescaling changes the norm by the expected square. -/
theorem norm_scale (factor : K) (proportion : Proportion K) :
    norm (scale factor proportion) = factor ^ 2 * norm proportion := by
  unfold norm scale
  rw [Vector.quadrance_scale]
  ring1

/-- Definition 56 on displayed representatives. -/
def mul (left right : Proportion K) : Proportion K :=
  ⟨left.scalar * right.scalar - Vector.dot left.vector right.vector,
    Vector.sub
      (Vector.add
        (Vector.scale left.scalar right.vector)
        (Vector.scale right.scalar left.vector))
      (Vector.cross left.vector right.vector)⟩

/-- Theorem 57's Euler four-square identity, proved directly in the eight
displayed coordinates. -/
theorem norm_mul (left right : Proportion K) :
    norm (mul left right) = norm left * norm right := by
  unfold norm mul Vector.quadrance Vector.dot Vector.sub Vector.add
    Vector.scale Vector.cross
  ring1

/-- The representative product is bilinear under independent rescalings. -/
theorem mul_scale_both (leftFactor rightFactor : K)
    (left right : Proportion K) :
    mul (scale leftFactor left) (scale rightFactor right) =
      scale (leftFactor * rightFactor) (mul left right) := by
  apply Proportion.ext
  · unfold mul scale
    simp only [Vector.dot_scale_left, Vector.dot_scale_right]
    ring1
  · apply Vector.ext <;> unfold mul scale Vector.scale Vector.sub Vector.add
      Vector.cross <;> ring1

/-- Quaternion associativity is a finite polynomial identity on the displayed
representatives. -/
theorem mul_assoc (first second third : Proportion K) :
    mul (mul first second) third = mul first (mul second third) := by
  apply Proportion.ext
  · unfold mul Vector.dot Vector.sub Vector.add Vector.scale Vector.cross
    ring1
  · apply Vector.ext <;> unfold mul Vector.dot Vector.sub Vector.add
      Vector.scale Vector.cross <;> ring1

/-- The scalar identity representative `(1,0)`. -/
def identity : Proportion K := ⟨1, Vector.zero⟩

@[simp] theorem identity_mul (proportion : Proportion K) :
    mul identity proportion = proportion := by
  apply Proportion.ext
  · unfold mul identity
    rw [Vector.dot_zero_left]
    ring1
  · apply Vector.ext <;> unfold mul identity Vector.zero Vector.sub
      Vector.add Vector.scale Vector.cross <;> ring1

@[simp] theorem mul_identity (proportion : Proportion K) :
    mul proportion identity = proportion := by
  apply Proportion.ext
  · unfold mul identity
    rw [Vector.dot_zero_right]
    ring1
  · apply Vector.ext <;> unfold mul identity Vector.zero Vector.sub
      Vector.add Vector.scale Vector.cross <;> ring1

/-- Quaternion conjugation of a displayed representative. -/
def conjugate (proportion : Proportion K) : Proportion K :=
  ⟨proportion.scalar, Vector.neg proportion.vector⟩

@[simp] theorem conjugate_conjugate (proportion : Proportion K) :
    conjugate (conjugate proportion) = proportion := by
  apply Proportion.ext
  · rfl
  · apply Vector.ext <;> unfold conjugate Vector.neg <;> ring1

/-- Quaternion conjugation reverses one displayed product. -/
theorem conjugate_mul_reverse (left right : Proportion K) :
    conjugate (mul left right) = mul (conjugate right) (conjugate left) := by
  apply Proportion.ext
  · unfold conjugate mul Vector.dot Vector.neg
    ring1
  · apply Vector.ext <;>
      unfold conjugate mul Vector.dot Vector.neg Vector.sub Vector.add
        Vector.scale Vector.cross <;> ring1

theorem norm_conjugate (proportion : Proportion K) :
    norm (conjugate proportion) = norm proportion := by
  unfold norm conjugate
  rw [Vector.quadrance_neg]

theorem mul_conjugate (proportion : Proportion K) :
    mul proportion (conjugate proportion) =
      scale (norm proportion) identity := by
  apply Proportion.ext
  · unfold mul conjugate scale identity norm Vector.quadrance Vector.dot
      Vector.neg
    ring1
  · apply Vector.ext <;> unfold mul conjugate scale identity norm
      Vector.quadrance Vector.dot Vector.zero Vector.neg Vector.sub Vector.add
      Vector.scale Vector.cross <;> ring1

theorem conjugate_mul (proportion : Proportion K) :
    mul (conjugate proportion) proportion =
      scale (norm proportion) identity := by
  apply Proportion.ext
  · unfold mul conjugate scale identity norm Vector.quadrance Vector.dot
      Vector.neg
    ring1
  · apply Vector.ext <;> unfold mul conjugate scale identity norm
      Vector.quadrance Vector.dot Vector.zero Vector.neg Vector.sub Vector.add
      Vector.scale Vector.cross <;> ring1

end Proportion

/-- The finite algebraic content of the paper's assertion that ordered
fields have no nonzero null proportions.  It avoids importing a general
infinite ordered-field hierarchy. -/
structure SumFourSquaresSeparate (K : Type*) [RFAP.ExplicitField K] where
  separate : ∀ scalar t r s : K,
    scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 = 0 →
      scalar = 0 ∧ t = 0 ∧ r = 0 ∧ s = 0

theorem proportion_eq_zero_of_norm_eq_zero
    (certificate : SumFourSquaresSeparate K) (proportion : Proportion K)
    (null : proportion.norm = 0) : proportion = Proportion.zero := by
  have coordinates := certificate.separate proportion.scalar
    proportion.vector.t proportion.vector.r proportion.vector.s (by
      unfold Proportion.norm Vector.quadrance Vector.dot at null
      simpa only [pow_two, add_assoc] using null)
  apply Proportion.ext
  · exact coordinates.1
  · exact Vector.ext coordinates.2.1 coordinates.2.2.1 coordinates.2.2.2

theorem proportion_norm_ne_zero_of_isNonzero
    (certificate : SumFourSquaresSeparate K) (proportion : Proportion K)
    (nonzero : proportion.IsNonzero) : proportion.norm ≠ 0 := by
  intro null
  exact nonzero (proportion_eq_zero_of_norm_eq_zero certificate proportion null)

/-- The repository's executable rationals carry the required four-square
separation certificate. -/
theorem rationalSumFourSquaresSeparate :
    SumFourSquaresSeparate RFAP.ConstructiveFraction.Rational where
  separate := by
    intro scalar t r s sumZero
    have scalarNonnegative :=
      RFAP.ConstructiveFraction.sq_nonneg_direct scalar
    have tNonnegative := RFAP.ConstructiveFraction.sq_nonneg_direct t
    have rNonnegative := RFAP.ConstructiveFraction.sq_nonneg_direct r
    have sNonnegative := RFAP.ConstructiveFraction.sq_nonneg_direct s
    have scalarUpper : scalar ^ 2 ≤ 0 := by
      have remainingNonnegative : 0 ≤ t ^ 2 + r ^ 2 + s ^ 2 :=
        add_nonneg (add_nonneg tNonnegative rNonnegative) sNonnegative
      have bounded : scalar ^ 2 ≤
          scalar ^ 2 + (t ^ 2 + r ^ 2 + s ^ 2) :=
        le_add_of_nonneg_right remainingNonnegative
      rwa [← add_assoc, ← add_assoc, sumZero] at bounded
    have tUpper : t ^ 2 ≤ 0 := by
      have remainingNonnegative : 0 ≤ scalar ^ 2 + r ^ 2 + s ^ 2 :=
        add_nonneg (add_nonneg scalarNonnegative rNonnegative) sNonnegative
      have bounded : t ^ 2 ≤
          t ^ 2 + (scalar ^ 2 + r ^ 2 + s ^ 2) :=
        le_add_of_nonneg_right remainingNonnegative
      calc
        t ^ 2 ≤ t ^ 2 + (scalar ^ 2 + r ^ 2 + s ^ 2) := bounded
        _ = scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 := by ring1
        _ = 0 := sumZero
    have rUpper : r ^ 2 ≤ 0 := by
      have remainingNonnegative : 0 ≤ scalar ^ 2 + t ^ 2 + s ^ 2 :=
        add_nonneg (add_nonneg scalarNonnegative tNonnegative) sNonnegative
      have bounded : r ^ 2 ≤
          r ^ 2 + (scalar ^ 2 + t ^ 2 + s ^ 2) :=
        le_add_of_nonneg_right remainingNonnegative
      calc
        r ^ 2 ≤ r ^ 2 + (scalar ^ 2 + t ^ 2 + s ^ 2) := bounded
        _ = scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 := by ring1
        _ = 0 := sumZero
    have sUpper : s ^ 2 ≤ 0 := by
      have remainingNonnegative : 0 ≤ scalar ^ 2 + t ^ 2 + r ^ 2 :=
        add_nonneg (add_nonneg scalarNonnegative tNonnegative) rNonnegative
      have bounded : s ^ 2 ≤
          s ^ 2 + (scalar ^ 2 + t ^ 2 + r ^ 2) :=
        le_add_of_nonneg_right remainingNonnegative
      calc
        s ^ 2 ≤ s ^ 2 + (scalar ^ 2 + t ^ 2 + r ^ 2) := bounded
        _ = scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 := by ring1
        _ = 0 := sumZero
    exact
      ⟨(RFAP.ConstructiveFraction.sq_eq_zero_direct scalar).mp
          (le_antisymm scalarUpper scalarNonnegative),
        (RFAP.ConstructiveFraction.sq_eq_zero_direct t).mp
          (le_antisymm tUpper tNonnegative),
        (RFAP.ConstructiveFraction.sq_eq_zero_direct r).mp
          (le_antisymm rUpper rNonnegative),
        (RFAP.ConstructiveFraction.sq_eq_zero_direct s).mp
          (le_antisymm sUpper sNonnegative)⟩

theorem rational_proportion_norm_ne_zero (proportion :
    Proportion RFAP.ConstructiveFraction.Rational)
    (nonzero : proportion.IsNonzero) : proportion.norm ≠ 0 :=
  proportion_norm_ne_zero_of_isNonzero rationalSumFourSquaresSeparate
    proportion nonzero

/-- A representative on which Definition 55's rational rotation formula is
executable.  The cached norm is its denominator certificate. -/
@[ext]
structure NonNullProportion (K : Type*) [RFAP.ExplicitField K]
    extends Proportion K where
  normNonzero : toProportion.norm ≠ 0

namespace NonNullProportion

/-- Every non-null representative is automatically a nonzero quadruple. -/
theorem isNonzero (proportion : NonNullProportion K) :
    proportion.toProportion.IsNonzero := by
  intro equalZero
  apply proportion.normNonzero
  rw [equalZero]
  exact Proportion.norm_zero

/-- The existence of a non-null representative rules out the trivial ring. -/
theorem one_ne_zero (proportion : NonNullProportion K) : (1 : K) ≠ 0 := by
  intro oneZero
  apply proportion.normNonzero
  calc
    proportion.toProportion.norm =
        proportion.toProportion.norm * 1 := by rw [mul_one]
    _ = proportion.toProportion.norm * 0 := by rw [oneZero]
    _ = 0 := by rw [mul_zero]

/-- Explicit homogeneous rescaling with its cached non-null certificate. -/
def scale (factor : K) (factorNonzero : factor ≠ 0)
    (proportion : NonNullProportion K) : NonNullProportion K where
  toProportion := Proportion.scale factor proportion.toProportion
  normNonzero := by
    rw [Proportion.norm_scale]
    exact RFAP.ExplicitField.mul_ne_zero
      (by
        simpa only [pow_two] using
          RFAP.ExplicitField.mul_ne_zero factorNonzero factorNonzero)
      proportion.normNonzero

/-- Equality of projective points by an explicit nonzero scale witness. -/
def Equivalent (left right : NonNullProportion K) : Prop :=
  left.toProportion.Equivalent right.toProportion

theorem equivalent_refl (proportion : NonNullProportion K) :
    proportion.Equivalent proportion := by
  exact ⟨1, proportion.one_ne_zero, (Proportion.one_scale _).symm⟩

theorem equivalent_symm {left right : NonNullProportion K}
    (equivalent : left.Equivalent right) : right.Equivalent left := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  have reverseCancel : factor⁻¹ * factor = 1 := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := cancel
  refine ⟨factor⁻¹, RFAP.ExplicitField.inv_ne_zero factorNonzero, ?_⟩
  calc
    left.toProportion = Proportion.scale 1 left.toProportion := by
      rw [Proportion.one_scale]
    _ = Proportion.scale (factor⁻¹ * factor) left.toProportion := by
      rw [reverseCancel]
    _ = Proportion.scale factor⁻¹
        (Proportion.scale factor left.toProportion) := by
      rw [Proportion.scale_scale]
    _ = Proportion.scale factor⁻¹ right.toProportion := by
      rw [← rightValue]

theorem equivalent_trans {first second third : NonNullProportion K}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) : first.Equivalent third := by
  rcases firstSecond with ⟨firstFactor, firstFactorNonzero, secondValue⟩
  rcases secondThird with ⟨secondFactor, secondFactorNonzero, thirdValue⟩
  refine ⟨secondFactor * firstFactor,
    RFAP.ExplicitField.mul_ne_zero secondFactorNonzero firstFactorNonzero, ?_⟩
  calc
    third.toProportion =
        Proportion.scale secondFactor second.toProportion := thirdValue
    _ = Proportion.scale secondFactor
        (Proportion.scale firstFactor first.toProportion) := by rw [secondValue]
    _ = Proportion.scale (secondFactor * firstFactor)
        first.toProportion := Proportion.scale_scale _ _ _

theorem equivalent_scale (factor : K) (factorNonzero : factor ≠ 0)
    (proportion : NonNullProportion K) :
    proportion.Equivalent (scale factor factorNonzero proportion) := by
  exact ⟨factor, factorNonzero, rfl⟩

/-- Theorem 57: the product of non-null proportions is total, with the
resulting norm certificate computed from the two input certificates. -/
def mul (left right : NonNullProportion K) : NonNullProportion K where
  toProportion := Proportion.mul left.toProportion right.toProportion
  normNonzero := by
    rw [Proportion.norm_mul]
    exact RFAP.ExplicitField.mul_ne_zero left.normNonzero right.normNonzero

theorem mul_norm (left right : NonNullProportion K) :
    (mul left right).toProportion.norm =
      left.toProportion.norm * right.toProportion.norm :=
  Proportion.norm_mul _ _

theorem mul_assoc (first second third : NonNullProportion K) :
    mul (mul first second) third = mul first (mul second third) := by
  have raw := Proportion.mul_assoc
    first.toProportion second.toProportion third.toProportion
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar raw
  · exact congrArg Proportion.vector raw

/-- The total product respects projective equivalence in both inputs. -/
theorem mul_respects_equivalent
    {left left' right right' : NonNullProportion K}
    (leftEquivalent : left.Equivalent left')
    (rightEquivalent : right.Equivalent right') :
    (mul left right).Equivalent (mul left' right') := by
  rcases leftEquivalent with ⟨leftFactor, leftFactorNonzero, leftValue⟩
  rcases rightEquivalent with ⟨rightFactor, rightFactorNonzero, rightValue⟩
  refine ⟨leftFactor * rightFactor,
    RFAP.ExplicitField.mul_ne_zero leftFactorNonzero rightFactorNonzero, ?_⟩
  change Proportion.mul left'.toProportion right'.toProportion =
    Proportion.scale (leftFactor * rightFactor)
      (Proportion.mul left.toProportion right.toProportion)
  rw [leftValue, rightValue, Proportion.mul_scale_both]

/-- The non-null identity representative, constructed from any inhabitant of
the non-null projective domain. -/
def identity (witness : NonNullProportion K) : NonNullProportion K where
  toProportion := Proportion.identity
  normNonzero := by
    unfold Proportion.norm Proportion.identity
    rw [Vector.quadrance_zero]
    simpa only [one_pow, add_zero] using witness.one_ne_zero

@[simp] theorem identity_mul (witness proportion : NonNullProportion K) :
    mul (identity witness) proportion = proportion := by
  have raw := Proportion.identity_mul proportion.toProportion
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar raw
  · exact congrArg Proportion.vector raw

@[simp] theorem mul_identity (proportion witness : NonNullProportion K) :
    mul proportion (identity witness) = proportion := by
  have raw := Proportion.mul_identity proportion.toProportion
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar raw
  · exact congrArg Proportion.vector raw

/-- Conjugation preserves the non-null certificate. -/
def conjugate (proportion : NonNullProportion K) : NonNullProportion K where
  toProportion := Proportion.conjugate proportion.toProportion
  normNonzero := by
    rw [Proportion.norm_conjugate]
    exact proportion.normNonzero

@[simp] theorem conjugate_conjugate (proportion : NonNullProportion K) :
    conjugate (conjugate proportion) = proportion := by
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar
      (Proportion.conjugate_conjugate proportion.toProportion)
  · exact congrArg Proportion.vector
      (Proportion.conjugate_conjugate proportion.toProportion)

/-- Non-null quaternion conjugation reverses multiplication exactly. -/
theorem conjugate_mul_reverse (left right : NonNullProportion K) :
    conjugate (mul left right) = mul (conjugate right) (conjugate left) := by
  have raw := Proportion.conjugate_mul_reverse left.toProportion
    right.toProportion
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar raw
  · exact congrArg Proportion.vector raw

/-- A representative times its conjugate is projectively the identity. -/
theorem mul_conjugate_equivalent_identity (proportion : NonNullProportion K) :
    (mul proportion (conjugate proportion)).Equivalent
      (identity proportion) := by
  apply equivalent_symm
  refine ⟨proportion.toProportion.norm, proportion.normNonzero, ?_⟩
  exact Proportion.mul_conjugate proportion.toProportion

theorem conjugate_mul_equivalent_identity (proportion : NonNullProportion K) :
    (mul (conjugate proportion) proportion).Equivalent
      (identity proportion) := by
  apply equivalent_symm
  refine ⟨proportion.toProportion.norm, proportion.normNonzero, ?_⟩
  exact Proportion.conjugate_mul proportion.toProportion

end NonNullProportion

end RationalRotations
