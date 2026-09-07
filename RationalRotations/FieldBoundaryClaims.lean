import RationalRotations.Handedness
import RationalRotations.NullVectors
import RationalRotations.RationalSurjectivity

/-!
# Field-specific claims between the numbered results

The paper makes several mathematical assertions in the prose surrounding
Theorems 24 and 29.  This module records them explicitly.  Ordered and
rational claims are proved directly from finite coordinates.  The assertion
that every half-spread value occurs over a finite field is computed from an
explicit finite carrier and cached square table, with no choice-derived
enumeration or witness.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- A null anchor has the unipotent quadratic cap formula stated before
Example 27. -/
theorem cap_of_null (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (null : vector.quadrance = 0) :
    cap vector defined =
      Matrix3.add Matrix3.identity
        (Matrix3.scale 2
          (Matrix3.add (anchor vector)
            (Matrix3.mul (anchor vector) (anchor vector)))) := by
  have denominatorOne : capDenominator vector = 1 := by
    unfold capDenominator
    rw [null]
    ring1
  have oneNonzero : (1 : K) ≠ 0 := by
    rw [← denominatorOne]
    exact defined
  have inverseOne : (1 : K)⁻¹ = 1 := by
    have cancel := RFAP.ExplicitField.mul_inv_cancel (1 : K) oneNonzero
    simpa only [one_mul] using cancel
  rw [cap_quadratic vector defined, denominatorOne,
    RFAP.ExplicitField.div_eq_mul_inv, inverseOne, mul_one]

/-- The characteristic polynomial of every null cap is `(X-1)³`, not only
for the displayed `F₅` example. -/
theorem characteristicValue_cap_of_null (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (null : vector.quadrance = 0) (X : K) :
    Matrix3.characteristicValue (cap vector defined) X = (X - 1) ^ 3 := by
  have denominatorOne : capDenominator vector = 1 := by
    unfold capDenominator
    rw [null]
    ring1
  have oneNonzero : (1 : K) ≠ 0 := by
    rw [← denominatorOne]
    exact defined
  have inverseOne : (1 : K)⁻¹ = 1 := by
    have cancel := RFAP.ExplicitField.mul_inv_cancel (1 : K) oneNonzero
    simpa only [one_mul] using cancel
  rw [characteristicValue_cap vector defined X, null, denominatorOne,
    RFAP.ExplicitField.div_eq_mul_inv, inverseOne]
  ring1

theorem cap_zero_eq_identity
    (defined : capDenominator (Vector.zero : Vector K) ≠ 0) :
    cap Vector.zero defined = Matrix3.identity := by
  rw [cap_of_null Vector.zero defined Vector.quadrance_zero]
  ext <;>
    unfold Matrix3.add Matrix3.scale Matrix3.mul Matrix3.identity anchor
      Vector.zero <;>
    ring1

/-! ## Rational cap claims -/

namespace RationalFieldClaims

abbrev Scalar := RFAP.ConstructiveFraction.Rational

/-- Rational vector quadrance is a visibly nonnegative sum of three stored
squares. -/
theorem vector_quadrance_nonnegative (vector : Vector Scalar) :
    0 ≤ vector.quadrance := by
  have tNonnegative : 0 ≤ vector.t * vector.t := by
    simpa only [pow_two] using
      RFAP.ConstructiveFraction.sq_nonneg_direct vector.t
  have rNonnegative : 0 ≤ vector.r * vector.r := by
    simpa only [pow_two] using
      RFAP.ConstructiveFraction.sq_nonneg_direct vector.r
  have sNonnegative : 0 ≤ vector.s * vector.s := by
    simpa only [pow_two] using
      RFAP.ConstructiveFraction.sq_nonneg_direct vector.s
  unfold Vector.quadrance Vector.dot
  exact add_nonneg (add_nonneg tNonnegative rNonnegative) sNonnegative

/-- The unnumbered assertion after Lemma 22: every rational anchor lies in
the domain of the cap. -/
theorem capDenominator_positive (vector : Vector Scalar) :
    0 < capDenominator vector := by
  have onePositive : (0 : Scalar) < 1 :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 1) (by decide)
  have oneAtMost : (1 : Scalar) ≤ 1 + vector.quadrance :=
    le_add_of_nonneg_right (vector_quadrance_nonnegative vector)
  unfold capDenominator
  exact lt_of_lt_of_le onePositive oneAtMost

theorem capDenominator_ne_zero (vector : Vector Scalar) :
    capDenominator vector ≠ 0 :=
  (capDenominator_positive vector).ne'

/-- Over the rationals a null anchor is zero, so the corresponding cap is the
identity; the nonidentity parabolic phenomenon of Example 27 cannot occur. -/
theorem null_cap_eq_identity (vector : Vector Scalar)
    (null : vector.quadrance = 0) :
    cap vector (capDenominator_ne_zero vector) = Matrix3.identity := by
  have vectorZero : vector = Vector.zero :=
    rational_only_zero_null_vector vector null
  rw [vectorZero]
  exact cap_zero_eq_identity _

end RationalFieldClaims

/-! ## Ordered half-spread interval -/

namespace OrderedFieldClaims

variable {F : Type*} [OrderedExplicitField F]

local instance : DecidableEq F := OrderedExplicitField.eq_decidable

private theorem vectorQuadrancePositive (vector : Vector F)
    (nonzero : vector ≠ Vector.zero) : 0 < vector.quadrance := by
  by_cases tZero : vector.t = 0
  · by_cases rZero : vector.r = 0
    · by_cases sZero : vector.s = 0
      · exact False.elim (nonzero (Vector.ext tZero rZero sZero))
      · unfold Vector.quadrance Vector.dot
        rw [tZero, rZero]
        simpa only [zero_mul, zero_add] using
          OrderedExplicitField.mul_self_pos_direct sZero
    · have rPositive := OrderedExplicitField.mul_self_pos_direct rZero
      by_cases sZero : vector.s = 0
      · unfold Vector.quadrance Vector.dot
        rw [tZero, sZero]
        simpa only [zero_mul, zero_add, add_zero] using rPositive
      · unfold Vector.quadrance Vector.dot
        rw [tZero, zero_mul, zero_add]
        exact OrderedExplicitField.add_pos_direct rPositive
          (OrderedExplicitField.mul_self_pos_direct sZero)
  · have tPositive := OrderedExplicitField.mul_self_pos_direct tZero
    by_cases rZero : vector.r = 0
    · by_cases sZero : vector.s = 0
      · unfold Vector.quadrance Vector.dot
        rw [rZero, sZero]
        simpa only [zero_mul, add_zero] using tPositive
      · unfold Vector.quadrance Vector.dot
        rw [rZero, zero_mul, add_zero]
        exact OrderedExplicitField.add_pos_direct tPositive
          (OrderedExplicitField.mul_self_pos_direct sZero)
    · have firstTwoPositive := OrderedExplicitField.add_pos_direct tPositive
        (OrderedExplicitField.mul_self_pos_direct rZero)
      by_cases sZero : vector.s = 0
      · unfold Vector.quadrance Vector.dot
        rw [sZero]
        simpa only [zero_mul, add_zero] using firstTwoPositive
      · unfold Vector.quadrance Vector.dot
        exact OrderedExplicitField.add_pos_direct firstTwoPositive
          (OrderedExplicitField.mul_self_pos_direct sZero)

theorem capDenominatorPositive (vector : Vector F) :
    0 < capDenominator vector := by
  by_cases vectorZero : vector = Vector.zero
  · rw [vectorZero]
    unfold capDenominator
    rw [Vector.quadrance_zero, add_zero]
    exact OrderedExplicitField.zero_lt_one_direct
  · unfold capDenominator
    exact OrderedExplicitField.add_pos_direct
      OrderedExplicitField.zero_lt_one_direct
      (vectorQuadrancePositive vector vectorZero)

/-- The lower half of the source's interval assertion: an ordered-field cap
has zero or strictly positive half spread. -/
theorem halfSpread_cap_eq_zero_or_positive (vector : Vector F)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : F) ≠ 0) :
    halfSpread (capRotation vector defined) = 0 ∨
      0 < halfSpread (capRotation vector defined) := by
  by_cases vectorZero : vector = Vector.zero
  · left
    rw [halfSpread_cap vector defined twoNonzero, vectorZero,
      Vector.quadrance_zero, RFAP.ExplicitField.zero_div]
  · right
    rw [halfSpread_cap vector defined twoNonzero,
      RFAP.ExplicitField.div_eq_mul_inv]
    exact OrderedExplicitField.mul_pos_direct
      (vectorQuadrancePositive vector vectorZero)
      (OrderedExplicitField.inv_pos_direct
        (capDenominatorPositive vector))

/-- The upper half of the interval assertion, expressed without adding a
second generic order hierarchy: the complement `1-p` is strictly positive. -/
theorem one_sub_halfSpread_cap_positive (vector : Vector F)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : F) ≠ 0) :
    0 < 1 - halfSpread (capRotation vector defined) := by
  rw [one_sub_halfSpread_cap vector defined twoNonzero,
    RFAP.ExplicitField.div_eq_mul_inv]
  exact OrderedExplicitField.mul_pos_direct
    OrderedExplicitField.zero_lt_one_direct
    (OrderedExplicitField.inv_pos_direct (capDenominatorPositive vector))

end OrderedFieldClaims

/-! ## Finite-field half-spread boundary -/

/-- Checked output representing one scalar by three displayed squares. -/
structure ThreeSquareRepresentation (value : K) where
  t : K
  r : K
  s : K
  equation : t ^ 2 + r ^ 2 + s ^ 2 = value

namespace ThreeSquareRepresentation

def vector (representation : ThreeSquareRepresentation (K := K) value) :
    Vector K :=
  ⟨representation.t, representation.r, representation.s⟩

theorem vector_quadrance
    (representation : ThreeSquareRepresentation (K := K) value) :
    representation.vector.quadrance = value := by
  unfold vector Vector.quadrance Vector.dot
  calc
    representation.t * representation.t +
          representation.r * representation.r +
          representation.s * representation.s =
        representation.t ^ 2 + representation.r ^ 2 +
          representation.s ^ 2 := by ring1
    _ = value := representation.equation

end ThreeSquareRepresentation

/-- Exact executable obligation behind the prose claim that every finite-field
element is a sum of three squares. -/
structure ThreeSquareAlgorithm (K : Type*) [RFAP.ExplicitField K] where
  represent : (value : K) → ThreeSquareRepresentation value

/-- The finite square-table argument proves the stronger assertion that every
element is a sum of two squares; adjoining a displayed zero supplies the
paper's three-square algorithm. -/
def FiniteOddFieldPresentation.threeSquareAlgorithm
    (presentation : FiniteOddFieldPresentation K) : ThreeSquareAlgorithm K where
  represent := fun value => by
    let pair := presentation.twoSquareRepresentation value
    refine
      { t := pair.first
        r := pair.second
        s := 0
        equation := ?_ }
    calc
      pair.first ^ 2 + pair.second ^ 2 + (0 : K) ^ 2 =
          pair.first ^ 2 + pair.second ^ 2 := by ring1
      _ = value := pair.equation

private theorem one_sub_ne_zero_of_ne_one {value : K}
    (notOne : value ≠ 1) : 1 - value ≠ 0 := by
  intro differenceZero
  apply notOne
  calc
    value = 1 - (1 - value) := by ring1
    _ = 1 := by rw [differenceZero]; ring1

/-- For `p ≠ 1`, three squares representing `p(1-p)` give the proportion
`(1-p:t:r:s)`, whose norm is exactly `1-p`. -/
def affineHalfSpreadPreimage (algorithm : ThreeSquareAlgorithm K)
    (value : K) (notOne : value ≠ 1) : NonNullProportion K := by
  let output := algorithm.represent (value * (1 - value))
  refine
    { scalar := 1 - value
      vector := output.vector
      normNonzero := ?_ }
  have quadrance := output.vector_quadrance
  change (1 - value) ^ 2 + output.vector.quadrance ≠ 0
  rw [quadrance]
  have normValue :
      (1 - value) ^ 2 + value * (1 - value) = 1 - value := by ring1
  rw [normValue]
  exact one_sub_ne_zero_of_ne_one notOne

theorem affineHalfSpreadPreimage_norm (algorithm : ThreeSquareAlgorithm K)
    (value : K) (notOne : value ≠ 1) :
    (affineHalfSpreadPreimage algorithm value notOne).toProportion.norm =
      1 - value := by
  let output := algorithm.represent (value * (1 - value))
  change (1 - value) ^ 2 + output.vector.quadrance = 1 - value
  rw [output.vector_quadrance]
  ring1

theorem affineHalfSpreadPreimage_value (algorithm : ThreeSquareAlgorithm K)
    (value : K) (notOne : value ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    halfSpread (affineHalfSpreadPreimage algorithm value notOne).rotation =
      value := by
  rw [NonNullProportion.halfSpread_rotation _ twoNonzero]
  let output := algorithm.represent (value * (1 - value))
  change output.vector.quadrance /
      (affineHalfSpreadPreimage algorithm value notOne).toProportion.norm =
    value
  rw [output.vector_quadrance,
    affineHalfSpreadPreimage_norm algorithm value notOne]
  rw [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    value * (1 - value) * (1 - value)⁻¹ =
        value * ((1 - value) * (1 - value)⁻¹) := by ring1
    _ = value := by
      rw [RFAP.ExplicitField.mul_inv_cancel
        (1 - value) (one_sub_ne_zero_of_ne_one notOne), mul_one]

private theorem one_ne_zero_of_two_ne_zero (twoNonzero : (2 : K) ≠ 0) :
    (1 : K) ≠ 0 := by
  intro oneZero
  apply twoNonzero
  calc
    (2 : K) = 1 + 1 := by ring1
    _ = 0 := by rw [oneZero, zero_add]

/-- A fixed proportion at infinity supplies half spread one. -/
def halfTurnHalfSpreadPreimage (twoNonzero : (2 : K) ≠ 0) :
    NonNullProportion K where
  scalar := 0
  vector := ⟨1, 0, 0⟩
  normNonzero := by
    intro normZero
    apply one_ne_zero_of_two_ne_zero twoNonzero
    calc
      (1 : K) = Proportion.norm
          (⟨0, (⟨1, 0, 0⟩ : Vector K)⟩ : Proportion K) := by
        unfold Proportion.norm Vector.quadrance Vector.dot
        ring1
      _ = 0 := normZero

theorem halfTurnHalfSpreadPreimage_value [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread (halfTurnHalfSpreadPreimage twoNonzero).rotation = 1 :=
  (NonNullProportion.halfSpread_rotation_eq_one_iff
    (halfTurnHalfSpreadPreimage twoNonzero) twoNonzero).2 rfl

/-- A three-square algorithm computes a rotation for every requested
half-spread value. -/
theorem halfSpread_surjective_of_threeSquareAlgorithm [DecidableEq K]
    (algorithm : ThreeSquareAlgorithm K) (twoNonzero : (2 : K) ≠ 0)
    (value : K) :
    ∃ proportion : NonNullProportion K,
      halfSpread proportion.rotation = value := by
  by_cases valueOne : value = 1
  · subst value
    exact ⟨halfTurnHalfSpreadPreimage twoNonzero,
      halfTurnHalfSpreadPreimage_value twoNonzero⟩
  · exact ⟨affineHalfSpreadPreimage algorithm value valueOne,
      affineHalfSpreadPreimage_value algorithm value valueOne twoNonzero⟩

/-- The unnumbered finite-field assertion after Theorem 29: an explicit
finite odd-field square presentation computes a rotation with every requested
half-spread value. -/
theorem FiniteOddFieldPresentation.halfSpread_surjective
    (presentation : FiniteOddFieldPresentation K) (value : K) :
    ∃ proportion : NonNullProportion K,
      halfSpread proportion.rotation = value := by
  letI : DecidableEq K := presentation.eqDecidable
  exact halfSpread_surjective_of_threeSquareAlgorithm
    presentation.threeSquareAlgorithm presentation.twoNonzero value

end RationalRotations
