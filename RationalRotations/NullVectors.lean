import RationalRotations.VectorAlgebra
import mathlib.Data.ConstructiveList
import mathlib.RFAP.ConstructiveFraction
import DivineProportions.Algebra.FieldFive

/-!
# Rational rotations, Theorem 2: null vectors

The paper treats ordered fields and finite fields separately.  The ordered
rational case below is proved from the stored finite numerator order on the
repository's canonical rational carrier.  The finite-field construction is
implemented by a recursive intersection search over explicit carrier and
square tables, so the resulting null vector is executable data rather than a
bare existence claim.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- An explicit certificate that three squares can sum to zero only
trivially.  Ordered computational fields can provide this finite interface
without importing a general infinite ordered-field hierarchy. -/
structure SumSquaresSeparate (K : Type*) [RFAP.ExplicitField K] where
  separate : ∀ first second third : K,
    first ^ 2 + second ^ 2 + third ^ 2 = 0 →
      first = 0 ∧ second = 0 ∧ third = 0

/-- The ordered-field half of Theorem 2, factored through its exact algebraic
content: a field whose sums of three squares separate coordinates has only
the zero null vector. -/
theorem only_zero_null_vector (certificate : SumSquaresSeparate K)
    (vector : Vector K) (null : vector.IsNull) : vector = Vector.zero := by
  have coordinates := certificate.separate vector.t vector.r vector.s (by
    unfold Vector.IsNull Vector.quadrance Vector.dot at null
    simpa only [pow_two] using null)
  exact Vector.ext coordinates.1 coordinates.2.1 coordinates.2.2

/-- The quotient-free canonical rationals carry an explicit proof that a
sum of three squares vanishes only coordinatewise. -/
theorem rationalSumSquaresSeparate :
    SumSquaresSeparate RFAP.ConstructiveFraction.Rational where
  separate := by
    intro first second third sumZero
    have firstNonnegative :=
      RFAP.ConstructiveFraction.sq_nonneg_direct first
    have secondNonnegative :=
      RFAP.ConstructiveFraction.sq_nonneg_direct second
    have thirdNonnegative :=
      RFAP.ConstructiveFraction.sq_nonneg_direct third
    have secondThirdNonnegative : 0 ≤ second ^ 2 + third ^ 2 :=
      add_nonneg secondNonnegative thirdNonnegative
    have firstUpper : first ^ 2 ≤ 0 := by
      have bounded : first ^ 2 ≤ first ^ 2 + (second ^ 2 + third ^ 2) :=
        le_add_of_nonneg_right secondThirdNonnegative
      rwa [← add_assoc, sumZero] at bounded
    have firstSquareZero : first ^ 2 = 0 :=
      le_antisymm firstUpper firstNonnegative
    have secondUpper : second ^ 2 ≤ 0 := by
      have bounded : second ^ 2 ≤
          first ^ 2 + second ^ 2 + third ^ 2 := by
        calc
          second ^ 2 ≤ first ^ 2 + second ^ 2 :=
            le_add_of_nonneg_left firstNonnegative
          _ ≤ first ^ 2 + second ^ 2 + third ^ 2 :=
            le_add_of_nonneg_right thirdNonnegative
      rwa [sumZero] at bounded
    have secondSquareZero : second ^ 2 = 0 :=
      le_antisymm secondUpper secondNonnegative
    have thirdUpper : third ^ 2 ≤ 0 := by
      have firstSecondNonnegative : 0 ≤ first ^ 2 + second ^ 2 :=
        add_nonneg firstNonnegative secondNonnegative
      have bounded : third ^ 2 ≤
          first ^ 2 + second ^ 2 + third ^ 2 :=
        le_add_of_nonneg_left firstSecondNonnegative
      rwa [sumZero] at bounded
    have thirdSquareZero : third ^ 2 = 0 :=
      le_antisymm thirdUpper thirdNonnegative
    exact
      ⟨(RFAP.ConstructiveFraction.sq_eq_zero_direct first).mp
          firstSquareZero,
        (RFAP.ConstructiveFraction.sq_eq_zero_direct second).mp
          secondSquareZero,
        (RFAP.ConstructiveFraction.sq_eq_zero_direct third).mp
          thirdSquareZero⟩

/-- In particular, the only null vector over the repository's executable
rational field is zero. -/
theorem rational_only_zero_null_vector
    (vector : Vector RFAP.ConstructiveFraction.Rational)
    (null : vector.IsNull) : vector = Vector.zero :=
  only_zero_null_vector rationalSumSquaresSeparate vector null

/-- The explicit collision between the two square tables used by the finite
field proof of Theorem 2. -/
structure SquareCollision (K : Type*) [RFAP.ExplicitField K] where
  first : K
  second : K
  collision : first ^ 2 = -(1 + second ^ 2)

/-- The paper's finite-field construction turns a square collision into the
displayed nonzero null vector `(t,r,1)`. -/
def SquareCollision.nullVector (collision : SquareCollision K) : Vector K :=
  ⟨collision.first, collision.second, 1⟩

/-- The vector computed from a square collision is null. -/
theorem SquareCollision.nullVector_isNull (collision : SquareCollision K) :
    collision.nullVector.IsNull := by
  unfold SquareCollision.nullVector Vector.IsNull Vector.quadrance Vector.dot
  change collision.first * collision.first +
      collision.second * collision.second + 1 * 1 = 0
  calc
    collision.first * collision.first +
          collision.second * collision.second + 1 * 1 =
        collision.first ^ 2 + collision.second ^ 2 + 1 := by ring1
    _ = 0 := by rw [collision.collision]; ring1

/-- When one is nonzero, the vector computed from a square collision is
nonzero because its last coordinate is one. -/
theorem SquareCollision.nullVector_ne_zero (collision : SquareCollision K)
    (oneNonzero : (1 : K) ≠ 0) :
    collision.nullVector ≠ Vector.zero := by
  intro equal
  have lastCoordinate := congrArg Vector.s equal
  exact oneNonzero lastCoordinate

/-- A nonzero null vector stored together with the two finite certificates
needed by every downstream use. -/
structure NonzeroNullVector (K : Type*) [RFAP.ExplicitField K] where
  vector : Vector K
  null : vector.IsNull
  nonzero : vector ≠ Vector.zero

/-- Package the paper's collision construction as executable output. -/
def SquareCollision.nonzeroNullVector (collision : SquareCollision K)
    (oneNonzero : (1 : K) ≠ 0) : NonzeroNullVector K where
  vector := collision.nullVector
  null := collision.nullVector_isNull
  nonzero := collision.nullVector_ne_zero oneNonzero

/-- Checked output representing one scalar by two displayed squares. -/
structure TwoSquareRepresentation (value : K) where
  first : K
  second : K
  equation : first ^ 2 + second ^ 2 = value

/-- Executable finite-field data used by the paper's square-counting
argument.  The presentation caches the duplicate-free carrier and square
tables, a root lookup for the cached square values, and the exact finite count
certificate tying the two tables together.  No carrier or witness is obtained
from a finiteness proposition. -/
structure FiniteOddFieldPresentation
    (K : Type*) [RFAP.ExplicitField K] where
  eqDecidable : DecidableEq K
  carrier : List K
  carrierNodup : carrier.Nodup
  carrierComplete : ∀ value : K, value ∈ carrier
  squareValues : List K
  squareValuesNodup : squareValues.Nodup
  squareValuesComplete : ∀ root : K, root ^ 2 ∈ squareValues
  squareRoot : K → K
  squareRoot_spec : ∀ value ∈ squareValues, squareRoot value ^ 2 = value
  squareCount : squareValues.length + squareValues.length = carrier.length + 1
  twoNonzero : (2 : K) ≠ 0

namespace FiniteOddFieldPresentation

variable (presentation : FiniteOddFieldPresentation K)

/-- Constructive square status: either a cached root or a function rejecting
every proposed root. -/
inductive SquareClassification (value : K) where
  | square (root : K) (equation : root ^ 2 = value)
  | nonsquare (noRoot : ∀ root : K, root ^ 2 ≠ value)

/-- A scalar is a square when a displayed root is supplied. -/
def HasSquareRoot (value : K) : Prop :=
  ∃ root : K, root ^ 2 = value

theorem mem_squareValues_iff_hasSquareRoot (value : K) :
    value ∈ presentation.squareValues ↔ HasSquareRoot value := by
  constructor
  · intro member
    exact ⟨presentation.squareRoot value,
      presentation.squareRoot_spec value member⟩
  · rintro ⟨root, equation⟩
    exact equation ▸ presentation.squareValuesComplete root

/-- Decide square status by the cached finite square table.  The negative
branch remains executable evidence: every proposed root is rejected using
the table's completeness certificate. -/
def classifySquare (value : K) : SquareClassification value := by
  letI : DecidableEq K := presentation.eqDecidable
  if member : value ∈ presentation.squareValues then
    exact SquareClassification.square (presentation.squareRoot value)
      (presentation.squareRoot_spec value member)
  else
    exact SquareClassification.nonsquare fun root equation =>
      member (equation ▸ presentation.squareValuesComplete root)

/-- The exact square/nonsquare split that controls the formulas customarily
expressed as `q mod 4`. -/
def classifyMinusOne : SquareClassification (-1 : K) :=
  presentation.classifySquare (-1)

/-- Translate the cached square table by `value ↦ target - value`. -/
def translatedSquareValues (target : K) : List K :=
  presentation.squareValues.map (fun value => target - value)

private theorem translateInjective (target : K) :
    Function.Injective (fun value : K => target - value) := by
  intro left right equal
  change target - left = target - right at equal
  calc
    left = target - (target - left) := by ring1
    _ = target - (target - right) :=
      congrArg (fun value => target - value) equal
    _ = right := by ring1

theorem translatedSquareValues_nodup (target : K) :
    (presentation.translatedSquareValues target).Nodup := by
  unfold translatedSquareValues
  exact QuotientFreeList.nodup_map_of_injective
    (translateInjective target) presentation.squareValuesNodup

private theorem translatedSquareValues_contained (target value : K)
    (_member : value ∈ presentation.translatedSquareValues target) :
    value ∈ presentation.carrier :=
  presentation.carrierComplete value

private theorem squareValues_contained (value : K)
    (_member : value ∈ presentation.squareValues) :
    value ∈ presentation.carrier :=
  presentation.carrierComplete value

/-- The concrete finite search whose success drives the two-square
construction. -/
def squareTableIntersection? (target : K) : Option K :=
  @QuotientFreeList.firstIntersection? K presentation.eqDecidable
    presentation.squareValues (presentation.translatedSquareValues target)

private theorem squareTableIntersection_nonempty (target : K) :
    presentation.squareTableIntersection? target ≠ none := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold squareTableIntersection?
  apply QuotientFreeList.firstIntersection?_ne_none_of_length_gt
    presentation.squareValuesNodup
    (presentation.translatedSquareValues_nodup target)
    presentation.squareValues_contained
    (presentation.translatedSquareValues_contained target)
    presentation.carrierNodup
  unfold translatedSquareValues
  rw [List.length_map, presentation.squareCount]
  exact Nat.lt_succ_self presentation.carrier.length

/-- Every requested scalar is computed as a sum of two squares.  The selected
intersection is obtained by recursive search over the two cached finite
tables, and the stored root lookup turns the selected square values into the
displayed witnesses. -/
def twoSquareRepresentation (target : K) : TwoSquareRepresentation target := by
  letI : DecidableEq K := presentation.eqDecidable
  let translated := presentation.translatedSquareValues target
  have foundNonempty :
      presentation.squareTableIntersection? target ≠ none :=
    presentation.squareTableIntersection_nonempty target
  cases found : presentation.squareTableIntersection? target with
  | none => exact False.elim (foundNonempty found)
  | some common =>
      have commonMembers :=
        QuotientFreeList.firstIntersection?_eq_some
          (left := presentation.squareValues) (right := translated) (by
            unfold squareTableIntersection? at found
            exact found)
      have complementMember :
          target - common ∈ presentation.squareValues := by
        rcases QuotientFreeList.mem_map.mp commonMembers.2 with
          ⟨source, sourceMember, translatedEqual⟩
        have sourceEqual : source = target - common := by
          calc
            source = target - (target - source) := by ring1
            _ = target - common := by rw [translatedEqual]
        exact sourceEqual ▸ sourceMember
      refine
        { first := presentation.squareRoot common
          second := presentation.squareRoot (target - common)
          equation := ?_ }
      rw [presentation.squareRoot_spec common commonMembers.1,
        presentation.squareRoot_spec (target - common) complementMember]
      ring1

/-- The paper's Theorem 2 collision is the target `-1` specialization of the
stronger two-square computation. -/
def squareCollision : SquareCollision K := by
  let representation := presentation.twoSquareRepresentation (-1)
  refine
    { first := representation.first
      second := representation.second
      collision := ?_ }
  have equation := representation.equation
  calc
    representation.first ^ 2 =
        (representation.first ^ 2 + representation.second ^ 2) -
          representation.second ^ 2 := by ring1
    _ = -1 - representation.second ^ 2 :=
      congrArg (fun value => value - representation.second ^ 2) equation
    _ = -(1 + representation.second ^ 2) := by ring1

end FiniteOddFieldPresentation

/-- Exact constructive input replacing the paper's cardinality argument for
a displayed finite field of odd characteristic.  A presentation supplies the
collision calculated for that field rather than globally enumerating all its
elements. -/
structure FiniteOddFieldNullCertificate
    (K : Type*) [RFAP.ExplicitField K] where
  twoNonzero : (2 : K) ≠ 0
  collision : SquareCollision K

namespace FiniteOddFieldNullCertificate

theorem oneNonzero (certificate : FiniteOddFieldNullCertificate K) :
    (1 : K) ≠ 0 := by
  intro oneZero
  apply certificate.twoNonzero
  calc
    (2 : K) = 1 + 1 := by ring1
    _ = 0 := by rw [oneZero, zero_add]

/-- A checked collision certificate computes the nonzero null vector asserted
by the finite-field half of Theorem 2. -/
def witness (certificate : FiniteOddFieldNullCertificate K) :
    NonzeroNullVector K :=
  certificate.collision.nonzeroNullVector certificate.oneNonzero

end FiniteOddFieldNullCertificate

namespace FiniteOddFieldPresentation

variable (presentation : FiniteOddFieldPresentation K)

/-- The complete finite square-table presentation computes the nonzero null
vector asserted by Theorem 2. -/
def nullCertificate : FiniteOddFieldNullCertificate K where
  twoNonzero := presentation.twoNonzero
  collision := presentation.squareCollision

end FiniteOddFieldPresentation

namespace FieldFive

abbrev Scalar := DivineProportions.FieldFive.Element

/-- Example 3's displayed vector `(1,2,0)` over the executable field `F₅`. -/
def nullVector : Vector Scalar := ⟨1, 2, 0⟩

/-- The collision `(0,2)` gives the alternate nonzero null vector `(0,2,1)`
used by the proof of Theorem 2. -/
def squareCollision : SquareCollision Scalar where
  first := 0
  second := 2
  collision := by decide

/-- Root lookup for the three cached square values `0`, `1`, and `4`. -/
private def cachedSquareRoot (value : Scalar) : Scalar :=
  if value = 4 then 2 else value

/-- The complete displayed carrier and square table for the executable `F₅`
model. -/
def finiteOddFieldPresentation : FiniteOddFieldPresentation Scalar where
  eqDecidable := inferInstance
  carrier := [0, 1, 2, 3, 4]
  carrierNodup := by decide
  carrierComplete := by decide +revert
  squareValues := [0, 1, 4]
  squareValuesNodup := by decide
  squareValuesComplete := by decide +revert
  squareRoot := cachedSquareRoot
  squareRoot_spec := by decide +revert
  squareCount := by decide
  twoNonzero := by decide

/-- Fully checked finite odd-field input for the executable `F₅` model,
computed by the generic finite square-table intersection. -/
def finiteOddFieldNullCertificate : FiniteOddFieldNullCertificate Scalar :=
  finiteOddFieldPresentation.nullCertificate

theorem certificateWitness_isNull :
    finiteOddFieldNullCertificate.witness.vector.IsNull :=
  finiteOddFieldNullCertificate.witness.null

theorem certificateWitness_ne_zero :
    finiteOddFieldNullCertificate.witness.vector ≠ Vector.zero :=
  finiteOddFieldNullCertificate.witness.nonzero

/-- Example 3: `(1,2,0)` has quadrance `1+4=0` in `F₅`. -/
theorem nullVector_isNull : nullVector.IsNull := by
  change (1 : Scalar) * 1 + 2 * 2 + 0 * 0 = 0
  decide

/-- Example 3's null vector is nevertheless nonzero. -/
theorem nullVector_ne_zero : nullVector ≠ Vector.zero := by decide

/-- Example 3 also observes that the nonzero null vector is perpendicular to
itself. -/
theorem nullVector_perpendicular_self :
    nullVector.Perpendicular nullVector := by
  change (1 : Scalar) * 1 + 2 * 2 + 0 * 0 = 0
  decide

end FieldFive

end RationalRotations
