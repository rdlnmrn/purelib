import RationalRotations.FiniteFieldSquareClasses
import RationalRotations.QuaternionObstruction
import DivineProportions.Algebra.FieldThree
import DivineProportions.Algebra.FieldSeven

/-!
# Constructive finite-field rotation enumeration

Problem 69 asks for counts over a displayed odd finite field.  This module
provides the executable layer used by those counts.  Projective points are not
obtained from a `Fintype` or a quotient: the four standard first-nonzero
coordinate charts are listed directly, and representatives whose four-square
norm vanishes are removed by a finite test.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

namespace FiniteOddFieldPresentation

variable (presentation : FiniteOddFieldPresentation K)

/-- All displayed affine vectors, in lexicographic carrier order. -/
def vectors : List (Vector K) :=
  presentation.carrier.flatMap fun t =>
    presentation.carrier.flatMap fun r =>
      presentation.carrier.map fun s => ⟨t, r, s⟩

/-- Every displayed four-coordinate proportion, before removing the zero-norm
locus or identifying nonzero scales. -/
def allProportionRepresentatives : List (Proportion K) :=
  presentation.carrier.flatMap fun scalar =>
    presentation.vectors.map fun vector => ⟨scalar, vector⟩

/-- The affine chart of projective three-space, normalized to scalar
coordinate one. -/
def affineProportionRepresentatives : List (Proportion K) :=
  presentation.vectors.map fun vector => ⟨1, vector⟩

/-- The first chart at infinity, normalized to vector coordinate `t = 1`. -/
def infinityTRepresentatives : List (Proportion K) :=
  presentation.carrier.flatMap fun r =>
    presentation.carrier.map fun s => ⟨0, ⟨1, r, s⟩⟩

/-- The second chart at infinity, normalized to `t = 0, r = 1`. -/
def infinityRRepresentatives : List (Proportion K) :=
  presentation.carrier.map fun s => ⟨0, ⟨0, 1, s⟩⟩

/-- The final point at infinity, normalized to `t = r = 0, s = 1`. -/
def infinitySRepresentative : Proportion K := ⟨0, ⟨0, 0, 1⟩⟩

/-- A duplicate-free-by-construction first-nonzero-coordinate list for
projective three-space.  Completeness and uniqueness are proved in the general
counting layer; this definition is already executable. -/
def projectiveRepresentatives : List (Proportion K) :=
  presentation.affineProportionRepresentatives ++
    presentation.infinityTRepresentatives ++
    presentation.infinityRRepresentatives ++
    [infinitySRepresentative]

theorem vectors_complete (vector : Vector K) :
    vector ∈ presentation.vectors := by
  unfold vectors
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨vector.t, presentation.carrierComplete vector.t, ?_⟩
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨vector.r, presentation.carrierComplete vector.r, ?_⟩
  apply QuotientFreeList.mem_map.mpr
  exact ⟨vector.s, presentation.carrierComplete vector.s, rfl⟩

theorem allProportionRepresentatives_complete (raw : Proportion K) :
    raw ∈ presentation.allProportionRepresentatives := by
  unfold allProportionRepresentatives
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨raw.scalar, presentation.carrierComplete raw.scalar, ?_⟩
  apply QuotientFreeList.mem_map.mpr
  exact ⟨raw.vector, presentation.vectors_complete raw.vector, rfl⟩

theorem affineProportion_mem (vector : Vector K) :
    (⟨1, vector⟩ : Proportion K) ∈
      presentation.projectiveRepresentatives := by
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  unfold affineProportionRepresentatives
  exact QuotientFreeList.mem_map.mpr
    ⟨vector, presentation.vectors_complete vector, rfl⟩

theorem infinityTProportion_mem (r s : K) :
    (⟨0, ⟨1, r, s⟩⟩ : Proportion K) ∈
      presentation.projectiveRepresentatives := by
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  right
  unfold infinityTRepresentatives
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨r, presentation.carrierComplete r, ?_⟩
  exact QuotientFreeList.mem_map.mpr
    ⟨s, presentation.carrierComplete s, rfl⟩

theorem infinityRProportion_mem (s : K) :
    (⟨0, ⟨0, 1, s⟩⟩ : Proportion K) ∈
      presentation.projectiveRepresentatives := by
  apply List.mem_append.mpr
  left
  apply List.mem_append.mpr
  right
  unfold infinityRRepresentatives
  exact QuotientFreeList.mem_map.mpr
    ⟨s, presentation.carrierComplete s, rfl⟩

theorem infinitySProportion_mem :
    (infinitySRepresentative : Proportion K) ∈
      presentation.projectiveRepresentatives := by
  apply List.mem_append.mpr
  right
  exact List.mem_singleton.mpr rfl

/-- Membership in the four-chart list exposes the normalized chart and its
displayed free coordinates. -/
theorem projectiveRepresentatives_cases {raw : Proportion K}
    (member : raw ∈ presentation.projectiveRepresentatives) :
    (∃ vector : Vector K, raw = ⟨1, vector⟩) ∨
    (∃ r s : K, raw = ⟨0, ⟨1, r, s⟩⟩) ∨
    (∃ s : K, raw = ⟨0, ⟨0, 1, s⟩⟩) ∨
    raw = infinitySRepresentative := by
  rcases List.mem_append.mp member with beforeS | atS
  · rcases List.mem_append.mp beforeS with beforeR | atR
    · rcases List.mem_append.mp beforeR with atAffine | atT
      · rcases QuotientFreeList.mem_map.mp atAffine with
          ⟨vector, _, equal⟩
        exact Or.inl ⟨vector, equal.symm⟩
      · rcases QuotientFreeList.mem_flatMap.mp atT with
          ⟨r, _, rMember⟩
        rcases QuotientFreeList.mem_map.mp rMember with ⟨s, _, equal⟩
        exact Or.inr (Or.inl ⟨r, s, equal.symm⟩)
    · rcases QuotientFreeList.mem_map.mp atR with ⟨s, _, equal⟩
      exact Or.inr (Or.inr (Or.inl ⟨s, equal.symm⟩))
  · exact Or.inr (Or.inr (Or.inr (List.mem_singleton.mp atS)))

private theorem one_ne_zero
    (presentation : FiniteOddFieldPresentation K) : (1 : K) ≠ 0 := by
  intro oneZero
  apply presentation.twoNonzero
  calc
    (2 : K) = 1 + 1 := by ring1
    _ = 0 := by rw [oneZero, zero_add]

private theorem nodup_flatMap_of_nodup
    {Alpha Beta : Type*} {values : List Alpha} {fiber : Alpha → List Beta}
    (valuesNodup : values.Nodup)
    (fiberNodup : ∀ value ∈ values, (fiber value).Nodup)
    (fiberDisjoint : ∀ left ∈ values, ∀ right ∈ values, left ≠ right →
      ∀ leftValue ∈ fiber left, ∀ rightValue ∈ fiber right,
        leftValue ≠ rightValue) :
    (values.flatMap fiber).Nodup := by
  induction values with
  | nil => exact List.Pairwise.nil
  | cons head tail inductionHypothesis =>
      rw [List.flatMap_cons]
      apply QuotientFreeList.nodup_append
      · exact fiberNodup head List.mem_cons_self
      · apply inductionHypothesis
        · exact (List.pairwise_cons.mp valuesNodup).2
        · intro value member
          exact fiberNodup value (List.mem_cons_of_mem head member)
        · intro left leftMember right rightMember different
          exact fiberDisjoint left (List.mem_cons_of_mem head leftMember)
            right (List.mem_cons_of_mem head rightMember) different
      · intro leftValue leftMember rightValue rightMember
        rcases QuotientFreeList.mem_flatMap.mp rightMember with
          ⟨right, rightInTail, rightValueMember⟩
        exact fiberDisjoint head List.mem_cons_self right
          (List.mem_cons_of_mem head rightInTail)
          ((List.pairwise_cons.mp valuesNodup).1 right rightInTail)
          leftValue leftMember rightValue rightValueMember

theorem vectors_nodup : presentation.vectors.Nodup := by
  unfold vectors
  apply nodup_flatMap_of_nodup presentation.carrierNodup
  · intro t _
    apply nodup_flatMap_of_nodup presentation.carrierNodup
    · intro r _
      apply QuotientFreeList.nodup_map_of_injective
      · intro left right equal
        exact congrArg Vector.s equal
      · exact presentation.carrierNodup
    · intro left _ right _ different leftVector leftMember rightVector
        rightMember equal
      rcases QuotientFreeList.mem_map.mp leftMember with ⟨leftS, _, leftEq⟩
      rcases QuotientFreeList.mem_map.mp rightMember with
        ⟨rightS, _, rightEq⟩
      apply different
      calc
        left = leftVector.r := congrArg Vector.r leftEq
        _ = rightVector.r := congrArg Vector.r equal
        _ = right := (congrArg Vector.r rightEq).symm
  · intro left _ right _ different leftVector leftMember rightVector
      rightMember equal
    rcases QuotientFreeList.mem_flatMap.mp leftMember with
      ⟨leftR, _, leftRMember⟩
    rcases QuotientFreeList.mem_map.mp leftRMember with
      ⟨leftS, _, leftEq⟩
    rcases QuotientFreeList.mem_flatMap.mp rightMember with
      ⟨rightR, _, rightRMember⟩
    rcases QuotientFreeList.mem_map.mp rightRMember with
      ⟨rightS, _, rightEq⟩
    apply different
    calc
      left = leftVector.t := congrArg Vector.t leftEq
      _ = rightVector.t := congrArg Vector.t equal
      _ = right := (congrArg Vector.t rightEq).symm

theorem allProportionRepresentatives_nodup :
    presentation.allProportionRepresentatives.Nodup := by
  unfold allProportionRepresentatives
  apply nodup_flatMap_of_nodup presentation.carrierNodup
  · intro scalar _
    apply QuotientFreeList.nodup_map_of_injective
    · intro left right equal
      exact congrArg Proportion.vector equal
    · exact presentation.vectors_nodup
  · intro left _ right _ different leftRaw leftMember rightRaw rightMember equal
    rcases QuotientFreeList.mem_map.mp leftMember with
      ⟨leftVector, _, leftEq⟩
    rcases QuotientFreeList.mem_map.mp rightMember with
      ⟨rightVector, _, rightEq⟩
    apply different
    calc
      left = leftRaw.scalar := congrArg Proportion.scalar leftEq
      _ = rightRaw.scalar := congrArg Proportion.scalar equal
      _ = right := (congrArg Proportion.scalar rightEq).symm

private theorem affineProportionRepresentatives_nodup :
    presentation.affineProportionRepresentatives.Nodup := by
  unfold affineProportionRepresentatives
  apply QuotientFreeList.nodup_map_of_injective
  · intro left right equal
    exact congrArg Proportion.vector equal
  · exact presentation.vectors_nodup

private theorem infinityTRepresentatives_nodup :
    presentation.infinityTRepresentatives.Nodup := by
  unfold infinityTRepresentatives
  apply nodup_flatMap_of_nodup presentation.carrierNodup
  · intro r _
    apply QuotientFreeList.nodup_map_of_injective
    · intro left right equal
      exact congrArg (fun value : Proportion K => value.vector.s) equal
    · exact presentation.carrierNodup
  · intro left _ right _ different leftValue leftMember rightValue
      rightMember equal
    rcases QuotientFreeList.mem_map.mp leftMember with ⟨leftS, _, leftEq⟩
    rcases QuotientFreeList.mem_map.mp rightMember with
      ⟨rightS, _, rightEq⟩
    apply different
    calc
      left = leftValue.vector.r :=
        congrArg (fun value : Proportion K => value.vector.r) leftEq
      _ = rightValue.vector.r :=
        congrArg (fun value : Proportion K => value.vector.r) equal
      _ = right :=
        (congrArg (fun value : Proportion K => value.vector.r) rightEq).symm

private theorem infinityRRepresentatives_nodup :
    presentation.infinityRRepresentatives.Nodup := by
  unfold infinityRRepresentatives
  apply QuotientFreeList.nodup_map_of_injective
  · intro left right equal
    exact congrArg (fun value : Proportion K => value.vector.s) equal
  · exact presentation.carrierNodup

private theorem affine_infinityT_disjoint {left right : Proportion K}
    (leftMember : left ∈ presentation.affineProportionRepresentatives)
    (rightMember : right ∈ presentation.infinityTRepresentatives) :
    left ≠ right := by
  rcases QuotientFreeList.mem_map.mp leftMember with ⟨vector, _, leftEqual⟩
  rcases QuotientFreeList.mem_flatMap.mp rightMember with
    ⟨r, _, rMember⟩
  rcases QuotientFreeList.mem_map.mp rMember with ⟨s, _, rightEqual⟩
  subst left
  subst right
  intro equal
  exact one_ne_zero presentation (congrArg Proportion.scalar equal)

private theorem beforeR_infinityR_disjoint {left right : Proportion K}
    (leftMember : left ∈
      presentation.affineProportionRepresentatives ++
        presentation.infinityTRepresentatives)
    (rightMember : right ∈ presentation.infinityRRepresentatives) :
    left ≠ right := by
  rcases QuotientFreeList.mem_map.mp rightMember with ⟨s, _, rightEqual⟩
  subst right
  rcases List.mem_append.mp leftMember with atAffine | atT
  · rcases QuotientFreeList.mem_map.mp atAffine with
      ⟨vector, _, leftEqual⟩
    subst left
    intro equal
    exact one_ne_zero presentation (congrArg Proportion.scalar equal)
  · rcases QuotientFreeList.mem_flatMap.mp atT with ⟨r, _, rMember⟩
    rcases QuotientFreeList.mem_map.mp rMember with
      ⟨otherS, _, leftEqual⟩
    subst left
    intro equal
    exact one_ne_zero presentation
      (congrArg (fun value : Proportion K => value.vector.t) equal)

private theorem beforeS_infinityS_disjoint {left right : Proportion K}
    (leftMember : left ∈
      (presentation.affineProportionRepresentatives ++
        presentation.infinityTRepresentatives) ++
        presentation.infinityRRepresentatives)
    (rightMember : right ∈ [infinitySRepresentative]) : left ≠ right := by
  have rightEqual := List.mem_singleton.mp rightMember
  subst right
  rcases List.mem_append.mp leftMember with beforeR | atR
  · rcases List.mem_append.mp beforeR with atAffine | atT
    · rcases QuotientFreeList.mem_map.mp atAffine with
        ⟨vector, _, leftEqual⟩
      subst left
      intro equal
      exact one_ne_zero presentation (congrArg Proportion.scalar equal)
    · rcases QuotientFreeList.mem_flatMap.mp atT with ⟨r, _, rMember⟩
      rcases QuotientFreeList.mem_map.mp rMember with
        ⟨s, _, leftEqual⟩
      subst left
      intro equal
      exact one_ne_zero presentation
        (congrArg (fun value : Proportion K => value.vector.t) equal)
  · rcases QuotientFreeList.mem_map.mp atR with ⟨s, _, leftEqual⟩
    subst left
    intro equal
    exact one_ne_zero presentation
      (congrArg (fun value : Proportion K => value.vector.r) equal)

theorem projectiveRepresentatives_nodup :
    presentation.projectiveRepresentatives.Nodup := by
  unfold projectiveRepresentatives
  have beforeRNodup :
      (presentation.affineProportionRepresentatives ++
        presentation.infinityTRepresentatives).Nodup :=
    QuotientFreeList.nodup_append
      presentation.affineProportionRepresentatives_nodup
      presentation.infinityTRepresentatives_nodup
      (fun left leftMember right rightMember =>
        presentation.affine_infinityT_disjoint leftMember rightMember)
  have beforeSNodup :
      ((presentation.affineProportionRepresentatives ++
        presentation.infinityTRepresentatives) ++
        presentation.infinityRRepresentatives).Nodup :=
    QuotientFreeList.nodup_append beforeRNodup
      presentation.infinityRRepresentatives_nodup
      (fun left leftMember right rightMember =>
        presentation.beforeR_infinityR_disjoint leftMember rightMember)
  exact QuotientFreeList.nodup_append beforeSNodup
    (QuotientFreeList.nodup_singleton infinitySRepresentative)
    (fun left leftMember right rightMember =>
      presentation.beforeS_infinityS_disjoint leftMember rightMember)

/-- Two normalized members of the four projective charts cannot differ by a
nonzero scale.  This is the quotient-free uniqueness theorem behind the
finite rotation carrier. -/
theorem projective_eq_of_equivalent {left right : Proportion K}
    (leftMember : left ∈ presentation.projectiveRepresentatives)
    (rightMember : right ∈ presentation.projectiveRepresentatives)
    (equivalent : left.Equivalent right) : left = right := by
  rcases presentation.projectiveRepresentatives_cases leftMember with
      ⟨leftVector, leftEqual⟩ |
      ⟨leftR, leftS, leftEqual⟩ |
      ⟨leftS, leftEqual⟩ | leftEqual <;>
    rcases presentation.projectiveRepresentatives_cases rightMember with
      ⟨rightVector, rightEqual⟩ |
      ⟨rightR, rightS, rightEqual⟩ |
      ⟨rightS, rightEqual⟩ | rightEqual <;>
    subst left <;> subst right
  all_goals
    rcases equivalent with ⟨factor, factorNonzero, scaled⟩
  · have scalar := congrArg Proportion.scalar scaled
    change (1 : K) = factor * 1 at scalar
    have factorOne : factor = 1 := by simpa using scalar.symm
    subst factor
    rw [Proportion.one_scale] at scaled
    exact scaled.symm
  · have scalar := congrArg Proportion.scalar scaled
    change (0 : K) = factor * 1 at scalar
    exact False.elim (factorNonzero (by simpa using scalar.symm))
  · have scalar := congrArg Proportion.scalar scaled
    change (0 : K) = factor * 1 at scalar
    exact False.elim (factorNonzero (by simpa using scalar.symm))
  · have scalar := congrArg Proportion.scalar scaled
    change (0 : K) = factor * 1 at scalar
    exact False.elim (factorNonzero (by simpa using scalar.symm))
  · have scalar := congrArg Proportion.scalar scaled
    change (1 : K) = factor * 0 at scalar
    exact False.elim (one_ne_zero presentation (by simpa using scalar))
  · have tCoordinate := congrArg (fun value : Proportion K => value.vector.t)
      scaled
    change (1 : K) = factor * 1 at tCoordinate
    have factorOne : factor = 1 := by simpa using tCoordinate.symm
    subst factor
    rw [Proportion.one_scale] at scaled
    exact scaled.symm
  · have tCoordinate := congrArg (fun value : Proportion K => value.vector.t)
      scaled
    change (0 : K) = factor * 1 at tCoordinate
    exact False.elim (factorNonzero (by simpa using tCoordinate.symm))
  · have tCoordinate := congrArg (fun value : Proportion K => value.vector.t)
      scaled
    change (0 : K) = factor * 1 at tCoordinate
    exact False.elim (factorNonzero (by simpa using tCoordinate.symm))
  · have scalar := congrArg Proportion.scalar scaled
    change (1 : K) = factor * 0 at scalar
    exact False.elim (one_ne_zero presentation (by simpa using scalar))
  · have tCoordinate := congrArg (fun value : Proportion K => value.vector.t)
      scaled
    change (1 : K) = factor * 0 at tCoordinate
    exact False.elim (one_ne_zero presentation (by simpa using tCoordinate))
  · have rCoordinate := congrArg (fun value : Proportion K => value.vector.r)
      scaled
    change (1 : K) = factor * 1 at rCoordinate
    have factorOne : factor = 1 := by simpa using rCoordinate.symm
    subst factor
    rw [Proportion.one_scale] at scaled
    exact scaled.symm
  · have rCoordinate := congrArg (fun value : Proportion K => value.vector.r)
      scaled
    change (0 : K) = factor * 1 at rCoordinate
    exact False.elim (factorNonzero (by simpa using rCoordinate.symm))
  · have scalar := congrArg Proportion.scalar scaled
    change (1 : K) = factor * 0 at scalar
    exact False.elim (one_ne_zero presentation (by simpa using scalar))
  · have tCoordinate := congrArg (fun value : Proportion K => value.vector.t)
      scaled
    change (1 : K) = factor * 0 at tCoordinate
    exact False.elim (one_ne_zero presentation (by simpa using tCoordinate))
  · have rCoordinate := congrArg (fun value : Proportion K => value.vector.r)
      scaled
    change (1 : K) = factor * 0 at rCoordinate
    exact False.elim (one_ne_zero presentation (by simpa using rCoordinate))
  · rfl

/-- Turn one raw projective representative into cached non-null data exactly
when its four-square norm is nonzero. -/
def certifyNonNull (raw : Proportion K) : Option (NonNullProportion K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact if normZero : raw.norm = 0 then none else
    some { toProportion := raw, normNonzero := normZero }

/-- Canonical non-null projective representatives.  Via the projective
rotation theorem these are the executable rotation carrier for Problem 69. -/
def nonNullProjectiveRepresentatives : List (NonNullProportion K) :=
  presentation.projectiveRepresentatives.filterMap presentation.certifyNonNull

/-- Every displayed non-null four-tuple, before quotienting by scale. -/
def allNonNullProportionRepresentatives : List (NonNullProportion K) :=
  presentation.allProportionRepresentatives.filterMap
    presentation.certifyNonNull

/-- A scalar bundled with the executable nonzeroness certificate needed for
projective rescaling. -/
structure DisplayedNonzeroScalar where
  value : K
  nonzero : value ≠ 0

theorem DisplayedNonzeroScalar.ext
    {left right : DisplayedNonzeroScalar (K := K)}
    (valueEq : left.value = right.value) : left = right := by
  cases left
  cases right
  cases valueEq
  rfl

def certifyNonzeroScalar (value : K) :
    Option (DisplayedNonzeroScalar (K := K)) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact if valueZero : value = 0 then none else
    some ⟨value, valueZero⟩

/-- Duplicate-free displayed carrier of the multiplicative nonzero scalars,
with every proof required for scaling cached in each element. -/
def nonzeroScalarWitnesses : List (DisplayedNonzeroScalar (K := K)) :=
  presentation.carrier.filterMap presentation.certifyNonzeroScalar

/-- Cached normalization of a non-null displayed proportion to the unique
first-nonzero-coordinate chart used by `projectiveRepresentatives`. -/
structure Canonicalization (source : NonNullProportion K) where
  representative : NonNullProportion K
  member : representative.toProportion ∈
    presentation.projectiveRepresentatives
  factor : K
  factorNonzero : factor ≠ 0
  representative_eq_scale :
    representative = source.scale factor factorNonzero
  equivalent : source.Equivalent representative

private theorem inverse_mul (value : K) (nonzero : value ≠ 0) :
    value⁻¹ * value = 1 := by
  calc
    value⁻¹ * value = value * value⁻¹ := by ring1
    _ = 1 := RFAP.ExplicitField.mul_inv_cancel value nonzero

private theorem eq_zero_of_not_ne (eqDecidable : DecidableEq K)
    {value : K} (notNonzero : ¬ value ≠ 0) : value = 0 := by
  cases eqDecidable value 0 with
  | isTrue equal => exact equal
  | isFalse nonzero => exact False.elim (notNonzero nonzero)

/-- Normalize by the first nonzero coordinate.  All four branches and the
scale witness are computed directly; no representative is chosen from a
quotient. -/
def canonicalize (source : NonNullProportion K) :
    presentation.Canonicalization source := by
  letI : DecidableEq K := presentation.eqDecidable
  if scalarNonzero : source.scalar ≠ 0 then
    let factor := source.scalar⁻¹
    have factorNonzero : factor ≠ 0 :=
      RFAP.ExplicitField.inv_ne_zero scalarNonzero
    let representative := source.scale factor factorNonzero
    refine
      { representative := representative
        member := ?_
        factor := factor
        factorNonzero := factorNonzero
        representative_eq_scale := rfl
        equivalent := ⟨factor, factorNonzero, rfl⟩ }
    have rawEqual : representative.toProportion =
        (⟨1, Vector.scale factor source.vector⟩ : Proportion K) := by
      change Proportion.scale factor source.toProportion = _
      apply Proportion.ext
      · exact inverse_mul source.scalar scalarNonzero
      · rfl
    rw [rawEqual]
    exact presentation.affineProportion_mem _
  else if tNonzero : source.vector.t ≠ 0 then
    let factor := source.vector.t⁻¹
    have factorNonzero : factor ≠ 0 :=
      RFAP.ExplicitField.inv_ne_zero tNonzero
    let representative := source.scale factor factorNonzero
    refine
      { representative := representative
        member := ?_
        factor := factor
        factorNonzero := factorNonzero
        representative_eq_scale := rfl
        equivalent := ⟨factor, factorNonzero, rfl⟩ }
    have rawEqual : representative.toProportion =
        (⟨0, ⟨1, factor * source.vector.r,
          factor * source.vector.s⟩⟩ : Proportion K) := by
      change Proportion.scale factor source.toProportion = _
      apply Proportion.ext
      · unfold Proportion.scale
        rw [eq_zero_of_not_ne presentation.eqDecidable scalarNonzero]
        ring1
      · apply Vector.ext
        · exact inverse_mul source.vector.t tNonzero
        · rfl
        · rfl
    rw [rawEqual]
    exact presentation.infinityTProportion_mem _ _
  else if rNonzero : source.vector.r ≠ 0 then
    let factor := source.vector.r⁻¹
    have factorNonzero : factor ≠ 0 :=
      RFAP.ExplicitField.inv_ne_zero rNonzero
    let representative := source.scale factor factorNonzero
    refine
      { representative := representative
        member := ?_
        factor := factor
        factorNonzero := factorNonzero
        representative_eq_scale := rfl
        equivalent := ⟨factor, factorNonzero, rfl⟩ }
    have rawEqual : representative.toProportion =
        (⟨0, ⟨0, 1, factor * source.vector.s⟩⟩ : Proportion K) := by
      change Proportion.scale factor source.toProportion = _
      apply Proportion.ext
      · unfold Proportion.scale
        rw [eq_zero_of_not_ne presentation.eqDecidable scalarNonzero]
        ring1
      · apply Vector.ext
        · unfold Proportion.scale Vector.scale
          rw [eq_zero_of_not_ne presentation.eqDecidable tNonzero]
          ring1
        · exact inverse_mul source.vector.r rNonzero
        · rfl
    rw [rawEqual]
    exact presentation.infinityRProportion_mem _
  else
    have sNonzero : source.vector.s ≠ 0 := by
      intro sZero
      apply source.normNonzero
      unfold Proportion.norm Vector.quadrance Vector.dot
      rw [eq_zero_of_not_ne presentation.eqDecidable scalarNonzero,
        eq_zero_of_not_ne presentation.eqDecidable tNonzero,
        eq_zero_of_not_ne presentation.eqDecidable rNonzero, sZero]
      ring1
    let factor := source.vector.s⁻¹
    have factorNonzero : factor ≠ 0 :=
      RFAP.ExplicitField.inv_ne_zero sNonzero
    let representative := source.scale factor factorNonzero
    refine
      { representative := representative
        member := ?_
        factor := factor
        factorNonzero := factorNonzero
        representative_eq_scale := rfl
        equivalent := ⟨factor, factorNonzero, rfl⟩ }
    have rawEqual : representative.toProportion =
        (infinitySRepresentative : Proportion K) := by
      change Proportion.scale factor source.toProportion = _
      apply Proportion.ext
      · unfold Proportion.scale infinitySRepresentative
        rw [eq_zero_of_not_ne presentation.eqDecidable scalarNonzero]
        ring1
      · apply Vector.ext
        · unfold Proportion.scale Vector.scale infinitySRepresentative
          rw [eq_zero_of_not_ne presentation.eqDecidable tNonzero]
          ring1
        · unfold Proportion.scale Vector.scale infinitySRepresentative
          rw [eq_zero_of_not_ne presentation.eqDecidable rNonzero]
          ring1
        · exact inverse_mul source.vector.s sNonzero
    rw [rawEqual]
    exact presentation.infinitySProportion_mem

theorem certifyNonNull_self (proportion : NonNullProportion K) :
    presentation.certifyNonNull proportion.toProportion = some proportion := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold certifyNonNull
  rw [dif_neg proportion.normNonzero]

private theorem certifyNonNull_eq_some_toProportion
    {raw : Proportion K} {result : NonNullProportion K}
    (certified : presentation.certifyNonNull raw = some result) :
    result.toProportion = raw := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold certifyNonNull at certified
  split at certified
  · contradiction
  · injection certified with resultEqual
    exact (congrArg NonNullProportion.toProportion resultEqual).symm

private theorem certifyNonNull_filterMap_nodup
    (presentation : FiniteOddFieldPresentation K) :
    ∀ (values : List (Proportion K)), values.Nodup →
      (values.filterMap presentation.certifyNonNull).Nodup
  | [], _ => List.Pairwise.nil
  | head :: tail, nodup => by
      cases certified : presentation.certifyNonNull head with
      | none =>
          rw [List.filterMap_cons_none certified]
          exact certifyNonNull_filterMap_nodup (presentation := presentation) tail
            (List.pairwise_cons.mp nodup).2
      | some headResult =>
          rw [List.filterMap_cons_some certified]
          apply List.pairwise_cons.mpr
          constructor
          · intro result resultMember resultsEqual
            rcases QuotientFreeList.mem_filterMap.mp resultMember with
              ⟨raw, rawMember, rawCertified⟩
            apply (List.pairwise_cons.mp nodup).1 raw rawMember
            calc
              head = headResult.toProportion :=
                (presentation.certifyNonNull_eq_some_toProportion
                  certified).symm
              _ = result.toProportion :=
                congrArg NonNullProportion.toProportion resultsEqual
              _ = raw :=
                presentation.certifyNonNull_eq_some_toProportion rawCertified
          · exact certifyNonNull_filterMap_nodup (presentation := presentation)
              tail
              (List.pairwise_cons.mp nodup).2

theorem allNonNullProportionRepresentatives_nodup :
    presentation.allNonNullProportionRepresentatives.Nodup := by
  unfold allNonNullProportionRepresentatives
  exact certifyNonNull_filterMap_nodup (presentation := presentation)
    presentation.allProportionRepresentatives
    presentation.allProportionRepresentatives_nodup

theorem allNonNullProportionRepresentatives_complete
    (proportion : NonNullProportion K) :
    proportion ∈ presentation.allNonNullProportionRepresentatives := by
  unfold allNonNullProportionRepresentatives
  apply QuotientFreeList.mem_filterMap.mpr
  exact
    ⟨proportion.toProportion,
      presentation.allProportionRepresentatives_complete
        proportion.toProportion,
      presentation.certifyNonNull_self proportion⟩

theorem certifyNonzeroScalar_self
    (scalar : DisplayedNonzeroScalar (K := K)) :
    presentation.certifyNonzeroScalar scalar.value = some scalar := by
  cases scalar with
  | mk value nonzero =>
      letI : DecidableEq K := presentation.eqDecidable
      unfold certifyNonzeroScalar
      rw [dif_neg nonzero]

private theorem certifyNonzeroScalar_eq_some_value
    {raw : K} {result : DisplayedNonzeroScalar (K := K)}
    (certified : presentation.certifyNonzeroScalar raw = some result) :
    result.value = raw := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold certifyNonzeroScalar at certified
  split at certified
  · contradiction
  · injection certified with resultEqual
    exact (congrArg DisplayedNonzeroScalar.value resultEqual).symm

private theorem certifyNonzeroScalar_filterMap_nodup :
    ∀ (values : List K), values.Nodup →
      (values.filterMap presentation.certifyNonzeroScalar).Nodup
  | [], _ => List.Pairwise.nil
  | head :: tail, nodup => by
      cases certified : presentation.certifyNonzeroScalar head with
      | none =>
          rw [List.filterMap_cons_none certified]
          exact certifyNonzeroScalar_filterMap_nodup tail
            (List.pairwise_cons.mp nodup).2
      | some headResult =>
          rw [List.filterMap_cons_some certified]
          apply List.pairwise_cons.mpr
          constructor
          · intro result resultMember resultsEqual
            rcases QuotientFreeList.mem_filterMap.mp resultMember with
              ⟨raw, rawMember, rawCertified⟩
            apply (List.pairwise_cons.mp nodup).1 raw rawMember
            calc
              head = headResult.value :=
                (presentation.certifyNonzeroScalar_eq_some_value
                  certified).symm
              _ = result.value :=
                congrArg DisplayedNonzeroScalar.value resultsEqual
              _ = raw :=
                presentation.certifyNonzeroScalar_eq_some_value rawCertified
          · exact certifyNonzeroScalar_filterMap_nodup tail
              (List.pairwise_cons.mp nodup).2

theorem nonzeroScalarWitnesses_nodup :
    presentation.nonzeroScalarWitnesses.Nodup := by
  unfold nonzeroScalarWitnesses
  exact certifyNonzeroScalar_filterMap_nodup presentation
    presentation.carrier presentation.carrierNodup

theorem nonzeroScalarWitnesses_complete
    (scalar : DisplayedNonzeroScalar (K := K)) :
    scalar ∈ presentation.nonzeroScalarWitnesses := by
  unfold nonzeroScalarWitnesses
  apply QuotientFreeList.mem_filterMap.mpr
  exact
    ⟨scalar.value, presentation.carrierComplete scalar.value,
      presentation.certifyNonzeroScalar_self scalar⟩

private def displayedNonzeroScalarOfValue (value : K) :
    DisplayedNonzeroScalar (K := K) := by
  letI : DecidableEq K := presentation.eqDecidable
  if valueZero : value = 0 then
    exact ⟨1, one_ne_zero presentation⟩
  else
    exact ⟨value, valueZero⟩

/-- Forgetting the bundled proof identifies the cached scalar carrier with
the independently used list of nonzero field elements. -/
def nonzeroScalarWitnessValueBijection : FiniteListBijection
    presentation.nonzeroScalarWitnesses presentation.nonzeroScalars where
  forward := DisplayedNonzeroScalar.value
  backward := presentation.displayedNonzeroScalarOfValue
  forward_mem := by
    intro scalar _
    exact (presentation.mem_nonzeroScalars_iff scalar.value).2
      ⟨scalar.nonzero, presentation.carrierComplete scalar.value⟩
  backward_mem := by
    intro value member
    exact presentation.nonzeroScalarWitnesses_complete
      (presentation.displayedNonzeroScalarOfValue value)
  backward_forward := by
    intro scalar _
    apply DisplayedNonzeroScalar.ext
    letI : DecidableEq K := presentation.eqDecidable
    unfold displayedNonzeroScalarOfValue
    rw [dif_neg scalar.nonzero]
  forward_backward := by
    intro value member
    have valueNonzero :=
      (presentation.mem_nonzeroScalars_iff value).1 member |>.1
    letI : DecidableEq K := presentation.eqDecidable
    unfold displayedNonzeroScalarOfValue
    rw [dif_neg valueNonzero]

theorem nonNullProjectiveRepresentatives_nodup :
    presentation.nonNullProjectiveRepresentatives.Nodup := by
  unfold nonNullProjectiveRepresentatives
  exact certifyNonNull_filterMap_nodup (presentation := presentation)
    presentation.projectiveRepresentatives
    presentation.projectiveRepresentatives_nodup

theorem raw_mem_of_nonNull_mem {proportion : NonNullProportion K}
    (member : proportion ∈ presentation.nonNullProjectiveRepresentatives) :
    proportion.toProportion ∈ presentation.projectiveRepresentatives := by
  unfold nonNullProjectiveRepresentatives at member
  rcases QuotientFreeList.mem_filterMap.mp member with
    ⟨raw, rawMember, certified⟩
  rw [presentation.certifyNonNull_eq_some_toProportion certified]
  exact rawMember

theorem canonicalize_mem (source : NonNullProportion K) :
    (presentation.canonicalize source).representative ∈
      presentation.nonNullProjectiveRepresentatives := by
  unfold nonNullProjectiveRepresentatives
  apply QuotientFreeList.mem_filterMap.mpr
  exact
    ⟨(presentation.canonicalize source).representative.toProportion,
      (presentation.canonicalize source).member,
      presentation.certifyNonNull_self
        (presentation.canonicalize source).representative⟩

/-- A displayed canonical projective representative cannot be fixed by a
nontrivial scalar.  The proof reads the normalized coordinate equal to one in
each of the four charts. -/
private theorem scale_factor_eq_one_of_projective_member
    {raw : Proportion K}
    (member : raw ∈ presentation.projectiveRepresentatives)
    (factor : K) (fixed : raw = Proportion.scale factor raw) :
    factor = 1 := by
  rcases presentation.projectiveRepresentatives_cases member with
      ⟨vector, rawEq⟩ |
      ⟨r, s, rawEq⟩ |
      ⟨s, rawEq⟩ | rawEq
  · have coordinate := congrArg Proportion.scalar fixed
    rw [rawEq] at coordinate
    change (1 : K) = factor * 1 at coordinate
    simpa only [mul_one] using coordinate.symm
  · have coordinate := congrArg
      (fun value : Proportion K => value.vector.t) fixed
    rw [rawEq] at coordinate
    change (1 : K) = factor * 1 at coordinate
    simpa only [mul_one] using coordinate.symm
  · have coordinate := congrArg
      (fun value : Proportion K => value.vector.r) fixed
    rw [rawEq] at coordinate
    change (1 : K) = factor * 1 at coordinate
    simpa only [mul_one] using coordinate.symm
  · have coordinate := congrArg
      (fun value : Proportion K => value.vector.s) fixed
    rw [rawEq] at coordinate
    change (1 : K) = factor * 1 at coordinate
    simpa only [mul_one] using coordinate.symm

/-- The explicit nonzero-scale orbits: one cached scalar paired with one
canonical non-null projective representative. -/
def scaleOrbitCoordinates : List
    (DisplayedNonzeroScalar (K := K) × NonNullProportion K) :=
  presentation.nonzeroScalarWitnesses.flatMap fun scalar =>
    presentation.nonNullProjectiveRepresentatives.map fun representative =>
      (scalar, representative)

theorem mem_scaleOrbitCoordinates_iff
    (coordinate : DisplayedNonzeroScalar (K := K) × NonNullProportion K) :
    coordinate ∈ presentation.scaleOrbitCoordinates ↔
      coordinate.1 ∈ presentation.nonzeroScalarWitnesses ∧
        coordinate.2 ∈ presentation.nonNullProjectiveRepresentatives := by
  constructor
  · intro member
    unfold scaleOrbitCoordinates at member
    rcases QuotientFreeList.mem_flatMap.mp member with
      ⟨scalar, scalarMember, pairMember⟩
    rcases QuotientFreeList.mem_map.mp pairMember with
      ⟨representative, representativeMember, pairEq⟩
    subst coordinate
    exact ⟨scalarMember, representativeMember⟩
  · rintro ⟨scalarMember, representativeMember⟩
    unfold scaleOrbitCoordinates
    apply QuotientFreeList.mem_flatMap.mpr
    exact
      ⟨coordinate.1, scalarMember,
        QuotientFreeList.mem_map.mpr
          ⟨coordinate.2, representativeMember, rfl⟩⟩

theorem scaleOrbitCoordinates_nodup :
    presentation.scaleOrbitCoordinates.Nodup := by
  unfold scaleOrbitCoordinates
  apply nodup_flatMap_of_nodup presentation.nonzeroScalarWitnesses_nodup
  · intro scalar _
    apply QuotientFreeList.nodup_map_of_injective
    · intro left right equal
      exact congrArg Prod.snd equal
    · exact presentation.nonNullProjectiveRepresentatives_nodup
  · intro left _ right _ different leftPair leftMember rightPair rightMember
      pairEq
    rcases QuotientFreeList.mem_map.mp leftMember with
      ⟨leftRepresentative, _, leftEq⟩
    rcases QuotientFreeList.mem_map.mp rightMember with
      ⟨rightRepresentative, _, rightEq⟩
    apply different
    calc
      left = leftPair.1 := congrArg Prod.fst leftEq
      _ = rightPair.1 := congrArg Prod.fst pairEq
      _ = right := (congrArg Prod.fst rightEq).symm

/-- Normalize a displayed non-null four-tuple and retain the inverse scaling
factor needed to reconstruct it from its canonical projective point. -/
def scaleOrbitForward (source : NonNullProportion K) :
    DisplayedNonzeroScalar (K := K) × NonNullProportion K :=
  let normalization := presentation.canonicalize source
  (⟨normalization.factor⁻¹,
      RFAP.ExplicitField.inv_ne_zero normalization.factorNonzero⟩,
    normalization.representative)

/-- Reconstruct a displayed non-null four-tuple from its nonzero scale and
canonical projective representative. -/
def scaleOrbitBackward
    (coordinate : DisplayedNonzeroScalar (K := K) × NonNullProportion K) :
    NonNullProportion K :=
  coordinate.2.scale coordinate.1.value coordinate.1.nonzero

theorem scaleOrbitForward_mem (source : NonNullProportion K) :
    presentation.scaleOrbitForward source ∈
      presentation.scaleOrbitCoordinates := by
  apply (presentation.mem_scaleOrbitCoordinates_iff
    (presentation.scaleOrbitForward source)).2
  exact
    ⟨presentation.nonzeroScalarWitnesses_complete
      (presentation.scaleOrbitForward source).1,
      presentation.canonicalize_mem source⟩

theorem scaleOrbitBackward_mem
    (coordinate : DisplayedNonzeroScalar (K := K) × NonNullProportion K) :
    scaleOrbitBackward coordinate ∈
      presentation.allNonNullProportionRepresentatives :=
  presentation.allNonNullProportionRepresentatives_complete
    (scaleOrbitBackward coordinate)

theorem scaleOrbitBackward_forward (source : NonNullProportion K) :
    scaleOrbitBackward
      (presentation.scaleOrbitForward source) = source := by
  let normalization := presentation.canonicalize source
  have inverseCancel : normalization.factor⁻¹ * normalization.factor = 1 := by
    calc
      normalization.factor⁻¹ * normalization.factor =
          normalization.factor * normalization.factor⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel normalization.factor
        normalization.factorNonzero
  have rawEq :
      (normalization.representative.scale normalization.factor⁻¹
        (RFAP.ExplicitField.inv_ne_zero
          normalization.factorNonzero)).toProportion =
        source.toProportion := by
    calc
      (normalization.representative.scale normalization.factor⁻¹
          (RFAP.ExplicitField.inv_ne_zero
            normalization.factorNonzero)).toProportion =
        Proportion.scale normalization.factor⁻¹
          normalization.representative.toProportion := rfl
      _ = Proportion.scale normalization.factor⁻¹
          (Proportion.scale normalization.factor source.toProportion) := by
        exact congrArg (Proportion.scale normalization.factor⁻¹)
          (congrArg NonNullProportion.toProportion
            normalization.representative_eq_scale)
      _ = Proportion.scale
          (normalization.factor⁻¹ * normalization.factor)
            source.toProportion :=
        Proportion.scale_scale _ _ _
      _ = source.toProportion := by
        rw [inverseCancel, Proportion.one_scale]
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar rawEq
  · exact congrArg Proportion.vector rawEq

theorem scaleOrbitForward_backward
    (coordinate : DisplayedNonzeroScalar (K := K) × NonNullProportion K)
    (member : coordinate ∈ presentation.scaleOrbitCoordinates) :
    presentation.scaleOrbitForward
      (scaleOrbitBackward coordinate) = coordinate := by
  let source := scaleOrbitBackward coordinate
  let normalization := presentation.canonicalize source
  have coordinateParts :=
    (presentation.mem_scaleOrbitCoordinates_iff coordinate).1 member
  have representativeRawEq : normalization.representative.toProportion =
      Proportion.scale
        (normalization.factor * coordinate.1.value)
          coordinate.2.toProportion := by
    calc
      normalization.representative.toProportion =
          (source.scale normalization.factor
            normalization.factorNonzero).toProportion :=
        congrArg NonNullProportion.toProportion
          normalization.representative_eq_scale
      _ = Proportion.scale normalization.factor
          (Proportion.scale coordinate.1.value
            coordinate.2.toProportion) := rfl
      _ = Proportion.scale
          (normalization.factor * coordinate.1.value)
            coordinate.2.toProportion :=
        Proportion.scale_scale _ _ _
  have equivalent : coordinate.2.Equivalent normalization.representative :=
    ⟨normalization.factor * coordinate.1.value,
      RFAP.ExplicitField.mul_ne_zero normalization.factorNonzero
        coordinate.1.nonzero,
      representativeRawEq⟩
  have representativeRawEqual : coordinate.2.toProportion =
      normalization.representative.toProportion :=
    presentation.projective_eq_of_equivalent
      (presentation.raw_mem_of_nonNull_mem coordinateParts.2)
      normalization.member equivalent
  have representativeEq : coordinate.2 = normalization.representative := by
    apply NonNullProportion.ext (K := K)
    · exact congrArg Proportion.scalar representativeRawEqual
    · exact congrArg Proportion.vector representativeRawEqual
  have fixed : coordinate.2.toProportion = Proportion.scale
      (normalization.factor * coordinate.1.value)
        coordinate.2.toProportion := by
    calc
      coordinate.2.toProportion = normalization.representative.toProportion :=
        congrArg NonNullProportion.toProportion representativeEq
      _ = Proportion.scale
          (normalization.factor * coordinate.1.value)
            coordinate.2.toProportion := representativeRawEq
  have productOne : normalization.factor * coordinate.1.value = 1 :=
    presentation.scale_factor_eq_one_of_projective_member
      (presentation.raw_mem_of_nonNull_mem coordinateParts.2)
      (normalization.factor * coordinate.1.value) fixed
  have inverseCancel : normalization.factor⁻¹ * normalization.factor = 1 := by
    calc
      normalization.factor⁻¹ * normalization.factor =
          normalization.factor * normalization.factor⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel normalization.factor
        normalization.factorNonzero
  have scalarEq : normalization.factor⁻¹ = coordinate.1.value := by
    calc
      normalization.factor⁻¹ = normalization.factor⁻¹ * 1 := by ring1
      _ = normalization.factor⁻¹ *
          (normalization.factor * coordinate.1.value) := by rw [productOne]
      _ = (normalization.factor⁻¹ * normalization.factor) *
          coordinate.1.value := by ring1
      _ = coordinate.1.value := by rw [inverseCancel, one_mul]
  apply Prod.ext
  · exact DisplayedNonzeroScalar.ext scalarEq
  · exact representativeEq.symm

/-- Explicit partition of every displayed non-null four-tuple into a unique
nonzero scale and canonical projective representative. -/
def nonNullScaleOrbitBijection : FiniteListBijection
    presentation.allNonNullProportionRepresentatives
      presentation.scaleOrbitCoordinates where
  forward := presentation.scaleOrbitForward
  backward := scaleOrbitBackward
  forward_mem := fun source _ => presentation.scaleOrbitForward_mem source
  backward_mem := fun coordinate _ =>
    presentation.scaleOrbitBackward_mem coordinate
  backward_forward := fun source _ =>
    presentation.scaleOrbitBackward_forward source
  forward_backward := fun coordinate member =>
    presentation.scaleOrbitForward_backward coordinate member

/-- The corresponding computed rotation list.  Its duplicate-freeness and
completeness are inherited from the canonical projective list and the inverse
theorem, rather than checked by matrix equality. -/
def rotations : List (Rotation K) :=
  presentation.nonNullProjectiveRepresentatives.map
    NonNullProportion.rotation

private theorem rotation_eq_of_matrix_eq {left right : Rotation K}
    (equal : left.matrix = right.matrix) : left = right := by
  cases left
  cases right
  cases equal
  rfl

private theorem nodup_map_of_injective_on
    {Alpha Beta : Type*} {values : List Alpha} (function : Alpha → Beta)
    (injectiveOn : ∀ left ∈ values, ∀ right ∈ values,
      function left = function right → left = right)
    (valuesNodup : values.Nodup) : (values.map function).Nodup := by
  induction values with
  | nil => exact List.Pairwise.nil
  | cons head tail inductionHypothesis =>
      rw [List.map_cons]
      apply List.pairwise_cons.mpr
      constructor
      · intro mapped mappedMember equal
        rcases QuotientFreeList.mem_map.mp mappedMember with
          ⟨source, sourceMember, sourceEqual⟩
        apply (List.pairwise_cons.mp valuesNodup).1 source sourceMember
        apply injectiveOn head List.mem_cons_self source
          (List.mem_cons_of_mem head sourceMember)
        exact equal.trans sourceEqual.symm
      · apply inductionHypothesis
        · intro left leftMember right rightMember equal
          exact injectiveOn left (List.mem_cons_of_mem head leftMember)
            right (List.mem_cons_of_mem head rightMember) equal
        · exact (List.pairwise_cons.mp valuesNodup).2

private theorem rotation_injective_on_canonical
    {left right : NonNullProportion K}
    (leftMember : left ∈ presentation.nonNullProjectiveRepresentatives)
    (rightMember : right ∈ presentation.nonNullProjectiveRepresentatives)
    (equal : left.rotation = right.rotation) : left = right := by
  letI : DecidableEq K := presentation.eqDecidable
  have matrixEqual : left.rotationMatrix = right.rotationMatrix :=
    congrArg Rotation.matrix equal
  have equivalent := NonNullProportion.equivalent_of_rotationMatrix_eq
    left right presentation.twoNonzero matrixEqual
  have rawEqual := presentation.projective_eq_of_equivalent
    (presentation.raw_mem_of_nonNull_mem leftMember)
    (presentation.raw_mem_of_nonNull_mem rightMember) equivalent
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar rawEqual
  · exact congrArg Proportion.vector rawEqual

theorem rotations_nodup : presentation.rotations.Nodup := by
  unfold rotations
  apply nodup_map_of_injective_on NonNullProportion.rotation
  · intro left leftMember right rightMember equal
    exact presentation.rotation_injective_on_canonical leftMember rightMember
      equal
  · exact presentation.nonNullProjectiveRepresentatives_nodup

/-- Every stored rotation occurs in the explicit canonical projective list.
The witness is the normalized executable inverse from Theorem 58. -/
theorem rotations_complete (rotation : Rotation K) :
    rotation ∈ presentation.rotations := by
  letI : DecidableEq K := presentation.eqDecidable
  let source := RotationProportion.ofRotation rotation presentation.twoNonzero
  let normalized := (presentation.canonicalize source).representative
  apply QuotientFreeList.mem_map.mpr
  refine ⟨normalized, presentation.canonicalize_mem source, ?_⟩
  apply rotation_eq_of_matrix_eq
  change normalized.rotationMatrix = rotation.matrix
  calc
    normalized.rotationMatrix = source.rotationMatrix :=
      (NonNullProportion.rotationMatrix_respects_equivalent
        (presentation.canonicalize source).equivalent).symm
    _ = rotation.matrix :=
      RotationProportion.ofRotation_rotationMatrix rotation
        presentation.twoNonzero

/-- A complete duplicate-free executable carrier of finite-field rotations. -/
structure RotationEnumeration where
  values : List (Rotation K)
  nodup : values.Nodup
  complete : ∀ rotation : Rotation K, rotation ∈ values

/-- The canonical four-chart rotation enumeration packaged with both finite
carrier certificates. -/
def rotationEnumeration : RotationEnumeration (K := K) where
  values := presentation.rotations
  nodup := presentation.rotations_nodup
  complete := presentation.rotations_complete

/-- The matrices underlying the canonical rotation carrier.  Keeping this
list separately makes matrix-level finite searches executable without
recomputing the projective rotation map. -/
def rotationMatrices : List (Matrix3 K) :=
  presentation.rotations.map Rotation.matrix

theorem rotationMatrices_nodup : presentation.rotationMatrices.Nodup := by
  unfold rotationMatrices
  apply nodup_map_of_injective_on Rotation.matrix
  · intro left _ right _ matrixEqual
    exact rotation_eq_of_matrix_eq matrixEqual
  · exact presentation.rotations_nodup

theorem rotationMatrices_complete (rotation : Rotation K) :
    rotation.matrix ∈ presentation.rotationMatrices := by
  unfold rotationMatrices
  exact QuotientFreeList.mem_map.mpr
    ⟨rotation, presentation.rotations_complete rotation, rfl⟩

/-- Complete duplicate-free executable carrier of the matrices representing
finite-field rotations. -/
structure RotationMatrixEnumeration where
  values : List (Matrix3 K)
  nodup : values.Nodup
  realizes : ∀ rotation : Rotation K, rotation.matrix ∈ values

def rotationMatrixEnumeration : RotationMatrixEnumeration (K := K) where
  values := presentation.rotationMatrices
  nodup := presentation.rotationMatrices_nodup
  realizes := presentation.rotationMatrices_complete

/-- Executable inverse from a finite-field rotation to its unique canonical
four-chart projective representative. -/
def canonicalRotationRepresentative (rotation : Rotation K) :
    NonNullProportion K := by
  letI : DecidableEq K := presentation.eqDecidable
  exact (presentation.canonicalize
    (RotationProportion.ofRotation rotation
      presentation.twoNonzero)).representative

theorem canonicalRotationRepresentative_mem (rotation : Rotation K) :
    presentation.canonicalRotationRepresentative rotation ∈
      presentation.nonNullProjectiveRepresentatives := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.canonicalize_mem
    (RotationProportion.ofRotation rotation presentation.twoNonzero)

theorem canonicalRotationRepresentative_rotation (rotation : Rotation K) :
    (presentation.canonicalRotationRepresentative rotation).rotation =
      rotation := by
  letI : DecidableEq K := presentation.eqDecidable
  apply rotation_eq_of_matrix_eq
  let source := RotationProportion.ofRotation rotation presentation.twoNonzero
  change (presentation.canonicalize source).representative.rotationMatrix =
    rotation.matrix
  calc
    (presentation.canonicalize source).representative.rotationMatrix =
        source.rotationMatrix :=
      (NonNullProportion.rotationMatrix_respects_equivalent
        (presentation.canonicalize source).equivalent).symm
    _ = rotation.matrix :=
      RotationProportion.ofRotation_rotationMatrix rotation
        presentation.twoNonzero

/-- The projective rotation theorem as an explicit finite-list bijection on
the canonical representatives used for counting. -/
def projectiveRotationBijection : FiniteListBijection
    presentation.nonNullProjectiveRepresentatives presentation.rotations where
  forward := NonNullProportion.rotation
  backward := presentation.canonicalRotationRepresentative
  forward_mem := by
    intro proportion member
    unfold rotations
    exact QuotientFreeList.mem_map.mpr ⟨proportion, member, rfl⟩
  backward_mem := fun rotation _ =>
    presentation.canonicalRotationRepresentative_mem rotation
  backward_forward := by
    intro proportion member
    apply presentation.rotation_injective_on_canonical
      (presentation.canonicalRotationRepresentative_mem proportion.rotation)
      member
    exact presentation.canonicalRotationRepresentative_rotation
      proportion.rotation
  forward_backward := by
    intro rotation _
    exact presentation.canonicalRotationRepresentative_rotation rotation

/-- The projective half-spread fiber, evaluated by the homogeneous closed
formula `Q(v)/N(x,v)`. -/
def halfSpreadFiber (value : K) : List (NonNullProportion K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.nonNullProjectiveRepresentatives.filter fun proportion =>
    proportion.vector.quadrance / proportion.toProportion.norm = value

/-- The affine quadric `Q(v) = value`, retained in normalized projective
coordinates so every point also caches the non-null norm certificate needed
by the rotation map.  This is constructed independently of half spread by
filtering the displayed four-chart carrier. -/
def affineQuadricRawRepresentatives (value : K) : List (Proportion K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.projectiveRepresentatives.filter fun raw =>
    raw.scalar = 1 ∧ raw.vector.quadrance = value

def affineQuadricRepresentatives (value : K) :
    List (NonNullProportion K) :=
  (presentation.affineQuadricRawRepresentatives value).filterMap
    presentation.certifyNonNull

/-- Canonical projective axis representatives: the displayed projective
plane at infinity, before removing its null conic. -/
def projectiveAxisRawRepresentatives : List (Proportion K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.projectiveRepresentatives.filter fun raw =>
    raw.scalar = 0

/-- The non-null projective-axis quadric complement parametrizing half turns.
The construction is independent of the half-spread fiber predicate. -/
def projectiveNonNullAxisRepresentatives :
    List (NonNullProportion K) :=
  presentation.projectiveAxisRawRepresentatives.filterMap
    presentation.certifyNonNull

theorem halfSpreadFiber_nodup (value : K) :
    (presentation.halfSpreadFiber value).Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold halfSpreadFiber
  exact List.Pairwise.filter _
    presentation.nonNullProjectiveRepresentatives_nodup

theorem affineQuadricRawRepresentatives_nodup (value : K) :
    (presentation.affineQuadricRawRepresentatives value).Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold affineQuadricRawRepresentatives
  exact List.Pairwise.filter _ presentation.projectiveRepresentatives_nodup

theorem affineQuadricRepresentatives_nodup (value : K) :
    (presentation.affineQuadricRepresentatives value).Nodup := by
  unfold affineQuadricRepresentatives
  exact certifyNonNull_filterMap_nodup (presentation := presentation)
    (presentation.affineQuadricRawRepresentatives value)
    (presentation.affineQuadricRawRepresentatives_nodup value)

theorem projectiveAxisRawRepresentatives_nodup :
    presentation.projectiveAxisRawRepresentatives.Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold projectiveAxisRawRepresentatives
  exact List.Pairwise.filter _ presentation.projectiveRepresentatives_nodup

theorem projectiveNonNullAxisRepresentatives_nodup :
    presentation.projectiveNonNullAxisRepresentatives.Nodup := by
  unfold projectiveNonNullAxisRepresentatives
  exact certifyNonNull_filterMap_nodup (presentation := presentation)
    presentation.projectiveAxisRawRepresentatives
    presentation.projectiveAxisRawRepresentatives_nodup

theorem mem_affineQuadricRepresentatives_iff
    (value : K) (proportion : NonNullProportion K) :
    proportion ∈ presentation.affineQuadricRepresentatives value ↔
      proportion ∈ presentation.nonNullProjectiveRepresentatives ∧
        proportion.scalar = 1 ∧
          proportion.vector.quadrance = value := by
  letI : DecidableEq K := presentation.eqDecidable
  constructor
  · intro member
    unfold affineQuadricRepresentatives at member
    rcases QuotientFreeList.mem_filterMap.mp member with
      ⟨raw, rawMember, certified⟩
    have filtered := List.mem_filter.mp rawMember
    have rawEqual :=
      presentation.certifyNonNull_eq_some_toProportion certified
    constructor
    · unfold nonNullProjectiveRepresentatives
      exact QuotientFreeList.mem_filterMap.mpr
        ⟨raw, filtered.1, certified⟩
    · rw [rawEqual]
      exact of_decide_eq_true filtered.2
  · rintro ⟨projectiveMember, scalarOne, quadranceValue⟩
    unfold affineQuadricRepresentatives
    apply QuotientFreeList.mem_filterMap.mpr
    refine ⟨proportion.toProportion, ?_,
      presentation.certifyNonNull_self proportion⟩
    apply List.mem_filter.mpr
    exact ⟨presentation.raw_mem_of_nonNull_mem projectiveMember,
      decide_eq_true ⟨scalarOne, quadranceValue⟩⟩

theorem mem_projectiveNonNullAxisRepresentatives_iff
    (proportion : NonNullProportion K) :
    proportion ∈ presentation.projectiveNonNullAxisRepresentatives ↔
      proportion ∈ presentation.nonNullProjectiveRepresentatives ∧
        proportion.scalar = 0 := by
  letI : DecidableEq K := presentation.eqDecidable
  constructor
  · intro member
    unfold projectiveNonNullAxisRepresentatives at member
    rcases QuotientFreeList.mem_filterMap.mp member with
      ⟨raw, rawMember, certified⟩
    have filtered := List.mem_filter.mp rawMember
    have rawEqual :=
      presentation.certifyNonNull_eq_some_toProportion certified
    constructor
    · unfold nonNullProjectiveRepresentatives
      exact QuotientFreeList.mem_filterMap.mpr
        ⟨raw, filtered.1, certified⟩
    · rw [rawEqual]
      exact of_decide_eq_true filtered.2
  · rintro ⟨projectiveMember, scalarZero⟩
    unfold projectiveNonNullAxisRepresentatives
    apply QuotientFreeList.mem_filterMap.mpr
    refine ⟨proportion.toProportion, ?_,
      presentation.certifyNonNull_self proportion⟩
    apply List.mem_filter.mpr
    exact ⟨presentation.raw_mem_of_nonNull_mem projectiveMember,
      decide_eq_true scalarZero⟩

/-- Canonical representatives whose four-square norm has square class one.
This is the executable kernel list for the map `chi`. -/
def quadranceClassKernel : List (NonNullProportion K) := by
  exact presentation.nonNullProjectiveRepresentatives.filter fun proportion =>
    presentation.isSquare proportion.toProportion.norm

/-- The other quadrance-class fiber in the canonical projective carrier. -/
def quadranceClassNontrivialFiber : List (NonNullProportion K) :=
  presentation.nonNullProjectiveRepresentatives.filter fun proportion =>
    !presentation.isSquare proportion.toProportion.norm

/-- On the canonical finite rotation carrier, the executable square-norm
filter is exactly the unit-quaternion kernel predicate. -/
theorem mem_quadranceClassKernel_iff_hasUnitRepresentative
    (proportion : NonNullProportion K) :
    proportion ∈ presentation.quadranceClassKernel ↔
      proportion ∈ presentation.nonNullProjectiveRepresentatives ∧
        proportion.HasUnitRepresentative := by
  letI : DecidableEq K := presentation.eqDecidable
  constructor
  · intro member
    have filtered := List.mem_filter.mp member
    have squareMember : proportion.toProportion.norm ∈
        presentation.squareValues := by
      unfold isSquare at filtered
      exact of_decide_eq_true filtered.2
    let root := presentation.squareRoot proportion.toProportion.norm
    have rootSquare : root ^ 2 = proportion.toProportion.norm :=
      presentation.squareRoot_spec proportion.toProportion.norm squareMember
    have rootNonzero : root ≠ 0 := by
      intro rootZero
      apply proportion.normNonzero
      calc
        proportion.toProportion.norm = root ^ 2 := rootSquare.symm
        _ = 0 := by rw [rootZero]; ring1
    refine ⟨filtered.1, root⁻¹,
      RFAP.ExplicitField.inv_ne_zero rootNonzero, ?_⟩
    rw [Proportion.norm_scale]
    have cancel := RFAP.ExplicitField.mul_inv_cancel root rootNonzero
    calc
      root⁻¹ ^ 2 * proportion.toProportion.norm =
          root⁻¹ ^ 2 * root ^ 2 := by rw [rootSquare]
      _ = (root * root⁻¹) ^ 2 := by ring1
      _ = 1 := by rw [cancel]; ring1
  · rintro ⟨carrierMember, factor, factorNonzero, unitNorm⟩
    unfold quadranceClassKernel
    rw [List.mem_filter]
    constructor
    · exact carrierMember
    · unfold isSquare
      apply decide_eq_true
      apply (presentation.mem_squareValues_iff_hasSquareRoot _).2
      refine ⟨factor⁻¹, ?_⟩
      rw [Proportion.norm_scale] at unitNorm
      have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
      calc
        factor⁻¹ ^ 2 = factor⁻¹ ^ 2 * 1 := by ring1
        _ = factor⁻¹ ^ 2 *
            (factor ^ 2 * proportion.toProportion.norm) := by rw [unitNorm]
        _ = (factor * factor⁻¹) ^ 2 *
            proportion.toProportion.norm := by ring1
        _ = proportion.toProportion.norm := by rw [cancel]; ring1

/-- The trivial nonzero square class. -/
def trivialSquareClass : SquareClassRepresentative K where
  value := 1
  nonzero := one_ne_zero presentation

/-- The deterministic representative of the second nonzero square class. -/
def nontrivialSquareClass : SquareClassRepresentative K where
  value := presentation.chosenNonsquare.value
  nonzero := nonsquare_ne_zero presentation.chosenNonsquare.noRoot

/-- Every nonzero square-class representative belongs constructively to one
of the two classes.  Both branches retain the explicit square factor. -/
inductive NonzeroSquareClassClassification
    (target : SquareClassRepresentative K) where
  | trivial (root : K) (rootSquare : root ^ 2 = target.value)
      (equivalent : presentation.trivialSquareClass.Equivalent target)
  | nontrivial (targetNoRoot : ∀ root : K, root ^ 2 ≠ target.value)
      (factor : K) (factorNonzero : factor ≠ 0)
      (equivalent : presentation.nontrivialSquareClass.Equivalent target)

/-- Compute which of the two nonzero square classes contains `target`. -/
def classifyNonzeroSquareClass (target : SquareClassRepresentative K) :
    presentation.NonzeroSquareClassClassification target := by
  cases presentation.classifySquare target.value with
  | square root rootSquare =>
      refine NonzeroSquareClassClassification.trivial root rootSquare ?_
      refine ⟨root, ?_, ?_⟩
      · intro rootZero
        apply target.nonzero
        calc
          target.value = root ^ 2 := rootSquare.symm
          _ = 0 := by rw [rootZero]; ring1
      · change target.value = root ^ 2 * (1 : K)
        rw [rootSquare]
        ring1
  | nonsquare targetNoRoot =>
      let chosen := presentation.chosenNonsquare
      let witness := presentation.nonsquareMulNonsquareSquareWitness
        chosen.value target.value chosen.noRoot targetNoRoot
      have chosenNonzero : chosen.value ≠ 0 :=
        nonsquare_ne_zero chosen.noRoot
      have witnessRootNonzero : witness.root ≠ 0 := by
        intro rootZero
        have productZero : chosen.value * target.value = 0 := by
          calc
            chosen.value * target.value = witness.root ^ 2 :=
              witness.equation.symm
            _ = 0 := by rw [rootZero]; ring1
        exact (RFAP.ExplicitField.mul_ne_zero chosenNonzero target.nonzero)
          productZero
      let factor := witness.root / chosen.value
      have factorNonzero : factor ≠ 0 :=
        RFAP.ExplicitField.div_ne_zero witnessRootNonzero chosenNonzero
      refine NonzeroSquareClassClassification.nontrivial targetNoRoot factor
        factorNonzero ?_
      refine ⟨factor, factorNonzero, ?_⟩
      change target.value = factor ^ 2 * chosen.value
      have chosenCancel := RFAP.ExplicitField.mul_inv_cancel chosen.value
        chosenNonzero
      unfold factor
      rw [RFAP.ExplicitField.div_eq_mul_inv]
      symm
      calc
        (witness.root * chosen.value⁻¹) ^ 2 * chosen.value =
            witness.root ^ 2 * chosen.value⁻¹ ^ 2 * chosen.value := by ring1
        _ =
            (chosen.value * target.value) * chosen.value⁻¹ ^ 2 *
              chosen.value := by rw [witness.equation]
        _ = target.value * (chosen.value * chosen.value⁻¹) ^ 2 := by ring1
        _ = target.value := by rw [chosenCancel]; ring1

/-- Two squares representing a nonzero scalar supply a four-square
representation with two cached zero coordinates. -/
def finiteQuadranceClassRepresentation
    (target : SquareClassRepresentative K) :
    FourSquareRepresentation target.value := by
  let pair := presentation.twoSquareRepresentation target.value
  exact
    { scalar := pair.first
      t := pair.second
      r := 0
      s := 0
      equation := by
        rw [show pair.first ^ 2 + pair.second ^ 2 = target.value from
          pair.equation]
        ring1 }

/-- Executable finite-field preimage of an arbitrary square-class
representative. -/
def quadranceClassPreimageProportion
    (target : SquareClassRepresentative K) : NonNullProportion K :=
  (presentation.finiteQuadranceClassRepresentation target).proportion target

theorem quadranceClassPreimageProportion_norm
    (target : SquareClassRepresentative K) :
    (presentation.quadranceClassPreimageProportion target).toProportion.norm =
      target.value := by
  exact FourSquareRepresentation.realizes_quadranceClass target
    (presentation.finiteQuadranceClassRepresentation target)

def quadranceClassPreimageRotation
    (target : SquareClassRepresentative K) : Rotation K :=
  (presentation.quadranceClassPreimageProportion target).rotation

/-- The finite-field quadrance-class map is onto, with a computed preimage
for every displayed nonzero representative. -/
theorem quadranceClassPreimage_realizes
    (target : SquareClassRepresentative K) :
    letI : DecidableEq K := presentation.eqDecidable
    (RotationQuadranceClass.ofRotation
      (presentation.quadranceClassPreimageRotation target)
      presentation.twoNonzero).Equivalent target := by
  letI : DecidableEq K := presentation.eqDecidable
  let source := presentation.quadranceClassPreimageProportion target
  let canonical := RotationProportion.ofRotation source.rotation
    presentation.twoNonzero
  have matrixEqual : canonical.rotationMatrix = source.rotationMatrix := by
    calc
      canonical.rotationMatrix = source.rotation.matrix :=
        RotationProportion.ofRotation_rotationMatrix source.rotation
          presentation.twoNonzero
      _ = source.rotationMatrix := rfl
  have equivalent := NonNullProportion.equivalent_of_rotationMatrix_eq
    canonical source presentation.twoNonzero matrixEqual
  have classEquivalent :=
    NonNullProportion.quadranceClass_respects_equivalent equivalent
  have sourceClassEqual : source.quadranceClass = target := by
    apply SquareClassRepresentative.ext
    exact FourSquareRepresentation.realizes_quadranceClass target
      (presentation.finiteQuadranceClassRepresentation target)
  change canonical.quadranceClass.Equivalent target
  rw [← sourceClassEqual]
  exact classEquivalent

/-- A fixed non-null proportion whose norm represents the nontrivial square
class. -/
def quadranceClassSwitcher : NonNullProportion K :=
  presentation.quadranceClassPreimageProportion
    presentation.nontrivialSquareClass

theorem quadranceClassSwitcher_norm :
    presentation.quadranceClassSwitcher.toProportion.norm =
      presentation.chosenNonsquare.value := by
  exact presentation.quadranceClassPreimageProportion_norm
    presentation.nontrivialSquareClass

/-- Multiply by the fixed nonsquare-norm proportion and normalize back to the
canonical four-chart carrier. -/
def switchQuadranceClassForward (source : NonNullProportion K) :
    NonNullProportion K :=
  (presentation.canonicalize
    (NonNullProportion.mul presentation.quadranceClassSwitcher source)).representative

/-- The inverse switch uses the displayed quaternion conjugate. -/
def switchQuadranceClassBackward (source : NonNullProportion K) :
    NonNullProportion K :=
  (presentation.canonicalize
    (NonNullProportion.mul
      (NonNullProportion.conjugate presentation.quadranceClassSwitcher)
      source)).representative

private theorem canonical_nonNull_eq_of_equivalent
    {left right : NonNullProportion K}
    (leftMember : left ∈ presentation.nonNullProjectiveRepresentatives)
    (rightMember : right ∈ presentation.nonNullProjectiveRepresentatives)
    (equivalent : left.Equivalent right) : left = right := by
  have rawEqual := presentation.projective_eq_of_equivalent
    (presentation.raw_mem_of_nonNull_mem leftMember)
    (presentation.raw_mem_of_nonNull_mem rightMember) equivalent
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar rawEqual
  · exact congrArg Proportion.vector rawEqual

private theorem canonicalize_norm_hasSquareRoot
    (source : NonNullProportion K) (root : K)
    (rootSquare : root ^ 2 = source.toProportion.norm) :
    HasSquareRoot
      (presentation.canonicalize source).representative.toProportion.norm := by
  rcases (presentation.canonicalize source).equivalent with
    ⟨factor, _, representativeValue⟩
  refine ⟨factor * root, ?_⟩
  calc
    (factor * root) ^ 2 = factor ^ 2 * source.toProportion.norm := by
      rw [← rootSquare]
      ring1
    _ = (Proportion.scale factor source.toProportion).norm :=
      (Proportion.norm_scale factor source.toProportion).symm
    _ = (presentation.canonicalize source).representative.toProportion.norm :=
      congrArg Proportion.norm representativeValue.symm

private theorem canonicalize_norm_noRoot
    (source : NonNullProportion K)
    (sourceNoRoot : ∀ root : K, root ^ 2 ≠ source.toProportion.norm) :
    ∀ root : K,
      root ^ 2 ≠
        (presentation.canonicalize source).representative.toProportion.norm := by
  rcases (presentation.canonicalize source).equivalent with
    ⟨factor, factorNonzero, representativeValue⟩
  have factorSquareNonzero : factor ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero factorNonzero factorNonzero
  have scaledNoRoot := square_mul_nonsquare_noRoot (factor ^ 2) factor
    source.toProportion.norm factorSquareNonzero rfl sourceNoRoot
  intro root rootSquare
  apply scaledNoRoot root
  calc
    root ^ 2 =
        (presentation.canonicalize source).representative.toProportion.norm :=
      rootSquare
    _ = (Proportion.scale factor source.toProportion).norm :=
      congrArg Proportion.norm representativeValue
    _ = factor ^ 2 * source.toProportion.norm :=
      Proportion.norm_scale factor source.toProportion

theorem switchQuadranceClassForward_mem
    {source : NonNullProportion K}
    (member : source ∈ presentation.quadranceClassKernel) :
    presentation.switchQuadranceClassForward source ∈
      presentation.quadranceClassNontrivialFiber := by
  letI : DecidableEq K := presentation.eqDecidable
  have sourceSquareAccepted := (List.mem_filter.mp member).2
  unfold isSquare at sourceSquareAccepted
  have sourceSquareMember := of_decide_eq_true sourceSquareAccepted
  let sourceRoot := presentation.squareRoot source.toProportion.norm
  have sourceRootSquare : sourceRoot ^ 2 = source.toProportion.norm :=
    presentation.squareRoot_spec source.toProportion.norm sourceSquareMember
  let switcher := presentation.quadranceClassSwitcher
  let product := NonNullProportion.mul switcher source
  have productNoRoot : ∀ root : K,
      root ^ 2 ≠ product.toProportion.norm := by
    have baseNoRoot := square_mul_nonsquare_noRoot
      source.toProportion.norm sourceRoot
      presentation.chosenNonsquare.value source.normNonzero sourceRootSquare
      presentation.chosenNonsquare.noRoot
    intro root rootSquare
    apply baseNoRoot root
    calc
      root ^ 2 = product.toProportion.norm := rootSquare
      _ = switcher.toProportion.norm * source.toProportion.norm :=
        NonNullProportion.mul_norm switcher source
      _ = presentation.chosenNonsquare.value *
          source.toProportion.norm := by
        rw [presentation.quadranceClassSwitcher_norm]
      _ = source.toProportion.norm *
          presentation.chosenNonsquare.value := by ring1
  have resultNoRoot := presentation.canonicalize_norm_noRoot product
    productNoRoot
  unfold quadranceClassNontrivialFiber
  rw [List.mem_filter]
  constructor
  · exact presentation.canonicalize_mem product
  · apply Eq.mpr (Bool.not_eq_true' _)
    unfold isSquare
    apply decide_eq_false
    intro squareMember
    exact resultNoRoot (presentation.squareRoot
      (presentation.canonicalize product).representative.toProportion.norm)
      (presentation.squareRoot_spec _ squareMember)

theorem switchQuadranceClassBackward_mem
    {source : NonNullProportion K}
    (member : source ∈ presentation.quadranceClassNontrivialFiber) :
    presentation.switchQuadranceClassBackward source ∈
      presentation.quadranceClassKernel := by
  letI : DecidableEq K := presentation.eqDecidable
  have sourceRejected := (List.mem_filter.mp member).2
  have sourceSquareFalse := Eq.mp (Bool.not_eq_true' _) sourceRejected
  unfold isSquare at sourceSquareFalse
  have sourceNotSquare := decide_eq_false_iff_not.mp sourceSquareFalse
  have sourceNoRoot : ∀ root : K,
      root ^ 2 ≠ source.toProportion.norm := by
    intro root rootSquare
    exact sourceNotSquare
      (rootSquare ▸ presentation.squareValuesComplete root)
  let switcher := presentation.quadranceClassSwitcher
  let conjugate := NonNullProportion.conjugate switcher
  let product := NonNullProportion.mul conjugate source
  have conjugateNorm : conjugate.toProportion.norm =
      presentation.chosenNonsquare.value := by
    calc
      conjugate.toProportion.norm = switcher.toProportion.norm :=
        Proportion.norm_conjugate switcher.toProportion
      _ = presentation.chosenNonsquare.value :=
        presentation.quadranceClassSwitcher_norm
  let witness := presentation.nonsquareMulNonsquareSquareWitness
    presentation.chosenNonsquare.value source.toProportion.norm
    presentation.chosenNonsquare.noRoot sourceNoRoot
  have productRootSquare : witness.root ^ 2 = product.toProportion.norm := by
    calc
      witness.root ^ 2 = presentation.chosenNonsquare.value *
          source.toProportion.norm := witness.equation
      _ = conjugate.toProportion.norm * source.toProportion.norm := by
        rw [conjugateNorm]
      _ = product.toProportion.norm :=
        (NonNullProportion.mul_norm conjugate source).symm
  rcases presentation.canonicalize_norm_hasSquareRoot product witness.root
      productRootSquare with ⟨resultRoot, resultRootSquare⟩
  unfold quadranceClassKernel
  rw [List.mem_filter]
  constructor
  · exact presentation.canonicalize_mem product
  · unfold isSquare
    apply decide_eq_true
    exact (presentation.mem_squareValues_iff_hasSquareRoot _).2
      ⟨resultRoot, resultRootSquare⟩

theorem switchQuadranceClassBackward_forward
    {source : NonNullProportion K}
    (member : source ∈ presentation.quadranceClassKernel) :
    presentation.switchQuadranceClassBackward
        (presentation.switchQuadranceClassForward source) = source := by
  let switcher := presentation.quadranceClassSwitcher
  let forwardProduct := NonNullProportion.mul switcher source
  let forwardRepresentative :=
    (presentation.canonicalize forwardProduct).representative
  let backwardProduct := NonNullProportion.mul
    (NonNullProportion.conjugate switcher) forwardRepresentative
  have replaceForward :
      (NonNullProportion.mul (NonNullProportion.conjugate switcher)
          forwardProduct).Equivalent backwardProduct := by
    exact NonNullProportion.mul_respects_equivalent
      (NonNullProportion.equivalent_refl _)
      (presentation.canonicalize forwardProduct).equivalent
  have cancel :
      (NonNullProportion.mul (NonNullProportion.conjugate switcher)
          forwardProduct).Equivalent source := by
    change (NonNullProportion.mul (NonNullProportion.conjugate switcher)
      (NonNullProportion.mul switcher source)).Equivalent source
    rw [← NonNullProportion.mul_assoc]
    have lifted := NonNullProportion.mul_respects_equivalent
      (NonNullProportion.conjugate_mul_equivalent_identity switcher)
      (NonNullProportion.equivalent_refl source)
    rw [NonNullProportion.identity_mul] at lifted
    exact lifted
  have backwardProductEquivalent : backwardProduct.Equivalent source :=
    NonNullProportion.equivalent_trans
      (NonNullProportion.equivalent_symm replaceForward) cancel
  unfold switchQuadranceClassBackward switchQuadranceClassForward
  apply presentation.canonical_nonNull_eq_of_equivalent
    (presentation.canonicalize_mem backwardProduct)
    (List.mem_filter.mp member).1
  exact NonNullProportion.equivalent_trans
    (NonNullProportion.equivalent_symm
      (presentation.canonicalize backwardProduct).equivalent)
    backwardProductEquivalent

theorem switchQuadranceClassForward_backward
    {source : NonNullProportion K}
    (member : source ∈ presentation.quadranceClassNontrivialFiber) :
    presentation.switchQuadranceClassForward
        (presentation.switchQuadranceClassBackward source) = source := by
  let switcher := presentation.quadranceClassSwitcher
  let backwardProduct := NonNullProportion.mul
    (NonNullProportion.conjugate switcher) source
  let backwardRepresentative :=
    (presentation.canonicalize backwardProduct).representative
  let forwardProduct :=
    NonNullProportion.mul switcher backwardRepresentative
  have replaceBackward :
      (NonNullProportion.mul switcher backwardProduct).Equivalent
        forwardProduct := by
    exact NonNullProportion.mul_respects_equivalent
      (NonNullProportion.equivalent_refl _)
      (presentation.canonicalize backwardProduct).equivalent
  have cancel :
      (NonNullProportion.mul switcher backwardProduct).Equivalent source := by
    change (NonNullProportion.mul switcher
      (NonNullProportion.mul (NonNullProportion.conjugate switcher)
        source)).Equivalent source
    rw [← NonNullProportion.mul_assoc]
    have lifted := NonNullProportion.mul_respects_equivalent
      (NonNullProportion.mul_conjugate_equivalent_identity switcher)
      (NonNullProportion.equivalent_refl source)
    rw [NonNullProportion.identity_mul] at lifted
    exact lifted
  have forwardProductEquivalent : forwardProduct.Equivalent source :=
    NonNullProportion.equivalent_trans
      (NonNullProportion.equivalent_symm replaceBackward) cancel
  unfold switchQuadranceClassForward switchQuadranceClassBackward
  apply presentation.canonical_nonNull_eq_of_equivalent
    (presentation.canonicalize_mem forwardProduct)
    (List.mem_filter.mp member).1
  exact NonNullProportion.equivalent_trans
    (NonNullProportion.equivalent_symm
      (presentation.canonicalize forwardProduct).equivalent)
    forwardProductEquivalent

/-- Multiplication by one fixed nonsquare-norm proportion exchanges the two
quadrance-class fibers. -/
def quadranceClassFiberBijection : FiniteListBijection
    presentation.quadranceClassKernel
    presentation.quadranceClassNontrivialFiber where
  forward := presentation.switchQuadranceClassForward
  backward := presentation.switchQuadranceClassBackward
  forward_mem := fun _ member =>
    presentation.switchQuadranceClassForward_mem member
  backward_mem := fun _ member =>
    presentation.switchQuadranceClassBackward_mem member
  backward_forward := fun _ member =>
    presentation.switchQuadranceClassBackward_forward member
  forward_backward := fun _ member =>
    presentation.switchQuadranceClassForward_backward member

theorem quadranceClassKernel_length_eq_nontrivialFiber_length :
    presentation.quadranceClassKernel.length =
      presentation.quadranceClassNontrivialFiber.length := by
  apply FiniteListBijection.length_eq
    presentation.quadranceClassFiberBijection
  · exact presentation.nonNullProjectiveRepresentatives_nodup.filter _
  · exact presentation.nonNullProjectiveRepresentatives_nodup.filter _

/-- The affine cap-domain quadric excluded by `1 + Q(v) = 0`. -/
def excludedAnchorQuadric : List (Vector K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.vectors.filter fun vector => vector.quadrance = -1

/-- The affine null cone, including its vertex. -/
def nullVectors : List (Vector K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.vectors.filter fun vector => vector.quadrance = 0

/-- Nonzero null anchors.  Their caps are precisely the nonidentity
half-spread-zero (parabolic) rotations. -/
def nonzeroNullVectors : List (Vector K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.vectors.filter fun vector =>
    vector.quadrance = 0 && decide (vector ≠ Vector.zero)

theorem mem_nonzeroNullVectors_iff (vector : Vector K) :
    vector ∈ presentation.nonzeroNullVectors ↔
      vector ∈ presentation.vectors ∧
        vector.quadrance = 0 ∧ vector ≠ Vector.zero := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold nonzeroNullVectors
  rw [List.mem_filter]
  simp only [Bool.and_eq_true, decide_eq_true_eq]

/-- Canonical first-nonzero-coordinate representatives of the projective null
directions.  The first chart is `(1,r,s)` with `r²+s²=-1`; the second is
`(0,1,s)` with `s²=-1`.  No third chart can be null. -/
def nullDirectionRepresentatives : List (Vector K) :=
  ((presentation.twoSquareFiber (-1)).map fun pair =>
      ⟨1, pair.first, pair.second⟩) ++
    (presentation.squareRootFiber (-1)).map fun root => ⟨0, 1, root⟩

theorem nullDirectionRepresentatives_nodup :
    presentation.nullDirectionRepresentatives.Nodup := by
  unfold nullDirectionRepresentatives
  apply QuotientFreeList.nodup_append
  · apply QuotientFreeList.nodup_map_of_injective
    · intro left right equal
      apply ScalarPair.ext
      · exact congrArg Vector.r equal
      · exact congrArg Vector.s equal
    · exact presentation.twoSquareFiber_nodup (-1)
  · apply QuotientFreeList.nodup_map_of_injective
    · intro left right equal
      exact congrArg Vector.s equal
    · exact presentation.squareRootFiber_nodup (-1)
  · intro left leftMember right rightMember equal
    rcases QuotientFreeList.mem_map.mp leftMember with
      ⟨pair, _, leftEqual⟩
    rcases QuotientFreeList.mem_map.mp rightMember with
      ⟨root, _, rightEqual⟩
    apply one_ne_zero presentation
    calc
      (1 : K) = left.t := congrArg Vector.t leftEqual
      _ = right.t := congrArg Vector.t equal
      _ = 0 := (congrArg Vector.t rightEqual).symm

theorem nullDirectionRepresentative_null {direction : Vector K}
    (member : direction ∈ presentation.nullDirectionRepresentatives) :
    direction.quadrance = 0 := by
  unfold nullDirectionRepresentatives at member
  rcases List.mem_append.mp member with firstChart | secondChart
  · rcases QuotientFreeList.mem_map.mp firstChart with
      ⟨pair, pairMember, equal⟩
    have pairQuadrance :=
      (presentation.mem_twoSquareFiber_iff (-1) pair).1 pairMember
    rw [← equal]
    unfold Vector.quadrance Vector.dot ScalarPair.quadrance at *
    change (1 : K) * 1 + pair.first * pair.first +
      pair.second * pair.second = 0
    have pairQuadranceMul :
        pair.first * pair.first + pair.second * pair.second = -1 := by
      simpa only [pow_two] using pairQuadrance
    calc
      (1 : K) * 1 + pair.first * pair.first + pair.second * pair.second =
          1 + (pair.first * pair.first + pair.second * pair.second) := by ring1
      _ = 1 + (-1) := by rw [pairQuadranceMul]
      _ = 0 := by ring1
  · rcases QuotientFreeList.mem_map.mp secondChart with
      ⟨root, rootMember, equal⟩
    have rootSquare :=
      (presentation.mem_squareRootFiber_iff (-1) root).1 rootMember
    rw [← equal]
    unfold Vector.quadrance Vector.dot
    change (0 : K) * 0 + 1 * 1 + root * root = 0
    have rootSquareMul : root * root = -1 := by
      simpa only [pow_two] using rootSquare
    rw [rootSquareMul]
    ring1

theorem nullDirectionRepresentative_nonzero {direction : Vector K}
    (member : direction ∈ presentation.nullDirectionRepresentatives) :
    direction ≠ Vector.zero := by
  unfold nullDirectionRepresentatives at member
  rcases List.mem_append.mp member with firstChart | secondChart
  · rcases QuotientFreeList.mem_map.mp firstChart with
      ⟨pair, _, equal⟩
    intro directionZero
    apply one_ne_zero presentation
    calc
      (1 : K) = direction.t := congrArg Vector.t equal
      _ = Vector.zero.t := congrArg Vector.t directionZero
      _ = 0 := rfl
  · rcases QuotientFreeList.mem_map.mp secondChart with
      ⟨root, _, equal⟩
    intro directionZero
    apply one_ne_zero presentation
    calc
      (1 : K) = direction.r := congrArg Vector.r equal
      _ = Vector.zero.r := congrArg Vector.r directionZero
      _ = 0 := rfl

theorem nullDirectionRepresentative_projectiveMember
    {direction : Vector K}
    (member : direction ∈ presentation.nullDirectionRepresentatives) :
    (⟨0, direction⟩ : Proportion K) ∈
      presentation.projectiveRepresentatives := by
  unfold nullDirectionRepresentatives at member
  rcases List.mem_append.mp member with firstChart | secondChart
  · rcases QuotientFreeList.mem_map.mp firstChart with
      ⟨pair, _, equal⟩
    rw [← equal]
    exact presentation.infinityTProportion_mem pair.first pair.second
  · rcases QuotientFreeList.mem_map.mp secondChart with
      ⟨root, _, equal⟩
    rw [← equal]
    exact presentation.infinityRProportion_mem root

/-- Cached normalization of one nonzero null anchor to its canonical
projective direction and its nonzero affine parameter. -/
structure NullDirectionNormalization (source : Vector K) where
  representative : Vector K
  representativeMember : representative ∈
    presentation.nullDirectionRepresentatives
  parameter : K
  parameterNonzero : parameter ≠ 0
  source_eq_scale : source = Vector.scale parameter representative

/-- Normalize a nonzero null vector by its first nonzero coordinate.  The
impossible third chart is rejected directly from the null equation. -/
def normalizeNullDirection (source : Vector K)
    (sourceNull : source.quadrance = 0)
    (sourceNonzero : source ≠ Vector.zero) :
    presentation.NullDirectionNormalization source := by
  letI : DecidableEq K := presentation.eqDecidable
  if tNonzero : source.t ≠ 0 then
    let inverse := source.t⁻¹
    let pair : ScalarPair K :=
      ⟨inverse * source.r, inverse * source.s⟩
    let representative : Vector K := ⟨1, pair.first, pair.second⟩
    have tCancel := RFAP.ExplicitField.mul_inv_cancel source.t tNonzero
    have residual : source.r ^ 2 + source.s ^ 2 = -(source.t ^ 2) := by
      calc
        source.r ^ 2 + source.s ^ 2 =
            source.quadrance - source.t ^ 2 := by
          unfold Vector.quadrance Vector.dot
          ring1
        _ = -(source.t ^ 2) := by rw [sourceNull]; ring1
    have pairQuadrance : pair.quadrance = -1 := by
      unfold pair ScalarPair.quadrance inverse
      calc
        (source.t⁻¹ * source.r) ^ 2 +
            (source.t⁻¹ * source.s) ^ 2 =
          source.t⁻¹ ^ 2 * (source.r ^ 2 + source.s ^ 2) := by ring1
        _ = source.t⁻¹ ^ 2 * (-(source.t ^ 2)) := by rw [residual]
        _ = -((source.t * source.t⁻¹) ^ 2) := by ring1
        _ = -1 := by rw [tCancel]; ring1
    have pairMember : pair ∈ presentation.twoSquareFiber (-1) :=
      (presentation.mem_twoSquareFiber_iff (-1) pair).2 pairQuadrance
    refine
      { representative := representative
        representativeMember := ?_
        parameter := source.t
        parameterNonzero := tNonzero
        source_eq_scale := ?_ }
    · unfold nullDirectionRepresentatives
      apply List.mem_append.mpr
      left
      exact QuotientFreeList.mem_map.mpr ⟨pair, pairMember, rfl⟩
    · apply Vector.ext
      · change source.t = source.t * 1
        ring1
      · change source.r = source.t * (source.t⁻¹ * source.r)
        calc
          source.r = 1 * source.r := by ring1
          _ = (source.t * source.t⁻¹) * source.r := by rw [tCancel]
          _ = source.t * (source.t⁻¹ * source.r) := by ring1
      · change source.s = source.t * (source.t⁻¹ * source.s)
        calc
          source.s = 1 * source.s := by ring1
          _ = (source.t * source.t⁻¹) * source.s := by rw [tCancel]
          _ = source.t * (source.t⁻¹ * source.s) := by ring1
  else if rNonzero : source.r ≠ 0 then
    let inverse := source.r⁻¹
    let root := inverse * source.s
    let representative : Vector K := ⟨0, 1, root⟩
    have tZero := eq_zero_of_not_ne presentation.eqDecidable tNonzero
    have rCancel := RFAP.ExplicitField.mul_inv_cancel source.r rNonzero
    have residual : source.s ^ 2 = -(source.r ^ 2) := by
      calc
        source.s ^ 2 = source.quadrance - source.r ^ 2 := by
          unfold Vector.quadrance Vector.dot
          rw [tZero]
          ring1
        _ = -(source.r ^ 2) := by rw [sourceNull]; ring1
    have rootSquare : root ^ 2 = -1 := by
      unfold root inverse
      calc
        (source.r⁻¹ * source.s) ^ 2 =
            source.r⁻¹ ^ 2 * source.s ^ 2 := by ring1
        _ = source.r⁻¹ ^ 2 * (-(source.r ^ 2)) := by rw [residual]
        _ = -((source.r * source.r⁻¹) ^ 2) := by ring1
        _ = -1 := by rw [rCancel]; ring1
    have rootMember : root ∈ presentation.squareRootFiber (-1) :=
      (presentation.mem_squareRootFiber_iff (-1) root).2 rootSquare
    refine
      { representative := representative
        representativeMember := ?_
        parameter := source.r
        parameterNonzero := rNonzero
        source_eq_scale := ?_ }
    · unfold nullDirectionRepresentatives
      apply List.mem_append.mpr
      right
      exact QuotientFreeList.mem_map.mpr ⟨root, rootMember, rfl⟩
    · apply Vector.ext
      · change source.t = source.r * 0
        rw [tZero]
        ring1
      · change source.r = source.r * 1
        ring1
      · change source.s = source.r * (source.r⁻¹ * source.s)
        calc
          source.s = 1 * source.s := by ring1
          _ = (source.r * source.r⁻¹) * source.s := by rw [rCancel]
          _ = source.r * (source.r⁻¹ * source.s) := by ring1
  else
    have tZero := eq_zero_of_not_ne presentation.eqDecidable tNonzero
    have rZero := eq_zero_of_not_ne presentation.eqDecidable rNonzero
    have sSquareZero : source.s * source.s = 0 := by
      calc
        source.s * source.s = source.quadrance := by
          unfold Vector.quadrance Vector.dot
          rw [tZero, rZero]
          ring1
        _ = 0 := sourceNull
    have sZero : source.s = 0 := by
      cases presentation.eqDecidable source.s 0 with
      | isTrue equal => exact equal
      | isFalse sNonzero =>
          exact False.elim
            (RFAP.ExplicitField.mul_ne_zero sNonzero sNonzero sSquareZero)
    apply False.elim
    apply sourceNonzero
    apply Vector.ext
    · exact tZero
    · exact rZero
    · exact sZero

/-- Canonical null-direction representatives are unique under every displayed
nonzero projective scaling. -/
theorem nullDirectionRepresentative_eq_of_scaled
    {left right : Vector K}
    (leftMember : left ∈ presentation.nullDirectionRepresentatives)
    (rightMember : right ∈ presentation.nullDirectionRepresentatives)
    {factor : K} (factorNonzero : factor ≠ 0)
    (scaled : right = Vector.scale factor left) : left = right := by
  have equivalent :
      (⟨0, left⟩ : Proportion K).Equivalent (⟨0, right⟩ : Proportion K) := by
    refine ⟨factor, factorNonzero, ?_⟩
    apply Proportion.ext
    · unfold Proportion.scale
      ring1
    · exact scaled
  have equal := presentation.projective_eq_of_equivalent
    (presentation.nullDirectionRepresentative_projectiveMember leftMember)
    (presentation.nullDirectionRepresentative_projectiveMember rightMember)
    equivalent
  exact congrArg Proportion.vector equal

/-- Scaling one canonical null direction is injective in its affine
parameter. -/
theorem nullDirection_scale_injective {direction : Vector K}
    (member : direction ∈ presentation.nullDirectionRepresentatives) :
    Function.Injective (fun parameter : K => Vector.scale parameter direction) := by
  intro left right equal
  unfold nullDirectionRepresentatives at member
  rcases List.mem_append.mp member with firstChart | secondChart
  · rcases QuotientFreeList.mem_map.mp firstChart with
      ⟨pair, _, directionEqual⟩
    have coordinate := congrArg Vector.t equal
    rw [← directionEqual] at coordinate
    change left * 1 = right * 1 at coordinate
    simpa using coordinate
  · rcases QuotientFreeList.mem_map.mp secondChart with
      ⟨root, _, directionEqual⟩
    have coordinate := congrArg Vector.r equal
    rw [← directionEqual] at coordinate
    change left * 1 = right * 1 at coordinate
    simpa using coordinate

private theorem capDenominator_ne_zero_of_null_counting
    (presentation : FiniteOddFieldPresentation K)
    (vector : Vector K) (null : vector.quadrance = 0) :
    capDenominator vector ≠ 0 := by
  unfold capDenominator
  rw [null, add_zero]
  exact one_ne_zero presentation

/-- The canonical parabolic rotation attached to a displayed null anchor. -/
def parabolicRotation (presentation : FiniteOddFieldPresentation K)
    (vector : Vector K) (null : vector.quadrance = 0) :
    Rotation K :=
  capRotation vector
    (presentation.capDenominator_ne_zero_of_null_counting vector null)

theorem parabolicRotation_halfSpread (vector : Vector K)
    (null : vector.quadrance = 0) :
    halfSpread (presentation.parabolicRotation vector null) = 0 := by
  unfold parabolicRotation
  rw [halfSpread_cap vector _ presentation.twoNonzero, null,
    RFAP.ExplicitField.zero_div]

theorem parabolicRotation_characteristic (vector : Vector K)
    (null : vector.quadrance = 0) (X : K) :
    Matrix3.characteristicValue
        (presentation.parabolicRotation vector null).matrix X =
      (X - 1) ^ 3 := by
  unfold parabolicRotation capRotation
  rw [characteristicValue_cap vector _ X, null]
  have denominatorOne : capDenominator vector = 1 := by
    unfold capDenominator
    rw [null]
    ring1
  rw [denominatorOne]
  have oneInverse : (1 : K)⁻¹ = 1 := by
    have cancel := RFAP.ExplicitField.mul_inv_cancel (1 : K)
      (one_ne_zero presentation)
    simpa only [one_mul] using cancel
  simp only [RFAP.ExplicitField.div_eq_mul_inv, oneInverse]
  ring1

theorem parabolicRotation_fixedAnchor (vector : Vector K)
    (null : vector.quadrance = 0) :
    Matrix3.rowMul vector
        (presentation.parabolicRotation vector null).matrix = vector := by
  change Matrix3.rowMul vector
      (cap vector
        (presentation.capDenominator_ne_zero_of_null_counting vector null)) =
    vector
  exact rowMul_self_cap vector
    (presentation.capDenominator_ne_zero_of_null_counting vector null)

private theorem cap_zero_eq_identity_counting
    (presentation : FiniteOddFieldPresentation K) :
    cap (Vector.zero : Vector K)
        (presentation.capDenominator_ne_zero_of_null_counting
          Vector.zero Vector.quadrance_zero) = Matrix3.identity := by
  ext <;>
    unfold cap capDenominator Matrix3.add Matrix3.scale Matrix3.identity
      Matrix3.mul anchor Vector.zero Vector.quadrance Vector.dot <;>
    ring1

private theorem cap_eq_of_vector_eq_counting {left right : Vector K}
    (equal : left = right) (leftDefined : capDenominator left ≠ 0)
    (rightDefined : capDenominator right ≠ 0) :
    cap left leftDefined = cap right rightDefined := by
  subst right
  rfl

theorem parabolicRotation_nonidentity (vector : Vector K)
    (null : vector.quadrance = 0) (nonzero : vector ≠ Vector.zero) :
    (presentation.parabolicRotation vector null).matrix ≠ Matrix3.identity := by
  intro identity
  apply nonzero
  apply cap_injective presentation.twoNonzero vector Vector.zero
    (presentation.capDenominator_ne_zero_of_null_counting vector null)
    (presentation.capDenominator_ne_zero_of_null_counting
      Vector.zero Vector.quadrance_zero)
  calc
    cap vector
        (presentation.capDenominator_ne_zero_of_null_counting vector null) =
      Matrix3.identity := identity
    _ = cap Vector.zero
        (presentation.capDenominator_ne_zero_of_null_counting
          Vector.zero Vector.quadrance_zero) :=
      presentation.cap_zero_eq_identity_counting.symm

theorem parabolicRotation_injective
    {left right : Vector K} (leftNull : left.quadrance = 0)
    (rightNull : right.quadrance = 0)
    (equal : presentation.parabolicRotation left leftNull =
      presentation.parabolicRotation right rightNull) : left = right := by
  apply cap_injective presentation.twoNonzero left right
    (presentation.capDenominator_ne_zero_of_null_counting left leftNull)
    (presentation.capDenominator_ne_zero_of_null_counting right rightNull)
  exact congrArg Rotation.matrix equal

/-- The nonidentity parabolic rotations lying over one canonical projective
null direction, parametrized by every displayed nonzero scalar. -/
def parabolicRotationsOverDirection (direction : Vector K)
    (directionMember : direction ∈
      presentation.nullDirectionRepresentatives) : List (Rotation K) :=
  presentation.nonzeroScalars.map fun parameter =>
    presentation.parabolicRotation (Vector.scale parameter direction) (by
      rw [Vector.quadrance_scale,
        presentation.nullDirectionRepresentative_null directionMember]
      ring1)

theorem parabolicRotationsOverDirection_nodup (direction : Vector K)
    (directionMember : direction ∈
      presentation.nullDirectionRepresentatives) :
    (presentation.parabolicRotationsOverDirection direction
      directionMember).Nodup := by
  unfold parabolicRotationsOverDirection
  apply QuotientFreeList.nodup_map_of_injective
  · intro left right equal
    apply presentation.nullDirection_scale_injective directionMember
    apply presentation.parabolicRotation_injective
      (leftNull := by
        rw [Vector.quadrance_scale,
          presentation.nullDirectionRepresentative_null directionMember]
        ring1)
      (rightNull := by
        rw [Vector.quadrance_scale,
          presentation.nullDirectionRepresentative_null directionMember]
        ring1)
    exact equal
  · exact presentation.nonzeroScalars_nodup

theorem parabolicRotationsOverDirection_length (direction : Vector K)
    (directionMember : direction ∈
      presentation.nullDirectionRepresentatives) :
    (presentation.parabolicRotationsOverDirection direction
      directionMember).length = presentation.carrier.length - 1 := by
  unfold parabolicRotationsOverDirection
  rw [List.length_map, presentation.nonzeroScalars_length]

theorem parabolicRotationsOverDirection_mem_properties
    (direction : Vector K)
    (directionMember : direction ∈
      presentation.nullDirectionRepresentatives)
    {rotation : Rotation K}
    (member : rotation ∈ presentation.parabolicRotationsOverDirection
      direction directionMember) :
    halfSpread rotation = 0 ∧
      rotation.matrix ≠ Matrix3.identity ∧
      ∀ X : K, Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3 := by
  unfold parabolicRotationsOverDirection at member
  rcases QuotientFreeList.mem_map.mp member with
    ⟨parameter, parameterMember, equal⟩
  have parameterNonzero :=
    (presentation.mem_nonzeroScalars_iff parameter).1 parameterMember |>.1
  have scaledNull : (Vector.scale parameter direction).quadrance = 0 := by
    rw [Vector.quadrance_scale,
      presentation.nullDirectionRepresentative_null directionMember]
    ring1
  have scaledNonzero : Vector.scale parameter direction ≠ Vector.zero := by
    intro scaledZero
    apply parameterNonzero
    apply presentation.nullDirection_scale_injective directionMember
    calc
      Vector.scale parameter direction = Vector.zero := scaledZero
      _ = Vector.scale 0 direction := (Vector.zero_scale direction).symm
  rw [← equal]
  exact
    ⟨presentation.parabolicRotation_halfSpread _ scaledNull,
      presentation.parabolicRotation_nonidentity _ scaledNull scaledNonzero,
      presentation.parabolicRotation_characteristic _ scaledNull⟩

/-- Every nonidentity half-spread-zero rotation has one and only one displayed
nonzero null anchor.  The existential retains the null and nonzero
certificates used to construct the cap. -/
theorem parabolicRotation_complete (rotation : Rotation K)
    (spreadZero : halfSpread rotation = 0)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    ∃ vector : Vector K, ∃ null : vector.quadrance = 0,
      vector ≠ Vector.zero ∧
      vector ∈ presentation.nonzeroNullVectors ∧
        rotation = presentation.parabolicRotation vector null := by
  have notHalfTurn : halfSpread rotation ≠ 1 := by
    intro spreadOne
    apply one_ne_zero presentation
    calc
      (1 : K) = halfSpread rotation := spreadOne.symm
      _ = 0 := spreadZero
  let vector := rotationAnchorVector rotation notHalfTurn
  have null : vector.quadrance = 0 := by
    have recoveredQuadrance := quadrance_rotationAnchorVector rotation
      notHalfTurn presentation.twoNonzero
    rw [spreadZero] at recoveredQuadrance
    simpa only [sub_zero, RFAP.ExplicitField.zero_div] using
      recoveredQuadrance
  have nonzero : vector ≠ Vector.zero := by
    intro vectorZero
    apply nonidentity
    have recovered := cap_rotationAnchor rotation notHalfTurn
      presentation.twoNonzero
    have zeroCap := presentation.cap_zero_eq_identity_counting
    calc
      rotation.matrix = cap vector
          (rotationAnchorVector_capDefined rotation notHalfTurn
            presentation.twoNonzero) := recovered.symm
      _ = cap Vector.zero
          (presentation.capDenominator_ne_zero_of_null_counting
            Vector.zero Vector.quadrance_zero) :=
        cap_eq_of_vector_eq_counting vectorZero _ _
      _ = Matrix3.identity := zeroCap
  have member : vector ∈ presentation.nonzeroNullVectors :=
    (presentation.mem_nonzeroNullVectors_iff vector).2
      ⟨presentation.vectors_complete vector, null, nonzero⟩
  refine ⟨vector, null, nonzero, member, ?_⟩
  apply rotation_eq_of_matrix_eq
  exact (cap_rotationAnchor rotation notHalfTurn presentation.twoNonzero).symm

/-- Characteristic-polynomial form of parabolic completeness.  This is the
literal converse requested by Problem 69: every nonidentity rotation with
characteristic polynomial `(X - 1)^3` is a cap of one displayed nonzero null
anchor. -/
theorem parabolicRotation_complete_of_characteristic
    (rotation : Rotation K)
    (characteristic : ∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    ∃ vector : Vector K, ∃ null : vector.quadrance = 0,
      vector ≠ Vector.zero ∧
      vector ∈ presentation.nonzeroNullVectors ∧
        rotation = presentation.parabolicRotation vector null :=
  presentation.parabolicRotation_complete rotation
    ((characteristicUnipotent_iff_halfSpread_eq_zero rotation
      presentation.twoNonzero).1 characteristic)
    nonidentity

/-- Executable canonical null-direction and nonzero parameter coordinates for
one nonidentity parabolic rotation. -/
structure ParabolicDirectionCoordinates (rotation : Rotation K) where
  direction : Vector K
  directionMember : direction ∈ presentation.nullDirectionRepresentatives
  parameter : K
  parameterMember : parameter ∈ presentation.nonzeroScalars
  scaledNull : (Vector.scale parameter direction).quadrance = 0
  rotation_eq : rotation = presentation.parabolicRotation
    (Vector.scale parameter direction) scaledNull

/-- Recover the canonical projective null direction and its affine parameter
directly from a nonidentity half-spread-zero rotation. -/
def parabolicDirectionCoordinates (rotation : Rotation K)
    (spreadZero : halfSpread rotation = 0)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    presentation.ParabolicDirectionCoordinates rotation := by
  have notHalfTurn : halfSpread rotation ≠ 1 := by
    intro spreadOne
    apply one_ne_zero presentation
    calc
      (1 : K) = halfSpread rotation := spreadOne.symm
      _ = 0 := spreadZero
  let anchorVector := rotationAnchorVector rotation notHalfTurn
  have anchorNull : anchorVector.quadrance = 0 := by
    have recoveredQuadrance := quadrance_rotationAnchorVector rotation
      notHalfTurn presentation.twoNonzero
    rw [spreadZero] at recoveredQuadrance
    simpa only [sub_zero, RFAP.ExplicitField.zero_div] using
      recoveredQuadrance
  have anchorNonzero : anchorVector ≠ Vector.zero := by
    intro anchorZero
    apply nonidentity
    have recovered := cap_rotationAnchor rotation notHalfTurn
      presentation.twoNonzero
    have zeroCap := presentation.cap_zero_eq_identity_counting
    calc
      rotation.matrix = cap anchorVector
          (rotationAnchorVector_capDefined rotation notHalfTurn
            presentation.twoNonzero) := recovered.symm
      _ = cap Vector.zero
          (presentation.capDenominator_ne_zero_of_null_counting
            Vector.zero Vector.quadrance_zero) :=
        cap_eq_of_vector_eq_counting anchorZero _ _
      _ = Matrix3.identity := zeroCap
  let normalization := presentation.normalizeNullDirection anchorVector
    anchorNull anchorNonzero
  have directionNull : normalization.representative.quadrance = 0 :=
    presentation.nullDirectionRepresentative_null
      normalization.representativeMember
  have scaledNull :
      (Vector.scale normalization.parameter
        normalization.representative).quadrance = 0 := by
    rw [Vector.quadrance_scale, directionNull]
    ring1
  refine
    { direction := normalization.representative
      directionMember := normalization.representativeMember
      parameter := normalization.parameter
      parameterMember :=
        (presentation.mem_nonzeroScalars_iff normalization.parameter).2
          ⟨normalization.parameterNonzero,
            presentation.carrierComplete normalization.parameter⟩
      scaledNull := scaledNull
      rotation_eq := ?_ }
  apply rotation_eq_of_matrix_eq
  let scaledDefined :=
    presentation.capDenominator_ne_zero_of_null_counting
      (Vector.scale normalization.parameter normalization.representative)
      scaledNull
  change rotation.matrix = cap
    (Vector.scale normalization.parameter normalization.representative)
      scaledDefined
  have recovered := cap_rotationAnchor rotation notHalfTurn
    presentation.twoNonzero
  calc
    rotation.matrix = cap anchorVector
        (rotationAnchorVector_capDefined rotation notHalfTurn
          presentation.twoNonzero) := recovered.symm
    _ = cap (Vector.scale normalization.parameter normalization.representative)
        scaledDefined :=
      cap_eq_of_vector_eq_counting normalization.source_eq_scale _ _

/-- Executable direction/parameter normal form obtained directly from the
paper's characteristic-polynomial description of a parabolic rotation. -/
def parabolicDirectionCoordinatesOfCharacteristic
    (rotation : Rotation K)
    (characteristic : ∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    presentation.ParabolicDirectionCoordinates rotation :=
  presentation.parabolicDirectionCoordinates rotation
    ((characteristicUnipotent_iff_halfSpread_eq_zero rotation
      presentation.twoNonzero).1 characteristic)
    nonidentity

/-- Any other canonical direction/parameter description of the same
parabolic rotation agrees with the computed coordinates. -/
theorem parabolicDirectionCoordinates_unique (rotation : Rotation K)
    (spreadZero : halfSpread rotation = 0)
    (nonidentity : rotation.matrix ≠ Matrix3.identity)
    (direction : Vector K)
    (directionMember : direction ∈
      presentation.nullDirectionRepresentatives)
    (parameter : K) (parameterNonzero : parameter ≠ 0)
    (scaledNull : (Vector.scale parameter direction).quadrance = 0)
    (rotationEq : rotation = presentation.parabolicRotation
      (Vector.scale parameter direction) scaledNull) :
    let coordinates := presentation.parabolicDirectionCoordinates rotation
      spreadZero nonidentity
    direction = coordinates.direction ∧ parameter = coordinates.parameter := by
  let coordinates := presentation.parabolicDirectionCoordinates rotation
    spreadZero nonidentity
  have coordinateParameterNonzero :=
    (presentation.mem_nonzeroScalars_iff coordinates.parameter).1
      coordinates.parameterMember |>.1
  have rotationEqual :
      presentation.parabolicRotation (Vector.scale parameter direction)
          scaledNull =
        presentation.parabolicRotation
          (Vector.scale coordinates.parameter coordinates.direction)
          coordinates.scaledNull :=
    rotationEq.symm.trans coordinates.rotation_eq
  have anchorEqual :
      Vector.scale parameter direction =
        Vector.scale coordinates.parameter coordinates.direction :=
    presentation.parabolicRotation_injective scaledNull
      coordinates.scaledNull rotationEqual
  let factor := coordinates.parameter⁻¹ * parameter
  have factorNonzero : factor ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.inv_ne_zero coordinateParameterNonzero)
      parameterNonzero
  have coordinateCancel := inverse_mul coordinates.parameter
    coordinateParameterNonzero
  have scaledDirections :
      coordinates.direction = Vector.scale factor direction := by
    apply Vector.ext
    · have coordinate := congrArg Vector.t anchorEqual
      change parameter * direction.t =
        coordinates.parameter * coordinates.direction.t at coordinate
      change coordinates.direction.t =
        (coordinates.parameter⁻¹ * parameter) * direction.t
      calc
        coordinates.direction.t = 1 * coordinates.direction.t := by ring1
        _ = (coordinates.parameter⁻¹ * coordinates.parameter) *
            coordinates.direction.t := by rw [coordinateCancel]
        _ = coordinates.parameter⁻¹ *
            (coordinates.parameter * coordinates.direction.t) := by ring1
        _ = coordinates.parameter⁻¹ * (parameter * direction.t) := by
          rw [coordinate]
        _ = (coordinates.parameter⁻¹ * parameter) * direction.t := by ring1
    · have coordinate := congrArg Vector.r anchorEqual
      change parameter * direction.r =
        coordinates.parameter * coordinates.direction.r at coordinate
      change coordinates.direction.r =
        (coordinates.parameter⁻¹ * parameter) * direction.r
      calc
        coordinates.direction.r = 1 * coordinates.direction.r := by ring1
        _ = (coordinates.parameter⁻¹ * coordinates.parameter) *
            coordinates.direction.r := by rw [coordinateCancel]
        _ = coordinates.parameter⁻¹ *
            (coordinates.parameter * coordinates.direction.r) := by ring1
        _ = coordinates.parameter⁻¹ * (parameter * direction.r) := by
          rw [coordinate]
        _ = (coordinates.parameter⁻¹ * parameter) * direction.r := by ring1
    · have coordinate := congrArg Vector.s anchorEqual
      change parameter * direction.s =
        coordinates.parameter * coordinates.direction.s at coordinate
      change coordinates.direction.s =
        (coordinates.parameter⁻¹ * parameter) * direction.s
      calc
        coordinates.direction.s = 1 * coordinates.direction.s := by ring1
        _ = (coordinates.parameter⁻¹ * coordinates.parameter) *
            coordinates.direction.s := by rw [coordinateCancel]
        _ = coordinates.parameter⁻¹ *
            (coordinates.parameter * coordinates.direction.s) := by ring1
        _ = coordinates.parameter⁻¹ * (parameter * direction.s) := by
          rw [coordinate]
        _ = (coordinates.parameter⁻¹ * parameter) * direction.s := by ring1
  have directionEqual := presentation.nullDirectionRepresentative_eq_of_scaled
    directionMember coordinates.directionMember factorNonzero scaledDirections
  constructor
  · exact directionEqual
  · apply presentation.nullDirection_scale_injective
      coordinates.directionMember
    calc
      Vector.scale parameter coordinates.direction =
          Vector.scale parameter direction := by rw [directionEqual]
      _ = Vector.scale coordinates.parameter coordinates.direction :=
        anchorEqual

/-- Executable four-way classification of one finite-field rotation.  The
endpoint cases retain the matrix, axis, or canonical parabolic coordinates
needed by downstream computations instead of storing only a proposition. -/
inductive RotationStratum (rotation : Rotation K) where
  | identity
      (spreadZero : halfSpread rotation = 0)
      (matrixIdentity : rotation.matrix = Matrix3.identity)
  | parabolic
      (spreadZero : halfSpread rotation = 0)
      (matrixNonidentity : rotation.matrix ≠ Matrix3.identity)
      (coordinates : presentation.ParabolicDirectionCoordinates rotation)
  | halfTurn
      (spreadOne : halfSpread rotation = 1)
      (axis : Vector K)
      (axisNonNull : axis.quadrance ≠ 0)
      (matrix_eq : rotation.matrix = halfTurn axis axisNonNull)
  | semisimple
      (spreadNonzero : halfSpread rotation ≠ 0)
      (spreadNotOne : halfSpread rotation ≠ 1)

/-- Classify a displayed rotation by the two finite half-spread tests and one
matrix-identity test. -/
def classifyRotationStratum (rotation : Rotation K) :
    presentation.RotationStratum rotation := by
  letI : DecidableEq K := presentation.eqDecidable
  by_cases spreadZero : halfSpread rotation = 0
  · by_cases matrixIdentity : rotation.matrix = Matrix3.identity
    · exact RotationStratum.identity spreadZero matrixIdentity
    · exact RotationStratum.parabolic spreadZero matrixIdentity
        (presentation.parabolicDirectionCoordinates rotation spreadZero
          matrixIdentity)
  · by_cases spreadOne : halfSpread rotation = 1
    · let axis := halfTurnAxis rotation spreadOne presentation.twoNonzero
      let axisNonNull := halfTurnAxis_nonNull rotation spreadOne
        presentation.twoNonzero
      exact RotationStratum.halfTurn spreadOne axis axisNonNull
        (rotation_eq_halfTurn_halfTurnAxis rotation spreadOne
          presentation.twoNonzero)
    · exact RotationStratum.semisimple spreadZero spreadOne

/-- Count a Boolean property on one displayed finite list. -/
private def listCountWhere {Alpha : Type*}
    (values : List Alpha) (predicate : Alpha → Bool) : Nat :=
  (values.filter predicate).length

private theorem listCountWhere_append {Alpha : Type*}
    (left right : List Alpha) (predicate : Alpha → Bool) :
    listCountWhere (left ++ right) predicate =
      listCountWhere left predicate + listCountWhere right predicate := by
  unfold listCountWhere
  rw [List.filter_append, List.length_append]

private theorem listCountWhere_map {Alpha Beta : Type*}
    (values : List Alpha) (function : Alpha → Beta)
    (predicate : Beta → Bool) :
    listCountWhere (values.map function) predicate =
      listCountWhere values (fun value => predicate (function value)) := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      unfold listCountWhere at inductionHypothesis ⊢
      rw [List.map_cons, List.filter_cons, List.filter_cons]
      cases accepted : predicate (function head) with
      | false =>
          change (List.filter predicate (List.map function tail)).length =
            (List.filter (fun value => predicate (function value)) tail).length
          exact inductionHypothesis
      | true =>
          change Nat.succ
              (List.filter predicate (List.map function tail)).length =
            Nat.succ
              (List.filter (fun value => predicate (function value)) tail).length
          exact congrArg Nat.succ inductionHypothesis

private theorem listCountWhere_congr {Alpha : Type*}
    (values : List Alpha) (left right : Alpha → Bool)
    (pointwise : ∀ value ∈ values, left value = right value) :
    listCountWhere values left = listCountWhere values right := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      unfold listCountWhere at inductionHypothesis ⊢
      rw [List.filter_cons, List.filter_cons,
        pointwise head List.mem_cons_self]
      cases accepted : right head with
      | false =>
          exact inductionHypothesis (fun value member =>
            pointwise value (List.mem_cons_of_mem head member))
      | true =>
          exact congrArg Nat.succ
            (inductionHypothesis (fun value member =>
              pointwise value (List.mem_cons_of_mem head member)))

private theorem listCountWhere_eq_zero_of_reject {Alpha : Type*}
    (values : List Alpha) (predicate : Alpha → Bool)
    (reject : ∀ value ∈ values, predicate value = false) :
    listCountWhere values predicate = 0 := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      unfold listCountWhere at inductionHypothesis ⊢
      rw [List.filter_cons, reject head List.mem_cons_self]
      exact inductionHypothesis (fun value member =>
        reject value (List.mem_cons_of_mem head member))

private theorem listCountWhere_add_complement {Alpha : Type*}
    (values : List Alpha) (predicate : Alpha → Bool) :
    listCountWhere values predicate +
      listCountWhere values (fun value => !predicate value) = values.length := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      unfold listCountWhere at inductionHypothesis ⊢
      rw [List.filter_cons, List.filter_cons]
      cases accepted : predicate head with
      | false =>
          rw [Bool.not_false]
          change (tail.filter predicate).length +
            Nat.succ (tail.filter fun value => !predicate value).length =
              Nat.succ tail.length
          rw [Nat.add_succ, inductionHypothesis]
      | true =>
          rw [Bool.not_true]
          change Nat.succ (tail.filter predicate).length +
            (tail.filter fun value => !predicate value).length =
              Nat.succ tail.length
          rw [Nat.succ_add, inductionHypothesis]

private theorem listCountWhere_add_complementary {Alpha : Type*}
    (values : List Alpha) (accepted rejected : Alpha → Bool)
    (complementary : ∀ value ∈ values, (!accepted value) = rejected value) :
    listCountWhere values accepted + listCountWhere values rejected =
      values.length := by
  have equal := listCountWhere_congr values
    (fun value => !accepted value) rejected complementary
  rw [← equal]
  exact listCountWhere_add_complement values accepted

theorem quadranceClassFibers_partition :
    presentation.quadranceClassKernel.length +
        presentation.quadranceClassNontrivialFiber.length =
      presentation.nonNullProjectiveRepresentatives.length := by
  exact listCountWhere_add_complement
    presentation.nonNullProjectiveRepresentatives
    (fun proportion => presentation.isSquare proportion.toProportion.norm)

private theorem flatMap_map_length {Alpha Beta Gamma : Type*}
    (outer : List Alpha) (inner : List Beta)
    (function : Alpha → Beta → Gamma) :
    (outer.flatMap fun left => inner.map fun right => function left right).length =
      outer.length * inner.length := by
  induction outer with
  | nil =>
      change 0 = 0 * inner.length
      exact (Nat.zero_mul inner.length).symm
  | cons head tail inductionHypothesis =>
      rw [List.flatMap_cons, List.length_append, List.length_map,
        inductionHypothesis, List.length_cons, Nat.succ_mul, Nat.add_comm]

private theorem flatMap_length_of_constant {Alpha Beta : Type*}
    (values : List Alpha) (fiber : Alpha → List Beta) (count : Nat)
    (fiberLength : ∀ value ∈ values, (fiber value).length = count) :
    (values.flatMap fiber).length = values.length * count := by
  induction values with
  | nil =>
      change 0 = 0 * count
      exact (Nat.zero_mul count).symm
  | cons head tail inductionHypothesis =>
      rw [List.flatMap_cons, List.length_append,
        fiberLength head List.mem_cons_self,
        inductionHypothesis (fun value member =>
          fiberLength value (List.mem_cons_of_mem head member)),
        List.length_cons, Nat.succ_mul, Nat.add_comm]

theorem nonzeroScalarWitnesses_length :
    presentation.nonzeroScalarWitnesses.length =
      presentation.carrier.length - 1 := by
  calc
    presentation.nonzeroScalarWitnesses.length =
        presentation.nonzeroScalars.length :=
      FiniteListBijection.length_eq
        presentation.nonzeroScalarWitnessValueBijection
        presentation.nonzeroScalarWitnesses_nodup
        presentation.nonzeroScalars_nodup
    _ = presentation.carrier.length - 1 :=
      presentation.nonzeroScalars_length

theorem scaleOrbitCoordinates_length :
    presentation.scaleOrbitCoordinates.length =
      (presentation.carrier.length - 1) *
        presentation.nonNullProjectiveRepresentatives.length := by
  unfold scaleOrbitCoordinates
  rw [flatMap_map_length, presentation.nonzeroScalarWitnesses_length]

/-- Counting the raw non-null four-tuples by their explicit scale orbits. -/
theorem allNonNullProportionRepresentatives_length :
    presentation.allNonNullProportionRepresentatives.length =
      (presentation.carrier.length - 1) *
        presentation.nonNullProjectiveRepresentatives.length := by
  calc
    presentation.allNonNullProportionRepresentatives.length =
        presentation.scaleOrbitCoordinates.length :=
      FiniteListBijection.length_eq presentation.nonNullScaleOrbitBijection
        presentation.allNonNullProportionRepresentatives_nodup
        presentation.scaleOrbitCoordinates_nodup
    _ = (presentation.carrier.length - 1) *
        presentation.nonNullProjectiveRepresentatives.length :=
      presentation.scaleOrbitCoordinates_length

private theorem foldr_add_map_zero {Alpha : Type*} (values : List Alpha) :
    (values.map fun _ => 0).foldr Nat.add 0 = 0 := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.foldr_cons, inductionHypothesis]

private theorem foldr_add_map_pointwise_add {Alpha : Type*}
    (values : List Alpha) (left right : Alpha → Nat) :
    (values.map fun value => left value + right value).foldr Nat.add 0 =
      (values.map left).foldr Nat.add 0 +
        (values.map right).foldr Nat.add 0 := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.map_cons, List.map_cons,
        List.foldr_cons, List.foldr_cons, List.foldr_cons,
        inductionHypothesis]
      calc
        (left head + right head) +
            ((tail.map left).foldr Nat.add 0 +
              (tail.map right).foldr Nat.add 0) =
          left head + (right head +
            ((tail.map left).foldr Nat.add 0 +
              (tail.map right).foldr Nat.add 0)) :=
            Nat.add_assoc _ _ _
        _ = left head + ((right head +
              (tail.map left).foldr Nat.add 0) +
            (tail.map right).foldr Nat.add 0) :=
          congrArg (Nat.add (left head))
            (Nat.add_assoc _ _ _).symm
        _ = left head + (((tail.map left).foldr Nat.add 0 +
              right head) +
            (tail.map right).foldr Nat.add 0) := by
          rw [Nat.add_comm (right head) ((tail.map left).foldr Nat.add 0)]
        _ = (left head + (tail.map left).foldr Nat.add 0) +
            (right head + (tail.map right).foldr Nat.add 0) := by
          rw [Nat.add_assoc (left head) ((tail.map left).foldr Nat.add 0)
            (right head + (tail.map right).foldr Nat.add 0),
            Nat.add_assoc ((tail.map left).foldr Nat.add 0) (right head)
              ((tail.map right).foldr Nat.add 0)]

private theorem listCountWhere_eq_foldr_indicators {Alpha : Type*}
    (values : List Alpha) (predicate : Alpha → Bool) :
    listCountWhere values predicate =
      (values.map fun value => if predicate value then 1 else 0).foldr
        Nat.add 0 := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      unfold listCountWhere at inductionHypothesis ⊢
      rw [List.filter_cons, List.map_cons, List.foldr_cons]
      cases accepted : predicate head with
      | false =>
          rw [if_neg (by decide : ¬ (false = true)),
            if_neg (by decide : ¬ (false = true))]
          exact inductionHypothesis.trans
            (Nat.zero_add _).symm
      | true =>
          rw [if_pos rfl, if_pos rfl, List.length_cons]
          calc
            (tail.filter predicate).length + 1 =
                1 + (tail.filter predicate).length := Nat.add_comm _ _
            _ = 1 +
                ((tail.map fun value =>
                  if predicate value then 1 else 0).foldr Nat.add 0) :=
              congrArg (Nat.add 1) inductionHypothesis

private theorem listCountWhere_cons {Alpha : Type*}
    (head : Alpha) (tail : List Alpha) (predicate : Alpha → Bool) :
    listCountWhere (head :: tail) predicate =
      (if predicate head then 1 else 0) + listCountWhere tail predicate := by
  unfold listCountWhere
  rw [List.filter_cons]
  cases predicate head with
  | false =>
      rw [if_neg (by decide : ¬ (false = true)),
        if_neg (by decide : ¬ (false = true)), Nat.zero_add]
  | true =>
      rw [if_pos rfl, if_pos rfl, List.length_cons]
      exact Nat.add_comm _ _

private theorem listCountWhere_sum_swap {Alpha Beta : Type*}
    (left : List Alpha) (right : List Beta)
    (predicate : Alpha → Beta → Bool) :
    (left.map fun leftValue =>
        listCountWhere right (predicate leftValue)).foldr Nat.add 0 =
      (right.map fun rightValue =>
        listCountWhere left (fun leftValue =>
          predicate leftValue rightValue)).foldr Nat.add 0 := by
  induction left with
  | nil =>
      rw [List.map_nil, List.foldr_nil]
      change 0 = (right.map fun _ => 0).foldr Nat.add 0
      exact (foldr_add_map_zero right).symm
  | cons head tail inductionHypothesis =>
      rw [List.map_cons, List.foldr_cons]
      calc
        listCountWhere right (predicate head) +
            (tail.map fun leftValue =>
              listCountWhere right (predicate leftValue)).foldr Nat.add 0 =
          (right.map fun rightValue =>
              (if predicate head rightValue then 1 else 0)).foldr Nat.add 0 +
            (right.map fun rightValue =>
              listCountWhere tail (fun leftValue =>
                predicate leftValue rightValue)).foldr Nat.add 0 := by
          rw [← listCountWhere_eq_foldr_indicators right (predicate head),
            inductionHypothesis]
        _ = (right.map fun rightValue =>
            (if predicate head rightValue then 1 else 0) +
              listCountWhere tail (fun leftValue =>
                predicate leftValue rightValue)).foldr Nat.add 0 :=
          (foldr_add_map_pointwise_add right
            (fun rightValue => if predicate head rightValue then 1 else 0)
            (fun rightValue => listCountWhere tail (fun leftValue =>
              predicate leftValue rightValue))).symm
        _ = (right.map fun rightValue =>
            listCountWhere (head :: tail) (fun leftValue =>
              predicate leftValue rightValue)).foldr Nat.add 0 := by
          apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
          apply QuotientFreeList.map_congr_left
          intro rightValue _
          exact (listCountWhere_cons head tail (fun leftValue =>
            predicate leftValue rightValue)).symm

private theorem listCountWhere_eq_one_of_eq_target {Alpha : Type*}
    (eqDecidable : DecidableEq Alpha) (values : List Alpha)
    (valuesNodup : values.Nodup) (target : Alpha) (targetMember : target ∈ values) :
    (letI : DecidableEq Alpha := eqDecidable
     listCountWhere values fun value => decide (value = target)) = 1 := by
  letI : DecidableEq Alpha := eqDecidable
  induction values with
  | nil => nomatch targetMember
  | cons head tail inductionHypothesis =>
      cases eqDecidable head target with
      | isTrue equal =>
          have targetNotInTail : target ∉ tail := by
            intro member
            apply (List.pairwise_cons.mp valuesNodup).1 target member
            exact equal
          rw [listCountWhere_cons]
          rw [decide_eq_true equal, if_pos rfl]
          have tailZero := listCountWhere_eq_zero_of_reject tail
            (fun value => decide (value = target)) (by
              intro value member
              apply decide_eq_false
              intro valueEqual
              exact targetNotInTail (valueEqual ▸ member))
          rw [tailZero]
      | isFalse different =>
          rw [listCountWhere_cons]
          rw [decide_eq_false different]
          simp only [Bool.false_eq_true, if_false, zero_add]
          apply inductionHypothesis (List.pairwise_cons.mp valuesNodup).2
          rcases List.mem_cons.mp targetMember with headMember | tailMember
          · exact False.elim (different headMember.symm)
          · exact tailMember

private theorem filter_and_eq_filter_filter {Alpha : Type*}
    (values : List Alpha) (first second : Alpha → Bool) :
    values.filter (fun value => first value && second value) =
      (values.filter first).filter second := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.filter_cons, List.filter_cons]
      cases firstAccepted : first head with
      | false =>
          rw [Bool.false_and]
          exact inductionHypothesis
      | true =>
          rw [Bool.true_and, if_pos rfl, List.filter_cons]
          cases secondAccepted : second head with
          | false =>
              have falseNeTrue : ¬ false = true := by
                intro impossible
                exact Bool.noConfusion impossible
              rw [if_neg falseNeTrue, if_neg falseNeTrue]
              exact inductionHypothesis
          | true =>
              rw [if_pos rfl, if_pos rfl, inductionHypothesis]

private theorem filter_ne_target_eq_self {Alpha : Type*}
    (eqDecidable : DecidableEq Alpha) (target : Alpha) :
    ∀ {values : List Alpha}, (∀ value ∈ values, value ≠ target) →
      (letI : DecidableEq Alpha := eqDecidable
       values.filter fun value => value ≠ target) = values
  | [], _ => rfl
  | head :: tail, allDifferent => by
      letI : DecidableEq Alpha := eqDecidable
      rw [List.filter_cons_of_pos
        (p := fun value : Alpha => decide (value ≠ target))
        (decide_eq_true (allDifferent head List.mem_cons_self))]
      rw [filter_ne_target_eq_self eqDecidable target (fun value member =>
        allDifferent value (List.mem_cons_of_mem head member))]

private theorem filter_ne_target_length_add_one {Alpha : Type*}
    (eqDecidable : DecidableEq Alpha) (target : Alpha) :
    ∀ {values : List Alpha}, values.Nodup → target ∈ values →
      (letI : DecidableEq Alpha := eqDecidable
       (values.filter fun value => value ≠ target).length + 1) = values.length
  | [], _, impossible => nomatch impossible
  | head :: tail, nodup, targetMember => by
      letI : DecidableEq Alpha := eqDecidable
      cases eqDecidable head target with
      | isTrue headTarget =>
          have tailDifferent : ∀ value ∈ tail, value ≠ target := by
            intro value member valueTarget
            apply (List.pairwise_cons.mp nodup).1 value member
            exact headTarget.trans valueTarget.symm
          rw [List.filter_cons_of_neg
            (p := fun value : Alpha => decide (value ≠ target))
            (fun accepted => (of_decide_eq_true accepted) headTarget)]
          rw [filter_ne_target_eq_self eqDecidable target tailDifferent]
          rfl
      | isFalse headDifferent =>
          have tailMember : target ∈ tail := by
            rcases List.mem_cons.mp targetMember with headMember | member
            · exact False.elim (headDifferent headMember.symm)
            · exact member
          rw [List.filter_cons_of_pos
            (p := fun value : Alpha => decide (value ≠ target))
            (decide_eq_true headDifferent)]
          have induction := filter_ne_target_length_add_one
            eqDecidable target (List.pairwise_cons.mp nodup).2 tailMember
          exact congrArg Nat.succ induction

private theorem listCountWhere_flatMap {Alpha Beta : Type*}
    (values : List Alpha) (fiber : Alpha → List Beta)
    (predicate : Beta → Bool) :
    listCountWhere (values.flatMap fiber) predicate =
      (values.map fun value =>
        listCountWhere (fiber value) predicate).foldr Nat.add 0 := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      rw [List.flatMap_cons, listCountWhere_append,
        inductionHypothesis, List.map_cons, List.foldr_cons]
      rfl

/-- Count one fixed-`t` slice of a Boolean property on affine vectors. -/
def vectorSliceCountWhere (t : K) (predicate : Vector K → Bool) : Nat :=
  (presentation.carrier.map fun r =>
    listCountWhere (presentation.carrier.map fun s => ⟨t, r, s⟩)
      predicate).foldr Nat.add 0

theorem vectorSliceQuadranceCount_eq_twoSquareCount (t value : K) :
    presentation.vectorSliceCountWhere t (fun vector =>
      @decide (vector.quadrance = value)
        (presentation.eqDecidable vector.quadrance value)) =
    presentation.twoSquareCount (value - t ^ 2) := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold vectorSliceCountWhere twoSquareCount twoSquareFiber scalarPairs
  change
    (presentation.carrier.map fun r =>
      listCountWhere
        (presentation.carrier.map fun s => (⟨t, r, s⟩ : Vector K))
        (fun vector => decide (vector.quadrance = value))).foldr Nat.add 0 =
      listCountWhere
        (presentation.carrier.flatMap fun r =>
          presentation.carrier.map fun s => (⟨r, s⟩ : ScalarPair K))
        (fun pair => decide (pair.quadrance = value - t ^ 2))
  rw [listCountWhere_flatMap]
  apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
  apply QuotientFreeList.map_congr_left
  intro r _
  rw [listCountWhere_map, listCountWhere_map]
  apply listCountWhere_congr
  intro s _
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    apply decide_eq_true
    have equation := of_decide_eq_true accepted
    unfold Vector.quadrance Vector.dot at equation
    unfold ScalarPair.quadrance
    calc
      r ^ 2 + s ^ 2 =
          (t * t + r * r + s * s) - t ^ 2 := by ring1
      _ = value - t ^ 2 := by rw [equation]
  · intro accepted
    apply decide_eq_true
    have equation := of_decide_eq_true accepted
    unfold ScalarPair.quadrance at equation
    unfold Vector.quadrance Vector.dot
    calc
      t * t + r * r + s * s = t ^ 2 + (r ^ 2 + s ^ 2) := by ring1
      _ = t ^ 2 + (value - t ^ 2) := by rw [equation]
      _ = value := by ring1

/-- Count a Boolean property over the displayed affine vector carrier without
first flattening its three nested loops.  Each fixed-`t` slice is reduced
separately, keeping concrete regression certificates within the ordinary
kernel recursion limit. -/
def vectorCountWhere (predicate : Vector K → Bool) : Nat :=
  (presentation.carrier.map fun t =>
    presentation.vectorSliceCountWhere t predicate).foldr Nat.add 0

theorem vectorCountWhere_congr (left right : Vector K → Bool)
    (pointwise : ∀ vector : Vector K, left vector = right vector) :
    presentation.vectorCountWhere left = presentation.vectorCountWhere right := by
  unfold vectorCountWhere vectorSliceCountWhere
  apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
  apply QuotientFreeList.map_congr_left
  intro t _
  apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
  apply QuotientFreeList.map_congr_left
  intro r _
  apply listCountWhere_congr
  intro vector _
  exact pointwise vector

/-- Count one fixed-`r` line in the first chart at infinity. -/
def infinityTSliceCountWhere (r : K)
    (predicate : Proportion K → Bool) : Nat :=
  listCountWhere (presentation.carrier.map fun s => ⟨0, ⟨1, r, s⟩⟩)
    predicate

/-- Count a Boolean property over the four canonical projective charts,
again retaining the nested chart loops rather than reducing one long list. -/
def projectiveCountWhere (predicate : Proportion K → Bool) : Nat :=
  let affine := presentation.vectorCountWhere fun vector =>
    predicate ⟨1, vector⟩
  let infinityT := (presentation.carrier.map fun r =>
    presentation.infinityTSliceCountWhere r predicate).foldr Nat.add 0
  let infinityR := listCountWhere
    (presentation.carrier.map fun s => ⟨0, ⟨0, 1, s⟩⟩) predicate
  let infinityS := if predicate infinitySRepresentative then 1 else 0
  affine + infinityT + infinityR + infinityS

/-- A projective predicate supported only in the scalar-one chart counts the
same objects as its displayed affine-vector predicate. -/
theorem projectiveCountWhere_eq_vectorCountWhere_of_infinity_rejected
    (predicate : Proportion K → Bool) (affinePredicate : Vector K → Bool)
    (affine : ∀ vector : Vector K,
      predicate ⟨1, vector⟩ = affinePredicate vector)
    (infinity : ∀ raw : Proportion K, raw.scalar = 0 → predicate raw = false) :
    presentation.projectiveCountWhere predicate =
      presentation.vectorCountWhere affinePredicate := by
  unfold projectiveCountWhere infinityTSliceCountWhere
  have affineEqual := presentation.vectorCountWhere_congr
    (fun vector => predicate ⟨1, vector⟩) affinePredicate affine
  rw [affineEqual]
  have infinityTZero : ∀ r : K,
      listCountWhere
        (presentation.carrier.map fun s =>
          (⟨0, ⟨1, r, s⟩⟩ : Proportion K)) predicate = 0 := by
    intro r
    apply listCountWhere_eq_zero_of_reject
    intro raw member
    rcases QuotientFreeList.mem_map.mp member with ⟨s, _, equal⟩
    rw [← equal]
    exact infinity ⟨0, ⟨1, r, s⟩⟩ rfl
  have infinityTMap :
      presentation.carrier.map (fun r =>
        listCountWhere
          (presentation.carrier.map fun s =>
            (⟨0, ⟨1, r, s⟩⟩ : Proportion K)) predicate) =
        presentation.carrier.map fun _ => 0 := by
    apply QuotientFreeList.map_congr_left
    intro r _
    exact infinityTZero r
  rw [infinityTMap, foldr_add_map_zero]
  have infinityRZero :
      listCountWhere
        (presentation.carrier.map fun s =>
          (⟨0, ⟨0, 1, s⟩⟩ : Proportion K)) predicate = 0 := by
    apply listCountWhere_eq_zero_of_reject
    intro raw member
    rcases QuotientFreeList.mem_map.mp member with ⟨s, _, equal⟩
    rw [← equal]
    exact infinity ⟨0, ⟨0, 1, s⟩⟩ rfl
  rw [infinityRZero, infinity infinitySRepresentative rfl]
  rfl

private theorem vectorSliceCountWhere_eq (t : K)
    (predicate : Vector K → Bool) :
    presentation.vectorSliceCountWhere t predicate =
      listCountWhere
        (presentation.carrier.flatMap fun r =>
          presentation.carrier.map fun s => ⟨t, r, s⟩) predicate := by
  unfold vectorSliceCountWhere
  exact (listCountWhere_flatMap presentation.carrier
    (fun r => presentation.carrier.map fun s => ⟨t, r, s⟩)
    predicate).symm

theorem vectorCountWhere_eq_length_filter (predicate : Vector K → Bool) :
    presentation.vectorCountWhere predicate =
      (presentation.vectors.filter predicate).length := by
  change presentation.vectorCountWhere predicate =
    listCountWhere presentation.vectors predicate
  unfold vectorCountWhere vectors
  rw [listCountWhere_flatMap]
  apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
  apply QuotientFreeList.map_congr_left
  intro t _
  exact presentation.vectorSliceCountWhere_eq t predicate

private theorem vectorCountWhere_eq_zero_of_reject
    (predicate : Vector K → Bool)
    (reject : ∀ vector ∈ presentation.vectors, predicate vector = false) :
    presentation.vectorCountWhere predicate = 0 := by
  rw [presentation.vectorCountWhere_eq_length_filter]
  exact listCountWhere_eq_zero_of_reject presentation.vectors predicate reject

private theorem affineCountWhere_eq (predicate : Proportion K → Bool) :
    presentation.vectorCountWhere (fun vector => predicate ⟨1, vector⟩) =
      listCountWhere presentation.affineProportionRepresentatives
        predicate := by
  unfold affineProportionRepresentatives
  rw [listCountWhere_map]
  exact presentation.vectorCountWhere_eq_length_filter _

private theorem infinityTCountWhere_eq
    (predicate : Proportion K → Bool) :
    (presentation.carrier.map fun r =>
      presentation.infinityTSliceCountWhere r predicate).foldr Nat.add 0 =
      listCountWhere presentation.infinityTRepresentatives predicate := by
  unfold infinityTRepresentatives
  rw [listCountWhere_flatMap]
  apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
  apply QuotientFreeList.map_congr_left
  intro r _
  rfl

private theorem infinityRCountWhere_eq
    (predicate : Proportion K → Bool) :
    listCountWhere
        (presentation.carrier.map fun s => ⟨0, ⟨0, 1, s⟩⟩) predicate =
      listCountWhere presentation.infinityRRepresentatives predicate := by
  rfl

private theorem infinitySCountWhere_eq
    (_presentation : FiniteOddFieldPresentation K)
    (predicate : Proportion K → Bool) :
    (if predicate infinitySRepresentative then 1 else 0) =
      listCountWhere [infinitySRepresentative] predicate := by
  unfold listCountWhere
  cases accepted : predicate infinitySRepresentative with
  | false =>
      rw [List.filter_cons, accepted]
      have falseNeTrue : ¬ false = true := by
        intro impossible
        exact Bool.noConfusion impossible
      rw [if_neg falseNeTrue, if_neg falseNeTrue]
      rfl
  | true =>
      rw [List.filter_cons, accepted]
      rw [if_pos rfl, if_pos rfl]
      rfl

/-- The chart-efficient counter is exactly the length of the corresponding
filter of the canonical projective list. -/
theorem projectiveCountWhere_eq_length_filter
    (predicate : Proportion K → Bool) :
    presentation.projectiveCountWhere predicate =
      (presentation.projectiveRepresentatives.filter predicate).length := by
  change presentation.projectiveCountWhere predicate =
    listCountWhere presentation.projectiveRepresentatives predicate
  unfold projectiveCountWhere projectiveRepresentatives
  rw [presentation.affineCountWhere_eq,
    presentation.infinityTCountWhere_eq,
    presentation.infinityRCountWhere_eq,
    presentation.infinitySCountWhere_eq]
  rw [listCountWhere_append, listCountWhere_append,
    listCountWhere_append]

theorem projectiveCountWhere_congr (left right : Proportion K → Bool)
    (pointwise : ∀ raw : Proportion K, left raw = right raw) :
    presentation.projectiveCountWhere left =
      presentation.projectiveCountWhere right := by
  rw [presentation.projectiveCountWhere_eq_length_filter,
    presentation.projectiveCountWhere_eq_length_filter]
  exact listCountWhere_congr presentation.projectiveRepresentatives
    left right (fun raw _ => pointwise raw)

private theorem length_filterMap_eq_count_isSome
    {Alpha Beta : Type*} (values : List Alpha) (function : Alpha → Option Beta) :
    (values.filterMap function).length =
      listCountWhere values (fun value => (function value).isSome) := by
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases selected : function head with
      | none =>
          have rejected : (function head).isSome = false :=
            congrArg Option.isSome selected
          rw [List.filterMap_cons_none selected]
          unfold listCountWhere at inductionHypothesis ⊢
          rw [List.filter_cons]
          rw [rejected]
          change (tail.filterMap function).length =
            (tail.filter fun value => (function value).isSome).length
          exact inductionHypothesis
      | some result =>
          have accepted : (function head).isSome = true :=
            congrArg Option.isSome selected
          rw [List.filterMap_cons_some selected]
          unfold listCountWhere at inductionHypothesis ⊢
          rw [List.filter_cons, List.length_cons]
          rw [accepted]
          change Nat.succ (tail.filterMap function).length =
            Nat.succ
              (tail.filter fun value => (function value).isSome).length
          exact congrArg Nat.succ inductionHypothesis

/-- Efficient executable count of the non-null canonical projective carrier. -/
def rotationCount : Nat := by
  exact presentation.projectiveCountWhere fun raw =>
    (presentation.certifyNonNull raw).isSome

/-- The efficient counter counts the proved duplicate-free complete rotation
carrier, not a separate unchecked table. -/
theorem rotationCount_eq_rotationEnumeration_length :
    presentation.rotationCount =
      presentation.rotationEnumeration.values.length := by
  unfold rotationCount rotationEnumeration RotationEnumeration.values rotations
  rw [List.length_map]
  calc
    presentation.projectiveCountWhere
          (fun raw => (presentation.certifyNonNull raw).isSome) =
        (presentation.projectiveRepresentatives.filter
          (fun raw => (presentation.certifyNonNull raw).isSome)).length :=
      presentation.projectiveCountWhere_eq_length_filter _
    _ = presentation.nonNullProjectiveRepresentatives.length := by
      unfold nonNullProjectiveRepresentatives
      exact (length_filterMap_eq_count_isSome
        presentation.projectiveRepresentatives
        presentation.certifyNonNull).symm

/-- Homogeneous Boolean test for a non-null projective point of prescribed
half spread. -/
def halfSpreadAccepted (value : K) (raw : Proportion K) : Bool := by
  letI : DecidableEq K := presentation.eqDecidable
  exact decide (raw.norm ≠ 0) &&
    decide (raw.vector.quadrance = value * raw.norm)

/-- The scalar whose square class determines the sign of a non-endpoint
half-spread fiber in Problem 69. -/
def halfSpreadDiscriminant (value : K) : K :=
  -value * (1 - value)

private def normNonzeroAccepted (raw : Proportion K) : Bool := by
  letI : DecidableEq K := presentation.eqDecidable
  exact decide (raw.norm ≠ 0)

private theorem certifyNonNull_isSome_eq_normNonzeroAccepted
    (raw : Proportion K) :
    (presentation.certifyNonNull raw).isSome =
      presentation.normNonzeroAccepted raw := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold certifyNonNull normNonzeroAccepted
  split
  next normZero =>
    rw [decide_eq_false (fun normNonzero => normNonzero normZero)]
    rfl
  next normNonzero =>
    rw [decide_eq_true normNonzero]
    rfl

private theorem certifiedSquareFilter_length_eq_rawCount :
    ∀ values : List (Proportion K),
      ((values.filterMap presentation.certifyNonNull).filter fun proportion =>
          presentation.isSquare proportion.toProportion.norm).length =
        listCountWhere values fun raw =>
          presentation.normNonzeroAccepted raw &&
            presentation.isSquare raw.norm
  | [] => rfl
  | head :: tail => by
      cases certified : presentation.certifyNonNull head with
      | none =>
          have isSomeFalse :
              (presentation.certifyNonNull head).isSome = false :=
            congrArg Option.isSome certified
          have nonzeroFalse :
              presentation.normNonzeroAccepted head = false := by
            calc
              presentation.normNonzeroAccepted head =
                  (presentation.certifyNonNull head).isSome :=
                (presentation.certifyNonNull_isSome_eq_normNonzeroAccepted
                  head).symm
              _ = false := isSomeFalse
          rw [List.filterMap_cons_none certified]
          unfold listCountWhere
          rw [List.filter_cons, nonzeroFalse, Bool.false_and]
          exact certifiedSquareFilter_length_eq_rawCount tail
      | some result =>
          have isSomeTrue :
              (presentation.certifyNonNull head).isSome = true :=
            congrArg Option.isSome certified
          have nonzeroTrue :
              presentation.normNonzeroAccepted head = true := by
            calc
              presentation.normNonzeroAccepted head =
                  (presentation.certifyNonNull head).isSome :=
                (presentation.certifyNonNull_isSome_eq_normNonzeroAccepted
                  head).symm
              _ = true := isSomeTrue
          rw [List.filterMap_cons_some certified]
          unfold listCountWhere
          rw [List.filter_cons, List.filter_cons, nonzeroTrue,
            Bool.true_and,
            presentation.certifyNonNull_eq_some_toProportion certified]
          cases square : presentation.isSquare head.norm with
          | false =>
              simp only [Bool.false_eq_true, if_false]
              exact certifiedSquareFilter_length_eq_rawCount tail
          | true =>
              exact congrArg Nat.succ
                (certifiedSquareFilter_length_eq_rawCount tail)

private theorem halfSpreadAccepted_one_of_scalar_zero (raw : Proportion K)
    (scalarZero : raw.scalar = 0) :
    presentation.halfSpreadAccepted 1 raw =
      presentation.normNonzeroAccepted raw := by
  letI : DecidableEq K := presentation.eqDecidable
  have normQuadrance : raw.norm = raw.vector.quadrance := by
    unfold Proportion.norm
    rw [scalarZero]
    ring1
  unfold halfSpreadAccepted normNonzeroAccepted
  rw [normQuadrance]
  have equation : raw.vector.quadrance = (1 : K) * raw.vector.quadrance := by
    ring1
  rw [decide_eq_true equation, Bool.and_true]

private theorem halfSpreadAccepted_one_of_scalar_nonzero
    (raw : Proportion K) (scalarNonzero : raw.scalar ≠ 0) :
    presentation.halfSpreadAccepted 1 raw = false := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold halfSpreadAccepted
  apply Bool.eq_false_iff.mpr
  intro accepted
  have acceptedParts := Eq.mp (Bool.and_eq_true _ _) accepted
  have equation := of_decide_eq_true acceptedParts.2
  have normEquation : raw.norm = raw.vector.quadrance := by
    calc
      raw.norm = (1 : K) * raw.norm := by ring1
      _ = raw.vector.quadrance := equation.symm
  have scalarSquareZero : raw.scalar ^ 2 = 0 := by
    unfold Proportion.norm at normEquation
    calc
      raw.scalar ^ 2 =
          (raw.scalar ^ 2 + raw.vector.quadrance) -
            raw.vector.quadrance := by ring1
      _ = raw.vector.quadrance - raw.vector.quadrance :=
        congrArg (fun norm => norm - raw.vector.quadrance) normEquation
      _ = 0 := by ring1
  have scalarSquareNonzero : raw.scalar ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero scalarNonzero scalarNonzero
  exact scalarSquareNonzero scalarSquareZero

/-- Non-null points in the first chart of the projective plane at infinity. -/
def infinityTNonNullCount : Nat := by
  exact listCountWhere presentation.scalarPairs fun pair =>
    presentation.normNonzeroAccepted
      ⟨0, ⟨1, pair.first, pair.second⟩⟩

/-- Non-null points in the second chart of the projective plane at infinity. -/
def infinityRNonNullCount : Nat := by
  exact listCountWhere presentation.carrier fun s =>
    presentation.normNonzeroAccepted ⟨0, ⟨0, 1, s⟩⟩

/-- Non-null proportions in the scalar-one affine chart. -/
def affineNonNullCount : Nat :=
  presentation.vectorCountWhere fun vector =>
    presentation.normNonzeroAccepted ⟨1, vector⟩

private theorem complement_one_add_nonzero (value : K) :
    letI : DecidableEq K := presentation.eqDecidable
    (!decide ((1 : K) + value ≠ 0)) = decide (value = -1) := by
  letI : DecidableEq K := presentation.eqDecidable
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro accepted
    apply decide_eq_true
    have nonzeroDecideFalse := Eq.mp (Bool.not_eq_true' _) accepted
    have notNonzero := decide_eq_false_iff_not.mp nonzeroDecideFalse
    have sumZero := eq_zero_of_not_ne presentation.eqDecidable notNonzero
    calc
      value = (1 + value) - 1 := by ring1
      _ = -1 := by rw [sumZero]; ring1
  · intro accepted
    have valueNegativeOne := of_decide_eq_true accepted
    apply Eq.mpr (Bool.not_eq_true' _)
    apply decide_eq_false
    intro sumNonzero
    apply sumNonzero
    rw [valueNegativeOne]
    ring1

private theorem scalarPairs_length :
    presentation.scalarPairs.length =
      presentation.carrier.length * presentation.carrier.length := by
  unfold scalarPairs
  exact flatMap_map_length presentation.carrier presentation.carrier
    (fun first second => (⟨first, second⟩ : ScalarPair K))

private theorem vectors_length :
    presentation.vectors.length = presentation.carrier.length *
      (presentation.carrier.length * presentation.carrier.length) := by
  unfold vectors
  apply flatMap_length_of_constant presentation.carrier
    (fun t => presentation.carrier.flatMap fun r =>
      presentation.carrier.map fun s => (⟨t, r, s⟩ : Vector K))
    (presentation.carrier.length * presentation.carrier.length)
  intro t _
  exact flatMap_map_length presentation.carrier presentation.carrier
    (fun r s => (⟨t, r, s⟩ : Vector K))

theorem affineNonNullCount_add_excludedAnchorQuadric :
    presentation.affineNonNullCount +
      presentation.excludedAnchorQuadric.length =
        presentation.carrier.length *
          (presentation.carrier.length * presentation.carrier.length) := by
  letI : DecidableEq K := presentation.eqDecidable
  have partition := listCountWhere_add_complementary presentation.vectors
    (fun vector => presentation.normNonzeroAccepted ⟨1, vector⟩)
    (fun vector => decide (vector.quadrance = (-1 : K))) (by
      intro vector _
      unfold normNonzeroAccepted
      have normEquation :
          Proportion.norm (⟨1, vector⟩ : Proportion K) =
            1 + vector.quadrance := by
        unfold Proportion.norm
        ring1
      rw [normEquation]
      exact presentation.complement_one_add_nonzero vector.quadrance)
  have affineAsList : presentation.affineNonNullCount =
      listCountWhere presentation.vectors (fun vector =>
        presentation.normNonzeroAccepted ⟨1, vector⟩) := by
    unfold affineNonNullCount listCountWhere
    exact presentation.vectorCountWhere_eq_length_filter _
  calc
    presentation.affineNonNullCount +
        presentation.excludedAnchorQuadric.length =
      listCountWhere presentation.vectors (fun vector =>
          presentation.normNonzeroAccepted ⟨1, vector⟩) +
        listCountWhere presentation.vectors (fun vector =>
          decide (vector.quadrance = (-1 : K))) := by
            rw [affineAsList]
            rfl
    _ = presentation.vectors.length := partition
    _ = presentation.carrier.length *
        (presentation.carrier.length * presentation.carrier.length) :=
      presentation.vectors_length

theorem infinityTNonNullCount_add_twoSquareCount_minus_one :
    presentation.infinityTNonNullCount +
      presentation.twoSquareCount (-1) =
        presentation.carrier.length * presentation.carrier.length := by
  letI : DecidableEq K := presentation.eqDecidable
  have partition := listCountWhere_add_complementary
    presentation.scalarPairs
    (fun pair => presentation.normNonzeroAccepted
      ⟨0, ⟨1, pair.first, pair.second⟩⟩)
    (fun pair => decide (pair.quadrance = (-1 : K))) (by
      intro pair _
      unfold normNonzeroAccepted
      have normEquation :
          Proportion.norm (⟨0, ⟨1, pair.first, pair.second⟩⟩ :
            Proportion K) = 1 + pair.quadrance := by
        unfold Proportion.norm ScalarPair.quadrance Vector.quadrance Vector.dot
        ring1
      rw [normEquation]
      exact presentation.complement_one_add_nonzero pair.quadrance)
  change presentation.infinityTNonNullCount +
      presentation.twoSquareCount (-1) =
        presentation.scalarPairs.length at partition
  rw [presentation.scalarPairs_length] at partition
  exact partition

theorem infinityRNonNullCount_add_squareRootCount_minus_one :
    presentation.infinityRNonNullCount +
      presentation.squareRootCount (-1) = presentation.carrier.length := by
  letI : DecidableEq K := presentation.eqDecidable
  have partition := listCountWhere_add_complementary presentation.carrier
    (fun s => presentation.normNonzeroAccepted ⟨0, ⟨0, 1, s⟩⟩)
    (fun s => decide (s ^ 2 = (-1 : K))) (by
      intro s _
      unfold normNonzeroAccepted
      have normEquation :
          Proportion.norm (⟨0, ⟨0, 1, s⟩⟩ : Proportion K) =
            1 + s ^ 2 := by
        unfold Proportion.norm Vector.quadrance Vector.dot
        ring1
      rw [normEquation]
      exact presentation.complement_one_add_nonzero (s ^ 2))
  change presentation.infinityRNonNullCount +
      presentation.squareRootCount (-1) = presentation.carrier.length at partition
  exact partition

/-- Efficient executable half-spread fiber count. -/
def halfSpreadFiberCount (value : K) : Nat :=
  presentation.projectiveCountWhere (presentation.halfSpreadAccepted value)

/-- The half-turn fiber is precisely the non-null projective plane at
infinity, decomposed into its three first-nonzero-coordinate charts. -/
theorem halfSpreadFiberCount_one_eq_infinityCounts :
    presentation.halfSpreadFiberCount 1 =
      presentation.infinityTNonNullCount +
        presentation.infinityRNonNullCount + 1 := by
  letI : DecidableEq K := presentation.eqDecidable
  have affineZero :
      presentation.vectorCountWhere (fun vector =>
        presentation.halfSpreadAccepted 1 ⟨1, vector⟩) = 0 := by
    apply presentation.vectorCountWhere_eq_zero_of_reject
    intro vector _
    exact presentation.halfSpreadAccepted_one_of_scalar_nonzero
      ⟨1, vector⟩ (one_ne_zero presentation)
  have infinityTEqual :
      (presentation.carrier.map fun r =>
        presentation.infinityTSliceCountWhere r
          (presentation.halfSpreadAccepted 1)).foldr Nat.add 0 =
        presentation.infinityTNonNullCount := by
    unfold infinityTNonNullCount infinityTSliceCountWhere scalarPairs
    rw [listCountWhere_flatMap]
    apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
    apply QuotientFreeList.map_congr_left
    intro r _
    rw [listCountWhere_map, listCountWhere_map]
    apply listCountWhere_congr
    intro s _
    exact presentation.halfSpreadAccepted_one_of_scalar_zero
      ⟨0, ⟨1, r, s⟩⟩ rfl
  have infinityREqual :
      listCountWhere
          (presentation.carrier.map fun s =>
            (⟨0, ⟨0, 1, s⟩⟩ : Proportion K))
          (presentation.halfSpreadAccepted 1) =
        presentation.infinityRNonNullCount := by
    unfold infinityRNonNullCount
    rw [listCountWhere_map]
    apply listCountWhere_congr
    intro s _
    exact presentation.halfSpreadAccepted_one_of_scalar_zero
      ⟨0, ⟨0, 1, s⟩⟩ rfl
  have infinitySAccepted :
      presentation.halfSpreadAccepted 1 infinitySRepresentative = true := by
    rw [presentation.halfSpreadAccepted_one_of_scalar_zero
      infinitySRepresentative rfl]
    unfold normNonzeroAccepted
    have normEquation :
        Proportion.norm (infinitySRepresentative : Proportion K) = 1 := by
      unfold infinitySRepresentative Proportion.norm Vector.quadrance Vector.dot
      ring1
    rw [normEquation]
    apply decide_eq_true
    exact one_ne_zero presentation
  unfold halfSpreadFiberCount projectiveCountWhere
  rw [affineZero, infinityTEqual, infinityREqual, infinitySAccepted]
  rw [if_pos rfl]
  change 0 + presentation.infinityTNonNullCount +
      presentation.infinityRNonNullCount + 1 = _
  rw [Nat.zero_add]

/-- The projective half-turn fiber also has `q²` elements.  The proof counts
all three charts and handles the split/nonsplit conic at infinity explicitly. -/
theorem halfSpreadFiberCount_one :
    presentation.halfSpreadFiberCount 1 =
      presentation.carrier.length * presentation.carrier.length := by
  have minusOneNonzero : (-1 : K) ≠ 0 := by
    intro minusOneZero
    apply one_ne_zero presentation
    calc
      (1 : K) = -(-1) := by ring1
      _ = 0 := by rw [minusOneZero]; ring1
  rw [presentation.halfSpreadFiberCount_one_eq_infinityCounts]
  cases presentation.classifyMinusOne with
  | square root rootSquare =>
      have tPartition :=
        presentation.infinityTNonNullCount_add_twoSquareCount_minus_one
      have rPartition :=
        presentation.infinityRNonNullCount_add_squareRootCount_minus_one
      rw [presentation.twoSquareCount_of_minus_one_square_of_ne_zero
          (-1) root rootSquare minusOneNonzero] at tPartition
      rw [presentation.squareRootCount_of_nonzero_square
          (-1) root minusOneNonzero rootSquare] at rPartition
      have rPlusOne : presentation.infinityRNonNullCount + 1 =
          presentation.carrier.length - 1 := by
        calc
          presentation.infinityRNonNullCount + 1 =
              ((presentation.infinityRNonNullCount + 1) + 1) - 1 :=
            (Nat.add_sub_cancel
              (presentation.infinityRNonNullCount + 1) 1).symm
          _ = (presentation.infinityRNonNullCount + 2) - 1 := by
            exact congrArg (fun count => count - 1)
              (Nat.add_assoc presentation.infinityRNonNullCount 1 1)
          _ = presentation.carrier.length - 1 :=
            congrArg (fun count => count - 1) rPartition
      calc
        presentation.infinityTNonNullCount +
            presentation.infinityRNonNullCount + 1 =
          presentation.infinityTNonNullCount +
            (presentation.infinityRNonNullCount + 1) :=
              Nat.add_assoc _ _ _
        _ = presentation.infinityTNonNullCount +
            (presentation.carrier.length - 1) :=
          congrArg (Nat.add presentation.infinityTNonNullCount) rPlusOne
        _ = presentation.carrier.length * presentation.carrier.length :=
          tPartition
  | nonsquare minusOneNoRoot =>
      have tPartition :=
        presentation.infinityTNonNullCount_add_twoSquareCount_minus_one
      have rPartition :=
        presentation.infinityRNonNullCount_add_squareRootCount_minus_one
      rw [presentation.twoSquareCount_of_minus_one_nonsquare_of_ne_zero
          (-1) minusOneNonzero minusOneNoRoot] at tPartition
      rw [presentation.squareRootCount_of_nonsquare
          (-1) minusOneNoRoot] at rPartition
      have rCount : presentation.infinityRNonNullCount =
          presentation.carrier.length := by
        calc
          presentation.infinityRNonNullCount =
              presentation.infinityRNonNullCount + 0 :=
            (Nat.add_zero _).symm
          _ = presentation.carrier.length := rPartition
      calc
        presentation.infinityTNonNullCount +
            presentation.infinityRNonNullCount + 1 =
          presentation.infinityTNonNullCount +
            (presentation.infinityRNonNullCount + 1) :=
              Nat.add_assoc _ _ _
        _ = presentation.infinityTNonNullCount +
            (presentation.carrier.length + 1) := by rw [rCount]
        _ = presentation.carrier.length * presentation.carrier.length :=
          tPartition

/-- The non-null projective rotation carrier is the affine non-null chart plus
the three non-null charts at infinity. -/
theorem rotationCount_eq_affineNonNullCount_add_infinityCounts :
    presentation.rotationCount = presentation.affineNonNullCount +
      presentation.infinityTNonNullCount +
        presentation.infinityRNonNullCount + 1 := by
  letI : DecidableEq K := presentation.eqDecidable
  have predicateEqual := presentation.projectiveCountWhere_congr
    (fun raw => (presentation.certifyNonNull raw).isSome)
    presentation.normNonzeroAccepted
    presentation.certifyNonNull_isSome_eq_normNonzeroAccepted
  have infinityTEqual :
      (presentation.carrier.map fun r =>
        presentation.infinityTSliceCountWhere r
          presentation.normNonzeroAccepted).foldr Nat.add 0 =
        presentation.infinityTNonNullCount := by
    unfold infinityTNonNullCount infinityTSliceCountWhere scalarPairs
    rw [listCountWhere_flatMap]
    apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
    apply QuotientFreeList.map_congr_left
    intro r _
    rw [listCountWhere_map, listCountWhere_map]
  have infinityREqual :
      listCountWhere
          (presentation.carrier.map fun s =>
            (⟨0, ⟨0, 1, s⟩⟩ : Proportion K))
          presentation.normNonzeroAccepted =
        presentation.infinityRNonNullCount := by
    unfold infinityRNonNullCount
    rw [listCountWhere_map]
  have infinitySAccepted :
      presentation.normNonzeroAccepted infinitySRepresentative = true := by
    unfold normNonzeroAccepted
    have normEquation :
        Proportion.norm (infinitySRepresentative : Proportion K) = 1 := by
      unfold infinitySRepresentative Proportion.norm Vector.quadrance Vector.dot
      ring1
    rw [normEquation]
    exact decide_eq_true (one_ne_zero presentation)
  calc
    presentation.rotationCount =
        presentation.projectiveCountWhere
          presentation.normNonzeroAccepted := predicateEqual
    _ = presentation.affineNonNullCount +
        presentation.infinityTNonNullCount +
          presentation.infinityRNonNullCount + 1 := by
      unfold projectiveCountWhere affineNonNullCount
      rw [infinityTEqual, infinityREqual, infinitySAccepted, if_pos rfl]

/-- Efficient executable count of the square-norm projective carrier. -/
def quadranceClassKernelCount : Nat := by
  exact presentation.projectiveCountWhere fun raw =>
    presentation.normNonzeroAccepted raw && presentation.isSquare raw.norm

theorem quadranceClassKernelCount_eq_length :
    presentation.quadranceClassKernelCount =
      presentation.quadranceClassKernel.length := by
  unfold quadranceClassKernelCount quadranceClassKernel
    nonNullProjectiveRepresentatives
  rw [presentation.projectiveCountWhere_eq_length_filter]
  exact (certifiedSquareFilter_length_eq_rawCount
    (presentation := presentation)
    presentation.projectiveRepresentatives).symm

theorem quadranceClassKernel_twice_eq_rotationCount :
    presentation.quadranceClassKernel.length +
        presentation.quadranceClassKernel.length =
      presentation.rotationCount := by
  calc
    presentation.quadranceClassKernel.length +
        presentation.quadranceClassKernel.length =
      presentation.quadranceClassKernel.length +
        presentation.quadranceClassNontrivialFiber.length := by
          rw [presentation.quadranceClassKernel_length_eq_nontrivialFiber_length]
    _ = presentation.nonNullProjectiveRepresentatives.length :=
      presentation.quadranceClassFibers_partition
    _ = presentation.rotationEnumeration.values.length := by
      unfold rotationEnumeration RotationEnumeration.values rotations
      rw [List.length_map]
    _ = presentation.rotationCount :=
      presentation.rotationCount_eq_rotationEnumeration_length.symm

/-- Efficient executable count of one affine ternary quadrance fiber. -/
def vectorQuadranceCount (value : K) : Nat := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.vectorCountWhere fun vector =>
    decide (vector.quadrance = value)

private theorem one_sub_ne_zero_of_ne_one_counting {value : K}
    (notOne : value ≠ 1) : 1 - value ≠ 0 := by
  intro differenceZero
  apply notOne
  calc
    value = 1 - (1 - value) := by ring1
    _ = 1 := by rw [differenceZero]; ring1

private theorem minus_one_ne_zero_counting
    (presentation : FiniteOddFieldPresentation K) : (-1 : K) ≠ 0 := by
  intro minusOneZero
  apply one_ne_zero presentation
  calc
    (1 : K) = -(-1) := by ring1
    _ = 0 := by rw [minusOneZero]; ring1

private theorem eq_div_of_mul_eq_counting {left right denominator : K}
    (denominatorNonzero : denominator ≠ 0)
    (product : left * denominator = right) :
    left = right / denominator := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel denominator
    denominatorNonzero
  rw [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    left = left * (denominator * denominator⁻¹) := by rw [cancel, mul_one]
    _ = (left * denominator) * denominator⁻¹ := by ring1
    _ = right * denominator⁻¹ := by rw [product]

private theorem halfSpreadAccepted_count_over_carrier
    (raw : Proportion K) :
    listCountWhere presentation.carrier (fun value =>
        presentation.halfSpreadAccepted value raw) =
      if presentation.normNonzeroAccepted raw then 1 else 0 := by
  letI : DecidableEq K := presentation.eqDecidable
  cases presentation.eqDecidable raw.norm 0 with
  | isTrue normZero =>
      have normRejected : presentation.normNonzeroAccepted raw = false := by
        unfold normNonzeroAccepted
        exact decide_eq_false (fun normNonzero => normNonzero normZero)
      have allRejected : ∀ value ∈ presentation.carrier,
          presentation.halfSpreadAccepted value raw = false := by
        intro value _
        unfold halfSpreadAccepted
        rw [decide_eq_false (fun normNonzero => normNonzero normZero),
          Bool.false_and]
      rw [listCountWhere_eq_zero_of_reject presentation.carrier
        (fun value => presentation.halfSpreadAccepted value raw) allRejected,
        normRejected]
      rfl
  | isFalse normNonzero =>
      let target := raw.vector.quadrance / raw.norm
      have normAccepted : presentation.normNonzeroAccepted raw = true := by
        unfold normNonzeroAccepted
        exact decide_eq_true normNonzero
      have predicateEqual : ∀ value ∈ presentation.carrier,
          presentation.halfSpreadAccepted value raw =
            decide (value = target) := by
        intro value _
        unfold halfSpreadAccepted
        rw [decide_eq_true normNonzero, Bool.true_and]
        apply Bool.eq_iff_iff.mpr
        constructor
        · intro accepted
          apply decide_eq_true
          exact eq_div_of_mul_eq_counting normNonzero
            (of_decide_eq_true accepted).symm
        · intro accepted
          apply decide_eq_true
          have multiplied := congrArg (fun scalar => scalar * raw.norm)
            (of_decide_eq_true accepted)
          change value * raw.norm = target * raw.norm at multiplied
          unfold target at multiplied
          rw [RFAP.ExplicitField.div_mul_cancel raw.vector.quadrance
            normNonzero] at multiplied
          exact multiplied.symm
      have countEqual := listCountWhere_congr presentation.carrier
        (fun value => presentation.halfSpreadAccepted value raw)
        (fun value => decide (value = target)) predicateEqual
      rw [countEqual,
        listCountWhere_eq_one_of_eq_target presentation.eqDecidable
          presentation.carrier presentation.carrierNodup target
          (presentation.carrierComplete target),
        normAccepted]
      rw [if_pos rfl]

/-- The displayed half-spread fibers form a genuine partition of the
rotation carrier.  Their finite sum therefore agrees with the independently
counted group order. -/
theorem halfSpreadFiberCounts_sum :
    (presentation.carrier.map presentation.halfSpreadFiberCount).foldr
        Nat.add 0 = presentation.rotationCount := by
  have countsAsLists :
      presentation.carrier.map presentation.halfSpreadFiberCount =
        presentation.carrier.map fun value =>
          listCountWhere presentation.projectiveRepresentatives
            (presentation.halfSpreadAccepted value) := by
    apply QuotientFreeList.map_congr_left
    intro value _
    unfold halfSpreadFiberCount
    exact presentation.projectiveCountWhere_eq_length_filter _
  have swapped := listCountWhere_sum_swap presentation.carrier
    presentation.projectiveRepresentatives
    (fun value raw => presentation.halfSpreadAccepted value raw)
  have rawCounts :
      presentation.projectiveRepresentatives.map (fun raw =>
          listCountWhere presentation.carrier (fun value =>
            presentation.halfSpreadAccepted value raw)) =
        presentation.projectiveRepresentatives.map (fun raw =>
          if presentation.normNonzeroAccepted raw then 1 else 0) := by
    apply QuotientFreeList.map_congr_left
    intro raw _
    exact presentation.halfSpreadAccepted_count_over_carrier raw
  have rotationAsNorm : presentation.rotationCount =
      presentation.projectiveCountWhere
        presentation.normNonzeroAccepted := by
    unfold rotationCount
    exact presentation.projectiveCountWhere_congr
      (fun raw => (presentation.certifyNonNull raw).isSome)
      presentation.normNonzeroAccepted
      presentation.certifyNonNull_isSome_eq_normNonzeroAccepted
  calc
    (presentation.carrier.map presentation.halfSpreadFiberCount).foldr
        Nat.add 0 =
      (presentation.carrier.map fun value =>
        listCountWhere presentation.projectiveRepresentatives
          (presentation.halfSpreadAccepted value)).foldr Nat.add 0 := by
      rw [countsAsLists]
    _ = (presentation.projectiveRepresentatives.map fun raw =>
        listCountWhere presentation.carrier (fun value =>
          presentation.halfSpreadAccepted value raw)).foldr Nat.add 0 := swapped
    _ = (presentation.projectiveRepresentatives.map fun raw =>
        if presentation.normNonzeroAccepted raw then 1 else 0).foldr
          Nat.add 0 := by rw [rawCounts]
    _ = listCountWhere presentation.projectiveRepresentatives
        presentation.normNonzeroAccepted :=
      (listCountWhere_eq_foldr_indicators
        presentation.projectiveRepresentatives
        presentation.normNonzeroAccepted).symm
    _ = presentation.projectiveCountWhere
        presentation.normNonzeroAccepted :=
      presentation.projectiveCountWhere_eq_length_filter
        presentation.normNonzeroAccepted |>.symm
    _ = presentation.rotationCount := rotationAsNorm.symm

/-- The paper's discriminant differs from `(-1) * h/(1-h)` by the displayed
nonzero square `(1-h)²`. -/
theorem halfSpreadDiscriminant_affine_factorization (value : K)
    (notOne : value ≠ 1) :
    halfSpreadDiscriminant value =
      ((-1 : K) * (value / (1 - value))) * (1 - value) ^ 2 := by
  have complementNonzero := one_sub_ne_zero_of_ne_one_counting notOne
  have complementCancel := RFAP.ExplicitField.mul_inv_cancel
    (1 - value) complementNonzero
  unfold halfSpreadDiscriminant
  rw [RFAP.ExplicitField.div_eq_mul_inv]
  symm
  calc
    ((-1 : K) * (value * (1 - value)⁻¹)) * (1 - value) ^ 2 =
        (-value * (1 - value)) *
          ((1 - value) * (1 - value)⁻¹) := by ring1
    _ = -value * (1 - value) := by rw [complementCancel, mul_one]

/-- Away from the half-turn value, the homogeneous half-spread fiber is the
affine ternary quadric `Q(v) = value / (1 - value)`. -/
theorem halfSpreadFiberCount_eq_vectorQuadranceCount (value : K)
    (notOne : value ≠ 1) :
    presentation.halfSpreadFiberCount value =
      presentation.vectorQuadranceCount (value / (1 - value)) := by
  letI : DecidableEq K := presentation.eqDecidable
  apply presentation.projectiveCountWhere_eq_vectorCountWhere_of_infinity_rejected
  · intro vector
    unfold halfSpreadAccepted
    change
      (decide ((1 : K) ^ 2 + vector.quadrance ≠ 0) &&
        decide (vector.quadrance =
          value * ((1 : K) ^ 2 + vector.quadrance))) =
        decide (vector.quadrance = value / (1 - value))
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro accepted
      apply decide_eq_true
      have acceptedParts := Eq.mp (Bool.and_eq_true _ _) accepted
      have equation := of_decide_eq_true acceptedParts.2
      apply eq_div_of_mul_eq_counting
        (one_sub_ne_zero_of_ne_one_counting notOne)
      calc
        vector.quadrance * (1 - value) =
            vector.quadrance - value * vector.quadrance := by ring1
        _ = value * ((1 : K) ^ 2 + vector.quadrance) -
            value * vector.quadrance :=
          congrArg (fun left => left - value * vector.quadrance) equation
        _ = value := by ring1
    · intro accepted
      have quadranceEquation := of_decide_eq_true accepted
      have complementNonzero := one_sub_ne_zero_of_ne_one_counting notOne
      have complementCancel := RFAP.ExplicitField.mul_inv_cancel
        (1 - value) complementNonzero
      have normEquation :
          (1 : K) ^ 2 + vector.quadrance = (1 - value)⁻¹ := by
        rw [quadranceEquation, RFAP.ExplicitField.div_eq_mul_inv]
        calc
          1 ^ 2 + value * (1 - value)⁻¹ =
              (1 - value) * (1 - value)⁻¹ +
                value * (1 - value)⁻¹ := by rw [complementCancel]; ring1
          _ = (1 - value + value) * (1 - value)⁻¹ := by ring1
          _ = (1 - value)⁻¹ := by ring1
      apply Eq.mpr (Bool.and_eq_true _ _)
      constructor
      · apply decide_eq_true
        rw [normEquation]
        exact RFAP.ExplicitField.inv_ne_zero complementNonzero
      · apply decide_eq_true
        rw [normEquation, quadranceEquation,
          RFAP.ExplicitField.div_eq_mul_inv]
  · intro raw scalarZero
    unfold halfSpreadAccepted
    apply Bool.eq_false_iff.mpr
    intro accepted
    have acceptedParts := Eq.mp (Bool.and_eq_true _ _) accepted
    have normNonzero := of_decide_eq_true acceptedParts.1
    have equation := of_decide_eq_true acceptedParts.2
    have normQuadrance : raw.norm = raw.vector.quadrance := by
      unfold Proportion.norm
      rw [scalarZero]
      ring1
    have equationQuadrance :
        raw.vector.quadrance = value * raw.vector.quadrance := by
      calc
        raw.vector.quadrance = value * raw.norm := equation
        _ = value * raw.vector.quadrance := by rw [normQuadrance]
    have productZero :
        (1 - value) * raw.vector.quadrance = 0 := by
      calc
        (1 - value) * raw.vector.quadrance =
            raw.vector.quadrance - value * raw.vector.quadrance := by ring1
        _ = value * raw.vector.quadrance -
            value * raw.vector.quadrance :=
          congrArg (fun left => left - value * raw.vector.quadrance)
            equationQuadrance
        _ = 0 := by ring1
    have quadranceNonzero : raw.vector.quadrance ≠ 0 := by
      rw [← normQuadrance]
      exact normNonzero
    have productNonzero := RFAP.ExplicitField.mul_ne_zero
      (one_sub_ne_zero_of_ne_one_counting notOne) quadranceNonzero
    exact productNonzero productZero

private theorem halfSpreadQuotient_eq_one_of_scalar_zero
    (proportion : NonNullProportion K)
    (scalarZero : proportion.scalar = 0) :
    proportion.vector.quadrance / proportion.toProportion.norm = 1 := by
  have normEq : proportion.toProportion.norm =
      proportion.vector.quadrance := by
    unfold Proportion.norm
    rw [scalarZero]
    ring1
  have quadranceNonzero : proportion.vector.quadrance ≠ 0 := by
    intro quadranceZero
    apply proportion.normNonzero
    rw [normEq, quadranceZero]
  rw [normEq, RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ExplicitField.mul_inv_cancel _ quadranceNonzero]

/-- A canonical representative in a non-half-turn fiber is necessarily in
the scalar-one affine chart. -/
theorem halfSpreadFiber_scalar_eq_one {value : K}
    (notOne : value ≠ 1) (proportion : NonNullProportion K)
    (member : proportion ∈ presentation.halfSpreadFiber value) :
    proportion.scalar = 1 := by
  letI : DecidableEq K := presentation.eqDecidable
  have filtered := List.mem_filter.mp member
  have fiberEq := of_decide_eq_true filtered.2
  have rawMember := presentation.raw_mem_of_nonNull_mem filtered.1
  have rejectScalarZero (scalarZero : proportion.scalar = 0) : False := by
    apply notOne
    calc
      value = proportion.vector.quadrance /
          proportion.toProportion.norm := fiberEq.symm
      _ = 1 := halfSpreadQuotient_eq_one_of_scalar_zero proportion scalarZero
  rcases presentation.projectiveRepresentatives_cases rawMember with
      ⟨vector, rawEq⟩ |
      ⟨r, s, rawEq⟩ |
      ⟨s, rawEq⟩ | rawEq
  · exact congrArg Proportion.scalar rawEq
  · apply False.elim
    apply rejectScalarZero
    exact congrArg Proportion.scalar rawEq
  · apply False.elim
    apply rejectScalarZero
    exact congrArg Proportion.scalar rawEq
  · apply False.elim
    apply rejectScalarZero
    exact congrArg Proportion.scalar rawEq

/-- Elementwise homogeneous-to-affine reduction for a non-half-turn fiber. -/
theorem halfSpreadFiber_quadrance_eq_affineValue {value : K}
    (notOne : value ≠ 1) (proportion : NonNullProportion K)
    (member : proportion ∈ presentation.halfSpreadFiber value) :
    proportion.vector.quadrance = value / (1 - value) := by
  letI : DecidableEq K := presentation.eqDecidable
  have filtered := List.mem_filter.mp member
  have fiberEq := of_decide_eq_true filtered.2
  have scalarOne := presentation.halfSpreadFiber_scalar_eq_one notOne
    proportion member
  have normEq : proportion.toProportion.norm =
      1 + proportion.vector.quadrance := by
    unfold Proportion.norm
    rw [scalarOne]
    ring1
  have dividedCancel := RFAP.ExplicitField.div_mul_cancel
    proportion.vector.quadrance proportion.normNonzero
  have quadranceEqProduct : proportion.vector.quadrance =
      value * proportion.toProportion.norm := by
    calc
      proportion.vector.quadrance =
          (proportion.vector.quadrance /
            proportion.toProportion.norm) *
              proportion.toProportion.norm := dividedCancel.symm
      _ = value * proportion.toProportion.norm := by rw [fiberEq]
  have product : proportion.vector.quadrance * (1 - value) = value := by
    calc
      proportion.vector.quadrance * (1 - value) =
          proportion.vector.quadrance -
            value * proportion.vector.quadrance := by ring1
      _ = value * proportion.toProportion.norm -
            value * proportion.vector.quadrance := by rw [quadranceEqProduct]
      _ = value * (1 + proportion.vector.quadrance) -
            value * proportion.vector.quadrance := by rw [normEq]
      _ = value := by ring1
  exact eq_div_of_mul_eq_counting
    (one_sub_ne_zero_of_ne_one_counting notOne) product

private theorem affineQuadric_member_halfSpreadFiber {value : K}
    (notOne : value ≠ 1) (proportion : NonNullProportion K)
    (member : proportion ∈ presentation.affineQuadricRepresentatives
      (value / (1 - value))) :
    proportion ∈ presentation.halfSpreadFiber value := by
  letI : DecidableEq K := presentation.eqDecidable
  have classified :=
    (presentation.mem_affineQuadricRepresentatives_iff
      (value / (1 - value)) proportion).1 member
  have normEq : proportion.toProportion.norm =
      1 + proportion.vector.quadrance := by
    unfold Proportion.norm
    rw [classified.2.1]
    ring1
  have complementNonzero := one_sub_ne_zero_of_ne_one_counting notOne
  have quotientCancel := RFAP.ExplicitField.div_mul_cancel value
    complementNonzero
  have quadranceComplement :
      proportion.vector.quadrance * (1 - value) = value := by
    rw [classified.2.2]
    exact quotientCancel
  have valueTimesNorm : value * proportion.toProportion.norm =
      proportion.vector.quadrance := by
    rw [normEq]
    calc
      value * (1 + proportion.vector.quadrance) =
          value + value * proportion.vector.quadrance := by ring1
      _ = proportion.vector.quadrance * (1 - value) +
            value * proportion.vector.quadrance := by
          rw [quadranceComplement]
      _ = proportion.vector.quadrance := by ring1
  have quotientEq := eq_div_of_mul_eq_counting proportion.normNonzero
    valueTimesNorm
  unfold halfSpreadFiber
  apply List.mem_filter.mpr
  exact ⟨classified.1, decide_eq_true quotientEq.symm⟩

/-- Explicit finite-list bijection from every non-half-turn rotation fiber to
the independently filtered affine quadric `Q(v) = h/(1-h)`.  The maps are
identity on the cached normalized representatives; the proof establishes
that the two independently defined lists have exactly the same members. -/
def affineHalfSpreadFiberBijection (value : K) (notOne : value ≠ 1) :
    FiniteListBijection (presentation.halfSpreadFiber value)
      (presentation.affineQuadricRepresentatives
        (value / (1 - value))) where
  forward := fun proportion => proportion
  backward := fun proportion => proportion
  forward_mem := by
    intro proportion member
    apply (presentation.mem_affineQuadricRepresentatives_iff
      (value / (1 - value)) proportion).2
    have filtered := List.mem_filter.mp member
    exact
      ⟨filtered.1,
        presentation.halfSpreadFiber_scalar_eq_one notOne proportion member,
        presentation.halfSpreadFiber_quadrance_eq_affineValue notOne
          proportion member⟩
  backward_mem := fun proportion member =>
    presentation.affineQuadric_member_halfSpreadFiber notOne proportion member
  backward_forward := by intro _ _; rfl
  forward_backward := by intro _ _; rfl

/-- In the half-turn fiber, the homogeneous equation forces scalar coordinate
zero, so the representative is an axis in the projective plane at infinity. -/
theorem halfSpreadFiber_one_scalar_eq_zero
    (proportion : NonNullProportion K)
    (member : proportion ∈ presentation.halfSpreadFiber 1) :
    proportion.scalar = 0 := by
  letI : DecidableEq K := presentation.eqDecidable
  have filtered := List.mem_filter.mp member
  have fiberEq := of_decide_eq_true filtered.2
  have dividedCancel := RFAP.ExplicitField.div_mul_cancel
    proportion.vector.quadrance proportion.normNonzero
  have quadranceEqNorm : proportion.vector.quadrance =
      proportion.toProportion.norm := by
    calc
      proportion.vector.quadrance =
          (proportion.vector.quadrance /
            proportion.toProportion.norm) *
              proportion.toProportion.norm := dividedCancel.symm
      _ = 1 * proportion.toProportion.norm := by rw [fiberEq]
      _ = proportion.toProportion.norm := by ring1
  have scalarSquareZero : proportion.scalar ^ 2 = 0 := by
    calc
      proportion.scalar ^ 2 = proportion.toProportion.norm -
          proportion.vector.quadrance := by
        unfold Proportion.norm
        ring1
      _ = proportion.vector.quadrance -
          proportion.vector.quadrance := by rw [← quadranceEqNorm]
      _ = 0 := by ring1
  exact ScalarPair.eq_zero_of_square_eq_zero presentation.eqDecidable
    proportion.scalar scalarSquareZero

private theorem projectiveAxis_member_halfSpreadFiber_one
    (proportion : NonNullProportion K)
    (member : proportion ∈
      presentation.projectiveNonNullAxisRepresentatives) :
    proportion ∈ presentation.halfSpreadFiber 1 := by
  letI : DecidableEq K := presentation.eqDecidable
  have classified :=
    (presentation.mem_projectiveNonNullAxisRepresentatives_iff
      proportion).1 member
  unfold halfSpreadFiber
  apply List.mem_filter.mpr
  exact
    ⟨classified.1,
      decide_eq_true
        (halfSpreadQuotient_eq_one_of_scalar_zero proportion classified.2)⟩

/-- Explicit bijection between the half-turn stratum and the independently
listed non-null projective axes (the projective plane at infinity with its
null conic removed). -/
def halfTurnProjectiveAxisBijection :
    FiniteListBijection (presentation.halfSpreadFiber 1)
      presentation.projectiveNonNullAxisRepresentatives where
  forward := fun proportion => proportion
  backward := fun proportion => proportion
  forward_mem := by
    intro proportion member
    apply (presentation.mem_projectiveNonNullAxisRepresentatives_iff
      proportion).2
    have filtered := List.mem_filter.mp member
    exact
      ⟨filtered.1,
        presentation.halfSpreadFiber_one_scalar_eq_zero proportion member⟩
  backward_mem := fun proportion member =>
    presentation.projectiveAxis_member_halfSpreadFiber_one proportion member
  backward_forward := by intro _ _; rfl
  forward_backward := by intro _ _; rfl

/-- Membership in the projective fiber computes the same half-spread value on
the represented rotation. -/
theorem halfSpread_rotation_eq_value_of_mem (value : K)
    (proportion : NonNullProportion K)
    (member : proportion ∈ presentation.halfSpreadFiber value) :
    halfSpread proportion.rotation = value := by
  letI : DecidableEq K := presentation.eqDecidable
  have filtered := List.mem_filter.mp member
  rw [NonNullProportion.halfSpread_rotation proportion
    presentation.twoNonzero]
  exact of_decide_eq_true filtered.2

/-- Under the zero-fiber affine-quadric bijection, the identity is exactly the
quadric origin. -/
theorem zeroFiber_rotation_identity_iff_vector_eq_zero
    (proportion : NonNullProportion K)
    (member : proportion ∈ presentation.halfSpreadFiber 0) :
    proportion.rotation.matrix = Matrix3.identity ↔
      proportion.vector = Vector.zero := by
  letI : DecidableEq K := presentation.eqDecidable
  have zeroNotOne : (0 : K) ≠ 1 := by
    intro zeroOne
    exact one_ne_zero presentation zeroOne.symm
  have scalarOne := presentation.halfSpreadFiber_scalar_eq_one zeroNotOne
    proportion member
  have scalarNonzero : proportion.scalar ≠ 0 := by
    rw [scalarOne]
    exact one_ne_zero presentation
  have oneInverse : (1 : K)⁻¹ = 1 := by
    have cancel := RFAP.ExplicitField.mul_inv_cancel (1 : K)
      (one_ne_zero presentation)
    simpa only [one_mul] using cancel
  have vectorNull : proportion.vector.quadrance = 0 := by
    simpa only [RFAP.ExplicitField.zero_div] using
      presentation.halfSpreadFiber_quadrance_eq_affineValue zeroNotOne
        proportion member
  let vectorDefined :=
    presentation.capDenominator_ne_zero_of_null_counting
      proportion.vector vectorNull
  have matrixCap : proportion.rotation.matrix =
      cap proportion.vector vectorDefined := by
    change proportion.rotationMatrix = cap proportion.vector vectorDefined
    calc
      proportion.rotationMatrix =
          cap (Vector.scale proportion.scalar⁻¹ proportion.vector)
            (reciprocalAnchorCapDefined proportion.scalar proportion.vector
              scalarNonzero proportion.normNonzero) :=
        NonNullProportion.rotationMatrix_eq_cap proportion scalarNonzero
      _ = cap proportion.vector vectorDefined := by
        congr 1
        rw [scalarOne, oneInverse, Vector.one_scale]
  constructor
  · intro matrixIdentity
    apply cap_injective presentation.twoNonzero proportion.vector Vector.zero
      vectorDefined
      (presentation.capDenominator_ne_zero_of_null_counting
        Vector.zero Vector.quadrance_zero)
    calc
      cap proportion.vector vectorDefined = proportion.rotation.matrix :=
        matrixCap.symm
      _ = Matrix3.identity := matrixIdentity
      _ = cap Vector.zero
          (presentation.capDenominator_ne_zero_of_null_counting
            Vector.zero Vector.quadrance_zero) :=
        presentation.cap_zero_eq_identity_counting.symm
  · intro vectorZero
    calc
      proportion.rotation.matrix = cap proportion.vector vectorDefined :=
        matrixCap
      _ = cap Vector.zero
          (presentation.capDenominator_ne_zero_of_null_counting
            Vector.zero Vector.quadrance_zero) :=
        cap_eq_of_vector_eq_counting vectorZero _ _
      _ = Matrix3.identity := presentation.cap_zero_eq_identity_counting

/-- The complementary points of the zero affine quadric are exactly the
nonidentity parabolic stratum. -/
theorem zeroFiber_rotation_nonidentity_iff_vector_ne_zero
    (proportion : NonNullProportion K)
    (member : proportion ∈ presentation.halfSpreadFiber 0) :
    proportion.rotation.matrix ≠ Matrix3.identity ↔
      proportion.vector ≠ Vector.zero := by
  constructor
  · intro matrixNonidentity vectorZero
    exact matrixNonidentity
      ((presentation.zeroFiber_rotation_identity_iff_vector_eq_zero
        proportion member).2 vectorZero)
  · intro vectorNonzero matrixIdentity
    exact vectorNonzero
      ((presentation.zeroFiber_rotation_identity_iff_vector_eq_zero
        proportion member).1 matrixIdentity)

/-- Every genuine middle affine quadric is precisely a semisimple rotation
fiber: its represented rotations have half spread different from both
endpoints. -/
theorem middleFiber_rotation_semisimple {value : K}
    (valueNonzero : value ≠ 0) (notOne : value ≠ 1)
    (proportion : NonNullProportion K)
    (member : proportion ∈ presentation.halfSpreadFiber value) :
    halfSpread proportion.rotation ≠ 0 ∧
      halfSpread proportion.rotation ≠ 1 := by
  have spreadEq := presentation.halfSpread_rotation_eq_value_of_mem value
    proportion member
  constructor
  · intro spreadZero
    apply valueNonzero
    exact spreadEq.symm.trans spreadZero
  · intro spreadOne
    apply notOne
    exact spreadEq.symm.trans spreadOne

/-- Every point of the projective-axis quadric complement represents a
half-turn rotation. -/
theorem projectiveAxis_rotation_halfTurn
    (proportion : NonNullProportion K)
    (member : proportion ∈
      presentation.projectiveNonNullAxisRepresentatives) :
    halfSpread proportion.rotation = 1 := by
  exact presentation.halfSpread_rotation_eq_value_of_mem 1 proportion
    (presentation.projectiveAxis_member_halfSpreadFiber_one proportion member)

theorem vectorQuadranceCount_eq_ternaryQuadranceSlicedCount (value : K) :
    presentation.vectorQuadranceCount value =
      presentation.ternaryQuadranceSlicedCount value := by
  unfold vectorQuadranceCount vectorCountWhere ternaryQuadranceSlicedCount
  apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
  apply QuotientFreeList.map_congr_left
  intro t _
  exact presentation.vectorSliceQuadranceCount_eq_twoSquareCount t value

theorem vectorQuadranceCount_zero :
    presentation.vectorQuadranceCount 0 =
      presentation.carrier.length * presentation.carrier.length := by
  rw [presentation.vectorQuadranceCount_eq_ternaryQuadranceSlicedCount]
  exact presentation.ternaryQuadranceSlicedCount_zero

theorem vectorQuadranceCount_of_split_square
    (value minusOneRoot valueRoot : K) (valueNonzero : value ≠ 0)
    (minusOneSquare : minusOneRoot ^ 2 = -1)
    (valueSquare : valueRoot ^ 2 = value) :
    presentation.vectorQuadranceCount value =
      presentation.carrier.length * presentation.carrier.length +
        presentation.carrier.length := by
  rw [presentation.vectorQuadranceCount_eq_ternaryQuadranceSlicedCount]
  exact presentation.ternaryQuadranceSlicedCount_of_split_square
    value minusOneRoot valueRoot valueNonzero minusOneSquare valueSquare

theorem vectorQuadranceCount_of_split_nonsquare
    (value minusOneRoot : K) (minusOneSquare : minusOneRoot ^ 2 = -1)
    (valueNoRoot : ∀ root : K, root ^ 2 ≠ value) :
    presentation.vectorQuadranceCount value =
      presentation.carrier.length * presentation.carrier.length -
        presentation.carrier.length := by
  rw [presentation.vectorQuadranceCount_eq_ternaryQuadranceSlicedCount]
  exact presentation.ternaryQuadranceSlicedCount_of_split_nonsquare
    value minusOneRoot minusOneSquare valueNoRoot

theorem vectorQuadranceCount_of_nonsplit_square
    (value valueRoot : K) (valueNonzero : value ≠ 0)
    (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
    (valueSquare : valueRoot ^ 2 = value) :
    presentation.vectorQuadranceCount value =
      presentation.carrier.length * presentation.carrier.length -
        presentation.carrier.length := by
  rw [presentation.vectorQuadranceCount_eq_ternaryQuadranceSlicedCount]
  exact presentation.ternaryQuadranceSlicedCount_of_nonsplit_square
    value valueRoot valueNonzero minusOneNoRoot valueSquare

theorem vectorQuadranceCount_of_nonsplit_nonsquare
    (value : K) (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
    (valueNoRoot : ∀ root : K, root ^ 2 ≠ value) :
    presentation.vectorQuadranceCount value =
      presentation.carrier.length * presentation.carrier.length +
        presentation.carrier.length := by
  rw [presentation.vectorQuadranceCount_eq_ternaryQuadranceSlicedCount]
  exact presentation.ternaryQuadranceSlicedCount_of_nonsplit_nonsquare
    value minusOneNoRoot valueNoRoot

/-- The identity/parabolic half-spread fiber always has `q²` elements. -/
theorem halfSpreadFiberCount_zero :
    presentation.halfSpreadFiberCount 0 =
      presentation.carrier.length * presentation.carrier.length := by
  have zeroNotOne : (0 : K) ≠ 1 := by
    intro zeroOne
    exact one_ne_zero presentation zeroOne.symm
  rw [presentation.halfSpreadFiberCount_eq_vectorQuadranceCount 0 zeroNotOne,
    RFAP.ExplicitField.zero_div, presentation.vectorQuadranceCount_zero]

/-- Exhaustive constructive count classification for a half-spread value
other than the half-turn endpoint.  The four nonzero branches retain the
displayed square witnesses (or rejecting functions) for both `-1` and the
affine value `h/(1-h)`. -/
inductive NonHalfTurnFiberCountClassification (value : K) where
  | zero (valueZero : value = 0)
      (count : presentation.halfSpreadFiberCount value =
        presentation.carrier.length * presentation.carrier.length)
  | splitSquare (valueNonzero : value ≠ 0)
      (minusOneRoot affineRoot : K)
      (minusOneSquare : minusOneRoot ^ 2 = -1)
      (affineSquare : affineRoot ^ 2 = value / (1 - value))
      (count : presentation.halfSpreadFiberCount value =
        presentation.carrier.length * presentation.carrier.length +
          presentation.carrier.length)
  | splitNonsquare (valueNonzero : value ≠ 0)
      (minusOneRoot : K) (minusOneSquare : minusOneRoot ^ 2 = -1)
      (affineNoRoot : ∀ root : K,
        root ^ 2 ≠ value / (1 - value))
      (count : presentation.halfSpreadFiberCount value =
        presentation.carrier.length * presentation.carrier.length -
          presentation.carrier.length)
  | nonsplitSquare (valueNonzero : value ≠ 0)
      (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
      (affineRoot : K)
      (affineSquare : affineRoot ^ 2 = value / (1 - value))
      (count : presentation.halfSpreadFiberCount value =
        presentation.carrier.length * presentation.carrier.length -
          presentation.carrier.length)
  | nonsplitNonsquare (valueNonzero : value ≠ 0)
      (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
      (affineNoRoot : ∀ root : K,
        root ^ 2 ≠ value / (1 - value))
      (count : presentation.halfSpreadFiberCount value =
        presentation.carrier.length * presentation.carrier.length +
          presentation.carrier.length)

/-- Compute the exact non-half-turn fiber regime from the cached finite square
tables. -/
def classifyNonHalfTurnFiberCount (value : K) (notOne : value ≠ 1) :
    presentation.NonHalfTurnFiberCountClassification value := by
  let affineValue := value / (1 - value)
  have reduction :=
    presentation.halfSpreadFiberCount_eq_vectorQuadranceCount value notOne
  have vectorSliced :=
    presentation.vectorQuadranceCount_eq_ternaryQuadranceSlicedCount affineValue
  cases presentation.classifyTernaryQuadranceCount affineValue with
  | zero affineZero count =>
      have valueZero : value = 0 := by
        have multiplied := congrArg (fun scalar => scalar * (1 - value))
          affineZero
        change value / (1 - value) * (1 - value) =
          0 * (1 - value) at multiplied
        rw [RFAP.ExplicitField.div_mul_cancel value
          (one_sub_ne_zero_of_ne_one_counting notOne), zero_mul] at multiplied
        exact multiplied
      exact NonHalfTurnFiberCountClassification.zero valueZero (by
        rw [valueZero]
        exact presentation.halfSpreadFiberCount_zero)
  | splitSquare affineNonzero minusOneRoot affineRoot minusOneSquare
      affineSquare count =>
      have valueNonzero : value ≠ 0 := by
        intro valueZero
        apply affineNonzero
        change value / (1 - value) = 0
        rw [valueZero, RFAP.ExplicitField.zero_div]
      exact NonHalfTurnFiberCountClassification.splitSquare valueNonzero
        minusOneRoot affineRoot minusOneSquare affineSquare
        (reduction.trans (vectorSliced.trans count))
  | splitNonsquare affineNonzero minusOneRoot minusOneSquare affineNoRoot
      count =>
      have valueNonzero : value ≠ 0 := by
        intro valueZero
        apply affineNonzero
        change value / (1 - value) = 0
        rw [valueZero, RFAP.ExplicitField.zero_div]
      exact NonHalfTurnFiberCountClassification.splitNonsquare valueNonzero
        minusOneRoot minusOneSquare affineNoRoot
        (reduction.trans (vectorSliced.trans count))
  | nonsplitSquare affineNonzero minusOneNoRoot affineRoot affineSquare
      count =>
      have valueNonzero : value ≠ 0 := by
        intro valueZero
        apply affineNonzero
        change value / (1 - value) = 0
        rw [valueZero, RFAP.ExplicitField.zero_div]
      exact NonHalfTurnFiberCountClassification.nonsplitSquare valueNonzero
        minusOneNoRoot affineRoot affineSquare
        (reduction.trans (vectorSliced.trans count))
  | nonsplitNonsquare affineNonzero minusOneNoRoot affineNoRoot count =>
      have valueNonzero : value ≠ 0 := by
        intro valueZero
        apply affineNonzero
        change value / (1 - value) = 0
        rw [valueZero, RFAP.ExplicitField.zero_div]
      exact NonHalfTurnFiberCountClassification.nonsplitNonsquare valueNonzero
        minusOneNoRoot affineNoRoot
        (reduction.trans (vectorSliced.trans count))

/-- The paper-facing two-case classification for a genuine middle
half-spread value.  A square discriminant gives the large fiber and a
nonsquare discriminant gives the small fiber. -/
inductive MiddleHalfSpreadFiberCountClassification (value : K) where
  | large (discriminantRoot : K)
      (discriminantSquare : discriminantRoot ^ 2 =
        halfSpreadDiscriminant value)
      (count : presentation.halfSpreadFiberCount value =
        presentation.carrier.length * presentation.carrier.length +
          presentation.carrier.length)
  | small (discriminantNoRoot : ∀ root : K,
      root ^ 2 ≠ halfSpreadDiscriminant value)
      (count : presentation.halfSpreadFiberCount value =
        presentation.carrier.length * presentation.carrier.length -
          presentation.carrier.length)

/-- Compute the `q²+q`/`q²-q` regime directly from the square class of
`-h(1-h)`. -/
def classifyMiddleHalfSpreadFiberCount (value : K)
    (valueNonzero : value ≠ 0) (notOne : value ≠ 1) :
    presentation.MiddleHalfSpreadFiberCountClassification value := by
  let affineValue := value / (1 - value)
  let complement := 1 - value
  have complementNonzero := one_sub_ne_zero_of_ne_one_counting notOne
  change complement ≠ 0 at complementNonzero
  have complementSquareNonzero : complement ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero complementNonzero complementNonzero
  have factorization :=
    halfSpreadDiscriminant_affine_factorization value notOne
  change halfSpreadDiscriminant value =
    ((-1 : K) * affineValue) * complement ^ 2 at factorization
  cases presentation.classifyNonHalfTurnFiberCount value notOne with
  | zero valueZero _ =>
      exact False.elim (valueNonzero valueZero)
  | splitSquare _ minusOneRoot affineRoot minusOneSquare affineSquare count =>
      refine MiddleHalfSpreadFiberCountClassification.large
        (minusOneRoot * affineRoot * complement) ?_ count
      calc
        (minusOneRoot * affineRoot * complement) ^ 2 =
            minusOneRoot ^ 2 * affineRoot ^ 2 * complement ^ 2 := by ring1
        _ =
            ((-1 : K) * affineValue) * complement ^ 2 := by
          rw [minusOneSquare, affineSquare]
        _ = halfSpreadDiscriminant value := factorization.symm
  | splitNonsquare _ minusOneRoot minusOneSquare affineNoRoot count =>
      let squareValue := (-1 : K) * complement ^ 2
      have squareValueNonzero : squareValue ≠ 0 :=
        RFAP.ExplicitField.mul_ne_zero
          (minus_one_ne_zero_counting presentation) complementSquareNonzero
      have squareEquation : (minusOneRoot * complement) ^ 2 = squareValue := by
        unfold squareValue
        calc
          (minusOneRoot * complement) ^ 2 =
              minusOneRoot ^ 2 * complement ^ 2 := by ring1
          _ = (-1 : K) * complement ^ 2 := by rw [minusOneSquare]
      have productNoRoot := square_mul_nonsquare_noRoot squareValue
        (minusOneRoot * complement) affineValue squareValueNonzero
        squareEquation affineNoRoot
      refine MiddleHalfSpreadFiberCountClassification.small ?_ count
      intro root rootSquare
      apply productNoRoot root
      calc
        root ^ 2 = halfSpreadDiscriminant value := rootSquare
        _ = squareValue * affineValue := by
          rw [factorization]
          unfold squareValue
          ring1
  | nonsplitSquare _ minusOneNoRoot affineRoot affineSquare count =>
      let squareValue := affineValue * complement ^ 2
      have affineNonzero : affineValue ≠ 0 := by
        unfold affineValue
        exact RFAP.ExplicitField.div_ne_zero valueNonzero complementNonzero
      have squareValueNonzero : squareValue ≠ 0 :=
        RFAP.ExplicitField.mul_ne_zero affineNonzero complementSquareNonzero
      have squareEquation : (affineRoot * complement) ^ 2 = squareValue := by
        unfold squareValue
        calc
          (affineRoot * complement) ^ 2 =
              affineRoot ^ 2 * complement ^ 2 := by ring1
          _ = affineValue * complement ^ 2 := by rw [affineSquare]
      have productNoRoot := square_mul_nonsquare_noRoot squareValue
        (affineRoot * complement) (-1) squareValueNonzero squareEquation
        minusOneNoRoot
      refine MiddleHalfSpreadFiberCountClassification.small ?_ count
      intro root rootSquare
      apply productNoRoot root
      calc
        root ^ 2 = halfSpreadDiscriminant value := rootSquare
        _ = squareValue * (-1 : K) := by
          rw [factorization]
          unfold squareValue
          ring1
  | nonsplitNonsquare _ minusOneNoRoot affineNoRoot count =>
      let witness := presentation.nonsquareMulNonsquareSquareWitness
        (-1) affineValue minusOneNoRoot affineNoRoot
      refine MiddleHalfSpreadFiberCountClassification.large
        (witness.root * complement) ?_ count
      calc
        (witness.root * complement) ^ 2 =
            witness.root ^ 2 * complement ^ 2 := by ring1
        _ =
            ((-1 : K) * affineValue) * complement ^ 2 := by
          rw [witness.equation]
        _ = halfSpreadDiscriminant value := factorization.symm

theorem nullVectors_nodup : presentation.nullVectors.Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold nullVectors
  exact presentation.vectors_nodup.filter _

theorem zero_mem_nullVectors :
    (Vector.zero : Vector K) ∈ presentation.nullVectors := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold nullVectors
  rw [List.mem_filter]
  simp only [decide_eq_true_eq]
  constructor
  · exact presentation.vectors_complete Vector.zero
  · unfold Vector.zero Vector.quadrance Vector.dot
    ring1

theorem nonzeroNullVectors_eq_filter_nullVectors :
    presentation.nonzeroNullVectors = by
      letI : DecidableEq K := presentation.eqDecidable
      exact presentation.nullVectors.filter fun vector => vector ≠ Vector.zero := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold nonzeroNullVectors nullVectors
  exact filter_and_eq_filter_filter presentation.vectors
    (fun vector => decide (vector.quadrance = 0))
    (fun vector => decide (vector ≠ Vector.zero))

theorem nonzeroNullVectors_length_add_one :
    presentation.nonzeroNullVectors.length + 1 =
      presentation.nullVectors.length := by
  letI : DecidableEq K := presentation.eqDecidable
  rw [presentation.nonzeroNullVectors_eq_filter_nullVectors]
  exact filter_ne_target_length_add_one
    (inferInstanceAs (DecidableEq (Vector K))) Vector.zero
    presentation.nullVectors_nodup presentation.zero_mem_nullVectors

theorem nullVectors_length_eq_vectorQuadranceCount_zero :
    presentation.nullVectors.length = presentation.vectorQuadranceCount 0 := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold nullVectors vectorQuadranceCount
  rw [presentation.vectorCountWhere_eq_length_filter]

theorem excludedAnchorQuadric_length_eq_vectorQuadranceCount :
    presentation.excludedAnchorQuadric.length =
      presentation.vectorQuadranceCount (-1) := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold excludedAnchorQuadric vectorQuadranceCount
  rw [presentation.vectorCountWhere_eq_length_filter]

private theorem minus_one_ne_zero
    (presentation : FiniteOddFieldPresentation K) : (-1 : K) ≠ 0 := by
  intro minusOneZero
  apply one_ne_zero presentation
  calc
    (1 : K) = -(-1) := by ring1
    _ = 0 := by rw [minusOneZero]; ring1

theorem excludedAnchorQuadric_length :
    presentation.excludedAnchorQuadric.length =
      presentation.carrier.length * presentation.carrier.length +
        presentation.carrier.length := by
  rw [presentation.excludedAnchorQuadric_length_eq_vectorQuadranceCount]
  cases presentation.classifyMinusOne with
  | square root rootSquare =>
      exact presentation.vectorQuadranceCount_of_split_square
        (-1) root root (minus_one_ne_zero presentation) rootSquare rootSquare
  | nonsquare minusOneNoRoot =>
      exact presentation.vectorQuadranceCount_of_nonsplit_nonsquare
        (-1) minusOneNoRoot minusOneNoRoot

/-- The excluded projective norm quadric, counted chart by chart: the affine
piece `Q(v) = -1`, followed by the two null charts at infinity.  The final
infinity point has norm one and contributes nothing. -/
def excludedProjectiveQuadricCount : Nat :=
  presentation.excludedAnchorQuadric.length +
    presentation.twoSquareCount (-1) + presentation.squareRootCount (-1)

private theorem infinityNullQuadricCount :
    presentation.twoSquareCount (-1) +
        presentation.squareRootCount (-1) =
      presentation.carrier.length + 1 := by
  have minusOneNonzero := minus_one_ne_zero presentation
  cases presentation.classifyMinusOne with
  | square root rootSquare =>
      rw [presentation.twoSquareCount_of_minus_one_square_of_ne_zero
          (-1) root rootSquare minusOneNonzero,
        presentation.squareRootCount_of_nonzero_square
          (-1) root minusOneNonzero rootSquare]
      have oneLe : 1 ≤ presentation.carrier.length :=
        List.length_pos_of_mem (presentation.carrierComplete 0)
      calc
        presentation.carrier.length - 1 + 2 =
            (presentation.carrier.length - 1 + 1) + 1 := by ring1
        _ = presentation.carrier.length + 1 := by
          rw [Nat.sub_add_cancel oneLe]
  | nonsquare minusOneNoRoot =>
      rw [presentation.twoSquareCount_of_minus_one_nonsquare_of_ne_zero
          (-1) minusOneNonzero minusOneNoRoot,
        presentation.squareRootCount_of_nonsquare (-1) minusOneNoRoot,
        Nat.add_zero]

/-- The projective null conic has exactly `q+1` canonical displayed
directions, independently of the square class of `-1`. -/
theorem nullDirectionRepresentatives_length :
    presentation.nullDirectionRepresentatives.length =
      presentation.carrier.length + 1 := by
  unfold nullDirectionRepresentatives
  rw [List.length_append, List.length_map, List.length_map]
  change presentation.twoSquareCount (-1) +
      presentation.squareRootCount (-1) = presentation.carrier.length + 1
  exact presentation.infinityNullQuadricCount

theorem excludedProjectiveQuadricCount_formula :
    presentation.excludedProjectiveQuadricCount =
      (presentation.carrier.length + 1) *
        (presentation.carrier.length + 1) := by
  unfold excludedProjectiveQuadricCount
  rw [presentation.excludedAnchorQuadric_length]
  calc
    presentation.carrier.length * presentation.carrier.length +
          presentation.carrier.length +
          presentation.twoSquareCount (-1) +
        presentation.squareRootCount (-1) =
      (presentation.carrier.length * presentation.carrier.length +
        presentation.carrier.length) +
        (presentation.twoSquareCount (-1) +
          presentation.squareRootCount (-1)) := by ring1
    _ = (presentation.carrier.length * presentation.carrier.length +
        presentation.carrier.length) +
        (presentation.carrier.length + 1) := by
      rw [presentation.infinityNullQuadricCount]
    _ = (presentation.carrier.length + 1) *
        (presentation.carrier.length + 1) := by ring1

private theorem nat_eq_sub_of_add_eq_counting
    {left subtracted total : Nat} (added : left + subtracted = total) :
    left = total - subtracted := by
  calc
    left = (left + subtracted) - subtracted :=
      (Nat.add_sub_cancel left subtracted).symm
    _ = total - subtracted :=
      congrArg (fun count => count - subtracted) added

/-- The complete explicit rotation carrier has the classical order
`q(q²-1)`, proved from the affine excluded quadric and the independently
counted projective plane at infinity. -/
theorem rotationCount_formula :
    presentation.rotationCount = presentation.carrier.length *
      (presentation.carrier.length * presentation.carrier.length - 1) := by
  have infinityCount : presentation.infinityTNonNullCount +
      presentation.infinityRNonNullCount + 1 =
        presentation.carrier.length * presentation.carrier.length := by
    calc
      presentation.infinityTNonNullCount +
          presentation.infinityRNonNullCount + 1 =
        presentation.halfSpreadFiberCount 1 :=
          presentation.halfSpreadFiberCount_one_eq_infinityCounts.symm
      _ = presentation.carrier.length * presentation.carrier.length :=
        presentation.halfSpreadFiberCount_one
  have rotationAsAffine : presentation.rotationCount =
      presentation.affineNonNullCount +
        presentation.carrier.length * presentation.carrier.length := by
    calc
      presentation.rotationCount = presentation.affineNonNullCount +
          presentation.infinityTNonNullCount +
            presentation.infinityRNonNullCount + 1 :=
        presentation.rotationCount_eq_affineNonNullCount_add_infinityCounts
      _ = presentation.affineNonNullCount +
          (presentation.infinityTNonNullCount +
            presentation.infinityRNonNullCount + 1) := by ring1
      _ = presentation.affineNonNullCount +
          presentation.carrier.length * presentation.carrier.length := by
        rw [infinityCount]
  have totalAdd : presentation.rotationCount + presentation.carrier.length =
      presentation.carrier.length *
        (presentation.carrier.length * presentation.carrier.length) := by
    calc
      presentation.rotationCount + presentation.carrier.length =
          (presentation.affineNonNullCount +
            presentation.carrier.length * presentation.carrier.length) +
              presentation.carrier.length :=
        congrArg (fun count => count + presentation.carrier.length)
          rotationAsAffine
      _ = presentation.affineNonNullCount +
          (presentation.carrier.length * presentation.carrier.length +
            presentation.carrier.length) := by ring1
      _ = presentation.affineNonNullCount +
          presentation.excludedAnchorQuadric.length := by
        rw [presentation.excludedAnchorQuadric_length]
      _ = presentation.carrier.length *
          (presentation.carrier.length * presentation.carrier.length) :=
        presentation.affineNonNullCount_add_excludedAnchorQuadric
  calc
    presentation.rotationCount =
        presentation.carrier.length *
          (presentation.carrier.length * presentation.carrier.length) -
            presentation.carrier.length :=
      nat_eq_sub_of_add_eq_counting totalAdd
    _ = presentation.carrier.length *
        (presentation.carrier.length * presentation.carrier.length - 1) := by
      symm
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]

/-- The order formula stated directly for the duplicate-free rotation list,
with the projective representative bijection used as the cardinal bridge. -/
theorem rotationCarrierCount_formula_via_projectiveBijection :
    presentation.rotations.length = presentation.carrier.length *
      (presentation.carrier.length * presentation.carrier.length - 1) := by
  have projectiveLength := FiniteListBijection.length_eq
    presentation.projectiveRotationBijection
    presentation.nonNullProjectiveRepresentatives_nodup
    presentation.rotations_nodup
  calc
    presentation.rotations.length =
        presentation.nonNullProjectiveRepresentatives.length :=
      projectiveLength.symm
    _ = presentation.rotationCount := by
      symm
      calc
        presentation.rotationCount =
            presentation.rotationEnumeration.values.length :=
          presentation.rotationCount_eq_rotationEnumeration_length
        _ = presentation.rotations.length := rfl
        _ = presentation.nonNullProjectiveRepresentatives.length :=
          projectiveLength.symm
    _ = presentation.carrier.length *
        (presentation.carrier.length * presentation.carrier.length - 1) :=
      presentation.rotationCount_formula

/-- Closed count of displayed non-null four-tuples before quotienting.  The
factor `q-1` is certified by the explicit scale-orbit bijection, not by a
quotient-cardinality theorem. -/
theorem allNonNullProportionRepresentatives_count_formula :
    presentation.allNonNullProportionRepresentatives.length =
      (presentation.carrier.length - 1) *
        (presentation.carrier.length *
          (presentation.carrier.length * presentation.carrier.length - 1)) := by
  have projectiveLength := FiniteListBijection.length_eq
    presentation.projectiveRotationBijection
    presentation.nonNullProjectiveRepresentatives_nodup
    presentation.rotations_nodup
  calc
    presentation.allNonNullProportionRepresentatives.length =
        (presentation.carrier.length - 1) *
          presentation.nonNullProjectiveRepresentatives.length :=
      presentation.allNonNullProportionRepresentatives_length
    _ = (presentation.carrier.length - 1) *
        presentation.rotations.length := by rw [projectiveLength]
    _ = (presentation.carrier.length - 1) *
        (presentation.carrier.length *
          (presentation.carrier.length * presentation.carrier.length - 1)) := by
      rw [presentation.rotationCarrierCount_formula_via_projectiveBijection]

/-- Each of the two quadrance classes contains exactly half of the displayed
rotation group.  This proves the equal-kernel assertion in Problem 69 without
using a quotient cardinality or a choice of coset representatives. -/
theorem quadranceClassKernelCount_formula :
    presentation.quadranceClassKernelCount =
      (presentation.carrier.length *
        (presentation.carrier.length * presentation.carrier.length - 1)) / 2 := by
  let kernelLength := presentation.quadranceClassKernel.length
  have doubled : kernelLength + kernelLength = presentation.rotationCount :=
    presentation.quadranceClassKernel_twice_eq_rotationCount
  have kernelIsHalf : kernelLength = (kernelLength + kernelLength) / 2 := by
    symm
    calc
      (kernelLength + kernelLength) / 2 = (2 * kernelLength) / 2 := by
        congr 1
        ring1
      _ = kernelLength :=
        Nat.mul_div_right kernelLength (by decide : 0 < 2)
  calc
    presentation.quadranceClassKernelCount = kernelLength :=
      presentation.quadranceClassKernelCount_eq_length
    _ = (kernelLength + kernelLength) / 2 := kernelIsHalf
    _ = presentation.rotationCount / 2 :=
      congrArg (fun count : Nat => count / 2) doubled
    _ = (presentation.carrier.length *
        (presentation.carrier.length * presentation.carrier.length - 1)) / 2 :=
      congrArg (fun count : Nat => count / 2)
        presentation.rotationCount_formula

/-- Efficient executable count of the nonzero affine null cone, equivalently
the nonidentity parabolic rotations in the scalar-one chart. -/
def parabolicCount : Nat := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.vectorCountWhere fun vector =>
    decide (vector.quadrance = 0) && decide (vector ≠ Vector.zero)

theorem parabolicCount_eq_nonzeroNullVectors_length :
    presentation.parabolicCount = presentation.nonzeroNullVectors.length := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold parabolicCount nonzeroNullVectors
  rw [presentation.vectorCountWhere_eq_length_filter]

theorem parabolicCount_add_one :
    presentation.parabolicCount + 1 =
      presentation.carrier.length * presentation.carrier.length := by
  rw [presentation.parabolicCount_eq_nonzeroNullVectors_length,
    presentation.nonzeroNullVectors_length_add_one,
    presentation.nullVectors_length_eq_vectorQuadranceCount_zero,
    presentation.vectorQuadranceCount_zero]

theorem parabolicCount_formula :
    presentation.parabolicCount =
      presentation.carrier.length * presentation.carrier.length - 1 := by
  have added := presentation.parabolicCount_add_one
  calc
    presentation.parabolicCount =
        (presentation.parabolicCount + 1) - 1 :=
      (Nat.add_sub_cancel presentation.parabolicCount 1).symm
    _ = presentation.carrier.length * presentation.carrier.length - 1 :=
      congrArg (fun count => count - 1) added

/-- A single executable package for the completed finite counting clauses of
Problem 69.  It stores the carrier, the value-by-value classifier, the
quadrance-class switch, and the canonical preimage function alongside the
closed count and completeness certificates. -/
structure ProblemSixtyNineFiniteSolution where
  rotationCarrier : RotationEnumeration (K := K)
  rotationCarrierCanonical :
    rotationCarrier.values = presentation.rotationEnumeration.values
  rotationMatrixCarrier : RotationMatrixEnumeration (K := K)
  rotationMatrixCarrierCanonical :
    rotationMatrixCarrier.values =
      presentation.rotationMatrixEnumeration.values
  projectiveRotationEquivalence : FiniteListBijection
    presentation.nonNullProjectiveRepresentatives presentation.rotations
  rawScaleOrbitEquivalence : FiniteListBijection
    presentation.allNonNullProportionRepresentatives
      presentation.scaleOrbitCoordinates
  rawProportionCount :
    presentation.allNonNullProportionRepresentatives.length =
      (presentation.carrier.length - 1) *
        (presentation.carrier.length *
          (presentation.carrier.length * presentation.carrier.length - 1))
  rotationCarrierCount : presentation.rotations.length =
    presentation.carrier.length *
      (presentation.carrier.length * presentation.carrier.length - 1)
  classifyStratum : ∀ rotation : Rotation K,
    presentation.RotationStratum rotation
  affineFiberQuadricEquivalence : ∀ value : K, value ≠ 1 →
    FiniteListBijection (presentation.halfSpreadFiber value)
      (presentation.affineQuadricRepresentatives
        (value / (1 - value)))
  halfTurnProjectiveAxisEquivalence : FiniteListBijection
    (presentation.halfSpreadFiber 1)
      presentation.projectiveNonNullAxisRepresentatives
  zeroFiberIdentityPoint : ∀ proportion : NonNullProportion K,
    proportion ∈ presentation.halfSpreadFiber 0 →
      (proportion.rotation.matrix = Matrix3.identity ↔
        proportion.vector = Vector.zero)
  middleFiberSemisimple : ∀ value : K, value ≠ 0 → value ≠ 1 →
    ∀ proportion : NonNullProportion K,
      proportion ∈ presentation.halfSpreadFiber value →
        halfSpread proportion.rotation ≠ 0 ∧
          halfSpread proportion.rotation ≠ 1
  totalCount : presentation.rotationCount = presentation.carrier.length *
    (presentation.carrier.length * presentation.carrier.length - 1)
  zeroFiberCount : presentation.halfSpreadFiberCount 0 =
    presentation.carrier.length * presentation.carrier.length
  halfTurnFiberCount : presentation.halfSpreadFiberCount 1 =
    presentation.carrier.length * presentation.carrier.length
  middleFiberClassification : ∀ value : K, value ≠ 0 → value ≠ 1 →
    presentation.MiddleHalfSpreadFiberCountClassification value
  halfSpreadFiberCountSum :
    (presentation.carrier.map presentation.halfSpreadFiberCount).foldr
      Nat.add 0 = presentation.rotationCount
  minusOneCardinalityClassification :
    presentation.MinusOneCardinalityClassification
  nullDirectionCount : presentation.nullDirectionRepresentatives.length =
    presentation.carrier.length + 1
  parabolicDirectionFiberCount : ∀ direction : Vector K,
    ∀ member : direction ∈ presentation.nullDirectionRepresentatives,
      (presentation.parabolicRotationsOverDirection direction member).length =
        presentation.carrier.length - 1
  parabolicCoordinates : ∀ rotation : Rotation K,
    ∀ _spreadZero : halfSpread rotation = 0,
    ∀ _nonidentity : rotation.matrix ≠ Matrix3.identity,
      presentation.ParabolicDirectionCoordinates rotation
  characteristicParabolicEquivalence : ∀ rotation : Rotation K,
    (∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3) ↔
        halfSpread rotation = 0
  parabolicCoordinatesFromCharacteristic : ∀ rotation : Rotation K,
    (∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3) →
    rotation.matrix ≠ Matrix3.identity →
      presentation.ParabolicDirectionCoordinates rotation
  parabolicAnchorCount : presentation.parabolicCount =
    presentation.carrier.length * presentation.carrier.length - 1
  parabolicComplete : ∀ rotation : Rotation K,
    halfSpread rotation = 0 → rotation.matrix ≠ Matrix3.identity →
      ∃ vector : Vector K, ∃ null : vector.quadrance = 0,
        vector ≠ Vector.zero ∧
        vector ∈ presentation.nonzeroNullVectors ∧
          rotation = presentation.parabolicRotation vector null
  parabolicCompleteFromCharacteristic : ∀ rotation : Rotation K,
    (∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3) →
    rotation.matrix ≠ Matrix3.identity →
      ∃ vector : Vector K, ∃ null : vector.quadrance = 0,
        vector ≠ Vector.zero ∧
        vector ∈ presentation.nonzeroNullVectors ∧
          rotation = presentation.parabolicRotation vector null
  excludedAffineCount : presentation.excludedAnchorQuadric.length =
    presentation.carrier.length * presentation.carrier.length +
      presentation.carrier.length
  excludedProjectiveCount : presentation.excludedProjectiveQuadricCount =
    (presentation.carrier.length + 1) *
      (presentation.carrier.length + 1)
  quadranceClassPreimage : SquareClassRepresentative K → Rotation K
  quadranceClassPreimageRealizes : ∀ target : SquareClassRepresentative K,
    letI : DecidableEq K := presentation.eqDecidable
    (RotationQuadranceClass.ofRotation
      (quadranceClassPreimage target) presentation.twoNonzero).Equivalent target
  quadranceClassFiberSwitch : FiniteListBijection
    presentation.quadranceClassKernel
    presentation.quadranceClassNontrivialFiber
  quadranceClassKernelCharacterization : ∀ proportion : NonNullProportion K,
    proportion ∈ presentation.quadranceClassKernel ↔
      proportion ∈ presentation.nonNullProjectiveRepresentatives ∧
        proportion.HasUnitRepresentative
  quadranceClassKernelCount : presentation.quadranceClassKernelCount =
    (presentation.carrier.length *
      (presentation.carrier.length * presentation.carrier.length - 1)) / 2

/-- Assemble the general odd-finite-field solution from the independently
checked finite carriers and bijections. -/
def problemSixtyNineFiniteSolution :
    presentation.ProblemSixtyNineFiniteSolution where
  rotationCarrier := presentation.rotationEnumeration
  rotationCarrierCanonical := rfl
  rotationMatrixCarrier := presentation.rotationMatrixEnumeration
  rotationMatrixCarrierCanonical := rfl
  projectiveRotationEquivalence := presentation.projectiveRotationBijection
  rawScaleOrbitEquivalence := presentation.nonNullScaleOrbitBijection
  rawProportionCount :=
    presentation.allNonNullProportionRepresentatives_count_formula
  rotationCarrierCount :=
    presentation.rotationCarrierCount_formula_via_projectiveBijection
  classifyStratum := presentation.classifyRotationStratum
  affineFiberQuadricEquivalence := fun value notOne =>
    presentation.affineHalfSpreadFiberBijection value notOne
  halfTurnProjectiveAxisEquivalence :=
    presentation.halfTurnProjectiveAxisBijection
  zeroFiberIdentityPoint := fun proportion member =>
    presentation.zeroFiber_rotation_identity_iff_vector_eq_zero
      proportion member
  middleFiberSemisimple := fun _value valueNonzero notOne proportion member =>
    presentation.middleFiber_rotation_semisimple valueNonzero notOne
      proportion member
  totalCount := presentation.rotationCount_formula
  zeroFiberCount := presentation.halfSpreadFiberCount_zero
  halfTurnFiberCount := presentation.halfSpreadFiberCount_one
  middleFiberClassification := fun value valueNonzero notOne =>
    presentation.classifyMiddleHalfSpreadFiberCount value valueNonzero notOne
  halfSpreadFiberCountSum := presentation.halfSpreadFiberCounts_sum
  minusOneCardinalityClassification :=
    presentation.classifyMinusOneCardinality
  nullDirectionCount := presentation.nullDirectionRepresentatives_length
  parabolicDirectionFiberCount := fun direction member =>
    presentation.parabolicRotationsOverDirection_length direction member
  parabolicCoordinates := fun rotation spreadZero nonidentity =>
    presentation.parabolicDirectionCoordinates rotation spreadZero nonidentity
  characteristicParabolicEquivalence := fun rotation =>
    characteristicUnipotent_iff_halfSpread_eq_zero rotation
      presentation.twoNonzero
  parabolicCoordinatesFromCharacteristic :=
    fun rotation characteristic nonidentity =>
      presentation.parabolicDirectionCoordinatesOfCharacteristic rotation
        characteristic nonidentity
  parabolicAnchorCount := presentation.parabolicCount_formula
  parabolicComplete := fun rotation spreadZero nonidentity =>
    presentation.parabolicRotation_complete rotation spreadZero nonidentity
  parabolicCompleteFromCharacteristic :=
    fun rotation characteristic nonidentity =>
      presentation.parabolicRotation_complete_of_characteristic rotation
        characteristic nonidentity
  excludedAffineCount := presentation.excludedAnchorQuadric_length
  excludedProjectiveCount :=
    presentation.excludedProjectiveQuadricCount_formula
  quadranceClassPreimage := presentation.quadranceClassPreimageRotation
  quadranceClassPreimageRealizes := fun target =>
    presentation.quadranceClassPreimage_realizes target
  quadranceClassFiberSwitch := presentation.quadranceClassFiberBijection
  quadranceClassKernelCharacterization := fun proportion =>
    presentation.mem_quadranceClassKernel_iff_hasUnitRepresentative proportion
  quadranceClassKernelCount := presentation.quadranceClassKernelCount_formula

end FiniteOddFieldPresentation

/-! ## Fully evaluated small-field regression presentations -/

namespace CountingExamples

open FiniteOddFieldPresentation

namespace FieldThree

abbrev Scalar := DivineProportions.FieldThree.Element

private def cachedSquareRoot (value : Scalar) : Scalar := value

def presentation : FiniteOddFieldPresentation Scalar where
  eqDecidable := inferInstance
  carrier := [0, 1, 2]
  carrierNodup := by decide
  carrierComplete := by decide +revert
  squareValues := [0, 1]
  squareValuesNodup := by decide
  squareValuesComplete := by decide +revert
  squareRoot := cachedSquareRoot
  squareRoot_spec := by decide +revert
  squareCount := by decide
  twoNonzero := by decide

theorem rotation_count : presentation.rotationCount = 24 := by decide

theorem rotation_enumeration_count :
    presentation.rotationEnumeration.values.length = 24 := by
  rw [← presentation.rotationCount_eq_rotationEnumeration_length]
  exact rotation_count

theorem all_nonNull_proportion_count :
    presentation.allNonNullProportionRepresentatives.length = 48 := by
  rw [presentation.allNonNullProportionRepresentatives_count_formula]
  decide

theorem halfSpread_fiber_counts :
    ([0, 1, 2] : List Scalar).map (fun value =>
      presentation.halfSpreadFiberCount value) =
        [9, 9, 6] := by decide

theorem twoSquare_fiber_counts :
    ([0, 1, 2] : List Scalar).map presentation.twoSquareCount =
      [1, 4, 4] := by decide

theorem ternaryQuadrance_fiber_counts :
    ([0, 1, 2] : List Scalar).map presentation.vectorQuadranceCount =
      [9, 6, 12] := by decide

theorem null_vector_count : presentation.vectorQuadranceCount 0 = 9 := by decide

theorem parabolic_count : presentation.parabolicCount = 8 := by decide

theorem null_direction_count :
    presentation.nullDirectionRepresentatives.length = 4 := by decide

theorem excluded_anchor_count :
    presentation.vectorQuadranceCount (-1) = 12 := by decide

theorem excluded_projective_count :
    presentation.excludedProjectiveQuadricCount = 16 := by decide

theorem quadrance_class_kernel_count :
    presentation.quadranceClassKernelCount = 12 := by decide

end FieldThree

namespace FieldFive

abbrev Scalar := DivineProportions.FieldFive.Element

def presentation : FiniteOddFieldPresentation Scalar :=
  RationalRotations.FieldFive.finiteOddFieldPresentation

theorem rotation_count : presentation.rotationCount = 120 := by
  decide

theorem rotation_enumeration_count :
    presentation.rotationEnumeration.values.length = 120 := by
  rw [← presentation.rotationCount_eq_rotationEnumeration_length]
  exact rotation_count

theorem all_nonNull_proportion_count :
    presentation.allNonNullProportionRepresentatives.length = 480 := by
  rw [presentation.allNonNullProportionRepresentatives_count_formula]
  decide

theorem halfSpread_fiber_counts :
    ([0, 1, 2, 3, 4] : List Scalar).map (fun value =>
      presentation.halfSpreadFiberCount value) =
        [25, 25, 20, 30, 20] := by decide

theorem twoSquare_fiber_counts :
    ([0, 1, 2, 3, 4] : List Scalar).map presentation.twoSquareCount =
      [9, 4, 4, 4, 4] := by decide

theorem ternaryQuadrance_fiber_counts :
    ([0, 1, 2, 3, 4] : List Scalar).map
        presentation.vectorQuadranceCount =
      [25, 30, 20, 20, 30] := by decide

theorem null_vector_count : presentation.vectorQuadranceCount 0 = 25 := by decide

theorem parabolic_count : presentation.parabolicCount = 24 := by decide

theorem null_direction_count :
    presentation.nullDirectionRepresentatives.length = 6 := by decide

theorem excluded_anchor_count :
    presentation.vectorQuadranceCount (-1) = 30 := by decide

theorem excluded_projective_count :
    presentation.excludedProjectiveQuadricCount = 36 := by decide

theorem quadrance_class_kernel_count :
    presentation.quadranceClassKernelCount = 60 := by
  decide

end FieldFive

namespace FieldSeven

abbrev Scalar := DivineProportions.FieldSeven.Element

private def cachedSquareRoot (value : Scalar) : Scalar :=
  if value = 2 then 3 else if value = 4 then 2 else value

def presentation : FiniteOddFieldPresentation Scalar where
  eqDecidable := inferInstance
  carrier := [0, 1, 2, 3, 4, 5, 6]
  carrierNodup := by decide
  carrierComplete := by decide +revert
  squareValues := [0, 1, 2, 4]
  squareValuesNodup := by decide
  squareValuesComplete := by decide +revert
  squareRoot := cachedSquareRoot
  squareRoot_spec := by decide +revert
  squareCount := by decide
  twoNonzero := by decide

theorem rotation_count : presentation.rotationCount = 336 := by
  decide

theorem rotation_enumeration_count :
    presentation.rotationEnumeration.values.length = 336 := by
  rw [← presentation.rotationCount_eq_rotationEnumeration_length]
  exact rotation_count

theorem all_nonNull_proportion_count :
    presentation.allNonNullProportionRepresentatives.length = 2016 := by
  rw [presentation.allNonNullProportionRepresentatives_count_formula]
  decide

private theorem halfSpread_count_zero :
    presentation.halfSpreadFiberCount 0 = 49 := by
  decide

private theorem halfSpread_count_one :
    presentation.halfSpreadFiberCount 1 = 49 := by
  decide

private theorem halfSpread_count_two :
    presentation.halfSpreadFiberCount 2 = 56 := by
  decide

private theorem halfSpread_count_three :
    presentation.halfSpreadFiberCount 3 = 42 := by
  decide

private theorem halfSpread_count_four :
    presentation.halfSpreadFiberCount 4 = 42 := by
  decide

private theorem halfSpread_count_five :
    presentation.halfSpreadFiberCount 5 = 42 := by
  decide

private theorem halfSpread_count_six :
    presentation.halfSpreadFiberCount 6 = 56 := by
  decide

theorem halfSpread_fiber_counts :
    ([0, 1, 2, 3, 4, 5, 6] : List Scalar).map (fun value =>
      presentation.halfSpreadFiberCount value) =
        [49, 49, 56, 42, 42, 42, 56] := by
  simp only [List.map_cons, List.map_nil]
  rw [halfSpread_count_zero, halfSpread_count_one, halfSpread_count_two,
    halfSpread_count_three, halfSpread_count_four, halfSpread_count_five,
    halfSpread_count_six]

theorem twoSquare_fiber_counts :
    ([0, 1, 2, 3, 4, 5, 6] : List Scalar).map
        presentation.twoSquareCount =
      [1, 8, 8, 8, 8, 8, 8] := by decide

theorem ternaryQuadrance_fiber_counts :
    ([0, 1, 2, 3, 4, 5, 6] : List Scalar).map
        presentation.vectorQuadranceCount =
      [49, 42, 42, 56, 42, 56, 56] := by decide

theorem null_vector_count : presentation.vectorQuadranceCount 0 = 49 := by
  decide

theorem parabolic_count : presentation.parabolicCount = 48 := by
  decide

theorem null_direction_count :
    presentation.nullDirectionRepresentatives.length = 8 := by
  decide

theorem excluded_anchor_count :
    presentation.vectorQuadranceCount (-1) = 56 := by
  decide

theorem excluded_projective_count :
    presentation.excludedProjectiveQuadricCount = 64 := by
  decide

theorem quadrance_class_kernel_count :
    presentation.quadranceClassKernelCount = 168 := by
  decide

end FieldSeven

end CountingExamples

end RationalRotations
