module

public import Purelib.Geometry.Quadratic.Finite.Fibers
import Purelib.Data.List.Bijection
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Finite.Odd.Presentation
public import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.Data.List.FilterMap
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Nodup
import Purelib.Data.Nat.Order
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Core
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Ring.Nat
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Algebra.Field.Finite.Odd

open Purelib.Algebra.Quaternion

open Purelib.Algebra.Quaternion.Projective.Basic

open Purelib.Data.List

open Purelib.LinearAlgebra

open scoped Purelib.Data.Nat

section
@[expose] public section

/-!
# Constructive finite-field rotation enumeration

Problem 69 asks for counts over a displayed odd finite field.  This module
provides the executable layer used by those counts.  Projective points are not
obtained from a `Fintype` or a quotient: the four standard first-nonzero
coordinate charts are listed directly, and representatives whose four-square
norm vanishes are removed by a finite test.
-/

section

variable {K : Type*} [ExplicitField K]

section

variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

/-- All displayed affine vectors, in lexicographic carrier order. -/
def vectors : List (Coordinates3.Vector
  K) :=
  presentation.carrier.flatMap fun t =>
    presentation.carrier.flatMap fun r =>
      presentation.carrier.map fun s => ⟨t, r, s⟩

/-- Every displayed four-coordinate proportion, before removing the zero-norm locus or identifying nonzero scales. -/
def allProportionRepresentatives : List
  (Projective.Basic.Proportion K) :=
  presentation.carrier.flatMap fun scalar =>
    presentation.vectors.map fun vector => ⟨scalar, vector⟩

/-- The affine chart of projective three-space, normalized to scalar coordinate one. -/
def affineProportionRepresentatives :
  List (Projective.Basic.Proportion K) :=
  presentation.vectors.map fun vector => ⟨1, vector⟩

/-- The first chart at infinity, normalized to vector coordinate `t = 1`. -/
def infinityTRepresentatives : List
  (Projective.Basic.Proportion K) :=
  presentation.carrier.flatMap fun r =>
    presentation.carrier.map fun s => ⟨0, ⟨1, r, s⟩⟩

/-- The second chart at infinity, normalized to `t = 0, r = 1`. -/
def infinityRRepresentatives : List
  (Projective.Basic.Proportion K) :=
  presentation.carrier.map fun s => ⟨0, ⟨0, 1, s⟩⟩

/-- The final point at infinity, normalized to `t = r = 0, s = 1`. -/
def infinitySRepresentative :
  Projective.Basic.Proportion K := ⟨0, ⟨0, 0, 1⟩⟩

/-- A duplicate-free-by-construction first-nonzero-coordinate list for projective three-space. Completeness and
uniqueness are proved in the general counting layer; this definition is already executable. -/
def projectiveRepresentatives : List
  (Projective.Basic.Proportion K) :=
  presentation.affineProportionRepresentatives ++
    presentation.infinityTRepresentatives ++
    presentation.infinityRRepresentatives ++
    [infinitySRepresentative]

/-- Every displayed three-coordinate vector occurs in the finite Cartesian carrier. -/
theorem vectors_complete (vector :
  Coordinates3.Vector K) :
    vector ∈ presentation.vectors := by
  unfold vectors
  apply Flatten.mem_flatMap.mpr
  refine ⟨vector.t, presentation.carrierComplete vector.t, ?_⟩
  apply Flatten.mem_flatMap.mpr
  refine ⟨vector.r, presentation.carrierComplete vector.r, ?_⟩
  apply Map.mem_map.mpr
  exact ⟨vector.s, presentation.carrierComplete vector.s, rfl⟩

/-- Every raw four-coordinate proportion occurs in the finite carrier enumeration. -/
theorem
  allProportionRepresentatives_complete
  (raw : Projective.Basic.Proportion K) :
    raw ∈ presentation.allProportionRepresentatives := by
  unfold allProportionRepresentatives
  apply Flatten.mem_flatMap.mpr
  refine ⟨raw.scalar, presentation.carrierComplete raw.scalar, ?_⟩
  apply Map.mem_map.mpr
  exact ⟨raw.vector, presentation.vectors_complete raw.vector, rfl⟩

/-- Every scalar-one representative occurs in the canonical projective chart list. -/
theorem affineProportion_mem (vector :
  Coordinates3.Vector K) :
    (⟨1, vector⟩ : Projective.Basic.Proportion K) ∈
      presentation.projectiveRepresentatives := by
  apply Membership.mem_append.mpr
  left
  apply Membership.mem_append.mpr
  left
  apply Membership.mem_append.mpr
  left
  unfold affineProportionRepresentatives
  exact Map.mem_map.mpr
    ⟨vector, presentation.vectors_complete vector, rfl⟩

/-- Every representative with scalar zero and first vector coordinate one occurs in the chart list. -/
theorem infinityTProportion_mem (r s :
  K) :
    (⟨0, ⟨1, r, s⟩⟩ : Projective.Basic.Proportion K) ∈
      presentation.projectiveRepresentatives := by
  apply Membership.mem_append.mpr
  left
  apply Membership.mem_append.mpr
  left
  apply Membership.mem_append.mpr
  right
  unfold infinityTRepresentatives
  apply Flatten.mem_flatMap.mpr
  refine ⟨r, presentation.carrierComplete r, ?_⟩
  exact Map.mem_map.mpr
    ⟨s, presentation.carrierComplete s, rfl⟩

/-- Every representative normalized at the second vector coordinate occurs in the chart list. -/
theorem infinityRProportion_mem (s : K)
  :
    (⟨0, ⟨0, 1, s⟩⟩ : Projective.Basic.Proportion K) ∈
      presentation.projectiveRepresentatives := by
  apply Membership.mem_append.mpr
  left
  apply Membership.mem_append.mpr
  right
  unfold infinityRRepresentatives
  exact Map.mem_map.mpr
    ⟨s, presentation.carrierComplete s, rfl⟩

/-- The final normalized point at infinity occurs in the chart list. -/
theorem infinitySProportion_mem :
    (infinitySRepresentative :
      Projective.Basic.Proportion K) ∈
      presentation.projectiveRepresentatives := by
  apply Membership.mem_append.mpr
  right
  exact Membership.mem_singleton.mpr rfl

/-- Membership in the four-chart list exposes the normalized chart and its displayed free coordinates. -/
theorem projectiveRepresentatives_cases
  {raw : Projective.Basic.Proportion K}
    (member : raw ∈ presentation.projectiveRepresentatives) :
    (∃ vector : Coordinates3.Vector K, raw = ⟨1, vector⟩) ∨
    (∃ r s : K, raw = ⟨0, ⟨1, r, s⟩⟩) ∨
    (∃ s : K, raw = ⟨0, ⟨0, 1, s⟩⟩) ∨
    raw = infinitySRepresentative := by
  rcases Membership.mem_append.mp member with beforeS | atS
  · rcases Membership.mem_append.mp beforeS with beforeR | atR
    · rcases Membership.mem_append.mp beforeR with atAffine | atT
      · rcases Map.mem_map.mp atAffine with
          ⟨vector, _, equal⟩
        exact Or.inl ⟨vector, equal.symm⟩
      · rcases Flatten.mem_flatMap.mp atT with
          ⟨r, _, rMember⟩
        rcases Map.mem_map.mp rMember with ⟨s, _, equal⟩
        exact Or.inr (Or.inl ⟨r, s, equal.symm⟩)
    · rcases Map.mem_map.mp atR with ⟨s, _, equal⟩
      exact Or.inr (Or.inr (Or.inl ⟨s, equal.symm⟩))
  · exact Or.inr (Or.inr (Or.inr (Membership.mem_singleton.mp atS)))

/-- Flattening duplicate-free pairwise disjoint fibers over a duplicate-free list introduces no duplicates.

The disjointness hypothesis distinguishes values from fibers at distinct retained indices. -/
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
      rw [Flatten.flatMap_cons]
      apply Nodup.nodup_append
      · exact fiberNodup head List.mem_cons_self
      · apply inductionHypothesis
        · exact (List.pairwise_cons.mp valuesNodup).2
        · intro value member
          exact fiberNodup value (List.mem_cons_of_mem head member)
        · intro left leftMember right rightMember different
          exact fiberDisjoint left (List.mem_cons_of_mem head leftMember)
            right (List.mem_cons_of_mem head rightMember) different
      · intro leftValue leftMember rightValue rightMember
        rcases Flatten.mem_flatMap.mp rightMember with
          ⟨right, rightInTail, rightValueMember⟩
        exact fiberDisjoint head List.mem_cons_self right
          (List.mem_cons_of_mem head rightInTail)
          ((List.pairwise_cons.mp valuesNodup).1 right rightInTail)
          leftValue leftMember rightValue rightValueMember

/-- The Cartesian vector enumeration contains no repeated vectors. -/
theorem vectors_nodup :
  presentation.vectors.Nodup := by
  unfold vectors
  apply nodup_flatMap_of_nodup
    presentation.carrierNodup
  · intro t _
    apply nodup_flatMap_of_nodup
      presentation.carrierNodup
    · intro r _
      apply Data.List.Nodup.nodup_map_of_injective
      · intro left right equal
        exact congrArg Coordinates3.Vector.s equal
      · exact presentation.carrierNodup
    · intro left _ right _ different leftVector leftMember rightVector
        rightMember equal
      rcases Map.mem_map.mp leftMember with ⟨leftS, _, leftEq⟩
      rcases Map.mem_map.mp rightMember with
        ⟨rightS, _, rightEq⟩
      apply different
      calc
        left = leftVector.r := congrArg Coordinates3.Vector.r leftEq
        _ = rightVector.r := congrArg Coordinates3.Vector.r equal
        _ = right := (congrArg Coordinates3.Vector.r rightEq).symm
  · intro left _ right _ different leftVector leftMember rightVector
      rightMember equal
    rcases Flatten.mem_flatMap.mp leftMember with
      ⟨leftR, _, leftRMember⟩
    rcases Map.mem_map.mp leftRMember with
      ⟨leftS, _, leftEq⟩
    rcases Flatten.mem_flatMap.mp rightMember with
      ⟨rightR, _, rightRMember⟩
    rcases Map.mem_map.mp rightRMember with
      ⟨rightS, _, rightEq⟩
    apply different
    calc
      left = leftVector.t := congrArg Coordinates3.Vector.t leftEq
      _ = rightVector.t := congrArg Coordinates3.Vector.t equal
      _ = right := (congrArg Coordinates3.Vector.t rightEq).symm

/-- The raw four-coordinate enumeration contains no repeated proportions. -/
theorem
  allProportionRepresentatives_nodup :
    presentation.allProportionRepresentatives.Nodup := by
  unfold allProportionRepresentatives
  apply nodup_flatMap_of_nodup
    presentation.carrierNodup
  · intro scalar _
    apply Data.List.Nodup.nodup_map_of_injective
    · intro left right equal
      exact congrArg Proportion.vector equal
    · exact presentation.vectors_nodup
  · intro left _ right _ different leftRaw leftMember rightRaw rightMember equal
    rcases Map.mem_map.mp leftMember with
      ⟨leftVector, _, leftEq⟩
    rcases Map.mem_map.mp rightMember with
      ⟨rightVector, _, rightEq⟩
    apply different
    calc
      left = leftRaw.scalar := congrArg Proportion.scalar leftEq
      _ = rightRaw.scalar := congrArg Proportion.scalar equal
      _ = right := (congrArg Proportion.scalar rightEq).symm

/-- The scalar-one projective chart has no repeated representatives. -/
private theorem
  affineProportionRepresentatives_nodup
  :
    presentation.affineProportionRepresentatives.Nodup := by
  unfold affineProportionRepresentatives
  apply Data.List.Nodup.nodup_map_of_injective
  · intro left right equal
    exact congrArg Proportion.vector equal
  · exact presentation.vectors_nodup

/-- The first chart at infinity has no repeated representatives. -/
private theorem
  infinityTRepresentatives_nodup :
    presentation.infinityTRepresentatives.Nodup := by
  unfold infinityTRepresentatives
  apply nodup_flatMap_of_nodup
    presentation.carrierNodup
  · intro r _
    apply Data.List.Nodup.nodup_map_of_injective
    · intro left right equal
      exact congrArg (fun value : Projective.Basic.Proportion K => value.vector.s) equal
    · exact presentation.carrierNodup
  · intro left _ right _ different leftValue leftMember rightValue
      rightMember equal
    rcases Map.mem_map.mp leftMember with ⟨leftS, _, leftEq⟩
    rcases Map.mem_map.mp rightMember with
      ⟨rightS, _, rightEq⟩
    apply different
    calc
      left = leftValue.vector.r :=
        congrArg (fun value : Projective.Basic.Proportion K => value.vector.r) leftEq
      _ = rightValue.vector.r :=
        congrArg (fun value : Projective.Basic.Proportion K => value.vector.r) equal
      _ = right :=
        (congrArg (fun value : Projective.Basic.Proportion K => value.vector.r) rightEq).symm

/-- The second chart at infinity has no repeated representatives. -/
private theorem
  infinityRRepresentatives_nodup :
    presentation.infinityRRepresentatives.Nodup := by
  unfold infinityRRepresentatives
  apply Data.List.Nodup.nodup_map_of_injective
  · intro left right equal
    exact congrArg (fun value : Projective.Basic.Proportion K => value.vector.s) equal
  · exact presentation.carrierNodup

/-- The scalar-one chart and the first chart at infinity have distinct representatives. -/
private theorem
  affine_infinityT_disjoint {left right
  : Projective.Basic.Proportion K}
    (leftMember : left ∈ presentation.affineProportionRepresentatives)
    (rightMember : right ∈ presentation.infinityTRepresentatives) :
    left ≠ right := by
  rcases Map.mem_map.mp leftMember with ⟨vector, _, leftEqual⟩
  rcases Flatten.mem_flatMap.mp rightMember with
    ⟨r, _, rMember⟩
  rcases Map.mem_map.mp rMember with ⟨s, _, rightEqual⟩
  subst left
  subst right
  intro equal
  exact Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation (congrArg
    Proportion.scalar equal)

/-- Representatives in the first two charts differ from those normalized at the second vector coordinate. -/
private theorem
  beforeR_infinityR_disjoint {left right
  : Projective.Basic.Proportion K}
    (leftMember : left ∈
      presentation.affineProportionRepresentatives ++
        presentation.infinityTRepresentatives)
    (rightMember : right ∈ presentation.infinityRRepresentatives) :
    left ≠ right := by
  rcases Map.mem_map.mp rightMember with ⟨s, _, rightEqual⟩
  subst right
  rcases Membership.mem_append.mp leftMember with atAffine | atT
  · rcases Map.mem_map.mp atAffine with
      ⟨vector, _, leftEqual⟩
    subst left
    intro equal
    exact Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation (congrArg
      Proportion.scalar equal)
  · rcases Flatten.mem_flatMap.mp atT with ⟨r, _, rMember⟩
    rcases Map.mem_map.mp rMember with
      ⟨otherS, _, leftEqual⟩
    subst left
    intro equal
    exact Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation
      (congrArg (fun value : Projective.Basic.Proportion K => value.vector.t) equal)

/-- No representative in the first three charts equals the final normalized point. -/
private theorem
  beforeS_infinityS_disjoint {left right
  : Projective.Basic.Proportion K}
    (leftMember : left ∈
      (presentation.affineProportionRepresentatives ++
        presentation.infinityTRepresentatives) ++
        presentation.infinityRRepresentatives)
    (rightMember : right ∈ [infinitySRepresentative]) :
      left ≠ right := by
  have rightEqual := Membership.mem_singleton.mp rightMember
  subst right
  rcases Membership.mem_append.mp leftMember with beforeR | atR
  · rcases Membership.mem_append.mp beforeR with atAffine | atT
    · rcases Map.mem_map.mp atAffine with
        ⟨vector, _, leftEqual⟩
      subst left
      intro equal
      exact Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation (congrArg
        Proportion.scalar equal)
    · rcases Flatten.mem_flatMap.mp atT with ⟨r, _, rMember⟩
      rcases Map.mem_map.mp rMember with
        ⟨s, _, leftEqual⟩
      subst left
      intro equal
      exact Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation
        (congrArg (fun value : Projective.Basic.Proportion K => value.vector.t) equal)
  · rcases Map.mem_map.mp atR with ⟨s, _, leftEqual⟩
    subst left
    intro equal
    exact Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation
      (congrArg (fun value : Projective.Basic.Proportion K => value.vector.r) equal)

/-- The four concatenated canonical projective charts contain no duplicates. -/
theorem projectiveRepresentatives_nodup
  :
    presentation.projectiveRepresentatives.Nodup := by
  unfold projectiveRepresentatives
  have beforeRNodup :
      (presentation.affineProportionRepresentatives ++
        presentation.infinityTRepresentatives).Nodup :=
    Nodup.nodup_append
      presentation.affineProportionRepresentatives_nodup
      presentation.infinityTRepresentatives_nodup
      (fun left leftMember right rightMember =>
        presentation.affine_infinityT_disjoint leftMember rightMember)
  have beforeSNodup :
      ((presentation.affineProportionRepresentatives ++
        presentation.infinityTRepresentatives) ++
        presentation.infinityRRepresentatives).Nodup :=
    Nodup.nodup_append beforeRNodup
      presentation.infinityRRepresentatives_nodup
      (fun left leftMember right rightMember =>
        presentation.beforeR_infinityR_disjoint leftMember rightMember)
  exact Nodup.nodup_append beforeSNodup
    (Nodup.nodup_singleton infinitySRepresentative)
    (fun left leftMember right rightMember =>
      presentation.beforeS_infinityS_disjoint leftMember rightMember)

/-- Two normalized members of the four projective charts cannot differ by a nonzero scale. This is the quotient-free
uniqueness theorem behind the finite rotation carrier. -/
theorem projective_eq_of_equivalent
  {left right : Projective.Basic.Proportion K}
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
    exact False.elim (Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation
      (by simpa using scalar))
  · have tCoordinate := congrArg (fun value : Projective.Basic.Proportion K => value.vector.t)
      scaled
    change (1 : K) = factor * 1 at tCoordinate
    have factorOne : factor = 1 := by simpa using tCoordinate.symm
    subst factor
    rw [Proportion.one_scale] at scaled
    exact scaled.symm
  · have tCoordinate := congrArg (fun value : Projective.Basic.Proportion K => value.vector.t)
      scaled
    change (0 : K) = factor * 1 at tCoordinate
    exact False.elim (factorNonzero (by simpa using tCoordinate.symm))
  · have tCoordinate := congrArg (fun value : Projective.Basic.Proportion K => value.vector.t)
      scaled
    change (0 : K) = factor * 1 at tCoordinate
    exact False.elim (factorNonzero (by simpa using tCoordinate.symm))
  · have scalar := congrArg Proportion.scalar scaled
    change (1 : K) = factor * 0 at scalar
    exact False.elim (Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation
      (by simpa using scalar))
  · have tCoordinate := congrArg (fun value : Projective.Basic.Proportion K => value.vector.t)
      scaled
    change (1 : K) = factor * 0 at tCoordinate
    exact False.elim (Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation
      (by simpa using tCoordinate))
  · have rCoordinate := congrArg (fun value : Projective.Basic.Proportion K => value.vector.r)
      scaled
    change (1 : K) = factor * 1 at rCoordinate
    have factorOne : factor = 1 := by simpa using rCoordinate.symm
    subst factor
    rw [Proportion.one_scale] at scaled
    exact scaled.symm
  · have rCoordinate := congrArg (fun value : Projective.Basic.Proportion K => value.vector.r)
      scaled
    change (0 : K) = factor * 1 at rCoordinate
    exact False.elim (factorNonzero (by simpa using rCoordinate.symm))
  · have scalar := congrArg Proportion.scalar scaled
    change (1 : K) = factor * 0 at scalar
    exact False.elim (Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation
      (by simpa using scalar))
  · have tCoordinate := congrArg (fun value : Projective.Basic.Proportion K => value.vector.t)
      scaled
    change (1 : K) = factor * 0 at tCoordinate
    exact False.elim (Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation
      (by simpa using tCoordinate))
  · have rCoordinate := congrArg (fun value : Projective.Basic.Proportion K => value.vector.r)
      scaled
    change (1 : K) = factor * 0 at rCoordinate
    exact False.elim (Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation
      (by simpa using rCoordinate))
  · rfl

/-- Turn one raw projective representative into cached non-null data exactly when its four-square norm is nonzero. -/
def certifyNonNull (raw :
  Projective.Basic.Proportion K) : Option (Projective.Basic.NonNullProportion K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact if normZero : raw.norm = 0 then none else
    some { toProportion := raw, normNonzero := normZero }

/-- Canonical non-null projective representatives. Via the projective rotation theorem these are the executable rotation
carrier for Problem 69. -/
def nonNullProjectiveRepresentatives :
  List (Projective.Basic.NonNullProportion K) :=
  presentation.projectiveRepresentatives.filterMap presentation.certifyNonNull

/-- Every displayed non-null four-tuple, before quotienting by scale. -/
def allNonNullProportionRepresentatives
  : List (Projective.Basic.NonNullProportion K) :=
  presentation.allProportionRepresentatives.filterMap
    presentation.certifyNonNull

set_option genInjectivity false in
/-- A scalar bundled with the executable nonzeroness certificate needed for projective rescaling. -/
structure DisplayedNonzeroScalar where
  /-- The retained field scalar. -/ value : K
  /-- The retained scalar is nonzero. -/ nonzero : value ≠ 0

constructive_injectivity DisplayedNonzeroScalar

end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

namespace Purelib.Geometry.Projective.Quaternion.Finite.Enumeration.FiniteOddFieldPresentation.DisplayedNonzeroScalar

/-- Certified nonzero scalars are equal when their retained values are equal. -/
theorem
  ext
    {left right : Presentation.FiniteOddFieldPresentation.DisplayedNonzeroScalar (K := K)}
    (valueEq : left.value = right.value) : left = right := by
  cases left
  cases right
  cases valueEq
  rfl

end Purelib.Geometry.Projective.Quaternion.Finite.Enumeration.FiniteOddFieldPresentation.DisplayedNonzeroScalar

open Purelib.Geometry.Projective.Quaternion.Finite

namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

/-- Test a scalar for nonzeroness and retain the proof on success.

Use the presentation's explicit equality decision; zero returns `none`. -/
def certifyNonzeroScalar (value : K) :
    Option (DisplayedNonzeroScalar (K := K)) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact if valueZero : value = 0 then none else
    some ⟨value, valueZero⟩

/-- Duplicate-free displayed carrier of the multiplicative nonzero scalars, with every proof required for scaling cached
in each element. -/
def nonzeroScalarWitnesses : List
  (DisplayedNonzeroScalar (K := K)) :=
  presentation.carrier.filterMap presentation.certifyNonzeroScalar

set_option genInjectivity false in
/-- Cached normalization of a non-null displayed proportion to the unique first-nonzero-coordinate chart used by
`projectiveRepresentatives`. -/
structure Canonicalization (source :
  Projective.Basic.NonNullProportion K) where
  /-- The cached normalized non-null proportion. -/ representative : Projective.Basic.NonNullProportion K
  /-- Its raw proportion lies in the canonical first-nonzero-coordinate chart list. -/ member :
    representative.toProportion ∈
    presentation.projectiveRepresentatives
  /-- The computed scalar multiplying the original source to normalize it. -/ factor : K
  /-- The normalization factor is nonzero. -/ factorNonzero : factor ≠ 0
  /-- The cached representative is exactly the original source scaled by the retained factor. -/ representative_eq_scale
    :
    representative = source.scale factor factorNonzero
  /-- The source and cached representative are related by an explicit nonzero scale. -/ equivalent : source.Equivalent
    representative

constructive_injectivity Canonicalization

/-- The displayed inverse of a nonzero scalar cancels multiplication by that scalar. -/
public theorem inverse_mul (value : K)
  (nonzero : value ≠ 0) :
    value⁻¹ * value = 1 := by
  calc
    value⁻¹ * value = value * value⁻¹ := by ring1
    _ = 1 := ExplicitField.mul_inv_cancel value nonzero

/-- Decidable equality recovers scalar equality with zero from the negation of nonzeroness. -/
public theorem eq_zero_of_not_ne
  (eqDecidable : DecidableEq K)
    {value : K} (notNonzero : ¬ value ≠ 0) : value = 0 := by
  cases eqDecidable value 0 with
  | isTrue equal => exact equal
  | isFalse nonzero => exact False.elim (notNonzero nonzero)

/-- Normalize by the first nonzero coordinate. All four branches and the scale witness are computed directly; no
representative is chosen from a quotient. -/
def canonicalize (source :
  Projective.Basic.NonNullProportion K) :
    presentation.Canonicalization source := by
  letI : DecidableEq K := presentation.eqDecidable
  if scalarNonzero : source.scalar ≠ 0 then
    let factor := source.scalar⁻¹
    have factorNonzero : factor ≠ 0 :=
      ExplicitField.inv_ne_zero scalarNonzero
    let representative := source.scale factor factorNonzero
    refine
      { representative := representative
        member := ?_
        factor := factor
        factorNonzero := factorNonzero
        representative_eq_scale := rfl
        equivalent := ⟨factor, factorNonzero, rfl⟩ }
    have rawEqual : representative.toProportion =
        (⟨1, Coordinates3.Vector.scale factor source.vector⟩ : Projective.Basic.Proportion K) :=
          by
      change Purelib.Algebra.Quaternion.Projective.Basic.Proportion.scale factor source.toProportion = _
      apply Proportion.ext
      · exact inverse_mul source.scalar
          scalarNonzero
      · rfl
    rw [rawEqual]
    exact presentation.affineProportion_mem _
  else if tNonzero : source.vector.t ≠ 0 then
    let factor := source.vector.t⁻¹
    have factorNonzero : factor ≠ 0 :=
      ExplicitField.inv_ne_zero tNonzero
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
          factor * source.vector.s⟩⟩ : Projective.Basic.Proportion K) := by
      change Purelib.Algebra.Quaternion.Projective.Basic.Proportion.scale factor source.toProportion = _
      apply Proportion.ext
      · unfold Purelib.Algebra.Quaternion.Projective.Basic.Proportion.scale
        rw [eq_zero_of_not_ne
          presentation.eqDecidable scalarNonzero]
        ring1
      · apply Coordinates3.Vector.ext
        · exact inverse_mul source.vector.t
            tNonzero
        · rfl
        · rfl
    rw [rawEqual]
    exact presentation.infinityTProportion_mem _ _
  else if rNonzero : source.vector.r ≠ 0 then
    let factor := source.vector.r⁻¹
    have factorNonzero : factor ≠ 0 :=
      ExplicitField.inv_ne_zero rNonzero
    let representative := source.scale factor factorNonzero
    refine
      { representative := representative
        member := ?_
        factor := factor
        factorNonzero := factorNonzero
        representative_eq_scale := rfl
        equivalent := ⟨factor, factorNonzero, rfl⟩ }
    have rawEqual : representative.toProportion =
        (⟨0, ⟨0, 1, factor * source.vector.s⟩⟩ : Projective.Basic.Proportion K) := by
      change Purelib.Algebra.Quaternion.Projective.Basic.Proportion.scale factor source.toProportion = _
      apply Proportion.ext
      · unfold Purelib.Algebra.Quaternion.Projective.Basic.Proportion.scale
        rw [eq_zero_of_not_ne
          presentation.eqDecidable scalarNonzero]
        ring1
      · apply Coordinates3.Vector.ext
        · unfold Purelib.Algebra.Quaternion.Projective.Basic.Proportion.scale
            Coordinates3.Vector.scale
          rw [eq_zero_of_not_ne
            presentation.eqDecidable tNonzero]
          ring1
        · exact inverse_mul source.vector.r
            rNonzero
        · rfl
    rw [rawEqual]
    exact presentation.infinityRProportion_mem _
  else
    have sNonzero : source.vector.s ≠ 0 := by
      intro sZero
      apply source.normNonzero
      unfold Purelib.Algebra.Quaternion.Projective.Basic.Proportion.norm
        Coordinates3.Vector.quadrance Coordinates3.Vector.dot
      rw [eq_zero_of_not_ne
        presentation.eqDecidable scalarNonzero,
        eq_zero_of_not_ne
          presentation.eqDecidable tNonzero,
        eq_zero_of_not_ne
          presentation.eqDecidable rNonzero, sZero]
      ring1
    let factor := source.vector.s⁻¹
    have factorNonzero : factor ≠ 0 :=
      ExplicitField.inv_ne_zero sNonzero
    let representative := source.scale factor factorNonzero
    refine
      { representative := representative
        member := ?_
        factor := factor
        factorNonzero := factorNonzero
        representative_eq_scale := rfl
        equivalent := ⟨factor, factorNonzero, rfl⟩ }
    have rawEqual : representative.toProportion =
        (infinitySRepresentative :
          Projective.Basic.Proportion K) := by
      change Purelib.Algebra.Quaternion.Projective.Basic.Proportion.scale factor source.toProportion = _
      apply Proportion.ext
      · unfold Purelib.Algebra.Quaternion.Projective.Basic.Proportion.scale
          infinitySRepresentative
        rw [eq_zero_of_not_ne
          presentation.eqDecidable scalarNonzero]
        ring1
      · apply Coordinates3.Vector.ext
        · unfold Purelib.Algebra.Quaternion.Projective.Basic.Proportion.scale
            Coordinates3.Vector.scale
            infinitySRepresentative
          rw [eq_zero_of_not_ne
            presentation.eqDecidable tNonzero]
          ring1
        · unfold Purelib.Algebra.Quaternion.Projective.Basic.Proportion.scale
            Coordinates3.Vector.scale
            infinitySRepresentative
          rw [eq_zero_of_not_ne
            presentation.eqDecidable rNonzero]
          ring1
        · exact inverse_mul source.vector.s
            sNonzero
    rw [rawEqual]
    exact presentation.infinitySProportion_mem

/-- Certifying the raw coordinates of an already non-null proportion returns the original proportion. -/
theorem certifyNonNull_self (proportion
  : Projective.Basic.NonNullProportion K) :
    presentation.certifyNonNull proportion.toProportion = some proportion := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold certifyNonNull
  rw [dif_neg proportion.normNonzero]

/-- Successful non-null certification preserves the original raw proportion. -/
public theorem
  certifyNonNull_eq_some_toProportion
    {raw : Projective.Basic.Proportion K} {result : Projective.Basic.NonNullProportion K}
    (certified : presentation.certifyNonNull raw = some result) :
    result.toProportion = raw := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold certifyNonNull at certified
  split at certified
  · contradiction
  · injection certified with resultEqual
    exact (congrArg NonNullProportion.toProportion resultEqual).symm

/-- Filtering a duplicate-free proportion list by non-null certification preserves absence of duplicates. -/
public theorem
  certifyNonNull_filterMap_nodup
    (presentation : Presentation.FiniteOddFieldPresentation K) :
    ∀ (values : List (Projective.Basic.Proportion K)), values.Nodup →
      (values.filterMap presentation.certifyNonNull).Nodup
  | [], _ => List.Pairwise.nil
  | head :: tail, nodup => by
      cases certified : presentation.certifyNonNull head with
      | none =>
          rw [FilterMap.filterMap_cons_none certified]
          exact certifyNonNull_filterMap_nodup
            (presentation := presentation) tail
            (List.pairwise_cons.mp nodup).2
      | some headResult =>
          rw [FilterMap.filterMap_cons_some certified]
          apply List.pairwise_cons.mpr
          constructor
          · intro result resultMember resultsEqual
            rcases FilterMap.mem_filterMap.mp resultMember with
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
          · exact
              certifyNonNull_filterMap_nodup
              (presentation := presentation)
              tail
              (List.pairwise_cons.mp nodup).2

/-- The certified enumeration of all non-null proportions contains no duplicates. -/
theorem
  allNonNullProportionRepresentatives_nodup
  :
    presentation.allNonNullProportionRepresentatives.Nodup := by
  unfold allNonNullProportionRepresentatives
  exact certifyNonNull_filterMap_nodup (presentation :=
    presentation)
    presentation.allProportionRepresentatives
    presentation.allProportionRepresentatives_nodup

/-- Every displayed non-null proportion occurs in the certified raw enumeration. -/
theorem
  allNonNullProportionRepresentatives_complete
    (proportion : Projective.Basic.NonNullProportion K) :
    proportion ∈ presentation.allNonNullProportionRepresentatives := by
  unfold allNonNullProportionRepresentatives
  apply FilterMap.mem_filterMap.mpr
  exact
    ⟨proportion.toProportion,
      presentation.allProportionRepresentatives_complete
        proportion.toProportion,
      presentation.certifyNonNull_self proportion⟩

/-- Certifying the value of a retained nonzero scalar returns that scalar with its proof. -/
theorem certifyNonzeroScalar_self
    (scalar : DisplayedNonzeroScalar (K := K)) :
    presentation.certifyNonzeroScalar scalar.value = some scalar := by
  cases scalar with
  | mk value nonzero =>
      letI : DecidableEq K := presentation.eqDecidable
      unfold certifyNonzeroScalar
      rw [dif_neg nonzero]

/-- Successful nonzero certification preserves the input scalar value. -/
private theorem
  certifyNonzeroScalar_eq_some_value
    {raw : K} {result : DisplayedNonzeroScalar (K :=
      K)}
    (certified : presentation.certifyNonzeroScalar raw = some result) :
    result.value = raw := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold certifyNonzeroScalar at certified
  split at certified
  · contradiction
  · injection certified with resultEqual
    exact (congrArg DisplayedNonzeroScalar.value
      resultEqual).symm

/-- Certifying nonzero entries of a duplicate-free scalar list introduces no duplicates. -/
private theorem
  certifyNonzeroScalar_filterMap_nodup :
    ∀ (values : List K), values.Nodup →
      (values.filterMap presentation.certifyNonzeroScalar).Nodup
  | [], _ => List.Pairwise.nil
  | head :: tail, nodup => by
      cases certified : presentation.certifyNonzeroScalar head with
      | none =>
          rw [FilterMap.filterMap_cons_none certified]
          exact
            certifyNonzeroScalar_filterMap_nodup
            tail
            (List.pairwise_cons.mp nodup).2
      | some headResult =>
          rw [FilterMap.filterMap_cons_some certified]
          apply List.pairwise_cons.mpr
          constructor
          · intro result resultMember resultsEqual
            rcases FilterMap.mem_filterMap.mp resultMember with
              ⟨raw, rawMember, rawCertified⟩
            apply (List.pairwise_cons.mp nodup).1 raw rawMember
            calc
              head = headResult.value :=
                (presentation.certifyNonzeroScalar_eq_some_value
                  certified).symm
              _ = result.value :=
                congrArg DisplayedNonzeroScalar.value
                  resultsEqual
              _ = raw :=
                presentation.certifyNonzeroScalar_eq_some_value rawCertified
          · exact
              certifyNonzeroScalar_filterMap_nodup
              tail
              (List.pairwise_cons.mp nodup).2

/-- The finite carrier of certified nonzero scalars contains no duplicates. -/
theorem nonzeroScalarWitnesses_nodup :
    presentation.nonzeroScalarWitnesses.Nodup := by
  unfold nonzeroScalarWitnesses
  exact certifyNonzeroScalar_filterMap_nodup
    presentation
    presentation.carrier presentation.carrierNodup

/-- Every displayed nonzero scalar occurs in the certified finite carrier. -/
theorem nonzeroScalarWitnesses_complete
    (scalar : DisplayedNonzeroScalar (K := K)) :
    scalar ∈ presentation.nonzeroScalarWitnesses := by
  unfold nonzeroScalarWitnesses
  apply FilterMap.mem_filterMap.mpr
  exact
    ⟨scalar.value, presentation.carrierComplete scalar.value,
      presentation.certifyNonzeroScalar_self scalar⟩

/-- Retain a nonzero input scalar, replacing zero by the displayed unit. -/
public def
  displayedNonzeroScalarOfValue (value :
  K) :
    DisplayedNonzeroScalar (K := K) := by
  letI : DecidableEq K := presentation.eqDecidable
  if valueZero : value = 0 then
    exact ⟨1, Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation⟩
  else
    exact ⟨value, valueZero⟩

/-- Forgetting the bundled proof identifies the cached scalar carrier with the independently used list of nonzero field
elements. -/
def nonzeroScalarWitnessValueBijection :
  Bijection.ListBijection
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
    apply Enumeration.FiniteOddFieldPresentation.DisplayedNonzeroScalar.ext
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

/-- The canonical non-null projective enumeration contains no duplicates. -/
theorem
  nonNullProjectiveRepresentatives_nodup
  :
    presentation.nonNullProjectiveRepresentatives.Nodup := by
  unfold nonNullProjectiveRepresentatives
  exact certifyNonNull_filterMap_nodup (presentation :=
    presentation)
    presentation.projectiveRepresentatives
    presentation.projectiveRepresentatives_nodup

/-- Forgetting non-null evidence recovers membership in the raw canonical chart list. -/
theorem raw_mem_of_nonNull_mem
  {proportion : Projective.Basic.NonNullProportion K}
    (member : proportion ∈ presentation.nonNullProjectiveRepresentatives) :
    proportion.toProportion ∈ presentation.projectiveRepresentatives := by
  unfold nonNullProjectiveRepresentatives at member
  rcases FilterMap.mem_filterMap.mp member with
    ⟨raw, rawMember, certified⟩
  rw [presentation.certifyNonNull_eq_some_toProportion certified]
  exact rawMember

/-- The computed normalized representative belongs to the certified canonical enumeration. -/
theorem canonicalize_mem (source :
  Projective.Basic.NonNullProportion K) :
    (presentation.canonicalize source).representative ∈
      presentation.nonNullProjectiveRepresentatives := by
  unfold nonNullProjectiveRepresentatives
  apply FilterMap.mem_filterMap.mpr
  exact
    ⟨(presentation.canonicalize source).representative.toProportion,
      (presentation.canonicalize source).member,
      presentation.certifyNonNull_self
        (presentation.canonicalize source).representative⟩

/-- A displayed canonical projective representative cannot be fixed by a nontrivial scalar. The proof reads the
normalized coordinate equal to one in each of the four charts. -/
private theorem
  scale_factor_eq_one_of_projective_member
    {raw : Projective.Basic.Proportion K}
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
      (fun value : Projective.Basic.Proportion K => value.vector.t) fixed
    rw [rawEq] at coordinate
    change (1 : K) = factor * 1 at coordinate
    simpa only [mul_one] using coordinate.symm
  · have coordinate := congrArg
      (fun value : Projective.Basic.Proportion K => value.vector.r) fixed
    rw [rawEq] at coordinate
    change (1 : K) = factor * 1 at coordinate
    simpa only [mul_one] using coordinate.symm
  · have coordinate := congrArg
      (fun value : Projective.Basic.Proportion K => value.vector.s) fixed
    rw [rawEq] at coordinate
    change (1 : K) = factor * 1 at coordinate
    simpa only [mul_one] using coordinate.symm

/-- The explicit nonzero-scale orbits: one cached scalar paired with one canonical non-null projective representative.
-/
def scaleOrbitCoordinates : List
    (DisplayedNonzeroScalar (K := K) ×
      Projective.Basic.NonNullProportion K) :=
  presentation.nonzeroScalarWitnesses.flatMap fun scalar =>
    presentation.nonNullProjectiveRepresentatives.map fun representative =>
      (scalar, representative)

/-- Orbit-coordinate membership is exactly membership of its scalar and canonical representative. -/
theorem mem_scaleOrbitCoordinates_iff
    (coordinate : DisplayedNonzeroScalar (K := K) ×
      Projective.Basic.NonNullProportion K) :
    coordinate ∈ presentation.scaleOrbitCoordinates ↔
      coordinate.1 ∈ presentation.nonzeroScalarWitnesses ∧
        coordinate.2 ∈ presentation.nonNullProjectiveRepresentatives := by
  constructor
  · intro member
    unfold scaleOrbitCoordinates at member
    rcases Flatten.mem_flatMap.mp member with
      ⟨scalar, scalarMember, pairMember⟩
    rcases Map.mem_map.mp pairMember with
      ⟨representative, representativeMember, pairEq⟩
    subst coordinate
    exact ⟨scalarMember, representativeMember⟩
  · rintro ⟨scalarMember, representativeMember⟩
    unfold scaleOrbitCoordinates
    apply Flatten.mem_flatMap.mpr
    exact
      ⟨coordinate.1, scalarMember,
        Map.mem_map.mpr
          ⟨coordinate.2, representativeMember, rfl⟩⟩

/-- The finite list of scalar-and-representative orbit coordinates has no duplicates. -/
theorem scaleOrbitCoordinates_nodup :
    presentation.scaleOrbitCoordinates.Nodup := by
  unfold scaleOrbitCoordinates
  apply nodup_flatMap_of_nodup
    presentation.nonzeroScalarWitnesses_nodup
  · intro scalar _
    apply Data.List.Nodup.nodup_map_of_injective
    · intro left right equal
      exact congrArg Prod.snd equal
    · exact presentation.nonNullProjectiveRepresentatives_nodup
  · intro left _ right _ different leftPair leftMember rightPair rightMember
      pairEq
    rcases Map.mem_map.mp leftMember with
      ⟨leftRepresentative, _, leftEq⟩
    rcases Map.mem_map.mp rightMember with
      ⟨rightRepresentative, _, rightEq⟩
    apply different
    calc
      left = leftPair.1 := congrArg Prod.fst leftEq
      _ = rightPair.1 := congrArg Prod.fst pairEq
      _ = right := (congrArg Prod.fst rightEq).symm

/-- Normalize a displayed non-null four-tuple and retain the inverse scaling factor needed to reconstruct it from its
canonical projective point. -/
def scaleOrbitForward (source :
  Projective.Basic.NonNullProportion K) :
    DisplayedNonzeroScalar (K := K) ×
      Projective.Basic.NonNullProportion K :=
  let normalization := presentation.canonicalize source
  (⟨normalization.factor⁻¹,
      ExplicitField.inv_ne_zero normalization.factorNonzero⟩,
    normalization.representative)

/-- Reconstruct a displayed non-null four-tuple from its nonzero scale and canonical projective representative. -/
def scaleOrbitBackward
    (coordinate : DisplayedNonzeroScalar (K := K) ×
      Projective.Basic.NonNullProportion K) :
    Projective.Basic.NonNullProportion K :=
  coordinate.2.scale coordinate.1.value coordinate.1.nonzero

/-- Normalizing any non-null proportion gives listed orbit coordinates. -/
theorem scaleOrbitForward_mem (source :
  Projective.Basic.NonNullProportion K) :
    presentation.scaleOrbitForward source ∈
      presentation.scaleOrbitCoordinates := by
  apply (presentation.mem_scaleOrbitCoordinates_iff
    (presentation.scaleOrbitForward source)).2
  exact
    ⟨presentation.nonzeroScalarWitnesses_complete
      (presentation.scaleOrbitForward source).1,
      presentation.canonicalize_mem source⟩

/-- Reconstructing any certified scale and non-null representative gives a listed raw non-null proportion. -/
theorem scaleOrbitBackward_mem
    (coordinate : DisplayedNonzeroScalar (K := K) ×
      Projective.Basic.NonNullProportion K) :
    scaleOrbitBackward coordinate ∈
      presentation.allNonNullProportionRepresentatives :=
  presentation.allNonNullProportionRepresentatives_complete
    (scaleOrbitBackward coordinate)

/-- Reconstruction after normalization returns the original non-null proportion.

The retained inverse scale cancels the normalization factor on the actual stored representative. -/
theorem scaleOrbitBackward_forward
  (source : Projective.Basic.NonNullProportion K) :
    scaleOrbitBackward
      (presentation.scaleOrbitForward source) = source := by
  let normalization := presentation.canonicalize source
  have inverseCancel : normalization.factor⁻¹ * normalization.factor = 1 := by
    calc
      normalization.factor⁻¹ * normalization.factor =
          normalization.factor * normalization.factor⁻¹ := by ring1
      _ = 1 := ExplicitField.mul_inv_cancel normalization.factor
        normalization.factorNonzero
  have rawEq :
      (normalization.representative.scale normalization.factor⁻¹
        (ExplicitField.inv_ne_zero
          normalization.factorNonzero)).toProportion =
        source.toProportion := by
    calc
      (normalization.representative.scale normalization.factor⁻¹
          (ExplicitField.inv_ne_zero
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

/-- Normalization after reconstruction returns the original listed orbit coordinates.

Membership supplies the canonical representative whose first nonzero coordinate fixes both the representative and its
scalar uniquely. -/
theorem scaleOrbitForward_backward
    (coordinate : DisplayedNonzeroScalar (K := K) ×
      Projective.Basic.NonNullProportion K)
    (member : coordinate ∈ presentation.scaleOrbitCoordinates) :
    presentation.scaleOrbitForward
      (scaleOrbitBackward coordinate) = coordinate :=
        by
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
      ExplicitField.mul_ne_zero normalization.factorNonzero
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
      _ = 1 := ExplicitField.mul_inv_cancel normalization.factor
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
  · exact Enumeration.FiniteOddFieldPresentation.DisplayedNonzeroScalar.ext
      scalarEq
  · exact representativeEq.symm

/-- Explicit partition of every displayed non-null four-tuple into a unique nonzero scale and canonical projective
representative. -/
def nonNullScaleOrbitBijection :
  Bijection.ListBijection
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

end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

/-! ## Fully evaluated small-field regression presentations -/

end

end
