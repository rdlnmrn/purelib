module

public import Purelib.Geometry.Rotations.Cayley.Cap
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Algebra.Quadratic.Pair.Basic
import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Filter
import Purelib.Data.List.Membership
import Purelib.Data.List.Nodup
public import Purelib.Geometry.Projective.Quaternion.Finite.Enumeration
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Algebra.Field.Finite.Odd.SquareFibers
import Purelib.Geometry.Quadratic.Finite.Fibers
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Algebra.Field.Finite.Odd

open Purelib.Algebra.Field.Finite.Odd.Presentation

open Purelib.Algebra.Quadratic

open Purelib.Algebra.Quaternion

open Purelib.Algebra.Quaternion.Projective.Basic

open Purelib.Data.List

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Geometry.Rotations.Cayley

open Purelib.LinearAlgebra

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

namespace Purelib.Algebra.Field.Finite.Odd.Presentation

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace FiniteOddFieldPresentation

variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The affine cap-domain quadric excluded by `1 + Q(v) = 0`. -/
def excludedAnchorQuadric : List
  (Coordinates3.Vector K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.vectors.filter fun vector => vector.quadrance = -1

/-- The affine null cone, including its vertex. -/
def nullVectors : List
  (Coordinates3.Vector K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.vectors.filter fun vector => vector.quadrance = 0

/-- Nonzero null anchors. Their caps are precisely the nonidentity half-spread-zero (parabolic) rotations. -/
def nonzeroNullVectors : List
  (Coordinates3.Vector K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.vectors.filter fun vector =>
    vector.quadrance = 0 && decide (vector ≠ Coordinates3.Vector.zero)

/-- Filtered membership retains carrier membership, nullity and nonvanishing.

The original Boolean conjunction records the zero-quadrance and nonzero-vector
decisions. Its two acceptance certificates recover the displayed conditions. -/
theorem mem_nonzeroNullVectors_iff
  (vector : Coordinates3.Vector K) :
    vector ∈ presentation.nonzeroNullVectors ↔
      vector ∈ presentation.vectors ∧
        vector.quadrance = 0 ∧ vector ≠ Coordinates3.Vector.zero := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold FiniteOddFieldPresentation.nonzeroNullVectors
  constructor
  · intro member
    rcases Filter.mem_filter.mp member with ⟨source, accepted⟩
    have nullAccepted : decide (vector.quadrance = 0) = true := by
      cases result : decide (vector.quadrance = 0) with
      | false =>
          rw [result] at accepted
          change false = true at accepted
          nomatch accepted
      | true => rfl
    have nonzeroAccepted : decide (vector ≠ Coordinates3.Vector.zero) = true := by
      rw [nullAccepted] at accepted
      exact accepted
    exact ⟨source, of_decide_eq_true nullAccepted, of_decide_eq_true nonzeroAccepted⟩
  · rintro ⟨source, null, nonzero⟩
    apply Filter.mem_filter.mpr
    refine ⟨source, ?_⟩
    rw [decide_eq_true null, decide_eq_true nonzero]
    rfl

/-- Canonical first-nonzero-coordinate representatives of the projective null directions. The first chart is `(1,r,s)`
with `r²+s²=-1`; the second is `(0,1,s)` with `s²=-1`. No third chart can be null. -/
def nullDirectionRepresentatives : List
  (Coordinates3.Vector K) :=
  ((presentation.twoSquareFiber (-1)).map fun pair =>
      ⟨1, pair.re, pair.im⟩) ++
    (presentation.squareRootFiber (-1)).map fun root => ⟨0, 1, root⟩

/-- The two normalized null-direction charts enumerate representatives without repetitions. -/
theorem
  nullDirectionRepresentatives_nodup :
    presentation.nullDirectionRepresentatives.Nodup := by
  unfold FiniteOddFieldPresentation.nullDirectionRepresentatives
  apply Nodup.nodup_append
  · apply Data.List.Nodup.nodup_map_of_injective
    · intro left right equal
      apply Quadratic.Pair.ext
      · exact congrArg Coordinates3.Vector.r equal
      · exact congrArg Coordinates3.Vector.s equal
    · exact presentation.twoSquareFiber_nodup (-1)
  · apply Data.List.Nodup.nodup_map_of_injective
    · intro left right equal
      exact congrArg Coordinates3.Vector.s equal
    · exact presentation.squareRootFiber_nodup (-1)
  · intro left leftMember right rightMember equal
    rcases Map.mem_map.mp leftMember with
      ⟨pair, _, leftEqual⟩
    rcases Map.mem_map.mp rightMember with
      ⟨root, _, rightEqual⟩
    apply FiniteOddFieldPresentation.one_ne_zero presentation
    calc
      (1 : K) = left.t := congrArg Coordinates3.Vector.t leftEqual
      _ = right.t := congrArg Coordinates3.Vector.t equal
      _ = 0 := (congrArg Coordinates3.Vector.t rightEqual).symm

/-- Every enumerated normalized direction is null. -/
theorem nullDirectionRepresentative_null
  {direction : Coordinates3.Vector K}
    (member : direction ∈ presentation.nullDirectionRepresentatives) :
    direction.quadrance = 0 := by
  unfold FiniteOddFieldPresentation.nullDirectionRepresentatives at member
  rcases Membership.mem_append.mp member with firstChart | secondChart
  · rcases Map.mem_map.mp firstChart with
      ⟨pair, pairMember, equal⟩
    have pairQuadrance :=
      (presentation.mem_twoSquareFiber_iff (-1) pair).1 pairMember
    rw [← equal]
    unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot Quadratic.Pair.quadrance at *
    change (1 : K) * 1 + pair.re * pair.re +
      pair.im * pair.im = 0
    have pairQuadranceMul :
        pair.re * pair.re + pair.im * pair.im = -1 := by
      simpa only [pow_two] using pairQuadrance
    calc
      (1 : K) * 1 + pair.re * pair.re + pair.im * pair.im =
          1 + (pair.re * pair.re + pair.im * pair.im) := by ring1
      _ = 1 + (-1) := by rw [pairQuadranceMul]
      _ = 0 := by ring1
  · rcases Map.mem_map.mp secondChart with
      ⟨root, rootMember, equal⟩
    have rootSquare :=
      (presentation.mem_squareRootFiber_iff (-1) root).1 rootMember
    rw [← equal]
    unfold Coordinates3.Vector.quadrance Coordinates3.Vector.dot
    change (0 : K) * 0 + 1 * 1 + root * root = 0
    have rootSquareMul : root * root = -1 := by
      simpa only [pow_two] using rootSquare
    rw [rootSquareMul]
    ring1

/-- Every enumerated normalized direction is nonzero. -/
theorem
  nullDirectionRepresentative_nonzero
  {direction : Coordinates3.Vector K}
    (member : direction ∈ presentation.nullDirectionRepresentatives) :
    direction ≠ Coordinates3.Vector.zero := by
  unfold FiniteOddFieldPresentation.nullDirectionRepresentatives at member
  rcases Membership.mem_append.mp member with firstChart | secondChart
  · rcases Map.mem_map.mp firstChart with
      ⟨pair, _, equal⟩
    intro directionZero
    apply FiniteOddFieldPresentation.one_ne_zero presentation
    calc
      (1 : K) = direction.t := congrArg Coordinates3.Vector.t equal
      _ = Coordinates3.Vector.zero.t := congrArg Coordinates3.Vector.t directionZero
      _ = 0 := rfl
  · rcases Map.mem_map.mp secondChart with
      ⟨root, _, equal⟩
    intro directionZero
    apply FiniteOddFieldPresentation.one_ne_zero presentation
    calc
      (1 : K) = direction.r := congrArg Coordinates3.Vector.r equal
      _ = Coordinates3.Vector.zero.r := congrArg Coordinates3.Vector.r directionZero
      _ = 0 := rfl

/-- A normalized null direction embeds as an enumerated projective point with scalar coordinate zero. -/
theorem
  nullDirectionRepresentative_projectiveMember
    {direction : Coordinates3.Vector K}
    (member : direction ∈ presentation.nullDirectionRepresentatives) :
    (⟨0, direction⟩ : Projective.Basic.Proportion K) ∈
      presentation.projectiveRepresentatives := by
  unfold FiniteOddFieldPresentation.nullDirectionRepresentatives at member
  rcases Membership.mem_append.mp member with firstChart | secondChart
  · rcases Map.mem_map.mp firstChart with
      ⟨pair, _, equal⟩
    rw [← equal]
    exact presentation.infinityTProportion_mem pair.re pair.im
  · rcases Map.mem_map.mp secondChart with
      ⟨root, _, equal⟩
    rw [← equal]
    exact presentation.infinityRProportion_mem root

set_option genInjectivity false in
/-- Cached normalization of one nonzero null anchor to its canonical projective direction and its nonzero affine
parameter. -/
structure NullDirectionNormalization
  (source : Coordinates3.Vector K) where
  /-- The cached canonical null-direction representative. -/ representative : Coordinates3.Vector K
  /-- The representative belongs to the explicit two-chart list. -/ representativeMember : representative ∈
    presentation.nullDirectionRepresentatives
  /-- The retained affine scaling parameter. -/ parameter : K
  /-- The scaling parameter is nonzero. -/ parameterNonzero : parameter ≠ 0
  /-- The source equals the retained parameter times its canonical representative. -/ source_eq_scale : source =
    Coordinates3.Vector.scale parameter representative

constructive_injectivity NullDirectionNormalization

/-- Normalize a nonzero null vector by its first nonzero coordinate. The impossible third chart is rejected directly
from the null equation. -/
def normalizeNullDirection (source :
  Coordinates3.Vector K)
    (sourceNull : source.quadrance = 0)
    (sourceNonzero : source ≠ Coordinates3.Vector.zero) :
    presentation.NullDirectionNormalization source := by
  letI : DecidableEq K := presentation.eqDecidable
  if tNonzero : source.t ≠ 0 then
    let inverse := source.t⁻¹
    let pair : Quadratic.Pair K (1 : K) :=
      ⟨inverse * source.r, inverse * source.s⟩
    let representative : Coordinates3.Vector K := ⟨1, pair.re, pair.im⟩
    have tCancel := Algebra.Field.ExplicitField.mul_inv_cancel source.t tNonzero
    have residual : source.r ^ 2 + source.s ^ 2 = -(source.t ^ 2) := by
      calc
        source.r ^ 2 + source.s ^ 2 =
            source.quadrance - source.t ^ 2 := by
          unfold Purelib.LinearAlgebra.Coordinates3.Vector.quadrance Purelib.LinearAlgebra.Coordinates3.Vector.dot
          ring1
        _ = -(source.t ^ 2) := by rw [sourceNull]; ring1
    have pairQuadrance : pair.quadrance = -1 := by
      unfold pair Quadratic.Pair.quadrance inverse
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
    · unfold Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.nullDirectionRepresentatives
      apply Membership.mem_append.mpr
      left
      exact Map.mem_map.mpr ⟨pair, pairMember, rfl⟩
    · apply Coordinates3.Vector.ext
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
    let representative : Coordinates3.Vector K := ⟨0, 1, root⟩
    have tZero := FiniteOddFieldPresentation.eq_zero_of_not_ne presentation.eqDecidable tNonzero
    have rCancel := Algebra.Field.ExplicitField.mul_inv_cancel source.r rNonzero
    have residual : source.s ^ 2 = -(source.r ^ 2) := by
      calc
        source.s ^ 2 = source.quadrance - source.r ^ 2 := by
          unfold Purelib.LinearAlgebra.Coordinates3.Vector.quadrance Purelib.LinearAlgebra.Coordinates3.Vector.dot
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
    · unfold Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.nullDirectionRepresentatives
      apply Membership.mem_append.mpr
      right
      exact Map.mem_map.mpr ⟨root, rootMember, rfl⟩
    · apply Coordinates3.Vector.ext
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
    have tZero := FiniteOddFieldPresentation.eq_zero_of_not_ne presentation.eqDecidable tNonzero
    have rZero := FiniteOddFieldPresentation.eq_zero_of_not_ne presentation.eqDecidable rNonzero
    have sSquareZero : source.s * source.s = 0 := by
      calc
        source.s * source.s = source.quadrance := by
          unfold Purelib.LinearAlgebra.Coordinates3.Vector.quadrance Purelib.LinearAlgebra.Coordinates3.Vector.dot
          rw [tZero, rZero]
          ring1
        _ = 0 := sourceNull
    have sZero : source.s = 0 := by
      cases presentation.eqDecidable source.s 0 with
      | isTrue equal => exact equal
      | isFalse sNonzero =>
          exact False.elim
            (Algebra.Field.ExplicitField.mul_ne_zero sNonzero sNonzero sSquareZero)
    apply False.elim
    apply sourceNonzero
    apply Coordinates3.Vector.ext
    · exact tZero
    · exact rZero
    · exact sZero

/-- Canonical null-direction representatives are unique under every displayed nonzero projective scaling. -/
theorem
  nullDirectionRepresentative_eq_of_scaled
    {left right : Coordinates3.Vector K}
    (leftMember : left ∈ presentation.nullDirectionRepresentatives)
    (rightMember : right ∈ presentation.nullDirectionRepresentatives)
    {factor : K} (factorNonzero : factor ≠ 0)
    (scaled : right = Coordinates3.Vector.scale factor left) : left = right := by
  have equivalent :
      (⟨0, left⟩ : Projective.Basic.Proportion K).Equivalent (⟨0, right⟩ : Projective.Basic.Proportion K) := by
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

/-- Scaling one canonical null direction is injective in its affine parameter. -/
theorem nullDirection_scale_injective
  {direction : Coordinates3.Vector K}
    (member : direction ∈ presentation.nullDirectionRepresentatives) :
    Function.Injective (fun parameter : K => Coordinates3.Vector.scale parameter direction) := by
  intro left right equal
  unfold FiniteOddFieldPresentation.nullDirectionRepresentatives at member
  rcases Membership.mem_append.mp member with firstChart | secondChart
  · rcases Map.mem_map.mp firstChart with
      ⟨pair, _, directionEqual⟩
    have coordinate := congrArg Coordinates3.Vector.t equal
    rw [← directionEqual] at coordinate
    change left * 1 = right * 1 at coordinate
    simpa using coordinate
  · rcases Map.mem_map.mp secondChart with
      ⟨root, _, directionEqual⟩
    have coordinate := congrArg Coordinates3.Vector.r equal
    rw [← directionEqual] at coordinate
    change left * 1 = right * 1 at coordinate
    simpa using coordinate

end FiniteOddFieldPresentation

/-! ## Fully evaluated small-field regression presentations -/

end Purelib.Algebra.Field.Finite.Odd.Presentation

end

section
open Purelib
open Purelib.Algebra.Field
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3
open Purelib.Geometry.Rotations.Cayley
open Purelib.Algebra.Field.Finite.Odd
open Purelib.Algebra.Field.Finite.Odd.Presentation
namespace Purelib.Geometry.Rotations.Cayley.Cap
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- A null anchor has nonzero cap denominator in the displayed odd field. -/
public theorem
  capDenominator_ne_zero_of_null_presentation
    (presentation : Presentation.FiniteOddFieldPresentation K)
    (vector : Coordinates3.Vector K) (null : vector.quadrance = 0) :
    Cap.capDenominator vector ≠ 0 := by
  unfold Cap.capDenominator
  rw [null, add_zero]
  exact Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation

end Purelib.Geometry.Rotations.Cayley.Cap
end
