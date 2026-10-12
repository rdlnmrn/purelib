module

public import Purelib.Geometry.Projective.Line.Scale
public import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Nodup

/-!
# Finite projective-line charts

The two original homogeneous coordinates are normalized in the first
nonzero coordinate. The displayed odd-field carrier supplies the affine
chart, and the remaining point is the original pair `(0,1)`.
-/

public section

namespace Purelib.Geometry.Projective.Line.Proj

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.Finite.Odd.Presentation (FiniteOddFieldPresentation)
open Purelib.Data.List

variable {K : Type*} [ExplicitField K] (presentation : FiniteOddFieldPresentation K)

/-- Enumerate the affine pairs `(1,t)` followed by the point `(0,1)`.

The original finite scalar carrier determines the order of the first
chart. These pairs are canonical representatives of all nonzero pairs
up to their original cross-multiplication relation.
-/
@[expose] def finiteRepresentatives : List (Proj K) :=
  presentation.carrier.map (fun value => ⟨1, value⟩) ++ [⟨0, 1⟩]

/-- A listed projective-line point is either an affine pair or the remaining point. -/
theorem finiteRepresentatives_cases {point : Proj K} (member : point ∈ finiteRepresentatives presentation) :
    (∃ value : K, point = ⟨1, value⟩) ∨ point = ⟨0, 1⟩ := by
  rcases Membership.mem_append.mp member with affine | infinity
  · rcases Map.mem_map.mp affine with ⟨value, _, equal⟩
    exact Or.inl ⟨value, equal.symm⟩
  · exact Or.inr (Membership.mem_singleton.mp infinity)

/-- Every listed projective-line pair has a nonzero original coordinate. -/
theorem finiteRepresentatives_nonzero {point : Proj K} (member : point ∈ finiteRepresentatives presentation) :
    point.Nonzero := by
  rcases finiteRepresentatives_cases presentation member with ⟨value, equal⟩ | equal
  · rw [equal]
    exact Or.inl presentation.one_ne_zero
  · rw [equal]
    exact Or.inr presentation.one_ne_zero

/-- The canonical projective-line list contains no repeated pairs. -/
theorem finiteRepresentatives_nodup : (finiteRepresentatives presentation).Nodup := by
  apply Nodup.nodup_append
  · exact Nodup.nodup_map_of_injective (fun _ _ equal => congrArg Proj.q equal) presentation.carrierNodup
  · exact Nodup.nodup_singleton _
  · intro left leftMember right rightMember equal
    rcases Map.mem_map.mp leftMember with ⟨value, _, leftEqual⟩
    have rightEqual := Membership.mem_singleton.mp rightMember
    exact presentation.one_ne_zero (congrArg Proj.p (leftEqual.trans (equal.trans rightEqual)))

/-- The complete projective-line chart list has exactly `q+1` pairs. -/
theorem finiteRepresentatives_length : (finiteRepresentatives presentation).length = presentation.carrier.length + 1 :=
  (Append.length_append _ _).trans (congrArg (fun length => length + 1) (Map.length_map _ _))

/-- Equivalent listed projective-line pairs are the same original coordinate pair.

The affine chart fixes its first coordinate to one. Its points cannot
be equivalent to `(0,1)`, and cross multiplication reads back the second
coordinate without choosing a scale witness.
-/
theorem finiteRepresentatives_eq_of_equivalent {left right : Proj K}
    (leftMember : left ∈ finiteRepresentatives presentation)
    (rightMember : right ∈ finiteRepresentatives presentation) (equivalent : left.Equivalent right) : left = right := by
  rcases finiteRepresentatives_cases presentation leftMember with ⟨leftValue, leftEqual⟩ | leftEqual
  · rcases finiteRepresentatives_cases presentation rightMember with ⟨rightValue, rightEqual⟩ | rightEqual
    · rw [leftEqual, rightEqual] at equivalent ⊢
      apply Proj.ext
      · rfl
      · change 1 * rightValue = 1 * leftValue at equivalent
        exact (ExplicitField.eq_of_mul_eq_mul_left presentation.one_ne_zero equivalent).symm
    · rw [leftEqual, rightEqual] at equivalent
      change 1 * 1 = 0 * leftValue at equivalent
      exact False.elim (presentation.one_ne_zero ((mul_one (1 : K)).symm.trans
        (equivalent.trans (zero_mul leftValue))))
  · rcases finiteRepresentatives_cases presentation rightMember with ⟨rightValue, rightEqual⟩ | rightEqual
    · rw [leftEqual, rightEqual] at equivalent
      change 0 * rightValue = 1 * 1 at equivalent
      exact False.elim (presentation.one_ne_zero ((mul_one (1 : K)).symm.trans
        (equivalent.symm.trans (zero_mul rightValue))))
    · exact leftEqual.trans rightEqual.symm

/-- Compute a listed representative and retain its exact nonzero scale from the original pair.

The first nonzero original coordinate determines the reciprocal factor.
The returned factor, pair and list membership retain the same input point;
the nonzero certificate excludes the zero pair in the second chart.
-/
@[expose] def finiteNormalize (point : Proj K) (nonzero : point.Nonzero) :
    Σ' factor : K, Σ' representative : Proj K, factor ≠ 0 ∧
      representative ∈ finiteRepresentatives presentation ∧ representative = point.scale factor := by
  letI : DecidableEq K := presentation.eqDecidable
  if first : point.p ≠ 0 then
    let factor := point.p⁻¹
    refine ⟨factor, ⟨1, factor * point.q⟩, ExplicitField.inv_ne_zero first, ?_, ?_⟩
    · apply Membership.mem_append.mpr
      exact Or.inl (Map.mem_map.mpr ⟨_, presentation.carrierComplete _, rfl⟩)
    · apply Proj.ext
      · exact ((mul_comm _ _).trans (ExplicitField.mul_inv_cancel _ first)).symm
      · rfl
  else
    have firstZero : point.p = 0 := Decidable.byContradiction first
    have second : point.q ≠ 0 := by
      rcases nonzero with firstNonzero | secondNonzero
      · exact False.elim (firstNonzero firstZero)
      · exact secondNonzero
    refine ⟨point.q⁻¹, ⟨0, 1⟩, ExplicitField.inv_ne_zero second, ?_, ?_⟩
    · exact Membership.mem_append.mpr (Or.inr List.mem_cons_self)
    · apply Proj.ext
      · change 0 = point.q⁻¹ * point.p
        rw [firstZero, mul_zero]
      · exact ((mul_comm _ _).trans (ExplicitField.mul_inv_cancel _ second)).symm

end Purelib.Geometry.Projective.Line.Proj
