module

public import Purelib.Algebra.Field.ExplicitField
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Divine Proportions, Examples 19.5--19.8

The algebraic content of the decimal-field pictures is supplied by the
generic folium theorems.  The `F₁₃` pictures are checked here as closed
certificates on exactly the coordinates printed in the source.  We do not
install a field instance or enumerate the carrier to prove an exclusivity
claim.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterNineteenFolium

open Purelib.Algebra

namespace ChapterNineteenFoliumExamples

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
namespace FieldThirteen

/-- The thirteen displayed residue classes used only for the two closed
source calculations. -/
abbrev F₁₃ := Fin 13

/-- Thirteen is nonzero, enabling residue arithmetic. -/
instance instNeZeroThirteen : NeZero 13 := ⟨by decide⟩

set_option genInjectivity false in
/-- A pair of residue coordinates modulo thirteen. -/
structure Point13 where
  /-- The horizontal coordinate, as a residue modulo thirteen. -/ x : F₁₃
  /-- The vertical coordinate, as a residue modulo thirteen. -/ y : F₁₃
deriving DecidableEq

constructive_injectivity Point13

set_option genInjectivity false in
/-- Three residue coefficients of a displayed affine line modulo thirteen. -/
structure Line13 where
  /-- The horizontal coefficient, as a residue modulo thirteen. -/ a : F₁₃
  /-- The vertical coefficient, as a residue modulo thirteen. -/ b : F₁₃
  /-- The constant coefficient, as a residue modulo thirteen. -/ c : F₁₃
deriving DecidableEq

constructive_injectivity Line13

set_option genInjectivity false in
/-- Six residue coefficients of a displayed quadratic equation modulo thirteen. -/
structure Conic13 where
  /-- The coefficient of x squared, as a residue modulo thirteen. -/ d : F₁₃
  /-- The coefficient of x y, as a residue modulo thirteen. -/ e : F₁₃
  /-- The coefficient of y squared, as a residue modulo thirteen. -/ f : F₁₃
  /-- The coefficient of x, as a residue modulo thirteen. -/ a : F₁₃
  /-- The coefficient of y, as a residue modulo thirteen. -/ b : F₁₃
  /-- The constant coefficient, as a residue modulo thirteen. -/ c : F₁₃
deriving DecidableEq

constructive_injectivity Conic13

/-- Evaluate x cubed plus y cubed plus three x y at a residue point. -/
@[expose] def foliumValue (point : Point13) : F₁₃ :=
  point.x ^ 3 + point.y ^ 3 + 3 * point.x * point.y

/-- The point satisfies the zero equation of the displayed cubic folium. -/
@[expose] def FoliumContains (point : Point13) : Prop :=
  foliumValue point = 0

/-- The cleared folium parameter denominator one plus the cube of the parameter. -/
@[expose] def parameterDenominator13 (parameter : F₁₃) : F₁₃ :=
  1 + parameter ^ 3

/-- Denominator-cleared form of equation (19.3), requiring no inverse table. -/
@[expose] def IsParameterPoint (parameter : F₁₃) (point : Point13) : Prop :=
  parameterDenominator13 parameter * point.x = -3 * parameter ∧
    parameterDenominator13 parameter * point.y = -3 * parameter ^ 2

/-- The displayed affine linear equation vanishes at the supplied residue point. -/
@[expose] def Line13.Contains (line : Line13) (point : Point13) : Prop :=
  line.a * point.x + line.b * point.y + line.c = 0

/-- The displayed quadratic equation vanishes at the supplied residue point. -/
@[expose] def Conic13.Contains (conic : Conic13) (point : Point13) : Prop :=
  conic.d * point.x ^ 2 + conic.e * point.x * point.y +
      conic.f * point.y ^ 2 + conic.a * point.x +
      conic.b * point.y + conic.c = 0

/-- The displayed folium point (0, 0) for parameter 0 modulo thirteen. -/
@[expose] def point0 : Point13 := ⟨0, 0⟩
/-- The displayed folium point (5, 5) for parameter 1 modulo thirteen. -/
@[expose] def point1 : Point13 := ⟨5, 5⟩
/-- The displayed folium point (8, 3) for parameter 2 modulo thirteen. -/
@[expose] def point2 : Point13 := ⟨8, 3⟩
/-- The displayed folium point (2, 6) for parameter 3 modulo thirteen. -/
@[expose] def point3 : Point13 := ⟨2, 6⟩
/-- The displayed folium point (7, 9) for parameter 5 modulo thirteen. -/
@[expose] def point5 : Point13 := ⟨7, 9⟩
/-- The displayed folium point (11, 1) for parameter 6 modulo thirteen. -/
@[expose] def point6 : Point13 := ⟨11, 1⟩
/-- The displayed folium point (3, 8) for parameter 7 modulo thirteen. -/
@[expose] def point7 : Point13 := ⟨3, 8⟩
/-- The displayed folium point (9, 7) for parameter 8 modulo thirteen. -/
@[expose] def point8 : Point13 := ⟨9, 7⟩
/-- The displayed folium point (6, 2) for parameter 9 modulo thirteen. -/
@[expose] def point9 : Point13 := ⟨6, 2⟩
/-- The displayed folium point (1, 11) for parameter 11 modulo thirteen. -/
@[expose] def point11 : Point13 := ⟨1, 11⟩

/-- Example 19.6: all ten parameter labels and coordinates displayed in
Figure 19.4 satisfy both the cleared parameter equation and the folium. -/
theorem displayed_parameter_points :
    (IsParameterPoint 0 point0 ∧ FoliumContains point0) ∧
      (IsParameterPoint 1 point1 ∧ FoliumContains point1) ∧
      (IsParameterPoint 2 point2 ∧ FoliumContains point2) ∧
      (IsParameterPoint 3 point3 ∧ FoliumContains point3) ∧
      (IsParameterPoint 5 point5 ∧ FoliumContains point5) ∧
      (IsParameterPoint 6 point6 ∧ FoliumContains point6) ∧
      (IsParameterPoint 7 point7 ∧ FoliumContains point7) ∧
      (IsParameterPoint 8 point8 ∧ FoliumContains point8) ∧
      (IsParameterPoint 9 point9 ∧ FoliumContains point9) ∧
      (IsParameterPoint 11 point11 ∧ FoliumContains point11) := by
  unfold IsParameterPoint parameterDenominator13 FoliumContains foliumValue
    point0 point1 point2 point3 point5 point6 point7 point8 point9 point11
  decide

/-- The three omitted parameter labels have `1+t³=0`, exactly as stated in
Example 19.6. -/
theorem omitted_parameter_denominators :
    parameterDenominator13 4 = 0 ∧
      parameterDenominator13 10 = 0 ∧
      parameterDenominator13 12 = 0 := by
  unfold parameterDenominator13
  decide

/-- Example 19.6 packaged without an impermissible proof that enumerates all
field elements. -/
theorem example_19_6 :
    parameterDenominator13 4 = 0 ∧
      parameterDenominator13 10 = 0 ∧
      parameterDenominator13 12 = 0 ∧
      (IsParameterPoint 0 point0 ∧ FoliumContains point0) ∧
      (IsParameterPoint 1 point1 ∧ FoliumContains point1) ∧
      (IsParameterPoint 2 point2 ∧ FoliumContains point2) ∧
      (IsParameterPoint 3 point3 ∧ FoliumContains point3) ∧
      (IsParameterPoint 5 point5 ∧ FoliumContains point5) ∧
      (IsParameterPoint 6 point6 ∧ FoliumContains point6) ∧
      (IsParameterPoint 7 point7 ∧ FoliumContains point7) ∧
      (IsParameterPoint 8 point8 ∧ FoliumContains point8) ∧
      (IsParameterPoint 9 point9 ∧ FoliumContains point9) ∧
      (IsParameterPoint 11 point11 ∧ FoliumContains point11) := by
  exact ⟨omitted_parameter_denominators.1,
    omitted_parameter_denominators.2.1,
    omitted_parameter_denominators.2.2,
    displayed_parameter_points⟩

/-- The tangent line `2x+3y+4=0` printed in Example 19.7. -/
@[expose] def tangentLine11 : Line13 := ⟨2, 3, 4⟩

/-- The tangent conic `3x²+3xy+7y²+10x+y+6=0` printed there. -/
@[expose] def tangentConic11 : Conic13 := ⟨3, 3, 7, 10, 1, 6⟩

/-- Substituting `t=11` in (19.5) and (19.6) yields the printed modular
coefficients. -/
theorem parameter_eleven_coefficients :
    (11 * (2 - 11 ^ 3) : F₁₃) = 3 * tangentLine11.a ∧
      (2 * 11 ^ 3 - 1 : F₁₃) = 3 * tangentLine11.b ∧
      (3 * 11 ^ 2 : F₁₃) = 3 * tangentLine11.c ∧
      (3 * 11 * parameterDenominator13 11 : F₁₃) = tangentConic11.d ∧
      (-(parameterDenominator13 11 ^ 2) : F₁₃) = tangentConic11.e ∧
      (3 * 11 ^ 2 * parameterDenominator13 11 : F₁₃) =
        tangentConic11.f ∧
      (9 * 11 ^ 2 : F₁₃) = tangentConic11.a ∧
      (9 * 11 ^ 4 : F₁₃) = tangentConic11.b ∧
      (9 * 11 ^ 3 : F₁₃) = tangentConic11.c := by
  unfold tangentLine11 tangentConic11 parameterDenominator13
  decide

/-- Example 19.7: the displayed base point and every displayed intersection
point satisfy the relevant equations.  The source's count is represented by
these literal witnesses, without a global root enumeration. -/
theorem example_19_7 :
    IsParameterPoint 11 point11 ∧ FoliumContains point11 ∧
      tangentLine11.Contains point11 ∧ tangentLine11.Contains point3 ∧
      tangentConic11.Contains point11 ∧
      tangentConic11.Contains point5 ∧
      tangentConic11.Contains point2 ∧
      tangentConic11.Contains point6 := by
  unfold IsParameterPoint parameterDenominator13 FoliumContains foliumValue
    Line13.Contains Conic13.Contains tangentLine11 tangentConic11
    point11 point3 point5 point2 point6
  decide

end FieldThirteen
end ChapterNineteenFoliumExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterNineteenFolium

end
