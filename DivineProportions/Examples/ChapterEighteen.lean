import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Centers.NinePointCircle

/-!
# Divine Proportions, Chapter 18 worked example

Example 18.1 is a closed arithmetic certificate in the seventeen displayed
residue classes.  It deliberately does not install a field structure or prove
laws by ranging over every residue: only the literal coordinates and
coefficient triples printed in the book are evaluated by the kernel.
-/

namespace DivineProportions

namespace ChapterEighteenExamples

namespace ExampleEighteenOne

/-- The seventeen displayed residue classes used only for this closed
calculation. -/
abbrev F₁₇ := Fin 17

instance instNeZeroSeventeen : NeZero 17 := ⟨by decide⟩

/-- A coordinate pair for the closed `F₁₇` certificate. -/
structure Point17 where
  x : F₁₇
  y : F₁₇
deriving DecidableEq

/-- A displayed coefficient triple for the closed `F₁₇` certificate. -/
structure Line17 where
  a : F₁₇
  b : F₁₇
  c : F₁₇
deriving DecidableEq

/-- Incidence in the displayed residue calculation. -/
def Line17.Contains (line : Line17) (point : Point17) : Prop :=
  line.a * point.x + line.b * point.y + line.c = 0

/-- Equality of line proportions, without selecting a scale factor. -/
def Line17.Equivalent (left right : Line17) : Prop :=
  left.a * right.b = right.a * left.b ∧
    left.a * right.c = right.a * left.c ∧
    left.b * right.c = right.b * left.c

/-- Direction quadrance of a displayed line. -/
def lineNorm17 (line : Line17) : F₁₇ :=
  line.a ^ 2 + line.b ^ 2

/-- Quadrance of two displayed points. -/
def quadrance17 (first second : Point17) : F₁₇ :=
  (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2

/-- The midpoint formula in `F₁₇`, where `2⁻¹=9`. -/
def midpoint17 (first second : Point17) : Point17 :=
  ⟨9 * (first.x + second.x), 9 * (first.y + second.y)⟩

/-- The centroid formula in `F₁₇`, where `3⁻¹=6`. -/
def centroid17 (first second third : Point17) : Point17 :=
  ⟨6 * (first.x + second.x + third.x),
    6 * (first.y + second.y + third.y)⟩

/-- The displayed line through two points. -/
def lineThrough17 (first second : Point17) : Line17 :=
  ⟨first.y - second.y, second.x - first.x,
    first.x * second.y - second.x * first.y⟩

/-- The displayed altitude through a point to a line. -/
def altitudeThrough17 (point : Point17) (line : Line17) : Line17 :=
  ⟨-line.b, line.a, line.b * point.x - line.a * point.y⟩

/-- Membership in the circle with displayed center and quadrance. -/
def circleContains17
    (center : Point17) (circleQuadrance : F₁₇) (point : Point17) : Prop :=
  quadrance17 center point = circleQuadrance

def a₁ : Point17 := ⟨2, 3⟩
def a₂ : Point17 := ⟨10, 5⟩
def a₃ : Point17 := ⟨6, 12⟩

/-- The side `A₂A₃`, opposite `A₁`. -/
def line₁ : Line17 := ⟨2, 6, 1⟩

/-- The side `A₁A₃`, opposite `A₂`. -/
def line₂ : Line17 := ⟨7, 12, 1⟩

/-- The null side `A₁A₂`, opposite `A₃`. -/
def line₃ : Line17 := ⟨12, 3, 1⟩

def circumcenter : Point17 := ⟨5, 8⟩
def orthocenter : Point17 := ⟨8, 4⟩
def centroid : Point17 := ⟨6, 1⟩

def midpoint₁ : Point17 := ⟨8, 0⟩
def midpoint₂ : Point17 := ⟨4, 16⟩
def midpoint₃ : Point17 := ⟨6, 4⟩

def ninePointCenter17 : Point17 := ⟨15, 6⟩
def eulerLine : Line17 := ⟨3, 15, 1⟩

def foot₁ : Point17 := ⟨0, 14⟩
def foot₂ : Point17 := ⟨13, 15⟩

def orthocenterMidpoint₁ : Point17 := ⟨5, 12⟩
def orthocenterMidpoint₂ : Point17 := ⟨9, 13⟩
def orthocenterMidpoint₃ : Point17 := ⟨7, 8⟩

/-- The three book-provided side triples represent the corresponding lines
through the vertices and contain their two endpoints. -/
theorem displayed_side_lines :
    line₁.Equivalent (lineThrough17 a₂ a₃) ∧
      line₂.Equivalent (lineThrough17 a₁ a₃) ∧
      line₃.Equivalent (lineThrough17 a₁ a₂) ∧
      line₁.Contains a₂ ∧ line₁.Contains a₃ ∧
      line₂.Contains a₁ ∧ line₂.Contains a₃ ∧
      line₃.Contains a₁ ∧ line₃.Contains a₂ := by
  unfold Line17.Equivalent Line17.Contains lineThrough17
    line₁ line₂ line₃ a₁ a₂ a₃
  decide

/-- The third side is null, while the other two sides admit ordinary altitude
feet. -/
theorem side_nullity :
    lineNorm17 line₁ ≠ 0 ∧ lineNorm17 line₂ ≠ 0 ∧
      lineNorm17 line₃ = 0 := by
  unfold lineNorm17 line₁ line₂ line₃
  decide

/-- The displayed circumcenter has equal quadrance to all three vertices. -/
theorem circumcenter_quadrances :
    quadrance17 circumcenter a₁ = 0 ∧
      quadrance17 circumcenter a₂ = 0 ∧
      quadrance17 circumcenter a₃ = 0 := by
  unfold quadrance17 circumcenter a₁ a₂ a₃
  decide

/-- The displayed orthocenter lies on all three displayed altitudes. -/
theorem orthocenter_altitudes :
    (altitudeThrough17 a₁ line₁).Contains orthocenter ∧
      (altitudeThrough17 a₂ line₂).Contains orthocenter ∧
      (altitudeThrough17 a₃ line₃).Contains orthocenter := by
  unfold Line17.Contains altitudeThrough17 orthocenter
    a₁ a₂ a₃ line₁ line₂ line₃
  decide

/-- The printed centroid and all three side midpoints are the values produced
by the finite formulas. -/
theorem centroid_and_side_midpoints :
    centroid17 a₁ a₂ a₃ = centroid ∧
      midpoint17 a₂ a₃ = midpoint₁ ∧
      midpoint17 a₁ a₃ = midpoint₂ ∧
      midpoint17 a₁ a₂ = midpoint₃ := by
  unfold centroid17 midpoint17 centroid midpoint₁ midpoint₂ midpoint₃
    a₁ a₂ a₃
  decide

/-- The printed nine-point center is the midpoint of `CO`, and the three
side midpoints have its displayed null-circle quadrance zero. -/
theorem nine_point_center_and_quadrance :
    midpoint17 circumcenter orthocenter = ninePointCenter17 ∧
      quadrance17 ninePointCenter17 midpoint₁ = 0 ∧
      quadrance17 ninePointCenter17 midpoint₂ = 0 ∧
      quadrance17 ninePointCenter17 midpoint₃ = 0 := by
  unfold midpoint17 quadrance17 circumcenter orthocenter ninePointCenter17
    midpoint₁ midpoint₂ midpoint₃
  decide

/-- The two existing altitude feet have exactly the two incidence properties
that characterize them.  The missing third foot is accounted for by the null
side in `side_nullity`. -/
theorem altitude_feet :
    line₁.Contains foot₁ ∧
      (altitudeThrough17 a₁ line₁).Contains foot₁ ∧
      line₂.Contains foot₂ ∧
      (altitudeThrough17 a₂ line₂).Contains foot₂ := by
  unfold Line17.Contains altitudeThrough17 line₁ line₂ a₁ a₂ foot₁ foot₂
  decide

/-- The altitude through `A₃` to the null side `l₃` has no intersection with
that side, so the source's missing `F₃` is a proved absence rather than an
omitted coordinate.  The proof is Presburger normalization of the two
displayed modular linear equations, not enumeration of the carrier. -/
theorem no_third_altitude_foot (candidate : Point17) :
    ¬ (line₃.Contains candidate ∧
      (altitudeThrough17 a₃ line₃).Contains candidate) := by
  intro bothIncidences
  rcases candidate with ⟨⟨x, xLess⟩, ⟨y, yLess⟩⟩
  simp only [Line17.Contains, altitudeThrough17, line₃, a₃,
    Fin.add_def, Fin.mul_def, Fin.neg_def, Fin.sub_def] at bothIncidences
  have firstEquation := congrArg Fin.val bothIncidences.1
  have secondEquation := congrArg Fin.val bothIncidences.2
  simp at firstEquation secondEquation
  change (12 * x + 3 * y + 1) % 17 = 0 at firstEquation
  change (14 * x + 12 * y + 27) % 17 = 0 at secondEquation
  omega0

/-- The three printed points `Pᵢ` are the midpoints of `AᵢO`. -/
theorem orthocenter_midpoints :
    midpoint17 a₁ orthocenter = orthocenterMidpoint₁ ∧
      midpoint17 a₂ orthocenter = orthocenterMidpoint₂ ∧
      midpoint17 a₃ orthocenter = orthocenterMidpoint₃ := by
  unfold midpoint17 a₁ a₂ a₃ orthocenter orthocenterMidpoint₁
    orthocenterMidpoint₂ orthocenterMidpoint₃
  decide

/-- All nine points named in the source—including the center itself—lie on
the quadrance-zero nine-point circle. -/
theorem null_nine_point_circle :
    circleContains17 ninePointCenter17 0 midpoint₁ ∧
      circleContains17 ninePointCenter17 0 midpoint₂ ∧
      circleContains17 ninePointCenter17 0 midpoint₃ ∧
      circleContains17 ninePointCenter17 0 foot₁ ∧
      circleContains17 ninePointCenter17 0 foot₂ ∧
      circleContains17 ninePointCenter17 0 orthocenterMidpoint₁ ∧
      circleContains17 ninePointCenter17 0 orthocenterMidpoint₂ ∧
      circleContains17 ninePointCenter17 0 orthocenterMidpoint₃ ∧
      circleContains17 ninePointCenter17 0 ninePointCenter17 := by
  unfold circleContains17 quadrance17 ninePointCenter17 midpoint₁ midpoint₂
    midpoint₃ foot₁ foot₂ orthocenterMidpoint₁ orthocenterMidpoint₂
    orthocenterMidpoint₃
  decide

/-- The four printed centers lie on the displayed Euler line. -/
theorem euler_line_incidences :
    eulerLine.Contains orthocenter ∧
      eulerLine.Contains ninePointCenter17 ∧
      eulerLine.Contains centroid ∧
      eulerLine.Contains circumcenter := by
  unfold Line17.Contains eulerLine orthocenter ninePointCenter17 centroid
    circumcenter
  decide

/-- Example 18.1, packaged as the complete collection of its closed
arithmetic certificates. -/
theorem example_18_1 :
    lineNorm17 line₃ = 0 ∧
      (∀ candidate : Point17,
        ¬ (line₃.Contains candidate ∧
          (altitudeThrough17 a₃ line₃).Contains candidate)) ∧
      midpoint17 circumcenter orthocenter = ninePointCenter17 ∧
      circleContains17 ninePointCenter17 0 midpoint₁ ∧
      circleContains17 ninePointCenter17 0 midpoint₂ ∧
      circleContains17 ninePointCenter17 0 midpoint₃ ∧
      circleContains17 ninePointCenter17 0 foot₁ ∧
      circleContains17 ninePointCenter17 0 foot₂ ∧
      circleContains17 ninePointCenter17 0 orthocenterMidpoint₁ ∧
      circleContains17 ninePointCenter17 0 orthocenterMidpoint₂ ∧
      circleContains17 ninePointCenter17 0 orthocenterMidpoint₃ ∧
      circleContains17 ninePointCenter17 0 ninePointCenter17 ∧
      eulerLine.Contains orthocenter ∧
      eulerLine.Contains ninePointCenter17 ∧
      eulerLine.Contains centroid ∧
      eulerLine.Contains circumcenter := by
  exact ⟨side_nullity.2.2, no_third_altitude_foot,
    nine_point_center_and_quadrance.1,
    null_nine_point_circle.1, null_nine_point_circle.2.1,
    null_nine_point_circle.2.2.1, null_nine_point_circle.2.2.2.1,
    null_nine_point_circle.2.2.2.2.1,
    null_nine_point_circle.2.2.2.2.2.1,
    null_nine_point_circle.2.2.2.2.2.2.1,
    null_nine_point_circle.2.2.2.2.2.2.2.1,
    null_nine_point_circle.2.2.2.2.2.2.2.2,
    euler_line_incidences.1, euler_line_incidences.2.1,
    euler_line_incidences.2.2.1, euler_line_incidences.2.2.2⟩

end ExampleEighteenOne

end ChapterEighteenExamples

end DivineProportions
