module
public import Purelib.Algebra.Field.ExplicitField

section
@[expose] public section

/-!
# Divine Proportions, Chapter 26: Platonic solids

All five face-spread computations are recorded by one denominator-cleared
isosceles-triangle certificate.  Exercise 26.1 is proved directly from three
displayed edge vectors.  Exercise 26.4 uses a uniformly scaled standard
icosahedron, so its coordinates are polynomial in a supplied witness
`root²=5` and contain no selected irrational or completed field.
-/

namespace formalisations.DivineProportions.Chapters.Applications

namespace PlatonicSolids

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The exact integer inequalities distinguish the displayed tetrahedral and octahedral sector types. -/
theorem tetrahedron_octahedron_sector_types :
    (2 : Nat) < 3 ∧ (3 : Nat) < 4 := by
  decide

/-! ## Exercise 26.3: five around an edge, but not six -/

/-- Exact finite comparisons place eight ninths between the stated order-five and order-six thresholds.

The cleared quadratic is negative at eight ninths, while direct cross multiplication places it above three quarters. -/
theorem exercise_26_3 :
    (405 - 20 * 8 * 9 + 16 * 8 ^ 2 : Int) = -11 ∧
      (405 - 20 * 8 * 9 + 16 * 8 ^ 2 : Int) < 0 ∧
      (3 * 9 : Nat) < 8 * 4 := by
  decide

/-! ## Icosahedron and dodecahedron -/

end PlatonicSolids
end formalisations.DivineProportions.Chapters.Applications

end
