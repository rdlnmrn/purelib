module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Finite.Five
public import Purelib.Algebra.Field.Finite.Five.Presentation
import Purelib.Algebra.Field.Finite.Odd.Presentation
public import Purelib.Algebra.Field.Finite.Seven
public import Purelib.Algebra.Field.Finite.Three
public import Purelib.Geometry.Rotations.FiniteField.Classification
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.Geometry.Projective.Quaternion.Finite.Counts
import Purelib.Geometry.Projective.Quaternion.Finite.Enumeration
import Purelib.Geometry.Quadratic.Finite.Fibers
import Purelib.Geometry.Quadratic.Finite.NullDirections
import Purelib.Geometry.Rotations.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector

open Purelib.Algebra.Field

open Purelib

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

namespace Purelib.Examples.Geometry.Rotations.FieldCounting

open Purelib.Examples

open Purelib.Algebra.Field.Finite.Three renaming Element -> F3
open Purelib.Algebra.Field.Finite.Five renaming Element -> F5
open Purelib.Algebra.Field.Finite.Seven renaming Element -> F7

open Purelib.Examples.Geometry.Rotations

open Purelib.Rotations

variable {K : Type*} [ExplicitField K]

/-! ## Fully evaluated small-field regression presentations -/

namespace CountingExamples

namespace FieldThree

/-- The identity lookup on F₃, giving the retained roots of its square values zero and one. -/
public def
  cachedSquareRoot
  (value : F3) : F3 := value

section
/-- The executable odd-field presentation of F3, retaining its complete carrier, square table and certified square
roots. -/
def presentation :
  Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation F3 where
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

/-- The finite F3 rotation count is 24. -/
theorem rotation_count :
  presentation.rotationCount = 24 := by decide

/-- The actual executable F3 rotation enumeration has length 24. -/
theorem rotation_enumeration_count
  :
    presentation.rotationEnumeration.values.length = 24 :=
      by
  rw [←
    presentation.rotationCount_eq_rotationEnumeration_length]
  exact rotation_count

/-- There are 48 nonnull displayed four-coordinate proportion representatives over F3. -/
theorem
  all_nonNull_proportion_count :
    presentation.allNonNullProportionRepresentatives.length
      = 48 := by
  rw
    [presentation.allNonNullProportionRepresentatives_count_formula]
  decide

/-- The half-spread fiber counts in carrier order are [9,9,6]. -/
theorem halfSpread_fiber_counts :
    ([0, 1, 2] : List F3).map (fun value =>
      presentation.halfSpreadFiberCount value) =
        [9, 9, 6] := by decide

/-- The two-square fiber counts in carrier order are [1,4,4]. -/
theorem twoSquare_fiber_counts :
    ([0, 1, 2] : List F3).map
      presentation.twoSquareCount =
      [1, 4, 4] := by decide

/-- The ternary quadrance fiber counts in carrier order are [9,6,12]. -/
theorem
  ternaryQuadrance_fiber_counts :
    ([0, 1, 2] : List F3).map
      presentation.vectorQuadranceCount =
      [9, 6, 12] := by decide

/-- The F3 null-vector count, including zero, is 9. -/
theorem null_vector_count :
  presentation.vectorQuadranceCount 0 = 9 := by decide

/-- The nonidentity parabolic rotation count over F3 is 8. -/
theorem parabolic_count :
  presentation.parabolicCount = 8 := by decide

/-- The explicit F3 null-direction representatives number 4. -/
theorem null_direction_count :
    presentation.nullDirectionRepresentatives.length = 4 :=
      by decide

/-- There are 12 F3 anchors with quadrance minus one. -/
theorem excluded_anchor_count :
    presentation.vectorQuadranceCount (-1) = 12 := by
      decide

/-- The excluded projective norm-zero quadric has 16 displayed representatives over F3. -/
theorem excluded_projective_count :
    presentation.excludedProjectiveQuadricCount = 16 := by
      decide

/-- The quadrance-square-class kernel has 12 rotations over F3. -/
theorem
  quadrance_class_kernel_count :
    presentation.quadranceClassKernelCount = 12 := by
      decide

end

end FieldThree

namespace FieldFive

/-- The executable odd-field presentation of F5, retaining its complete carrier, square table and certified square
roots. -/
def presentation :
  Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation F5 :=
  Algebra.Field.Finite.Five.Presentation.FieldFive.finiteOddFieldPresentation

section
/-- The finite F5 rotation count is 120. -/
theorem rotation_count :
  presentation.rotationCount = 120 := by
  decide

/-- The actual executable F5 rotation enumeration has length 120. -/
theorem rotation_enumeration_count :
    presentation.rotationEnumeration.values.length = 120 :=
      by
  rw [←
    presentation.rotationCount_eq_rotationEnumeration_length]
  exact rotation_count

/-- There are 480 nonnull displayed four-coordinate proportion representatives over F5. -/
theorem all_nonNull_proportion_count
  :
    presentation.allNonNullProportionRepresentatives.length
      = 480 := by
  rw
    [presentation.allNonNullProportionRepresentatives_count_formula]
  decide

/-- The half-spread fiber counts in carrier order are [25,25,20,30,20]. -/
theorem halfSpread_fiber_counts :
    ([0, 1, 2, 3, 4] : List F5).map (fun value =>
      presentation.halfSpreadFiberCount value) =
        [25, 25, 20, 30, 20] := by decide

/-- The two-square fiber counts in carrier order are [9,4,4,4,4]. -/
theorem twoSquare_fiber_counts :
    ([0, 1, 2, 3, 4] : List F5).map
      presentation.twoSquareCount =
      [9, 4, 4, 4, 4] := by decide

/-- The ternary quadrance fiber counts in carrier order are [25,30,20,20,30]. -/
theorem
  ternaryQuadrance_fiber_counts :
    ([0, 1, 2, 3, 4] : List F5).map
        presentation.vectorQuadranceCount =
      [25, 30, 20, 20, 30] := by decide

/-- The F5 null-vector count, including zero, is 25. -/
theorem null_vector_count :
  presentation.vectorQuadranceCount 0 = 25 := by decide

/-- The nonidentity parabolic rotation count over F5 is 24. -/
theorem parabolic_count :
  presentation.parabolicCount = 24 := by decide

/-- The explicit F5 null-direction representatives number 6. -/
theorem null_direction_count :
    presentation.nullDirectionRepresentatives.length = 6 :=
      by decide

/-- There are 30 F5 anchors with quadrance minus one. -/
theorem excluded_anchor_count :
    presentation.vectorQuadranceCount (-1) = 30 := by decide

/-- The excluded projective norm-zero quadric has 36 displayed representatives over F5. -/
theorem excluded_projective_count :
    presentation.excludedProjectiveQuadricCount = 36 := by
      decide

/-- The quadrance-square-class kernel has 60 rotations over F5. -/
theorem quadrance_class_kernel_count
  :
    presentation.quadranceClassKernelCount = 60 := by
  decide

end

end FieldFive

namespace FieldSeven

/-- The explicit F₇ square-root lookup sending two to three, four to two, and other inputs to themselves. -/
public def
  cachedSquareRoot
  (value : F7) : F7 :=
  if value = 2 then 3 else if value = 4 then 2 else value

section
/-- The executable odd-field presentation of F7, retaining its complete carrier, square table and certified square
roots. -/
def presentation :
  Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation F7 where
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

/-- The finite F7 rotation count is 336. -/
theorem rotation_count :
  presentation.rotationCount = 336 := by
  decide

/-- The actual executable F7 rotation enumeration has length 336. -/
theorem rotation_enumeration_count
  :
    presentation.rotationEnumeration.values.length = 336 :=
      by
  rw [←
    presentation.rotationCount_eq_rotationEnumeration_length]
  exact rotation_count

/-- There are 2016 nonnull displayed four-coordinate proportion representatives over F7. -/
theorem
  all_nonNull_proportion_count :
    presentation.allNonNullProportionRepresentatives.length
      = 2016 := by
  rw
    [presentation.allNonNullProportionRepresentatives_count_formula]
  decide

/-- The F₇ half-spread fiber at zero has 49 rotations. -/
private theorem
  halfSpread_count_zero
  :
    presentation.halfSpreadFiberCount 0 = 49 := by
  decide

/-- The F₇ half-spread fiber at one has 49 rotations. -/
private theorem
  halfSpread_count_one
  :
    presentation.halfSpreadFiberCount 1 = 49 := by
  decide

/-- The F₇ half-spread fiber at two has 56 rotations. -/
private theorem
  halfSpread_count_two
  :
    presentation.halfSpreadFiberCount 2 = 56 := by
  decide

/-- The F₇ half-spread fiber at three has 42 rotations. -/
private theorem
  halfSpread_count_three
  :
    presentation.halfSpreadFiberCount 3 = 42 := by
  decide

/-- The F₇ half-spread fiber at four has 42 rotations. -/
private theorem
  halfSpread_count_four
  :
    presentation.halfSpreadFiberCount 4 = 42 := by
  decide

/-- The F₇ half-spread fiber at five has 42 rotations. -/
private theorem
  halfSpread_count_five
  :
    presentation.halfSpreadFiberCount 5 = 42 := by
  decide

/-- The F₇ half-spread fiber at six has 56 rotations. -/
private theorem
  halfSpread_count_six
  :
    presentation.halfSpreadFiberCount 6 = 56 := by
  decide

/-- The half-spread fiber counts in carrier order are [49,49,56,42,42,42,56]. -/
theorem halfSpread_fiber_counts :
    ([0, 1, 2, 3, 4, 5, 6] : List F7).map (fun value =>
      presentation.halfSpreadFiberCount value) =
        [49, 49, 56, 42, 42, 42, 56] := by
  simp only [List.map_cons, List.map_nil]
  rw [halfSpread_count_zero,
    halfSpread_count_one,
    halfSpread_count_two,
    halfSpread_count_three,
      halfSpread_count_four,
      halfSpread_count_five,
    halfSpread_count_six]

/-- The two-square fiber counts in carrier order are [1,8,8,8,8,8,8]. -/
theorem twoSquare_fiber_counts :
    ([0, 1, 2, 3, 4, 5, 6] : List F7).map
        presentation.twoSquareCount =
      [1, 8, 8, 8, 8, 8, 8] := by decide

/-- The ternary quadrance fiber counts in carrier order are [49,42,42,56,42,56,56]. -/
theorem
  ternaryQuadrance_fiber_counts :
    ([0, 1, 2, 3, 4, 5, 6] : List F7).map
        presentation.vectorQuadranceCount =
      [49, 42, 42, 56, 42, 56, 56] := by decide

/-- The F7 null-vector count, including zero, is 49. -/
theorem null_vector_count :
  presentation.vectorQuadranceCount 0 = 49 := by
  decide

/-- The nonidentity parabolic rotation count over F7 is 48. -/
theorem parabolic_count :
  presentation.parabolicCount = 48 := by
  decide

/-- The explicit F7 null-direction representatives number 8. -/
theorem null_direction_count :
    presentation.nullDirectionRepresentatives.length = 8 :=
      by
  decide

/-- There are 56 F7 anchors with quadrance minus one. -/
theorem excluded_anchor_count :
    presentation.vectorQuadranceCount (-1) = 56 := by
  decide

/-- The excluded projective norm-zero quadric has 64 displayed representatives over F7. -/
theorem excluded_projective_count :
    presentation.excludedProjectiveQuadricCount = 64 := by
  decide

/-- The quadrance-square-class kernel has 168 rotations over F7. -/
theorem
  quadrance_class_kernel_count :
    presentation.quadranceClassKernelCount = 168 := by
  decide

end

end FieldSeven

end CountingExamples

end Purelib.Examples.Geometry.Rotations.FieldCounting

end
