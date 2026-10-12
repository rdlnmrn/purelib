module
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Geometry.Quadratic.Ternary.SplitNullConic
public import Purelib.Geometry.Rotations.Ternary.Split.RationalConjugacy
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.Ternary.Minkowski
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rotations.Ternary.Split.Parabolic

open Purelib

open Purelib.Data.Rat

@[expose] public section

/-!
# Checked rational parabolic conjugacy examples

These examples evaluate the finite split-matrix transporter in both null-conic
charts.  They also exercise the Clifford lift and its projective conjugacy
certificate, rather than checking only a determinant formula.
-/

namespace formalisations.RationalRotations.Chapters.RationalParabolicConjugacyExamples

open Purelib.Geometry.Rotations.Ternary.Split.RationalConjugacy.MinkowskiClifford

/-- The canonical constructive rational coefficient type for the parabolic conjugacy examples. -/
abbrev Scalar := Fraction.Rational

/-- One is nonzero in the rational coefficient field. -/
theorem oneNonzero : (1 : Scalar) ≠ 0 := by decide

/-- Two is nonzero in the rational coefficient field. -/
theorem twoNonzero : (2 : Scalar) ≠ 0 := by decide

open Purelib.Geometry.Rotations.Ternary.Split.RationalConjugacy.MinkowskiClifford.ParabolicConjugacy

/-- This example forces the `first + second = 0` chart on the left and the
ordinary nonzero-sum chart on the right. -/
def chartSwitchData :
  Geometry.Rotations.Ternary.Split.RationalConjugacy.MinkowskiClifford.ParabolicConjugacy.TransportMatrixData oneNonzero
  twoNonzero
    1 (-1) 0 1 2 3 (by decide) (by decide) (by decide) (by decide) :=
  Geometry.Rotations.Ternary.Split.RationalConjugacy.MinkowskiClifford.ParabolicConjugacy.transportMatrixData oneNonzero
    twoNonzero 1 (-1) 0 1 2 3
    (by decide) (by decide) (by decide) (by decide)

/-- The chart-switch transporter is the matrix with rows (0, −4) and (3/2, 3/2). -/
theorem chartSwitch_matrix :
    chartSwitchData.matrix =
      ⟨0, -4, (3 : Scalar) / 2, (3 : Scalar) / 2⟩ := by
  decide

/-- The chart-switch transporter has determinant six. -/
theorem chartSwitch_determinant :
    LinearAlgebra.Coordinates2.Matrix.determinant chartSwitchData.matrix = 6 := by
  decide

/-- The retained Clifford lift conjugates the chart-switch example projectively.

The source uses the zero-sum null-conic chart with parameter two; the target uses the nonzero-sum chart with parameter
three. -/
theorem chartSwitch_projective_conjugacy :
    let left := Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicAt oneNonzero
      (Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford.nullParameter 1 (-1))
      (Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford.nullParameter_isNull oneNonzero 1 (-1)) 2
    let right := Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicAt oneNonzero
      (Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford.nullParameter 0 1)
      (Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford.nullParameter_isNull oneNonzero 0 1) 3
    let conjugator :=
      Geometry.Rotations.Ternary.Split.RationalConjugacy.MinkowskiClifford.ParabolicConjugacy.nonNullFromMatrix
      oneNonzero twoNonzero
      chartSwitchData.matrix chartSwitchData.determinant_nonzero
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.Equivalent right)
      (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.mul
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.mul
          (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.conjugate conjugator) left)
        conjugator) := by
  exact
    ParabolicConjugacy.transported_parabolic_equivalent
    oneNonzero twoNonzero
    1 (-1) 0 1 2 3 (by decide) (by decide) (by decide) (by decide)

/-- A second example stays in the nonzero-sum chart but changes both the null
axis and the sign and magnitude of the parabolic parameter. -/
def genericData :
  Geometry.Rotations.Ternary.Split.RationalConjugacy.MinkowskiClifford.ParabolicConjugacy.TransportMatrixData oneNonzero
  twoNonzero
    2 1 1 2 (-2) 5 (by decide) (by decide) (by decide) (by decide) :=
  Geometry.Rotations.Ternary.Split.RationalConjugacy.MinkowskiClifford.ParabolicConjugacy.transportMatrixData oneNonzero
    twoNonzero 2 1 1 2 (-2) 5
    (by decide) (by decide) (by decide) (by decide)

/-- The generic transporter is the matrix with rows (−5, −1) and (0, 2). -/
theorem generic_matrix :
    genericData.matrix = ⟨-5, -1, 0, 2⟩ := by
  decide

/-- The generic transporter has determinant minus ten. -/
theorem generic_determinant :
    LinearAlgebra.Coordinates2.Matrix.determinant genericData.matrix = -10 := by
  decide

/-- The retained Clifford lift conjugates the generic parabolic example projectively.

Both axes use the nonzero-sum chart, with parabolic parameters minus two and five. -/
theorem generic_projective_conjugacy :
    let left := Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicAt oneNonzero
      (Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford.nullParameter 2 1)
      (Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford.nullParameter_isNull oneNonzero 2 1) (-2)
    let right := Geometry.Rotations.Ternary.Split.Parabolic.MinkowskiClifford.parabolicAt oneNonzero
      (Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford.nullParameter 1 2)
      (Geometry.Quadratic.Ternary.SplitNullConic.MinkowskiClifford.nullParameter_isNull oneNonzero 1 2) 5
    let conjugator :=
      Geometry.Rotations.Ternary.Split.RationalConjugacy.MinkowskiClifford.ParabolicConjugacy.nonNullFromMatrix
      oneNonzero twoNonzero
      genericData.matrix genericData.determinant_nonzero
    (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.Equivalent right)
      (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.mul
        (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.mul
          (Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford.conjugate conjugator) left)
        conjugator) := by
  exact
    ParabolicConjugacy.transported_parabolic_equivalent
    oneNonzero twoNonzero
    2 1 1 2 (-2) 5 (by decide) (by decide) (by decide) (by decide)

end formalisations.RationalRotations.Chapters.RationalParabolicConjugacyExamples
