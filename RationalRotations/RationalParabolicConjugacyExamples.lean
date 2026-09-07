import RationalRotations.RationalParabolicConjugacy

/-!
# Checked rational parabolic conjugacy examples

These examples evaluate the finite split-matrix transporter in both null-conic
charts.  They also exercise the Clifford lift and its projective conjugacy
certificate, rather than checking only a determinant formula.
-/

namespace RationalRotations.RationalParabolicConjugacyExamples

abbrev Scalar := RFAP.ConstructiveFraction.Rational

theorem oneNonzero : (1 : Scalar) ≠ 0 := by decide

theorem twoNonzero : (2 : Scalar) ≠ 0 := by decide

open MinkowskiClifford
open MinkowskiClifford.ParabolicConjugacy

/-- This example forces the `first + second = 0` chart on the left and the
ordinary nonzero-sum chart on the right. -/
def chartSwitchData : TransportMatrixData oneNonzero twoNonzero
    1 (-1) 0 1 2 3 (by decide) (by decide) (by decide) (by decide) :=
  transportMatrixData oneNonzero twoNonzero 1 (-1) 0 1 2 3
    (by decide) (by decide) (by decide) (by decide)

theorem chartSwitch_matrix :
    chartSwitchData.matrix =
      ⟨0, -4, (3 : Scalar) / 2, (3 : Scalar) / 2⟩ := by
  decide

theorem chartSwitch_determinant :
    Matrix2.determinant chartSwitchData.matrix = 6 := by
  decide

theorem chartSwitch_projective_conjugacy :
    let left := parabolicAt oneNonzero (nullParameter 1 (-1))
      (nullParameter_isNull oneNonzero 1 (-1)) 2
    let right := parabolicAt oneNonzero (nullParameter 0 1)
      (nullParameter_isNull oneNonzero 0 1) 3
    let conjugator := nonNullFromMatrix oneNonzero twoNonzero
      chartSwitchData.matrix chartSwitchData.determinant_nonzero
    right.Equivalent
      (TernaryForm.NonNullEvenClifford.mul
        (TernaryForm.NonNullEvenClifford.mul conjugator.conjugate left)
        conjugator) := by
  exact transported_parabolic_equivalent oneNonzero twoNonzero
    1 (-1) 0 1 2 3 (by decide) (by decide) (by decide) (by decide)

/-- A second example stays in the nonzero-sum chart but changes both the null
axis and the sign and magnitude of the parabolic parameter. -/
def genericData : TransportMatrixData oneNonzero twoNonzero
    2 1 1 2 (-2) 5 (by decide) (by decide) (by decide) (by decide) :=
  transportMatrixData oneNonzero twoNonzero 2 1 1 2 (-2) 5
    (by decide) (by decide) (by decide) (by decide)

theorem generic_matrix :
    genericData.matrix = ⟨-5, -1, 0, 2⟩ := by
  decide

theorem generic_determinant :
    Matrix2.determinant genericData.matrix = -10 := by
  decide

theorem generic_projective_conjugacy :
    let left := parabolicAt oneNonzero (nullParameter 2 1)
      (nullParameter_isNull oneNonzero 2 1) (-2)
    let right := parabolicAt oneNonzero (nullParameter 1 2)
      (nullParameter_isNull oneNonzero 1 2) 5
    let conjugator := nonNullFromMatrix oneNonzero twoNonzero
      genericData.matrix genericData.determinant_nonzero
    right.Equivalent
      (TernaryForm.NonNullEvenClifford.mul
        (TernaryForm.NonNullEvenClifford.mul conjugator.conjugate left)
        conjugator) := by
  exact transported_parabolic_equivalent oneNonzero twoNonzero
    2 1 1 2 (-2) 5 (by decide) (by decide) (by decide) (by decide)

end RationalRotations.RationalParabolicConjugacyExamples
