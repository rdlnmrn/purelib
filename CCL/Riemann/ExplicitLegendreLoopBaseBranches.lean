import CCL.Riemann.LegendreFactorGeometry
import CCL.Riemann.PreparedRefinementPrograms

/-!
# Explicit finite branch tracks at the Legendre loop base

The rational root boxes already used by the concrete Legendre crossing are
upgraded here to degree-complete shrinking branch tracks.  Factorwise vertical
and horizontal line clearances supply the four pieces of ambient evidence
required by `WindingOneState`, so the finite period layer can consume these
tracks directly without replaying the generic global isolator or Newton
extraction.
-/

namespace CCL.Riemann.ExplicitLegendreLoopBaseBranches

open CCL.Riemann.LegendrePaths
open CCL.Riemann.PeriodMatrix

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

/-- The common rational loop base, kept independent of the heavyweight
worked crossing-segment example. -/
def baseParameter : Gaussian := gaussian (1 / 4) 2

/-- The exact Legendre curve at the common rational loop base. -/
def baseCurve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve 1 where
  polynomial := polynomial baseParameter
  nonzero := polynomial_isZero baseParameter
  squarefree := CCL.Riemann.LegendreSquarefree.certificate baseParameter
    (by decide)
  degreeShape := .odd (polynomial_natDegree baseParameter)

@[simp] theorem baseCurve_polynomial :
    baseCurve.polynomial =
      CCL.Riemann.LegendrePaths.polynomial baseParameter := rfl

theorem baseCurve_degree : baseCurve.polynomial.natDegree = 3 := by
  exact CCL.Riemann.LegendrePaths.polynomial_natDegree baseParameter

private theorem finThree_cases (index : Fin 3) :
    index = 0 ∨ index = 1 ∨ index = 2 := by
  rcases index with ⟨value, bound⟩
  omega0

def baseFactors :=
  CCL.Riemann.LegendreFactorGeometry.factors baseParameter

def baseFactorsVerticalClearance (x : Coordinate)
    (apartZero : x ≠ 0)
    (apartMoving : x ≠ baseParameter.re)
    (apartOne : x ≠ 1) :
    RFAP.BoxClearance.VerticalLineClearance baseFactors
      (RFAP.GlobalWinding.largeSquareBox baseCurve.polynomial) x :=
  RFAP.BoxClearance.VerticalLineClearance.mul
    (RFAP.BoxClearance.VerticalLineClearance.mul
      (RFAP.AffineWinding.translatedCoordinate_verticalLineClearance
        0 _ x apartZero)
      (RFAP.AffineWinding.translatedCoordinate_verticalLineClearance
        baseParameter _ x apartMoving))
    (RFAP.AffineWinding.translatedCoordinate_verticalLineClearance
      1 _ x apartOne)

def basePolynomialVerticalClearance (x : Coordinate)
    (apartZero : x ≠ 0)
    (apartMoving : x ≠ baseParameter.re)
    (apartOne : x ≠ 1) :
    RFAP.BoxClearance.VerticalLineClearance baseCurve.polynomial
      (RFAP.GlobalWinding.largeSquareBox baseCurve.polynomial) x := by
  rw [baseCurve_polynomial,
    CCL.Riemann.LegendreFactorGeometry.polynomial_eq_factors]
  exact baseFactorsVerticalClearance x apartZero apartMoving apartOne

def baseFactorsHorizontalClearance (y : Coordinate)
    (apartZero : y ≠ 0)
    (apartMoving : y ≠ baseParameter.im) :
    RFAP.BoxClearance.HorizontalLineClearance baseFactors
      (RFAP.GlobalWinding.largeSquareBox baseCurve.polynomial) y :=
  RFAP.BoxClearance.HorizontalLineClearance.mul
    (RFAP.BoxClearance.HorizontalLineClearance.mul
      (RFAP.AffineWinding.translatedCoordinate_horizontalLineClearance
        0 _ y apartZero)
      (RFAP.AffineWinding.translatedCoordinate_horizontalLineClearance
        baseParameter _ y apartMoving))
    (RFAP.AffineWinding.translatedCoordinate_horizontalLineClearance
      1 _ y apartZero)

def basePolynomialHorizontalClearance (y : Coordinate)
    (apartZero : y ≠ 0)
    (apartMoving : y ≠ baseParameter.im) :
    RFAP.BoxClearance.HorizontalLineClearance baseCurve.polynomial
      (RFAP.GlobalWinding.largeSquareBox baseCurve.polynomial) y := by
  rw [baseCurve_polynomial,
    CCL.Riemann.LegendreFactorGeometry.polynomial_eq_factors]
  exact baseFactorsHorizontalClearance y apartZero apartMoving

/-- Large pairwise-separated period boxes.  Period preparation benefits from
anchors far from every branch point, independently of the narrower projection
owners used by concrete braid-extraction clients. -/
def baseBranchBox : Fin 3 → RFAP.Boxes.Box
  | ⟨0, _⟩ =>
      { xLower := -(1 / 2)
        xUpper := 1 / 16
        yLower := -(1 / 2)
        yUpper := 1 / 2
        x_valid := by decide
        y_valid := by decide }
  | ⟨1, _⟩ =>
      { xLower := 1 / 8
        xUpper := 3 / 8
        yLower := 3 / 2
        yUpper := 5 / 2
        x_valid := by decide
        y_valid := by decide }
  | ⟨2, _⟩ =>
      { xLower := 15 / 16
        xUpper := 3 / 2
        yLower := -(1 / 2)
        yUpper := 1 / 2
        x_valid := by decide
        y_valid := by decide }

theorem baseBranchBox_proper (index : Fin 3) :
    (baseBranchBox index).Proper := by
  rcases finThree_cases index with h | h | h <;> subst index <;>
    constructor <;> decide

def baseBranchFactorsClearance : ∀ index : Fin 3,
    RFAP.BoxClearance.BoundaryClearance baseFactors (baseBranchBox index)
  | ⟨0, _⟩ =>
      CCL.Riemann.LegendreFactorGeometry.factorsClearance
        (CCL.Riemann.LegendreFactorGeometry.centeredClearance 0
          (by decide +revert) (by decide +revert)
          (by decide +revert) (by decide +revert))
        (CCL.Riemann.LegendreFactorGeometry.aboveClearance
          baseParameter
            (by decide +revert))
        (CCL.Riemann.LegendreFactorGeometry.rightClearance 1
          (by decide +revert))
  | ⟨1, _⟩ =>
      CCL.Riemann.LegendreFactorGeometry.factorsClearance
        (CCL.Riemann.LegendreFactorGeometry.leftClearance 0
          (by decide +revert))
        (CCL.Riemann.LegendreFactorGeometry.centeredClearance
          baseParameter
          (by decide +revert) (by decide +revert)
          (by decide +revert) (by decide +revert))
        (CCL.Riemann.LegendreFactorGeometry.rightClearance 1
          (by decide +revert))
  | ⟨2, _⟩ =>
      CCL.Riemann.LegendreFactorGeometry.factorsClearance
        (CCL.Riemann.LegendreFactorGeometry.leftClearance 0
          (by decide +revert))
        (CCL.Riemann.LegendreFactorGeometry.aboveClearance
          baseParameter
            (by decide +revert))
        (CCL.Riemann.LegendreFactorGeometry.centeredClearance 1
          (by decide +revert) (by decide +revert)
          (by decide +revert) (by decide +revert))

def baseBranchClearance (index : Fin 3) :
    RFAP.BoxClearance.BoundaryClearance baseCurve.polynomial
      (baseBranchBox index) := by
  rw [baseCurve_polynomial,
    CCL.Riemann.LegendreFactorGeometry.polynomial_eq_factors]
  exact baseBranchFactorsClearance index

theorem baseBranchWinding (index : Fin 3) :
    RFAP.Winding.quadrupledBoxWinding baseCurve.polynomial
      (baseBranchBox index) = 4 := by
  rcases finThree_cases index with h | h | h
  · subst index
    rw [baseCurve_polynomial,
      CCL.Riemann.LegendreFactorGeometry.polynomial_eq_factors]
    apply CCL.Riemann.LegendreFactorGeometry.factors_winding_of_sum
      (baseBranchBox_proper 0)
      (CCL.Riemann.LegendreFactorGeometry.centeredClearance 0
        (by decide) (by decide) (by decide) (by decide))
      (CCL.Riemann.LegendreFactorGeometry.aboveClearance
        baseParameter (by decide))
      (CCL.Riemann.LegendreFactorGeometry.rightClearance 1 (by decide))
    have zeroWinding : RFAP.Winding.quadrupledBoxWinding
        (CCL.Riemann.LegendreFactorGeometry.factor 0) (baseBranchBox 0) = 4 :=
      RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 0
        (by decide) (by decide) (by decide) (by decide)
    have movingWinding : RFAP.Winding.quadrupledBoxWinding
        (CCL.Riemann.LegendreFactorGeometry.factor baseParameter)
          (baseBranchBox 0) = 0 := by decide
    have oneWinding : RFAP.Winding.quadrupledBoxWinding
        (CCL.Riemann.LegendreFactorGeometry.factor 1) (baseBranchBox 0) = 0 :=
      by decide
    rw [zeroWinding, movingWinding, oneWinding]
    ring1
  · subst index
    rw [baseCurve_polynomial,
      CCL.Riemann.LegendreFactorGeometry.polynomial_eq_factors]
    apply CCL.Riemann.LegendreFactorGeometry.factors_winding_of_sum
      (baseBranchBox_proper 1)
      (CCL.Riemann.LegendreFactorGeometry.leftClearance 0 (by decide))
      (CCL.Riemann.LegendreFactorGeometry.centeredClearance
        baseParameter
        (by decide) (by decide) (by decide) (by decide))
      (CCL.Riemann.LegendreFactorGeometry.rightClearance 1 (by decide))
    have zeroWinding : RFAP.Winding.quadrupledBoxWinding
        (CCL.Riemann.LegendreFactorGeometry.factor 0) (baseBranchBox 1) = 0 :=
      CCL.Riemann.LegendreFactorGeometry.factor_winding_zero_of_left 0
        (baseBranchBox_proper 1)
        (CCL.Riemann.LegendreFactorGeometry.leftClearance 0 (by decide))
        (by decide)
    have movingWinding : RFAP.Winding.quadrupledBoxWinding
        (CCL.Riemann.LegendreFactorGeometry.factor baseParameter)
          (baseBranchBox 1) = 4 :=
      RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate
        baseParameter
          (by decide) (by decide) (by decide) (by decide)
    have oneWinding : RFAP.Winding.quadrupledBoxWinding
        (CCL.Riemann.LegendreFactorGeometry.factor 1) (baseBranchBox 1) = 0 :=
      CCL.Riemann.LegendreFactorGeometry.factor_winding_zero_of_right 1
        (baseBranchBox_proper 1)
        (CCL.Riemann.LegendreFactorGeometry.rightClearance 1 (by decide))
        (by decide)
    rw [zeroWinding, movingWinding, oneWinding]
    ring1
  · subst index
    rw [baseCurve_polynomial,
      CCL.Riemann.LegendreFactorGeometry.polynomial_eq_factors]
    apply CCL.Riemann.LegendreFactorGeometry.factors_winding_of_sum
      (baseBranchBox_proper 2)
      (CCL.Riemann.LegendreFactorGeometry.leftClearance 0 (by decide))
      (CCL.Riemann.LegendreFactorGeometry.aboveClearance
        baseParameter (by decide))
      (CCL.Riemann.LegendreFactorGeometry.centeredClearance 1
        (by decide) (by decide) (by decide) (by decide))
    have zeroWinding : RFAP.Winding.quadrupledBoxWinding
        (CCL.Riemann.LegendreFactorGeometry.factor 0) (baseBranchBox 2) = 0 :=
      by decide
    have movingWinding : RFAP.Winding.quadrupledBoxWinding
        (CCL.Riemann.LegendreFactorGeometry.factor baseParameter)
          (baseBranchBox 2) = 0 := by decide
    have oneWinding : RFAP.Winding.quadrupledBoxWinding
        (CCL.Riemann.LegendreFactorGeometry.factor 1) (baseBranchBox 2) = 4 :=
      RFAP.AffineWinding.quadrupledBoxWinding_translatedCoordinate 1
        (by decide) (by decide) (by decide) (by decide)
    rw [zeroWinding, movingWinding, oneWinding]
    ring1

/-- One small common rational floor retained in the runtime representation of
the explicit branch states.  The stronger factorwise clearances above prove
this floor, but keeping their normalized products out of the state payload
makes the downstream prepared-path checker substantially cheaper to execute. -/
private def periodClearanceFloor : Coordinate where
  num := 1
  den := 262144
  den_pos := by decide
  reduced := ⟨⟨1, 0, by decide⟩⟩

private theorem periodClearanceFloor_positive :
    0 < periodClearanceFloor := by decide

private def boundaryClearanceWithFloor
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {box : RFAP.Boxes.Box}
    (lower : ∀ value : RFAP.ConstructiveGaussian.Gaussian,
      RFAP.BoxClearance.OnBoxBoundary box value →
        periodClearanceFloor <=
          RFAP.ConstructiveGaussian.Gaussian.normSq
            (polynomial.eval value)) :
    RFAP.BoxClearance.BoundaryClearance polynomial box where
  bound := periodClearanceFloor
  positive := periodClearanceFloor_positive
  lower := lower

private def verticalClearanceWithFloor
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box} {x : Coordinate}
    (lower : ∀ y : Coordinate, ambient.yLower <= y →
      y <= ambient.yUpper → periodClearanceFloor <=
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval (RFAP.Winding.point x y))) :
    RFAP.BoxClearance.VerticalLineClearance polynomial ambient x where
  bound := periodClearanceFloor
  positive := periodClearanceFloor_positive
  lower := lower

private def horizontalClearanceWithFloor
    {polynomial : RFAP.ConstructivePolynomial.GaussianPolynomial}
    {ambient : RFAP.Boxes.Box} {y : Coordinate}
    (lower : ∀ x : Coordinate, ambient.xLower <= x →
      x <= ambient.xUpper → periodClearanceFloor <=
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (polynomial.eval (RFAP.Winding.point x y))) :
    RFAP.BoxClearance.HorizontalLineClearance polynomial ambient y where
  bound := periodClearanceFloor
  positive := periodClearanceFloor_positive
  lower := lower

private def rawAmbientLeftClearance (index : Fin 3) :
    RFAP.BoxClearance.VerticalLineClearance baseCurve.polynomial
      (RFAP.GlobalWinding.largeSquareBox baseCurve.polynomial)
      (baseBranchBox index).xLower :=
  basePolynomialVerticalClearance _
    (by rcases finThree_cases index with h | h | h <;> subst index <;> decide)
    (by rcases finThree_cases index with h | h | h <;> subst index <;> decide)
    (by rcases finThree_cases index with h | h | h <;> subst index <;> decide)

private def rawAmbientRightClearance (index : Fin 3) :
    RFAP.BoxClearance.VerticalLineClearance baseCurve.polynomial
      (RFAP.GlobalWinding.largeSquareBox baseCurve.polynomial)
      (baseBranchBox index).xUpper :=
  basePolynomialVerticalClearance _
    (by rcases finThree_cases index with h | h | h <;> subst index <;> decide)
    (by rcases finThree_cases index with h | h | h <;> subst index <;> decide)
    (by rcases finThree_cases index with h | h | h <;> subst index <;> decide)

private def rawAmbientBottomClearance (index : Fin 3) :
    RFAP.BoxClearance.HorizontalLineClearance baseCurve.polynomial
      (RFAP.GlobalWinding.largeSquareBox baseCurve.polynomial)
      (baseBranchBox index).yLower :=
  basePolynomialHorizontalClearance _
    (by rcases finThree_cases index with h | h | h <;> subst index <;> decide)
    (by rcases finThree_cases index with h | h | h <;> subst index <;> decide)

private def rawAmbientTopClearance (index : Fin 3) :
    RFAP.BoxClearance.HorizontalLineClearance baseCurve.polynomial
      (RFAP.GlobalWinding.largeSquareBox baseCurve.polynomial)
      (baseBranchBox index).yUpper :=
  basePolynomialHorizontalClearance _
    (by rcases finThree_cases index with h | h | h <;> subst index <;> decide)
    (by rcases finThree_cases index with h | h | h <;> subst index <;> decide)

private theorem periodClearanceFloor_le_boundary (index : Fin 3) :
    periodClearanceFloor <= (baseBranchClearance index).bound := by
  rcases finThree_cases index with h | h | h <;> subst index <;> decide

private theorem periodClearanceFloor_le_left (index : Fin 3) :
    periodClearanceFloor <= (rawAmbientLeftClearance index).bound := by
  rcases finThree_cases index with h | h | h <;> subst index <;> decide

private theorem periodClearanceFloor_le_right (index : Fin 3) :
    periodClearanceFloor <= (rawAmbientRightClearance index).bound := by
  rcases finThree_cases index with h | h | h <;> subst index <;> decide

private theorem periodClearanceFloor_le_bottom (index : Fin 3) :
    periodClearanceFloor <= (rawAmbientBottomClearance index).bound := by
  rcases finThree_cases index with h | h | h <;> subst index <;> decide

private theorem periodClearanceFloor_le_top (index : Fin 3) :
    periodClearanceFloor <= (rawAmbientTopClearance index).bound := by
  rcases finThree_cases index with h | h | h <;> subst index <;> decide

/-- A large explicit period box upgraded directly to the stronger state
needed for total shrinking refinement. -/
def baseBranchStateAt (index : Fin 3) :
    RFAP.ShrinkingTrack.WindingOneState baseCurve.polynomial
      (RFAP.GlobalWinding.largeSquareBox baseCurve.polynomial) where
  box := baseBranchBox index
  refinesAmbient := by
    unfold RFAP.Boxes.Box.Refines RFAP.GlobalWinding.largeSquareBox
      RFAP.Boxes.Box.symmetric
    rcases finThree_cases index with indexZero | indexOne | indexTwo <;>
      subst index <;> decide
  proper := baseBranchBox_proper index
  clearance := boundaryClearanceWithFloor (fun value boundary =>
    (periodClearanceFloor_le_boundary index).trans
      ((baseBranchClearance index).lower value boundary))
  rawWindingFour := baseBranchWinding index
  ambientLeftClearance := verticalClearanceWithFloor (fun y bottom top =>
    (periodClearanceFloor_le_left index).trans
      ((rawAmbientLeftClearance index).lower y bottom top))
  ambientRightClearance := verticalClearanceWithFloor (fun y bottom top =>
    (periodClearanceFloor_le_right index).trans
      ((rawAmbientRightClearance index).lower y bottom top))
  ambientBottomClearance := horizontalClearanceWithFloor (fun x left right =>
    (periodClearanceFloor_le_bottom index).trans
      ((rawAmbientBottomClearance index).lower x left right))
  ambientTopClearance := horizontalClearanceWithFloor (fun x left right =>
    (periodClearanceFloor_le_top index).trans
      ((rawAmbientTopClearance index).lower x left right))

/-- Reindex the three displayed states by the curve's computed degree. -/
def baseBranchState
    (index : Fin baseCurve.polynomial.natDegree) :
    RFAP.ShrinkingTrack.WindingOneState baseCurve.polynomial
      (RFAP.GlobalWinding.largeSquareBox baseCurve.polynomial) :=
  baseBranchStateAt (Fin.cast baseCurve_degree index)

theorem baseBranchBox_pairwise
    (left right : Fin 3) (different : left ≠ right) :
    (baseBranchBox left).Separated (baseBranchBox right) := by
  rcases finThree_cases left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases finThree_cases right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim | decide

theorem baseBranchState_pairwise
    (left right : Fin baseCurve.polynomial.natDegree)
    (different : left ≠ right) :
    (baseBranchState left).box.Separated
      (baseBranchState right).box := by
  have castDifferent : Fin.cast baseCurve_degree left ≠
      Fin.cast baseCurve_degree right := by
    intro equal
    apply different
    apply Fin.ext
    exact congrArg Fin.val equal
  exact baseBranchBox_pairwise _ _ castDifferent

theorem baseCurve_degree_gt_one : 1 < baseCurve.polynomial.natDegree := by
  rw [baseCurve_degree]
  decide

/-- Explicit degree-complete branch data for the common loop base. -/
def baseBranchData (_ : Unit) :
    CCL.Riemann.BranchIsolation.Data baseCurve :=
  CCL.Riemann.BranchIsolation.Data.ofStates baseCurve
    baseCurve_degree_gt_one baseBranchState baseBranchState_pairwise

/-- Canonical finite standard-period programs generated from the explicit
branch tracks rather than the generic global isolator. -/
def basePeriodData (_ : Unit) : PeriodData baseCurve :=
  CCL.Riemann.PreparedRefinementPrograms.standardPeriodDataOfData
    baseCurve (baseBranchData ())

/-- The explicit programs realize the symplectic branch-cut basis generated
from the same three tracks. -/
theorem basePeriodData_realization :
    CCL.Riemann.PreparedRefinementPrograms.FiniteSymplecticCycleRealization
      baseCurve (basePeriodData ()).cycles
      (CCL.Riemann.BranchCutLifts.symplecticBasisOfData
        baseCurve (baseBranchData ())).cycles :=
  CCL.Riemann.PreparedRefinementPrograms.standardPeriodDataOfData_realization
    baseCurve (baseBranchData ())

end CCL.Riemann.ExplicitLegendreLoopBaseBranches
