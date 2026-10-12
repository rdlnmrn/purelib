module
import Purelib.Data.Fin
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Fin.Cases
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Legendre.FactorGeometry
import Purelib.Curves.Legendre.Paths
public import Purelib.Curves.Legendre.Squarefree
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Translated
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Winding.Box.Affine
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Riemann.Integration.PreparedRefinementPrograms
import Purelib.RootIsolation.State.WindingOne.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Nat.Coprime.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Tactic.Ring

section
public section

/-!
# Explicit finite branch tracks at the Legendre loop base

The rational root boxes already used by the concrete Legendre crossing are
upgraded here to degree-complete shrinking branch tracks.  Factorwise vertical
and horizontal line clearances supply the four pieces of ambient evidence
required by `WindingOneState`, so the finite period layer can consume these
tracks directly without replaying the generic global isolator or Newton
extraction.
-/

namespace Purelib.Examples.Curves.Legendre.LoopBaseBranches

open Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius
open Purelib.Polynomial.Winding
open Purelib.Data.Gaussian
open Purelib.Data.Fin
open Purelib.Polynomial.Clearance.Box.Line.Basic (VerticalLineClearance)
open Purelib.Polynomial.Clearance.Box.Line.Basic (HorizontalLineClearance)

open Purelib

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib.Examples

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

/-- The common rational loop base, kept independent of the heavyweight
worked crossing-segment example. -/
@[expose] def baseParameter : Gaussian :=
  Legendre.Paths.gaussian (1 / 4) 2

/-- The exact Legendre curve at the common rational loop base. -/
@[expose] def baseCurve :
  Hyperelliptic.Basic.HyperellipticCurve 1 where
  polynomial := Legendre.Paths.polynomial baseParameter
  nonzero := Legendre.Paths.polynomial_isZero baseParameter
  squarefree := Legendre.Squarefree.certificate baseParameter
    (by decide)
  degreeShape := .odd (Legendre.Paths.polynomial_natDegree baseParameter)

/-- The retained loop-base curve reads back the Legendre polynomial at 1/4+2i. -/
@[simp] theorem baseCurve_polynomial :
    baseCurve.polynomial =
      Legendre.Paths.polynomial baseParameter := rfl

/-- The loop-base curve polynomial has degree three. -/
theorem baseCurve_degree :
  baseCurve.polynomial.natDegree = 3 := by
  exact Legendre.Paths.polynomial_natDegree baseParameter

/-- The three exact linear factors at the loop-base parameter. -/
@[expose] def baseFactors :=
  Legendre.FactorGeometry.factors baseParameter

/-- Certify the factored cubic along a vertical line avoiding the three root real coordinates. -/
@[expose] def baseFactorsVerticalClearance (x :
  Fraction.Rational)
    (apartZero : x ≠ 0)
    (apartMoving : x ≠ baseParameter.re)
    (apartOne : x ≠ 1) :
    VerticalLineClearance baseFactors
      (Box.largeSquareBox baseCurve.polynomial) x :=
  VerticalLineClearance.mul
    (VerticalLineClearance.mul
      (Clearance.Box.Line.Translated.translatedCoordinate_verticalLineClearance
        0 _ x apartZero)
      (Clearance.Box.Line.Translated.translatedCoordinate_verticalLineClearance
        baseParameter _ x apartMoving))
    (Clearance.Box.Line.Translated.translatedCoordinate_verticalLineClearance
      1 _ x apartOne)

/-- Transport the factorwise vertical clearance to the exact loop-base polynomial. -/
@[expose] def basePolynomialVerticalClearance (x :
  Fraction.Rational)
    (apartZero : x ≠ 0)
    (apartMoving : x ≠ baseParameter.re)
    (apartOne : x ≠ 1) :
    VerticalLineClearance baseCurve.polynomial
      (Box.largeSquareBox baseCurve.polynomial) x :=
        by
  rw [baseCurve_polynomial,
    Legendre.FactorGeometry.polynomial_eq_factors]
  exact baseFactorsVerticalClearance x apartZero apartMoving apartOne

/-- Certify the factored cubic along a horizontal line avoiding the root imaginary coordinates zero and two. -/
@[expose] def baseFactorsHorizontalClearance (y :
  Fraction.Rational)
    (apartZero : y ≠ 0)
    (apartMoving : y ≠ baseParameter.im) :
    HorizontalLineClearance baseFactors
      (Box.largeSquareBox baseCurve.polynomial) y :=
  HorizontalLineClearance.mul
    (HorizontalLineClearance.mul
      (Clearance.Box.Line.Translated.translatedCoordinate_horizontalLineClearance
        0 _ y apartZero)
      (Clearance.Box.Line.Translated.translatedCoordinate_horizontalLineClearance
        baseParameter _ y apartMoving))
    (Clearance.Box.Line.Translated.translatedCoordinate_horizontalLineClearance
      1 _ y apartZero)

/-- Transport the factorwise horizontal clearance to the exact loop-base polynomial. -/
@[expose] def basePolynomialHorizontalClearance (y :
  Fraction.Rational)
    (apartZero : y ≠ 0)
    (apartMoving : y ≠ baseParameter.im) :
    HorizontalLineClearance baseCurve.polynomial
      (Box.largeSquareBox baseCurve.polynomial) y :=
        by
  rw [baseCurve_polynomial,
    Legendre.FactorGeometry.polynomial_eq_factors]
  exact baseFactorsHorizontalClearance y apartZero apartMoving

/-- The three pairwise-separated rational boxes at the retained loop base.

Each finite coordinate selects its original box with the exact rational endpoints
and strict width certificates. The two stationary roots and moving root retain
their displayed order. -/
@[expose] def baseBranchBox (index : Fin 3) :
  Rational.Box :=
  Data.Fin.casesDependent (motive := fun _ => Rational.Box)
    ({ xLower := -(1 / 2)
       xUpper := 1 / 16
       yLower := -(1 / 2)
       yUpper := 1 / 2
       x_valid := by decide
       y_valid := by decide })
    (fun previous => Data.Fin.casesDependent (motive := fun _ => Rational.Box)
      ({ xLower := 1 / 8
         xUpper := 3 / 8
         yLower := 3 / 2
         yUpper := 5 / 2
         x_valid := by decide
         y_valid := by decide })
      (fun last => Data.Fin.casesDependent (motive := fun _ => Rational.Box)
        ({ xLower := 15 / 16
           xUpper := 3 / 2
           yLower := -(1 / 2)
           yUpper := 1 / 2
           x_valid := by decide
           y_valid := by decide })
        (fun empty => (Nat.not_lt_zero _ empty.isLt).elim) last) previous) index

/-- Every displayed loop-base branch box has positive coordinate widths. -/
theorem baseBranchBox_proper (index : Fin 3) :
    (baseBranchBox index).Proper := by
  rcases Cases.three index with h | h | h <;> subst index <;>
    constructor <;> decide

/-- The factored loop-base cubic has certified nonzero values on each branch-box boundary.

Each finite coordinate retains the original factorwise clearance, using the
centered, above, left or right separation certificate for that same displayed box. -/
@[expose] def baseBranchFactorsClearance (index : Fin 3) :
    BoundaryClearance baseFactors
      (baseBranchBox index) :=
  Data.Fin.casesDependent (motive := fun index : Fin 3 => BoundaryClearance
    baseFactors (baseBranchBox index))
    (Legendre.FactorGeometry.factorsClearance
       (Legendre.FactorGeometry.centeredClearance 0
         (by decide +revert) (by decide +revert)
         (by decide +revert) (by decide +revert))
       (Legendre.FactorGeometry.aboveClearance
         baseParameter
           (by decide +revert))
       (Legendre.FactorGeometry.rightClearance 1
         (by decide +revert)))
    (fun previous => Data.Fin.casesDependent (motive := fun index : Fin 2 =>
      BoundaryClearance baseFactors
      (baseBranchBox index.succ))
      (Legendre.FactorGeometry.factorsClearance
         (Legendre.FactorGeometry.leftClearance 0
           (by decide +revert))
         (Legendre.FactorGeometry.centeredClearance
           baseParameter
           (by decide +revert) (by decide +revert)
           (by decide +revert) (by decide +revert))
         (Legendre.FactorGeometry.rightClearance 1
           (by decide +revert)))
      (fun last => Data.Fin.casesDependent (motive := fun index : Fin 1 =>
        BoundaryClearance baseFactors
        (baseBranchBox index.succ.succ))
        (Legendre.FactorGeometry.factorsClearance
           (Legendre.FactorGeometry.leftClearance 0
             (by decide +revert))
           (Legendre.FactorGeometry.aboveClearance
             baseParameter
               (by decide +revert))
           (Legendre.FactorGeometry.centeredClearance 1
             (by decide +revert) (by decide +revert)
             (by decide +revert) (by decide +revert)))
        (fun empty => (Nat.not_lt_zero _ empty.isLt).elim) last) previous) index

/-- Transport each displayed branch-box clearance to the exact loop-base polynomial. -/
@[expose] def baseBranchClearance (index : Fin 3) :
    BoundaryClearance baseCurve.polynomial
      (baseBranchBox index) := by
  rw [baseCurve_polynomial,
    Legendre.FactorGeometry.polynomial_eq_factors]
  exact baseBranchFactorsClearance index

/-- Every displayed branch box has quadrupled polynomial winding four. -/
theorem baseBranchWinding (index : Fin 3) :
    Box.Basic.quadrupledBoxWinding baseCurve.polynomial
      (baseBranchBox index) = 4 := by
  rcases Cases.three index with h | h | h
  · subst index
    rw [baseCurve_polynomial,
      Legendre.FactorGeometry.polynomial_eq_factors]
    apply Legendre.FactorGeometry.factors_winding_of_sum
      (baseBranchBox_proper 0)
      (Legendre.FactorGeometry.centeredClearance 0
        (by decide) (by decide) (by decide) (by decide))
      (Legendre.FactorGeometry.aboveClearance
        baseParameter (by decide))
      (Legendre.FactorGeometry.rightClearance 1 (by decide))
    have zeroWinding : Box.Basic.quadrupledBoxWinding
        (Legendre.FactorGeometry.factor 0) (baseBranchBox 0) = 4 :=
      Box.Affine.quadrupledBoxWinding_translatedCoordinate 0
        (by decide) (by decide) (by decide) (by decide)
    have movingWinding : Box.Basic.quadrupledBoxWinding
        (Legendre.FactorGeometry.factor baseParameter)
          (baseBranchBox 0) = 0 := by decide
    have oneWinding : Box.Basic.quadrupledBoxWinding
        (Legendre.FactorGeometry.factor 1) (baseBranchBox 0) = 0 :=
      by decide
    rw [zeroWinding, movingWinding, oneWinding]
    ring1
  · subst index
    rw [baseCurve_polynomial,
      Legendre.FactorGeometry.polynomial_eq_factors]
    apply Legendre.FactorGeometry.factors_winding_of_sum
      (baseBranchBox_proper 1)
      (Legendre.FactorGeometry.leftClearance 0 (by decide))
      (Legendre.FactorGeometry.centeredClearance
        baseParameter
        (by decide) (by decide) (by decide) (by decide))
      (Legendre.FactorGeometry.rightClearance 1 (by decide))
    have zeroWinding : Box.Basic.quadrupledBoxWinding
        (Legendre.FactorGeometry.factor 0) (baseBranchBox 1) = 0 :=
      Legendre.FactorGeometry.factor_winding_zero_of_left 0
        (baseBranchBox_proper 1)
        (Legendre.FactorGeometry.leftClearance 0 (by decide))
        (by decide)
    have movingWinding : Box.Basic.quadrupledBoxWinding
        (Legendre.FactorGeometry.factor baseParameter)
          (baseBranchBox 1) = 4 :=
      Box.Affine.quadrupledBoxWinding_translatedCoordinate
        baseParameter
          (by decide) (by decide) (by decide) (by decide)
    have oneWinding : Box.Basic.quadrupledBoxWinding
        (Legendre.FactorGeometry.factor 1) (baseBranchBox 1) = 0 :=
      Legendre.FactorGeometry.factor_winding_zero_of_right 1
        (baseBranchBox_proper 1)
        (Legendre.FactorGeometry.rightClearance 1 (by decide))
        (by decide)
    rw [zeroWinding, movingWinding, oneWinding]
    ring1
  · subst index
    rw [baseCurve_polynomial,
      Legendre.FactorGeometry.polynomial_eq_factors]
    apply Legendre.FactorGeometry.factors_winding_of_sum
      (baseBranchBox_proper 2)
      (Legendre.FactorGeometry.leftClearance 0 (by decide))
      (Legendre.FactorGeometry.aboveClearance
        baseParameter (by decide))
      (Legendre.FactorGeometry.centeredClearance 1
        (by decide) (by decide) (by decide) (by decide))
    have zeroWinding : Box.Basic.quadrupledBoxWinding
        (Legendre.FactorGeometry.factor 0) (baseBranchBox 2) = 0 :=
      by decide
    have movingWinding : Box.Basic.quadrupledBoxWinding
        (Legendre.FactorGeometry.factor baseParameter)
          (baseBranchBox 2) = 0 := by decide
    have oneWinding : Box.Basic.quadrupledBoxWinding
        (Legendre.FactorGeometry.factor 1) (baseBranchBox 2) = 4 :=
      Box.Affine.quadrupledBoxWinding_translatedCoordinate 1
        (by decide) (by decide) (by decide) (by decide)
    rw [zeroWinding, movingWinding, oneWinding]
    ring1

/-- One small common rational floor retained in the runtime representation of
the explicit branch states.  The stronger factorwise clearances above prove
this floor, but keeping their normalized products out of the state payload
makes the downstream prepared-path checker substantially cheaper to execute. -/
@[expose] def periodClearanceFloor : Fraction.Rational where
  num := 1
  den := 262144
  den_pos := by decide
  reduced := ⟨⟨1, 0, by decide⟩⟩

/-- The retained rational clearance floor 1/262144 is strictly positive. -/
theorem periodClearanceFloor_positive :
    0 < periodClearanceFloor := by decide

/-- Construct boundary clearance using the fixed positive floor and a supplied pointwise squared-norm bound. -/
@[expose] def boundaryClearanceWithFloor
    {polynomial : CoefficientPolynomial}
    {box : Rational.Box}
    (lower : ∀ value : Gaussian.Basic.Canonical,
      Rational.Box.Boundary.OnBoxBoundary box value →
        periodClearanceFloor <=
          Norm.Basic.normSq
            (polynomial.eval value)) :
    BoundaryClearance polynomial box where
  bound := periodClearanceFloor
  positive := periodClearanceFloor_positive
  lower := by
    intro value boundary
    have scalar := lower value boundary
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar

/-- Construct vertical-line clearance using the fixed positive floor and a supplied bound throughout the ambient height
interval. -/
@[expose] def verticalClearanceWithFloor
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {x : Fraction.Rational}
    (lower : ∀ y : Fraction.Rational, ambient.yLower <= y →
      y <= ambient.yUpper → periodClearanceFloor <=
        Norm.Basic.normSq
          (polynomial.eval (Gaussian.Components.Basic.point x y))) :
    VerticalLineClearance polynomial ambient x where
  bound := periodClearanceFloor
  positive := periodClearanceFloor_positive
  lower := by
    intro y bottom top
    have scalar := lower y bottom top
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar

/-- Construct horizontal-line clearance using the fixed positive floor and a supplied bound throughout the ambient width
interval. -/
@[expose] def horizontalClearanceWithFloor
    {polynomial : CoefficientPolynomial}
    {ambient : Rational.Box} {y : Fraction.Rational}
    (lower : ∀ x : Fraction.Rational, ambient.xLower <= x →
      x <= ambient.xUpper → periodClearanceFloor <=
        Norm.Basic.normSq
          (polynomial.eval (Gaussian.Components.Basic.point x y))) :
    HorizontalLineClearance polynomial ambient y where
  bound := periodClearanceFloor
  positive := periodClearanceFloor_positive
  lower := by
    intro x left right
    have scalar := lower x left right
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar

/-- The factorwise vertical clearance along the left side of the selected branch box within the original ambient square.
-/
@[expose] def rawAmbientLeftClearance (index : Fin 3) :
    VerticalLineClearance baseCurve.polynomial
      (Box.largeSquareBox baseCurve.polynomial)
      (baseBranchBox index).xLower :=
  basePolynomialVerticalClearance _
    (by rcases Cases.three index with h | h | h <;> subst index <;> decide)
    (by rcases Cases.three index with h | h | h <;> subst index <;> decide)
    (by rcases Cases.three index with h | h | h <;> subst index <;> decide)

/-- The factorwise vertical clearance along the right side of the selected branch box within the original ambient
square. -/
@[expose] def rawAmbientRightClearance (index : Fin 3) :
    VerticalLineClearance baseCurve.polynomial
      (Box.largeSquareBox baseCurve.polynomial)
      (baseBranchBox index).xUpper :=
  basePolynomialVerticalClearance _
    (by rcases Cases.three index with h | h | h <;> subst index <;> decide)
    (by rcases Cases.three index with h | h | h <;> subst index <;> decide)
    (by rcases Cases.three index with h | h | h <;> subst index <;> decide)

/-- The factorwise horizontal clearance along the bottom side of the selected branch box within the original ambient
square. -/
@[expose] def rawAmbientBottomClearance (index : Fin 3) :
    HorizontalLineClearance baseCurve.polynomial
      (Box.largeSquareBox baseCurve.polynomial)
      (baseBranchBox index).yLower :=
  basePolynomialHorizontalClearance _
    (by rcases Cases.three index with h | h | h <;> subst index <;> decide)
    (by rcases Cases.three index with h | h | h <;> subst index <;> decide)

/-- The factorwise horizontal clearance along the top side of the selected branch box within the original ambient
square. -/
@[expose] def rawAmbientTopClearance (index : Fin 3) :
    HorizontalLineClearance baseCurve.polynomial
      (Box.largeSquareBox baseCurve.polynomial)
      (baseBranchBox index).yUpper :=
  basePolynomialHorizontalClearance _
    (by rcases Cases.three index with h | h | h <;> subst index <;> decide)
    (by rcases Cases.three index with h | h | h <;> subst index <;> decide)

/-- The retained rational floor is bounded by every original branch-box boundary clearance. -/
theorem periodClearanceFloor_le_boundary (index : Fin 3) :
    periodClearanceFloor <= (baseBranchClearance
      index).bound := by
  rcases Cases.three index with h | h | h <;> subst index <;> decide

/-- The retained rational floor is bounded by the factorwise clearance on the left ambient line. -/
theorem periodClearanceFloor_le_left (index : Fin 3) :
    periodClearanceFloor <= (rawAmbientLeftClearance
      index).bound := by
  rcases Cases.three index with h | h | h <;> subst index <;> decide

/-- The retained rational floor is bounded by the factorwise clearance on the right ambient line. -/
theorem periodClearanceFloor_le_right (index : Fin 3) :
    periodClearanceFloor <= (rawAmbientRightClearance
      index).bound := by
  rcases Cases.three index with h | h | h <;> subst index <;> decide

/-- The retained rational floor is bounded by the factorwise clearance on the bottom ambient line. -/
theorem periodClearanceFloor_le_bottom (index : Fin 3) :
    periodClearanceFloor <= (rawAmbientBottomClearance
      index).bound := by
  rcases Cases.three index with h | h | h <;> subst index <;> decide

/-- The retained rational floor is bounded by the factorwise clearance on the top ambient line. -/
theorem periodClearanceFloor_le_top (index : Fin 3) :
    periodClearanceFloor <= (rawAmbientTopClearance
      index).bound := by
  rcases Cases.three index with h | h | h <;> subst index <;> decide

/-- A large explicit period box upgraded directly to the stronger state
needed for total shrinking refinement. -/
@[expose] def baseBranchStateAt (index : Fin 3) :
    WindingOneState baseCurve.polynomial
      (Box.largeSquareBox baseCurve.polynomial) where
  box := baseBranchBox index
  refinesAmbient := by
    unfold Rational.Box.Refines Box.largeSquareBox
      Purelib.Geometry.Rational.Box.symmetric
    rcases Purelib.Data.Fin.Cases.three index with indexZero | indexOne | indexTwo <;>
      subst index <;> decide
  proper := baseBranchBox_proper index
  clearance := boundaryClearanceWithFloor (fun value boundary =>
    (periodClearanceFloor_le_boundary index).trans
      (by
        have scalar := ((baseBranchClearance index).lower value boundary)
        rw [← Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar))
  rawWindingFour := baseBranchWinding index
  ambientLeftClearance := verticalClearanceWithFloor (fun y bottom top =>
    (periodClearanceFloor_le_left index).trans
      (by
        have scalar := ((rawAmbientLeftClearance index).lower y bottom top)
        rw [← Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar))
  ambientRightClearance := verticalClearanceWithFloor (fun y bottom top =>
    (periodClearanceFloor_le_right index).trans
      (by
        have scalar := ((rawAmbientRightClearance index).lower y bottom top)
        rw [← Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar))
  ambientBottomClearance := horizontalClearanceWithFloor (fun x left right =>
    (periodClearanceFloor_le_bottom index).trans
      (by
        have scalar := ((rawAmbientBottomClearance index).lower x left right)
        rw [← Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar))
  ambientTopClearance := horizontalClearanceWithFloor (fun x left right =>
    (periodClearanceFloor_le_top index).trans
      (by
        have scalar := ((rawAmbientTopClearance index).lower x left right)
        rw [← Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar))

/-- Reindex the three displayed states by the curve's computed degree. -/
@[expose] def baseBranchState
    (index : Fin baseCurve.polynomial.natDegree) :
    WindingOneState baseCurve.polynomial
      (Box.largeSquareBox baseCurve.polynomial) :=
  baseBranchStateAt (Fin.cast baseCurve_degree index)

/-- Distinct displayed branch indices have separated rational boxes. -/
theorem baseBranchBox_pairwise
    (left right : Fin 3) (different : left ≠ right) :
    (baseBranchBox left).Separated (baseBranchBox
      right) := by
  rcases Cases.three left with leftZero | leftOne | leftTwo <;>
    subst left <;>
    rcases Cases.three right with rightZero | rightOne | rightTwo <;>
    subst right <;>
    first | exact (different rfl).elim | decide

/-- Distinct degree-indexed branch states retain separated displayed boxes. -/
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

/-- The loop-base cubic has degree greater than one. -/
theorem baseCurve_degree_gt_one : 1 <
  baseCurve.polynomial.natDegree := by
  rw [baseCurve_degree]
  decide

/-- Explicit degree-complete branch data for the common loop base. -/
@[expose] def baseBranchData (_ : Unit) :
    Hyperelliptic.Branches.BranchIsolation.Data baseCurve :=
  Hyperelliptic.Branches.BranchIsolation.Data.ofStates baseCurve
    baseCurve_degree_gt_one baseBranchState
      baseBranchState_pairwise

/-- Canonical finite standard-period programs generated from the explicit
branch tracks rather than the generic global isolator. -/
@[expose] def basePeriodData (_ : Unit) :
  Periods.PeriodMatrix.PeriodData baseCurve :=
  Integration.PreparedRefinementPrograms.rawPeriodDataOfData
    baseCurve (baseBranchData ())

/-- The explicit programs realize the symplectic branch-cut basis generated
from the same three tracks. -/
theorem basePeriodData_realization :
    Integration.PreparedRefinementPrograms.SymplecticCycleRealization
      baseCurve (basePeriodData ()).cycles
      (Hyperelliptic.Branches.BranchCutLifts.symplecticBasisOfData
        baseCurve (baseBranchData ())).cycles :=
  Integration.PreparedRefinementPrograms.rawPeriodDataOfData_realization
    baseCurve (baseBranchData ())

end Purelib.Examples.Curves.Legendre.LoopBaseBranches

end
