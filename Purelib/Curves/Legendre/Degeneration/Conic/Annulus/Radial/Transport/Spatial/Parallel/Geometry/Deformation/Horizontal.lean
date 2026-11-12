module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry.Deformation.Lift
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Continuation
import Purelib.Geometry.Rational.Affine.Segment.Convex
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Coordinates
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Actual horizontal preparations on the SAME ruled short-arc strip

At a fixed original blend, rational arc fractions traverse the original
curved-to-chord deformation. Its physical variation follows from the original
quarter distance and the actual endpoint chord, using squared-distance
contraction under their common blend. Original factor budgets prepare this
horizontal function without changing the vertical preparations or source.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry

namespace Deformation

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation
open Factors (Budgets)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first last : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {targetReading : Transport.Reading actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7}

/-- The SAME actual curve has its original finite squared-distance ceiling in the short arc fraction. -/
theorem fraction_curve_distance (left right : Fraction.Rational) :
    Norm.Basic.normSq (coordinate site parameter 2 quarter positive (first + left * (last - first)) -
      coordinate site parameter 2 quarter positive (first + right * (last - first))) ≤
      ((25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (last - first) ^ 2) * (right - left) ^ 2 := by
  have actual := quarter_base_distance_le site parameter 2 quarter positive
    (of_decide_eq_true rfl) (Fraction.Order.Basic.le_refl 2)
    (first + left * (last - first)) (first + right * (last - first))
  change Norm.Basic.normSq (coordinate site parameter 2 quarter positive (first + left * (last - first)) -
      coordinate site parameter 2 quarter positive (first + right * (last - first))) ≤ _ at actual
  exact actual.trans_eq (by ring1)

/-- The SAME original endpoint chord has the identical finite short-fraction squared-distance ceiling. -/
theorem fraction_chord_distance (left right : Fraction.Rational) :
    Norm.Basic.normSq (Tangent.baseChord site parameter 2 quarter positive first (last - first) left -
      Tangent.baseChord site parameter 2 quarter positive first (last - first) right) ≤
      ((25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (last - first) ^ 2) * (right - left) ^ 2 := by
  have endpoints := quarter_base_distance_le site parameter 2 quarter positive
    (of_decide_eq_true rfl) (Fraction.Order.Basic.le_refl 2) last first
  unfold Tangent.baseChord
  rewrite [show first + (last - first) = last by ring1, Affine.normSq_line_sub]
  change Norm.Basic.normSq (coordinate site parameter 2 quarter positive last -
    coordinate site parameter 2 quarter positive first) ≤ _ at endpoints
  have bound := Arithmetic.mul_le_mul_of_nonneg_right_direct endpoints
    (Arithmetic.sq_nonneg_direct (left - right))
  exact bound.trans_eq (by ring1)

/-- Every unit blend of the SAME ruled strip has the original short-fraction variation ceiling. -/
theorem horizontal_distance (geometry : Geometry source targetReading anchor.regular payment)
    {blend : Fraction.Rational} (inside : FixedRootBoxPath.Inside blend) (left right : Fraction.Rational) :
    Norm.Basic.normSq (geometry.deformation left blend - geometry.deformation right blend) ≤
      ((25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (last - first) ^ 2) * (right - left) ^ 2 := by
  have convex := Affine.Segment.normSq_line_difference_le
    (coordinate site parameter 2 quarter positive (first + left * (last - first)))
    (Tangent.baseChord site parameter 2 quarter positive first (last - first) left)
    (coordinate site parameter 2 quarter positive (first + right * (last - first)))
    (Tangent.baseChord site parameter 2 quarter positive first (last - first) right) inside
  have curves := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (fraction_curve_distance (site := site) (parameter := parameter) (quarter := quarter)
      (positive := positive) (first := first) (last := last) left right)
    (Arithmetic.sub_nonneg_direct inside.2)
  have chords := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (fraction_chord_distance (site := site) (parameter := parameter) (quarter := quarter)
      (positive := positive) (first := first) (last := last) left right) inside.1
  exact convex.trans ((Arithmetic.add_le_add_direct curves chords).trans_eq (by ring1))

/-- The physical horizontal variation scale retains the original half-gap and exact original chart width. -/
@[expose] def horizontalScale (site : Fin 2) (parameter : Canonical)
    (first last : Fraction.Rational) : Fraction.Rational :=
  (25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (last - first) ^ 2

/-- The original physical horizontal scale is nonnegative. -/
theorem horizontalScale_nonnegative (site : Fin 2) (parameter : Canonical) (first last : Fraction.Rational) :
    0 ≤ horizontalScale site parameter first last :=
  Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 25 / 4) (Norm.Basic.normSq_nonneg _))
    (Arithmetic.sq_nonneg_direct _)

/-- Original horizontal factor paths and actual finite preparations at the SAME retained unit blend. -/
@[expose] def Horizontal (budgets : Budgets anchor)
    (geometry : Geometry source targetReading anchor.regular payment) (ordered : first ≤ last)
    (blend : Fraction.Rational) (inside : FixedRootBoxPath.Inside blend) :=
  Factors.Continuation budgets (fun fraction => geometry.deformation fraction blend)
    (fun _ fractionInside => geometry.deformation_inside ordered fractionInside inside)
    (horizontalScale site parameter first last) (horizontalScale_nonnegative site parameter first last)
    (fun left right _ _ => horizontal_distance (anchor := anchor) geometry inside left right)

namespace Horizontal

/-- Prepare both original factors once along the SAME actual horizontal strip function and retained source budgets. -/
def build (budgets : Budgets anchor) (geometry : Geometry source targetReading anchor.regular payment)
    (ordered : first ≤ last) (blend : Fraction.Rational) (inside : FixedRootBoxPath.Inside blend) :
    Horizontal budgets geometry ordered blend inside :=
  Factors.Continuation.build budgets (fun fraction => geometry.deformation fraction blend)
    (fun _ fractionInside => geometry.deformation_inside ordered fractionInside inside)
    (horizontalScale site parameter first last) (horizontalScale_nonnegative site parameter first last)
    (fun left right _ _ => horizontal_distance (anchor := anchor) geometry inside left right)

variable {budgets : Budgets anchor} {geometry : Geometry source targetReading anchor.regular payment}
variable {ordered : first ≤ last} {blend : Fraction.Rational} {inside : FixedRootBoxPath.Inside blend}

/-- The actual horizontal normalized source is the original fixed source coordinate's unchanged quadratic. -/
theorem normal_source (completed : Horizontal budgets geometry ordered blend inside) :
    completed.normal.point 0 = Clearance.normalizedRadicand site parameter
      (coordinate site parameter 2 quarter positive first) :=
  (completed.normal_point 0).trans (congrArg (Clearance.normalizedRadicand site parameter)
    (geometry.deformation_first blend))

/-- The actual horizontal normalized target is the original fixed target coordinate's unchanged quadratic. -/
theorem normal_target (completed : Horizontal budgets geometry ordered blend inside) :
    completed.normal.point 1 = Clearance.normalizedRadicand site parameter
      (coordinate site parameter 2 quarter positive last) :=
  (completed.normal_point 1).trans (congrArg (Clearance.normalizedRadicand site parameter)
    (geometry.deformation_last blend))

/-- The actual horizontal cofactor source is the original fixed source coordinate's unchanged remaining factor. -/
theorem unit_source (completed : Horizontal budgets geometry ordered blend inside) :
    completed.unit.point 0 = (unitPolynomial site).eval (coordinate site parameter 2 quarter positive first) :=
  (completed.unit_point 0).trans (congrArg (fun point : Canonical => (unitPolynomial site).eval point)
    (geometry.deformation_first blend))

/-- The actual horizontal cofactor target is the original fixed target coordinate's unchanged remaining factor. -/
theorem unit_target (completed : Horizontal budgets geometry ordered blend inside) :
    completed.unit.point 1 = (unitPolynomial site).eval (coordinate site parameter 2 quarter positive last) :=
  (completed.unit_point 1).trans (congrArg (fun point : Canonical => (unitPolynomial site).eval point)
    (geometry.deformation_last blend))

end Horizontal
end Deformation

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry
