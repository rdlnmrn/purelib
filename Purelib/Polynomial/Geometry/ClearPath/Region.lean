module

public import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Data.Gaussian.Norm.Basic

/-! # Reclear an identical oriented axis segment from whole-box clearance

The retained segment supplies its exact physical endpoints and axis.
Quantitative region clearance on another original box supplies its new
complete coordinate-line certificate. No point, orientation or affine
parameterization is changed by this polynomial/ambient operation.
-/

public section

namespace Purelib.Polynomial.Geometry.ClearPath.ClearSegment

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Components
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)

variable {first last : GaussianPolynomial} {ambient box : Geometry.Rational.Box}
    {start finish : Canonical}

/-- Reclear the same oriented physical axis segment using an actual whole-box certificate and retained endpoint bounds.

The segment's original constructor determines horizontal or vertical
orientation. Its endpoints are retained literally, while the new region
bound pays the entire corresponding coordinate line inside the new box.
-/
def reclear (segment : ClearSegment first ambient start finish)
    (clearance : RegionClearance last box) (firstInside : box.Contains start) (lastInside : box.Contains finish) :
    ClearSegment last box start finish := by
  cases segment with
  | horizontal xStart xFinish y _ _ _ _ _ =>
      exact .horizontal xStart xFinish y firstInside.1 firstInside.2.1 lastInside.1 lastInside.2.1
        { bound := clearance.bound
          positive := clearance.positive
          lower := fun value lower upper => by
            have bound := clearance.lower (Data.Gaussian.Basic.point value y)
              ⟨lower, upper, firstInside.2.2.1, firstInside.2.2.2⟩
            rewrite [Norm.Basic.normSq_eq_canonical] at bound
            exact bound }
  | vertical x yStart yFinish _ _ _ _ _ =>
      exact .vertical x yStart yFinish firstInside.2.2.1 firstInside.2.2.2 lastInside.2.2.1 lastInside.2.2.2
        { bound := clearance.bound
          positive := clearance.positive
          lower := fun value lower upper => by
            have bound := clearance.lower (Data.Gaussian.Basic.point x value)
              ⟨firstInside.1, firstInside.2.1, lower, upper⟩
            rewrite [Norm.Basic.normSq_eq_canonical] at bound
            exact bound }

/-- Reclearance keeps the exact affine physical point at every retained rational parameter. -/
theorem reclear_pointAt (segment : ClearSegment first ambient start finish)
    (clearance : RegionClearance last box) (firstInside : box.Contains start) (lastInside : box.Contains finish)
    (parameter : Data.Rat.Fraction.Rational) :
    (segment.reclear clearance firstInside lastInside).pointAt parameter = segment.pointAt parameter := by
  rfl

/-- The re-cleared segment lies in the new certified physical box, including its fixed coordinate. -/
theorem reclear_withinAmbient (segment : ClearSegment first ambient start finish)
    (clearance : RegionClearance last box) (firstInside : box.Contains start) (lastInside : box.Contains finish) :
    (segment.reclear clearance firstInside lastInside).WithinAmbient := by
  cases segment with
  | horizontal => exact ⟨firstInside.2.2.1, firstInside.2.2.2⟩
  | vertical => exact ⟨firstInside.1, firstInside.2.1⟩

/-- The new complete line clearance retains exactly the supplied region bound. -/
theorem reclear_clearanceBound (segment : ClearSegment first ambient start finish)
    (clearance : RegionClearance last box) (firstInside : box.Contains start) (lastInside : box.Contains finish) :
    (segment.reclear clearance firstInside lastInside).clearanceBound = clearance.bound := by
  cases segment <;> rfl

end Purelib.Polynomial.Geometry.ClearPath.ClearSegment

end
