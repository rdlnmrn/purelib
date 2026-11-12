module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Overlap
public import Purelib.Polynomial.Geometry.ClearPath.Region
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Quantitative spatial sections in the original signed strip budget

The original oriented segment is re-cleared on the SAME retained physical
box at one admitted interpolation time. Its actual polynomial variation
bound pays a spatial PathData in the original seed budget. This constructs
no root selector, new Frame, source preparation or member.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches

variable {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    (range : Range patch) (budget : FixedRootBoxBudget.Budget patch.base.seed.owner)
    (factory : budget = range.seedBudget)
    {ambient : Box} {start finish : Canonical}
    (segment : ClearSegment (Paths.polynomial parameter) ambient start finish)
    (firstInside : patch.box.Contains start) (lastInside : patch.box.Contains finish)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound)
    (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1)

/-- Construct an actual spatial root-comparison path using the SAME original whole-strip seed budget.

Every spatial fraction stays in the original patch by its retained endpoint
admissions. The changed polynomial's region clearance pays re-clearance of
that identical oriented segment. Its original affine-substitution bound
supplies the finite comparison scale; no signed agreement is an input.
-/
def spatialPath : FixedRootBoxPath.PathData budget budget :=
  let clearance := range.interpolated_clearance time inside increment admitted
  let shifted := segment.reclear clearance firstInside lastInside
  have within := segment.reclear_withinAmbient clearance firstInside lastInside
  let scale := ClearSheetContinuation.variationBound shifted 0 1
  { point := fun fraction =>
      (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval (segment.pointAt fraction)
    nonzero := fun fraction fractionInside =>
      range.strip_nonzero (segment.pointAt_contains_of_endpoints firstInside lastInside fraction fractionInside)
        ((⟨time, 0⟩ : Canonical) * increment) (range.interpolated_admitted time inside increment admitted)
    firstMovement := by
      intro fraction fractionInside
      have paid := range.seed_movement_le
        (segment.pointAt_contains_of_endpoints firstInside lastInside fraction fractionInside)
        ((⟨time, 0⟩ : Canonical) * increment) (range.interpolated_admitted time inside increment admitted)
      rewrite [factory, range.seedBudget_movement]
      rewrite [Norm.Basic.normSq_eq_canonical] at paid
      exact paid
    secondMovement := by
      intro fraction fractionInside
      have paid := range.seed_movement_le
        (segment.pointAt_contains_of_endpoints firstInside lastInside fraction fractionInside)
        ((⟨time, 0⟩ : Canonical) * increment) (range.interpolated_admitted time inside increment admitted)
      rewrite [factory, range.seedBudget_movement]
      rewrite [Norm.Basic.normSq_eq_canonical] at paid
      exact paid
    scale := scale
    scale_nonnegative := ClearSheetContinuation.variationBound_nonneg shifted 0 1
    variation := by
      intro first last firstPaid lastPaid
      have varied := ClearSheetContinuation.evaluation_variation_le shifted within first last firstPaid lastPaid
      have pointEq := congrArg (fun pair : Canonical × Canonical => Norm.Basic.normSq
        ((Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval pair.1 -
          (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval pair.2))
        (congrArg₂ Prod.mk (segment.reclear_pointAt clearance firstInside lastInside first)
          (segment.reclear_pointAt clearance firstInside lastInside last))
      have scalar : ClearSheetContinuation.variationBound shifted first last = scale * (last - first) ^ 2 := by
        unfold scale
        rewrite [ClearSheetContinuation.variationBound_eq_denseLipschitz,
          ClearSheetContinuation.variationBound_eq_denseLipschitz]
        ring1
      rewrite [← Norm.Basic.normSq_eq_canonical]
      exact pointEq.symm.trans_le (varied.trans_eq scalar) }

/-- The retained spatial path reads the exact original affine segment at every rational fraction. -/
theorem spatialPath_point (fraction : Rational) :
    (range.spatialPath budget factory segment firstInside lastInside increment admitted time inside).point fraction =
      (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval (segment.pointAt fraction) := by
  unfold spatialPath
  rfl

/-- Its spatial variation scale is the original computed polynomial bound on the SAME re-cleared segment. -/
theorem spatialPath_scale :
    (range.spatialPath budget factory segment firstInside lastInside increment admitted time inside).scale =
      ClearSheetContinuation.variationBound
        (segment.reclear (range.interpolated_clearance time inside increment admitted) firstInside lastInside) 0 1 := by
  unfold spatialPath
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

end
