module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.IncrementArea

@[expose] public section

/-!
# Exact closing edges for cached increment polygons

Appending the negative total closes the actual increment list and preserves
its signed area. In particular this operation does not discard excursions
or infer zero area from zero total.
-/

namespace Purelib.Integration.Path.IncrementAreaClosure

open Purelib.Integration.Path.IncrementArea

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- A Gaussian displacement and its negative have zero signed cross area. -/
private theorem closing_cross (value : IncrementArea.Gaussian) : BoundaryRibbon.area value (-value) = 0 := by
  have equal := BoundaryRibbon.area_sub_self_right value 0
  simpa only [Basic.zero_sub, IncrementArea.area_zero_right] using equal

namespace Summary

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- Close the original increment path by appending the negative of its retained total.

The returned summary has total zero and reuses the original cached area with its exact closing equality. -/
def close {increments : List IncrementArea.Gaussian} (summary : IncrementArea.Summary increments) :
  IncrementArea.Summary (increments ++ [-summary.total]) where
  total := 0
  total_eq := by rw [IncrementArea.sum_append, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
    Data.Gaussian.Norm.Sum.Basic.gaussianSum,
    Basic.add_zero, ← summary.total_eq, add_neg_cancel]
  area := summary.area
  area_eq := by
    rw [IncrementArea.pathArea_append, IncrementArea.pathArea_cons]
    simp only [Data.Gaussian.Norm.Sum.Basic.gaussianSum, IncrementArea.area_zero_right, Basic.add_zero, show
      IncrementArea.pathArea ([] : List IncrementArea.Gaussian) = 0 from rfl]
    rw [← summary.total_eq, IncrementAreaClosure.closing_cross, Basic.add_zero]
    exact summary.area_eq

open Purelib.Integration.Path
/-- The closed retained increment summary has total zero. -/
theorem close_total {increments : List IncrementArea.Gaussian} (summary : IncrementArea.Summary increments) :
  (IncrementAreaClosure.Summary.close summary).total = 0 := rfl

/-- Closing the original increment summary preserves its cached area. -/
theorem close_area {increments : List IncrementArea.Gaussian} (summary : IncrementArea.Summary increments) :
  (IncrementAreaClosure.Summary.close summary).area = summary.area := rfl

end Summary
end Purelib.Integration.Path.IncrementAreaClosure
