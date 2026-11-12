module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Shifted
import Purelib.Data.Rat.Fraction.Order.Field

/-! # One shifted-polynomial allocation for the retained covered-parent family

The single cached finite range minimum is quartered once as a scalar
allocation. Every original parent occurrence then obtains quantitative
changed-polynomial clearance on its identical retained neighborhood box,
without executing a range factory or source preparation again.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ParameterRange

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count : Nat} {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count parents} (ranges : ParameterRange covered)

/-- Quarter the same cached finite range minimum for shifted clearance throughout all retained physical boxes. -/
@[expose] def shiftedBound : Rational := ranges.bound / 4

/-- The common shifted-polynomial allocation is positive, including for an empty covered-parent family. -/
theorem shiftedBound_positive : 0 < ranges.shiftedBound :=
  Order.Field.div_pos_direct ranges.bound_positive (by decide +kernel)

/-- The tighter common allocation continues to admit every original actual query and endpoint Step. -/
theorem shiftedBound_le_bound : ranges.shiftedBound ≤ ranges.bound :=
  Order.Field.divide_le_self ranges.bound_positive.le (by decide +kernel : (1 : Rational) ≤ 4)

/-- The cached finite minimum pays the shifted-polynomial allocation of each identical retained patch occurrence. -/
theorem shiftedBound_le_entry (index : Fin parents.length) :
    ranges.shiftedBound ≤ (ranges.entry index).shiftedBound :=
  Order.Field.divide_mono (ranges.bound_le_entry index) (by decide +kernel : (0 : Rational) < 4)

/-- Construct shifted-polynomial clearance on the actual original neighborhood at one retained parent occurrence.

Only the stored entry is consumed. Its whole prepared-patch factory
equality remains available separately; no range, source, point, root or
endpoint preparation is rerun by this operation.
-/
def shiftedClearance (index : Fin parents.length) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ ranges.shiftedBound) :
    RegionClearance (Paths.polynomial (parameter + increment))
      ((covered.entry index).val.neighborhood count).box :=
  (ranges.entry index).shiftedClearance increment (admitted.trans (ranges.shiftedBound_le_entry index))

/-- The actual per-occurrence shifted region certificate preserves its original observation site's denominator floor. -/
theorem shiftedClearance_bound (index : Fin parents.length) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ ranges.shiftedBound) :
    (ranges.shiftedClearance index increment admitted).bound =
      (((covered.entry index).val.neighborhood count).base.site.denominatorValue / 4) / 4 := by
  exact (ranges.entry index).shiftedClearance_bound increment (admitted.trans (ranges.shiftedBound_le_entry index))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ParameterRange

end
