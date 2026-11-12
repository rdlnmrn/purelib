module
public import Purelib.Integration.Polynomial.Gaussian.Partition.Cells
public import Purelib.Integration.Polynomial.Gaussian.Partition.Continuous
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Comparison
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Coordinates

/-!
# Source bounds for original compiled polynomial paths

Each original segment supplies its persistent rational source process.
Their existing bound-process addition retains source order and constructs
the path enclosure. Every state contains the real coordinate of the actual
compiled path sample.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous

open Purelib.Approximation
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Integration.Polynomial.Gaussian

/-- Build ordered path bounds from one finite rational projection of each original segment. -/
@[expose] def boundProcessOf (projection : Segment.Basic.PolynomialSegment →
    Dense.Rational.Basic.CoordinatePolynomial) : Source.PolynomialPath → BoundProcess
  | [] => BoundProcess.exact 0
  | source :: remaining =>
      (Rational.Continuous.boundProcess (projection source)).add (boundProcessOf projection remaining)

/-- Construct the original ordered path's persistent real-coordinate integration bounds. -/
@[expose] def boundProcess : Source.PolynomialPath → BoundProcess :=
  boundProcessOf Partition.Continuous.projected

/-- Construct the original ordered path's persistent imaginary-coordinate integration bounds. -/
@[expose] def imaginaryBoundProcess : Source.PolynomialPath → BoundProcess :=
  boundProcessOf Partition.Continuous.projectedIm

/-- An additive coordinate with admitted original segment samples is admitted by the ordered path bounds. -/
theorem sample_contains_of_projection
    (projection : Segment.Basic.PolynomialSegment → Dense.Rational.Basic.CoordinatePolynomial)
    (coordinate : Basic.Canonical → Fraction.Rational) (zero : coordinate 0 = 0)
    (add : ∀ first second, coordinate (first + second) = coordinate first + coordinate second)
    (segmentInside : ∀ {source : Segment.Basic.PolynomialSegment} (compiled : Segment.CompiledSegment source)
      (state : (Rational.Continuous.boundProcess (projection source)).State),
      ((Rational.Continuous.boundProcess (projection source)).bound state).Contains (coordinate compiled.sample)) :
    ∀ {source : Source.PolynomialPath} (compiled : CompiledCells source)
      (state : (boundProcessOf projection source).State),
      ((boundProcessOf projection source).bound state).Contains (coordinate compiled.sample)
  | [], .nil, state => by
      cases state
      apply (Interval.exact_contains_iff _ _).mpr
      exact zero
  | _ :: _, .cons head tail, state => by
      have first := segmentInside head state.1
      have remaining := sample_contains_of_projection projection coordinate zero add segmentInside tail state.2
      have sum := Interval.add_contains first remaining
      change (((Rational.Continuous.boundProcess (projection _)).bound state.1).add
        ((boundProcessOf projection _).bound state.2)).Contains (coordinate (head.sample + tail.sample))
      rw [add]
      exact sum

/-- Every saved path state contains the actual original compiled path sample's real coordinate. -/
theorem sample_contains {source : Source.PolynomialPath} (compiled : CompiledCells source)
    (state : (boundProcess source).State) : ((boundProcess source).bound state).Contains compiled.sample.re :=
  sample_contains_of_projection Partition.Continuous.projected Basic.Canonical.re Basic.zero_re Basic.add_re
    (fun compiled state => Partition.Continuous.compiled_state_contains compiled state) compiled state

/-- Every saved imaginary path state contains the same original compiled sample's imaginary coordinate. -/
theorem imaginary_sample_contains {source : Source.PolynomialPath} (compiled : CompiledCells source)
    (state : (imaginaryBoundProcess source).State) :
    ((imaginaryBoundProcess source).bound state).Contains compiled.sample.im :=
  sample_contains_of_projection Partition.Continuous.projectedIm Basic.Canonical.im Basic.zero_im Basic.add_im
    (fun compiled state => Partition.Continuous.compiled_im_state_contains compiled state) compiled state

/-- Independent saved path bounds compare through the original compiled samples and both actual widths. -/
theorem midpoints_difference_le {source : Source.PolynomialPath} (left right : CompiledCells source)
    (leftState rightState : (boundProcess source).State) :
    Purelib.Data.Rat.Fraction.abs (((boundProcess source).bound leftState).midpoint -
      ((boundProcess source).bound rightState).midpoint) ≤
      ((boundProcess source).bound leftState).width + ((boundProcess source).bound rightState).width := by
  have leftInside := sample_contains left leftState
  have rightInside := sample_contains right rightState
  have same : left.sample.re = right.sample.re := congrArg Basic.Canonical.re
    (left.sample_source.trans right.sample_source.symm)
  rw [← same] at rightInside
  have overlap := Interval.overlaps_of_common leftInside rightInside
  exact Interval.abs_sub_le_of_overlaps
    ((boundProcess source).bound leftState).midpoint_contains
    ((boundProcess source).bound rightState).midpoint_contains overlap

/-- Independent saved imaginary bounds compare through the original compiled samples and actual widths. -/
theorem imaginary_midpoints_difference_le {source : Source.PolynomialPath} (left right : CompiledCells source)
    (leftState rightState : (imaginaryBoundProcess source).State) :
    Fraction.abs (((imaginaryBoundProcess source).bound leftState).midpoint -
      ((imaginaryBoundProcess source).bound rightState).midpoint) ≤
      ((imaginaryBoundProcess source).bound leftState).width +
        ((imaginaryBoundProcess source).bound rightState).width := by
  have leftInside := imaginary_sample_contains left leftState
  have rightInside := imaginary_sample_contains right rightState
  have same : left.sample.im = right.sample.im := congrArg Basic.Canonical.im
    (left.sample_source.trans right.sample_source.symm)
  rw [← same] at rightInside
  have overlap := Interval.overlaps_of_common leftInside rightInside
  exact Interval.abs_sub_le_of_overlaps
    ((imaginaryBoundProcess source).bound leftState).midpoint_contains
    ((imaginaryBoundProcess source).bound rightState).midpoint_contains overlap

/-- Pair the actual real and imaginary midpoint readings of one original path. -/
@[expose] def midpoint (source : Source.PolynomialPath) (realState : (boundProcess source).State)
    (imaginaryState : (imaginaryBoundProcess source).State) : Basic.Canonical :=
  ⟨((boundProcess source).bound realState).midpoint, ((imaginaryBoundProcess source).bound imaginaryState).midpoint⟩

/-- Both original coordinate bounds contain the coordinates of the same compiled Gaussian path sample. -/
theorem sample_coordinates_contained {source : Source.PolynomialPath} (compiled : CompiledCells source)
    (realState : (boundProcess source).State) (imaginaryState : (imaginaryBoundProcess source).State) :
    ((boundProcess source).bound realState).Contains compiled.sample.re ∧
      ((imaginaryBoundProcess source).bound imaginaryState).Contains compiled.sample.im :=
  ⟨sample_contains compiled realState, imaginary_sample_contains compiled imaginaryState⟩

/-- The original Gaussian sample differs from the paired midpoint by the two actual half-width budgets. -/
theorem sample_midpoint_normSq_le {source : Source.PolynomialPath} (compiled : CompiledCells source)
    (realState : (boundProcess source).State) (imaginaryState : (imaginaryBoundProcess source).State) :
    Norm.Basic.normSq (compiled.sample - midpoint source realState imaginaryState) ≤
      (((boundProcess source).bound realState).width * (1 / 2)) ^ 2 +
      (((imaginaryBoundProcess source).bound imaginaryState).width * (1 / 2)) ^ 2 := by
  exact Norm.Coordinates.sub_normSq_le compiled.sample (midpoint source realState imaginaryState) _ _
    (Interval.abs_sub_midpoint_le (sample_contains compiled realState))
    (Interval.abs_sub_midpoint_le (imaginary_sample_contains compiled imaginaryState))

/-- Independent paired midpoint readings satisfy a squared-norm bound from both actual coordinate widths.

Each pair uses its own original real and imaginary saved states. Both
coordinates are compared through the same retained compiled path samples;
no independent Gaussian value is selected. -/
theorem midpoints_normSq_le {source : Source.PolynomialPath} (left right : CompiledCells source)
    (leftReal rightReal : (boundProcess source).State)
    (leftImaginary rightImaginary : (imaginaryBoundProcess source).State) :
    Norm.Basic.normSq (midpoint source leftReal leftImaginary - midpoint source rightReal rightImaginary) ≤
      (((boundProcess source).bound leftReal).width + ((boundProcess source).bound rightReal).width) ^ 2 +
      (((imaginaryBoundProcess source).bound leftImaginary).width +
        ((imaginaryBoundProcess source).bound rightImaginary).width) ^ 2 := by
  exact Norm.Coordinates.sub_normSq_le (midpoint source leftReal leftImaginary)
    (midpoint source rightReal rightImaginary) _ _
    (midpoints_difference_le left right leftReal rightReal)
    (imaginary_midpoints_difference_le left right leftImaginary rightImaginary)

end Purelib.Integration.Polynomial.Gaussian.Partition.Cells.Continuous

end
