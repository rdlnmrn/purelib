module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
public import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.Dyadic.DyadicPairedAreaRefinement
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Full paired-path comparison from increment errors. Every dyadic sample
is paired explicitly, and both count factors cancel the squared widths. -/
namespace Purelib.Integration.Path.DyadicPairedIncrementComparison

open Purelib.Data.Rat in
/-- The rational carrier for paired path comparison parameters and budgets. -/
private abbrev Coordinate := Fraction.Rational

open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Topology.Polygon in
/-- Retain the corresponding original left and right primitive increments in common dyadic subdivision order. -/
@[expose] def incrementPairs (left right : Fraction.Rational → Stokes.PrimitivePoint) : Nat → Fraction.Rational →
  Fraction.Rational → List (Stokes.PrimitivePoint × Stokes.PrimitivePoint)
  | 0, first, last => [(Stokes.PrimitivePoint.sub (left last) (left first), Stokes.PrimitivePoint.sub (right last)
    (right first))]
  | depth + 1, first, last => Purelib.Integration.Path.DyadicPairedIncrementComparison.incrementPairs left right depth
    first (PreparedBoxPartitions.midpoint first last) ++
      Purelib.Integration.Path.DyadicPairedIncrementComparison.incrementPairs left right depth
        (PreparedBoxPartitions.midpoint first last) last

section
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Topology.Polygon
/-- First readback of the retained pairs is the exact original left-path increment list. -/
theorem incrementPairs_left (left right : Fraction.Rational → Stokes.PrimitivePoint) (depth : Nat) (first last :
  Fraction.Rational) :
    (DyadicPairedIncrementComparison.incrementPairs left right depth first last).map Prod.fst =
      DyadicPairedPrimitivePaths.increments left depth first last := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih => rw [DyadicPairedIncrementComparison.incrementPairs, Data.List.Map.map_append, ih, ih]; rfl

/-- Second readback of the retained pairs is the exact original right-path increment list. -/
theorem incrementPairs_right (left right : Fraction.Rational → Stokes.PrimitivePoint) (depth : Nat) (first last :
  Fraction.Rational) :
    (DyadicPairedIncrementComparison.incrementPairs left right depth first last).map Prod.snd =
      DyadicPairedPrimitivePaths.increments right depth first last := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih => rw [DyadicPairedIncrementComparison.incrementPairs, Data.List.Map.map_append, ih, ih]; rfl

/-- Pairwise increment differences equal the dyadic increments of the original pointwise path difference. -/
theorem incrementPairs_difference (left right : Fraction.Rational → Stokes.PrimitivePoint) (depth : Nat) (first last :
  Fraction.Rational) :
    (DyadicPairedIncrementComparison.incrementPairs left right depth first last).map (fun pair =>
      Stokes.PrimitivePoint.sub pair.1 pair.2) =
      DyadicPairedPrimitivePaths.increments (fun parameter => Stokes.PrimitivePoint.sub (left parameter) (right
        parameter)) depth first last := by
  induction depth generalizing first last with
  | zero =>
      apply congrArg List.singleton
      apply congrArg₂ Stokes.PrimitivePoint.mk <;> dsimp only [Stokes.PrimitivePoint.sub] <;> ring1
  | succ depth ih => rw [DyadicPairedIncrementComparison.incrementPairs, Data.List.Map.map_append, ih, ih]; rfl

end

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Compare the two original paired dyadic increment areas using separate movement and difference-drift bounds.

The ordered endpoints lie in the shared certified interval; the resulting sixteenfold error-times-slope bound keeps the
original width to the fourth power and is independent of depth. -/
theorem increments_area_difference_bound (left right : Fraction.Rational → Stokes.PrimitivePoint) {lower upper error
  slope : Fraction.Rational}
    (errorNonnegative : 0 ≤ error) (slopeNonnegative : 0 ≤ slope)
    (leftBound : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (left last) (left first)) (slope * (last -
        first) ^ 2))
    (rightBound : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (right last) (right first)) (slope * (last -
        first) ^ 2))
    (errors : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      PrimitiveAreaBounds.PrimitivePoint.Bounded (Stokes.PrimitivePoint.sub (Stokes.PrimitivePoint.sub (left last)
        (right last)) (Stokes.PrimitivePoint.sub (left first) (right first))) (error * (last - first) ^ 2))
    (depth : Nat) {first last : Fraction.Rational} (firstInside : lower ≤ first ∧ first ≤ upper)
    (lastInside : lower ≤ last ∧ last ≤ upper) (ordered : first ≤ last) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments left depth first
      last) -
      PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments right depth first last)) ≤ 16 * error * slope *
        (last - first) ^ 4 := by
  let pairs := DyadicPairedIncrementComparison.incrementPairs left right depth first last
  have bounded := PairedIncrementComparison.area_difference_bound pairs
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Geometric.Basic.quarterRadius_nonneg errorNonnegative depth)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Geometric.Basic.quarterRadius_nonneg slopeNonnegative depth)
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    (by
      intro pair member
      apply DyadicPairedAreaRefinement.increments_bounded (fun parameter => Stokes.PrimitivePoint.sub (left parameter)
        (right parameter)) errors depth firstInside lastInside ordered
      rw [← DyadicPairedIncrementComparison.incrementPairs_difference]
      exact Map.mem_map_of_mem member)
    (by
      intro pair member
      apply DyadicPairedAreaRefinement.increments_bounded left leftBound depth firstInside lastInside ordered
      rw [← DyadicPairedIncrementComparison.incrementPairs_left left right]
      exact Map.mem_map_of_mem member)
    (by
      intro pair member
      apply DyadicPairedAreaRefinement.increments_bounded right rightBound depth firstInside lastInside ordered
      rw [← DyadicPairedIncrementComparison.incrementPairs_right left right]
      exact Map.mem_map_of_mem member)
  have length : pairs.length = 2 ^ depth :=
    (Data.List.Map.length_map Prod.fst pairs).symm.trans ((congrArg List.length
      (DyadicPairedIncrementComparison.incrementPairs_left left right depth first last)).trans
      (DyadicPairedAreaRefinement.increments_length left depth first last))
  rw [DyadicPairedIncrementComparison.incrementPairs_left, DyadicPairedIncrementComparison.incrementPairs_right, length]
    at bounded
  have cancel (value : Fraction.Rational) : (((2 ^ depth : Nat) : Fraction.Rational) ^ 2) *
    Geometric.Basic.quarterRadius value depth = value := by
    rw [pow_two, mul_assoc]
    exact Geometric.DyadicCount.dyadic_count_cancel value depth
  exact bounded.trans_eq (by
    calc
      _ = 16 * ((((2 ^ depth : Nat) : Fraction.Rational) ^ 2) * Geometric.Basic.quarterRadius error depth) *
        ((((2 ^ depth : Nat) : Fraction.Rational) ^ 2) * Geometric.Basic.quarterRadius slope depth) * (last - first) ^ 4
          := by ring1
      _ = _ := by rw [cancel, cancel])

end Purelib.Integration.Path.DyadicPairedIncrementComparison
