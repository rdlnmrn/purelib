module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularDyadicPairedTrace
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData
public import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.DyadicSteps
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Both physical orientations give an increasing unit-interval source
parameter after reflection. Every retained fine step has its exact dyadic width. -/
namespace Purelib.Integration.Path.Resampling.OrientedBounds

open Purelib
open Purelib.Data.Rat
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceChordData (sourceParameters sourceParameters_first
  sourceParameters_last)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BoundaryTraceParameters (firstParameter lastParameter)

open Purelib.Riemann.Normalization in
/-- Keep a forward parameter or reflect a backward parameter through one-half. -/
@[expose] def orientParameter (forward : Bool) (parameter : InverseRootPolynomial.Coordinate) : Coordinate :=
  if forward then parameter else 1 - parameter

open Purelib.Integration.Path in
open Purelib.Riemann.Normalization in
/-- Applying the same parameter orientation twice returns the original parameter. -/
theorem orientParameter_twice (forward : Bool) (parameter : InverseRootPolynomial.Coordinate) :
    Resampling.OrientedBounds.orientParameter forward (Resampling.OrientedBounds.orientParameter forward parameter) =
      parameter := by
  cases forward <;> simp only [Resampling.OrientedBounds.orientParameter, if_neg Bool.false_ne_true, if_pos (rfl : true
    = true), -eq_self, -iff_self] <;> first | rfl | ring1

section
open Purelib.Integration.Path
/-- The original oriented start parameter maps to zero. -/
theorem orientParameter_start (forward : Bool) : Resampling.OrientedBounds.orientParameter forward (if forward then 0
  else 1) = 0 := by
  cases forward <;> simp only [Resampling.OrientedBounds.orientParameter, if_neg Bool.false_ne_true, if_pos (rfl : true
    = true), sub_self, -eq_self, -iff_self] <;> rfl

/-- The original oriented finish parameter maps to one. -/
theorem orientParameter_finish (forward : Bool) : Resampling.OrientedBounds.orientParameter forward (if forward then 1
  else 0) = 1 := by
  cases forward <;> simp only [Resampling.OrientedBounds.orientParameter, if_neg Bool.false_ne_true, if_pos (rfl : true
    = true), (show ∀ x : Fraction.Rational, x - 0 = x by intro x; ring1), -eq_self, -iff_self] <;> rfl

end

open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Normalization in
open Purelib.Topology.Polygon in
/-- Orienting both the source and original parameter chain preserves its exact primitive increment list. -/
theorem oriented_increments (values : InverseRootPolynomial.Coordinate → Stokes.PrimitivePoint) (forward : Bool)
    (first : InverseRootPolynomial.Coordinate) (points : List InverseRootPolynomial.Coordinate) :
    SourceListResampling.increments (fun parameter => values (Resampling.OrientedBounds.orientParameter forward
      parameter))
      (Resampling.OrientedBounds.orientParameter forward first) (points.map (Resampling.OrientedBounds.orientParameter
        forward)) =
      SourceListResampling.increments values first points := by
  induction points generalizing first with
  | nil => rfl
  | cons next rest ih =>
    exact congrArg₂ List.cons
      (congrArg₂ Stokes.PrimitivePoint.sub
        (congrArg values (Resampling.OrientedBounds.orientParameter_twice forward next))
        (congrArg values (Resampling.OrientedBounds.orientParameter_twice forward first))) (ih next)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Paths in
/-- The original oriented source step equals the retained interval width times the dyadic step. -/
theorem sourceParameters_step (forward : Bool) (range : PreparedAxisPartitions.Interval) (depth : Nat)
    (edge : Fin (RectangularDyadicPairedTrace.dyadicCount depth)) :
    Resampling.OrientedBounds.orientParameter forward (SourceChordData.sourceParameters forward range depth edge.succ) -
      Resampling.OrientedBounds.orientParameter forward (SourceChordData.sourceParameters forward range depth
        edge.castSucc) =
        (range.upper - range.lower) * (1 / 2) ^ depth := by
  have step := (DyadicSteps.tail_steps depth 0 1).indexed edge
  have affine : Resampling.OrientedBounds.orientParameter forward (SourceChordData.sourceParameters forward range depth
    edge.succ) -
      Resampling.OrientedBounds.orientParameter forward (SourceChordData.sourceParameters forward range depth
        edge.castSucc) =
        (range.upper - range.lower) *
          (DyadicTrace.indexed 0
            (DyadicTrace.tail depth 0 1) edge.succ -
           DyadicTrace.indexed 0
            (DyadicTrace.tail depth 0 1) edge.castSucc) := by
    cases forward <;> simp only [Resampling.OrientedBounds.orientParameter, SourceChordData.sourceParameters,
      BoundaryTraceParameters.firstParameter, BoundaryTraceParameters.lastParameter,
      if_neg Bool.false_ne_true, if_pos (rfl : true = true), -eq_self, -iff_self] <;> ring1
  exact affine.trans ((congrArg (fun step => (range.upper - range.lower) * step) step).trans (by ring1))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior in
open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Paths in
/-- The exact oriented source parameters form an ordered chain with their retained interval endpoints.

The original orientation, interval owner and dyadic depth determine every vertex without replacing the original source
sequence. -/
theorem sourceParameters_chain (forward : Bool) (range : PreparedAxisPartitions.Interval) (depth : Nat) :
    SourceResampling.Chain (Resampling.OrientedBounds.orientParameter forward (BoundaryTraceParameters.firstParameter
      forward range))
      (List.ofFn (fun edge : Fin (RectangularDyadicPairedTrace.dyadicCount depth) =>
        Resampling.OrientedBounds.orientParameter forward (SourceChordData.sourceParameters forward range depth
          edge.succ)))
      (Resampling.OrientedBounds.orientParameter forward (BoundaryTraceParameters.lastParameter forward range)) := by
  have chain := SourceResampling.chain_ofFn
    (fun vertex => Resampling.OrientedBounds.orientParameter forward (SourceChordData.sourceParameters forward range
      depth vertex)) (by
      intro edge
      apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      rw [Resampling.OrientedBounds.sourceParameters_step]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sub_nonneg_direct range.ordered.le)
        (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) depth))
  rw [SourceChordData.sourceParameters_first, SourceChordData.sourceParameters_last] at chain
  exact chain

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior in
open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Normalization in
open Purelib.Riemann.Paths in
/-- A unit-subinterval source chain inherits any common bound on its original dyadic step.

The retained interval containment and orientation certify the exact ordered parameter widths at the supplied depth. -/
theorem sourceParameters_widths (forward : Bool) (range : PreparedAxisPartitions.Interval) (depth : Nat)
    (within : 0 ≤ range.lower ∧ range.upper ≤ 1) {width : InverseRootPolynomial.Coordinate}
    (bounded : (1 / 2 : InverseRootPolynomial.Coordinate) ^ depth ≤ width) :
    SourceResampling.widths (Resampling.OrientedBounds.orientParameter forward (BoundaryTraceParameters.firstParameter
      forward range))
      (List.ofFn (fun edge : Fin (RectangularDyadicPairedTrace.dyadicCount depth) =>
        Resampling.OrientedBounds.orientParameter forward (SourceChordData.sourceParameters forward range depth
          edge.succ))) width := by
  have steps := SourceResampling.widths_ofFn
    (fun vertex => Resampling.OrientedBounds.orientParameter forward (SourceChordData.sourceParameters forward range
      depth vertex)) width (by
      intro edge
      rw [Resampling.OrientedBounds.sourceParameters_step]
      have rangeLe : range.upper - range.lower ≤ 1 :=
        (Fraction.Order.Arithmetic.sub_le_sub_direct within.2 within.1).trans_eq ((show ∀ x : Fraction.Rational, x - 0 =
          x by intro x; ring1) _)
      exact ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct rangeLe
        (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1 / 2)
          depth)).trans_eq
        (Fraction.Field.one_mul _)).trans bounded)
  rw [SourceChordData.sourceParameters_first] at steps
  exact steps

end Purelib.Integration.Path.Resampling.OrientedBounds
