module
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
public import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Path.Dyadic.SourceResampling
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Integration.Path.Dyadic.SourceListResampling
import Purelib.Integration.Path.Dyadic.DyadicSteps
public import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Compare an actual finite source chain against its original dyadic
reference, retaining all increments and the actual reference depth. -/
namespace Purelib.Integration.Path.Dyadic.SourceDyadicResampling

open Purelib.Data.Rat

open Purelib.Riemann.Periods.CenteredBilinearPath

open Purelib.Integration.Path.PairedIncrementArea (area)

open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Periods in
/-- The original dyadic endpoint list terminates at its exact retained last endpoint. -/
private theorem terminal_dyadic (depth : Nat) (first last : CenteredBilinearPath.Coordinate) :
    SourceListResampling.terminal first (DyadicTrace.tail depth first last) = last := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih => rw [DyadicTrace.tail, SourceListResampling.terminal_append, ih, ih]

open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- Source-list increments over the original dyadic targets equal the canonical paired dyadic increments. -/
private theorem increments_dyadic (values : CenteredBilinearPath.Coordinate → Stokes.PrimitivePoint) (depth : Nat)
  (first last : CenteredBilinearPath.Coordinate) :
    SourceListResampling.increments values first (DyadicTrace.tail depth first last) =
      DyadicPairedPrimitivePaths.increments values depth first last := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih =>
    rw [DyadicTrace.tail, SourceListResampling.increments_append, SourceDyadicResampling.terminal_dyadic, ih, ih]; rfl

open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Periods in
/-- Ordered endpoints give an ordered chain through the original dyadic target list. -/
private theorem dyadic_chain (depth : Nat) {first last : CenteredBilinearPath.Coordinate} (ordered : first ≤ last) :
    SourceResampling.Chain first (DyadicTrace.tail depth first last) last := by
  induction depth generalizing first last with
  | zero => exact .cons ordered (.nil last)
  | succ depth ih =>
    have middle := PreparedBoxPartitions.midpoint_between ordered
    exact SourceListResampling.Chain.append (ih middle.1) (ih middle.2)

section
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Periods
/-- An exact common step bounded by a width gives the same width bound on every retained step. -/
private theorem steps_widths {first step width : CenteredBilinearPath.Coordinate} {points : List
  CenteredBilinearPath.Coordinate}
    (steps : DyadicSteps.Steps first points step) (bound : step ≤ width) : SourceResampling.widths first points width :=
      by
  induction points generalizing first with
  | nil => trivial
  | cons next rest ih => exact ⟨steps.1.trans_le bound, ih steps.2⟩

/-- Increasing the common width bound preserves the original parameter-chain width certificate. -/
private theorem widths_mono {first width next : CenteredBilinearPath.Coordinate} {points : List
  CenteredBilinearPath.Coordinate}
    (steps : SourceResampling.widths first points width) (bound : width ≤ next) : SourceResampling.widths first points
      next := by
  induction points generalizing first with
  | nil => trivial
  | cons head rest ih => exact ⟨steps.1.trans bound, ih steps.2⟩

end

open Purelib.Data.Gaussian in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Periods in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Compare an original unit-interval parameter chain with the dyadic chain at the supplied depth.

Both sample the same two-coordinate source with its retained movement bound; the area estimate uses the larger of the
original mesh width and dyadic step, with factor sixteen times squared density. -/
theorem dyadic_resampling_bound (values : CenteredBilinearPath.Coordinate → Stokes.PrimitivePoint) {density width :
  CenteredBilinearPath.Coordinate}
    (increment : ∀ a b, 0 ≤ a → a ≤ 1 → 0 ≤ b → b ≤ 1 →
      PrimitiveAreaBounds.PrimitivePoint.Bounded
        (Stokes.PrimitivePoint.sub (values b) (values a)) (density * (b - a) ^ 2))
    {points : List CenteredBilinearPath.Coordinate} (chain : SourceResampling.Chain 0 points 1) (steps :
      SourceResampling.widths 0 points width) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (area (SourceListResampling.increments values 0 points) -
      area (DyadicPairedPrimitivePaths.increments values depth 0 1)) ≤
        16 * density ^ 2 * (max width ((1 / 2 : CenteredBilinearPath.Coordinate) ^ depth)) ^ 2 := by
  have rightSteps := SourceDyadicResampling.steps_widths (DyadicSteps.tail_steps depth 0 1)
    ((show (1 - 0 : CenteredBilinearPath.Coordinate) * (1 / 2) ^ depth = (1 / 2) ^ depth by ring1).trans_le
      (Fraction.Order.Basic.le_max_right width _))
  have estimate := SourceListResampling.increment_resampling_bound values increment chain
    (SourceDyadicResampling.dyadic_chain depth (by decide))
    (by decide) (by decide) (SourceDyadicResampling.widths_mono steps (Fraction.Order.Basic.le_max_left _ _)) rightSteps
  rw [SourceDyadicResampling.increments_dyadic] at estimate
  exact estimate.trans_eq (by ring1)

end Purelib.Integration.Path.Dyadic.SourceDyadicResampling

end
