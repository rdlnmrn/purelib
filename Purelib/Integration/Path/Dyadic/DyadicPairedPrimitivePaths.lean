module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
public import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Tactic.Ring

public section

/-! Actual paired dyadic increments, with the endpoint contribution retained
when reading their full area as a bilinear boundary integral. -/
namespace Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths

open Purelib.Data.List

open Purelib.Data.Gaussian in
/-- The canonical Gaussian carrier underlying paired primitive coordinates. -/
private abbrev Gaussian := Basic.Canonical

open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Topology.Polygon in
/-- List the original paired primitive differences in midpoint-subdivision order. -/
@[expose] def increments (values : Fraction.Rational → Stokes.PrimitivePoint) : Nat → Fraction.Rational →
  Fraction.Rational → List Stokes.PrimitivePoint
  | 0, first, last => [Stokes.PrimitivePoint.sub (values last) (values first)]
  | depth + 1, first, last =>
      Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths.increments values depth first
        (PreparedBoxPartitions.midpoint first last) ++
        Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths.increments values depth
        (PreparedBoxPartitions.midpoint first last) last

section
open Purelib.Data.Rat
open Purelib.Integration.Path.Dyadic
open Purelib.Topology.Polygon
/-- Left readback equals the original left-coordinate dyadic increments.

Both scans follow the same retained midpoint subdivisions and concatenate
their left and right subintervals in the original order. -/
theorem increments_left (values : Fraction.Rational → Stokes.PrimitivePoint) (depth : Nat) (first last :
  Fraction.Rational) :
    (DyadicPairedPrimitivePaths.increments values depth first last).map Stokes.PrimitivePoint.left =
      DyadicPrimitivePaths.dyadicIncrements (fun parameter => (values parameter).left) depth first last := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih => rw [DyadicPairedPrimitivePaths.increments, Map.map_append, ih, ih]; rfl

/-- Right readback equals the original right-coordinate dyadic increments.

Both scans follow the same retained midpoint subdivisions. Projection keeps
the right coordinate of each paired endpoint difference in that order. -/
theorem increments_right (values : Fraction.Rational → Stokes.PrimitivePoint) (depth : Nat) (first last :
  Fraction.Rational) :
    (DyadicPairedPrimitivePaths.increments values depth first last).map Stokes.PrimitivePoint.right =
      DyadicPrimitivePaths.dyadicIncrements (fun parameter => (values parameter).right) depth first last := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih => rw [DyadicPairedPrimitivePaths.increments, Map.map_append, ih, ih]; rfl

end

open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
open Purelib.Topology.Polygon in
/-- The paired dyadic increment total is the exact original finish-minus-start primitive difference. -/
theorem increments_total (values : Fraction.Rational → Stokes.PrimitivePoint) (depth : Nat) (first last :
  Fraction.Rational) :
    PairedIncrementArea.total (DyadicPairedPrimitivePaths.increments values depth first last) =
      Stokes.PrimitivePoint.sub (values last) (values first) := by
  unfold PairedIncrementArea.total
  rw [DyadicPairedPrimitivePaths.increments_left, DyadicPairedPrimitivePaths.increments_right,
    DyadicPrimitivePaths.dyadicIncrements_sum, DyadicPrimitivePaths.dyadicIncrements_sum]
  rfl

open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Periods in
open Purelib.Topology.Polygon in
/-- Paired increment area retains the endpoint chord correction.

Each finite midpoint split combines the original paired increments and their
endpoint differences. The area is the bilinear dyadic area less the chord
between the same original endpoints. -/
theorem increments_area (values : Fraction.Rational → Stokes.PrimitivePoint) (depth : Nat) (first last :
  Fraction.Rational) :
    PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments values depth first last) =
      DyadicBilinearBoundaryRibbon.dyadicArea values depth first last - Stokes.edgeArea (values first) (values last) :=
        by
  induction depth generalizing first last with
  | zero =>
      change Stokes.edgeArea (Stokes.PrimitivePoint.sub (values last) (values first)) Stokes.PrimitivePoint.zero + 0 =
        Stokes.edgeArea (values first) (values last) - Stokes.edgeArea (values first) (values last)
      simp only [Stokes.edgeArea, Stokes.PrimitivePoint.zero, mul_zero, zero_mul, sub_self, add_zero, -eq_self,
        -iff_self]
      rfl
  | succ depth ih =>
      rw [DyadicPairedPrimitivePaths.increments, PairedAreaBlocks.area_append, ih, ih,
        DyadicPairedPrimitivePaths.increments_total, DyadicPairedPrimitivePaths.increments_total,
        DyadicBilinearBoundaryRibbon.dyadicArea_succ]
      simp only [Stokes.edgeArea, Stokes.PrimitivePoint.sub]
      ring1

end Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
