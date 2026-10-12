module
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Polygon.Stokes
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon

public import Purelib.Riemann.Integration.RectangularPairedPointBanks
public import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

@[expose] public section

/-! The common model-owned trace realizes the actual recursive dyadic line area. -/
namespace Purelib.Riemann.Paths.RectangularDyadicPairedTrace

open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Periods.CenteredBilinearPath (area)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularPairedSegments (PairedSegmentPiece)
open Purelib.Riemann.Integration.RectangularPairedPointBanks (Trace)
open Purelib.Integration.Path.Dyadic.DyadicTrace (tail indexed indexed_inside indexed_last tail_terminal
  indexed_dyadic_area)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin_congr)

variable {leftColumns leftRows rightColumns rightRows : Nat}
  {leftGeometry : Geometry leftColumns leftRows} {rightGeometry : Geometry rightColumns rightRows}

open Purelib.Integration.Path.Dyadic in
/-- The exact edge count of the original unit-interval dyadic tail at the selected depth. -/
abbrev dyadicCount (depth : Nat) : Nat := (DyadicTrace.tail depth 0 1).length

open Purelib.Data in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Integration in
/-- Construct the original paired-piece trace from the exact retained dyadic parameter tail.

The indexed tail supplies the same bounded parameter vector and endpoint equations used to cache the original piece's
affine points. -/
def dyadic (piece : PairedSegmentPiece leftGeometry rightGeometry) (depth : Nat) : Trace piece (dyadicCount depth) :=
  let parameters := Vector.Basic.vectorOfFn (DyadicTrace.indexed 0 (DyadicTrace.tail depth 0 1))
  RectangularPairedPointBanks.Trace.build piece parameters
    (fun vertex => by
      dsimp only [parameters]
      rw [Vector.Basic.vectorOfFn_apply]
      exact DyadicTrace.indexed_inside depth (by decide) vertex)
    (by dsimp only [parameters]; rw [Vector.Basic.vectorOfFn_apply]; rfl)
    (by
        dsimp only [parameters];
        rw [Vector.Basic.vectorOfFn_apply, DyadicTrace.indexed_last, DyadicTrace.tail_terminal])

open Purelib.Data in
open Purelib.Geometry.Rational in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Integration in
/-- Each retained dyadic trace point equals the original affine segment at its exact indexed dyadic parameter. -/
theorem dyadic_points (piece : PairedSegmentPiece leftGeometry rightGeometry) (depth : Nat)
    (vertex : Fin (dyadicCount depth + 1)) :
    (dyadic piece depth).points vertex = Affine.line piece.first (piece.last - piece.first)
      (DyadicTrace.indexed 0 (DyadicTrace.tail depth 0 1) vertex) := by
  rw [(dyadic piece depth).points_eq]
  dsimp only [dyadic, RectangularPairedPointBanks.Trace.build]
  rw [Vector.Basic.vectorOfFn_apply]

open Purelib.Integration.Path.Dyadic.DyadicTrace in
open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Integration.Path.Dyadic in
open Purelib.Riemann.Periods in
/-- The retained paired trace area equals the original dyadic bilinear area on the same affine segment.

Pointwise finite-sum transport preserves the original ordered dyadic edge occurrences and both primitive-value
coordinates. -/
theorem dyadic_area (piece : PairedSegmentPiece leftGeometry rightGeometry) (depth : Nat)
    (values : Basic.Canonical → PrimitivePoint) :
    area (fun vertex : Fin (dyadicCount depth + 1) => values ((dyadic piece depth).points vertex)) =
      DyadicBilinearBoundaryRibbon.dyadicArea
        (fun parameter => values (Affine.line piece.first (piece.last - piece.first) parameter)) depth 0 1 := by
  have equal : area (fun vertex : Fin (dyadicCount depth + 1) => values ((dyadic piece depth).points vertex)) =
      area (fun vertex : Fin (dyadicCount depth + 1) => values (Affine.line piece.first (piece.last - piece.first)
        (DyadicTrace.indexed 0 (DyadicTrace.tail depth 0 1) vertex))) := by
    unfold area
    apply FiniteSum.Fin.sumFin_congr
    intro edge
    dsimp only
    rw [dyadic_points piece depth edge.castSucc, dyadic_points piece depth edge.succ]
  have indexed := DyadicTrace.indexed_dyadic_area
    (fun parameter => values (Affine.line piece.first (piece.last - piece.first) parameter)) depth 0 1
  exact equal.trans indexed

end Purelib.Riemann.Paths.RectangularDyadicPairedTrace
