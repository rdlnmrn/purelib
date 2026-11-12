module

public import Purelib.Riemann.Paths.ClearBoxPaths
public import Purelib.Polynomial.Geometry.ClearPath.Distance
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Tactic.Ring

/-! # Whole-source distances along the actual axis-aligned Route factory

The original factory's zero, one or two edge occurrences retain their
orientation and common corner. The corner separates the real and imaginary
displacements, so their squared energies add to the whole endpoint energy.
-/

public section

namespace Purelib.Riemann.Paths.ClearBoxPaths.Route

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)

variable {polynomial : ClearPath.GaussianPolynomial} {box : Box}

/-- The original horizontal-then-vertical corner partitions the two exact squared coordinate displacements. -/
private theorem corner_energy (start finish : Canonical) :
    Norm.Basic.normSq (Components.Basic.point finish.re start.im - start) +
        Norm.Basic.normSq (finish - Components.Basic.point finish.re start.im) =
      Norm.Basic.normSq (finish - start) := by
  rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical,
    Norm.Basic.normSq_eq_canonical]
  change (finish.re - start.re) * (finish.re - start.re) +
      (start.im - start.im) * (start.im - start.im) +
      ((finish.re - finish.re) * (finish.re - finish.re) +
        (finish.im - start.im) * (finish.im - start.im)) =
    (finish.re - start.re) * (finish.re - start.re) +
      (finish.im - start.im) * (finish.im - start.im)
  ring1

/-- Every point on every SAME retained factory edge is bounded from its original source.

In the two-edge case the second leg retains the whole first displacement;
the orthogonal corner identity pays both terms. The zero-edge branch has
no moving observations, and neither singleton branch acquires another edge.
-/
theorem build_pointBound (clearance : RegionClearance polynomial box)
    (start finish : Canonical) (first : box.Contains start) (last : box.Contains finish) :
    ClearPath.PointBound start (2 * Norm.Basic.normSq (finish - start))
      (build clearance start finish first last).path := by
  unfold build
  split
  · rename_i equal
    cases equal
    exact True.intro
  · dsimp only
    split
    · exact ClearPath.PointBound.single _
    · split
      · exact ClearPath.PointBound.single _
      · exact ClearPath.PointBound.pair _ _ (corner_energy start finish)

end Purelib.Riemann.Paths.ClearBoxPaths.Route

end
