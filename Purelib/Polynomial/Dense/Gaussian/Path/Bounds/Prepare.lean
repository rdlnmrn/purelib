module

import Purelib.Data.Rat.Interval.Radius
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Cover.Retained
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Pair.Cover.Prepare
import Purelib.Polynomial.Clearance.Pair.Enclosure
import Purelib.Polynomial.Clearance.Pair.Sample

/-!
# Cached polynomial bounds on a retained affine path

Finite interval Horner enclosures and squared variation bounds give an executable
denominator-clearance test.  Component enclosures improve the value ceiling;
retained quadratic and finite-cover certificates sharpen unresolved margins
without losing an existing lower bound.
Failure means only that this proposal has no
positive margin; it is not a root or a non-certifiability certificate.  All
parameter polynomials and numerical bounds are cached with their exact laws.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Geometry.Rational

namespace Data

variable {polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial} {origin direction : Canonical} {interval :
  Data.Rat.Interval.Bounds}

/-- Demand-driven separation on the unchanged path.  Accepted data and a
previously retained attempt are reused verbatim.  Exact endpoint zeros skip
subdivision; the caller can report its separately checked obstruction.

The original positive-floor, retained-attempt and endpoint-zero branches return the same data. Only the remaining branch
prepares clearance from the cached enclosures and sample certificate. -/
@[expose] public def sharpen (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval) :
  Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval :=
  if 0 < data.lowerBound then data
  else
    match data.clearance with
    | some _ => data
    | none =>
        if data.sample = 0 then data
        else if data.value interval.upper = 0 then data
        else
          let clearance := Clearance.Pair.Cover.Retained.fromEnclosures
            data.enclosures (some data.sampleCertificate)
          { data with
            clearance := some clearance
            lowerBound := max (max (Data.Gaussian.Norm.Basic.normSq data.sample / 2 -
              data.slopeBound * Data.Rat.Interval.Radius.sampleRadiusSq
                interval interval.lower) data.enclosures.normFloor)
                clearance.result.normFloor
            lowerBound_eq := rfl }

/-- Sharpening leaves an already positive path bound unchanged.

The first retained branch checks the supplied positive lower bound and returns the same complete data record. -/
public theorem sharpen_of_positive (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval)
  (positive : 0 < data.lowerBound) :
    data.sharpen = data := by
  rw [Dense.Gaussian.Path.Bounds.Basic.Data.sharpen, if_pos positive]

/-- Sharpening cannot decrease the retained squared-norm lower bound.

All early-return branches retain their lower bound. The remaining branch combines the same proposals with a nonnegative
retained-cover floor. -/
public theorem sharpen_lowerBound (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction interval) :
    data.lowerBound ≤ data.sharpen.lowerBound := by
  unfold Dense.Gaussian.Path.Bounds.Basic.Data.sharpen
  split
  · exact le_rfl
  · rename_i unresolved
    split
    · exact le_rfl
    · split
      · exact le_rfl
      · split
        · exact le_rfl
        · exact (le_of_not_gt unresolved).trans (Dense.Gaussian.Path.Bounds.Basic.Data.lowerBound_nonnegative _)

/-- Sharpening cannot decrease the retained coordinate lower bound.

All early-return branches retain their coordinate floor. The remaining branch combines the existing enclosure floor with
the new cover coordinate proposal. -/
public theorem sharpen_coordinateLower (data : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction
  interval) :
    data.coordinateLower ≤ data.sharpen.coordinateLower := by
  unfold Dense.Gaussian.Path.Bounds.Basic.Data.sharpen
  split
  · exact le_rfl
  · split
    · exact le_rfl
    · rename_i absent
      split
      · exact le_rfl
      · split
        · exact le_rfl
        · change max data.enclosures.coordinateFloor (Clearance.Pair.Cover.Retained.optionalCoordinate data.clearance) ≤
            max data.enclosures.coordinateFloor _
          rw [absent]
          exact Fraction.Order.Basic.max_le (Fraction.Order.Basic.le_max_left _ _)
            (data.enclosures.coordinateFloor_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _))

end Data

end Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic

namespace Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Prepare

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib
open Purelib.Data
open Purelib.Polynomial

/-- Public coefficient-only bounds with internally generated separation
proposals.  Unresolved proposals remain inspectable in the returned data.

Coarse preparation computes and caches the affine and interval data once. Sharpening then reuses that record and
performs refinement only when its retained stop conditions permit it. -/
@[expose] public def prepare (polynomial : Basic.CanonicalCoefficients.CoefficientPolynomial) (origin direction :
  Canonical)
    (interval : Data.Rat.Interval.Bounds) : Dense.Gaussian.Path.Bounds.Basic.Data polynomial origin direction
      interval :=
  (Dense.Gaussian.Path.Bounds.Basic.prepareCoarse polynomial origin direction interval).sharpen

end Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Prepare
