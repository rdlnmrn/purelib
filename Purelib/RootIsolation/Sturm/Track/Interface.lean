module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Refinement
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.RootIsolation.Sturm.Count.Basic
import Purelib.RootIsolation.Sturm.Track.Basic
public import Purelib.RootIsolation.Sturm.Track.Request
import Purelib.Data.Rat.Interval.Width
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Polynomial.Dense.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Shrinking nonzero-event tracks

The original rational polynomial has a retained nonzero coefficient certificate and a proper current cell with nonzero
doubled Sturm count. Its finite request operations preserve that polynomial and refine the same current event.
-/

public section

namespace Purelib.RootIsolation.Sturm.Track.Interface

set_option genInjectivity false in
/-- A total finite refinement machine for one displayed nonzero Sturm event.
The current interval and its nonzero doubled count are explicit finite data.

The original rational polynomial has a retained nonzero coefficient certificate and a proper current cell with nonzero
doubled Sturm count. Its finite request operations preserve that polynomial and refine the same current event. -/
structure ZeroEventTrack (polynomial : Dense.Rational.Basic.CoordinatePolynomial) where
  /-- The original event polynomial is nonzero. -/ polynomialNonzero : polynomial.isZero = false
  /-- The retained current finite Sturm-count state for the original event polynomial. -/ current :
    Sturm.Track.Basic.State polynomial

constructive_injectivity ZeroEventTrack

namespace ZeroEventTrack

/-- Answer one positive rational width request and retain the same executable
track interface at the returned interval.

The nonzero polynomial and current proper event cell remain fixed while finite refinement answers the supplied positive
rational width request, retaining its nonzero doubled-count evidence. -/
@[expose] def request
    {polynomial : Dense.Rational.Basic.CoordinatePolynomial} (track : Sturm.Track.Interface.ZeroEventTrack polynomial)
    (epsilon : Fraction.Rational) : Sturm.Track.Interface.ZeroEventTrack polynomial :=
  { polynomialNonzero := track.polynomialNonzero
    current := Sturm.Track.Request.request polynomial
      track.polynomialNonzero track.current epsilon }

/-- Every request returns a rational subinterval of the current interval. -/
theorem request_refines
    {polynomial : Dense.Rational.Basic.CoordinatePolynomial} (track : Sturm.Track.Interface.ZeroEventTrack polynomial)
    (epsilon : Fraction.Rational) :
    (track.request epsilon).current.cell.interval.Refines
      track.current.cell.interval :=
  Sturm.Track.Request.request_refines polynomial
    track.polynomialNonzero track.current epsilon

/-- A positive request bounds the returned rational interval width. -/
theorem request_width_le
    {polynomial : Dense.Rational.Basic.CoordinatePolynomial} (track : Sturm.Track.Interface.ZeroEventTrack polynomial)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (Data.Rat.Interval.Bounds.width (track.request epsilon).current.cell.interval) ≤ epsilon :=
  Sturm.Track.Request.request_width_le polynomial
    track.polynomialNonzero track.current epsilon positive

/-- The returned state retains an explicit nonzero doubled Sturm count. -/
theorem request_countNonzero
    {polynomial : Dense.Rational.Basic.CoordinatePolynomial} (track : Sturm.Track.Interface.ZeroEventTrack polynomial)
    (epsilon : Fraction.Rational) :
    Sturm.Count.Basic.sturmRootCount2 polynomial
      (track.request epsilon).current.cell.interval.lower
      (track.request epsilon).current.cell.interval.upper ≠ 0 :=
  (track.request epsilon).current.countNonzero

/-- Successive requests are nested by direct composition of their displayed
rational refinement certificates. -/
theorem successive_refines
    {polynomial : Dense.Rational.Basic.CoordinatePolynomial} (track : Sturm.Track.Interface.ZeroEventTrack polynomial)
    (first second : Fraction.Rational) :
    ((track.request first).request second).current.cell.interval.Refines
      track.current.cell.interval :=
  Data.Rat.Interval.Refinement.intervalRefines_trans
    (Sturm.Track.Interface.ZeroEventTrack.request_refines (track.request first) second)
    (Sturm.Track.Interface.ZeroEventTrack.request_refines track first)

end ZeroEventTrack

end Purelib.RootIsolation.Sturm.Track.Interface

end
