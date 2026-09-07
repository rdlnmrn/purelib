import FTA.CCLBranchEventOwner

/-!
# Exact rational terminals on identically-zero event charts

This small module keeps the identically-zero midpoint calculation separate
from the deeply dependent coupled-controller payload.  The split lets the
ordinary heartbeat and recursion settings elaborate both pieces directly.
-/

namespace FTA
namespace CCLEventTerminal

open CCL
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.ComputablePolynomial
open FTA.ProjectivePath

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial := DensePolynomial QI

structure ExactRationalRoot (p : GaussianPolynomial) where
  point : QI
  root : p.eval point = 0

/-- An exact rational root together with the rational box that caused its
discovery.  This localized form is used by the final transducer layers so an
exact terminal cannot be confused with a different separated root region. -/
structure LocalizedExactRationalRoot
    (p : GaussianPolynomial) (box : RatBox) where
  point : QI
  root : p.eval point = 0
  contains : box.Contains point

/-- Identically-zero cleared coordinates need no parser-owner re-isolation:
the canonical relevant-event interval already excludes projective poles, so
its rational midpoint is an exact affine polynomial root. -/
def RelevantCurveEvent.identicallyZeroRoot
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    (event : RelevantCurveEvent p path box)
    (realZero : (clearedReal p path).isZero = true)
    (imagZero : (clearedImag p path).isZero = true) :
    ExactRationalRoot p := by
  let interval := ownerRoot event
  let parameter := FTA.RationalPolynomialBounds.midpoint
    interval.interval.lower interval.interval.upper
  let point := path.value parameter
  have lower : interval.interval.lower ≤ parameter :=
    (FTA.RationalPolynomialBounds.lower_lt_midpoint interval.proper).le
  have upper : parameter ≤ interval.interval.upper :=
    (FTA.RationalPolynomialBounds.midpoint_lt_upper interval.proper).le
  have denominator :=
    FTA.CCLBranchEventOwner.RelevantCurveEvent.ownerDenominator_ne
      event lower upper
  exact
    { point := point
      root := ProjectivePath.eval_eq_zero_of_cleared_isZero p path parameter
        denominator realZero imagZero }

/-- When both projectively cleared coordinates vanish identically, the
midpoint of the final rational owner interval is an exact affine root. -/
def InputEventCell.identicallyZeroRoot
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (realZero : (clearedReal p path).isZero = true)
    (imagZero : (clearedImag p path).isZero = true) :
    ExactRationalRoot p := by
  let refined := (cell.branch.computeEventSigns cell.parent).refined
  let parameter := FTA.RationalPolynomialBounds.midpoint
    refined.interval.lower refined.interval.upper
  let point := path.value parameter
  have lower : refined.interval.lower ≤ parameter :=
    (FTA.RationalPolynomialBounds.lower_lt_midpoint refined.proper).le
  have upper : parameter ≤ refined.interval.upper :=
    (FTA.RationalPolynomialBounds.midpoint_lt_upper refined.proper).le
  have denominator := cell.path_denominator_ne_on_cell lower upper
  exact
    { point := point
      root := ProjectivePath.eval_eq_zero_of_cleared_isZero p path parameter
        denominator realZero imagZero }

/-- Executable clearance-controlled rational point used for a localized exact
terminal. -/
def InputEventCell.interiorApproximationPoint
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : FTA.LocalExtraction.BoxBoundaryClearanceCertificate p box) :
    QI :=
  path.value
    (cell.clearedApproximation (cell.interiorApproximationWidth clearance)
      (cell.interiorApproximationWidth_pos clearance)).refined.interval.lower

theorem InputEventCell.interiorApproximationPoint_strictContains
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : FTA.LocalExtraction.BoxBoundaryClearanceCertificate p box) :
    box.StrictContains (InputEventCell.interiorApproximationPoint cell clearance) := by
  simpa only [InputEventCell.interiorApproximationPoint] using
    cell.clearedApproximation_strictContains clearance

theorem InputEventCell.interiorApproximationPoint_root_of_identicallyZero
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : FTA.LocalExtraction.BoxBoundaryClearanceCertificate p box)
    (realZero : (clearedReal p path).isZero = true)
    (imagZero : (clearedImag p path).isZero = true) :
    p.eval (InputEventCell.interiorApproximationPoint cell clearance) = 0 := by
  let epsilon := cell.interiorApproximationWidth clearance
  have epsilonPositive := cell.interiorApproximationWidth_pos clearance
  let approximation := cell.clearedApproximation epsilon epsilonPositive
  let parameter := approximation.refined.interval.lower
  have lower :
      (cell.branch.computeEventSigns cell.parent).refined.interval.lower ≤
        parameter := by
    simpa only [parameter, approximation] using approximation.refines.1
  have upper : parameter ≤
      (cell.branch.computeEventSigns cell.parent).refined.interval.upper := by
    exact approximation.refined.proper.le.trans approximation.refines.2
  have denominator := cell.path_denominator_ne_on_cell lower upper
  simpa only [InputEventCell.interiorApproximationPoint, epsilon, approximation,
    parameter] using
      ProjectivePath.eval_eq_zero_of_cleared_isZero p path parameter denominator
        realZero imagZero

/-- The clearance-controlled rational approximation point is strictly inside
the event's root box.  When both cleared coordinates vanish identically, that
same point is therefore an exact localized rational root. -/
def InputEventCell.identicallyZeroLocalizedRoot
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (clearance : FTA.LocalExtraction.BoxBoundaryClearanceCertificate p box)
    (realZero : (clearedReal p path).isZero = true)
    (imagZero : (clearedImag p path).isZero = true) :
    LocalizedExactRationalRoot p box :=
  { point := InputEventCell.interiorApproximationPoint cell clearance
    root := InputEventCell.interiorApproximationPoint_root_of_identicallyZero
      cell clearance realZero imagZero
    contains :=
      (InputEventCell.interiorApproximationPoint_strictContains cell clearance).contains }

end CCLEventTerminal
end FTA
