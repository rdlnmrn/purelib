module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry.Deformation.Lift
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Values.Comparison
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Route.Acquisition.Comparison.Initial.Endpoint
import Purelib.Data.Rat.Interval.Radius
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Actual curved and paid-route boundaries of the signed ruled lift

The old queried deformation product agrees with an arbitrary original curved
Reading at its exact curve-side point. Both fixed endpoint sides preserve the
original source and target signs. Independently retained actual L-route
factor readings compare at their exact common physical points, and the
already derived paid-route Endpoint connects its literal stored full-cubic
finish Owner. No observation or owner preparation is replayed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry

namespace Deformation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Factors (Budgets)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first last : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {targetReading : Transport.Reading actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7}
variable {budgets : Budgets anchor} {geometry : Geometry source targetReading anchor.regular payment}
variable {ordered : first ≤ last}

include firstInside lastInside in
/-- The original orientation-preserving fraction parameter stays in the original quarter interval. -/
theorem fraction_time_inside (fraction : Fraction.Rational) (inside : FixedRootBoxPath.Inside fraction) :
    FixedRootBoxPath.Inside (first + fraction * (last - first)) :=
  Box.coordinate_between firstInside lastInside inside

include payment in
/-- The SAME original depth-seven payment pays the actual intermediate curve time without strengthening the input. -/
theorem fraction_time_paid (ordered : first ≤ last) (fraction : Fraction.Rational)
    (inside : FixedRootBoxPath.Inside fraction) :
    ((first + fraction * (last - first)) - first) ^ 2 ≤
      Approximation.Rational.Geometric.Basic.quarterRadius 1 7 := by
  let interval : Interval.Bounds := ⟨first, last, ordered⟩
  have contained := Box.coordinate_between ⟨Fraction.Order.Basic.le_refl first, ordered⟩
    ⟨ordered, Fraction.Order.Basic.le_refl last⟩ inside
  have short := Interval.Radius.sub_sq_le_sampleRadiusSq interval (sample := interval.lower) contained
  rewrite [Interval.Radius.sampleRadiusSq_lower_eq_widthSq] at short
  exact short.trans payment

namespace Lift.Reading

variable {fraction : Fraction.Rational} {fractionInside : FixedRootBoxPath.Inside fraction}
variable {completed : Lift budgets geometry ordered fraction fractionInside}
variable {blend : Fraction.Rational} {blendInside : FixedRootBoxPath.Inside blend}

/-- The actual zero-blend product agrees with the independently retained curved Reading at the SAME arc fraction.

The source Seed, signed ordinate containment and actual cofactor refinements
construct both factor comparisons. The input curved Reading may be any old
query of the original retained quarter preparation; it is not rebuilt.
-/
def curve (reading : Reading completed 0 (of_decide_eq_true rfl))
    (curved : Transport.Reading actual (first + fraction * (last - first))
      (fraction_time_inside (firstInside := firstInside) (lastInside := lastInside) fraction fractionInside)) :
    NamedEquivalent reading.values.value.name curved.lift.value.name :=
  Factors.Values.agrees_geometric budgets reading.values
    (geometry.deformation_inside ordered fractionInside (of_decide_eq_true rfl))
    reading.unit_refines reading.normal_refines curved
    (geometry.deformation_curve fraction)
    (fraction_time_paid (payment := payment) ordered fraction fractionInside)

/-- Two actual signed-strip queries at an equal physical point retain the same full-cubic sheet.

Both original factor query caches and complete Values remain separate. Their
refinement into the original two source boxes constructs the comparison even
when the arc fractions, blend parameters and preparations differ.
-/
def equivalent (reading : Reading completed blend blendInside)
    {otherFraction : Fraction.Rational} {otherFractionInside : FixedRootBoxPath.Inside otherFraction}
    {otherCompleted : Lift budgets geometry ordered otherFraction otherFractionInside}
    {otherBlend : Fraction.Rational} {otherBlendInside : FixedRootBoxPath.Inside otherBlend}
    (other : Reading otherCompleted otherBlend otherBlendInside)
    (point_eq : geometry.deformation fraction blend = geometry.deformation otherFraction otherBlend) :
    NamedEquivalent reading.values.value.name other.values.value.name :=
  Factors.Values.equivalent budgets reading.values other.values
    (geometry.deformation_inside ordered fractionInside blendInside) point_eq
    reading.unit_refines reading.normal_refines other.unit_refines other.normal_refines

/-- Compare actual deformation and physical factor queries on the SAME sharp spatial box.

The physical input can be a cached head or tail reading of the original
L-route. Its original segment, completed preparation, actual query Owners
and product remain indices. Exact common-point evidence is geometric only;
the full signed root comparison is derived here from the source budgets.
-/
def segment (reading : Reading completed blend blendInside)
    {start finish : Canonical}
    {segment : ClearSegment (Paths.polynomial parameter) (Factors.sourceBox anchor) start finish}
    {within : segment.WithinAmbient} {segmentCompleted : Factors.Segment budgets segment within}
    {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}
    (physical : Factors.Segment.Reading segmentCompleted time inside)
    (point_eq : geometry.deformation fraction blend = segment.pointAt time) :
    NamedEquivalent reading.values.value.name physical.values.value.name :=
  Factors.Values.equivalent budgets reading.values physical.values
    (geometry.deformation_inside ordered fractionInside blendInside) point_eq
    reading.unit_refines reading.normal_refines physical.unit_refines physical.normal_refines

end Lift.Reading

/-- Every blend on the fixed first endpoint has the unchanged actual source Lift's full-cubic sign. -/
def source_equivalent {completed : Lift budgets geometry ordered 0 (of_decide_eq_true rfl)}
    {blend : Fraction.Rational} {inside : FixedRootBoxPath.Inside blend}
    (reading : Lift.Reading completed blend inside) :
    NamedEquivalent reading.values.value.name source.lift.value.name := by
  have sourcePaid : (first - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7 := by
    rewrite [show first - first = 0 by ring1, show (0 : Fraction.Rational) ^ 2 = 0 by decide +kernel]
    exact (Fraction.Order.Arithmetic.sq_nonneg_direct (last - first)).trans payment
  exact Factors.Values.agrees_geometric budgets reading.values
    (geometry.deformation_inside ordered (of_decide_eq_true rfl) inside)
    reading.unit_refines reading.normal_refines source (geometry.deformation_first blend) sourcePaid

/-- Every blend on the fixed last endpoint has the independently retained actual target Lift's full-cubic sign. -/
def target_equivalent {completed : Lift budgets geometry ordered 1 (of_decide_eq_true rfl)}
    {blend : Fraction.Rational} {inside : FixedRootBoxPath.Inside blend}
    (reading : Lift.Reading completed blend inside) :
    NamedEquivalent reading.values.value.name targetReading.lift.value.name :=
  Factors.Values.agrees_geometric budgets reading.values
    (geometry.deformation_inside ordered (of_decide_eq_true rfl) inside)
    reading.unit_refines reading.normal_refines targetReading (geometry.deformation_last blend) payment

/-- The SAME actual supplied paid-route source Owner agrees with the signed ruled lift's fixed source side. -/
def paid_source (entry : Factors.Route.Acquisition.Comparison.Initial source)
    {completed : Lift budgets geometry ordered 0 (of_decide_eq_true rfl)}
    {blend : Fraction.Rational} {inside : FixedRootBoxPath.Inside blend}
    (reading : Lift.Reading completed blend inside) :
    NamedEquivalent (ownerRootName entry.owner.parameterNonzero entry.owner) reading.values.value.name :=
  entry.equivalent.symm.trans (source_equivalent reading).symm

/-- The literal stored paid L-route finish Owner agrees with the SAME signed deformation's fixed target side.

The retained original Endpoint supplies its internally derived route/output
comparison, including all actual advances, observations and handoffs. The
new target-side comparison is derived from the original source Seed and
cofactor budget. No equality to another paid execution or old cover is used.
-/
def paid_finish {entry : Factors.Route.Acquisition.Comparison.Initial source}
    {factors : Factors.Route budgets geometry}
    {retained : Factors.Route.Acquisition factors entry.owner}
    {result : Factors.Route.Acquisition.Comparison.Initial.Result entry retained}
    (endpoint : Factors.Route.Acquisition.Comparison.Initial.Result.Endpoint entry result)
    {completed : Lift budgets geometry ordered 1 (of_decide_eq_true rfl)}
    {blend : Fraction.Rational} {inside : FixedRootBoxPath.Inside blend}
    (reading : Lift.Reading completed blend inside) :
    NamedEquivalent (ownerRootName retained.finishOwner.parameterNonzero retained.finishOwner)
      reading.values.value.name :=
  endpoint.finish.trans (target_equivalent reading).symm

end Deformation

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Geometry
