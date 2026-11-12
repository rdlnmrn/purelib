module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading
import Purelib.Riemann.Topology.SquareRootContinuationChain.Exact.Transport
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Norm.Basic

/-! # Comparison with original geometric endpoint lifts

The actual prepared physical-factor query and the independent original
quarter Reading remain separate inputs. Their exact spatial endpoint identity
and original depth-seven payment derive the normalized and cofactor name
comparisons internally. The resulting actual full product agrees with the
original target Lift.value. This proves no identity with the separate
full-cubic Covered.finishOwner of the spatial route.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
  (ownerRootName)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Topology
open Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
open Purelib.RootIsolation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {first : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {source : Transport.Reading actual first firstInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}
variable {last : Fraction.Rational} {lastInside : FixedRootBoxPath.Inside last}

/-- Compare the actual retained normalized query certificate with the original exact target ordinate.

The actual target lies in the same source signed square by the original
quarter payment. Its original conic square and the exact physical endpoint
identity give the unchanged radicand. Candidate containment comes from the
actual queried Owner's source-seed refinement, preserving all input caches.
-/
def normal_agrees_target (reading : Reading completed time inside)
    (point_eq : segment.pointAt time = (Parameter.sourcePoint site parameter (Waist.direction quarter last)).base)
    (paid : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7) :
    NamedEquivalent reading.values.normalRoot.value.name
      (Coherence.exact (Parameter.sourcePoint site parameter (Waist.direction quarter last)).ordinate).name := by
  have square := (Parameter.sourcePoint site parameter (Waist.direction quarter last)).quadratic
  rewrite [← (Parameter.sourcePoint site parameter (Waist.direction quarter last)).coordinate_base,
    ← point_eq] at square
  have targetInside := Clearance.quarter_ordinate_inside site parameter quarter first last anchor.seed.separation paid
  exact anchor.seed.retained_agrees_exact reading.normal reading.values.normalRoot reading.values.normalRoot_eq
    reading.normal_refines (Parameter.sourcePoint site parameter (Waist.direction quarter last)).ordinate
    square targetInside

/-- Compare the two original cofactor Owners through the identical retained reference budget.

The actual queried Owner and the independently retained target Owner refine
the same original source box. Their exact physical endpoint identity reindexes
only the target parameter, and the original budget supplies both comparisons.
-/
def unit_owner_agrees_target (reading : Reading completed time inside)
    (target : Transport.Reading actual last lastInside)
    (point_eq : segment.pointAt time = (Parameter.sourcePoint site parameter (Waist.direction quarter last)).base) :
    NamedEquivalent (ownerRootName reading.unit.parameterNonzero reading.unit)
      (ownerRootName target.unit.parameterNonzero target.unit) := by
  have targetRefines : target.unit.track.initial.box.Refines actual.data.source.track.initial.box := by
    rewrite [target.unit_eq, SquareRoot.Owner.Transport.castOwnerParameter_initial_box]
    exact target.trace.refines
  have physical := segment.pointAt_contains within time inside
  have nonzero := budgets.unit_nonzero physical
  have movement := budgets.unit_movement physical
  rewrite [Norm.Basic.normSq_eq_canonical] at movement
  exact budgets.unit.retainedOwnersEquivalentOfEq
    (congrArg (fun point : Canonical => (unitPolynomial site).eval point) point_eq) nonzero movement
    reading.unit target.unit reading.unit_refines targetRefines

/-- The actual retained cofactor certificate agrees with the independent original target certificate.

The owner comparison consumes both original refinements and the same cached
budget. Exact certificate-name readbacks retain both complete caches without
reacquiring a target root or rebuilding either original preparation.
-/
def unit_agrees_target (reading : Reading completed time inside)
    (target : Transport.Reading actual last lastInside)
    (point_eq : segment.pointAt time = (Parameter.sourcePoint site parameter (Waist.direction quarter last)).base) :
    NamedEquivalent reading.values.unitRoot.value.name target.lift.unitRoot.value.name := by
  have queriedName : reading.values.unitRoot.value.name = ownerRootName reading.unit.parameterNonzero reading.unit := by
    rewrite [reading.values.unitRoot_eq]
    rfl
  exact NamedEquivalent.transport
    (first := ownerRootName reading.unit.parameterNonzero reading.unit)
    (second := ownerRootName target.unit.parameterNonzero target.unit)
    (left := reading.values.unitRoot.value.name) (right := target.lift.unitRoot.value.name)
    queriedName.symm target.lift.unitRoot_name.symm (reading.unit_owner_agrees_target target point_eq)

/-- The actual full product of retained physical factor queries agrees with the original target geometric Lift.value.

The normalized and cofactor comparisons are constructed from the actual
retained inputs. Original product congruence and complete value readbacks
preserve both full programs; no full-cubic path Owner is substituted for them.
-/
def agrees_target (reading : Reading completed time inside)
    (target : Transport.Reading actual last lastInside)
    (point_eq : segment.pointAt time = (Parameter.sourcePoint site parameter (Waist.direction quarter last)).base)
    (paid : (last - first) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 7) :
    NamedEquivalent reading.values.value.name target.lift.value.name := by
  rewrite [reading.values.value_eq, target.lift.value_eq]
  exact Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    reading.values.unitRoot.value target.lift.unitRoot.value reading.values.normalRoot.value
    (Coherence.exact (Parameter.sourcePoint site parameter (Waist.direction quarter last)).ordinate)
    (reading.unit_agrees_target target point_eq) (reading.normal_agrees_target point_eq paid)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading
