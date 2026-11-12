module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Coefficient.Allocation
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Stages
public import Purelib.Polynomial.Geometry.ClearPath.Width
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Bounds
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Joint fine observations at the original geometric request indices

Both request families are computed before observing the original factor
Owners. Each primary observation is selected after its separately retained
fine comparison. Original RequestedSamples consumes those same primary
observations and one paired product, preserving all geometric interfaces.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

namespace Reading.Payment

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside} {anchor : Parameter.Anchor source.lift}
variable {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {within : segment.WithinAmbient} {completed : Segment budgets segment within}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}
variable {differential : OddPowerDifferential (Paths.polynomial parameter)}
variable {data : Waist.Differential.Bounds.Data site parameter differential}

attribute [local irreducible] Purelib.Curves.Legendre.Degeneration.coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Coefficient.Bounds

set_option genInjectivity false in
/-- One before-observation fine schedule and the SAME actual primary observations at original geometric indices.

The original request and sample caches remain intact. Independent fine
requests and actual index orders strengthen the payment on those same
primary states; they do not relabel or replace an old observation.
-/
structure Fine (reading : Reading completed time inside) (bounds : Coefficient.Bounds data anchor)
    (target : AccuracyRequest) where
  /-- The original geometric interface, containing these newly acquired actual primary observations. -/
  selected : RequestedSamples (anchor := anchor) reading
  /-- The coefficient-computed common tolerance chosen before either factor observation. -/
  work : AccuracyRequest
  /-- The common request is the exact original allocation factory. -/
  work_eq : work = Coefficient.Allocation.request bounds target
  /-- The actual same-segment parameter-width request computed before either factor observation. -/
  width : AccuracyRequest
  /-- The width cache is the original geometric factory on this actual segment and work request. -/
  width_eq : width = segment.widthRequest work
  /-- The computed sufficient finite parameter depth for this same physical work request. -/
  minimum : Nat
  /-- The depth cache is the original finite geometric-search factory. -/
  minimum_eq : minimum = segment.widthMinimum work
  /-- The independently cached cofactor residual ceiling. -/
  unitLimit : AccuracyRequest
  /-- The cofactor ceiling pays both the common tolerance and original geometric cap. -/
  unitLimit_eq : unitLimit = work.minimum (unitResidual anchor)
  /-- The separately cached normalized residual ceiling. -/
  normalLimit : AccuracyRequest
  /-- The normalized ceiling pays both of its actual original demands. -/
  normalLimit_eq : normalLimit = work.minimum (normalResidual anchor)
  /-- The separately cached product-radius ceiling. -/
  outputLimit : AccuracyRequest
  /-- The product ceiling pays the common tolerance and original geometric output cap. -/
  outputLimit_eq : outputLimit = work.minimum (radiusOutput anchor)
  /-- The original common multiplication request and both actual fine residual/radius requests. -/
  requests : ProductRequests reading.values.unitRoot reading.values.normalRoot unitLimit normalLimit outputLimit
  /-- The complete fine request cache is the original constructor on the SAME two root certificates. -/
  requests_eq : requests = ProductRequests.build reading.values.unitRoot reading.values.normalRoot
    unitLimit normalLimit outputLimit
  /-- The original cofactor's fine observation and primary observation selected afterward. -/
  unit : JointRequest reading.values.unitRoot selected.requests.first requests.first
  /-- The entire cofactor joint cache is its original once-executed request factory. -/
  unit_eq : unit = requestJoint reading.values.unitRoot selected.requests.first requests.first
  /-- The selected geometric cofactor observation is exactly that primary observation, with all caches. -/
  unit_selected : unit.2.val = selected.samples.unit
  /-- The normalized root's separate fine and subsequent primary observations. -/
  normal : JointRequest reading.values.normalRoot selected.requests.last requests.last
  /-- The entire normalized joint cache is the original factory on its original certificate. -/
  normal_eq : normal = requestJoint reading.values.normalRoot selected.requests.last requests.last
  /-- The selected geometric normalized observation is exactly that separately retained primary observation. -/
  normal_selected : normal.2.val = selected.samples.normal

constructive_injectivity Fine

namespace Fine

/-- Compute every request first, acquire both original joint caches once, then retain their SAME primary product.

The builder does not consume an old unpaid RequestedSamples execution. Its
new primary observations retain their original geometric request indices;
the two extra paid observations and index orders remain stored separately.
-/
def build (reading : Reading completed time inside) (bounds : Coefficient.Bounds data anchor)
    (target : AccuracyRequest) : Fine reading bounds target := by
  let work := Coefficient.Allocation.request bounds target
  let width := segment.widthRequest work
  let minimum := Approximation.Rational.Geometric.Search.firstQuarterBelow 1 0 width.tolerance
  let unitLimit := work.minimum (unitResidual anchor)
  let normalLimit := work.minimum (normalResidual anchor)
  let outputLimit := work.minimum (radiusOutput anchor)
  let requests := ProductRequests.build reading.values.unitRoot reading.values.normalRoot
    unitLimit normalLimit outputLimit
  let primary := ProductRequests.build reading.values.unitRoot reading.values.normalRoot
    (unitResidual anchor) (normalResidual anchor) (radiusOutput anchor)
  let unit := requestJoint reading.values.unitRoot primary.first requests.first
  let normal := requestJoint reading.values.normalRoot primary.last requests.last
  let product := unit.2.val.productReading normal.2.val reading.values.value reading.values.value_eq
  let samples : Samples reading primary.first primary.last := ⟨unit.2.val, normal.2.val, ⟨product, rfl⟩⟩
  let selected := RequestedSamples.ofCompleted primary rfl samples
  exact ⟨selected, work, rfl, width, rfl, minimum, (segment.widthMinimum_eq work).symm,
    unitLimit, rfl, normalLimit, rfl, outputLimit, rfl, requests, rfl,
    unit, rfl, rfl, normal, rfl, rfl⟩

variable {reading : Reading completed time inside} {bounds : Coefficient.Bounds data anchor}
variable {target : AccuracyRequest} (fine : Fine reading bounds target)

/-- The actual later cofactor state follows its own retained fine comparison index. -/
theorem unit_after : fine.unit.1.comparison.leftIndex ≤ fine.selected.samples.unit.comparison.leftIndex := by
  have order := fine.unit.2.property
  rewrite [fine.unit_selected] at order
  exact order

/-- The actual later normalized state follows its separate retained fine comparison index. -/
theorem normal_after : fine.normal.1.comparison.leftIndex ≤ fine.selected.samples.normal.comparison.leftIndex := by
  have order := fine.normal.2.property
  rewrite [fine.normal_selected] at order
  exact order

/-- Every candidate of the SAME actual primary cofactor observation meets the computed common fine residual. -/
theorem unit_residual_lt {candidate : Canonical}
    (possible : fine.selected.samples.unit.observation.Possible candidate) :
    Norm.Basic.normSq (candidate * candidate - (unitPolynomial site).eval (segment.pointAt time)) <
      fine.work.tolerance := by
  have paid := fine.unit.1.residual_lt_after fine.selected.samples.unit fine.unit_after possible
  have limit := fine.requests.first_residual_lt
  have common : fine.unitLimit.tolerance ≤ fine.work.tolerance := by
    rewrite [fine.unitLimit_eq]
    exact fine.work.minimum_le_left _
  exact (paid.trans limit).trans_le common

/-- Every candidate of the SAME actual primary normalized observation meets its computed common fine residual. -/
theorem normal_residual_lt {candidate : Canonical}
    (possible : fine.selected.samples.normal.observation.Possible candidate) :
    Norm.Basic.normSq (candidate * candidate - Clearance.normalizedRadicand site parameter (segment.pointAt time)) <
      fine.work.tolerance := by
  have paid := fine.normal.1.residual_lt_after fine.selected.samples.normal fine.normal_after possible
  have limit := fine.requests.last_residual_lt
  have common : fine.normalLimit.tolerance ≤ fine.work.tolerance := by
    rewrite [fine.normalLimit_eq]
    exact fine.work.minimum_le_left _
  exact (paid.trans limit).trans_le common

/-- The literal primary product Reading pays the fine output target using both actual retained index orders. -/
theorem product_radius_lt : fine.selected.samples.product.radius < fine.work.tolerance := by
  have paid := fine.requests.product_radius_lt_after fine.unit.1 fine.normal.1
    fine.selected.samples.unit fine.selected.samples.normal fine.unit_after fine.normal_after
    reading.values.value reading.values.value_eq
  have common : fine.outputLimit.tolerance ≤ fine.work.tolerance := by
    rewrite [fine.outputLimit_eq]
    exact fine.work.minimum_le_left _
  rewrite [← fine.selected.samples.product_eq] at paid
  exact paid.trans_le common

/-- The SAME newly selected product keeps its complete original geometric radius payment as well. -/
theorem geometric_radius_lt : fine.selected.samples.product.radius < (radiusOutput anchor).tolerance :=
  fine.selected.product_radius_lt

/-- The coefficient-computed common request pays the chosen free target internally. -/
theorem work_payment : Coefficient.Allocation.cost bounds * fine.work.tolerance ≤ target.tolerance := by
  rewrite [fine.work_eq]
  exact Coefficient.Allocation.request_payment bounds target

/-- The SAME common request pays the original independent physical-displacement ceiling. -/
theorem work_spatial_le : fine.work.tolerance ≤ (spatialRequest anchor).tolerance := by
  rewrite [fine.work_eq]
  exact Coefficient.Allocation.request_spatial_le bounds target

/-- The SAME actual segment's displayed parameter width pays the computed common physical tolerance. -/
theorem distance_le_of_width {first last : Fraction.Rational}
    (paid : (first - last) ^ 2 ≤ fine.width.tolerance) :
    Norm.Basic.normSq (segment.pointAt first - segment.pointAt last) ≤ fine.work.tolerance :=
  segment.distance_le_of_width fine.work
    (Eq.mp (congrArg (fun width : AccuracyRequest => (first - last) ^ 2 ≤ width.tolerance) fine.width_eq) paid)

/-- A parameter cell at the SAME cached sufficient depth pays the actual common physical request. -/
theorem distance_le_of_depth {first last : Fraction.Rational}
    (paid : (first - last) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 fine.minimum) :
    Norm.Basic.normSq (segment.pointAt first - segment.pointAt last) ≤ fine.work.tolerance :=
  segment.distance_le_of_depth fine.work
    (Eq.mp (congrArg (fun depth : Nat =>
      (first - last) ^ 2 ≤ Approximation.Rational.Geometric.Basic.quarterRadius 1 depth) fine.minimum_eq) paid)

end Fine

end Reading.Payment

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment

end
