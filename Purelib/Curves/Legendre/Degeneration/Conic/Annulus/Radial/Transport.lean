module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Coordinates
public import Purelib.Riemann.RootContinuation.FixedRootBoxPath.Preparation.Reading
import Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Ordinate
import Purelib.Approximation.Gaussian.Name.Coherent.Transport
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.RootContinuation.SquareRootTrace
public import Purelib.Geometry.Rational.Affine.Segment
public import Purelib.Data.Gaussian.Norm.SquareResidual
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Name.Sampling
public import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
public import Purelib.Riemann.RootContinuation.SquareRootProvenance
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Actual original root traces on radial conic quarters

Every radial quarter uses the original conic point and cubic cofactor. A
retained reference owner and budget prepare actual finite accepted root moves;
requested-time readings reuse that exact preparation. The resulting original
cubic lifts are compared with the independent signed patch lifts internally.

These are time traces at a retained radial scale. A radial deformation trace,
primitive boundary, integral homotopy and canonical cut attachment are distinct
additional constructions.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic.Canonical (normSq)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
  (ownerRootName ownerRootName_castOwnerParameter)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.RootIsolation

/-- The exact original parameter-distance admission proposition for the radial family. -/
@[expose] def RadiusBound (site : Fin 2) (parameter : Canonical) : Prop :=
  Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)

/-- The exact original fixed-budget path type on one retained signed reference owner. -/
@[expose] def RootPath {site : Fin 2} (source : Owner (UnitRoot.seed site ^ 2))
    (budget : FixedRootBoxBudget.Budget source) : Type := FixedRootBoxPath.PathData budget budget

/-- The exact pointwise readback proposition of an original radial-quarter root path.

The named proposition retains the complete path and its original parameters
without expanding their dependent owners inside every record constructor.
-/
@[irreducible, expose] def PathReadback {site : Fin 2} {source : Owner (UnitRoot.seed site ^ 2)}
    {budget : FixedRootBoxBudget.Budget source} (path : FixedRootBoxPath.PathData budget budget)
    (parameter : Canonical) (scale : Fraction.Rational) (quarter : UnitCircuitQuarter) (positive : 0 < scale) : Prop :=
  ∀ time, path.point time = cofactor site parameter scale quarter positive time

set_option genInjectivity false in
/-- Original radial-quarter data retaining one full reference owner, its budget and the exact cubic-cofactor path. -/
structure Data (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational) (quarter : UnitCircuitQuarter)
    (positive : 0 < scale) where
  /-- The exact original lower radial admission certificate. -/ lower : 1 ≤ scale
  /-- The exact original upper radial admission certificate. -/ upper : scale ≤ 2
  /-- The exact original parameter-distance admission certificate. -/ bound : RadiusBound site parameter
  /-- The complete original signed reference owner cached once. -/ source : Owner (UnitRoot.seed site ^ 2)
  /-- The retained owner is the original signed cofactor reference. -/
  source_eq : source = UnitRoot.Transport.source site
  /-- The whole-quarter budget belongs to this exact original source. -/ budget : FixedRootBoxBudget.Budget source
  /-- The original spatial-patch movement allowance remains one half. -/ movement_eq : budget.movement = 1 / 2
  /-- The certified original radial-quarter cofactor path. -/ path : RootPath (site := site) source budget
  /-- Every retained path reading is the cofactor at the identical original conic point. -/
  points_eq : PathReadback (site := site) path parameter scale quarter positive

constructive_injectivity Data

namespace Data

/-- Read the exact original cubic cofactor at a requested parameter of the retained path. -/
theorem point_eq {site : Fin 2} {parameter : Canonical} {scale : Fraction.Rational} {quarter : UnitCircuitQuarter}
    {positive : 0 < scale} (data : Data site parameter scale quarter positive) (time : Fraction.Rational) :
    data.path.point time = cofactor site parameter scale quarter positive time := by
  have retained := data.points_eq
  unfold PathReadback at retained
  exact retained time

/-- Prepare exact radial-quarter path data using a supplied original cached reference and its retained budget.

Both path budgets use the identical input cache. Original annulus admission
pays nonvanishing and source movement; the actual ellipse estimate pays time
variation without introducing a polygon or a replacement sampler.
-/
def ofBudget (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational) (quarter : UnitCircuitQuarter)
    (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (source : Owner (UnitRoot.seed site ^ 2)) (source_eq : source = UnitRoot.Transport.source site)
    (budget : FixedRootBoxBudget.Budget source) (movement_eq : budget.movement = 1 / 2) :
    Data site parameter scale quarter positive := by
  have movement (time : Fraction.Rational) :
      (UnitRoot.seed site ^ 2 - cofactor site parameter scale quarter positive time).normSq ≤ budget.movement := by
    have result := UnitRoot.variation_bound site
      (point_inside site parameter scale (Waist.direction quarter time) positive lower upper bound)
    rewrite [Norm.Basic.normSq_eq_canonical] at result
    rewrite [movement_eq]
    exact result
  let path : FixedRootBoxPath.PathData budget budget :=
    { point := cofactor site parameter scale quarter positive
      nonzero := fun time _ => unit_ne_zero site
        (point_inside site parameter scale (Waist.direction quarter time) positive lower upper bound)
      firstMovement := fun time _ => movement time
      secondMovement := fun time _ => movement time
      scale := (25 / 4) * Norm.Basic.normSq (halfGap site parameter)
      scale_nonnegative := Arithmetic.mul_nonneg_direct
        (by decide +kernel) (Norm.Basic.normSq_nonneg _)
      variation := by
        intro left right _ _
        have result := cofactor_distance_le site parameter scale quarter positive lower upper left right
        rewrite [Norm.Basic.normSq_eq_canonical,
          show (left - right) ^ 2 = (right - left) ^ 2 by ring1] at result
        exact result }
  exact
    { lower := lower
      upper := upper
      bound := bound
      source := source
      source_eq := source_eq
      budget := budget
      movement_eq := movement_eq
      path := path
      points_eq := by unfold PathReadback; exact fun _ => rfl }

/-- Acquire one original reference and budget and construct its actual radial-quarter path data. -/
def build (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational) (quarter : UnitCircuitQuarter)
    (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    Data site parameter scale quarter positive :=
  let source := UnitRoot.Transport.source site
  let budget := FixedRootBoxBudget.Budget.acquire source (1 / 2) (by decide +kernel) (by
    rewrite [UnitRoot.Transport.source_bound]
    decide +kernel)
  ofBudget site parameter scale quarter positive lower upper bound source rfl budget rfl

end Data

set_option genInjectivity false in
/-- A complete original radial-quarter trace retaining its exact data and the actual accepted finite root moves. -/
structure Quarter (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational) (quarter : UnitCircuitQuarter)
    (positive : 0 < scale) where
  /-- The actual original reference, retained budget and exact cofactor path. -/
  data : Data site parameter scale quarter positive
  /-- The original accepted advances and shared midpoint caches on that identical path. -/
  prepared : FixedRootBoxPath.Preparation.Result data.path

constructive_injectivity Quarter

namespace Quarter

/-- Construct a complete actual root trace from the identical retained radial-quarter path data. -/
def ofData {site : Fin 2} {parameter : Canonical} {scale : Fraction.Rational} {quarter : UnitCircuitQuarter}
    {positive : 0 < scale} (data : Data site parameter scale quarter positive) :
    Quarter site parameter scale quarter positive :=
  { data := data
    prepared := FixedRootBoxPath.Preparation.Result.build data.path }

/-- Acquire the original radial-quarter data and construct actual accepted cofactor advances at computed depth. -/
def build (site : Fin 2) (parameter : Canonical) (scale : Fraction.Rational) (quarter : UnitCircuitQuarter)
    (positive : 0 < scale) (lower : 1 ≤ scale) (upper : scale ≤ 2)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    Quarter site parameter scale quarter positive :=
  ofData (Data.build site parameter scale quarter positive lower upper bound)

variable {site : Fin 2} {parameter : Canonical} {scale : Fraction.Rational} {quarter : UnitCircuitQuarter}
variable {positive : 0 < scale}

end Quarter

variable {site : Fin 2} {parameter : Canonical} {scale : Fraction.Rational} {quarter : UnitCircuitQuarter}
variable {positive : 0 < scale}

set_option genInjectivity false in
/-- One actual requested-time cubic reading retaining the original trace query and its full original lift.

The cofactor owner is only reindexed by the original path reading equation.
The lift is built from that same cached owner and acquires its complete root
certificate once; the independent signed patch remains a comparison input.
-/
structure Reading (actual : Quarter site parameter scale quarter positive)
    (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time) where
  /-- The exact query of the retained original prepared tree. -/
  trace : FixedRootBoxPath.Preparation.Reading actual.data.path time
  /-- The cached query is the original preparation's requested-time reading. -/
  trace_eq : trace = actual.prepared.read time inside
  /-- The complete original queried cofactor owner at the original conic base. -/
  unit : Owner ((unitPolynomial site).eval (point site parameter scale (Waist.direction quarter time) positive).base)
  /-- Only the exact original path-parameter equality reindexes the queried owner. -/
  unit_eq : unit = SquareRoot.Owner.Transport.castOwnerParameter (actual.data.point_eq time) trace.owner
  /-- The original cubic lift built from that identical cached cofactor owner. -/
  lift : Lift (point site parameter scale (Waist.direction quarter time) positive) unit

constructive_injectivity Reading

namespace Reading

variable {site : Fin 2} {parameter : Canonical} {scale : Fraction.Rational} {quarter : UnitCircuitQuarter}
variable {positive : 0 < scale}
variable {actual : Quarter site parameter scale quarter positive}
variable {time : Fraction.Rational} {inside : FixedRootBoxPath.Inside time}

/-- Query the retained actual trace once and construct its original cubic lift on that cached owner. -/
def build (actual : Quarter site parameter scale quarter positive)
    (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time) : Reading actual time inside :=
  let trace := actual.prepared.read time inside
  let unit := SquareRoot.Owner.Transport.castOwnerParameter (actual.data.point_eq time) trace.owner
  let lift := Lift.ofUnit (point site parameter scale (Waist.direction quarter time) positive) unit
  { trace := trace
    trace_eq := rfl
    unit := unit
    unit_eq := rfl
    lift := lift }

/-- Two readings at the same time on the same original prepared quarter retain the identical complete cofactor owner. -/
theorem unit_eq_other (left right : Reading actual time inside) : left.unit = right.unit := by
  rewrite [left.unit_eq, right.unit_eq, left.trace_eq, right.trace_eq]
  rfl

/-- Two actual readings of the same retained prepared-quarter query have identical whole numerical cubic channels.

Both original trace equations identify the same queried cofactor owner.
Each original lift's full root and product equations retain that owner's
actual certificate and exact conic ordinate, without replacing either
Reading or identifying independently chosen roots by scalar coincidence.
-/
theorem value_eq_other (left right : Reading actual time inside) : left.lift.value = right.lift.value := by
  have first : left.lift.value =
      (left.unit.certificate left.unit.parameterNonzero).value.mul
        (CoherentNamed.Coherence.exact
          (point site parameter scale (Waist.direction quarter time) positive).ordinate) := by
    rewrite [left.lift.value_eq, left.lift.unitRoot_eq, left.lift.unitOwner_eq]
    rfl
  have last : right.lift.value =
      (right.unit.certificate right.unit.parameterNonzero).value.mul
        (CoherentNamed.Coherence.exact
          (point site parameter scale (Waist.direction quarter time) positive).ordinate) := by
    rewrite [right.lift.value_eq, right.lift.unitRoot_eq, right.lift.unitOwner_eq]
    rfl
  exact first.trans ((congrArg (fun unit : Owner
    ((unitPolynomial site).eval (point site parameter scale (Waist.direction quarter time) positive).base) =>
      (unit.certificate unit.parameterNonzero).value.mul
        (CoherentNamed.Coherence.exact (point site parameter scale (Waist.direction quarter time) positive).ordinate))
    (left.unit_eq_other right)).trans last.symm)

/-- The queried original cubic lift retains the original selected signed cofactor window. -/
theorem signed (reading : Reading actual time inside) :
    reading.lift.unitOwner.track.initial.box.Refines (UnitRoot.box site) := by
  rewrite [reading.lift.unitOwner_eq, reading.unit_eq,
    SquareRoot.Owner.Transport.castOwnerParameter_initial_box]
  have originalBox : actual.data.source.track.initial.box = UnitRoot.box site := by
    rewrite [actual.data.source_eq, UnitRoot.Transport.source_box]
    rfl
  exact Eq.mp (congrArg (fun box => reading.trace.owner.track.initial.box.Refines box) originalBox)
    reading.trace.refines

/-- Convert a requested full-cubic square residual to an original cofactor residual request.

The exact original conic ordinate determines the positive sensitivity
factor. The supplied root channel, retained certificate and its original
numerical process are unchanged.
-/
@[expose] def productRequest (_reading : Reading actual time inside)
    (accuracy : AccuracyRequest) : AccuracyRequest :=
  ⟨accuracy.tolerance /
      (1 + Norm.Basic.normSq (point site parameter scale (Waist.direction quarter time) positive).ordinate ^ 2),
    Fraction.Order.Field.div_pos_direct accuracy.positive
      (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide +kernel)
        (Arithmetic.sq_nonneg_direct _))⟩

/-- Request one paid original cofactor observation sufficient for the original full-cubic square residual. -/
@[expose] def requestProduct (reading : Reading actual time inside) (accuracy : AccuracyRequest) :
    CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot (reading.productRequest accuracy) :=
  CertifiedSquareRoot.Sampling.request reading.lift.unitRoot (reading.productRequest accuracy)

/-- The actual product reading of a retained original cofactor observation and its exact original conic ordinate. -/
@[expose] def productReading (reading : Reading actual time inside) {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot accuracy) : Canonical :=
  sample.reading * (point site parameter scale (Waist.direction quarter time) positive).ordinate

/-- The original product-state transport retains the supplied cofactor state and exact-ordinate state literally. -/
@[expose] def productState (reading : Reading actual time inside) {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot accuracy) :
    reading.lift.value.name.process.State :=
  CoherentNamed.castState reading.lift.value_eq.symm
    ⟨sample.state, (CoherentNamed.Coherence.exact
      (point site parameter scale (Waist.direction quarter time) positive).ordinate).name.state⟩

/-- The displayed product reading is possible in the original full-cubic process at its transported state. -/
theorem productReading_possible (reading : Reading actual time inside) {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot accuracy) :
    reading.lift.value.name.process.Possible (reading.productState sample) (reading.productReading sample) :=
  reading.lift.product_possible sample.reading_possible

/-- Every supplied paid product observation keeps the original cofactor witness inside its original signed window. -/
theorem productReading_signed (reading : Reading actual time inside) {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot accuracy) :
    (UnitRoot.box site).Contains sample.reading :=
  reading.signed.contains (sample.reading_in_initial_box reading.lift.unitOwner reading.lift.unitRoot_eq)

/-- The full-cubic state consumes the identical actual cofactor-state radius and original exact ordinate factor. -/
theorem productState_radius (reading : Reading actual time inside) {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot accuracy) :
    (reading.lift.value.name.process.ball (reading.productState sample)).radiusSq =
      4 * (reading.lift.unitRoot.value.name.process.ball sample.state).radiusSq *
        Norm.Basic.normSq (point site parameter scale (Waist.direction quarter time) positive).ordinate :=
  reading.lift.product_radius sample.state

/-- The actual product reading pays the requested square residual of the original full cubic.

The exact conic factorization transfers the actual cached cofactor residual.
Its computed request pays the ordinate sensitivity without a new root
isolation, target comparison, or replacement numerical channel.
-/
theorem productReading_residual_lt (reading : Reading actual time inside) {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot
      (reading.productRequest accuracy)) :
    Norm.Basic.normSq (reading.productReading sample * reading.productReading sample -
      (Paths.polynomial parameter).eval
        (point site parameter scale (Waist.direction quarter time) positive).base) < accuracy.tolerance := by
  let ordinate := (point site parameter scale (Waist.direction quarter time) positive).ordinate
  let sensitivity := Norm.Basic.normSq ordinate ^ 2
  let request := reading.productRequest accuracy
  have requestPositive : 0 < request.tolerance := request.positive
  have residual := sample.reading_residual_lt.le
  have bound : Norm.Basic.normSq (reading.productReading sample * reading.productReading sample -
      (Paths.polynomial parameter).eval
        (point site parameter scale (Waist.direction quarter time) positive).base) ≤ request.tolerance * sensitivity :=
    ((point site parameter scale (Waist.direction quarter time) positive).product_residual sample.reading).trans_le
      (Arithmetic.mul_le_mul_of_nonneg_right_direct residual
        (Arithmetic.sq_nonneg_direct _))
  have factor : sensitivity < 1 + sensitivity := by
    exact (show sensitivity = 0 + sensitivity by ring1).trans_lt
      (Arithmetic.add_lt_add_right_direct (by decide +kernel) sensitivity)
  exact bound.trans_lt ((Arithmetic.mul_lt_mul_of_pos_left_direct requestPositive factor).trans_eq (by
    exact Fraction.Field.div_mul_cancel_of_ne accuracy.tolerance (1 + sensitivity)
      (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide +kernel)
        (Arithmetic.sq_nonneg_direct _)).ne'))

/-- The actual queried cofactor owner agrees with the independent original signed owner at the same conic point. -/
def unit_agrees (reading : Reading actual time inside) :
    NamedEquivalent (ownerRootName reading.unit.parameterNonzero reading.unit)
      (ownerRootName
        (UnitRoot.owner site (point site parameter scale (Waist.direction quarter time) positive).base
          (point_inside site parameter scale (Waist.direction quarter time) positive
            actual.data.lower actual.data.upper actual.data.bound)).parameterNonzero
        (UnitRoot.owner site (point site parameter scale (Waist.direction quarter time) positive).base
          (point_inside site parameter scale (Waist.direction quarter time) positive
            actual.data.lower actual.data.upper actual.data.bound))) := by
  let independent := UnitRoot.owner site (point site parameter scale (Waist.direction quarter time) positive).base
    (point_inside site parameter scale (Waist.direction quarter time) positive
      actual.data.lower actual.data.upper actual.data.bound)
  let atPath := SquareRoot.Owner.Transport.castOwnerParameter (actual.data.point_eq time).symm independent
  have refines : atPath.track.initial.box.Refines actual.data.source.track.initial.box := by
    rewrite [SquareRoot.Owner.Transport.castOwnerParameter_initial_box, UnitRoot.owner_initial_box,
      actual.data.source_eq, UnitRoot.Transport.source_box]
    exact Box.refines_refl _
  have canonical := actual.data.path.firstRetained time inside atPath refines
  have traced := reading.trace.agrees inside
  have compared := traced.trans canonical
  have retainedName := congrArg (fun owner => ownerRootName owner.parameterNonzero owner) reading.unit_eq
  exact NamedEquivalent.transport
    (retainedName.trans (ownerRootName_castOwnerParameter (actual.data.point_eq time) reading.trace.owner)).symm
    (ownerRootName_castOwnerParameter (actual.data.point_eq time).symm independent) compared

/-- The actual queried cubic channel agrees internally with the independent original signed radial lift. -/
def agrees (reading : Reading actual time inside) :
    NamedEquivalent reading.lift.value.name
      (Radial.lift site parameter scale (Waist.direction quarter time) positive
        actual.data.lower actual.data.upper actual.data.bound).value.name :=
  Lift.value_agrees reading.lift (Radial.lift site parameter scale (Waist.direction quarter time)
    positive actual.data.lower actual.data.upper actual.data.bound)
    (NamedEquivalent.transport reading.lift.unitRoot_name.symm
      (Radial.lift site parameter scale (Waist.direction quarter time) positive
        actual.data.lower actual.data.upper actual.data.bound).unitRoot_name.symm
      reading.unit_agrees)

/-- Prepare the identical actual parallel-circle cubic channel for division using its internally derived apartness. -/
def parallelPrepared {positive : (0 : Fraction.Rational) < 2}
    {actual : Quarter site parameter 2 quarter positive}
    (reading : Reading actual time inside) (regular : parameter ≠ criticalValue site) :
    Purelib.Approximation.Gaussian.Division.Prepared reading.lift.value :=
  Radial.parallelPrepared (Waist.direction quarter time) regular reading.lift

/-- An actual paid parallel product reading has the original uniform half-gap norm floor. -/
theorem parallel_productReading_lower {positive : (0 : Fraction.Rational) < 2}
    {actual : Quarter site parameter 2 quarter positive} {time : Fraction.Rational}
    {inside : FixedRootBoxPath.Inside time} (reading : Reading actual time inside)
    {accuracy : AccuracyRequest}
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation reading.lift.unitRoot
      (reading.productRequest accuracy)) :
    (9 / 64 : Fraction.Rational) * Norm.Basic.normSq (halfGap site parameter) ≤
      Norm.Basic.normSq (reading.productReading sample) :=
  Radial.parallel_product_lower site parameter quarter time (reading.productReading_signed sample)

/-- Two actual paid parallel product observations keep the same signed full-cubic sum floor on a short chart edge. -/
theorem parallel_productReading_sum_lower {positive : (0 : Fraction.Rational) < 2}
    {actual : Quarter site parameter 2 quarter positive} {first last : Fraction.Rational}
    {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
    (firstReading : Reading actual first firstInside) (lastReading : Reading actual last lastInside)
    {firstAccuracy lastAccuracy : AccuracyRequest}
    (firstSample : CertifiedSquareRoot.Sampling.ResidualObservation firstReading.lift.unitRoot
      (firstReading.productRequest firstAccuracy))
    (lastSample : CertifiedSquareRoot.Sampling.ResidualObservation lastReading.lift.unitRoot
      (lastReading.productRequest lastAccuracy))
    (paid : (first - last) ^ 2 ≤ (1 / Fraction.Cast.fromInt 16384 : Fraction.Rational)) :
    Norm.Basic.normSq (halfGap site parameter) / 4 ≤
      Norm.Basic.normSq (firstReading.productReading firstSample + lastReading.productReading lastSample) :=
  Radial.parallel_product_sum_lower site parameter quarter first last
    (firstReading.productReading_signed firstSample) (lastReading.productReading_signed lastSample) paid

/-- The uniform actual-product norm floor at the retained labelled regular parallel fibre. -/
@[expose] def traceFloor (_reading : Reading actual time inside) : Fraction.Rational :=
  (9 / 64) * Norm.Basic.normSq (halfGap site parameter)

/-- The signed actual-product sum floor on a paid original parallel chart edge. -/
@[expose] def traceSumFloor (_reading : Reading actual time inside) : Fraction.Rational :=
  Norm.Basic.normSq (halfGap site parameter) / 4

/-- Regularity makes both original full-product trace floors strictly positive. -/
theorem traceFloors_positive (reading : Reading actual time inside) (regular : parameter ≠ criticalValue site) :
    0 < reading.traceFloor ∧ 0 < reading.traceSumFloor := by
  have gap := Norm.Basic.normSq_pos (Polynomial.Quadratic.Split.halfGap_ne_zero
    (by decide +kernel : (2 : Canonical) ≠ 0) regular.symm)
  exact ⟨Arithmetic.mul_pos_direct (by decide +kernel) gap,
    Fraction.Order.Field.div_pos_direct gap (by decide +kernel)⟩

/-- The computed common residual and polynomial-movement request for original full-product trace edges. -/
@[expose] def traceRequest (reading : Reading actual time inside) (regular : parameter ≠ criticalValue site) :
    AccuracyRequest :=
  let floors := reading.traceFloors_positive regular
  ⟨min (reading.traceFloor ^ 2) (reading.traceFloor * reading.traceSumFloor) / Fraction.Cast.fromInt 16384,
    Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Basic.lt_min (Arithmetic.pow_pos_direct floors.1 2)
        (Arithmetic.mul_pos_direct floors.1 floors.2)) (by decide +kernel)⟩

/-- The computed time request pays the signed chart window and the actual retained polynomial-movement scale. -/
@[expose] def residualTimeRequest (_reading : Reading actual time inside) (request : AccuracyRequest)
    (movementScale : Fraction.Rational) (nonnegative : 0 ≤ movementScale) : AccuracyRequest :=
  ⟨min (1 / Fraction.Cast.fromInt 16384) (request.tolerance / (1 + movementScale)),
    Fraction.Order.Basic.lt_min (by decide +kernel)
      (Fraction.Order.Field.div_pos_direct request.positive
        (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide +kernel) nonnegative))⟩

/-- The computed time allowance never exceeds its original positive residual request.

The nonnegative movement scale gives a denominator at least one. The exact
original minimum and direct rational division bound retain the supplied
request without choosing a stage or a successful future comparison.
-/
theorem residualTimeRequest_le (reading : Reading actual time inside) (request : AccuracyRequest)
    (movementScale : Fraction.Rational) (nonnegative : 0 ≤ movementScale) :
    (reading.residualTimeRequest request movementScale nonnegative).tolerance ≤ request.tolerance := by
  have denominator : 1 ≤ 1 + movementScale := by
    have bounded := Arithmetic.add_le_add_direct
      (Fraction.Order.Basic.le_refl (1 : Fraction.Rational)) nonnegative
    exact (show (1 : Fraction.Rational) = 1 + 0 by ring1).trans_le bounded
  exact (Fraction.Order.Basic.min_le_right _ _).trans
    (Fraction.Order.Field.divide_le_self request.positive.le denominator)

/-- A paid actual chart width pays both the original signed window and the supplied full-polynomial residual request. -/
theorem residualTimeRequest_pays (reading : Reading actual time inside) (request : AccuracyRequest)
    (movementScale : Fraction.Rational) (nonnegative : 0 ≤ movementScale) (width : Fraction.Rational)
    (paid : width ^ 2 ≤ (reading.residualTimeRequest request movementScale nonnegative).tolerance) :
    width ^ 2 ≤ (1 / Fraction.Cast.fromInt 16384 : Fraction.Rational) ∧
      movementScale * width ^ 2 ≤ request.tolerance := by
  have positive : 0 < 1 + movementScale :=
    Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide +kernel) nonnegative
  have scaleLe : movementScale ≤ 1 + movementScale :=
    (show movementScale = 0 + movementScale by ring1).trans_le
      (Arithmetic.add_le_add_right_direct (by decide +kernel) movementScale)
  refine ⟨paid.trans (Fraction.Order.Basic.min_le_left _ _), ?_⟩
  calc
    _ ≤ (1 + movementScale) * width ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct scaleLe
        (Arithmetic.sq_nonneg_direct _)
    _ ≤ (1 + movementScale) * (request.tolerance / (1 + movementScale)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (paid.trans (Fraction.Order.Basic.min_le_right _ _)) positive.le
    _ = _ := (Fraction.Field.mul_comm _ _).trans (Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne')

/-- Strict finite time payment also pays the actual movement strictly, including zero movement scale. -/
theorem residualTimeRequest_pays_lt (reading : Reading actual time inside) (request : AccuracyRequest)
    (movementScale : Fraction.Rational) (nonnegative : 0 ≤ movementScale) (width : Fraction.Rational)
    (paid : width ^ 2 < (reading.residualTimeRequest request movementScale nonnegative).tolerance) :
    movementScale * width ^ 2 < request.tolerance := by
  have positive : 0 < 1 + movementScale :=
    Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide +kernel) nonnegative
  have scaleLe : movementScale ≤ 1 + movementScale :=
    (show movementScale = 0 + movementScale by ring1).trans_le
      (Arithmetic.add_le_add_right_direct (by decide +kernel) movementScale)
  calc
    _ ≤ (1 + movementScale) * width ^ 2 :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct scaleLe
        (Arithmetic.sq_nonneg_direct _)
    _ < (1 + movementScale) * (request.tolerance / (1 + movementScale)) :=
      Arithmetic.mul_lt_mul_of_pos_left_direct positive
        (paid.trans_le (Fraction.Order.Basic.min_le_right _ _))
    _ = _ := (Fraction.Field.mul_comm _ _).trans (Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne')

/-- Weakening the residual accuracy increases the same retained time allowance. -/
theorem residualTimeRequest_mono (reading : Reading actual time inside) (first last : AccuracyRequest)
    (order : first.tolerance ≤ last.tolerance) (movementScale : Fraction.Rational) (nonnegative : 0 ≤ movementScale) :
    (reading.residualTimeRequest first movementScale nonnegative).tolerance ≤
      (reading.residualTimeRequest last movementScale nonnegative).tolerance :=
  Fraction.Order.Basic.min_le_min (Fraction.Order.Basic.le_refl _)
    (Fraction.Order.Field.divide_mono order
      (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide +kernel) nonnegative))

/-- The original edge request is the same shared residual/time operation at its original computed accuracy. -/
@[expose] def traceTimeRequest (reading : Reading actual time inside) (regular : parameter ≠ criticalValue site)
    (movementScale : Fraction.Rational) (nonnegative : 0 ≤ movementScale) : AccuracyRequest :=
  reading.residualTimeRequest (reading.traceRequest regular) movementScale nonnegative

/-- The original trace request retains both original time and full-polynomial payments. -/
theorem traceTimeRequest_pays (reading : Reading actual time inside) (regular : parameter ≠ criticalValue site)
    (movementScale : Fraction.Rational) (nonnegative : 0 ≤ movementScale) (width : Fraction.Rational)
    (paid : width ^ 2 ≤ (reading.traceTimeRequest regular movementScale nonnegative).tolerance) :
    width ^ 2 ≤ (1 / Fraction.Cast.fromInt 16384 : Fraction.Rational) ∧
      movementScale * width ^ 2 ≤ (reading.traceRequest regular).tolerance :=
  reading.residualTimeRequest_pays (reading.traceRequest regular) movementScale nonnegative width paid

/-- Produce an actual original full-polynomial trace edge from two paid original cofactor observation caches.

The scalar request and time request are computed from the original retained
half-gap and polynomial movement scale. Both numerical samples remain
possible in their original cubic product channels. The proof constructs all
four rational Edge.Small conditions; no successful target comparison or
pre-existing owner trace is supplied. Optional exact product-cache views let
adjacent edges consume the same stored scalars; omitted views preserve the
original standalone computation.
-/
@[expose] def traceEdgeOfSamples {positive : (0 : Fraction.Rational) < 2}
    {actual : Quarter site parameter 2 quarter positive} {first last : Fraction.Rational}
    {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
    (firstReading : Reading actual first firstInside) (lastReading : Reading actual last lastInside)
    (regular : parameter ≠ criticalValue site) (movementScale : Fraction.Rational) (nonnegative : 0 ≤ movementScale)
    (movement : ∀ time : Fraction.Rational, 0 ≤ time ∧ time ≤ 1 →
      Norm.Basic.normSq ((Paths.polynomial parameter).eval
        (Geometry.Rational.Affine.line
          (point site parameter 2 (Waist.direction quarter first) positive).base
          ((point site parameter 2 (Waist.direction quarter last) positive).base -
            (point site parameter 2 (Waist.direction quarter first) positive).base) time) -
        (Paths.polynomial parameter).eval (point site parameter 2 (Waist.direction quarter first) positive).base) ≤
        movementScale * (first - last) ^ 2)
    (paid : (first - last) ^ 2 ≤
      (firstReading.traceTimeRequest regular movementScale nonnegative).tolerance)
    (firstSample : CertifiedSquareRoot.Sampling.ResidualObservation firstReading.lift.unitRoot
      (firstReading.productRequest (firstReading.traceRequest regular)))
    (lastSample : CertifiedSquareRoot.Sampling.ResidualObservation lastReading.lift.unitRoot
      (lastReading.productRequest (firstReading.traceRequest regular)))
    (firstProduct : {value : Canonical // value = firstReading.productReading firstSample} :=
      ⟨firstReading.productReading firstSample, rfl⟩)
    (lastProduct : {value : Canonical // value = lastReading.productReading lastSample} :=
      ⟨lastReading.productReading lastSample, rfl⟩) :
    SquareRootTrace.Edge (Paths.polynomial parameter) firstProduct.val lastProduct.val
      (point site parameter 2 (Waist.direction quarter first) positive).base
      (point site parameter 2 (Waist.direction quarter last) positive).base := by
  let polynomial := Paths.polynomial parameter
  let baseFirst := (point site parameter 2 (Waist.direction quarter first) positive).base
  let baseLast := (point site parameter 2 (Waist.direction quarter last) positive).base
  let firstValue := firstProduct.val
  let lastValue := lastProduct.val
  let lower := firstReading.traceFloor
  let sumLower := firstReading.traceSumFloor
  let request := firstReading.traceRequest regular
  have floors := firstReading.traceFloors_positive regular
  have payments := firstReading.traceTimeRequest_pays regular movementScale nonnegative (first - last) paid
  have normLower : lower ≤ Norm.Basic.normSq firstValue := by
    change lower ≤ Norm.Basic.normSq firstProduct.val
    rewrite [firstProduct.property]
    exact firstReading.parallel_productReading_lower firstSample
  have sumPaid : sumLower ≤ Norm.Basic.normSq (firstValue + lastValue) := by
    change sumLower ≤ Norm.Basic.normSq (firstProduct.val + lastProduct.val)
    rewrite [firstProduct.property, lastProduct.property]
    exact firstReading.parallel_productReading_sum_lower lastReading firstSample lastSample payments.1
  have firstResidual : Norm.Basic.normSq (firstValue * firstValue - polynomial.eval baseFirst) < request.tolerance := by
    change Norm.Basic.normSq (firstProduct.val * firstProduct.val - polynomial.eval baseFirst) < request.tolerance
    rewrite [firstProduct.property]
    exact firstReading.productReading_residual_lt firstSample
  have lastResidual : Norm.Basic.normSq (lastValue * lastValue - polynomial.eval baseLast) < request.tolerance := by
    change Norm.Basic.normSq (lastProduct.val * lastProduct.val - polynomial.eval baseLast) < request.tolerance
    rewrite [lastProduct.property]
    exact lastReading.productReading_residual_lt lastSample
  have endpoint := movement 1 (by constructor <;> decide +kernel)
  rewrite [Geometry.Rational.Affine.Segment.line_segment_one] at endpoint
  have parameterMovement : Norm.Basic.normSq (polynomial.eval baseFirst - polynomial.eval baseLast) ≤
      movementScale * (first - last) ^ 2 := by
    rewrite [Norm.Bounds.normSq_sub_symm]
    exact endpoint
  have distance := Norm.SquareResidual.distance_mul_le sumPaid firstResidual.le lastResidual.le parameterMovement
  have qSquare : request.tolerance ≤ lower ^ 2 / Fraction.Cast.fromInt 16384 :=
    Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Basic.min_le_left _ _) (by decide +kernel)
  have qProduct : request.tolerance ≤ lower * sumLower / Fraction.Cast.fromInt 16384 :=
    Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Basic.min_le_right _ _) (by decide +kernel)
  have relativeResidual : request.tolerance ≤ Norm.Basic.normSq firstValue ^ 2 / 1024 :=
    qSquare.trans ((Fraction.Order.Field.div_le_div_of_nonneg_left_direct
      (Arithmetic.sq_nonneg_direct _) (by decide +kernel : (0 : Fraction.Rational) < 1024)
      (by decide +kernel : (1024 : Fraction.Rational) ≤ Fraction.Cast.fromInt 16384)).trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Arithmetic.pow_le_pow_direct floors.1.le normLower 2) (by decide +kernel)))
  have distancePaid : Norm.Basic.normSq (firstValue - lastValue) ≤ lower / 1024 := by
    apply Arithmetic.le_of_mul_le_mul_right_direct (c := sumLower) _ floors.2
    calc
      _ ≤ 4 * (request.tolerance + request.tolerance) + 2 * (movementScale * (first - last) ^ 2) := distance
      _ ≤ 10 * request.tolerance :=
        (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
          (Arithmetic.mul_le_mul_of_nonneg_left_direct payments.2 (by decide +kernel))).trans_eq
            (by ring1)
      _ ≤ 10 * (lower * sumLower / Fraction.Cast.fromInt 16384) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct qProduct (by decide +kernel)
      _ = (10 / Fraction.Cast.fromInt 16384 : Fraction.Rational) * (lower * sumLower) := by
        simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1
      _ ≤ (1 / 1024 : Fraction.Rational) * (lower * sumLower) :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel)
          (Arithmetic.mul_nonneg_direct floors.1.le floors.2.le)
      _ = _ := by simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1
  let variation := SquareRootTrace.EdgeData.baseVariation polynomial baseFirst baseLast
  let data := SquareRootTrace.EdgeData.ofVariation polynomial firstValue lastValue baseFirst baseLast variation
    (SquareRootTrace.EdgeData.baseVariation_eval polynomial baseFirst baseLast)
    (movementScale * (first - last) ^ 2) (by
      intro time inside
      rewrite [SquareRootTrace.EdgeData.baseVariation_eval]
      have bounded := movement time inside
      rewrite [Norm.Basic.normSq_eq_canonical] at bounded
      exact bounded)
  refine ⟨data, ?_⟩
  change 0 < normSq firstValue ∧
    normSq (lastValue - firstValue) ≤ normSq firstValue / 1024 ∧
    normSq (firstValue ^ 2 - polynomial.eval baseFirst) ≤ normSq firstValue ^ 2 / 1024 ∧
    movementScale * (first - last) ^ 2 ≤ normSq firstValue ^ 2 / 1024
  refine ⟨?_, ?_, ?_, ?_⟩
  · rewrite [← Norm.Basic.normSq_eq_canonical]
    exact floors.1.trans_le normLower
  · rewrite [← Norm.Basic.normSq_eq_canonical, ← Norm.Basic.normSq_eq_canonical,
      Norm.Bounds.normSq_sub_symm]
    exact distancePaid.trans (Arithmetic.mul_le_mul_of_nonneg_right_direct normLower
      (by decide +kernel))
  · rewrite [← Norm.Basic.normSq_eq_canonical, ← Norm.Basic.normSq_eq_canonical, pow_two]
    exact firstResidual.le.trans relativeResidual
  · rewrite [← Norm.Basic.normSq_eq_canonical]
    exact payments.2.trans relativeResidual

/-- Every possible original full-product candidate has its cofactor in the retained signed window.

The witness is extracted only in this proposition. Its process state is the
original paired product state, and the complete original cofactor cache
identity supplies containment without reconstructing a root owner.
-/
theorem candidate_signed (reading : Reading actual time inside)
    {state : reading.lift.value.name.process.State} {candidate : Canonical}
    (possible : reading.lift.value.name.process.Possible state candidate) :
    ∃ cofactor : Canonical, (UnitRoot.box site).Contains cofactor ∧
      candidate = cofactor * (point site parameter scale (Waist.direction quarter time) positive).ordinate := by
  rcases reading.lift.candidate_factors possible with ⟨cofactor, cofactorPossible, equal⟩
  exact ⟨cofactor, reading.signed.contains
    (CertifiedSquareRoot.Sampling.candidate_in_initial_box reading.lift.unitOwner
      reading.lift.unitRoot_eq cofactorPossible), equal⟩

/-- Arbitrary actual candidate pairs retain the signed sum floor on a quantitatively short parallel chart edge. -/
theorem parallel_candidate_sum_lower {positive : (0 : Fraction.Rational) < 2}
    {actual : Quarter site parameter 2 quarter positive} {first last : Fraction.Rational}
    {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
    (firstReading : Reading actual first firstInside) (lastReading : Reading actual last lastInside)
    {firstState : firstReading.lift.value.name.process.State}
    {lastState : lastReading.lift.value.name.process.State} {firstValue lastValue : Canonical}
    (firstPossible : firstReading.lift.value.name.process.Possible firstState firstValue)
    (lastPossible : lastReading.lift.value.name.process.Possible lastState lastValue)
    (paid : (first - last) ^ 2 ≤ (1 / Fraction.Cast.fromInt 16384 : Fraction.Rational)) :
    firstReading.traceSumFloor ≤ Norm.Basic.normSq (firstValue + lastValue) := by
  rcases firstReading.candidate_signed firstPossible with ⟨firstRoot, firstSigned, firstEqual⟩
  rcases lastReading.candidate_signed lastPossible with ⟨lastRoot, lastSigned, lastEqual⟩
  rewrite [firstEqual, lastEqual]
  exact Radial.parallel_product_sum_lower site parameter quarter first last firstSigned lastSigned paid

/-- The computed square-residual accuracy for an actual cross-product distance request.

The signed sum floor scales the requested squared distance. Two residuals
and the original radicand movement consume at most ten sixteenths of this
request, leaving a strict margin before the requested distance.
-/
@[expose] def pairRequest (reading : Reading actual time inside) (regular : parameter ≠ criticalValue site)
    (distance : AccuracyRequest) : AccuracyRequest :=
  ⟨distance.tolerance * reading.traceSumFloor / 16,
    Fraction.Order.Field.div_pos_direct
      (Arithmetic.mul_pos_direct distance.positive (reading.traceFloors_positive regular).2)
      (by decide +kernel)⟩

/-- Original square comparisons pay an actual fixed-distance comparison of the two retained product names.

The independently requested starts and actual two square-residual comparison
indices are preserved. Quantitative time payment, both original signed
candidate windows and original full-polynomial movement supply the result;
no successful root comparison or target owner agreement is assumed.
-/
@[expose] def pairComparisonOfResiduals {positive : (0 : Fraction.Rational) < 2}
    {actual : Quarter site parameter 2 quarter positive} {first last : Fraction.Rational}
    {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
    (firstReading : Reading actual first firstInside) (lastReading : Reading actual last lastInside)
    (regular : parameter ≠ criticalValue site) (distance : AccuracyRequest)
    (movementScale : Fraction.Rational) (nonnegative : 0 ≤ movementScale)
    (movement : Norm.Basic.normSq ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) positive).base -
      (Paths.polynomial parameter).eval (point site parameter 2 (Waist.direction quarter last) positive).base) ≤
        movementScale * (first - last) ^ 2)
    (paid : (first - last) ^ 2 ≤
      (firstReading.residualTimeRequest (firstReading.pairRequest regular distance)
        movementScale nonnegative).tolerance)
    (firstStart lastStart : Nat)
    (firstResidual : Equivalence.Comparison
      (Sequence.Arithmetic.Product.sampledProductApproximation
        firstReading.lift.value.name firstReading.lift.value.name)
      (Name.Sampling.approximation (CoherentNamed.Coherence.exact ((Paths.polynomial parameter).eval
        (point site parameter 2 (Waist.direction quarter first) positive).base)).name)
      firstStart 0 (firstReading.pairRequest regular distance).tolerance)
    (lastResidual : Equivalence.Comparison
      (Sequence.Arithmetic.Product.sampledProductApproximation
        lastReading.lift.value.name lastReading.lift.value.name)
      (Name.Sampling.approximation (CoherentNamed.Coherence.exact ((Paths.polynomial parameter).eval
        (point site parameter 2 (Waist.direction quarter last) positive).base)).name)
      lastStart 0 (firstReading.pairRequest regular distance).tolerance) :
    Equivalence.Comparison (Name.Sampling.approximation firstReading.lift.value.name)
      (Name.Sampling.approximation lastReading.lift.value.name) firstStart lastStart distance.tolerance where
  leftIndex := firstResidual.leftIndex
  rightIndex := lastResidual.leftIndex
  left_ge := firstResidual.left_ge
  right_ge := lastResidual.left_ge
  close := by
    intro leftLater rightLater leftOrder rightOrder
    let firstValue := (Name.Sampling.approximation firstReading.lift.value.name).sample leftLater
    let lastValue := (Name.Sampling.approximation lastReading.lift.value.name).sample rightLater
    let request := firstReading.pairRequest regular distance
    have payments := firstReading.residualTimeRequest_pays request movementScale nonnegative (first - last) paid
    have sumLower : firstReading.traceSumFloor ≤ Norm.Basic.normSq (firstValue + lastValue) :=
      firstReading.parallel_candidate_sum_lower lastReading
        (Process.Sampling.witnessAt_possible _ _ leftLater)
        (Process.Sampling.witnessAt_possible _ _ rightLater) payments.1
    have firstBound := firstResidual.close leftOrder (Nat.le_refl firstResidual.rightIndex)
    have lastBound := lastResidual.close rightOrder (Nat.le_refl lastResidual.rightIndex)
    change Norm.Basic.normSq (firstValue * firstValue - (Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) positive).base) < request.tolerance at firstBound
    change Norm.Basic.normSq (lastValue * lastValue - (Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter last) positive).base) < request.tolerance at lastBound
    have estimate := Norm.SquareResidual.distance_mul_le sumLower firstBound.le lastBound.le movement
    apply Arithmetic.lt_of_mul_lt_mul_right_direct (c := firstReading.traceSumFloor) _
      (firstReading.traceFloors_positive regular).2
    calc
      _ ≤ 4 * (request.tolerance + request.tolerance) + 2 * (movementScale * (first - last) ^ 2) := estimate
      _ ≤ 10 * request.tolerance :=
        (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
          (Arithmetic.mul_le_mul_of_nonneg_left_direct payments.2 (by decide +kernel))).trans_eq
          (by ring1)
      _ = (10 / 16 : Fraction.Rational) * (distance.tolerance * firstReading.traceSumFloor) := by
        change 10 * (distance.tolerance * firstReading.traceSumFloor / 16) = _
        simp only [Fraction.Field.div_eq_mul_inv_direct]
        ring1
      _ < 1 * (distance.tolerance * firstReading.traceSumFloor) :=
        Arithmetic.mul_lt_mul_of_pos_right_direct (by decide +kernel)
          (Arithmetic.mul_pos_direct distance.positive (firstReading.traceFloors_positive regular).2)
      _ = _ := by ring1

/-- An exact cache view of both original full-product square-residual comparisons.

The two original Comparisons retain their original names, requested starts,
selected indices and every-future-tail bounds. Whole factory equalities bind
each retained value to the original square procedure at the computed request.
No new root or comparison certificate record is introduced.
-/
@[expose] def PairResiduals {positive : (0 : Fraction.Rational) < 2}
    {actual : Quarter site parameter 2 quarter positive} {first last : Fraction.Rational}
    {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
    (firstReading : Reading actual first firstInside) (lastReading : Reading actual last lastInside)
    (regular : parameter ≠ criticalValue site) (distance : AccuracyRequest) (firstStart lastStart : Nat) : Type :=
  let request := firstReading.pairRequest regular distance
  {retained : Equivalence.Comparison
      (Sequence.Arithmetic.Product.sampledProductApproximation
        firstReading.lift.value.name firstReading.lift.value.name)
      (Name.Sampling.approximation (CoherentNamed.Coherence.exact ((Paths.polynomial parameter).eval
        (point site parameter 2 (Waist.direction quarter first) positive).base)).name)
      firstStart 0 request.tolerance //
    retained = (SquareRootProvenance.sampled_square firstReading.lift.square).compare
      firstStart 0 request.tolerance request.positive} ×
  {retained : Equivalence.Comparison
      (Sequence.Arithmetic.Product.sampledProductApproximation
        lastReading.lift.value.name lastReading.lift.value.name)
      (Name.Sampling.approximation (CoherentNamed.Coherence.exact ((Paths.polynomial parameter).eval
        (point site parameter 2 (Waist.direction quarter last) positive).base)).name)
      lastStart 0 request.tolerance //
    retained = (SquareRootProvenance.sampled_square lastReading.lift.square).compare
      lastStart 0 request.tolerance request.positive}

namespace PairResiduals

variable {positive : (0 : Fraction.Rational) < 2} {actual : Quarter site parameter 2 quarter positive}
variable {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {lastInside : FixedRootBoxPath.Inside last}
variable {firstReading : Reading actual first firstInside} {lastReading : Reading actual last lastInside}
variable {regular : parameter ≠ criticalValue site} {distance : AccuracyRequest} {firstStart lastStart : Nat}

/-- Materialize the two actual original square comparisons once at the two supplied starts. -/
@[expose] def build (firstReading : Reading actual first firstInside) (lastReading : Reading actual last lastInside)
    (regular : parameter ≠ criticalValue site) (distance : AccuracyRequest) (firstStart lastStart : Nat) :
    PairResiduals firstReading lastReading regular distance firstStart lastStart :=
  let request := firstReading.pairRequest regular distance
  let first := (SquareRootProvenance.sampled_square firstReading.lift.square).compare
    firstStart 0 request.tolerance request.positive
  let last := (SquareRootProvenance.sampled_square lastReading.lift.square).compare
    lastStart 0 request.tolerance request.positive
  ⟨⟨first, rfl⟩, ⟨last, rfl⟩⟩

/-- Consume both retained original residual comparisons into the paid original raw-product Comparison.

This operation performs neither square comparison again. Its selected
indices and all-future bound use the two actual retained comparison caches.
-/
@[expose] def comparison (residuals : PairResiduals firstReading lastReading regular distance firstStart lastStart)
    (movementScale : Fraction.Rational) (nonnegative : 0 ≤ movementScale)
    (movement : Norm.Basic.normSq ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) positive).base -
      (Paths.polynomial parameter).eval (point site parameter 2 (Waist.direction quarter last) positive).base) ≤
        movementScale * (first - last) ^ 2)
    (paid : (first - last) ^ 2 ≤
      (firstReading.residualTimeRequest (firstReading.pairRequest regular distance)
        movementScale nonnegative).tolerance) :
    Equivalence.Comparison (Name.Sampling.approximation firstReading.lift.value.name)
      (Name.Sampling.approximation lastReading.lift.value.name) firstStart lastStart distance.tolerance :=
  firstReading.pairComparisonOfResiduals lastReading regular distance movementScale nonnegative movement paid
    firstStart lastStart residuals.1.val residuals.2.val

/-- The raw-product comparison uses the literal retained first square-comparison index. -/
theorem comparison_leftIndex
    (residuals : PairResiduals firstReading lastReading regular distance firstStart lastStart)
    (movementScale : Fraction.Rational) (nonnegative : 0 ≤ movementScale)
    (movement : Norm.Basic.normSq ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) positive).base -
      (Paths.polynomial parameter).eval (point site parameter 2 (Waist.direction quarter last) positive).base) ≤
        movementScale * (first - last) ^ 2)
    (paid : (first - last) ^ 2 ≤
      (firstReading.residualTimeRequest (firstReading.pairRequest regular distance)
        movementScale nonnegative).tolerance) :
    (residuals.comparison movementScale nonnegative movement paid).leftIndex = residuals.1.val.leftIndex := rfl

/-- The raw-product comparison uses the literal retained last square-comparison index. -/
theorem comparison_rightIndex
    (residuals : PairResiduals firstReading lastReading regular distance firstStart lastStart)
    (movementScale : Fraction.Rational) (nonnegative : 0 ≤ movementScale)
    (movement : Norm.Basic.normSq ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) positive).base -
      (Paths.polynomial parameter).eval (point site parameter 2 (Waist.direction quarter last) positive).base) ≤
        movementScale * (first - last) ^ 2)
    (paid : (first - last) ^ 2 ≤
      (firstReading.residualTimeRequest (firstReading.pairRequest regular distance)
        movementScale nonnegative).tolerance) :
    (residuals.comparison movementScale nonnegative movement paid).rightIndex = residuals.2.val.leftIndex := rfl

end PairResiduals

/-- The actual target-owner apartness supplies the finite signed product-distance request. -/
@[expose] def ownerDistance {point : Canonical} (target : Owner point) : AccuracyRequest :=
  ⟨(target.certificate target.parameterNonzero).apart.certificate.lowerSq / 64,
    Fraction.Order.Field.div_pos_direct (target.certificate target.parameterNonzero).apart.certificate.positive
      (by decide +kernel)⟩

/-- The exact retained signed source alignment and actual target-channel comparison.

The alignment consumes the original source agreement at the two retained
residual indices. Both original owners, the actual tolerance and comparison
factory identity remain indexed by their supplied original data.
-/
@[expose] def OwnerAgreement {positive : (0 : Fraction.Rational) < 2}
    {actual : Quarter site parameter 2 quarter positive} {first last : Fraction.Rational}
    {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
    (firstReading : Reading actual first firstInside) (lastReading : Reading actual last lastInside)
    (regular : parameter ≠ criticalValue site)
    (source : Owner ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) positive).base))
    (target : Owner ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter last) positive).base))
    (sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      firstReading.lift.value.name)
    {firstStart lastStart : Nat}
    (residuals : PairResiduals firstReading lastReading regular (ownerDistance target) firstStart lastStart) :
    Type :=
    Σ _alignment : {retained : Equivalence.Comparison
        (Name.Sampling.approximation (source.certificate source.parameterNonzero).value.name)
        (Name.Sampling.approximation firstReading.lift.value.name) 0 residuals.1.val.leftIndex
        (ownerDistance target).tolerance //
      retained = sourceAgreement.compare 0 residuals.1.val.leftIndex
        (ownerDistance target).tolerance (ownerDistance target).positive},
      NamedEquivalent (target.certificate target.parameterNonzero).value.name lastReading.lift.value.name

namespace OwnerAgreement

/-- Read the actual retained target-channel agreement without rebuilding its source alignment. -/
@[expose] def agrees {positive : (0 : Fraction.Rational) < 2}
    {actual : Quarter site parameter 2 quarter positive} {first last : Fraction.Rational}
    {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
    (firstReading : Reading actual first firstInside) (lastReading : Reading actual last lastInside)
    (regular : parameter ≠ criticalValue site)
    (source : Owner ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) positive).base))
    (target : Owner ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter last) positive).base))
    (sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      firstReading.lift.value.name)
    {firstStart lastStart : Nat}
    (residuals : PairResiduals firstReading lastReading regular (ownerDistance target) firstStart lastStart)
    (retained : OwnerAgreement firstReading lastReading regular source target sourceAgreement residuals) :
    NamedEquivalent (target.certificate target.parameterNonzero).value.name lastReading.lift.value.name :=
  retained.2

end OwnerAgreement

/-- Compare an actual continued full-cubic owner with the retained target product channel from computed bounds.

The actual source and target owners are inputs, with the original paid box
refinement and a fixed source-box diagonal payment. Two original retained
square comparisons derive the signed product-tail bound. One source alignment
then feeds the original two-tail root comparison; no target agreement,
caller-supplied successful comparison or replacement owner is used.
-/
@[expose] def ownerAgreementOfResiduals {positive : (0 : Fraction.Rational) < 2}
    {actual : Quarter site parameter 2 quarter positive} {first last : Fraction.Rational}
    {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
    (firstReading : Reading actual first firstInside) (lastReading : Reading actual last lastInside)
    (regular : parameter ≠ criticalValue site)
    (source : Owner ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) positive).base))
    (target : Owner ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter last) positive).base))
    (sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      firstReading.lift.value.name)
    (refines : target.track.initial.box.Refines source.track.initial.box)
    (small : source.track.initial.box.diagonalSq ≤
      (target.certificate target.parameterNonzero).apart.certificate.lowerSq / 16)
    (movementScale : Fraction.Rational) (nonnegative : 0 ≤ movementScale)
    (movement : Norm.Basic.normSq ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) positive).base -
      (Paths.polynomial parameter).eval (point site parameter 2 (Waist.direction quarter last) positive).base) ≤
        movementScale * (first - last) ^ 2)
    (paid : (first - last) ^ 2 ≤ (firstReading.residualTimeRequest
      (firstReading.pairRequest regular (ownerDistance target)) movementScale nonnegative).tolerance)
    (firstStart lastStart : Nat)
    (residuals : PairResiduals firstReading lastReading regular (ownerDistance target) firstStart lastStart) :
    OwnerAgreement firstReading lastReading regular source target sourceAgreement residuals := by
  let pair := residuals.comparison movementScale nonnegative movement paid
  exact SquareRootChannelOwnership.equivalent_in_refining_box source target
    firstReading.lift.value lastReading.lift.value sourceAgreement lastReading.lift.square
    pair.leftIndex pair.rightIndex refines small
    (fun firstIndex lastIndex firstOrder lastOrder => (by
      have retained := pair.close firstOrder lastOrder
      rewrite [Norm.Basic.normSq_eq_canonical] at retained
      exact retained.le))

end Reading

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport
