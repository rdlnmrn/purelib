module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport
import Purelib.Curves.Legendre.Degeneration.UnitRoot.Transport
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Bounds.Horner
public import Purelib.Integration.Path.Dyadic.DyadicSteps
import Purelib.Geometry.Rational.Box.Segment
public import Purelib.Geometry.Rational.Box.Hull
import Purelib.Geometry.Rational.Box.Point
import Purelib.Geometry.Rational.Affine.Segment
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# The original regular parallel circuit with actual continuous sheet owners

Four original scale-two rational conic quarters retain their prepared root
traces and actual cubic endpoint owners. Their operational seams and closure
are derived through the original independent signed lifts. All cubic channels
have internally prepared apart presentations, including the real-axis seams.

The sheet evidence consists of the actual transported root and cubic owners.
The branch switches of the scale-one waist are not part of this regular
circuit. Radial integral homotopy and canonical A/B cut attachment remain
additional geometric certificates.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.RootIsolation
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Bounds (Horner)
open Purelib.Approximation.Rational
open Purelib.Approximation (AccuracyRequest)
open Purelib.Integration.Path.Dyadic

set_option genInjectivity false in
/-- One regular original parallel quarter retaining the actual trace, endpoint lifts and prepared apart channels. -/
structure Leg (site : Fin 2) (parameter : Canonical) (quarter : UnitCircuitQuarter) where
  /-- The original regular-parameter certificate. -/ regular : parameter ≠ criticalValue site
  /-- The complete original scale-two quarter root trace. -/
  actual : Quarter site parameter 2 quarter (by decide +kernel)
  /-- The identical original source query and its cached full cubic lift. -/
  source : Reading actual 0 (by decide +kernel)
  /-- A division-ready presentation of that exact retained source cubic channel. -/
  sourcePrepared : Approximation.Gaussian.Division.Prepared source.lift.value
  /-- The identical actual advanced finish query and its cached full cubic lift. -/
  target : Reading actual 1 (by decide +kernel)
  /-- A division-ready presentation of that exact retained actual finish cubic channel. -/
  targetPrepared : Approximation.Gaussian.Division.Prepared target.lift.value

constructive_injectivity Leg

namespace Leg

/-- Cache both original endpoint queries and their apart presentations from the identical supplied actual quarter. -/
def ofQuarter {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    (regular : parameter ≠ criticalValue site) (actual : Quarter site parameter 2 quarter (by decide +kernel)) :
    Leg site parameter quarter :=
  let source := Reading.build actual 0 (by decide +kernel)
  let target := Reading.build actual 1 (by decide +kernel)
  { regular := regular
    actual := actual
    source := source
    sourcePrepared := source.parallelPrepared regular
    target := target
    targetPrepared := target.parallelPrepared regular }

/-- The retained source cofactor is precisely the original preparation's source, with only its exact index re-read. -/
theorem source_unit {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    (leg : Leg site parameter quarter) :
    leg.source.unit = RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter (leg.actual.data.point_eq 0)
      leg.actual.prepared.source := by
  rewrite [leg.source.unit_eq, leg.source.trace_eq, leg.actual.prepared.read_source]
  rfl

/-- The retained finish cofactor is precisely the actual advanced finish of the same original preparation. -/
theorem target_unit {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    (leg : Leg site parameter quarter) :
    leg.target.unit = RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter (leg.actual.data.point_eq 1)
      leg.actual.prepared.finishOwner := by
  rewrite [leg.target.unit_eq, leg.target.trace_eq, leg.actual.prepared.read_finish]
  rfl

/-- Read the same retained endpoint cache or query the identical original prepared quarter at an interior time.

The source and finish cases retain the complete original Reading objects.
Only equality of their original chart times reindexes these values; interior
queries consume the same actual prepared quarter and its retained root tree.
-/
def readingAt {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    (leg : Leg site parameter quarter) (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time) :
    Reading leg.actual time inside := by
  if zero : time = 0 then
    cases zero
    exact leg.source
  else if one : time = 1 then
    cases one
    exact leg.target
  else
    exact Reading.build leg.actual time inside

/-- A source-time request retains the identical complete original source Reading. -/
theorem readingAt_zero {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    (leg : Leg site parameter quarter) : leg.readingAt 0 (by decide +kernel) = leg.source := by
  unfold readingAt
  rewrite [dif_pos rfl]
  rfl

/-- A finish-time request retains the identical complete original target Reading. -/
theorem readingAt_one {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    (leg : Leg site parameter quarter) : leg.readingAt 1 (by decide +kernel) = leg.target := by
  unfold readingAt
  rewrite [dif_neg (by decide +kernel : (1 : Fraction.Rational) ≠ 0), dif_pos rfl]
  rfl

/-- A time equal to one reads the identical complete original finish cache with only its time index transported. -/
theorem readingAt_of_one {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    (leg : Leg site parameter quarter) (time : Fraction.Rational) (inside : FixedRootBoxPath.Inside time)
    (equal : time = 1) : HEq (leg.readingAt time inside) leg.target := by
  cases equal
  exact heq_of_eq leg.readingAt_one

/-- The actual retained polynomial Horner cache pays this original quarter's affine-base movement scale. -/
@[expose] def traceMovement {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    (_leg : Leg site parameter quarter) (bounds : Horner) : Fraction.Rational :=
  bounds.slope * ((25 / 4) * Norm.Basic.normSq (halfGap site parameter))

/-- The exact original polynomial Horner cache gives a nonnegative full-polynomial movement scale. -/
theorem traceMovement_nonnegative {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    (leg : Leg site parameter quarter) (bounds : Horner)
    (retained : bounds = Bounds.Box.denseHornerNormBounds (Paths.polynomial parameter) (spatialBox site)) :
    0 ≤ leg.traceMovement bounds := by
  have nonnegative := (Bounds.Box.denseHornerNormBounds_nonneg (Paths.polynomial parameter) (spatialBox site)).2
  change 0 ≤ (Bounds.Box.denseHornerNormBounds (Paths.polynomial parameter) (spatialBox site)).slope at nonnegative
  rewrite [← retained] at nonnegative
  exact Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _))

/-- A stronger residual request on the identical original Leg edge contract. -/
@[expose] def TraceAccuracy {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    (leg : Leg site parameter quarter) : Type :=
  {request : AccuracyRequest // request.tolerance ≤ (leg.source.traceRequest leg.regular).tolerance}

/-- An exact cache view of the original polynomial fold and its original bounded geometric search.

The original Horner cache is computed once. The Selection retains the actual
quotient, ceiling, finite fuel, returned stage, attained allowance and strict
payment for the original product-trace request. No successful root comparison
or independently supplied owner trace occurs in this view.
-/
@[expose] def TraceBudget {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    (leg : Leg site parameter quarter)
    (accuracy : TraceAccuracy leg := ⟨leg.source.traceRequest leg.regular, Fraction.Order.Basic.le_refl _⟩) : Type :=
  Σ bounds : {retained : Horner //
      retained = Bounds.Box.denseHornerNormBounds (Paths.polynomial parameter) (spatialBox site)},
    Geometric.Search.Selection 1 7
      (leg.source.residualTimeRequest accuracy.val (leg.traceMovement bounds.val)
        (leg.traceMovement_nonnegative bounds.val bounds.property)).tolerance

namespace TraceBudget

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter} {leg : Leg site parameter quarter}
variable {accuracy : TraceAccuracy leg}

/-- Consume the retained original whole Horner cache and compute one selection at the actual stronger request. -/
@[expose] def ofBounds (leg : Leg site parameter quarter)
    (bounds : Horner)
    (bounds_eq : bounds = Bounds.Box.denseHornerNormBounds (Paths.polynomial parameter) (spatialBox site))
    (accuracy : TraceAccuracy leg) : TraceBudget leg accuracy :=
  let request := leg.source.residualTimeRequest accuracy.val (leg.traceMovement bounds)
    (leg.traceMovement_nonnegative bounds bounds_eq)
  ⟨⟨bounds, bounds_eq⟩, Geometric.Search.Selection.build 1 (by decide +kernel) 7 request.tolerance request.positive⟩

/-- Compute the original polynomial fold once and retain its selection at the supplied actual residual request. -/
@[expose] def build (leg : Leg site parameter quarter)
    (accuracy : TraceAccuracy leg := ⟨leg.source.traceRequest leg.regular, Fraction.Order.Basic.le_refl _⟩) :
    TraceBudget leg accuracy :=
  let bounds := Bounds.Box.denseHornerNormBounds (Paths.polynomial parameter) (spatialBox site)
  ofBounds leg bounds rfl accuracy

/-- Read the identical complete original polynomial Horner cache retained by this trace budget. -/
@[expose] def bounds (budget : TraceBudget leg accuracy) : Horner := budget.1.val

/-- A retained-cache factory keeps the identical complete supplied Horner value. -/
theorem ofBounds_bounds (leg : Leg site parameter quarter) (bounds : Horner)
    (bounds_eq : bounds = Bounds.Box.denseHornerNormBounds (Paths.polynomial parameter) (spatialBox site))
    (accuracy : TraceAccuracy leg) : (ofBounds leg bounds bounds_eq accuracy).bounds = bounds := rfl

/-- The retained complete cache is the original polynomial fold at the original labelled spatial patch. -/
theorem bounds_eq (budget : TraceBudget leg accuracy) : budget.bounds =
    Bounds.Box.denseHornerNormBounds (Paths.polynomial parameter) (spatialBox site) := budget.1.property

/-- Read the actual original finite search and every retained request/payment field without repeating it. -/
@[expose] def selection (budget : TraceBudget leg accuracy) : Geometric.Search.Selection 1 7
    (leg.source.residualTimeRequest accuracy.val (leg.traceMovement budget.bounds)
      (leg.traceMovement_nonnegative budget.bounds budget.bounds_eq)).tolerance := budget.2

/-- The internally selected trace depth is bounded by the actual retained finite fuel. -/
theorem depth_le (budget : TraceBudget leg accuracy) : budget.selection.stage ≤ 7 + budget.selection.fuel :=
  budget.selection.upper

/-- Every actual adjacent edge of the selected original dyadic mesh strictly pays the computed trace-time request. -/
theorem edge_paid_lt (budget : TraceBudget leg accuracy)
    (edge : Fin (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1).length) :
    (DyadicTrace.indexed 0 (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) edge.castSucc -
      DyadicTrace.indexed 0 (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) edge.succ) ^ 2 <
      (leg.source.residualTimeRequest accuracy.val (leg.traceMovement budget.bounds)
        (leg.traceMovement_nonnegative budget.bounds budget.bounds_eq)).tolerance := by
  have width := (DyadicSteps.tail_steps budget.selection.stage (0 : Fraction.Rational) 1).width_square edge
  calc
    _ = (DyadicTrace.indexed 0 (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) edge.succ -
        DyadicTrace.indexed 0
          (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) edge.castSucc) ^ 2 := by
      ring1
    _ = Geometric.Basic.quarterRadius 1 budget.selection.stage * ((1 : Fraction.Rational) - 0) ^ 2 := width
    _ = Geometric.Basic.quarterRadius 1 budget.selection.stage := by ring1
    _ < _ := budget.selection.later_accurate (Nat.le_refl _)

/-- Every actual adjacent edge also satisfies the original weak trace-time payment contract. -/
theorem edge_paid (budget : TraceBudget leg accuracy)
    (edge : Fin (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1).length) :
    (DyadicTrace.indexed 0 (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) edge.castSucc -
      DyadicTrace.indexed 0 (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) edge.succ) ^ 2 ≤
      (leg.source.residualTimeRequest accuracy.val (leg.traceMovement budget.bounds)
        (leg.traceMovement_nonnegative budget.bounds budget.bounds_eq)).tolerance :=
  (budget.edge_paid_lt edge).le

/-- Every actual adjacent polynomial movement strictly fits the requested residual allowance. -/
theorem movement_paid_lt (budget : TraceBudget leg accuracy)
    (edge : Fin (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1).length) :
    leg.traceMovement budget.bounds *
      (DyadicTrace.indexed 0 (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) edge.castSucc -
        DyadicTrace.indexed 0 (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) edge.succ) ^ 2 <
      accuracy.val.tolerance :=
  leg.source.residualTimeRequest_pays_lt accuracy.val (leg.traceMovement budget.bounds)
    (leg.traceMovement_nonnegative budget.bounds budget.bounds_eq) _ (budget.edge_paid_lt edge)

/-- Every selected stronger edge also pays the original complete Edge construction. -/
theorem edge_paid_trace (budget : TraceBudget leg accuracy)
    (edge : Fin (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1).length) :
    (DyadicTrace.indexed 0 (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) edge.castSucc -
      DyadicTrace.indexed 0 (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1) edge.succ) ^ 2 ≤
      (leg.source.traceTimeRequest leg.regular (leg.traceMovement budget.bounds)
        (leg.traceMovement_nonnegative budget.bounds budget.bounds_eq)).tolerance :=
  (budget.edge_paid edge).trans (leg.source.residualTimeRequest_mono accuracy.val
    (leg.source.traceRequest leg.regular) accuracy.property (leg.traceMovement budget.bounds)
    (leg.traceMovement_nonnegative budget.bounds budget.bounds_eq))

/-- The same retained polynomial fold controls every affine spatial chord between two original chart points. -/
theorem movement (budget : TraceBudget leg accuracy) (first last time : Fraction.Rational)
    (inside : 0 ≤ time ∧ time ≤ 1) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval
      (Geometry.Rational.Affine.line
        (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base
        ((point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).base -
          (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base) time) -
      (Paths.polynomial parameter).eval
        (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base) ≤
      leg.traceMovement budget.bounds * (first - last) ^ 2 := by
  have firstInside := point_inside site parameter 2 (Waist.direction quarter first) (by decide +kernel)
    leg.actual.data.lower leg.actual.data.upper leg.actual.data.bound
  have lastInside := point_inside site parameter 2 (Waist.direction quarter last) (by decide +kernel)
    leg.actual.data.lower leg.actual.data.upper leg.actual.data.bound
  have chordInside := Geometry.Rational.Box.contains_line firstInside lastInside inside
  have polynomialBound := Bounds.Box.normSq_eval_sub_eval_le (Paths.polynomial parameter) chordInside firstInside
  have scaleEq : Bounds.Box.denseEvalNormLipschitzBound (Paths.polynomial parameter) (spatialBox site) =
      budget.bounds.slope := congrArg Horner.slope budget.bounds_eq.symm
  rewrite [scaleEq] at polynomialBound
  have chordBound := Geometry.Rational.Affine.Segment.normSq_source_sub_line_le
    (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base
    (point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).base inside
  have baseBound := quarter_base_distance_le site parameter 2 quarter (by decide +kernel)
    leg.actual.data.lower leg.actual.data.upper first last
  have slopeNonnegative := (Bounds.Box.denseHornerNormBounds_nonneg
    (Paths.polynomial parameter) (spatialBox site)).2
  change 0 ≤ (Bounds.Box.denseHornerNormBounds (Paths.polynomial parameter) (spatialBox site)).slope at slopeNonnegative
  rewrite [← budget.bounds_eq] at slopeNonnegative
  have ordered : Norm.Basic.normSq
      (Geometry.Rational.Affine.line
        (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base
        ((point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).base -
          (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base) time -
        (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base) ≤
      (25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2 := by
    rewrite [Norm.Bounds.normSq_sub_symm]
    exact chordBound.trans baseBound
  exact polynomialBound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ordered
    slopeNonnegative).trans_eq (by unfold traceMovement; ring1))

/-- The same retained Horner cache bounds polynomial movement throughout the exact endpoint rectangle.

The original endpoint point boxes determine a possibly degenerate hull.
Its diagonal is the actual endpoint distance, so the quarter's intrinsic
base-distance estimate controls every contained point, not only the chord.
-/
theorem movement_inBox (budget : TraceBudget leg accuracy) (first last : Fraction.Rational)
    (value : Canonical)
    (inside : (Box.Hull.hull
      (Box.Point.pointBox
        (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base)
      (Box.Point.pointBox
        (point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).base)).Contains value) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval value -
      (Paths.polynomial parameter).eval
        (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base) ≤
      leg.traceMovement budget.bounds * (first - last) ^ 2 := by
  have firstInside := point_inside site parameter 2 (Waist.direction quarter first) (by decide +kernel)
    leg.actual.data.lower leg.actual.data.upper leg.actual.data.bound
  have lastInside := point_inside site parameter 2 (Waist.direction quarter last) (by decide +kernel)
    leg.actual.data.lower leg.actual.data.upper leg.actual.data.bound
  have hullRefines := Box.Hull.refines
    (left := Box.Point.pointBox
      (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base)
    (right := Box.Point.pointBox
      (point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).base)
    (outer := spatialBox site) firstInside lastInside
  have polynomialBound := Bounds.Box.normSq_eval_sub_eval_le (Paths.polynomial parameter)
    (hullRefines.contains inside) firstInside
  have scaleEq : Bounds.Box.denseEvalNormLipschitzBound (Paths.polynomial parameter) (spatialBox site) =
      budget.bounds.slope := congrArg Horner.slope budget.bounds_eq.symm
  rewrite [scaleEq] at polynomialBound
  have displacement := Box.normSq_sub_le_diagonalSq inside
    (Box.Hull.hull_contains_left (Box.Point.pointBox_contains
      (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base))
  rewrite [Box.Hull.pointBoxes_diagonalSq,
    Norm.Bounds.normSq_sub_symm
      (point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).base
      (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base] at displacement
  have baseBound := quarter_base_distance_le site parameter 2 quarter (by decide +kernel)
    leg.actual.data.lower leg.actual.data.upper first last
  have slopeNonnegative := (Bounds.Box.denseHornerNormBounds_nonneg
    (Paths.polynomial parameter) (spatialBox site)).2
  change 0 ≤ (Bounds.Box.denseHornerNormBounds (Paths.polynomial parameter) (spatialBox site)).slope at slopeNonnegative
  rewrite [← budget.bounds_eq] at slopeNonnegative
  exact polynomialBound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (displacement.trans baseBound) slopeNonnegative).trans_eq (by unfold traceMovement; ring1))

/-- The same original retained movement bound pays the exact two chart endpoints. -/
theorem movement_endpoints (budget : TraceBudget leg accuracy) (first last : Fraction.Rational) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval
        (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base -
      (Paths.polynomial parameter).eval
        (point site parameter 2 (Waist.direction quarter last) (by decide +kernel)).base) ≤
      leg.traceMovement budget.bounds * (first - last) ^ 2 := by
  have retained := budget.movement first last 1 (by constructor <;> decide +kernel)
  rewrite [Geometry.Rational.Affine.line_one, Norm.Bounds.normSq_sub_symm] at retained
  exact retained

end TraceBudget

/-- Construct an actual full-cubic trace edge at any bounded edge of the internally paid original Leg mesh.

Both original Leg readings are selected by their true dyadic positions,
using the original cached endpoint queries at zero and one. Their original
cofactor observations are requested once each and retained with the exact
computed full-product Edge. No target identification or owner trace is an
input. Adjacent-edge sample sharing and full OwnerPath assembly remain
separate operations.
-/
@[expose] def traceEdgeAt {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
    (leg : Leg site parameter quarter) {accuracy : TraceAccuracy leg} (budget : TraceBudget leg accuracy)
    (edge : Fin (DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1).length) :
    let times := DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1
    let first := leg.readingAt (DyadicTrace.indexed 0 times edge.castSucc)
      (DyadicTrace.indexed_inside budget.selection.stage (by decide +kernel) edge.castSucc)
    let last := leg.readingAt (DyadicTrace.indexed 0 times edge.succ)
      (DyadicTrace.indexed_inside budget.selection.stage (by decide +kernel) edge.succ)
    Σ firstSample : CertifiedSquareRoot.Sampling.ResidualObservation first.lift.unitRoot
        (first.productRequest (first.traceRequest leg.regular)),
      Σ lastSample : CertifiedSquareRoot.Sampling.ResidualObservation last.lift.unitRoot
          (last.productRequest (first.traceRequest leg.regular)),
        SquareRootTrace.Edge (Paths.polynomial parameter)
          (first.productReading firstSample) (last.productReading lastSample)
          (point site parameter 2 (Waist.direction quarter (DyadicTrace.indexed 0 times edge.castSucc))
            (by decide +kernel)).base
          (point site parameter 2 (Waist.direction quarter (DyadicTrace.indexed 0 times edge.succ))
            (by decide +kernel)).base :=
  let times := DyadicTrace.tail budget.selection.stage (0 : Fraction.Rational) 1
  let first := leg.readingAt (DyadicTrace.indexed 0 times edge.castSucc)
    (DyadicTrace.indexed_inside budget.selection.stage (by decide +kernel) edge.castSucc)
  let last := leg.readingAt (DyadicTrace.indexed 0 times edge.succ)
    (DyadicTrace.indexed_inside budget.selection.stage (by decide +kernel) edge.succ)
  let firstSample := first.requestProduct (first.traceRequest leg.regular)
  let lastSample := last.requestProduct (first.traceRequest leg.regular)
  ⟨firstSample, ⟨lastSample, first.traceEdgeOfSamples last leg.regular (leg.traceMovement budget.bounds)
    (leg.traceMovement_nonnegative budget.bounds budget.bounds_eq)
    (budget.movement _ _) (budget.edge_paid_trace edge) firstSample lastSample⟩⟩

end Leg

/-- The exact original operational cubic comparison between two retained parallel-quarter endpoint owners. -/
@[irreducible, expose] def Seam {site : Fin 2} {parameter : Canonical} {firstQuarter lastQuarter : UnitCircuitQuarter}
    (first : Leg site parameter firstQuarter) (last : Leg site parameter lastQuarter) : Type :=
  NamedEquivalent first.target.lift.value.name last.source.lift.value.name

set_option genInjectivity false in
/-- The four original regular parallel quarters in geometric order with internally derived continuous cubic seams. -/
structure Circuit (site : Fin 2) (parameter : Canonical) where
  /-- The original retained first quarter. -/ first : Leg site parameter .first
  /-- The original retained second quarter. -/ second : Leg site parameter .second
  /-- The original retained third quarter. -/ third : Leg site parameter .third
  /-- The original retained fourth quarter. -/ fourth : Leg site parameter .fourth
  /-- Actual first finish and second source agree at the same regular seam. -/ first_second : Seam first second
  /-- Actual second finish and third source agree at the same regular seam. -/ second_third : Seam second third
  /-- Actual third finish and fourth source agree at the same regular seam. -/ third_fourth : Seam third fourth
  /-- Actual fourth finish and first source agree on the same regular closure. -/ fourth_first : Seam fourth first

constructive_injectivity Circuit

namespace Circuit

/-- Assemble actual original quarter traces and derive every cubic seam and the closure internally. -/
def ofQuarters {site : Fin 2} {parameter : Canonical} (regular : parameter ≠ criticalValue site)
    (firstQuarter : Quarter site parameter 2 .first (by decide +kernel))
    (secondQuarter : Quarter site parameter 2 .second (by decide +kernel))
    (thirdQuarter : Quarter site parameter 2 .third (by decide +kernel))
    (fourthQuarter : Quarter site parameter 2 .fourth (by decide +kernel)) : Circuit site parameter := by
  let first := Leg.ofQuarter regular firstQuarter
  let second := Leg.ofQuarter regular secondQuarter
  let third := Leg.ofQuarter regular thirdQuarter
  let fourth := Leg.ofQuarter regular fourthQuarter
  have join {firstQuarter lastQuarter : UnitCircuitQuarter}
      (first : Leg site parameter firstQuarter) (last : Leg site parameter lastQuarter)
      (equal : Waist.direction firstQuarter 1 = Waist.direction lastQuarter 0) : Seam first last := by
    unfold Seam
    have values := congrArg (fun direction =>
      (Radial.lift site parameter 2 direction (by decide +kernel)
        first.actual.data.lower first.actual.data.upper first.actual.data.bound).value) equal
    exact first.target.agrees.trans
      (NamedEquivalent.transport (congrArg (fun value => value.name) values).symm rfl last.source.agrees.symm)
  exact
    { first := first
      second := second
      third := third
      fourth := fourth
      first_second := join first second Waist.directions_join.1
      second_third := join second third Waist.directions_join.2.1
      third_fourth := join third fourth Waist.directions_join.2.2.1
      fourth_first := join fourth first Waist.directions_join.2.2.2 }

/-- Construct all four actual quarter traces using the identical supplied original reference and budget caches.

The same retained source and budget are passed to each original path builder.
Each resulting preparation keeps its own actual accepted moves and endpoint
owners; their comparisons derive the circuit without re-isolating roots.
-/
def ofBudget (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational))
    (source : Owner (UnitRoot.seed site ^ 2)) (source_eq : source = UnitRoot.Transport.source site)
    (budget : FixedRootBoxBudget.Budget source) (movement_eq : budget.movement = 1 / 2) : Circuit site parameter :=
  let first := Quarter.ofData (Data.ofBudget site parameter 2 .first (by decide +kernel)
    (by decide +kernel) (by decide +kernel) bound source source_eq budget movement_eq)
  let second := Quarter.ofData (Data.ofBudget site parameter 2 .second (by decide +kernel)
    (by decide +kernel) (by decide +kernel) bound source source_eq budget movement_eq)
  let third := Quarter.ofData (Data.ofBudget site parameter 2 .third (by decide +kernel)
    (by decide +kernel) (by decide +kernel) bound source source_eq budget movement_eq)
  let fourth := Quarter.ofData (Data.ofBudget site parameter 2 .fourth (by decide +kernel)
    (by decide +kernel) (by decide +kernel) bound source source_eq budget movement_eq)
  ofQuarters regular first second third fourth

/-- Acquire one original reference and budget and construct the full regular parallel circuit with actual seams. -/
def build (site : Fin 2) (parameter : Canonical) (regular : parameter ≠ criticalValue site)
    (bound : Norm.Basic.normSq (parameter - criticalValue site) ≤ (1 / 64 : Fraction.Rational)) :
    Circuit site parameter :=
  let source := UnitRoot.Transport.source site
  let budget := FixedRootBoxBudget.Budget.acquire source (1 / 2) (by decide +kernel) (by
    rewrite [UnitRoot.Transport.source_bound]
    decide +kernel)
  ofBudget site parameter regular bound source rfl budget rfl

/-- Select the identical cached original parallel leg by its original geometric quarter label. -/
@[expose] def leg {site : Fin 2} {parameter : Canonical} (circuit : Circuit site parameter) :
    (quarter : UnitCircuitQuarter) → Leg site parameter quarter
  | .first => circuit.first
  | .second => circuit.second
  | .third => circuit.third
  | .fourth => circuit.fourth

end Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport
