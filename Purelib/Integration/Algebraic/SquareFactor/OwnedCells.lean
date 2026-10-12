module
import Purelib.Data.List.Map

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.SquareRootSheets
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
public import Purelib.Integration.Algebraic.SquareFactor.CellModels
public import Purelib.Integration.Algebraic.SquareFactor.PathContinuation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Gaussian.Components.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Owner-backed uniform cells for the transported differential

An accepted continuation edge supplies its cached prepared owner.  Every
point query transports that owner, and every admitted quotient reading is
proved to satisfy the ordinary cell's local allowance.  No point independently
reselects a sheet, and the actual quotient process supplies the observations.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.OwnedCells

open Purelib.Riemann
open Purelib.Riemann.Branches

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
open Purelib.Integration.Algebraic.SquareFactor.PathContinuation
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Norm.Basic (normSq_eq_canonical)

open Purelib.Data.Rat in
/-- The rational parameter carrier for retained continuation cells. -/
abbrev Coordinate := Fraction.Rational
/-- The original coherent Gaussian approximation owner carrier. -/
abbrev CoherentNamed := Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
/-- The original certified subdivision endpoint carrier. -/
abbrev Endpoint := Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint
/-- The square-root continuation owner indexed by its exact target. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {request :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request}
  {prepared : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Prepared polynomial request} {segment :
    Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}
  {data : Purelib.Integration.Algebraic.SquareFactor.PathInput.Data prepared segment}

open Purelib.Integration.Algebraic.SquareFactor in
set_option genInjectivity false in
/-- A retained continuation edge with its original source cache and certified small movement.

The starting endpoint, root owner and exact step request remain linked to the cached prepared owner used for transport.
-/
structure Edge (safe : data.Safe) where
  /-- The original starting endpoint of the retained continuation edge. -/ left : Endpoint
  /-- The original square-root continuation owner at the starting endpoint's exact target. -/ owner : Owner
    (data.radicand.parameterPolynomial.eval ((PathContinuation.clearSegment safe).pointAt left.parameter))
  /-- The original continuation step request, including its endpoint and root diameter. -/ step :
    PreparedSheetContinuation.StepRequest
  /-- The original cached source tied to this segment, starting endpoint, owner and step. -/ cached :
    PreparedSheetContinuation.CachedSource (PathContinuation.clearSegment safe) left owner step
  /-- The original step endpoint is no earlier than the retained starting endpoint. -/ ordered : left.parameter ≤
    step.endpoint.parameter
  /-- The retained edge movement is smaller than the original prepared owner's clearance. -/ small :
    ClearSheetContinuation.variationBound (PathContinuation.clearSegment safe) left.parameter step.endpoint.parameter <
    (PreparedSheetContinuation.prepared (PathContinuation.clearSegment safe) left owner
      step).track.initial.clearance.bound

constructive_injectivity Edge

namespace Edge

variable {safe : data.Safe}

section
open Purelib.Integration.Algebraic.SquareFactor
/-- The exact ordered parameter interval of the retained edge, certified inside the unit interval. -/
@[expose] def span (edge : OwnedCells.Edge safe) : CellModels.Span :=
  ⟨⟨edge.left.parameter, edge.step.endpoint.parameter, edge.ordered⟩,
    ⟨edge.left.inside.1, edge.step.endpoint.inside.2⟩⟩

/-- Read the original continuation edge parameter at the supplied rational fraction. -/
@[expose] def parameter (edge : OwnedCells.Edge safe) (fraction : OwnedCells.Coordinate) : Coordinate :=
  PreparedSheetContinuation.parameterAt edge.left edge.step fraction

end

open Purelib.Integration.Algebraic.SquareFactor.OwnedCells.Edge in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The retained continuation parameter equals the affine parameter of the edge span. -/
theorem parameter_eq (edge : OwnedCells.Edge safe) (fraction : OwnedCells.Coordinate) :
    edge.parameter fraction = edge.span.parameter fraction := by
  rw [parameter, PreparedSheetContinuation.parameterAt_eq_affine]
  unfold OwnedCells.Edge.span CellModels.Span.parameter CellModels.Span.width
  ring1

section
open Purelib.Integration.Algebraic.SquareFactor
/-- Evaluate the original radicand parameter polynomial at the retained edge parameter. -/
@[expose] def target (edge : OwnedCells.Edge safe) (fraction : OwnedCells.Coordinate) : Gaussian :=
  data.radicand.parameterPolynomial.eval ((PathContinuation.clearSegment safe).pointAt (edge.parameter fraction))

/-- The retained target equals the original physical-segment radicand value. -/
theorem target_eq (edge : OwnedCells.Edge safe) (fraction : OwnedCells.Coordinate) :
    edge.target fraction = prepared.reduction.radicand.eval (segment.point (edge.span.parameter fraction)) := by
  rw [OwnedCells.Edge.target, PathContinuation.radicand_eq, edge.parameter_eq]

/-- Safety excludes a zero radicand at every in-range edge parameter. -/
theorem target_nonzero (edge : OwnedCells.Edge safe) {fraction : OwnedCells.Coordinate}
    (inside : PathInput.unitInterval.Contains fraction) : edge.target fraction ≠ 0 := by
  rw [edge.target_eq]
  exact safe.radicand_nonzero (edge.span.inside_unit (edge.span.parameter_inside inside))

end

open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The exact target movement remains below the retained prepared owner's initial clearance. -/
theorem pointSmall (edge : OwnedCells.Edge safe) (fraction : OwnedCells.Coordinate)
    (inside : PathInput.unitInterval.Contains fraction) :
    Data.Gaussian.Norm.Basic.normSq (data.radicand.parameterPolynomial.eval ((PathContinuation.clearSegment
      safe).pointAt
      edge.left.parameter) -
      edge.target fraction) < edge.cached.preparedOwner.track.initial.clearance.bound := by
  rw [edge.cached.preparedOwner_eq]
  exact PreparedSheetContinuation.pointNormSmall (PathContinuation.clearSegment safe) (PathContinuation.within safe)
    edge.left edge.owner edge.step edge.ordered edge.small fraction inside

section
open Purelib.Integration.Algebraic.SquareFactor
open Purelib.RootIsolation.SquareRoot.Clearance
/-- Transport the exact cached prepared owner to the supplied in-range edge parameter.

The target nonzero proof, movement bound and original transport reserve retain the same cache and continuation request.
-/
@[expose] def ownerAt (edge : OwnedCells.Edge safe) (fraction : OwnedCells.Coordinate) (inside :
  PathInput.unitInterval.Contains fraction) :
    OwnedCells.Owner (edge.target fraction) :=
  ExactQuadraticOwnerClearance.reservedTransport edge.cached.preparedOwner
    (edge.target_nonzero inside) (edge.pointSmall fraction inside)
    (PreparedSheetContinuation.transportReserve (PathContinuation.clearSegment safe) edge.left edge.step)

/-- The transported owner's initial box refines the original cached prepared owner's initial box. -/
theorem ownerAt_refines (edge : OwnedCells.Edge safe) (fraction : OwnedCells.Coordinate)
    (inside : PathInput.unitInterval.Contains fraction) :
    (edge.ownerAt fraction inside).track.initial.box.Refines edge.cached.preparedOwner.track.initial.box :=
  ExactQuadraticOwnerClearance.reservedTransport_initial_box_refines edge.cached.preparedOwner
    (edge.target_nonzero inside) (edge.pointSmall fraction inside)
    (PreparedSheetContinuation.transportReserve (PathContinuation.clearSegment safe) edge.left edge.step)

end

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.RootContinuation in
/-- Certify the exact transported root at the retained edge target. -/
@[expose] def root (edge : OwnedCells.Edge safe) (fraction : OwnedCells.Coordinate) (inside :
  PathInput.unitInterval.Contains fraction) :
    CertifiedSquareRoot.Certificate (edge.target fraction) :=
  (edge.ownerAt fraction inside).certificate (edge.target_nonzero inside)

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Every possible retained root reading lies in the original cached prepared owner's initial box. -/
theorem root_candidate_inside (edge : OwnedCells.Edge safe) (fraction : OwnedCells.Coordinate)
    (inside : PathInput.unitInterval.Contains fraction)
    (state : (edge.root fraction inside).value.name.process.State) {candidate : SquareFactor.Gaussian}
    (possible : (edge.root fraction inside).value.name.process.Possible state candidate) :
    edge.cached.preparedOwner.track.initial.box.Contains candidate :=
  (edge.ownerAt_refines fraction inside).contains
    ((edge.ownerAt fraction inside).certificate_candidate_in_initial_box
      (edge.target_nonzero inside) state possible)

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.RootContinuation in
/-- Every possible retained root reading satisfies the original physical-point residual target. -/
theorem root_candidate_residual (edge : OwnedCells.Edge safe) (fraction : OwnedCells.Coordinate)
    (inside : PathInput.unitInterval.Contains fraction)
    (state : (edge.root fraction inside).value.name.process.State) {candidate : SquareFactor.Gaussian}
    (possible : (edge.root fraction inside).value.name.process.Possible state candidate) :
    Data.Gaussian.Norm.Basic.normSq (candidate * candidate -
        prepared.reduction.radicand.eval (segment.point (edge.span.parameter fraction))) ≤
      SquareRootSheets.residualTarget
        (prepared.reduction.radicand.eval (segment.point (edge.span.parameter fraction))) := by
  rw [← edge.target_eq]
  change (CertifiedSquareRoot.approximation (edge.ownerAt fraction inside).track).Possible
    state.source candidate at possible
  rcases possible with ⟨later, _, rfl⟩
  have scalar := (CertifiedSquareRoot.sample_residual_lt_target (edge.target_nonzero inside)
    (edge.ownerAt fraction inside).track later).le
  rw [← normSq_eq_canonical] at scalar
  exact scalar

open Purelib.Approximation.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Form the original rational coefficient using the retained transported root name and its nonzero certificate. -/
@[expose] def source (edge : OwnedCells.Edge safe) (fraction : OwnedCells.Coordinate) (inside :
  PathInput.unitInterval.Contains fraction) :
    CoherentNamed :=
  let root := edge.root fraction inside
  Name.Coherent.CoherentNamed.div
    (Name.Coherent.CoherentNamed.Coherence.exact
      (data.numerator.value (edge.span.parameter fraction) /
        data.denominator.value (edge.span.parameter fraction)))
    root.value root.apart

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Every possible coefficient reading decomposes through a possible reading of the exact retained root owner. -/
theorem source_components (edge : OwnedCells.Edge safe) (fraction : OwnedCells.Coordinate)
    (inside : PathInput.unitInterval.Contains fraction)
    (state : (edge.source fraction inside).name.process.State) {candidate : SquareFactor.Gaussian}
    (possible : (edge.source fraction inside).name.process.Possible state candidate) :
    ∃ rootCandidate : SquareFactor.Gaussian,
      (edge.root fraction inside).value.name.process.Possible state.2 rootCandidate ∧
      candidate = CoefficientBounds.coefficient data (edge.span.parameter fraction) rootCandidate := by
  rcases possible with ⟨numerator, denominator, numeratorPossible, denominatorPossible, rfl⟩
  refine ⟨denominator, denominatorPossible, ?_⟩
  change numerator = data.numerator.value (edge.span.parameter fraction) /
    data.denominator.value (edge.span.parameter fraction) at numeratorPossible
  rw [numeratorPossible]
  rfl

open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Construct the cell model from a retained initial root reading and the original cached prepared enclosure.

The chosen witness belongs to the edge's original root name; its enclosure and residual certificates establish the
cached coefficient allowance. -/
@[expose] def model (edge : OwnedCells.Edge safe) : CellModels.Model data edge.span := by
  let root := edge.root 0 (by decide)
  let reading := root.value.name.process.witness root.value.name.state
  apply CellModels.make safe edge.span edge.cached.preparedOwner.track.initial.box
    reading.val (edge.root_candidate_inside 0 (by decide) root.value.name.state reading.property)
  have residual := edge.root_candidate_residual 0 (by decide) root.value.name.state reading.property
  have pointEqual : edge.span.parameter 0 = edge.span.interval.lower := by
    unfold CellModels.Span.parameter
    rw [Fraction.Field.mul_zero_direct, add_zero]
  rw [pointEqual] at residual
  exact residual

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Polynomial.Ascending in
/-- Every possible edge-source reading meets the exact edge model allowance at the requested in-range fraction. -/
theorem source_candidate_error_le (edge : OwnedCells.Edge safe) (fraction : OwnedCells.Coordinate)
    (inside : PathInput.unitInterval.Contains fraction)
    (state : (edge.source fraction inside).name.process.State) {candidate : SquareFactor.Gaussian}
    (possible : (edge.source fraction inside).name.process.Possible state candidate) :
    Data.Gaussian.Norm.Basic.normSq (candidate - Gaussian.Evaluation.eval edge.model.cell.polynomial ⟨fraction, 0⟩) ≤
      edge.model.cell.localAllowance := by
  rcases edge.source_components fraction inside state possible with ⟨rootCandidate, rootPossible, rfl⟩
  exact edge.model.candidate_error_le safe inside
    (edge.root_candidate_inside fraction inside state.2 rootPossible)
    (edge.root_candidate_residual fraction inside state.2 rootPossible)

end Edge

open Purelib.Integration.Algebraic.SquareFactor in
set_option genInjectivity false in
/-- A retained continuation edge and its cached exact cell model. -/
structure Cell (safe : data.Safe) where
  /-- The original retained continuation edge. -/ edge : Edge safe
  /-- The cached cell model indexed by the original edge span. -/ model : CellModels.Model data edge.span
  /-- The cached model equals the exact model of the original retained edge. -/ model_eq : model = edge.model

constructive_injectivity Cell

open Purelib.Integration.Algebraic.SquareFactor in
/-- Cache the exact model of the supplied retained continuation edge. -/
@[expose] def compileEdge {safe : data.Safe} (edge : Edge safe) : Cell safe :=
  ⟨edge, edge.model, rfl⟩

namespace Cell

variable {safe : data.Safe}

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Polynomial.Ascending in
/-- Every possible edge-source reading meets the allowance of the cell's retained cached model. -/
theorem source_candidate_error_le (cell : OwnedCells.Cell safe) (fraction : OwnedCells.Coordinate)
    (inside : PathInput.unitInterval.Contains fraction)
    (state : (cell.edge.source fraction inside).name.process.State) {candidate : SquareFactor.Gaussian}
    (possible : (cell.edge.source fraction inside).name.process.Possible state candidate) :
    Data.Gaussian.Norm.Basic.normSq (candidate - Gaussian.Evaluation.eval cell.model.cell.polynomial ⟨fraction, 0⟩) ≤
      cell.model.cell.localAllowance := by
  rw [cell.model_eq]
  exact cell.edge.source_candidate_error_le fraction inside state possible

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Cell in
set_option genInjectivity false in
/-- A local model observation tied to the exact source process state and requested fraction.

The possible-reading proof names the retained source, and the parameter equality identifies the observation with the
original request. -/
structure Observation (source : OwnedCells.CoherentNamed)
    (model : Basic.CellModel) (fraction : OwnedCells.Coordinate) where
  /-- The retained state of the exact source approximation process. -/ readingState : source.name.process.State
  /-- The local polynomial observation with its certified allowance. -/ observation : Basic.LocalObservation
    model.polynomial model.localAllowance
  /-- The observation uses the exact requested fraction. -/ parameter_eq : observation.parameter = fraction
  /-- The retained integrand reading is possible at the exact retained source state. -/ readingPossible :
    source.name.process.Possible
    readingState observation.integrandReading

constructive_injectivity Observation

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Polynomial.Ascending in
/-- Read the exact retained source at the requested in-range fraction and certify its local model error.

The result retains the source process state, its actual witness reading and the decomposition into polynomial value plus
bounded error. -/
@[expose] def query (cell : OwnedCells.Cell safe) (fraction : OwnedCells.Coordinate) (inside :
  PathInput.unitInterval.Contains fraction) :
    OwnedCells.Cell.Observation (cell.edge.source fraction inside) cell.model.cell fraction :=
  let source := cell.edge.source fraction inside
  let reading := source.name.process.witness source.name.state
  { readingState := source.name.state
    observation :=
      { parameter := fraction
        integrandReading := reading.val
        error := reading.val - Gaussian.Evaluation.eval cell.model.cell.polynomial ⟨fraction, 0⟩
        decomposition := rfl
        error_le := by
          have scalar := cell.source_candidate_error_le fraction inside source.name.state reading.property
          rw [normSq_eq_canonical] at scalar
          exact scalar }
    parameter_eq := rfl
    readingPossible := reading.property }

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Transport a possible coefficient reading to the original differential on a positive square-factor domain.

The same possible root reading is retained, and its residual bound supplies the nonzero root needed for the exact
coefficient identity. -/
theorem source_original_components (cell : OwnedCells.Cell safe)
    (originalDomain : 0 < data.squareFactor.lowerBound)
    (fraction : OwnedCells.Coordinate) (inside : PathInput.unitInterval.Contains fraction)
    (state : (cell.edge.source fraction inside).name.process.State) {candidate : SquareFactor.Gaussian}
    (possible : (cell.edge.source fraction inside).name.process.Possible state candidate) :
    ∃ rootCandidate : SquareFactor.Gaussian,
      (cell.edge.root fraction inside).value.name.process.Possible state.2 rootCandidate ∧
      candidate = request.originalNumerator prepared.reduction
          (segment.point (cell.edge.span.parameter fraction)) /
        SquareFactor.coordinate prepared.reduction (segment.point (cell.edge.span.parameter fraction)) rootCandidate :=
          by
  rcases cell.edge.source_components fraction inside state possible with
    ⟨rootCandidate, rootPossible, candidateEq⟩
  refine ⟨rootCandidate, rootPossible, candidateEq.trans ?_⟩
  rw [CoefficientBounds.coefficient_eq]
  have parameterInside := cell.edge.span.inside_unit (cell.edge.span.parameter_inside inside)
  have residual := cell.edge.root_candidate_residual fraction inside state.2 rootPossible
  have rootNonzero : rootCandidate ≠ 0 := by
    intro zero
    have positive := (CoefficientBounds.rootLower_positive safe).trans_le (CoefficientBounds.rootLower_le safe
      parameterInside residual)
    rw [zero, Norm.Basic.normSq_zero] at positive
    exact (lt_irrefl _ positive).elim
  exact data.coefficient_transport originalDomain parameterInside rootCandidate rootNonzero

end Cell

section
open Purelib.Integration.Algebraic.SquareFactor
/-- Compile the original continuation run in order, preserving every step's endpoint, owner, request and cached source.
-/
@[expose] def compileSubdivision {safe : data.Safe} {left : Endpoint}
    {owner : Owner (data.radicand.parameterPolynomial.eval ((PathContinuation.clearSegment safe).pointAt
      left.parameter))} :
    PreparedSheetContinuation.Subdivision (PathContinuation.clearSegment safe) (PathContinuation.within safe) left owner
      → List (Cell safe)
  | .stop _ _ => []
  | .next left owner step cached ordered small remaining =>
      compileEdge ⟨left, owner, step, cached, ordered, small⟩ ::
        compileSubdivision remaining

/-- The compiled cell count equals the original subdivision step count. -/
theorem compileSubdivision_length {safe : data.Safe} {left : Endpoint}
    {owner : Owner (data.radicand.parameterPolynomial.eval ((PathContinuation.clearSegment safe).pointAt
      left.parameter))}
    (run : PreparedSheetContinuation.Subdivision (PathContinuation.clearSegment safe) (PathContinuation.within safe)
      left owner) :
    (compileSubdivision run).length = run.stepCount := by
  induction run with
  | stop _ _ => rfl
  | next _ _ _ _ _ _ _ ih =>
      simpa only [compileSubdivision, List.length_cons,
        PreparedSheetContinuation.Subdivision.stepCount_next]
        using congrArg Nat.succ ih

/-- Compiled physical cell endpoints read the original subdivision parameter edges in order. -/
theorem compileSubdivision_geometry {safe : data.Safe} {left : Endpoint}
    {owner : Owner (data.radicand.parameterPolynomial.eval ((PathContinuation.clearSegment safe).pointAt
      left.parameter))}
    (run : PreparedSheetContinuation.Subdivision (PathContinuation.clearSegment safe) (PathContinuation.within safe)
      left owner) :
    (compileSubdivision run).map (fun cell => (cell.model.cell.start, cell.model.cell.finish)) =
      run.parameterEdges.map (fun endpoints =>
        (segment.point endpoints.1.parameter, segment.point endpoints.2.parameter)) := by
  induction run with
  | stop _ _ => rfl
  | next _ _ _ _ _ _ _ ih =>
      simp only [compileSubdivision, List.map_cons,
        PreparedSheetContinuation.Subdivision.parameterEdges_next]
      exact congrArg (List.cons _) ih

/-- Compiled parameter edges equal the original retained subdivision edges. -/
theorem compileSubdivision_parameterEdges {safe : data.Safe} {left : Endpoint}
    {owner : Owner (data.radicand.parameterPolynomial.eval ((PathContinuation.clearSegment safe).pointAt
      left.parameter))}
    (run : PreparedSheetContinuation.Subdivision (PathContinuation.clearSegment safe) (PathContinuation.within safe)
      left owner) :
    (compileSubdivision run).map (fun cell =>
      (⟨cell.edge.left, cell.edge.step.endpoint⟩ : ClearSheetContinuation.Subdivision.ParameterEdge)) =
      run.parameterEdges := by
  induction run with
  | stop _ _ => rfl
  | next _ _ _ _ _ _ _ ih =>
      simp only [compileSubdivision, List.map_cons,
        PreparedSheetContinuation.Subdivision.parameterEdges_next]
      exact congrArg (List.cons _) ih

/-- Compiled step requests equal the original retained subdivision requests. -/
theorem compileSubdivision_requests {safe : data.Safe} {left : Endpoint}
    {owner : Owner (data.radicand.parameterPolynomial.eval ((PathContinuation.clearSegment safe).pointAt
      left.parameter))}
    (run : PreparedSheetContinuation.Subdivision (PathContinuation.clearSegment safe) (PathContinuation.within safe)
      left owner) :
    (compileSubdivision run).map (fun cell => cell.edge.step) = run.requests := by
  induction run with
  | stop _ _ => rfl
  | next _ _ _ _ _ _ _ ih =>
      simp only [compileSubdivision, List.map_cons,
        PreparedSheetContinuation.Subdivision.requests_next]
      exact congrArg (List.cons _) ih

end

open Purelib.Integration.Algebraic.SquareFactor in
set_option genInjectivity false in
/-- The exact selected subdivision mesh together with its cached ordered compiled cells.

The selection equation retains the original sheet and resolution request, and the cell equation ties compilation to that
same run. -/
structure CompiledRun (safe : data.Safe) (sheet : Fin 2)
    (rootDiameter : Coordinate) (positive : 0 < rootDiameter) (minimumDepth : Nat) where
  /-- The selected mesh indexed by the original sheet owner and resolution request. -/ mesh :
    PathContinuation.SelectedMesh safe (PathContinuation.initialOwner safe sheet) rootDiameter positive minimumDepth
  /-- The retained mesh equals the exact original mesh selection. -/ mesh_eq : mesh = PathContinuation.selectMesh safe
    sheet rootDiameter positive minimumDepth
  /-- The retained ordered list of compiled continuation cells. -/ cells : List (Cell safe)
  /-- The cached cells equal compilation of the retained mesh's exact run. -/ cells_eq : cells =
    compileSubdivision mesh.run

constructive_injectivity CompiledRun

open Purelib.Integration.Algebraic.SquareFactor in
/-- Select the original mesh once and compile its retained run once, preserving both cache equations. -/
@[expose] def compile {safe : data.Safe} (sheet : Fin 2) (rootDiameter : Coordinate) (positive : 0 <
  rootDiameter)
    (minimumDepth : Nat) : CompiledRun safe sheet rootDiameter positive minimumDepth :=
  let mesh := PathContinuation.selectMesh safe sheet rootDiameter positive minimumDepth
  ⟨mesh, rfl, compileSubdivision mesh.run, rfl⟩

section
open Purelib.Integration.Algebraic.SquareFactor
/-- Read the exact retained subdivision run from the compiled mesh. -/
@[expose] def CompiledRun.run {safe : data.Safe} {sheet : Fin 2}
    {rootDiameter : Coordinate} {positive : 0 < rootDiameter} {minimumDepth : Nat}
    (compiled : CompiledRun safe sheet rootDiameter positive minimumDepth) :
    PreparedSheetContinuation.Subdivision (PathContinuation.clearSegment safe) (PathContinuation.within safe)
      PathContinuation.first
      (PathContinuation.initialOwner safe sheet) := compiled.mesh.run

/-- Read the actual selected mesh depth. -/
@[expose] def CompiledRun.depth {safe : data.Safe} {sheet : Fin 2}
    {rootDiameter : Coordinate} {positive : 0 < rootDiameter} {minimumDepth : Nat}
    (compiled : CompiledRun safe sheet rootDiameter positive minimumDepth) : Nat := compiled.mesh.depth

/-- The actual selected depth meets the original minimum-depth request. -/
theorem CompiledRun.minimumDepth_le {safe : data.Safe} {sheet : Fin 2}
    {rootDiameter : Coordinate} {positive : 0 < rootDiameter} {minimumDepth : Nat}
    (compiled : CompiledRun safe sheet rootDiameter positive minimumDepth) :
    minimumDepth ≤ compiled.depth := compiled.mesh.minimumDepth_le

end

open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Read the path model from the retained compiled cell models in their original order. -/
@[expose] def CompiledRun.pathModel {safe : data.Safe} {sheet : Fin 2}
    {rootDiameter : Coordinate} {positive : 0 < rootDiameter} {minimumDepth : Nat}
    (compiled : CompiledRun safe sheet rootDiameter positive minimumDepth) :
    Basic.PathModel :=
  ⟨compiled.cells.map (fun cell => cell.model.cell)⟩

open Purelib.Integration.Algebraic.SquareFactor
/-- The retained path model's cell count equals the original run's step count. -/
theorem CompiledRun.cellCount {safe : data.Safe} {sheet : Fin 2}
    {rootDiameter : Coordinate} {positive : 0 < rootDiameter} {minimumDepth : Nat}
    (compiled : CompiledRun safe sheet rootDiameter positive minimumDepth) :
    compiled.pathModel.cells.length = compiled.run.stepCount := by
  rw [CompiledRun.pathModel, Purelib.Data.List.Map.length_map, compiled.cells_eq,
    compileSubdivision_length,
    CompiledRun.run]

/-- The retained compiled cell geometry equals the original subdivision's physical parameter-edge geometry. -/
theorem CompiledRun.geometry {safe : data.Safe} {sheet : Fin 2}
    {rootDiameter : Coordinate} {positive : 0 < rootDiameter} {minimumDepth : Nat}
    (compiled : CompiledRun safe sheet rootDiameter positive minimumDepth) :
    compiled.cells.map (fun cell => (cell.model.cell.start, cell.model.cell.finish)) =
      compiled.run.parameterEdges.map (fun endpoints =>
        (segment.point endpoints.1.parameter, segment.point endpoints.2.parameter)) := by
  rw [compiled.cells_eq]
  exact compileSubdivision_geometry compiled.run

end Purelib.Integration.Algebraic.SquareFactor.OwnedCells
