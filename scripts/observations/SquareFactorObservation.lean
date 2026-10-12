module
public import Purelib.System.IO
import Purelib.Data.String.Basic
public import Purelib.Data.String.Parsing
public import Purelib.Data.List.Control
public import Purelib.Data.List.ToString
public import Purelib.Data.Int.Decimal
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Power.Isolation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
import Purelib.Polynomial.Clearance.Box.Boundary.RootRadius
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Global
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Newton.Search.Iteration
import Purelib.RootIsolation.SquareRoot.Newton.Search
import Purelib.Geometry.Rational.Box.Sample.Five

import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Integration.Algebraic.SquareFactor.Accuracy
import Purelib.Integration.Algebraic.SquareFactor.ChildCells
import Purelib.Integration.Algebraic.SquareFactor.ChildMeshes
import Purelib.Integration.Algebraic.SquareFactor.IntegrationLayers
import Purelib.Integration.Algebraic.SquareFactor.ObservationInput
import Purelib.Integration.Algebraic.SquareFactor.OwnedCells
import Purelib.Integration.Algebraic.SquareFactor.PathContinuation
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Integration.Algebraic.SquareFactor.PathObservation
public import Purelib.Integration.Algebraic.SquareFactor.PolynomialObservation
import Purelib.Integration.Algebraic.SquareFactor.UniformRefinement
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
import Purelib.Integration.Algebraic.SquareFactor.ObservationTransport
import Purelib.Data.Gaussian.Norm.Comparison
import Init.Data.List.Basic
import Init.Prelude
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Computation.Query.Basic
import Purelib.Computation.Query.Replay
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Data.CCL.Transducer.Replay.Machine.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Nat.Positive
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Algebraic.SquareFactor.CellModels
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Integration.Program.Gaussian.Cached.Allocation
import Purelib.Integration.Program.Gaussian.Cached.Policy
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Newton.Restart.Separated.Basic
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.Raw.FromRegion
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

set_option backward.match.sparseCases false

open scoped Purelib.Data.String Purelib.Data.Int.Decimal Purelib.Data.List

open Purelib

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic

open Purelib.CCL.Progressive

open Purelib.Curves.Hyperelliptic.Differentials

open Purelib.Data.Gaussian.Basic.Canonical.Norm

open Purelib.Geometry

open Purelib.Geometry.Rational.Box.Sample

open Purelib.Integration.Algebraic.SquareFactor

open Purelib.Integration.Algebraic.SquareFactor.IntegrationLayers

open Purelib.Integration.Polynomial.Gaussian

open Purelib.Integration.Program.Gaussian

open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation

open Purelib.Polynomial

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Clearance.Box.Boundary

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Power.Gaussian

open Purelib.Polynomial.Winding.Box

open Purelib.Riemann.Branches

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Topology

open Purelib.RootIsolation.Newton.Search

open Purelib.RootIsolation.Power

open Purelib.RootIsolation.SquareRoot.Clearance

open Purelib.RootIsolation.SquareRoot.Newton

public section

/-!
Short-iteration runtime diagnostics for the coefficient-first original-path
integrator.  No Legendre fixture or generated bank is imported.  Build once
for native runs; guard diagnostics with systemd memory limits and an explicit
SIGKILL timeout.  Budget mode does not force root preparation or a model.
Observation mode runs the actual nonempty observation and source-free replay.
Neither mode replaces the universal Lean proofs or the axiom/build gates.
-/

namespace SquareFactorObservationHarness

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Integration.Algebraic.SquareFactor.PathObservation (Policy ObservationRequest)

/-- `p=x²(x³+1)`: repeated input with a positive-genus squarefree reduction. The retained nonstationary path avoids the
removed coordinate zero. -/
@[expose] def polynomial : GaussianPolynomial := ⟨[1, 0, 0, 1, 0, 0]⟩
/-- The nonstationary real segment from one to seventeen sixteenths. -/
@[expose] def segment : Segment := ⟨1, ⟨17 / 16, 0⟩⟩
/-- The original-coordinate differential request of degree zero. -/
@[expose] def differential : Request := .original 0

/-- The retained integration refinement and observation schedule for the fixture. -/
@[expose] def policy : Policy := ⟨⟨0, 0⟩, ⟨4, [4]⟩⟩
/-- The original observation request at source index zero and target one. -/
@[expose] def query : ObservationRequest := ⟨0, 1, by decide⟩

/-- Print and flush one square-factor integration diagnostic message. -/
@[expose] def report (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Evaluate a thunk through IO without inlining its timing boundary. -/
@[noinline, expose] def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

/-- Render the exact numerator and denominator of a rational value. -/
@[expose] def fractionText (value : PathInput.Coordinate) : String := s!"{value.num}/{value.den}"

/-- Prepare the original polynomial, differential and path and verify the intended squarefree reduction degrees. -/
@[expose] def prepare : IO (ObservationInput.PreparedEntry
    polynomial differential segment 0 .originalCoordinate) := do
  report "square-factor: preparing raw polynomial and original-coordinate segment"
  let started ← IO.monoMsNow
  let result ← evaluate fun _ =>
    ObservationInput.prepare polynomial differential segment 0 .originalCoordinate
  match result with
  | .error _ => throw (IO.userError "raw repeated-factor input was rejected")
  | .ok entry =>
      report
        s!"square-factor: input accepted in {(← IO.monoMsNow) - started} ms; reduced \
          degree={entry.prepared.reduction.radicand.natDegree}; square-factor \
          degree={entry.prepared.reduction.squareFactor.natDegree}"
      unless entry.prepared.reduction.radicand.natDegree = 3 ∧
          entry.prepared.reduction.squareFactor.natDegree = 1 do
        throw (IO.userError "example does not have the intended positive-genus repeated-factor reduction")
      pure entry

/-- Report the original coefficient bounds and computed continuation resolution for a selected layer.

The diagnostic reads the actual parameter and root scales without constructing a numerical observation. -/
@[expose] def budget (index : Nat := 0) : IO Unit := do
  let entry ← prepare
  report
    s!"square-factor: numerator={entry.prepared.weight.numerator.coeffs.length} coefficients; \
      denominator={entry.prepared.weight.denominator.coeffs.length} coefficients"
  report
    s!"square-factor: numerator value ceiling={fractionText entry.data.numerator.valueBound}; squared \
      slope={fractionText entry.data.numerator.slopeBound}"
  report
    s!"square-factor: denominator value ceiling={fractionText entry.data.denominator.valueBound}; squared \
      floor={fractionText entry.data.denominator.lowerBound}; squared \
      slope={fractionText entry.data.denominator.slopeBound}"
  report
    s!"square-factor: radicand value ceiling={fractionText entry.data.radicand.valueBound}; squared \
      floor={fractionText entry.data.radicand.lowerBound}; coordinate \
      floor={fractionText entry.data.radicand.coordinateLower}"
  report s!"square-factor: root squared-norm floor={fractionText entry.data.rootNormFloor}"
  let clear := PathContinuation.clearSegment entry.safe
  let parameterPolynomial := ClearSheetContinuation.segmentPolynomial clear
  let slope ← evaluate fun _ => Dense.Gaussian.Bounds.Box.denseEvalNormLipschitzBound
    parameterPolynomial ClearSheetContinuation.parameterAmbient
  let clampedSlope ← evaluate fun _ => Dense.Gaussian.Bounds.Box.denseLipschitzBound
    parameterPolynomial ClearSheetContinuation.parameterAmbient
  report
    s!"square-factor: raw squared-slope bound={fractionText slope}; clamped continuation \
      slope={fractionText clampedSlope}"
  let target := Geometric.Basic.quarterRadius 1 index
  let resolution ← evaluate fun _ => Accuracy.resolve entry.safe 1 (by decide)
    target (Geometric.Basic.quarterRadius_pos (by decide) index)
  let depth ← evaluate fun _ => PathContinuation.maximumDepth entry.safe
    resolution.rootDiameter resolution.minimumDepth
  report
    s!"square-factor: parameter scale={fractionText resolution.parameterScale}; root \
      scale={fractionText resolution.rootScale}"
  report
    s!"square-factor: layer={index}; target={fractionText target}; root \
      diameter={fractionText resolution.rootDiameter}; numerical depth={resolution.minimumDepth}; maximum continuation \
      depth={depth}; maximum cells=2^{depth}"

/-- Diagnose checked initial extraction using the actual coefficient-computed large square and generic axis eliminants.
Off-centre seeds are deterministic box geometry, not supplied root certificates. -/
@[expose] def seed : IO Unit := do
  let entry ← prepare
  let parameter := entry.prepared.reduction.radicand.eval segment.start
  have nonzero : parameter ≠ 0 := by
    simpa only [parameter, ← Segment.point_zero segment] using
      entry.safe.radicand_nonzero (show (0 : PathInput.Coordinate) ≤ 0 ∧ (0 : PathInput.Coordinate) ≤ 1 by decide)
  let input := Isolation.isolationInput nonzero
    SquareRootDegree.degreeTwo (by decide)
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter SquareRootDegree.degreeTwo
  let region : Region.ClearRegion p (RootRadius.Box.largeSquareBox p) :=
    { box := RootRadius.Box.largeSquareBox p
      refinesAmbient := Rational.Box.refines_refl _
      proper := RootRadius.Box.largeSquareBox_proper p
      clearance := RootRadius.largeSquare_boundaryClearance input.degreePositive }
  have winding : Winding.Box.Basic.quadrupledBoxWinding p region.box ≠ 0 := by
    change Winding.Box.Basic.quadrupledBoxWinding p (RootRadius.Box.largeSquareBox p) ≠ 0
    rw [Global.quadrupledBoxWinding_largeSquare_eq_degree input.degreePositive,
      Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
    decide
  let raw := region.raw winding
  let box ← evaluate fun _ => raw.box
  let proposals := Five.seeds box
  for proposal in proposals do
    report s!"square-factor: checked seed ({fractionText proposal.re}, {fractionText proposal.im})"
    let started ← IO.monoMsNow
    let result ← evaluate fun _ => Iteration.search input.elimination raw 1 6 0 proposal
    match result with
    | none => report s!"square-factor: seed rejected in {(← IO.monoMsNow) - started} ms"
    | some accepted =>
        report
          s!"square-factor: seed accepted in {(← IO.monoMsNow) - started} ms; \
            diagonal²={fractionText accepted.state.box.diagonalSq}; \
            clearance={fractionText accepted.state.clearance.bound}"

/-- Compare first-edge acceptance across the constructor's finite depth range, retaining the same once-computed initial
owner. This does not claim acceptance of the whole mesh or completion of an integral observation. -/
@[expose] def firstEdges : IO Unit := do
  let entry ← prepare
  let resolution := Accuracy.resolve entry.safe 1 (by decide) 1 (by decide)
  let clear := PathContinuation.clearSegment entry.safe
  let first := PathContinuation.first
  let last := PathContinuation.last
  let owner ← evaluate fun _ => PathContinuation.initialOwner entry.safe 0
  let maximum := PathContinuation.maximumDepth entry.safe
    resolution.rootDiameter resolution.minimumDepth
  for offset in List.range (maximum + 1 - resolution.minimumDepth) do
    let depth := resolution.minimumDepth + offset
    let started ← IO.monoMsNow
    let requests := PreparedSheetContinuation.Subdivision.dyadicRequests depth first last
      resolution.rootDiameter resolution.rootDiameterPositive
    let some request := requests.head? | throw (IO.userError "dyadic mesh has no first edge")
    let cached ← evaluate fun _ => PreparedSheetContinuation.CachedSource.canonical
      clear first owner request
    let small ← evaluate fun _ => decide (ClearSheetContinuation.variationBound clear
      first.parameter request.endpoint.parameter < cached.preparedOwner.track.initial.clearance.bound)
    report s!"square-factor: depth={depth}; first edge accepted={small}; elapsed={(← IO.monoMsNow) - started} ms"
    if small then return
  throw (IO.userError "no first edge accepted even at the computed sufficient depth")

/-- Time the actual owner/preparation checker at one displayed mesh depth. This only diagnoses finite proposal
acceptance; it is not an observation run. -/
@[expose] def mesh (depth : Nat) : IO Unit := do
  let entry ← prepare
  let resolution := Accuracy.resolve entry.safe 1 (by decide) 1 (by decide)
  let clear := PathContinuation.clearSegment entry.safe
  let first := PathContinuation.first
  let last := PathContinuation.last
  let started ← IO.monoMsNow
  report "square-factor: selecting the initial root owner"
  let owner ← evaluate fun _ => PathContinuation.initialOwner entry.safe 0
  let box ← evaluate fun _ => owner.track.initial.box
  report s!"square-factor: initial owner in {(← IO.monoMsNow) - started} ms; diagonal²={fractionText box.diagonalSq}"
  let requests := PreparedSheetContinuation.Subdivision.dyadicRequests depth first last
    resolution.rootDiameter resolution.rootDiameterPositive
  let some firstRequest := requests.head? | throw (IO.userError "dyadic mesh has no first edge")
  report s!"square-factor: preparing first edge at depth={depth}"
  let cached ← evaluate fun _ => PreparedSheetContinuation.CachedSource.canonical clear first owner firstRequest
  let small ← evaluate fun _ => decide (ClearSheetContinuation.variationBound clear
    first.parameter firstRequest.endpoint.parameter < cached.preparedOwner.track.initial.clearance.bound)
  report s!"square-factor: first edge accepted={small}; elapsed={(← IO.monoMsNow) - started} ms"
  if small then
    let checked ← evaluate fun _ => PreparedSheetContinuation.Subdivision.tryDyadic clear
      (PathContinuation.within entry.safe) first last owner depth
      resolution.rootDiameter resolution.rootDiameterPositive
    report s!"square-factor: entire mesh accepted={checked.isSome}; elapsed={(← IO.monoMsNow) - started} ms"

/-- Instrument the production checker's preparation and advance operations. The dependent endpoint owner is threaded
unchanged into the next operation. Log the first sixteen steps and then every 256th step, so large meshes do not turn
this into a terminal-output benchmark. -/
@[expose] def traceSteps {p : SquareFactor.GaussianPolynomial} {ambient : Rational.Box}
    {start finish : SquareFactor.Gaussian}
    (clear : ClearPath.ClearSegment p ambient start finish)
    (within : clear.WithinAmbient) (sampleAt : Option Nat) (index : Nat)
    (left : ClearSheetContinuation.Subdivision.Endpoint)
    (owner : SquareRootContinuationChain.Owner (p.eval (clear.pointAt left.parameter))) :
    List PreparedSheetContinuation.StepRequest →
      IO (PreparedSheetContinuation.Subdivision clear within left owner)
  | [] => do
      report s!"square-factor trace: completed {index} continuation steps"
      return .stop left owner
  | request :: remaining => do
      if sampleAt == some index then
        let geometry ← evaluate fun _ => decide
          (owner.track.initial.box.diagonalSq < request.rootDiameter)
        let ready ← evaluate fun _ => decide
          (PreparedSheetContinuation.AlreadyPrepared clear left owner request)
        let refreshedStart ← IO.monoMsNow
        let refreshed ← evaluate fun _ =>
          ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner
        let refreshedReady ← evaluate fun _ => decide
          (PreparedSheetContinuation.AlreadyPrepared clear left refreshed request)
        let refreshedCarries ← evaluate fun _ => decide
          (ClearSheetContinuation.variationBound clear left.parameter request.endpoint.parameter <
            refreshed.track.initial.clearance.bound)
        report
          s!"square-factor sample: geometry={geometry}; ready={ready}; refreshed ready={refreshedReady}; refreshed \
            carries={refreshedCarries}; refresh elapsed={(← IO.monoMsNow) - refreshedStart} ms"
        let sharpStart ← IO.monoMsNow
        let sharp ← evaluate fun _ => QuadraticCoefficientClearance.strengthen owner
        let sharpReady ← evaluate fun _ => decide
          (PreparedSheetContinuation.AlreadyPrepared clear left sharp request)
        let sharpCarries ← evaluate fun _ => decide
          (ClearSheetContinuation.variationBound clear left.parameter request.endpoint.parameter <
            sharp.track.initial.clearance.bound)
        report
          s!"square-factor sample: coefficient refresh ready={sharpReady}; carries={sharpCarries}; \
            elapsed={(← IO.monoMsNow) - sharpStart} ms"
        let resetStart ← IO.monoMsNow
        let moving ← evaluate fun _ =>
          ExactQuadraticOwnerClearance.movingRecenter? owner
        report
          s!"square-factor sample: moving reset available={moving.isSome}; elapsed={(← IO.monoMsNow) - resetStart} ms"
        let uniformStart ← IO.monoMsNow
        let uniform ← evaluate fun _ => QuadraticCoefficientClearance.strengthen
          (UniformSquareRootPreparation.prepared clear left.parameter left.inside
            owner request.rootDiameter request.rootDiameterPositive)
        let uniformReady ← evaluate fun _ => decide
          (PreparedSheetContinuation.AlreadyPrepared clear left uniform request)
        let uniformCarries ← evaluate fun _ => decide
          (ClearSheetContinuation.variationBound clear left.parameter request.endpoint.parameter <
            uniform.track.initial.clearance.bound)
        report
          s!"square-factor sample: uniform reset ready={uniformReady}; carries={uniformCarries}; \
            elapsed={(← IO.monoMsNow) - uniformStart} ms"
        let target := UniformSquareRootPreparation.sampleResidualTarget clear owner request.rootDiameter
        let grid := CheckedSquareRootNewton.gridFor target
        report s!"square-factor sample: step={index}; testing rounded sample"
        let started ← IO.monoMsNow
        let candidate ← evaluate fun _ => Search.search
          (p.eval (clear.pointAt left.parameter))
          (UniformSquareRootPreparation.SampleAcceptable clear owner request.rootDiameter)
          8 grid (UniformSquareRootPreparation.ownerMidpoint owner.track.initial.box)
        let some accepted := candidate | throw (IO.userError "rounded sample proposal rejected")
        report
          s!"square-factor sample: rounded accepted in {(← IO.monoMsNow) - started} ms; denominator \
            bits=({accepted.val.re.den.log2 + 1},{accepted.val.im.den.log2 + 1})"
        let canonicalStart ← IO.monoMsNow
        let canonical ← evaluate fun _ => UniformSquareRootPreparation.sample clear owner request.rootDiameter
        unless canonical == accepted.val do
          throw (IO.userError "canonical cached search differs from the independently checked proposal")
        report
          s!"square-factor sample: canonical agrees in {(← IO.monoMsNow) - canonicalStart} ms; denominator \
            bits=({canonical.re.den.log2 + 1},{canonical.im.den.log2 + 1})"
        return .stop left owner
      let logging := decide (index < 16 ∨ index % 256 = 0)
      if logging then report s!"square-factor trace: step={index}; preparing"
      let started ← IO.monoMsNow
      let cached ← evaluate fun _ => PreparedSheetContinuation.CachedSource.canonical
        clear left owner request
      let bound ← evaluate fun _ => cached.preparedOwner.track.initial.clearance.bound
      if logging then
        report
          s!"square-factor trace: step={index}; prepared in {(← IO.monoMsNow) - started} ms; clearance \
            bits=({bound.num.natAbs.log2 + 1},{bound.den.log2 + 1})"
      if ordered : left.parameter ≤ request.endpoint.parameter then
        if small : ClearSheetContinuation.variationBound clear
            left.parameter request.endpoint.parameter < cached.preparedOwner.track.initial.clearance.bound then
          if logging then report s!"square-factor trace: step={index}; advancing"
          let advancing ← IO.monoMsNow
          let advanced ← evaluate fun _ =>
            (⟨PreparedSheetContinuation.advanceCached
                clear within left owner request cached small, rfl⟩ :
              {next : SquareRootContinuationChain.Owner
                  (p.eval (clear.pointAt request.endpoint.parameter)) //
                next = PreparedSheetContinuation.advanceCached
                  clear within left owner request cached small})
          let next := advanced.val
          let nextBound ← evaluate fun _ => next.track.initial.clearance.bound
          if logging then
            report
              s!"square-factor trace: step={index}; advanced in {(← IO.monoMsNow) - advancing} ms; clearance \
                bits=({nextBound.num.natAbs.log2 + 1},{nextBound.den.log2 + 1})"
          let tail ← traceSteps clear within sampleAt (index + 1) request.endpoint next remaining
          have canonicalSmall : ClearSheetContinuation.variationBound clear
              left.parameter request.endpoint.parameter <
                (PreparedSheetContinuation.prepared clear left owner request).track.initial.clearance.bound := by
            rw [cached.preparedOwner_eq] at small
            exact small
          return PreparedSheetContinuation.Subdivision.nextCached
            clear within left owner request cached ordered small canonicalSmall
              (advanced.property ▸ tail)
        else throw (IO.userError s!"square-factor trace: step={index}; rejected continuation edge")
      else throw (IO.userError s!"square-factor trace: step={index}; unordered continuation edge")

/-- Trace the same raw-input fixture without forcing its cell models or CCL output. Completion here is only a
continuation diagnostic. -/
@[expose] def trace (depth : Nat) (sampleAt : Option Nat := none) : IO Unit := do
  let entry ← prepare
  let resolution := Accuracy.resolve entry.safe 1 (by decide) 1 (by decide)
  let clear := PathContinuation.clearSegment entry.safe
  let first := PathContinuation.first
  let last := PathContinuation.last
  report s!"square-factor trace: initializing depth={depth}"
  let owner ← evaluate fun _ => PathContinuation.initialOwner entry.safe 0
  let requests ← evaluate fun _ => PreparedSheetContinuation.Subdivision.dyadicRequests
    depth first last resolution.rootDiameter resolution.rootDiameterPositive
  let _ ← traceSteps clear (PathContinuation.within entry.safe)
    sampleAt 0 first owner requests
  pure ()

/-- Materialize the same complete initial layer in its three production phases, sharing the actual continuation between
them. This diagnoses the initial source cost only; it does not replace the full observation test. -/
@[expose] def initialPhases : IO Unit := do
  let entry ← prepare
  let resolution := Accuracy.resolve entry.safe 1 (by decide) 1 (by decide)
  let started ← IO.monoMsNow
  report "square-factor phases: selecting and retaining the full checked continuation"
  let last := PathContinuation.last
  let mesh ← evaluate fun _ => PathContinuation.selectMesh entry.safe 0
    resolution.rootDiameter resolution.rootDiameterPositive resolution.minimumDepth
  let run := mesh.run
  let depth := mesh.depth
  unless resolution.minimumDepth ≤ depth ∧ run.stepCount = 2 ^ depth ∧
      run.endpoint.parameter = last.parameter do
    throw (IO.userError "initial-layer diagnostic did not retain the entire canonical request mesh")
  report
    s!"square-factor phases: continuation ready in {(← IO.monoMsNow) - started} ms; selected depth={depth}; \
      steps={run.stepCount}"
  let cellStart ← IO.monoMsNow
  report "square-factor phases: compiling the actual inherited cell models"
  let cells ← evaluate fun _ => OwnedCells.compileSubdivision run
  report s!"square-factor phases: {cells.length} cells ready in {(← IO.monoMsNow) - cellStart} ms"
  let model : Path.Basic.PathModel := ⟨cells.map (fun cell => cell.model.cell)⟩
  let sumStart ← IO.monoMsNow
  report "square-factor phases: summing the exact original-differential cell integrals"
  let sample ← evaluate fun _ => model.integralSample
  report
    s!"square-factor phases: sum ready in {(← IO.monoMsNow) - sumStart} ms; denominator bits=({sample.re.den.log2 + 1},\
      {sample.im.den.log2 + 1})"
  report "Initial-layer phases completed only; use observe for the actual nonempty output and replay."

/-- Time consecutive production refinements while retaining each actual parent layer. This isolates the expensive stage
without rerunning the initial source or guessing the observer's next refinement query. -/
@[expose] def refineLayers {p : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request} {prepared :
  SquareFactor.Prepared p request}
    {segment : PathInput.Segment} {data : PathInput.Data prepared segment} {safe : data.Safe} {index : Nat}
    (parent : IntegrationLayers.Layer safe index)
    (sampleFinal normFinal : Bool) : Nat → IO Unit
  | 0 => do
      if sampleFinal then
        report s!"square-factor refinement: summing final layer={index}; cells={parent.cells.length}"
        let started ← IO.monoMsNow
        let sample ← evaluate fun _ => parent.model.integralSample
        report
          s!"square-factor refinement: exact sum elapsed={(← IO.monoMsNow) - started} ms; denominator \
            bits=({sample.re.den.log2 + 1},{sample.im.den.log2 + 1})"
        if normFinal then
          report "square-factor norm: comparing unreduced displays at threshold one"
          let comparisonStarted ← IO.monoMsNow
          let comparisons ← evaluate fun _ =>
            let le := @decide (Data.Gaussian.Norm.Basic.normSq sample ≤ 1)
              (Comparison.decidableNormSqLE sample 1)
            let ge := @decide (1 ≤ Data.Gaussian.Norm.Basic.normSq sample)
              (Comparison.decidableLENormSq 1 sample)
            let lt := @decide (Data.Gaussian.Norm.Basic.normSq sample < 1)
              (Comparison.decidableNormSqLT sample 1)
            (le, ge, lt)
          report s!"square-factor norm: three raw comparisons elapsed={(← IO.monoMsNow) - comparisonStarted} ms"
          report "square-factor norm: evaluating from retained reducedness"
          let fastStarted ← IO.monoMsNow
          let fast ← evaluate fun _ => Comparison.normSqFromReduced sample
          report s!"square-factor norm: reduced-square elapsed={(← IO.monoMsNow) - fastStarted} ms"
          report "square-factor norm: evaluating ordinary exact squared norm"
          let referenceStarted ← IO.monoMsNow
          let reference ← evaluate fun _ => Data.Gaussian.Norm.Basic.normSq sample
          report s!"square-factor norm: reference elapsed={(← IO.monoMsNow) - referenceStarted} ms"
          unless fast = reference do throw (IO.userError "reduced-square norm changed the exact rational result")
          unless comparisons = (decide (reference ≤ 1), decide (1 ≤ reference), decide (reference < 1)) do
            throw (IO.userError "raw norm comparisons changed a numerical decision")
          report "square-factor norm: exact canonical numerator and denominator agree"
      report "Refinement diagnostic completed only; use observe for generated-run acceptance."
  | remaining + 1 => do
      report
        s!"square-factor refinement: starting layer={index + 1}; parent depth={parent.depth}; \
          cells={parent.cells.length}"
      let started ← IO.monoMsNow
      let next ← evaluate fun _ => Next.make parent
      let layer := next.layer
      unless parent.depth ≤ layer.depth ∧ layer.cells.length = 2 ^ layer.depth ∧
          layer.allowance < Geometric.Basic.quarterRadius 1 (index + 1) do
        throw (IO.userError "refinement lost its complete mesh or numerical target")
      report
        s!"square-factor refinement: layer={index + 1}; depth={layer.depth}; cells={layer.cells.length}; \
          elapsed={(← IO.monoMsNow) - started} ms"
      refineLayers layer sampleFinal normFinal remaining

/-- Build one retained initial layer and time consecutive production refinements from it. -/
@[expose] def refinementPhases (count : Nat) (sampleFinal : Bool := false) (normFinal : Bool := false) : IO Unit := do
  let entry ← prepare
  report "square-factor refinement: constructing the shared initial layer"
  let started ← IO.monoMsNow
  let layer ← evaluate fun _ => IntegrationLayers.initial entry.safe 0
  report
    s!"square-factor refinement: initial depth={layer.depth}; cells={layer.cells.length}; \
      elapsed={(← IO.monoMsNow) - started} ms"
  refineLayers layer sampleFinal normFinal count

/-- Retain exactly the first checked initial edge, avoiding a complete initial-layer build when profiling one inherited
child. -/
@[expose] def firstParent (entry : ObservationInput.PreparedEntry
    polynomial differential segment 0 .originalCoordinate) (parentDepth : Nat) :
    IO (OwnedCells.Cell entry.safe) := do
  let clear := PathContinuation.clearSegment entry.safe
  let first := PathContinuation.first
  let last := PathContinuation.last
  let resolution := Accuracy.resolve entry.safe 1 (by decide) 1 (by decide)
  let started ← IO.monoMsNow
  let owner ← evaluate fun _ => PathContinuation.initialOwner entry.safe 0
  let requests := (PreparedSheetContinuation.Subdivision.dyadicRequests parentDepth first last
    resolution.rootDiameter resolution.rootDiameterPositive).take 1
  let some run ← evaluate (fun _ => PreparedSheetContinuation.Subdivision.trySteps clear
      (PathContinuation.within entry.safe) first owner requests)
    | throw (IO.userError "first parent edge rejected at the displayed diagnostic depth")
  let cells ← evaluate fun _ => OwnedCells.compileSubdivision run
  let some parent := cells.head? | throw (IO.userError "first-parent diagnostic produced no cell")
  report s!"square-factor child: first parent ready in {(← IO.monoMsNow) - started} ms; parent depth={parentDepth}"
  pure parent

/-- Isolate the first parent's exact child preparation and centre costs. The parent is the actual first checked edge of
the displayed initial mesh; this deliberately diagnoses one block, not a complete path observation. -/
@[expose] def childPhases (parentDepth index : Nat) : IO Unit := do
  let entry ← prepare
  let parent ← firstParent entry parentDepth
  let first := PathContinuation.first
  let last := PathContinuation.last
  let target := Geometric.Basic.quarterRadius 1 index
  let resolution := Accuracy.resolve entry.safe 1 (by decide)
    target (Geometric.Basic.quarterRadius_pos (by decide) index)
  let minimum := resolution.minimumDepth - parentDepth
  let maximum := UniformRefinement.maximumAdditionalDepth
    resolution.rootDiameter minimum [parent]
  for offset in List.range (maximum + 1 - minimum) do
    let depth := minimum + offset
    let preparedStart ← IO.monoMsNow
    report s!"square-factor child: checking layer={index}; additional depth={depth}"
    let mesh ← evaluate fun _ => ChildMeshes.tryBuild parent
      resolution.rootDiameter resolution.rootDiameterPositive depth first last (by decide)
    report s!"square-factor child: accepted={mesh.isSome}; preparation elapsed={(← IO.monoMsNow) - preparedStart} ms"
    match mesh with
    | none => pure ()
    | some mesh =>
        let cellStart ← IO.monoMsNow
        let block ← evaluate fun _ => ChildMeshes.compile mesh
        report s!"square-factor child: centres elapsed={(← IO.monoMsNow) - cellStart} ms; cells={block.cells.length}"
        report "One first-parent diagnostic only; use observe for generated-run acceptance."
        return
  throw (IO.userError "first-parent checker rejected its proved sufficient depth")

/-- Time the inherited owner, checked diameter proposal, uniform fallback and production preparation separately. These
are diagnostics of the same child request, not alternative evidence supplied to the public constructor. -/
@[expose] def childPreparation {p : SquareFactor.GaussianPolynomial} {request : SquareFactor.Request} {prepared :
  SquareFactor.Prepared p request}
    {segment : PathInput.Segment} {data : PathInput.Data prepared segment} {safe : data.Safe}
    (parent : OwnedCells.Cell safe)
    (left right : ClearSheetContinuation.Subdivision.Endpoint)
    (diameter : PathInput.Coordinate) (positive : 0 < diameter) : IO Unit := do
  let clear := PathContinuation.clearSegment safe
  let current := ChildCells.endpointAt parent left
  let step := ChildCells.childRequest parent right diameter positive
  let variation := ClearSheetContinuation.variationBound clear
    current.parameter step.endpoint.parameter
  report s!"square-factor preparation: child fractions=[{fractionText left.parameter},{fractionText right.parameter}]"
  let ownerStart ← IO.monoMsNow
  let owner ← evaluate fun _ => parent.edge.ownerAt left.parameter left.inside
  report s!"square-factor preparation: inherited owner elapsed={(← IO.monoMsNow) - ownerStart} ms"
  let ready ← evaluate fun _ => decide (PreparedSheetContinuation.AlreadyPrepared clear current owner step)
  report
    s!"square-factor preparation: ready={ready}; carries={decide (variation < owner.track.initial.clearance.bound)}"
  let checkedStart ← IO.monoMsNow
  let checked ← evaluate fun _ => CheckedSquareRootPreparation.attempt clear current.parameter owner diameter
  report
    s!"square-factor preparation: diameter proposal elapsed={(← IO.monoMsNow) - checkedStart} ms; \
      accepted={(checked.value clear current.parameter owner diameter).isSome}"
  match checked.outcome with
  | .error failure =>
      report s!"square-factor preparation: retained warmup={failure.warmup.steps.length}/2; \
        search={failure.steps.length}/6"
      match failure.reason with
      | .search .. =>
          match checked.search.finished with
          | .accepted .. => report "square-factor preparation: search certificate unavailable"
          | .exhausted .. => report "square-factor preparation: finite search budget exhausted"
          | .zeroDerivative .. => report "square-factor preparation: rejected center has zero derivative"
      | .candidate _ _ _ miss =>
          match miss with
          | .diameter _ => report "square-factor preparation: candidate fails requested diameter"
          | .clearance _ _ => report "square-factor preparation: diameter passes; predicted clearance fails"
          | .ambient _ _ _ => report "square-factor preparation: diameter and clearance pass; ambient fails"
  | .ok checked =>
      report
        s!"square-factor preparation: diameter proposal \
          carries={decide (variation < checked.value.track.initial.clearance.bound)}"
  let sampleStart ← IO.monoMsNow
  let sample ← evaluate fun _ => UniformSquareRootPreparation.sampleCandidates clear owner diameter
  report
    s!"square-factor preparation: sample proposals elapsed={(← IO.monoMsNow) - sampleStart} ms; \
      accepted={sample.isSome}"
  let restartStart ← IO.monoMsNow
  let restart ← evaluate fun _ => UniformSquareRootPreparation.restartInput clear
    current.parameter current.inside owner diameter positive
  report
    s!"square-factor preparation: restart input elapsed={(← IO.monoMsNow) - restartStart} ms; center denominator \
      bits=({restart.source.anchor.re.den.log2 + 1},{restart.source.anchor.im.den.log2 + 1})"
  let eliminationStart ← IO.monoMsNow
  let elimination ← evaluate fun _ => (SquareRootReconditioning.isolationInput owner.parameterNonzero).elimination
  report
    s!"square-factor preparation: generic axis elimination elapsed={(← IO.monoMsNow) - eliminationStart} ms; \
      coefficients={elimination.vertical.coeffs.length}"
  let quadraticStart ← IO.monoMsNow
  let quadratic ← evaluate fun _ => QuadraticAxisElimination.quadraticAxisElimination
    (data.radicand.parameterPolynomial.eval (clear.pointAt current.parameter))
  report
    s!"square-factor preparation: quadratic axis elimination elapsed={(← IO.monoMsNow) - quadraticStart} ms; \
      coefficients={quadratic.vertical.coeffs.length}"
  let uniformStart ← IO.monoMsNow
  let uniform ← evaluate fun _ => UniformSquareRootPreparation.prepared clear
    current.parameter current.inside owner diameter positive
  report s!"square-factor preparation: uniform elapsed={(← IO.monoMsNow) - uniformStart} ms"
  let sharpStart ← IO.monoMsNow
  let sharp ← evaluate fun _ => QuadraticCoefficientClearance.strengthen uniform
  report
    s!"square-factor preparation: sharpen elapsed={(← IO.monoMsNow) - sharpStart} ms; \
      carries={decide (variation < sharp.track.initial.clearance.bound)}"
  let canonicalStart ← IO.monoMsNow
  let canonical ← evaluate fun _ => PreparedSheetContinuation.CachedSource.canonical clear current owner step
  report
    s!"square-factor preparation: production elapsed={(← IO.monoMsNow) - canonicalStart} ms; \
      carries={decide (variation < canonical.preparedOwner.track.initial.clearance.bound)}"

/-- Inspect the two exact child requests of the retained first parent at the requested layer. -/
@[expose] def preparationPhases (parentDepth index : Nat) : IO Unit := do
  let entry ← prepare
  let parent ← firstParent entry parentDepth
  let first := PathContinuation.first
  let last := PathContinuation.last
  let middle := ChildMeshes.midpoint first last
  let resolution := Accuracy.resolve entry.safe 1 (by decide)
    (Geometric.Basic.quarterRadius 1 index) (Geometric.Basic.quarterRadius_pos (by decide) index)
  childPreparation parent first middle resolution.rootDiameter resolution.rootDiameterPositive
  childPreparation parent middle last resolution.rootDiameter resolution.rootDiameterPositive
  report "Preparation diagnostics only; use observe for generated-run acceptance."

/-- Run a nonempty original-differential observation and verify its exact source-free replay.

Check complete machine and selected model data, requested output length and both enclosure bounds. -/
@[expose] def observe (count : Nat) : IO Unit := do
  unless 0 < count do throw (IO.userError "acceptance observation must emit a nonempty prefix")
  let entry ← prepare
  report s!"square-factor: starting actual original-differential observation, bits={count}"
  let started ← IO.monoMsNow
  report "square-factor: forcing the shared original-differential source"
  let source ← evaluate fun _ => entry.source
  report
    s!"square-factor: shared source ready in {(← IO.monoMsNow) - started} ms; error \
      scale={fractionText source.value.errorScale}"
  let observed ← evaluate fun _ =>
    PolynomialObservation.observePrepared entry policy query count
  let selected ← evaluate fun _ => observed.recorded.observation
  let preparedRequest ← evaluate fun _ => observed.preparedRequest
  report s!"square-factor: observed in {(← IO.monoMsNow) - started} ms; word={selected.word}"
  let replayed ← evaluate fun _ => Integration.Program.Gaussian.CCL.Replay.Observation.Transcript.replay
    (IntegrationReplay.control (PathObservation.program entry.source policy))
    query count observed.recorded.trace
  match replayed with
  | .error _ => throw (IO.userError "actual receipt failed source-free replay")
  | .ok replayed =>
      unless replayed.machine == selected.machine && replayed.selected.index == preparedRequest.index &&
          replayed.selected.sample == preparedRequest.cache.sample &&
          replayed.selected.allowance == preparedRequest.cache.allowance &&
          replayed.selected.ball.center == preparedRequest.cache.sample &&
          replayed.selected.ball.radiusSq == preparedRequest.radiusSq && replayed.word.length == count &&
          decide (replayed.selected.ball.radiusSq < query.target ∧ replayed.selected.allowance < query.target) do
        throw (IO.userError "actual original-differential observation failed its numerical/replay checks")
      report s!"square-factor: replay and accuracy passed; queries={observed.recorded.trace.map (·.query)}"

/-- Acquire only the queries requested by the actual source-free replay protocol. This diagnostic exposes expensive
refinement stages without guessing the adaptive query sequence. Its finite acquisition budget is not an argument of the
public observation constructor. -/
@[expose] def acquire (program : Cached.Basic.CachedProgram) (count : Nat) :
    Nat → IntegrationReplay.Trace → IO Unit
  | remaining, trace => do
      let control := IntegrationReplay.control program
      match Integration.Program.Gaussian.CCL.Replay.Observation.Transcript.replay control query count trace with
      | .ok observation =>
          unless observation.word.length = count ∧ observation.selected.ball.radiusSq < query.target ∧
              observation.selected.allowance < query.target do
            throw (IO.userError "acquired replay failed the original observation request")
          report s!"square-factor acquired: word={observation.word}; queries={trace.map (·.query)}"
          report "Diagnostic acquisition completed only; use observe for generated-run acceptance."
      | .error (.transcript (.missing index)) =>
          match remaining with
          | 0 => throw (IO.userError
            s!"diagnostic reply budget exhausted before query {index}; no non-certifiability conclusion")
          | remaining + 1 =>
              report s!"square-factor acquired: requesting query={index}; source index={policy.schedule.index index}"
              let started ← IO.monoMsNow
              let reply ← evaluate fun _ => program.stage index
              report
                s!"square-factor acquired: query={index}; cells={reply.model.cells.length}; \
                  elapsed={(← IO.monoMsNow) - started} ms; sample denominator bits=({reply.sample.re.den.log2 + 1},\
                  {reply.sample.im.den.log2 + 1})"
              acquire program count remaining (trace ++ [⟨index, reply⟩])
      | .error _ => throw (IO.userError "source-supplied reply failed replay validation")

/-- Acquire only the adaptive queries requested by the actual replay protocol within a finite reply budget. -/
@[expose] def queryPhases (count replyBudget : Nat) : IO Unit := do
  unless 0 < count do throw (IO.userError "diagnostic observation must request a nonempty prefix")
  let entry ← prepare
  report "square-factor acquired: forcing the shared original-differential source"
  let started ← IO.monoMsNow
  let source ← evaluate fun _ => entry.source
  let program ← evaluate fun _ => PathObservation.program source policy
  report s!"square-factor acquired: source ready in {(← IO.monoMsNow) - started} ms"
  acquire program count replyBudget []

end SquareFactorObservationHarness

/-- Parse the requested square-factor preparation, refinement, observation or replay diagnostic mode. -/
@[expose] def main (arguments : List String) : IO Unit :=
  match arguments with
  | ["budget"] => SquareFactorObservationHarness.budget 0
  | ["budget", index] =>
      match Purelib.Data.String.toNat? index with
      | some index => SquareFactorObservationHarness.budget index
      | none => throw (IO.userError "layer index must be a natural number")
  | ["seed"] => SquareFactorObservationHarness.seed
  | ["first-edges"] => SquareFactorObservationHarness.firstEdges
  | ["initial-phases"] => SquareFactorObservationHarness.initialPhases
  | ["refinement-phases", count] =>
      match Purelib.Data.String.toNat? count with
      | some count => SquareFactorObservationHarness.refinementPhases count
      | none => throw (IO.userError "refinement count must be a natural number")
  | ["refinement-sample-phases", count] =>
      match Purelib.Data.String.toNat? count with
      | some count => SquareFactorObservationHarness.refinementPhases count true
      | none => throw (IO.userError "refinement count must be a natural number")
  | ["refinement-norm-phases", count] =>
      match Purelib.Data.String.toNat? count with
      | some count => SquareFactorObservationHarness.refinementPhases count true true
      | none => throw (IO.userError "refinement count must be a natural number")
  | ["child-phases", depth, index] =>
      match Purelib.Data.String.toNat? depth, Purelib.Data.String.toNat? index with
      | some depth, some index => SquareFactorObservationHarness.childPhases depth index
      | _, _ => throw (IO.userError "parent depth and layer index must be natural numbers")
  | ["preparation-phases", depth, index] =>
      match Purelib.Data.String.toNat? depth, Purelib.Data.String.toNat? index with
      | some depth, some index => SquareFactorObservationHarness.preparationPhases depth index
      | _, _ => throw (IO.userError "parent depth and layer index must be natural numbers")
  | ["observe", count] =>
      match Purelib.Data.String.toNat? count with
      | some count => SquareFactorObservationHarness.observe count
      | none => throw (IO.userError "count must be a natural number")
  | ["query-phases", count, budget] =>
      match Purelib.Data.String.toNat? count, Purelib.Data.String.toNat? budget with
      | some count, some budget => SquareFactorObservationHarness.queryPhases count budget
      | _, _ => throw (IO.userError "count and diagnostic reply budget must be natural numbers")
  | ["mesh", depth] =>
      match Purelib.Data.String.toNat? depth with
      | some depth => SquareFactorObservationHarness.mesh depth
      | none => throw (IO.userError "depth must be a natural number")
  | ["trace", depth] =>
      match Purelib.Data.String.toNat? depth with
      | some depth => SquareFactorObservationHarness.trace depth
      | none => throw (IO.userError "depth must be a natural number")
  | ["sample", depth, index] =>
      match Purelib.Data.String.toNat? depth, Purelib.Data.String.toNat? index with
      | some depth, some index => SquareFactorObservationHarness.trace depth (some index)
      | _, _ => throw (IO.userError "depth and sample step must be natural numbers")
  | _ => throw (IO.userError
    "usage: square_factor_observation_harness budget [LAYER] | seed | first-edges | initial-phases | refinement-phases \
      LAYERS | refinement-sample-phases LAYERS | refinement-norm-phases LAYERS | child-phases PARENT_DEPTH LAYER | \
      preparation-phases PARENT_DEPTH LAYER | observe BIT_COUNT | query-phases BIT_COUNT REPLY_BUDGET | mesh DEPTH | \
      trace DEPTH | sample DEPTH STEP")
