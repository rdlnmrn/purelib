module

public import Purelib.Data.List.ToString
public import Purelib.Data.Prod.Basic

import Purelib.Data.Int.Decimal

import Purelib.Data.Range

import Purelib.Data.List.Control
import Purelib.Data.List.Map

meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.System.IO
import Purelib.System.FilePath
import Purelib.Data.String.Parsing

import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import scripts.checkpoint.Integration
import scripts.checkpoint.RootRefinement
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PreparedRootSafePeriodPrograms
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Surface.PreparedCycleReplay.Readiness
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Riemann.Periods.PeriodPolicies
public import Purelib.Riemann.Periods.PolynomialPeriodInput
public import Purelib.Riemann.Periods.PreparedRootClosedPeriodBank
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Transport.PreparedDeferredRecipeReplay
import Purelib.Riemann.Transport.PreparedDirectRefinementReplay

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchCutRepresentatives
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodBank
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay
import Purelib.Riemann.Periods.PolynomialPeriodObservation
import Purelib.Riemann.Topology.PreparedCycleReplay
public import Purelib.Riemann.RootContinuation.PreparedInitialRootReplay
public import Purelib.Curves.Hyperelliptic.Branches.BranchIsolationReplay
import Purelib.Riemann.Topology.PreparedCycleSeedReplay
public import scripts.checkpoint.Integration.Import
import scripts.checkpoint.RootState
import scripts.checkpoint.Center
import scripts.checkpoint.InitialExtraction
public import scripts.checkpoint.SquareRootFamily
public import scripts.checkpoint.PreparedCycle
public import scripts.checkpoint.PreparedCenter
import Init.Core
import Init.Data.Fin.Basic
import Init.Data.List.Lemmas
import Init.Data.List.OfFn
import Init.Data.Repr
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Integration.Preparation.Roots.PreparedRootSafeReplay.Restoration
import Purelib.Curves.Hyperelliptic.Preparation.Polynomial
import Purelib.Data.Gaussian.Field
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Cached.Allocation
import Purelib.Integration.Program.Gaussian.Cached.Policy
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Pair.Cover.Prepare
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Components
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedTraceClearance
import Purelib.Riemann.Periods.PeriodReplay
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.PreparedRootSafeAccuracy
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.RootContinuation.SquareRootOwnerFamily
import Purelib.RootIsolation.Exact.Basic
import Purelib.RootIsolation.Exact.LargeSquare
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Tactic.QuotientFreeOmega

-- Use complete constructor eliminators for the original match arms.
set_option backward.match.sparseCases false

open Purelib

open Purelib.Approximation

open Purelib.CCL.Progressive

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Geometry

open Purelib.Geometry.Path.Gaussian

open Purelib.Integration

open Purelib.RootIsolation

open Purelib.Polynomial

open Purelib.Data (Json)
open scoped Purelib.Data.String Purelib.Data.List Purelib.Data.Range
open Purelib.Data.Json (toJson)

public section

/-!
Acceptance diagnostics for the coefficient-first normalized standard-period
constructor.  The raw equation is `y² = x²(x³+1)`, with a computed cubic
reduced radicand and genus one.  The current multiplicity basis returns
`s=2x` and `q=(x³+1)/4`; no monic-square-factor convention is assumed.
This explicitly requests the reduced standard differential `dx/z` on
`z²=q`, not the original differential `dx/y`; the
original-coordinate path test lives in `SquareFactorObservationHarness`.

No genus, squarefreeness, branch-isolation or period certificate is supplied
by this harness.  Input mode checks only the computed algebraic preparation.
Observation mode must emit a nonempty prefix and replay the actual receipt.
It checkpoints individual cells of every requested model before aggregate
integration, then saves checked replies, query order, the receipt and profiles.
Canonical refinement states are retained across queries, with each successor's
input snapshots, selection and materialization recorded separately.  Checked
ordered extraction traces restore the exact original branch family.  The
old raw-tour bank and initial-centre loaders remain available for diagnostics
only; they are not used to acquire corrected observations. The corrected
ordered grid/centering acquisition does not yet have a disk-backed restore
boundary. Do not start long corrected observation runs until that recovery
path is implemented and restart-tested. Branch replay still performs winding
and clearance checks and may reuse an explicitly supplied older branch store.
Fresh generation is compared with the original complete runner using a proved
in-memory source cache.  Disk-only replay checks the finite numerical artifact;
it does not infer curve ownership from a filename or manifest.
Use an explicit SIGKILL timeout and systemd memory bound for runtime probes;
these measurements do not replace the universal proofs or repository gates.
-/

open Purelib.Riemann.RootContinuation

namespace PolynomialPeriodObservationHarness

variable {Result : Type}

open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial ->
  GaussianPolynomial
open Purelib.Riemann.Periods.PolynomialPeriodInput (Side Selection PreparedEntry)

/-- The stored Gaussian coefficient fixture with cubic value X cubed plus one and two trailing zeros. -/
@[expose] def polynomial : GaussianPolynomial := ⟨[1, 0, 0, 1, 0, 0]⟩
/-- Select cycle zero and differential zero on the requested standard-period side. -/
@[expose] def selection (side : Side) : Selection := ⟨side, 0, 0⟩
/-- The fixed observation schedule and finite query-allocation policy. -/
@[expose] def policy : Riemann.Periods.PeriodPolicies.Policy := ⟨⟨0, 0⟩, ⟨4, [4]⟩⟩
/-- The initial observation request with current index zero and target one. -/
@[expose] def request : Riemann.Periods.PeriodPolicies.Request := ⟨0, 1, by decide⟩

/-- Print and flush one period-observation diagnostic message. -/
@[expose] def report (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Evaluate a thunk through IO without inlining its timing boundary. -/
@[expose, noinline] def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

open scoped Purelib.Data.Int.Decimal in
/-- Render every exact real and imaginary polynomial coefficient as numerator/denominator pairs. -/
@[expose] def coefficientText (polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) : String :=
  letI : Repr (Int × Nat) := ⟨Purelib.Data.Prod.repr⟩
  letI : Repr ((Int × Nat) × (Int × Nat)) := ⟨Purelib.Data.Prod.repr⟩
  letI : Repr (List ((Int × Nat) × (Int × Nat))) := ⟨Purelib.Data.List.repr⟩
  reprStr (polynomial.coeffs.map fun value =>
    ((value.re.num, value.re.den), (value.im.num, value.im.den)))

/-- Check the internally generated reduction before forcing canonical branch isolation or the selected period's
numerical program. -/
@[expose] def withPrepared (side : Side)
    (use : PreparedEntry polynomial (selection side) → IO Unit) : IO Unit := do
  let started ← IO.monoMsNow
  report s!"normalized period {repr side}: preparing raw repeated-factor coefficients"
  let prepared := Riemann.Periods.PolynomialPeriodInput.prepare polynomial (selection side)
  match prepared with
  | .error _ => throw (IO.userError "valid reduced standard-period input was rejected")
  | .ok entry =>
      report
        s!"normalized period: computed genus={entry.prepared.genus}; \
          s={coefficientText entry.prepared.reduction.squareFactor}; \
          q={coefficientText entry.prepared.reduction.radicand}"
      let reduction := entry.prepared.reduction
      unless entry.prepared.genus = 1 ∧
          reduction.radicand.natDegree = 3 ∧ reduction.squareFactor.natDegree = 1 ∧
          (reduction.squareFactor * reduction.squareFactor * reduction.radicand).normalize = polynomial.normalize do
        throw (IO.userError "computed reduction failed degree/genus or exact reconstruction checks")
      report
        s!"normalized period: input accepted in {(← IO.monoMsNow) - started} ms; exact p=s²q reconstruction checked; \
          genus=1"
      use entry

/-- Check the coefficient-first preparation boundary without evaluating a numerical period. -/
@[expose] def input (side : Side) : IO Unit :=
  withPrepared side fun _ =>
    report "Input boundary checked only; no numerical period observation was evaluated."

/-- Restore the original branch family from checked ordered extraction traces. Numerical validation and the full
branch-interface equation remain separate; the continuation receives both, with no guessed source identity. -/
@[expose] def withCanonicalBranches {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (directory : System.FilePath)
    (use : (branches : Branches.BranchIsolation.Data prepared.prepared.curve) →
      branches = Branches.BranchIsolation.data prepared.prepared.curve → IO Unit)
    (savedOnly : Bool := false) : IO Unit := do
  let action : RootRefinementCheckpoint.Execution Unit := do
    IO.FS.createDirAll directory
    let curve := prepared.prepared.curve
    let higher := Branches.BranchCutLifts.degreeGtOne_of_cycleIndex curve
      (⟨0, prepared.bounds.cycle_lt⟩ : Fin prepared.prepared.genus)
    let source := Branches.BranchIsolationReplay.input curve higher
    let control ← RootRefinementCheckpoint.Control.create savedOnly
    IntegrationCheckpoint.profile directory
      "BEGIN canonical branch extraction checkpoints; original winding and clearance data checked"
    let result ← InitialExtractionCheckpoint.isolateLargeSquare source.elimination
      (.separated ⟨control.savedOnly, pure ()⟩ _ source.nonzero source.degreePositive)
      source.degreeAtLeastTwo source.squarefree
      control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("branches"))))
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("branch-proposal-counts.json")))) (← RootRefinementCheckpoint.Execution.counts)
    let branches := Branches.BranchIsolationReplay.data curve higher result.val
    have same : branches = Branches.BranchIsolation.data curve :=
      Branches.BranchIsolationReplay.data_eq curve higher result.val result.property
    IntegrationCheckpoint.profile directory
      "END exact canonical branch reconstruction; ordered source association proved"
    use branches same
  let (result, _) ← RootRefinementCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

/-- Compare the actual trace movement requirement with the universal preparation floor, without allocating any mesh or
acquiring root owners. -/
@[expose] def traceBudgetRows {polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Rational.Box} :
    {start finish : Data.Gaussian.Basic.Canonical} →
    Polynomial.Geometry.ClearPath polynomial ambient start finish → Nat → List Json
  | _, _, .nil _, _ => []
  | _, _, .cons segment remaining, index =>
      let budget := Riemann.Paths.PreparedTraceBudget.build segment
        Riemann.Paths.PreparedClearPathModels.zeroEndpoint Riemann.Paths.PreparedClearPathModels.oneEndpoint
      let movementDepth := Rational.Geometric.Search.firstQuarterBelow budget.variation 0 budget.movementBudget
      Json.mkObj
        [("segment", toJson index),
         ("start", toJson (IntegrationCheckpoint.gaussianData (segment.pointAt 0))),
         ("finish", toJson (IntegrationCheckpoint.gaussianData (segment.pointAt 1))),
         ("segmentClearance", toJson (IntegrationCheckpoint.fractionData segment.clearanceBound)),
         ("coveredCoordinateFloor", toJson (IntegrationCheckpoint.fractionData budget.clearance.cover.coordinateFloor)),
         ("coveredNormFloor", toJson (IntegrationCheckpoint.fractionData budget.clearance.cover.normFloor)),
         ("rootNormLower", toJson (IntegrationCheckpoint.fractionData budget.lower)),
         ("rootDiameter", toJson (IntegrationCheckpoint.fractionData budget.rootDiameter)),
         ("variation", toJson (IntegrationCheckpoint.fractionData budget.variation)),
         ("movementBudget", toJson (IntegrationCheckpoint.fractionData budget.movementBudget)),
         ("universalClearanceFloor", toJson (IntegrationCheckpoint.fractionData budget.clearanceFloor)),
         ("preparationFloorDepth", toJson budget.depth),
         ("tracedFallbackMinimumDepth", toJson movementDepth),
         ("tracedFallbackRequestsPerSegment", toJson (2 ^ movementDepth)),
         ("movementDepth", toJson movementDepth),
         ("movementRequestsPerSegment", toJson (2 ^ movementDepth)),
         ("scope", toJson
           "traced fallback only; the ordinary endpoint-return construction starts its bank search at depth zero")]
        :: traceBudgetRows remaining (index + 1)

open scoped Purelib.Data.List in
/-- Inspect the exact canonical A-cycle's root-trace budgets before allocating any bank or coefficient model. Saved
branch generators are forbidden; the resulting comparison does not change the canonical source. -/
@[expose] def preparationPhases (directory : System.FilePath :=
    ".lake/period-checkpoints/canonical-banks-actual-20260908-01") : IO Unit :=
  withPrepared .a fun prepared =>
    withCanonicalBranches prepared directory (fun restored _ => do
    let curve := prepared.prepared.curve
    let cycle : Fin prepared.prepared.genus := ⟨0, prepared.bounds.cycle_lt⟩
    let branchesCache : Thunk (Branches.BranchIsolation.Data curve) :=
      ⟨fun _ => restored⟩
    report "normalized phases: projecting restored branches with the computed curve's own certificate"
    let branchStarted ← IO.monoMsNow
    let anchors ← evaluate fun _ =>
      let branches := branchesCache.get
      List.ofFn fun index : Fin branches.siteCount =>
        let anchor := branches.anchorAt index
        (anchor.re.num.natAbs.log2 + 1, anchor.re.den.log2 + 1,
          anchor.im.num.natAbs.log2 + 1, anchor.im.den.log2 + 1)
    report
      s!"normalized phases: {anchors.length} canonical branches in {(← IO.monoMsNow) - branchStarted} ms; anchor bit \
        sizes={anchors}"
    let branches := branchesCache.get
    let higher := Branches.BranchCutLifts.degreeGtOne_of_cycleIndex curve cycle
    report "normalized phases: constructing the canonical branch configuration"
    let geometryBranches := (Branches.BranchConfiguration.configurationOfData curve branches).branches
    let left := Branches.BranchConfiguration.basisPairLeftIndexOfData curve branches cycle
    let right := Branches.BranchConfiguration.basisPairRightIndexOfData curve branches cycle
    let connectorCache := Thunk.mk fun _ =>
      Branches.Cuts.connectorAt geometryBranches higher left right 0
    let leftStateCache := Thunk.mk fun _ => Branches.Cuts.refinedState geometryBranches higher left 0
    let rightStateCache := Thunk.mk fun _ => Branches.Cuts.refinedState geometryBranches higher right 0
    let paths : List (String × List Json) :=
      [("forward", traceBudgetRows connectorCache.get 0),
       ("right", traceBudgetRows (Branches.BranchCutLifts.ownerBoundaryPath rightStateCache.get) 0),
       ("backward", traceBudgetRows (Branches.BranchCutLifts.ClearPath.reverse connectorCache.get) 0),
       ("left", traceBudgetRows (Branches.BranchCutLifts.ownerBoundaryPath leftStateCache.get) 0)]
    for (label, rows) in paths do
      IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
        (s!"trace-budget-v3-margin-{label}.json")))) rows
      for row in rows do report s!"{label}: {row.compress}"
    report "Exact trace budgets saved; no bank allocated and no changed-source equality claimed.") true

/-- The side-specific directory for corrected ordered period observations. -/
@[expose] def checkpointDirectory (side : Side) : System.FilePath :=
  .mk s!".lake/period-checkpoints/ordered-corrected-{if side == .a then "a" else "b"}"

/-- The ordinary joined-bank construction is unchanged from v4. Its exact request and source checks preserve those
completed banks across this update. -/
@[expose] def ordinaryBankDirectory (directory : System.FilePath) : System.FilePath :=
  (Purelib.System.FilePath.join (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory
    (System.FilePath.mk ("checked-return-v4"))) (System.FilePath.mk ("banks"))) (System.FilePath.mk ("ordinary")))

/-- Closure now permits one common root box. Preserve earlier closure and centring artifacts separately from this new
canonical source. -/
@[expose] def closedCycleDirectory (directory : System.FilePath) : System.FilePath :=
  (Purelib.System.FilePath.join directory (System.FilePath.mk ("checked-return-v5")))

set_option genInjectivity false in
/-- An evaluated value retaining equality to the exact supplied specification. -/
structure Materialized {α : Type} (specification : α) where
  /-- The evaluated result retained for later reuse. -/ value : α
  /-- The retained value equals the original specification. -/ equal : value = specification

constructive_injectivity Materialized

/-- Evaluate one named computation once, retaining its specification equation and timing boundaries. -/
@[expose] def materialize {α : Type} (directory : System.FilePath) (label : String)
    (work : Unit → α) : IO (Materialized (work ())) := do
  IntegrationCheckpoint.profile directory s!"BEGIN {label}"
  let result ← evaluate fun _ => (⟨work (), rfl⟩ : Materialized (work ()))
  IntegrationCheckpoint.profile directory s!"END {label}"
  pure result

/-- Select the original A or B owner-closed standard tour from the retained branch family. -/
@[expose] def cycleTour {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (branches : Branches.BranchIsolation.Data prepared.prepared.curve) :
    Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath prepared.prepared.curve :=
  let cycle : Fin prepared.prepared.genus := ⟨0, prepared.bounds.cycle_lt⟩
  let pair := Riemann.Integration.PreparedOwnerClosedBridges.OwnerClosedCyclePair.ofData prepared.prepared.curve
    branches cycle
  if side == .a then pair.aTour else pair.bTour

/-- Read the finite-cut cycle data of the selected original standard tour. -/
@[expose] def cycleData {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (branches : Branches.BranchIsolation.Data prepared.prepared.curve) :
    Riemann.Topology.PreparedCycleModels.PreparedCycleData prepared.prepared.curve :=
  .finiteCut (cycleTour prepared branches).joined.data

/-- Restore sequentially joined standard-tour banks from the original branch family. Old independent-bank artifacts are
retained, but only exact request matches may be reused for the new root-closed source. -/
@[expose] def withClosedTour {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (branches : Branches.BranchIsolation.Data prepared.prepared.curve)
    (directory : System.FilePath)
    (use : (tour : Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath prepared.prepared.curve) →
      tour = cycleTour prepared branches →
      SquareRoot.Replay.QuadraticTrackReplay.Ready tour.joined.data.forwardOwner → IO Unit)
    (savedOnly : Bool := false) : IO Unit := do
  let action : RootRefinementCheckpoint.Execution Unit := do
    let curve := prepared.prepared.curve
    let cycle : Fin prepared.prepared.genus := ⟨0, prepared.bounds.cycle_lt⟩
    let higher := Branches.BranchCutLifts.degreeGtOne_of_cycleIndex curve cycle
    let geometry := (Branches.BranchConfiguration.configurationOfData curve branches).branches
    let left := Branches.BranchConfiguration.basisPairLeftIndexOfData curve branches cycle
    let right := if side == .a then
        Branches.BranchConfiguration.basisPairRightIndexOfData curve branches cycle
      else Branches.BranchCutRepresentatives.BranchConfiguration.pairLeftIndexOfData curve branches (Fin.last
        prepared.prepared.genus)
    let control ← RootRefinementCheckpoint.Control.create savedOnly
    SquareRootFamilyCheckpoint.withFamily
      (Branches.Cuts.connectorAt_start_eval_ne_zero geometry higher left right 0)
      control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("endpoint-left")))) fun leftFamily =>
      RootClosedCycleCheckpoint.withBoundary
        (Branches.Cuts.refinedState geometry higher left 0)
        (Branches.Cuts.refinedState geometry higher right 0)
        (Branches.Cuts.connectorAt geometry higher left right 0)
        (Branches.Cuts.connectorAt_withinAmbient geometry higher left right 0)
        (leftFamily.owner 0) control (ordinaryBankDirectory directory) (closedCycleDirectory
          (Purelib.System.FilePath.join directory (System.FilePath.mk ("banks")))) fun tour equal => do
        have same : tour = cycleTour prepared branches := by
          rw [equal, leftFamily.owner_eq_independent 0]
          cases side <;> rfl
        have ready : SquareRoot.Replay.QuadraticTrackReplay.Ready tour.joined.data.forwardOwner := by
          rw [equal]
          have retained := Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath.total_initialOwner
            (Branches.Cuts.refinedState geometry higher left 0)
            (Branches.Cuts.refinedState geometry higher right 0)
            (Branches.Cuts.connectorAt geometry higher left right 0)
            (Branches.Cuts.connectorAt_withinAmbient geometry higher left right 0)
            (leftFamily.owner 0)
          have law := congrArg (fun packed : (parameter : Data.Gaussian.Basic.Canonical) ×
              Riemann.Topology.SquareRootContinuationChain.Owner parameter =>
            SquareRoot.Replay.QuadraticTrackReplay.Ready packed.2) retained
          exact law.mpr (SquareRoot.Replay.QuadraticTrackReplay.family leftFamily 0)
        use tour same ready
  let (result, _) ← RootRefinementCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

/-- Restore the original joined cycle data and its readiness with exact source equality. -/
@[expose] def withCycleData {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (branches : Branches.BranchIsolation.Data prepared.prepared.curve)
    (directory : System.FilePath)
    (use : (data : Thunk (Riemann.Topology.PreparedCycleModels.PreparedCycleData prepared.prepared.curve)) →
      data.get = cycleData prepared branches → Integration.Surface.PreparedCycleReplay.Readiness.CycleReady
        prepared.prepared.curve data.get →
      IO Unit) (savedOnly : Bool := false) : IO Unit :=
  withClosedTour prepared branches directory (savedOnly := savedOnly) fun tour same ready =>
    use (Thunk.mk fun _ => .finiteCut tour.joined.data)
      (congrArg (fun tour : Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath prepared.prepared.curve =>
        Riemann.Topology.PreparedCycleModels.PreparedCycleData.finiteCut tour.joined.data) same)
      (RootClosedCycleCheckpoint.ready tour ready)

/-- Reach the real prepared-cycle checkpoint boundary without centring or model generation. Replay mode forbids every
new diameter/isolation proposal. Every consumed checkpoint is checked against its exact canonical request. -/
@[expose] def cyclePhases (side : Side) (directory : System.FilePath) (savedOnly : Bool) : IO Unit :=
  withPrepared side fun prepared =>
    withCanonicalBranches prepared directory (savedOnly := savedOnly) fun branches _ =>
      withCycleData prepared branches directory (savedOnly := savedOnly) fun data _ _ => do
        let count := Riemann.Integration.PreparedSwitchedRefinements.cycleSourceParentCount data.get
        IntegrationCheckpoint.saveJson (closedCycleDirectory (Purelib.System.FilePath.join directory (System.FilePath.mk
          ("completed-cycle-preparation.json"))))
          ("exact original cycle and selected banks; no centred state or observation", coefficientText polynomial,
            reprStr (selection side), count)
        IntegrationCheckpoint.profile directory
          s!"COMPLETE original cycle preparation: {count} parents; no observation claimed"

/-- The first standard differential of the internally prepared curve. -/
@[expose] def differential {side : Side} (prepared : PreparedEntry polynomial (selection side)) :=
  Riemann.Periods.PeriodMatrix.standardDifferential
    (⟨0, prepared.bounds.differential_lt⟩ : Fin prepared.prepared.genus)

/-- Construct the original root-closed initial state from the selected tour and standard differential. -/
@[expose] def initialOfData {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (branches : Branches.BranchIsolation.Data prepared.prepared.curve) :=
  Riemann.Topology.PreparedRootSafeCycleStates.ClosedBoundaryDoublePath.rootClosedInitial (cycleTour prepared branches)
    (differential prepared)

/-- Root-closed refinement states indexed by the original selected tour's initial owner name. -/
abbrev StateOfData {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (branches : Branches.BranchIsolation.Data prepared.prepared.curve) :=
  Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState
    prepared.prepared.curve (differential prepared)
    (Riemann.Paths.OwnerTraceReadings.ownerName (cycleTour prepared branches).joined.data.forwardOwner)

/-- Restore the original centered initial state and transport its exact root index to the selected tour. -/
@[expose, irreducible] def restoredInitial {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (branches : Branches.BranchIsolation.Data prepared.prepared.curve)
    (tour : Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath prepared.prepared.curve)
    (same : tour = cycleTour prepared branches)
    (cached : Riemann.Topology.PreparedCycleReplay.CachedCycle prepared.prepared.curve (differential prepared)
      (.finiteCut tour.joined.data)) : StateOfData prepared branches :=
  Riemann.Periods.PreparedRootClosedPeriodBank.RootClosedState.castRoot
    (Riemann.RootContinuation.PreparedInitialRootReplay.initial prepared.prepared.curve
    (differential prepared) tour cached.restore cached.restore_eq)
      (congrArg (fun tour : Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath prepared.prepared.curve =>
        Riemann.Paths.OwnerTraceReadings.ownerName tour.joined.data.forwardOwner) same)

/-- The restored centered initial state equals the original state constructed from the same branch data. -/
public theorem restoredInitial_eq {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (branches : Branches.BranchIsolation.Data prepared.prepared.curve)
    (tour : Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath prepared.prepared.curve)
    (same : tour = cycleTour prepared branches)
    (cached : Riemann.Topology.PreparedCycleReplay.CachedCycle prepared.prepared.curve (differential prepared)
      (.finiteCut tour.joined.data)) :
    restoredInitial prepared branches tour same cached = initialOfData prepared branches := by
  unfold restoredInitial
  cases same
  rw [Riemann.RootContinuation.PreparedInitialRootReplay.initial_eq]
  rfl

/-- Original cycle readiness is retained by every parent of the restored initial state. -/
private theorem restoredInitial_ready {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (branches : Branches.BranchIsolation.Data prepared.prepared.curve)
    (tour : Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath prepared.prepared.curve)
    (same : tour = cycleTour prepared branches)
    (ready : Integration.Surface.PreparedCycleReplay.Readiness.CycleReady prepared.prepared.curve (.finiteCut
      tour.joined.data))
    (cached : Riemann.Topology.PreparedCycleReplay.CachedCycle prepared.prepared.curve (differential prepared)
      (.finiteCut tour.joined.data)) :
    Riemann.Transport.PreparedDirectRefinementReplay.AllReady
      (restoredInitial prepared branches tour same cached).state.parents := by
  unfold restoredInitial
  rw [Riemann.Periods.PreparedRootClosedPeriodBank.RootClosedState.castRoot_state]
  exact Integration.Surface.PreparedCycleReplay.Readiness.restored prepared.prepared.curve (differential prepared) ready
    cached

set_option genInjectivity false in
/-- A restored initial state with complete source equality and parent-readiness evidence. -/
structure CertifiedInitial {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (branches : Branches.BranchIsolation.Data prepared.prepared.curve) where
  /-- The restored root-closed initial state. -/ value : StateOfData prepared branches
  /-- The restored value equals the initial state of the original branch data. -/ equal : value = initialOfData prepared
    branches
  /-- Every retained initial parent has the required exact source-track readiness. -/ ready :
    Riemann.Transport.PreparedDirectRefinementReplay.AllReady value.state.parents

constructive_injectivity CertifiedInitial

/-- Package the restored original initial state with its source and readiness proofs. -/
@[expose] def certifyInitial {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (branches : Branches.BranchIsolation.Data prepared.prepared.curve)
    (tour : Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath prepared.prepared.curve)
    (same : tour = cycleTour prepared branches)
    (ready : Integration.Surface.PreparedCycleReplay.Readiness.CycleReady prepared.prepared.curve (.finiteCut
      tour.joined.data))
    (cached : Riemann.Topology.PreparedCycleReplay.CachedCycle prepared.prepared.curve (differential prepared)
      (.finiteCut tour.joined.data)) : CertifiedInitial prepared branches :=
  ⟨restoredInitial prepared branches tour same cached,
   restoredInitial_eq prepared branches tour same cached,
   by exact restoredInitial_ready prepared branches tour same ready cached⟩

/-- Reload the original centres, retaining the same tour's root-return data. -/
@[expose] def withCenteredCycleData {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (branches : Branches.BranchIsolation.Data prepared.prepared.curve)
    (directory : System.FilePath)
    (use : (data : Thunk (Riemann.Topology.PreparedCycleModels.PreparedCycleData prepared.prepared.curve)) →
      data.get = cycleData prepared branches →
      (root : Gaussian.Name.Basic.Named) →
      root = Riemann.Paths.OwnerTraceReadings.ownerName (cycleTour prepared branches).joined.data.forwardOwner →
      (initial : StateOfData prepared branches) → initial = initialOfData prepared branches →
      Riemann.Transport.PreparedDirectRefinementReplay.AllReady initial.state.parents → IO Unit) (savedOnly : Bool :=
        false) : IO Unit :=
  withClosedTour prepared branches directory (savedOnly := savedOnly) fun tour same ready => do
    let action : RootRefinementCheckpoint.Execution Unit := do
      let data := Thunk.mk fun _ => Riemann.Topology.PreparedCycleModels.PreparedCycleData.finiteCut tour.joined.data
      let control ← RootRefinementCheckpoint.Control.create savedOnly
      PreparedCenterCheckpoint.withCycle prepared.prepared.curve (differential prepared)
        data.get (RootClosedCycleCheckpoint.ready tour ready) control (closedCycleDirectory
          (Purelib.System.FilePath.join directory (System.FilePath.mk ("centers")))) fun cached => do
        let initial := certifyInitial prepared branches tour same (RootClosedCycleCheckpoint.ready tour ready) cached
        use data (congrArg (fun tour : Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath
          prepared.prepared.curve =>
          Riemann.Topology.PreparedCycleModels.PreparedCycleData.finiteCut tour.joined.data) same)
          (Riemann.Paths.OwnerTraceReadings.ownerName tour.joined.data.forwardOwner)
          (congrArg (fun tour : Riemann.Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath
            prepared.prepared.curve =>
            Riemann.Paths.OwnerTraceReadings.ownerName tour.joined.data.forwardOwner) same)
          initial.value initial.equal initial.ready
    let (result, _) ← RootRefinementCheckpoint.Execution.run action {}
    (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

/-- The ordered family of all standard differentials for the prepared genus. -/
@[expose] def targets {side : Side} (prepared : PreparedEntry polynomial (selection side)) :=
  Riemann.Integration.PreparedRefinementProgramCore.standardDifferentials prepared.prepared.genus

/-- The selected standard differential belongs to the retained target family. -/
theorem differential_mem {side : Side} (prepared : PreparedEntry polynomial (selection side)) :
    differential prepared ∈ targets prepared :=
  Riemann.Integration.PreparedRefinementProgramCore.standardDifferential_mem_standardDifferentials _

variable {root : Gaussian.Name.Basic.Named}

/-- Root-closed refinement states for the prepared curve and chosen retained root name. -/
abbrev RefinementState {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (root : Gaussian.Name.Basic.Named) :=
  Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState
    prepared.prepared.curve (differential prepared) root

/-- The scheduled refinement model is exactly the corresponding stage of the owned period program. -/
theorem initial_model_eq {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (initial : RefinementState prepared root)
    (programEqual : Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState.period initial (targets prepared)
      (differential prepared) (differential_mem prepared) =
      prepared.entry.program.integral) (index : Nat) :
    ((initial.states (targets prepared) (policy.schedule.index index)).state.model
        (differential prepared)) =
      ((Riemann.Periods.PeriodPolicies.program prepared.entry policy).stage index).model := by
  rw [Riemann.Periods.PeriodPolicies.program, policy.stage_eq]
  change _ = (prepared.entry.program.integral.model _)
  rw [← programEqual]
  rfl

/-- Preserve the exact canonical cell order while deferring each expensive coefficient witness until its own durable
checkpoint can be written. -/
@[expose] def cellThunks {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (target : Differentials.Basic.Differential genus) :
    ∀ {parents : List (Riemann.Integration.PreparedSwitchedRefinements.CenteredEdge curve source)}
      {start finish : Lifted.Basic.LiftedPoint 2},
      Riemann.Integration.PreparedSwitchedRefinements.SwitchedPathChain parents
        (start := start) (finish := finish) →
      List (Thunk Polynomial.Gaussian.Cell.Basic.CellModel)
  | [], _, _, .nil _ => []
  | _ :: _, _, _, .edge parent tail =>
      Thunk.mk (fun _ =>
        (Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge target parent).model) ::
        cellThunks target tail
  | _, _, _, .stationary coordinate _ tail =>
      Thunk.mk (fun _ => Riemann.Integration.PreparedSwitchedRefinements.stationaryModel coordinate) ::
        cellThunks target tail

/-- Forcing the ordered cell thunks recovers exactly the original recast cell list. -/
theorem cellThunks_eq {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (target : Differentials.Basic.Differential genus) :
    ∀ {parents : List (Riemann.Integration.PreparedSwitchedRefinements.CenteredEdge curve source)}
      {start finish : Lifted.Basic.LiftedPoint 2}
      (chain : Riemann.Integration.PreparedSwitchedRefinements.SwitchedPathChain parents
        (start := start) (finish := finish)),
      (cellThunks target chain).map Thunk.get = chain.recastCells target
  | [], _, _, .nil _ => rfl
  | _ :: _, _, _, .edge parent tail =>
      congrArg (fun cells =>
        (Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge target parent).model :: cells)
        (cellThunks_eq target tail)
  | parents, _, _, .stationary coordinate _ tail => by
      have tailEqual := cellThunks_eq target tail
      cases parents <;>
        exact congrArg (fun cells =>
          Riemann.Integration.PreparedSwitchedRefinements.stationaryModel coordinate :: cells)
          tailEqual

/-- Compute observation control from the retained initial geometry and cached zero-stage sample.

The error scale and center bound retain their exact nonnegativity certificates. -/
@[expose] def initialControlValue {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (initial : Riemann.Integration.PreparedSwitchedRefinements.DirectSwitchedState
      prepared.prepared.curve (differential prepared))
    (zero : Program.Gaussian.Cached.Basic.CachedModel) : IntegrationReplay.Control :=
  let flatScale := 4 * (3 * initial.scheduleBase (targets prepared))
  have flatNonnegative : 0 ≤ flatScale :=
    Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (initial.scheduleBase_positive _).le)
  { errorScale := initial.chain.switchFactor * flatScale
    errorScale_nonneg := Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct initial.chain.switchFactor_positive.le
      flatNonnegative
    centerBound := 2 * (Data.Gaussian.Norm.Basic.normSq zero.sample + flatScale)
    centerBound_nonneg := Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (Data.Gaussian.Norm.Basic.normSq_nonneg _) flatNonnegative) }

/-- Derive the unchanged control from the retained initial sample. All uses of the original period constructor below are
proof-only and erased natively. -/
@[expose] def initialControl {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (initial : RefinementState prepared root)
    (programEqual : Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState.period initial (targets prepared)
      (differential prepared) (differential_mem prepared) =
      prepared.entry.program.integral)
    (zero : Program.Gaussian.Cached.Basic.CachedModel)
    (zeroModel : zero.model = initial.state.model (differential prepared)) :
    IntegrationCheckpoint.KnownControl (Riemann.Periods.PeriodPolicies.program prepared.entry policy) := by
  let flatScale := 4 * (3 * initial.state.scheduleBase (targets prepared))
  let errorScale := initial.state.chain.switchFactor * flatScale
  let centerBound := 2 * (Data.Gaussian.Norm.Basic.normSq zero.sample + flatScale)
  have errorEqual : errorScale =
      (Riemann.Periods.PeriodPolicies.program prepared.entry policy).errorScale := by
    change errorScale = prepared.entry.program.integral.errorScale
    rw [← programEqual]
    unfold errorScale flatScale
    rfl
  have sampleEqual : zero.sample =
      (Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState.flatModel initial (targets prepared) (differential
        prepared) 0).integralSample := by
    rw [zero.sample_eq, zeroModel]
    exact Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState.sample_eq_flat initial
      (targets prepared) (differential prepared) 0
  have centerEqual : centerBound =
      (Riemann.Periods.PeriodPolicies.program prepared.entry policy).centerBound := by
    change centerBound = prepared.entry.program.integral.centerBound
    rw [← programEqual]
    change 2 * (Data.Gaussian.Norm.Basic.normSq zero.sample + flatScale) =
      2 * (Data.Gaussian.Norm.Basic.normSq
        (Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState.flatModel initial (targets prepared)
          (differential prepared) 0).integralSample +
        4 * (3 * initial.state.scheduleBase (targets prepared)))
    rw [sampleEqual]
  exact
    { value := initialControlValue prepared initial.state zero
      errorScale_eq := errorEqual
      centerBound_eq := centerEqual }

/-- Serialize the four exact rational bounds of a box in coordinate order. -/
@[expose] def boxData (box : Rational.Box) : List IntegrationCheckpoint.FractionData :=
  [box.xLower, box.xUpper, box.yLower, box.yUpper].map IntegrationCheckpoint.fractionData

set_option genInjectivity false in
/-- Retain the latest proved geometry, without keeping every intermediate parent list alive. Earlier requested models
have their own reply cache. Numeric disk snapshots do not reconstruct this proof-bearing state. -/
structure RefinementCursor {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (initial : Thunk (RefinementState prepared root)) where
  /-- The latest retained canonical refinement index. -/ last : Nat
  /-- The retained state at the latest refinement index. -/ state : Thunk (RefinementState prepared root)
  /-- The retained state equals the original iterated refinement at that index. -/ state_eq : state.get =
    initial.get.states (targets prepared) last
  /-- Optional retained readiness for the original initial parent list. -/ initialReady : Option (PLift
    (Riemann.Transport.PreparedDirectRefinementReplay.AllReady initial.get.state.parents))
  /-- Optional retained readiness for the current parent list. -/ ready : Option (PLift
    (Riemann.Transport.PreparedDirectRefinementReplay.AllReady state.get.state.parents))
  /-- The original constructor histories associated with the current retained parents. -/ histories :
    Riemann.Transport.PreparedDeferredRecipeReplay.Histories state.get.state.parents

constructive_injectivity RefinementCursor

/-- Restore or acquire one exact canonical successor while preserving its original state equation.

Saved-only replay requires retained readiness; incomplete replay saves typed
obligations. The successful continuation returns its exact result while keeping
the restored original state equation. -/
@[expose] def nextRefinement {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (directory : System.FilePath) (savedOnly : Bool) (initial : Thunk (RefinementState prepared root))
    (cursor : RefinementCursor prepared initial)
    (done : (next : RefinementCursor prepared initial) → next.last = cursor.last + 1 → IO Result) : IO Result := do
  let action : RootRefinementCheckpoint.Execution Result := do
    let previous := cursor.state
    let index := cursor.last + 1
    let target := initial.get.state.scheduleTarget (targets prepared) cursor.last
    let control ← RootRefinementCheckpoint.Control.create savedOnly
    let stepDirectory := (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk
      ("refinements-v1"))) (System.FilePath.mk (s!"step-{index}")))
    IntegrationCheckpoint.profile directory s!"refinement {index}: BEGIN original selection and child checkpoint replay"
    let some ready := cursor.ready | do
      if savedOnly then
        throw (IO.userError
          "corrected-period child replay requires retained readiness evidence; canonical generation forbidden in \
            replay mode")
      IntegrationCheckpoint.profile directory
        "Corrected-period readiness replay unavailable; acquiring the canonical successor"
      let step := Thunk.mk fun _ =>
        Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState.Step.acquire
          previous.get (targets prepared) target (initial.get.state.scheduleTarget_positive (targets prepared)
            cursor.last)
      let next := Thunk.mk fun _ => step.get.next
      have nextEqual : next.get = initial.get.states (targets prepared) index := by
        change
          (Riemann.Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState.Step.acquire
          previous.get (targets prepared) target _).next = _
        rw [cursor.state_eq]
        rfl
      done ⟨index, next, nextEqual, cursor.initialReady, none,
        Riemann.Transport.PreparedDeferredRecipeReplay.Histories.inherited next.get.state.parents⟩ rfl
    PreparedRefinementCheckpoint.withStep previous.get ready.down cursor.histories (targets prepared) target
      (initial.get.state.scheduleTarget_positive (targets prepared) cursor.last) control stepDirectory fun result => do
        match result with
        | .error pending =>
            IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join stepDirectory (System.FilePath.mk
              ("inconclusive.json")))) pending.report
            throw (IO.userError
              s!"refinement {index}: finite checkpoint replay is inconclusive; original attempt and unresolved \
                operands retained")
        | .ok restored =>
            let next := Thunk.mk fun _ => restored.value.next
            have nextEqual : next.get = initial.get.states (targets prepared) index := by
              change restored.value.next = _
              rw [restored.equal, cursor.state_eq]
              rfl
            let selected := restored.value.accuracy.result
            let count := next.get.state.parents.length
            IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join stepDirectory (System.FilePath.mk
              ("completed-state.json"))))
              (index, selected.depth, IntegrationCheckpoint.fractionData selected.rootDiameter, count)
            IntegrationCheckpoint.profile directory
              s!"refinement {index}: complete; parents={count}; original state restored"
            done ⟨index, next, nextEqual, cursor.initialReady, some ⟨restored.ready⟩, restored.histories⟩ rfl
  let (result, _) ← RootRefinementCheckpoint.Execution.run action {}
  (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) result

/-- Extend the retained refinements structurally, one successor at a time.

The continuation retains the higher-universe state and its exact index equation;
only its ordinary return value enters IO. -/
@[expose] def extendRefinements {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (directory : System.FilePath) (savedOnly : Bool) (initial : Thunk (RefinementState prepared root)) :
    (extra : Nat) → (cursor : RefinementCursor prepared initial) →
      ((extended : RefinementCursor prepared initial) → extended.last = cursor.last + extra → IO Result) → IO Result
  | 0, cursor, done => done cursor rfl
  | extra + 1, cursor, done =>
      nextRefinement prepared directory savedOnly initial cursor fun next nextEqual =>
        extendRefinements prepared directory savedOnly initial extra next fun extended extendedEqual =>
          done extended (by rw [extendedEqual, nextEqual]; omega)

/-- Generate one scheduled model from retained canonical refinement states and individually saved cells.

Preserve the complete stage-model equation when every cell retains its source identity, and keep the furthest completed
refinement cursor. -/
@[expose] def generateRefinedModel {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (directory : System.FilePath) (initial : Thunk (RefinementState prepared root))
    (programEqual : Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState.period initial.get (targets prepared)
      (differential prepared) (differential_mem prepared) =
      prepared.entry.program.integral) :
    IntegrationCheckpoint.ModelGenerator
      (Riemann.Periods.PeriodPolicies.program prepared.entry policy) (RefinementCursor prepared initial) :=
  fun {_} index cursor done => do
    let requested := policy.schedule.index index
    IntegrationCheckpoint.profile directory s!"query {index}: latest retained refinement is {cursor.last}"
    let start : RefinementCursor prepared initial :=
      if requested < cursor.last then ⟨0, initial, rfl, cursor.initialReady, cursor.initialReady,
        Riemann.Transport.PreparedDeferredRecipeReplay.Histories.inherited initial.get.state.parents⟩ else cursor
    have startLe : start.last ≤ requested := by
      dsimp only [start]
      split
      · exact Nat.zero_le _
      · omega
    extendRefinements prepared directory false initial (requested - start.last) start fun retained retainedEqual => do
      have retainedIndex : retained.last = requested := by rw [retainedEqual]; omega
      let state := retained.state
      have stateEqual : state.get = initial.get.states (targets prepared) requested := by
        rw [retained.state_eq, retainedIndex]
      let cells ← IntegrationCheckpoint.materializeCells directory index 0
        ((cellThunks (differential prepared) state.get.state.chain).map fun work =>
          IntegrationCheckpoint.CellTask.fromCached work work rfl)
      let model : Polynomial.Gaussian.Path.Basic.PathModel := ⟨cells.cells⟩
      let sourceEqual := cells.source_eq.map fun equal =>
        (PLift.up (show model =
          ((Riemann.Periods.PeriodPolicies.program prepared.entry policy).stage index).model from by
          change Polynomial.Gaussian.Path.Basic.PathModel.mk cells.cells = _
          rw [equal.down]
          simp only [-eq_self, -iff_self, Data.List.Map.map_map, IntegrationCheckpoint.CellTask.specification,
            IntegrationCheckpoint.CellTask.fromCached, Function.comp_def]
          rw [cellThunks_eq]
          change state.get.state.model (differential prepared) = _
          rw [stateEqual]
          exact initial_model_eq prepared initial.get programEqual index))
      done ⟨model, sourceEqual⟩ (if cursor.last ≤ retained.last then retained else cursor)

/-- Restore every needed successor from its saved original search and child centres before reconstructing a saved
model's source equation. -/
@[expose] def reloadModel {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (directory : System.FilePath) (initial : Thunk (RefinementState prepared root))
    (programEqual : Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState.period initial.get (targets prepared)
      (differential prepared) (differential_mem prepared) =
      prepared.entry.program.integral) :
    IntegrationCheckpoint.ModelReload
      (Riemann.Periods.PeriodPolicies.program prepared.entry policy) (RefinementCursor prepared initial) :=
  .certified fun {_} index cursor done => do
    let requested := policy.schedule.index index
    let start : RefinementCursor prepared initial :=
      if requested < cursor.last then ⟨0, initial, rfl, cursor.initialReady, cursor.initialReady,
        Riemann.Transport.PreparedDeferredRecipeReplay.Histories.inherited initial.get.state.parents⟩ else cursor
    have startLe : start.last ≤ requested := by
      dsimp only [start]
      split
      · exact Nat.zero_le _
      · omega
    extendRefinements prepared directory true initial (requested - start.last) start fun retained retainedEqual => do
      have retainedIndex : retained.last = requested := by rw [retainedEqual]; omega
      let state := retained.state
      let model := state.get.state.model (differential prepared)
      have sourceEqual : model =
          ((Riemann.Periods.PeriodPolicies.program prepared.entry policy).stage index).model := by
        change state.get.state.model (differential prepared) = _
        rw [retained.state_eq, retainedIndex]
        exact initial_model_eq prepared initial.get programEqual index
      done ⟨model, sourceEqual⟩ (if cursor.last ≤ retained.last then retained else cursor)

open scoped Purelib.Data.List in
/-- Serialize the exact polynomial, selection, schedule, allocation and observation request identity. -/
@[expose] def observationIdentity (side : Side) : String :=

    s!"ordered corrected standard tours v3; normalized dx/z; polynomial={coefficientText polynomial}; \
      selection={repr (selection side)}; schedule=({policy.schedule.offset},{policy.schedule.extraStride}); \
      allocation=({policy.allocation.initial},{policy.allocation.extensions}); request=({request.current},\
      {IntegrationCheckpoint.fractionText request.target})"

/-- Run the retained source after preparation. Ownership is supplied by the equality of the complete generated program,
not by an auxiliary raw-tour layout or a comparison of parent counts. This boundary also accepts the retained states of
the corrected ordered bank. -/
@[expose] def observeRetained {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (count : Nat) (directory : System.FilePath)
    (branches : Thunk (Branches.BranchIsolation.Data prepared.prepared.curve))
    (initial : Thunk (RefinementState prepared root))
    (initialReady : Option (PLift (Riemann.Transport.PreparedDirectRefinementReplay.AllReady
      initial.get.state.parents)))
    (programEqual : Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState.period initial.get (targets prepared)
      (differential prepared) (differential_mem prepared) =
      prepared.entry.program.integral) : IO Unit := do
  let source : Thunk Program.Gaussian.Cached.Basic.CachedProgram :=
    Thunk.mk fun _ => Riemann.Periods.PeriodPolicies.program prepared.entry policy
  let ensureInitial : IO Unit := do
    IntegrationCheckpoint.profile directory

        "Retained corrected-period state supplied with its complete program equation; disk successor replay requires \
          separate readiness evidence"
    let branchCount ← materialize directory "canonical branch isolation" fun _ => branches.get.siteCount
    IntegrationCheckpoint.profile directory s!"canonical branches={branchCount.value}"
    let actualCount ← materialize directory "initial centered state and source bound" fun _ =>
      initial.get.state.parents.length
    IntegrationCheckpoint.profile directory s!"source-certified initial parent count={actualCount.value}"
  let cursor : RefinementCursor prepared initial := ⟨0, initial, rfl, initialReady, initialReady,
    Riemann.Transport.PreparedDeferredRecipeReplay.Histories.inherited initial.get.state.parents⟩
  let modelReload := reloadModel prepared directory initial programEqual
  let generate : IntegrationCheckpoint.ModelGenerator source.get (RefinementCursor prepared initial) :=
    generateRefinedModel prepared directory initial programEqual
  let restoreInitial : IO
      (IntegrationCheckpoint.KnownControl source.get × IntegrationCheckpoint.KnownReply source.get) := do
    ensureInitial
    IntegrationCheckpoint.acquireReply directory source generate modelReload 0 cursor fun _ known _ => do
      let some seed := known |
        throw (IO.userError "source-certified initial acquisition did not retain its model equation")
      -- The reply index remains checked before deriving the original controller.
      if indexEqual : seed.index = 0 then
        have zeroModel : seed.reply.model = initial.get.state.model (differential prepared) := by
          rw [seed.equal, indexEqual]
          exact (initial_model_eq prepared initial.get programEqual 0).symm
        let control ← materialize directory "control from restored initial sample" fun _ =>
          initialControl prepared initial.get programEqual seed.reply zeroModel
        return (control.value, seed)
      else throw (IO.userError "initial acquisition returned a different query index")
  let prepare : IO (IntegrationCheckpoint.Preparation source.get) := do
    let (control, seed) ← restoreInitial
    return .certified control [seed]
  let reload : IntegrationCheckpoint.Reload source.get (RefinementCursor prepared initial) :=
    ⟨.certified (do return (← restoreInitial).1), modelReload⟩
  report s!"normalized period: checkpoints and profiles in {directory}"
  IntegrationCheckpoint.observeWithState directory (observationIdentity side) source prepare cursor generate reload
    request count

/-- Observe the requested corrected period from its original ordered branch family.

Use the proved complete program equation for the selected A or B state; numerical branch readbacks alone do not
establish ownership. -/
@[expose] def observeBranches {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (count : Nat) (directory : System.FilePath)
    (branches : Branches.BranchIsolation.Data prepared.prepared.curve)
    (same : branches = Branches.BranchIsolation.data prepared.prepared.curve) : IO Unit := by
  let bank := Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofData prepared.prepared.curve branches
  let index : Fin prepared.prepared.genus := ⟨0, prepared.bounds.cycle_lt⟩
  let initial := bank.initialRow index
  have canonical : bank = Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve prepared.prepared.curve := by
    dsimp only [bank]
    rw [same]
    exact (Meshes.PuncturedGrid.Paired.PeriodBank.PairedPeriodBank.ofCurve_positive prepared.prepared.curve index).symm
  cases side with
  | a =>
      have owned : Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState.period initial.a (targets prepared)
        (differential prepared) (differential_mem prepared) =
          prepared.entry.program.integral := by
        refine (initial.a_program ⟨0, prepared.bounds.differential_lt⟩).trans ?_
        rw [PreparedEntry.entry, prepared.entry_eq]
        rw [canonical]
        rfl
      exact observeRetained prepared count directory (Thunk.mk fun _ => branches) (Thunk.mk fun _ => initial.a) none
        owned
  | b =>
      have owned : Riemann.Periods.PreparedRootSafePeriodPrograms.RootClosedState.period initial.b (targets prepared)
        (differential prepared) (differential_mem prepared) =
          prepared.entry.program.integral := by
        refine (initial.b_program ⟨0, prepared.bounds.differential_lt⟩).trans ?_
        rw [PreparedEntry.entry, prepared.entry_eq]
        rw [canonical]
        rfl
      exact observeRetained prepared count directory (Thunk.mk fun _ => branches) (Thunk.mk fun _ => initial.b) none
        owned

/-- Observe the corrected canonical program. A separate branch store may reuse compatible isolation work through its
checked loader; raw-tour states and old observation receipts are never imported as corrected ownership. -/
@[expose] def observe (side : Side) (count : Nat) (directory : System.FilePath := checkpointDirectory side)
    (branchDirectory : Option System.FilePath := none) : IO Unit := do
  IntegrationCheckpoint.openStore directory (observationIdentity side)
  withPrepared side fun prepared =>
    withCanonicalBranches prepared (branchDirectory.getD directory) (observeBranches prepared count directory)

/-- Parse the standard-period side, accepting exactly a or b. -/
@[expose] def parseSide (name : String) : IO Side :=
  if name = "a" then pure .a
  else if name = "b" then pure .b
  else throw (IO.userError "side must be a or b")

/-- Profile one actual retained cell, not a replacement fixture. Save the numeric owner and targets before asking for
any coefficient witness, so the next diagnostic can replay those finite calculations without branch isolation. These
snapshots are diagnostic inputs, not serialized ownership proofs. -/
@[expose] def diagnoseEdge {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (target : Differentials.Basic.Differential genus)
    (parent : Riemann.Integration.PreparedSwitchedRefinements.CenteredEdge curve source)
    (directory : System.FilePath) : IO Unit := do
  let edge := Riemann.Integration.PreparedEdgeRecasting.recastPreparedEdge target parent.edge
  let centered := Thunk.mk fun _ =>
    Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge target parent
  IntegrationCheckpoint.profile directory "BEGIN selected cell geometry and numerical budgets"
  IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("edge.json"))))
    (Json.mkObj
    [("start", toJson (IntegrationCheckpoint.gaussianData (edge.point 0))),
     ("finish", toJson (IntegrationCheckpoint.gaussianData (edge.point 1))),
     ("left", toJson (IntegrationCheckpoint.fractionData edge.left.parameter)),
     ("right", toJson (IntegrationCheckpoint.fractionData edge.request.endpoint.parameter)),
     ("exponent", toJson target.exponent), ("sheet", toJson edge.sheet.val),
     ("readingTarget", toJson (IntegrationCheckpoint.fractionData edge.readingTarget)),
     ("rootResidualTarget", toJson (IntegrationCheckpoint.fractionData edge.rootResidualTarget))])
  IntegrationCheckpoint.profile directory "END selected cell geometry and numerical budgets; edge.json saved"
  let owner := Thunk.mk fun _ => edge.directQueryOwner 0 edge.baseInside
  IntegrationCheckpoint.profile directory "BEGIN direct query owner snapshot"
  IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("owner.json"))))
    (Json.mkObj
    [("parameter", toJson (IntegrationCheckpoint.gaussianData (curve.polynomial.eval (edge.point 0)))),
     ("ambient", toJson (boxData owner.get.ambient)),
     ("box", toJson (boxData owner.get.track.initial.box)),
     ("clearance", toJson (IntegrationCheckpoint.fractionData owner.get.track.initial.clearance.bound)),
     ("rootState", toJson (RootStateCheckpoint.capture owner.get.track.initial)),
     ("canonicalCenterCursor", toJson (CenterCheckpoint.capture edge)),
     ("transport", toJson (RootStateCheckpoint.TransportRequest.mk
       (IntegrationCheckpoint.gaussianData (curve.polynomial.eval (edge.point 1)))
       (IntegrationCheckpoint.fractionData
         (Riemann.Branches.PreparedSheetContinuation.transportReserve edge.segment
           edge.left edge.request))
       (some (IntegrationCheckpoint.fractionData
         (Riemann.Branches.PreparedSheetContinuation.preparedClearanceLower edge.segment
           edge.left edge.request))))),
     ("baseIndex", toJson (Riemann.RootContinuation.CertifiedSquareRoot.baseIndex owner.get.track))])
  IntegrationCheckpoint.profile directory "END direct query owner snapshot; owner.json saved"
  let residualIndex ← materialize directory "residual root state index" fun _ =>
    (show Nat from (edge.residualRootState 0 edge.baseInside).source)
  IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("residual-index.json"))))
    residualIndex.value
  let readingIndex ← materialize directory "quotient reading state root index" fun _ =>
    (show Nat from centered.get.center.state.2.source)
  IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("reading-index.json"))))
    readingIndex.value
  let coefficient ← materialize directory "canonical coefficient witness" fun _ =>
    centered.get.center.value
  IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("coefficient.json"))))
    (IntegrationCheckpoint.gaussianData coefficient.value)
  IntegrationCheckpoint.profile directory "BEGIN selected cell model serialization"
  IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("cell.json"))))
    (IntegrationCheckpoint.cellData centered.get.model)
  let saved : IntegrationCheckpoint.CellData ← IntegrationCheckpoint.loadJson ((Purelib.System.FilePath.join directory
    (System.FilePath.mk ("cell.json"))))
  discard <| IntegrationCheckpoint.checked "selected cell roundtrip" (IntegrationCheckpoint.decodeCell saved)
  IntegrationCheckpoint.profile directory "END selected cell model serialization; numeric roundtrip checked"

/-- Count stationary switches as cells, exactly as `cellThunks` does. Skip unrequested cells structurally without
evaluating their coefficient models. -/
@[expose] def diagnoseChain {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {source : Differentials.Basic.Differential genus}
    (target : Differentials.Basic.Differential genus)
    (directory : System.FilePath) :
    ∀ {parents : List (Riemann.Integration.PreparedSwitchedRefinements.CenteredEdge curve source)}
      {start finish : Lifted.Basic.LiftedPoint 2},
      Riemann.Integration.PreparedSwitchedRefinements.SwitchedPathChain parents
        (start := start) (finish := finish) → Nat → IO Unit
  | [], _, _, .nil _, _ => throw (IO.userError "cell index exceeds the actual canonical chain")
  | _ :: _, _, _, .edge parent _, 0 => diagnoseEdge target parent directory
  | _ :: _, _, _, .edge _ tail, index + 1 => diagnoseChain target directory tail index
  | _, _, _, .stationary coordinate _ _, 0 => do
      IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("cell.json"))))
        (IntegrationCheckpoint.cellData (Riemann.Integration.PreparedSwitchedRefinements.stationaryModel coordinate))
      IntegrationCheckpoint.profile directory "Selected cell is a stationary sheet switch"
  | _, _, _, .stationary _ _ tail, index + 1 => diagnoseChain target directory tail index

open scoped Purelib.Data.List in
/-- Profile one actual canonical cell in a fresh diagnostic store.

Retain the original bank layout and source state while skipping all unrequested coefficient models; the result is not an
observation receipt. -/
@[expose] def cellPhases (side : Side) (index : Nat) (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then
    throw (IO.userError "cell diagnostics require a fresh directory; existing checkpoints are not overwritten")
  IntegrationCheckpoint.openStore directory

      s!"canonical initial cell diagnostic; polynomial={coefficientText polynomial}; \
        selection={repr (selection side)}; cell={index}"
  IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("request.json"))))
    (Json.mkObj
    [("polynomial", toJson (coefficientText polynomial)),
     ("selection", toJson (reprStr (selection side))), ("cellIndex", toJson index),
     ("scope", toJson "initial canonical model cell diagnostic, not an observation receipt")])
  withPrepared side fun prepared => withCanonicalBranches prepared directory fun restored _ =>
    withCenteredCycleData prepared restored directory fun restoredData _ _ _ cachedInitial _ _ => do
    let branches := Thunk.mk fun _ => restored
    let data := restoredData
    let initial := Thunk.mk fun _ => cachedInitial
    discard <| materialize directory "canonical branch isolation" fun _ => branches.get.siteCount
    discard <| materialize directory "canonical cycle preparation/banks" fun _ =>
      Riemann.Integration.PreparedSwitchedRefinements.cycleSourceParentCount data.get
    let banks : List (String × Nat) := match data.get with
      | .bridge bridge =>
          let count := 2 ^ bridge.depth * bridge.basePath.segmentCount
          [("forward", count), ("right switch", 1), ("backward", count), ("left switch", 1)]
      | .finiteCut boundary =>
          [("forward", 2 ^ boundary.forwardDepth * boundary.connector.segmentCount),
           ("right boundary", 2 ^ boundary.rightBoundaryDepth * boundary.rightBoundaryPath.segmentCount),
           ("right switch", 1),
           ("backward", 2 ^ boundary.backwardDepth * boundary.connector.segmentCount),
           ("left boundary", 2 ^ boundary.leftBoundaryDepth * boundary.leftBoundaryPath.segmentCount),
           ("left switch", 1)]
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("bank-layout.json"))))
      banks
    IntegrationCheckpoint.profile directory s!"Canonical cell layout={banks}"
    discard <| materialize directory "initial centered state and source bound" fun _ => initial.get.state.parents.length
    IntegrationCheckpoint.profile directory
      s!"Selecting actual canonical cell {index}; no earlier cell coefficients requested"
    diagnoseChain (differential prepared) directory initial.get.state.chain index

/-- Record the original centered state's parent count, switch count and cached source allowance. -/
@[expose] public def recordInitial {side : Side} (prepared : PreparedEntry polynomial (selection side))
    (initial : RefinementState prepared root) (directory : System.FilePath) : IO Unit := do
  let count := initial.state.parents.length
  let allowance := initial.state.initialAllowanceBound (differential prepared)
  IntegrationCheckpoint.saveJson (closedCycleDirectory (Purelib.System.FilePath.join directory (System.FilePath.mk
    ("completed-initial-state.json"))))
    (Json.mkObj
      [("scope", toJson "exact original centred state and cached source allowance; no observation"),
       ("parentCount", toJson count),
       ("switchCount", toJson initial.state.chain.switchCount),
       ("sourceAllowance", toJson (IntegrationCheckpoint.fractionData allowance))])
  IntegrationCheckpoint.profile directory
    s!"COMPLETE original centred state: {count} parents; cached source allowance saved; no observation claimed"

/-- Reach the original centred state and its cached source allowance without starting a successor. Replay forbids new
preparation and coefficient proposals. -/
@[expose] def initialPhases (side : Side) (directory : System.FilePath) (savedOnly : Bool) : IO Unit :=
  withPrepared side fun prepared =>
    withCanonicalBranches prepared directory (savedOnly := savedOnly) fun branches _ =>
      withCenteredCycleData prepared branches directory (savedOnly := savedOnly) fun _ _ root rootEq original _ _ =>
        let initial := Riemann.Periods.PreparedRootClosedPeriodBank.RootClosedState.castRoot original rootEq.symm
        recordInitial (root := root) prepared initial directory

/-- Branch isolation can be restored independently of the changed cycle owner. The former raw-tour centred checkpoints
do not certify the corrected periods. -/
@[expose] def observeRestored (side : Side) (count : Nat) (sourceDirectory directory : System.FilePath) : IO Unit := do
  IntegrationCheckpoint.openStore directory (observationIdentity side)
  report
    "Restoring branch isolation only; corrected ordered geometry is acquired separately. Raw-tour centred checkpoints \
      are not reused as corrected periods."
  withPrepared side fun prepared =>
    withCanonicalBranches prepared sourceDirectory (savedOnly := true) fun branches same =>
      observeBranches prepared count directory branches same

/-- Isolate actual canonical successors without regenerating initial model coefficients or control metadata. This
profiles the same successor function used by observation mode; it is not an observation acceptance test. -/
@[expose] def refinementPhases (side : Side) (steps : Nat) (directory : System.FilePath) (savedOnly : Bool := false) :
  IO Unit := do
  report "Raw-tour refinement diagnostic; not corrected-period acquisition."
  unless 0 < steps do throw (IO.userError "refinement diagnostics require a positive step count")
  IO.FS.createDirAll directory
  withPrepared side fun prepared => withCanonicalBranches prepared directory (savedOnly := savedOnly) fun restored _ =>
    withCenteredCycleData prepared restored directory (savedOnly := savedOnly) fun restoredData _ root rootEq original _
      originalReady => do
    let cachedInitial := Riemann.Periods.PreparedRootClosedPeriodBank.RootClosedState.castRoot original rootEq.symm
    have initialReady : Riemann.Transport.PreparedDirectRefinementReplay.AllReady cachedInitial.state.parents := by
      rw [Riemann.Periods.PreparedRootClosedPeriodBank.RootClosedState.castRoot_state]
      exact originalReady
    let branches := Thunk.mk fun _ => restored
    let data := restoredData
    let initial := Thunk.mk fun _ => cachedInitial
    discard <| materialize directory "canonical branch isolation" fun _ => branches.get.siteCount
    discard <| materialize directory "canonical cycle preparation/banks" fun _ =>
      Riemann.Integration.PreparedSwitchedRefinements.cycleSourceParentCount data.get
    let count ← materialize directory "canonical initial geometry; no cell-model coefficients" fun _ =>
      initial.get.state.parents.length
    IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
      ("initial-parent-count.json")))) count.value
    let cursor : RefinementCursor prepared initial := ⟨0, initial, rfl, some ⟨initialReady⟩, some ⟨initialReady⟩,
    Riemann.Transport.PreparedDeferredRecipeReplay.Histories.inherited initial.get.state.parents⟩
    extendRefinements prepared directory savedOnly initial steps cursor fun retained _ => do
      IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
        ("completed-refinement-index.json")))) retained.last
      IntegrationCheckpoint.profile directory
        s!"COMPLETE refinement diagnostic through {retained.last}; no observation receipt claimed"

end PolynomialPeriodObservationHarness

namespace ReadinessProfile
open Purelib.Riemann

section
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
/-- Profile the original segment's radicand bound, root ambient box and predicted clearance three times. -/
@[expose] def segment {polynomial : GaussianPolynomial} {ambient : Rational.Box} {start finish :
  Data.Gaussian.Basic.Canonical}
    (source : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : IO Unit := do
  for index in [0:3] do
    let started ← IO.monoMsNow
    let bound ← PolynomialPeriodObservationHarness.evaluate fun _ => UniformSquareRootPreparation.radicandNormBound
      source
    Purelib.System.IO.println
      s!"readiness profile {index}: radicand bound {(← IO.monoMsNow) - started} ms; numerator \
        bits={bound.num.natAbs.log2 + 1}"
    let started ← IO.monoMsNow
    let box ← PolynomialPeriodObservationHarness.evaluate fun _ => UniformSquareRootPreparation.rootAmbient source
    Purelib.System.IO.println
      s!"readiness profile {index}: ambient {(← IO.monoMsNow) - started} ms; numerator \
        bits={box.xLower.num.natAbs.log2 + 1}"
    let started ← IO.monoMsNow
    let predicted ← PolynomialPeriodObservationHarness.evaluate fun _ => UniformSquareRootPreparation.predictedClearance
      source 1
    Purelib.System.IO.println
      s!"readiness profile {index}: predicted clearance {(← IO.monoMsNow) - started} ms; numerator \
        bits={predicted.num.natAbs.log2 + 1}"

/-- Profile the first retained clear segment without allocating an alternative path. -/
@[expose] def first {polynomial : GaussianPolynomial} {ambient : Rational.Box} {start finish :
  Data.Gaussian.Basic.Canonical} :
    Polynomial.Geometry.ClearPath polynomial ambient start finish → IO Unit
  | .nil _ => Purelib.System.IO.println "empty path"
  | .cons head _ => segment head

end

/-- Restore the original A-cycle branch data and profile its first connector segment with generation forbidden. -/
@[expose] def run (directory : System.FilePath) : IO Unit :=
  PolynomialPeriodObservationHarness.withPrepared .a fun prepared =>
    PolynomialPeriodObservationHarness.withCanonicalBranches prepared
      directory (fun branches _ => do
      let curve := prepared.prepared.curve
      let cycle : Fin prepared.prepared.genus := ⟨0, prepared.bounds.cycle_lt⟩
      let higher := Branches.BranchCutLifts.degreeGtOne_of_cycleIndex curve cycle
      let geometry := (Branches.BranchConfiguration.configurationOfData curve branches).branches
      let left := Branches.BranchConfiguration.basisPairLeftIndexOfData curve branches cycle
      let right := Branches.BranchConfiguration.basisPairRightIndexOfData curve branches cycle
      first (Branches.Cuts.connectorAt geometry higher left right 0)) true
end ReadinessProfile

/-- Dispatch coefficient preparation, checkpoint diagnostics, corrected observation or numerical replay.

Validate the requested side and finite counts while retaining the distinct source-restoration and source-free replay
boundaries. -/
@[expose] def main (arguments : List String) : IO Unit := do
  match arguments with
  | ["import-numerical", side, source, destination] =>
      let side ← PolynomialPeriodObservationHarness.parseSide side
      discard <| IntegrationCheckpoint.importNumerical source destination
        (PolynomialPeriodObservationHarness.observationIdentity side)
  | ["input", side] =>
      PolynomialPeriodObservationHarness.input (← PolynomialPeriodObservationHarness.parseSide side)
  | ["readiness-phases", directory] => ReadinessProfile.run directory
  | ["preparation-phases", "a"] => PolynomialPeriodObservationHarness.preparationPhases
  | ["preparation-phases", "a", directory] => PolynomialPeriodObservationHarness.preparationPhases directory
  | ["cycle-phases", side, directory] =>
      PolynomialPeriodObservationHarness.cyclePhases (← PolynomialPeriodObservationHarness.parseSide side) directory
        false
  | ["cycle-replay", side, directory] => do
      PolynomialPeriodObservationHarness.report "Raw-tour checkpoint diagnostic; not corrected-period acquisition."
      PolynomialPeriodObservationHarness.cyclePhases (← PolynomialPeriodObservationHarness.parseSide side) directory
        true
  | ["initial-phases", side, directory] =>
      PolynomialPeriodObservationHarness.initialPhases (← PolynomialPeriodObservationHarness.parseSide side) directory
        false
  | ["initial-replay", side, directory] =>
      PolynomialPeriodObservationHarness.initialPhases (← PolynomialPeriodObservationHarness.parseSide side) directory
        true
  | ["cell-phases", side, index, directory] =>
      let some index := (Purelib.Data.String.toNat? index) | throw (IO.userError "cell index must be a natural number")
      PolynomialPeriodObservationHarness.cellPhases (← PolynomialPeriodObservationHarness.parseSide side) index
        directory
  | ["refinement-phases", side, steps, directory] => do
      PolynomialPeriodObservationHarness.report "Raw-tour refinement diagnostic; not corrected-period acquisition."
      let some steps := (Purelib.Data.String.toNat? steps) | throw (IO.userError "step count must be a natural number")
      PolynomialPeriodObservationHarness.refinementPhases (← PolynomialPeriodObservationHarness.parseSide side) steps
        directory
  | ["refinement-replay", side, steps, directory] =>
      let some steps := (Purelib.Data.String.toNat? steps) | throw (IO.userError "step count must be a natural number")
      PolynomialPeriodObservationHarness.refinementPhases (← PolynomialPeriodObservationHarness.parseSide side) steps
        directory true
  | ["observe-restored", side, count, sourceDirectory, directory] =>
      let some count := (Purelib.Data.String.toNat? count) | throw (IO.userError "bit count must be a natural number")
      PolynomialPeriodObservationHarness.observeRestored
        (← PolynomialPeriodObservationHarness.parseSide side) count sourceDirectory directory
  | ["observe", side, count] =>
      let some count := (Purelib.Data.String.toNat? count) | throw (IO.userError "bit count must be a natural number")
      PolynomialPeriodObservationHarness.observe (← PolynomialPeriodObservationHarness.parseSide side) count
  | ["observe", side, count, directory] =>
      let some count := (Purelib.Data.String.toNat? count) | throw (IO.userError "bit count must be a natural number")
      PolynomialPeriodObservationHarness.observe (← PolynomialPeriodObservationHarness.parseSide side) count directory
  | ["observe", side, count, directory, branchDirectory] =>
      let some count := (Purelib.Data.String.toNat? count) | throw (IO.userError "bit count must be a natural number")
      PolynomialPeriodObservationHarness.observe (← PolynomialPeriodObservationHarness.parseSide side) count directory
        (some branchDirectory)
  | ["replay", directory, count] =>
      let some count := (Purelib.Data.String.toNat? count) | throw (IO.userError "bit count must be a natural number")
      IntegrationCheckpoint.replayOnly directory count
  | _ => throw (IO.userError
    "usage: polynomial_period_observation_harness input a|b | preparation-phases a [DIRECTORY] | readiness-phases \
      DIRECTORY | cycle-phases a|b DIRECTORY | cycle-replay a|b DIRECTORY | initial-phases a|b DIRECTORY | \
      initial-replay a|b DIRECTORY | cell-phases a|b CELL_INDEX DIRECTORY | refinement-phases|refinement-replay a|b \
      STEPS DIRECTORY | import-numerical a|b SOURCE_DIRECTORY DESTINATION_DIRECTORY | observe a|b BIT_COUNT \
      [DIRECTORY] | observe-restored a|b BIT_COUNT SOURCE_DIRECTORY OUTPUT_DIRECTORY | replay DIRECTORY BIT_COUNT")
