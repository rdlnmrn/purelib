module
import Purelib.Data.Rat.Bounds.Quarter
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementProgramCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedPeriodPrimitiveRequests
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests
public import Purelib.Integration.Path.IncrementAreaClosure
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

public section

open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann

/-!
# Shared cap requests on the actual complete exterior components

All adjacent grid intervals and required laps are retained. The original
root-closed period parents supply the reciprocal covers and every junction,
including the ambient corners. One polynomial and reading stage serves both
components in even degree and the full two-lap component in odd degree.
The actual root return bounds each final connector. Appending it closes the
retained increment polygon and preserves its full signed area exactly.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

set_option genInjectivity false in
/-- Root-closed programs and reciprocal covers are prepared once, before
any requested accuracy is chosen. -/
structure PreparedProgram (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (lifted :
  Meshes.LiftedPuncturedGrid base)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) where
  /-- The actual retained root-closed exterior program and its original indexed boundary. -/ program :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential
  /-- The reciprocal-cap preparation over that exact original program's cached parents. -/ cap :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path.Preparation regular program.cache.parents
  /-- The retained final coordinate join determined by the original root-return equivalence. -/ closing :
    Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins.ClosingJoin cap.bank

constructive_injectivity PreparedProgram

/-- Prepare reciprocal covers and the final root-return join of the original root-closed exterior program. -/
@[expose] def PreparedProgram.build (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (program :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.PreparedProgram regular lifted differential :=
  let cache := program.cache
  let covers := Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers.build cache.parents cache.covered
    program.onBoundary
  let prepared := Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path.Preparation.ofCache regular cache covers
  ⟨program, prepared, Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins.ClosingJoin.build prepared.bank
    (RootContinuation.PreparedCachedParentRoots.ParentCache.rootChain cache) cache.chain rfl (by
    change Gaussian.Equivalence.NamedEquivalent
      (Paths.OwnerTraceReadings.ownerName (Paths.PreparedPathGluing.finishOwner program.period.closed.traced.prepared))
      (Paths.OwnerTraceReadings.ownerName (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorOwner
        lifted program.sheet))
    rw [← program.period.closed.traced.finishOwner_eq]
    exact program.period.closed.rootReturn)⟩

set_option genInjectivity false in
/-- The retained complete exterior programs and their reciprocal-cap preparations.

The ordered indexed programs equal the actual exterior boundaries, including every required lap and component. -/
structure Preparation (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (lifted :
  Meshes.LiftedPuncturedGrid base)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) where
  /-- The ordered complete original exterior programs with their retained cap covers. -/ programs : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.PreparedProgram regular lifted differential)
  /-- The retained programs project to the exact original exterior boundary list. -/ indexed_eq : programs.map (fun
    prepared => prepared.program.indexed) = lifted.exteriorBoundaries

constructive_injectivity Preparation

/-- Prepare each original exterior program once while preserving its exact ordered boundary list. -/
@[expose] def Preparation.build (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (lifted :
  Meshes.LiftedPuncturedGrid base)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Preparation regular lifted differential :=
  let programs := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorPrograms lifted differential
  ⟨programs.map (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.PreparedProgram.build regular), by
    rw [Data.List.Map.map_map]
    change (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorPrograms lifted differential).map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.indexed = lifted.exteriorBoundaries
    exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorPrograms_indexed lifted differential⟩

set_option genInjectivity false in
/-- An accuracy request consumes its retained program and covers. -/
structure Entry (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (lifted :
  Meshes.LiftedPuncturedGrid base)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (totalTarget areaTarget :
      Normalization.InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The original exterior program and its previously prepared reciprocal covers and closing join. -/ prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.PreparedProgram regular lifted differential
  /-- The original total-comparison target is strictly positive. -/ positive : 0 < totalTarget
  /-- The connected-cap request paid from the original total tolerance while retaining its independent area target. -/
    request : Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest prepared.cap ((totalTarget / 4) / 4)
    areaTarget minimum
  /-- The original final-connector request paid by one quarter of the total target. -/ closing :
    Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.ClosingRequest (totalTarget / 4) minimum prepared.cap.bank
    prepared.closing

constructive_injectivity Entry

namespace Entry

/-- Prepare the original connected cap and closing requests with their retained quarter-paid total and independent area
tolerances. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.PreparedProgram regular lifted
  differential)
    (totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate) (totalPositive : 0 < totalTarget)
      (areaPositive : 0 < areaTarget) (minimum : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry regular lifted differential totalTarget areaTarget
      minimum :=
  have quarterPositive := Fraction.Order.Field.div_pos_direct totalPositive (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)
  ⟨prepared, totalPositive, Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest.build prepared.cap
    ((totalTarget / 4) / 4) areaTarget
    (Fraction.Order.Field.div_pos_direct quarterPositive (by decide)) areaPositive minimum,
    Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.ClosingRequest.build (totalTarget / 4) quarterPositive minimum
      prepared.cap.bank prepared.closing⟩

/-- Take the common original reading stage for connected-cap evaluation and the final closing request. -/
@[expose] def readingIndex (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry regular lifted
  differential totalTarget areaTarget minimum) : Nat :=
  max entry.request.readingIndex entry.closing.maximum

/-- Building an accuracy entry retains the exact original prepared exterior program. -/
theorem build_prepared (prepared : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.PreparedProgram regular
  lifted differential)
    (totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate) (totalPositive : 0 < totalTarget)
      (areaPositive : 0 < areaTarget) (minimum : Nat) :
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry.build prepared totalTarget areaTarget totalPositive
      areaPositive minimum).prepared = prepared := rfl

end Entry

variable {totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}

/-- Take the largest original polynomial stage across all cap-entry requests and the minimum floor. -/
@[expose] def maximum : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry regular lifted
  differential totalTarget areaTarget minimum) → Nat
  | [] => minimum
  | entry :: tail => max entry.request.index
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.maximum tail)

/-- Take the largest original coordinate-reading stage across all cap entries and the minimum floor. -/
@[expose] def readingMaximum : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry regular lifted
  differential totalTarget areaTarget minimum) → Nat
  | [] => minimum
  | entry :: tail => max entry.readingIndex
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.readingMaximum tail)

set_option genInjectivity false in
/-- An original exterior period sample and its exact closed reciprocal-cap polygon.

Retain the shared source primitive bank, final connector, zero-total polygon, unchanged signed area and all paid
comparison bounds. -/
structure SampledEntry (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (lifted :
  Meshes.LiftedPuncturedGrid base)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate) (minimum depth readingIndex : Nat) where
  /-- The original prepared cap entry consumed by this retained sample. -/ entry :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry regular lifted differential totalTarget areaTarget
    minimum
  /-- The actual connected-cap evaluation at the original shared sample, depth and reading stage. -/ result :
    Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest.Evaluation entry.request sample depth
    readingIndex
  /-- The controlled source-primitive request used by the original exterior period comparison. -/ source :
    Readings.PreparedControlledPrimitiveRequests.ControlledSumRequest
    (entry.prepared.program.period.initial.state.parents.map
    (Integration.PreparedEdgeRecasting.recastCenteredEdge (Periods.PeriodMatrix.standardDifferential
      differential.index))) genus
      ((((totalTarget / 4) / 4) / 4) / 4)
  /-- The period source request and retained cap comparison use exactly the same original primitive sum. -/ source_sum :
    source.primitiveSum = result.separated.compared.source.primitiveSum
  /-- The actual scheduled sample of the original exterior period using the retained source request. -/ period :
    Periods.PreparedPeriodPrimitiveRequests.PeriodSample entry.prepared.program.period.initial
    (Integration.PreparedRefinementProgramCore.standardDifferentials genus) (Periods.PeriodMatrix.standardDifferential
      differential.index) source minimum
  /-- The retained period sample is exactly the original integral program's model sample at its selected stage. -/
    program_sample : period.sample = ((entry.prepared.program.period.program differential.index).integral.model
    period.stage).integralSample
  /-- The cap's negative total is exactly the original first value minus the last. -/ closing_eq : -result.cap.total =
    result.firstValue - result.lastValue
  /-- The original final closing increment has squared norm below one quarter of the total target. -/ closing_small :
    Data.Gaussian.Norm.Basic.normSq (-result.cap.total) < totalTarget / 4
  /-- The retained original endpoint coordinate gap satisfies the collar-scaled closing bound. -/ coordinate_closing :
    Data.Gaussian.Norm.Basic.normSq (result.coordinates.first - result.coordinates.last) < collar.coordinateBound /
    64
  /-- The complete retained cap increment path followed by its actual closing increment. -/ polygon :
    Path.IncrementArea.Summary ((result.blocks.map (fun block => block.1 :: block.2)).flatten ++ [-result.cap.total])
  /-- The original closed cap polygon has total increment zero. -/ polygon_total : polygon.total = 0
  /-- Appending the actual closing increment preserves the original cap's signed area exactly. -/ polygon_area :
    polygon.area = result.cap.area
  /-- The original scheduled period sample differs from the open cap total by less than one quarter of the total target.
  -/
  open_integral_close : Data.Gaussian.Norm.Basic.normSq (period.sample - result.cap.total) < totalTarget / 4
  /-- The original scheduled period sample differs from the retained closed polygon total by less than the total target.
  -/
  integral_close : Data.Gaussian.Norm.Basic.normSq (period.sample - polygon.total) < totalTarget

constructive_injectivity SampledEntry

namespace SampledEntry

/-- Read a certified scheduled sample of the original exterior program,
using the same source primitive bank as the cap comparison. -/
@[expose] def build {index depth readingIndex : Nat} {box : Rational.Box}
    {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
    (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry regular lifted differential totalTarget
      areaTarget minimum)
    (result : Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest.Evaluation entry.request sample depth
      readingIndex)
    (closingLater : entry.closing.maximum ≤ readingIndex) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.SampledEntry regular lifted sample totalTarget areaTarget
      minimum depth readingIndex := by
  let program := entry.prepared.program
  let source := program.periodRequest result.separated.compared.source
  have sourceEq : source.primitiveSum = result.separated.compared.source.primitiveSum := program.periodRequest_sum _
  let period := program.period.requestedPrimitiveComparison differential.index source minimum
  have quarterPositive := Fraction.Order.Field.div_pos_direct entry.positive (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)
  have localPositive := Fraction.Order.Field.div_pos_direct quarterPositive (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)
  have scheduledClose : Data.Gaussian.Norm.Basic.normSq (period.sample - result.separated.left.total) < (totalTarget
    / 4) / 4 := by
    rw [result.separated.source_total, ← sourceEq,
      show period.sample - source.primitiveSum = -(source.primitiveSum - period.sample) by ring1,
        Gaussian.Norm.Basic.normSq_neg]
    have periodAccurate := period.accurate
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at periodAccurate
    exact periodAccurate.trans ((Purelib.Data.Rat.Bounds.Quarter.quarter_lt_self (Fraction.Order.Field.div_pos_direct
      localPositive (by decide))).trans
      (Purelib.Data.Rat.Bounds.Quarter.quarter_lt_self localPositive))
  have openClose : Data.Gaussian.Norm.Basic.normSq (period.sample - result.cap.total) < totalTarget / 4 :=
    (fun {first middle last : Normalization.InverseRootPolynomial.Gaussian} {target :
      Normalization.InverseRootPolynomial.Coordinate}
      (before : Data.Gaussian.Norm.Basic.normSq (first - middle) < target / 4)
      (after : Data.Gaussian.Norm.Basic.normSq (middle - last) < target / 4) =>
      show Data.Gaussian.Norm.Basic.normSq (first - last) < target from by
      have triangle : first - last = (first - middle) + (middle - last) := by ring1
      rewrite [triangle]
      exact Polynomial.Clearance.Box.Boundary.Basic.BoundaryClearance.normSq_add_lt_of_quarters before after.le)
        scheduledClose result.total_close
  have closingEq : -result.cap.total = result.firstValue - result.lastValue := by rw [result.total_eq]; ring1
  have closingSmall : Data.Gaussian.Norm.Basic.normSq (-result.cap.total) < totalTarget / 4 := by
    rw [closingEq, result.lastValue_eq, result.firstValue_eq]
    exact Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.ClosingRequest.accurate result.separated.parents
      entry.closing quarterPositive closingLater
  let polygon := Path.IncrementAreaClosure.Summary.close result.cap
  have close : Data.Gaussian.Norm.Basic.normSq (period.sample - polygon.total) < totalTarget := by
    apply (fun {first middle last : Normalization.InverseRootPolynomial.Gaussian} {target :
      Normalization.InverseRootPolynomial.Coordinate}
      (before : Data.Gaussian.Norm.Basic.normSq (first - middle) < target / 4)
      (after : Data.Gaussian.Norm.Basic.normSq (middle - last) < target / 4) =>
      show Data.Gaussian.Norm.Basic.normSq (first - last) < target from by
      have triangle : first - last = (first - middle) + (middle - last) := by ring1
      rewrite [triangle]
      exact Polynomial.Clearance.Box.Boundary.Basic.BoundaryClearance.normSq_add_lt_of_quarters before after.le)
        openClose
    change Data.Gaussian.Norm.Basic.normSq (result.cap.total - 0) < totalTarget / 4
    rw [Gaussian.Basic.sub_zero, ← Gaussian.Norm.Basic.normSq_neg result.cap.total]
    exact closingSmall
  refine ⟨entry, result, source, sourceEq, period, program.period.requestedPrimitiveComparison_sample differential.index
    source minimum,
    closingEq, closingSmall, ?_, polygon, rfl, rfl, openClose, close⟩
  rw [result.coordinates.last_eq, result.coordinates.first_eq]
  exact Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.ClosingRequest.coordinate_accurate result.separated.parents
    entry.closing closingLater

end SampledEntry

set_option genInjectivity false in
/-- The ordered original cap-entry evaluations using one common retained polynomial sample and reading stage. -/
structure Samples (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry regular lifted
  differential totalTarget areaTarget minimum))
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (depth readingIndex :
      Nat) where
  /-- The ordered evaluations of all original exterior entries using the same retained sample. -/ values : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.SampledEntry regular lifted sample totalTarget areaTarget
    minimum depth readingIndex)
  /-- Projecting the retained sampled entries gives exactly the original entry list. -/ entries_eq : values.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.SampledEntry.entry = entries

constructive_injectivity Samples

namespace Samples

variable {index depth readingIndex : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Evaluate every original entry at the shared sufficient stages, retaining the exact ordered entry list. -/
@[expose] def build : (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry regular lifted
  differential totalTarget areaTarget minimum)) →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.maximum entries ≤ index →
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.readingMaximum entries ≤ readingIndex →
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Samples entries sample depth readingIndex
  | [], _, _ => ⟨[], rfl⟩
  | entry :: tail, later, readingLater =>
      have headReading : entry.readingIndex ≤ readingIndex := (Data.Nat.Order.le_max_left _ _).trans readingLater
      let head := entry.request.evaluate sample depth readingIndex ((Data.Nat.Order.le_max_left _ _).trans later)
        ((Data.Nat.Order.le_max_left _ _).trans headReading)
      let remaining := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Samples.build tail
        ((Data.Nat.Order.le_max_right _ _).trans later) ((Data.Nat.Order.le_max_right _ _).trans readingLater)
      ⟨SampledEntry.build entry head ((Data.Nat.Order.le_max_right _ _).trans headReading) :: remaining.values,
        by
          change entry :: remaining.values.map
            Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.SampledEntry.entry = entry :: tail
          exact congrArg (List.cons entry) remaining.entries_eq⟩

end Samples

set_option genInjectivity false in
/-- Count-paid cap comparisons for the complete original exterior preparation.

Total and area allowances remain separate, with their actual payment bounds and independent polynomial and reading
maxima. -/
structure Request (prepared : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Preparation regular lifted
  differential) (totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The retained number of complete original exterior programs. -/ count : Nat
  /-- The retained count-paid total-comparison allowance for each original component. -/ total :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The total allowance is exactly the finite per-term payment of the original total target. -/ total_eq : total =
    Rational.Budget.Aggregate.perTerm totalTarget count
  /-- The retained per-component total allowance is strictly positive. -/ total_positive : 0 < total
  /-- The separate retained count-paid area allowance for each original component. -/ area :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The area allowance is exactly the finite per-term payment of the original area target. -/ area_eq : area =
    Rational.Budget.Aggregate.perTerm areaTarget count
  /-- The retained per-component area allowance is strictly positive. -/ area_positive : 0 < area
  /-- The original count-squared Purelib.Data.Gaussian.Norm.Sum.Bounds.normSq_gaussianSum_map_sub_le of total allowances
    is strictly below the total target. -/ total_paid : (count : Normalization.InverseRootPolynomial.Coordinate) *
    ((count : Normalization.InverseRootPolynomial.Coordinate) * total) < totalTarget
  /-- The original count-squared Purelib.Data.Gaussian.Norm.Sum.Bounds.normSq_gaussianSum_map_sub_le of area allowances
    is strictly below the area target. -/ area_paid : (count : Normalization.InverseRootPolynomial.Coordinate) * ((count
    : Normalization.InverseRootPolynomial.Coordinate) * area) < areaTarget
  /-- The actual ordered cap comparison entries for all original prepared programs. -/ entries : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry regular lifted differential total area minimum)
  /-- Each retained entry has the exact corresponding original prepared program. -/ entries_eq : entries.map
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry.prepared = prepared.programs
  /-- The retained entry count equals the original stored component count. -/ count_eq : entries.length = count
  /-- The sufficient common polynomial sample stage for all original entries. -/ index : Nat
  /-- The polynomial stage is exactly the retained original entry maximum. -/ index_eq : index =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.maximum entries
  /-- The sufficient common coordinate-reading stage for all original entries. -/ readingIndex : Nat
  /-- The reading stage is exactly the retained original reading maximum. -/ readingIndex_eq : readingIndex =
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.readingMaximum entries

constructive_injectivity Request

namespace Request

/-- Prepare separate count-paid total and area tolerances for every original exterior program before taking both stage
maxima. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Preparation regular lifted
  differential) (totalTarget areaTarget : Normalization.InverseRootPolynomial.Coordinate)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) (minimum : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Request prepared totalTarget areaTarget minimum := by
  let programs := prepared.programs
  let count := programs.length
  let total := Rational.Budget.Aggregate.perTerm totalTarget count
  let area := Rational.Budget.Aggregate.perTerm areaTarget count
  have totalLocal : 0 < total := Rational.Budget.Aggregate.perTerm_positive totalPositive count
  have areaLocal : 0 < area := Rational.Budget.Aggregate.perTerm_positive areaPositive count
  let entries := programs.map (fun program => Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry.build
    program total area totalLocal areaLocal minimum)
  have retained : entries.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry.prepared =
    prepared.programs := by
    simp only [entries, Data.List.Map.map_map, Function.comp_def,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry.build_prepared, -eq_self, -iff_self]
    change programs.map (fun value => value) = programs
    induction programs with
    | nil => rfl
    | cons head tail ih => exact congrArg (List.cons head) ih
  exact ⟨count, total, rfl, totalLocal, area, rfl, areaLocal, Rational.Budget.Aggregate.count_mul_perTerm_lt
    totalPositive count,
    Rational.Budget.Aggregate.count_mul_perTerm_lt areaPositive count, entries, retained, Data.List.Map.length_map _
      programs, Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.maximum entries, rfl,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.readingMaximum entries, rfl⟩

variable {prepared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Preparation regular lifted
  differential} {request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Request prepared
  totalTarget areaTarget minimum}
  {index depth readingIndex : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- The request retains the exact original complete exterior boundary occurrences. -/
theorem indexed_eq (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Request prepared totalTarget
  areaTarget minimum) :
    request.entries.map (fun entry => entry.prepared.program.indexed) = lifted.exteriorBoundaries := by
  have retained := congrArg (fun programs : List
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.PreparedProgram regular lifted differential) =>
    programs.map (fun prepared => prepared.program.indexed)) request.entries_eq
  have same : request.entries.map (fun entry => entry.prepared.program.indexed) =
      prepared.programs.map (fun prepared => prepared.program.indexed) := by
    simpa only [Data.List.Map.map_map, Function.comp_def, -eq_self, -iff_self] using retained
  exact same.trans prepared.indexed_eq

set_option genInjectivity false in
/-- The summed original exterior period and cap readings with separately paid total and area comparisons. -/
structure Evaluation (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Request prepared totalTarget
  areaTarget minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (depth readingIndex :
      Nat) where
  /-- The actual original entry evaluations using one shared retained cap sample. -/ samples :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Samples request.entries sample depth readingIndex
  /-- The retained sum of all original scheduled exterior period samples. -/ integral :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The retained integral is exactly the sum of the actual sampled original periods. -/ integral_eq : integral =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.values.map (fun value => value.period.sample))
  /-- The retained sum of all original closed-cap polygon totals. -/ capTotal :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The retained cap total is exactly the sum of the actual closed polygon totals. -/ capTotal_eq : capTotal =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.values.map (fun value => value.polygon.total))
  /-- The total of all retained closed-cap polygons is zero. -/ capTotal_zero : capTotal = 0
  /-- The retained sum of the original exterior source-path areas. -/ sourceArea :
    Normalization.InverseRootPolynomial.Gaussian
  /-- The source area is exactly the sum of the original retained left-path areas. -/ sourceArea_eq : sourceArea =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.values.map (fun value => value.result.separated.left.area))
  /-- The retained sum of all actual closed-cap signed areas. -/ capArea : Normalization.InverseRootPolynomial.Gaussian
  /-- The cap area is exactly the sum of the retained closed polygon areas. -/ capArea_eq : capArea =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.values.map (fun value => value.polygon.area))
  /-- The original total period sample and retained cap total satisfy the requested total error. -/ integral_close :
    Data.Gaussian.Norm.Basic.normSq (integral - capTotal) < totalTarget
  /-- The original source and retained cap area sums satisfy the separate requested area error. -/ area_close :
    Data.Gaussian.Norm.Basic.normSq (sourceArea - capArea) < areaTarget

constructive_injectivity Evaluation

/-- All complete components consume this exact common polynomial sample. -/
@[expose] def evaluate (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Request prepared totalTarget
  areaTarget minimum)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box) (depth readingIndex :
      Nat)
    (later : request.index ≤ index) (readingLater : request.readingIndex ≤ readingIndex) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Request.Evaluation request sample depth readingIndex :=
      by
  let samples : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Samples request.entries sample depth
    readingIndex := Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Samples.build request.entries
    (request.index_eq ▸ later) (request.readingIndex_eq ▸ readingLater)
  have countEq : samples.values.length = request.count := by
    rw [← Data.List.Map.length_map (values := samples.values)
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.SampledEntry.entry, samples.entries_eq,
      request.count_eq]
  let integral := Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.values.map (fun value => value.period.sample))
  let capTotal := Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.values.map (fun value => value.polygon.total))
  let sourceArea := Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.values.map (fun value =>
    value.result.separated.left.area))
  let capArea := Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.values.map (fun value => value.polygon.area))
  have capTotalZero : capTotal = 0 := by
    have zero : ∀ values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.SampledEntry regular lifted
      sample request.total request.area minimum depth readingIndex),
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value => value.polygon.total)) = 0 := by
      intro values
      induction values with
      | nil => rfl
      | cons head tail ih =>
          simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, head.polygon_total, ih,
            Gaussian.Basic.add_zero, -eq_self, -iff_self]
          rfl
    exact zero samples.values
  have integralClose : Data.Gaussian.Norm.Basic.normSq (integral - capTotal) < totalTarget := by
    have estimate := Purelib.Data.Gaussian.Norm.Sum.Bounds.normSq_gaussianSum_map_sub_le samples.values (fun value =>
      value.period.sample)
      (fun value => value.polygon.total) (fun value _ => value.integral_close.le)
    rw [countEq] at estimate
    exact estimate.trans_lt request.total_paid
  have areaClose : Data.Gaussian.Norm.Basic.normSq (sourceArea - capArea) < areaTarget := by
    have estimate := Purelib.Data.Gaussian.Norm.Sum.Bounds.normSq_gaussianSum_map_sub_le samples.values (bound :=
      request.area) (fun value => value.result.separated.left.area)
      (fun value => value.polygon.area) (fun value _ => by rw [value.polygon_area]; exact value.result.area_close.le)
    rw [countEq] at estimate
    exact estimate.trans_lt request.area_paid
  exact ⟨samples, integral, rfl, capTotal, rfl, capTotalZero, sourceArea, rfl, capArea, rfl, integralClose, areaClose⟩

set_option genInjectivity false in
/-- One retained cap-polynomial sample and the complete original request evaluated at its prepared reading stage. -/
structure Acquisition (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Request prepared totalTarget
  areaTarget minimum) (depth : Nat) where
  /-- The one actual cap-polynomial sample acquired at the original shared stage and collar box. -/ sample :
    Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential request.index collar.box
  /-- The complete original cap comparison evaluated using that exact sample and retained reading stage. -/ evaluated :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Request.Evaluation request sample depth
    request.readingIndex

constructive_injectivity Acquisition

/-- Acquire the original shared cap sample once, then evaluate all complete exterior components at the retained stages.
-/
@[expose] def acquire (request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Request prepared totalTarget
  areaTarget minimum) (depth : Nat) : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Request.Acquisition
  request depth :=
  let sample := Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample.build cap differential request.index collar.box
  ⟨sample, request.evaluate sample depth request.readingIndex le_rfl le_rfl⟩

end Request
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison
