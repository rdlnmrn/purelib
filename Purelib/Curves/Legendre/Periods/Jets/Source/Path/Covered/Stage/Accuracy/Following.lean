module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Accuracy.Source
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy.Retained
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Euler
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Payment
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Trace
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Data.Sigma.Factories
meta import Purelib.Elab.ConstructiveInjectivity

/-! # The retained following-grid fibre on one original endpoint Request

The raw endpoint Request, rather than an enclosing positive-node getter,
owns its cover, chain and sufficient source pair. The exact five original
cache fields retain their original pointwise factory equations. Their two
supplied operation values are the actual source-selection and reprepare
functions. Packaging and transport retain them without invocation; the
explicit grid builder executes the original five factories once in order.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Riemann.Topology
open Purelib.Curves.Legendre.Periods.Jets.Variation
open StageAttempt.Requested.Shifted

section

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (endpoint : Requested covered chain current floor rootStage accuracy)

/-- The original requested-source/member pair at this endpoint and the actual following joint mesh accuracy.

The raw Request fixes its own selected stage, cover, chain and source
floor. The whole endpoint Frame fixes the original coarse count and
connection request before the same increment request is minimized.
-/
@[expose] def FollowingSource (nextCurrent : Nat) (direction : Canonical) (moving : direction ≠ 0)
    (spatial : AccuracyRequest) (refinement : Nat) (positive : 0 < refinement) : Type _ :=
  let intervals := PositiveGridNode.coarseIntervals frame direction * refinement
  let positiveCount := PositiveGridNode.fineIntervals_positive frame direction refinement positive
  let nextAccuracy := (PositiveGridNode.connectionRequest frame intervals positiveCount spatial).minimum
    (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
      (Sampling.gridIncrement_nonzero intervals positiveCount direction moving))
  CompletedSource (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) covered chain
    (max nextCurrent (endpoint.selected.stage + 1)) floor rootStage nextAccuracy

variable (direction : Canonical) (moving : direction ≠ 0) (spatial : AccuracyRequest)
    (nextCurrent refinement : Nat) (positive : 0 < refinement)
    (ranges : ParameterRange (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (parents := parent :: parents)
      covered)
    (allocation : ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (targetCurrent targetFloor targetRootStage : Nat)
    (sourceFactory : Unit → endpoint.FollowingSource nextCurrent direction moving spatial refinement positive)
    (queryFactory : (paid : endpoint.FollowingSource nextCurrent direction moving spatial refinement positive) →
      QueryAgreement paid.1.prepared)

namespace FollowingGrid

/-- The original table, completion vector and trace at one retained following source and query operation.

This exact dependent tuple keeps the three whole factory equations and
all original geometric indices. Naming it shares the same type between
the full grid and its constructor, without acquiring or replacing a cache.
-/
@[expose] def TableCaches (common : endpoint.FollowingSource nextCurrent direction moving spatial refinement positive)
    (queries : QueryAgreement common.1.prepared) : Type _ :=
  let intervals := PositiveGridNode.coarseIntervals frame direction * refinement
  let positiveCount := PositiveGridNode.fineIntervals_positive frame direction refinement positive
  (table : { value :
      PositiveGridNode.Table
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents)
      (covered := covered) (chain := chain)
      (current := max nextCurrent (endpoint.selected.stage + 1)) (floor := floor) (rootStage := rootStage)
      intervals positiveCount direction moving
      (PositiveGridNode.connectionRequest frame intervals positiveCount spatial)
      common.1 common.2 ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage //
    value = PositiveGridNode.Table.build
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents)
      (covered := covered) (chain := chain)
      (current := max nextCurrent (endpoint.selected.stage + 1)) (floor := floor) (rootStage := rootStage)
      intervals positiveCount direction moving
      (PositiveGridNode.connectionRequest frame intervals positiveCount spatial)
      common.1 common.2 ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage }) ×
  (_completions : { value : PositiveGridNode.Table.Completions
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents)
      (covered := covered) (chain := chain)
      (current := max nextCurrent (endpoint.selected.stage + 1)) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positiveCount) (direction := direction) (moving := moving)
      (spatial := PositiveGridNode.connectionRequest frame intervals positiveCount spatial)
      (source := common.1) (member := common.2)
      (ranges := ranges) (allocation := allocation)
      (admitted := admitted) (widths := widths) (roots := roots)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      table.val queries //
    value = PositiveGridNode.Table.Completions.build
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents)
      (covered := covered) (chain := chain)
      (current := max nextCurrent (endpoint.selected.stage + 1)) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positiveCount) (direction := direction) (moving := moving)
      (spatial := PositiveGridNode.connectionRequest frame intervals positiveCount spatial)
      (source := common.1) (member := common.2)
      (ranges := ranges) (allocation := allocation)
      (admitted := admitted) (widths := widths) (roots := roots)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      table.val queries }) ×
  { value : PositiveGridNode.Table.Trace
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents)
      (covered := covered) (chain := chain)
      (current := max nextCurrent (endpoint.selected.stage + 1)) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positiveCount) (direction := direction) (moving := moving)
      (spatial := PositiveGridNode.connectionRequest frame intervals positiveCount spatial)
      (source := common.1) (member := common.2)
      (ranges := ranges) (allocation := allocation)
      (admitted := admitted) (widths := widths) (roots := roots)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage) table.val //
    value = PositiveGridNode.Table.Trace.build
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents)
      (covered := covered) (chain := chain)
      (current := max nextCurrent (endpoint.selected.stage + 1)) (floor := floor) (rootStage := rootStage)
      (intervals := intervals) (positive := positiveCount) (direction := direction) (moving := moving)
      (spatial := PositiveGridNode.connectionRequest frame intervals positiveCount spatial)
      (source := common.1) (member := common.2)
      (ranges := ranges) (allocation := allocation)
      (admitted := admitted) (widths := widths) (roots := roots)
      (targetCurrent := targetCurrent) (targetFloor := targetFloor) (targetRootStage := targetRootStage)
      table.val }

/-- Execute the original table, completion and trace factories once on the supplied source and queries. -/
private def buildTableCaches
    (common : endpoint.FollowingSource nextCurrent direction moving spatial refinement positive)
    (queries : QueryAgreement common.1.prepared) :
    TableCaches endpoint direction moving spatial nextCurrent refinement positive
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage common queries :=
  let intervals := PositiveGridNode.coarseIntervals frame direction * refinement
  let positiveCount := PositiveGridNode.fineIntervals_positive frame direction refinement positive
  let table := PositiveGridNode.Table.build
      (parameter := parameter) (frame := frame) (basis := basis) (count := count)
      (parent := parent) (parents := parents) (covered := covered) (chain := chain)
      (current := max nextCurrent (endpoint.selected.stage + 1)) (floor := floor) (rootStage := rootStage)
      intervals positiveCount direction moving
      (PositiveGridNode.connectionRequest frame intervals positiveCount spatial)
      common.1 common.2 ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage
  let completions := PositiveGridNode.Table.Completions.build table queries
  let trace := PositiveGridNode.Table.Trace.build table
  Data.Sigma.pair ⟨table, rfl⟩ (Data.Sigma.pair ⟨completions, rfl⟩ ⟨trace, rfl⟩)

end FollowingGrid

/-- The SAME five retained following caches and their original pointwise factory equations.

The two operation arguments name the actual retained factories; no new
query relation is assumed or constructed here. Specializing them to the
original incoming source/reprepare operations gives the existing node Grid
by exact definition reduction, including every original factory predicate.
-/
@[expose] def FollowingGrid : Type _ :=
  (common : { value : endpoint.FollowingSource nextCurrent direction moving spatial refinement positive //
    value = sourceFactory () }) ×
  (queries : { value : QueryAgreement common.val.1.prepared // value = queryFactory common.val }) ×
  FollowingGrid.TableCaches endpoint direction moving spatial nextCurrent refinement positive
    ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage common.val queries.val

namespace FollowingGrid

/-- Execute the five original following-grid factories in source, query, table, completion and trace order.

The two retained operations run once. The remaining factories consume
those same values through the original three-cache constructor.
-/
def build : endpoint.FollowingGrid direction moving spatial nextCurrent refinement positive
    ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage sourceFactory queryFactory :=
  Data.Sigma.ofSubtypeFactoriesWithTail sourceFactory queryFactory
    (γ := fun common queries => TableCaches endpoint direction moving spatial nextCurrent refinement positive
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage common queries)
    (fun common queries => buildTableCaches endpoint direction moving spatial nextCurrent refinement positive
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage common queries)

/-- The constructed grid is the complete original ordered five-factory execution. -/
private theorem constructed_factory :
    build endpoint direction moving spatial nextCurrent refinement positive ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage sourceFactory queryFactory =
    (let intervals := PositiveGridNode.coarseIntervals frame direction * refinement
     let positiveCount := PositiveGridNode.fineIntervals_positive frame direction refinement positive
     let common := sourceFactory ()
     let queries := queryFactory common
     let table := PositiveGridNode.Table.build
       (parameter := parameter) (frame := frame) (basis := basis) (count := count)
       (parent := parent) (parents := parents) (covered := covered) (chain := chain)
       (current := max nextCurrent (endpoint.selected.stage + 1)) (floor := floor) (rootStage := rootStage)
       intervals positiveCount direction moving
       (PositiveGridNode.connectionRequest frame intervals positiveCount spatial)
       common.1 common.2 ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage
     let completions := PositiveGridNode.Table.Completions.build table queries
     let trace := PositiveGridNode.Table.Trace.build table
     ⟨⟨common, rfl⟩, ⟨queries, rfl⟩, ⟨table, rfl⟩, ⟨completions, rfl⟩, ⟨trace, rfl⟩⟩) := rfl

/-- The original five complete values and their factory predicates are retained by the following-grid builder. -/
theorem build_factory :
    build endpoint direction moving spatial nextCurrent refinement positive ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage sourceFactory queryFactory =
    (let intervals := PositiveGridNode.coarseIntervals frame direction * refinement
     let positiveCount := PositiveGridNode.fineIntervals_positive frame direction refinement positive
     let common := sourceFactory ()
     let queries := queryFactory common
     let table := PositiveGridNode.Table.build
       (parameter := parameter) (frame := frame) (basis := basis) (count := count)
       (parent := parent) (parents := parents) (covered := covered) (chain := chain)
       (current := max nextCurrent (endpoint.selected.stage + 1)) (floor := floor) (rootStage := rootStage)
       intervals positiveCount direction moving
       (PositiveGridNode.connectionRequest frame intervals positiveCount spatial)
       common.1 common.2 ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage
     let completions := PositiveGridNode.Table.Completions.build table queries
     let trace := PositiveGridNode.Table.Trace.build table
     ⟨⟨common, rfl⟩, ⟨queries, rfl⟩, ⟨table, rfl⟩, ⟨completions, rfl⟩, ⟨trace, rfl⟩⟩) :=
  constructed_factory endpoint direction moving spatial nextCurrent refinement positive
    ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage sourceFactory queryFactory

set_option genInjectivity false in
/-- The original external geometric inputs, two actual operation values and SAME five-cache following Grid.

This record packages the actual range/allocation/width inputs
with the retained operations and cache. Admission remains the original
local normSq comparison. The operations are retained as functions and
are never invoked by packaging or endpoint transport.
-/
structure Window
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    {endpoint : Requested covered chain current floor rootStage accuracy}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    (direction : Canonical) (moving : direction ≠ 0) (spatial : AccuracyRequest)
    (nextCurrent refinement : Nat) (positive : 0 < refinement)
    (targetCurrent targetFloor targetRootStage : Nat) : Type _ where
  /-- The same original range cache on the endpoint's covered-parent family. -/
  ranges : ParameterRange covered
  /-- The same strip allocation retains its original local direction admission. -/
  allocation : { value : ParameterRange.StripAllocation ranges // Norm.Basic.normSq direction ≤ value.bound }
  /-- The original per-parent width requests. -/
  widths : Fin (parent :: parents).length → AccuracyRequest
  /-- The actual sufficient-source operation, retained without invoking it. -/
  sourceFactory : Unit → endpoint.FollowingSource nextCurrent direction moving spatial refinement positive
  /-- The actual query operation on that same sufficient-source family. -/
  queryFactory : (paid : endpoint.FollowingSource nextCurrent direction moving spatial refinement positive) →
    QueryAgreement paid.1.prepared
  /-- The complete original five-cache grid at those same inputs and operations. -/
  grid : endpoint.FollowingGrid direction moving spatial nextCurrent refinement positive
      ranges allocation.val allocation.property widths roots targetCurrent targetFloor targetRootStage
      sourceFactory queryFactory

constructive_injectivity Window

/-- Package the actual geometric inputs and already built cache without invoking any of its five factories. -/
@[expose] def ofGrid (grid : endpoint.FollowingGrid direction moving spatial nextCurrent refinement positive
    ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage sourceFactory queryFactory) :
    Window (endpoint := endpoint) (roots := roots) direction moving spatial nextCurrent refinement positive
      targetCurrent targetFloor targetRootStage :=
  ⟨ranges, ⟨allocation, admitted⟩, widths, sourceFactory, queryFactory, grid⟩

/-- The whole joint cache is exactly the original geometry, operations and five-cache value in their original order. -/
theorem ofGrid_factory (grid : endpoint.FollowingGrid direction moving spatial nextCurrent refinement positive
    ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage sourceFactory queryFactory) :
    ofGrid endpoint direction moving spatial nextCurrent refinement positive ranges allocation admitted widths
      roots targetCurrent targetFloor targetRootStage sourceFactory queryFactory grid =
      ⟨ranges, ⟨allocation, admitted⟩, widths, sourceFactory, queryFactory, grid⟩ := rfl

namespace Window

variable (window : Window (endpoint := endpoint) (roots := roots)
    direction moving spatial nextCurrent refinement positive targetCurrent targetFloor targetRootStage)

/-- Read the SAME complete cached source/query/table/completion/trace tuple at its own original geometric inputs. -/
def cache : endpoint.FollowingGrid direction moving spatial nextCurrent refinement positive
    window.ranges window.allocation.val window.allocation.property window.widths roots
    targetCurrent targetFloor targetRootStage window.sourceFactory window.queryFactory := window.grid

end Window

/-- Reading a freshly packaged window preserves its original dependent cache. -/
private theorem packaged_cache (grid : endpoint.FollowingGrid direction moving spatial nextCurrent refinement positive
    ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage sourceFactory queryFactory) :
    (ofGrid endpoint direction moving spatial nextCurrent refinement positive ranges allocation admitted widths
      roots targetCurrent targetFloor targetRootStage sourceFactory queryFactory grid).cache = grid := rfl

/-- Packaging and reading the joint window retains the complete SAME original five-cache value. -/
theorem cache_ofGrid (grid : endpoint.FollowingGrid direction moving spatial nextCurrent refinement positive
    ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage sourceFactory queryFactory) :
    (ofGrid endpoint direction moving spatial nextCurrent refinement positive ranges allocation admitted widths
      roots targetCurrent targetFloor targetRootStage sourceFactory queryFactory grid).cache = grid :=
  packaged_cache endpoint direction moving spatial nextCurrent refinement positive ranges allocation admitted widths
    roots targetCurrent targetFloor targetRootStage sourceFactory queryFactory grid

end FollowingGrid

end

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

end
