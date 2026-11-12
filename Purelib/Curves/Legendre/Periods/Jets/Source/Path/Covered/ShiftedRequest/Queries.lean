module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Agreement
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Queries.Preparation
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Queries
import Purelib.Data.List.DependentProduct

/-! # Actual completed query caches on one built absolute-time target

The original whole geometry factory selects its finite occurrence map.
Every original block Alignment is materialized once. These same caches
propagate genuine old all-query agreement and complete the actual target
checks, retaining existing Commons and acquiring only unpaid root work.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Request

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath.Acquisition.Segment
  (RootComparisons)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

/-- The SAME built target's occurrence, Alignment, query-agreement and actual Completion caches with whole factories.

This exact existing-container type adds no owner or record. The original
old preparation/roots and both parameter owners remain indices. Its query
invariant is computed from old agreement; target Completion is a result,
not an input or a relabelled finite-ready status.
-/
@[expose] def QueryCaches
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {whole : let first := DependentProduct.get (parent :: parents) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {index globalFloor rootStage : Nat}
    (request : Request whole index globalFloor rootStage)
    (wholeEq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks chain roots)
    (old : PreparedParents.QueryAgreement prepared) :=
  (stored : { value : Occurrences blocks request // value = ShiftedGeometry.occurrences
    (prepared := prepared) (ranges := ranges) (allocation := allocation) (admitted := admitted)
    (widths := widths) (oldGeometry := chain) (oldRoots := roots) blocks request wholeEq }) ×
  (aligned : { value : DependentProduct (parent :: parents) (fun outer =>
    RootComparisons.Alignment (DependentProduct.get (parent :: parents) blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) blocks outer).comparison.firstReference) //
    value = DependentProduct.ofFn (parent :: parents)
      (fun outer => (DependentProduct.get (parent :: parents) blocks outer).comparison.align) }) ×
  (queries : { value : PreparedParents.QueryAgreement request.attempt.2.1 //
    value = Occurrences.queryAgreement stored.val aligned.val old }) ×
  { completed : StageAttempt.Completion request.attempt //
    completed = StageAttempt.completeQueries request.attempt queries.val }

namespace QueryCaches

/-- Complete the SAME target using its already retained original occurrence and Alignment products.

Their whole original factory equations preserve both owner/caches. The
shared tail derives the actual query operation and completes the retained
attempt once; no source preparation, lookup, checker, occurrence or Alignment
producer executes here. Existing ready Commons stay owned by that actual attempt.
-/
def ofRetained
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {whole : let first := DependentProduct.get (parent :: parents) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {index globalFloor rootStage : Nat}
    (request : Request whole index globalFloor rootStage)
    (wholeEq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks chain roots)
    (old : PreparedParents.QueryAgreement prepared)
    (stored : Occurrences blocks request)
    (storedEq : stored = ShiftedGeometry.occurrences
      (prepared := prepared) (ranges := ranges) (allocation := allocation) (admitted := admitted)
      (widths := widths) (oldGeometry := chain) (oldRoots := roots) blocks request wholeEq)
    (aligned : DependentProduct (parent :: parents) (fun outer =>
      RootComparisons.Alignment (DependentProduct.get (parent :: parents) blocks outer).comparison.paths
        (DependentProduct.get (parent :: parents) blocks outer).comparison.firstReference))
    (alignedEq : aligned = DependentProduct.ofFn (parent :: parents)
      (fun outer => (DependentProduct.get (parent :: parents) blocks outer).comparison.align)) :
    QueryCaches request wholeEq old :=
  let queries := Occurrences.queryAgreement stored aligned old
  let completed := StageAttempt.completeQueries request.attempt queries
  ⟨⟨stored, storedEq⟩, ⟨aligned, alignedEq⟩, ⟨queries, rfl⟩, ⟨completed, rfl⟩⟩

/-- Read the SAME actual original global occurrence product. -/
@[expose] def occurrences
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {whole : let first := DependentProduct.get (parent :: parents) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {index globalFloor rootStage : Nat}
    {request : Request whole index globalFloor rootStage}
    {wholeEq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks chain roots}
    {old : PreparedParents.QueryAgreement prepared} (retained : QueryCaches request wholeEq old)
    : Occurrences blocks request := retained.1.val

/-- Read the SAME actual original block Alignment product. -/
@[expose] def aligned
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {whole : let first := DependentProduct.get (parent :: parents) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {index globalFloor rootStage : Nat}
    {request : Request whole index globalFloor rootStage}
    {wholeEq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks chain roots}
    {old : PreparedParents.QueryAgreement prepared} (retained : QueryCaches request wholeEq old)
    : DependentProduct (parent :: parents) (fun outer =>
      RootComparisons.Alignment (DependentProduct.get (parent :: parents) blocks outer).comparison.paths
        (DependentProduct.get (parent :: parents) blocks outer).comparison.firstReference) := retained.2.1.val

/-- Read the actual derived all-query operation on this SAME original target preparation. -/
@[expose] def queries
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {whole : let first := DependentProduct.get (parent :: parents) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {index globalFloor rootStage : Nat}
    {request : Request whole index globalFloor rootStage}
    {wholeEq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks chain roots}
    {old : PreparedParents.QueryAgreement prepared} (retained : QueryCaches request wholeEq old)
    : PreparedParents.QueryAgreement request.attempt.2.1 := retained.2.2.1.val

/-- Read the entire actual original target Completion, retaining all its old and new acquisition caches. -/
@[expose] def completion
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {whole : let first := DependentProduct.get (parent :: parents) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {index globalFloor rootStage : Nat}
    {request : Request whole index globalFloor rootStage}
    {wholeEq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks chain roots}
    {old : PreparedParents.QueryAgreement prepared} (retained : QueryCaches request wholeEq old)
    : StageAttempt.Completion request.attempt := retained.2.2.2.val

/-- The retained occurrence product has its original whole factory. -/
@[expose] def OccurrencesLaw : Prop :=
  ∀
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {whole : let first := DependentProduct.get (parent :: parents) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {index globalFloor rootStage : Nat}
    {request : Request whole index globalFloor rootStage}
    {wholeEq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks chain roots}
    {old : PreparedParents.QueryAgreement prepared} (retained : QueryCaches request wholeEq old),
    retained.occurrences = ShiftedGeometry.occurrences
    (prepared := prepared) (ranges := ranges) (allocation := allocation) (admitted := admitted)
    (widths := widths) (oldGeometry := chain) (oldRoots := roots) blocks request wholeEq

/-- The retained occurrence product has its original whole factory. -/
theorem occurrences_eq : OccurrencesLaw := by
  unfold OccurrencesLaw
  intro parameter increment frame basis target count parent parents covered floor baseStart baseFinish
    original stage targets prepared ranges allocation admitted widths blocks chain root roots whole index
    globalFloor rootStage request wholeEq old retained
  exact retained.1.property

/-- The retained alignment product has its original whole factory. -/
@[expose] def AlignmentLaw : Prop :=
  ∀
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {whole : let first := DependentProduct.get (parent :: parents) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {index globalFloor rootStage : Nat}
    {request : Request whole index globalFloor rootStage}
    {wholeEq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks chain roots}
    {old : PreparedParents.QueryAgreement prepared} (retained : QueryCaches request wholeEq old),
    retained.aligned = DependentProduct.ofFn (parent :: parents)
    (fun outer => (DependentProduct.get (parent :: parents) blocks outer).comparison.align)

/-- The retained alignment product has its original whole factory. -/
theorem aligned_eq : AlignmentLaw := by
  unfold AlignmentLaw
  intro parameter increment frame basis target count parent parents covered floor baseStart baseFinish
    original stage targets prepared ranges allocation admitted widths blocks chain root roots whole index
    globalFloor rootStage request wholeEq old retained
  exact retained.2.1.property

/-- The retained query operation uses its original occurrence and alignment caches. -/
@[expose] def QueriesLaw : Prop :=
  ∀
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {whole : let first := DependentProduct.get (parent :: parents) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {index globalFloor rootStage : Nat}
    {request : Request whole index globalFloor rootStage}
    {wholeEq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks chain roots}
    {old : PreparedParents.QueryAgreement prepared} (retained : QueryCaches request wholeEq old),
    retained.queries = Occurrences.queryAgreement retained.occurrences retained.aligned old

/-- The retained query operation uses its original occurrence and alignment caches. -/
theorem queries_eq : QueriesLaw := by
  unfold QueriesLaw
  intro parameter increment frame basis target count parent parents covered floor baseStart baseFinish
    original stage targets prepared ranges allocation admitted widths blocks chain root roots whole index
    globalFloor rootStage request wholeEq old retained
  exact retained.2.2.1.property

/-- The retained completion is the original factory on its stored query operation. -/
@[expose] def CompletionLaw : Prop :=
  ∀
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {whole : let first := DependentProduct.get (parent :: parents) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {index globalFloor rootStage : Nat}
    {request : Request whole index globalFloor rootStage}
    {wholeEq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks chain roots}
    {old : PreparedParents.QueryAgreement prepared} (retained : QueryCaches request wholeEq old),
    retained.completion = StageAttempt.completeQueries request.attempt retained.queries

/-- The retained completion is the original factory on its stored query operation. -/
theorem completion_eq : CompletionLaw := by
  unfold CompletionLaw
  intro parameter increment frame basis target count parent parents covered floor baseStart baseFinish
    original stage targets prepared ranges allocation admitted widths blocks chain root roots whole index
    globalFloor rootStage request wholeEq old retained
  exact retained.2.2.2.property

end QueryCaches

/-- Derive this SAME target's original query caches using an already stored exact Alignment product.

Only the original readonly occurrence map is materialized. The retained
Alignment and its whole producer equation are consumed unchanged; the
shared original tail derives query agreement and completes the own target.
No global source, block, trace or Alignment factory is replayed.
-/
def queryCachesOfAligned
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {whole : let first := DependentProduct.get (parent :: parents) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {index globalFloor rootStage : Nat}
    (request : Request whole index globalFloor rootStage)
    (wholeEq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks chain roots)
    (old : PreparedParents.QueryAgreement prepared)
    (aligned : DependentProduct (parent :: parents) (fun outer =>
      RootComparisons.Alignment (DependentProduct.get (parent :: parents) blocks outer).comparison.paths
        (DependentProduct.get (parent :: parents) blocks outer).comparison.firstReference))
    (alignedEq : aligned = DependentProduct.ofFn (parent :: parents)
      (fun outer => (DependentProduct.get (parent :: parents) blocks outer).comparison.align)) :
    QueryCaches request wholeEq old :=
  let stored := ShiftedGeometry.occurrences (prepared := prepared) (ranges := ranges)
    (allocation := allocation) (admitted := admitted) (widths := widths) (oldGeometry := chain) (oldRoots := roots)
    blocks request wholeEq
  QueryCaches.ofRetained request wholeEq old stored rfl aligned alignedEq

/-- Materialize the finite occurrence/alignment caches and derive this SAME actual target's complete bank internally.

The original target Request/preparations/checks and one global Targets cache
are inputs. The whole original geometry equality constructs membership in
that SAME acquired spine. No block acquisition, source preparation, source
query, finite check or bank lookup is replayed; only the original completion
operation can acquire unpaid endpoint refinements.
-/
def queryCaches
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {whole : let first := DependentProduct.get (parent :: parents) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {index globalFloor rootStage : Nat}
    (request : Request whole index globalFloor rootStage)
    (wholeEq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks chain roots)
    (old : PreparedParents.QueryAgreement prepared) : QueryCaches request wholeEq old :=
  let stored := ShiftedGeometry.occurrences (prepared := prepared) (ranges := ranges)
    (allocation := allocation) (admitted := admitted) (widths := widths) (oldGeometry := chain) (oldRoots := roots)
    blocks request wholeEq
  let aligned := DependentProduct.ofFn (parent :: parents)
    (fun outer => (DependentProduct.get (parent :: parents) blocks outer).comparison.align)
  QueryCaches.ofRetained request wholeEq old stored rfl aligned rfl

/-- The shared retained-cache tail preserves the complete original factory value. -/
private def QueryCachesFactoryLaw : Prop :=
  ∀
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)} {floor : Nat}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    {stage : Nat} {targets : CellEndpoints.Targets original stage}
    {prepared : PreparedParents covered floor targets}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {blocks : Blocks (target := target) prepared ranges allocation admitted widths}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {whole : let first := DependentProduct.get (parent :: parents) blocks 0
      ShiftedGeometry (target := target) (basis := basis) (count := count)
        (startPoint parent) (startPoint parent) first.first.root.value.name first.first.root.value.name}
    {index globalFloor rootStage : Nat}
    (request : Request whole index globalFloor rootStage)
    (wholeEq : whole = ShiftedGeometry.build prepared ranges allocation admitted widths blocks chain roots)
    (old : PreparedParents.QueryAgreement prepared),
    queryCaches request wholeEq old =
    let stored := ShiftedGeometry.occurrences (prepared := prepared) (ranges := ranges)
      (allocation := allocation) (admitted := admitted) (widths := widths) (oldGeometry := chain) (oldRoots := roots)
      blocks request wholeEq
    let aligned := DependentProduct.ofFn (parent :: parents)
      (fun outer => (DependentProduct.get (parent :: parents) blocks outer).comparison.align)
    let queries := Occurrences.queryAgreement stored aligned old
    let completed := StageAttempt.completeQueries request.attempt queries
    ⟨⟨stored, rfl⟩, ⟨aligned, rfl⟩, ⟨queries, rfl⟩, ⟨completed, rfl⟩⟩

/-- The shared retained-cache tail preserves the complete original factory value. -/
private theorem queryCaches_factory : QueryCachesFactoryLaw := by
  unfold QueryCachesFactoryLaw
  intro parameter increment frame basis target count parent parents covered floor baseStart baseFinish
    original stage targets prepared ranges allocation admitted widths blocks chain root roots whole index
    globalFloor rootStage request wholeEq old
  unfold queryCaches QueryCaches.ofRetained
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Request

end
