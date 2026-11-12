module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Refinement
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Endpoints.Partition.Primitive
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.Primitive
public import Purelib.Data.List.DependentProduct.Flatten
import Purelib.Algebra.FiniteSum.DependentProduct
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Data.List.DependentProduct
import Purelib.Riemann.Integration.PreparedConstantModels.Primitive
import Purelib.Riemann.Paths.OwnerTracePath.Primitive.Sewing
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Tactic.QuotientFreeOmega

/-! # Actual paid primitive sewing of the whole original physical Spine

The whole original refinement remains a runtime input. Nested parent banks
follow the SAME original Segment and parent products, including empty words.
Structural product flattening consumes their actual new primitive Spines.
The original geometric and root chains then construct every handoff in that
order and retain the literal source and paid finish Owners separately.

New source/finish observations use the original child accuracy. Their
comparisons retain the distinct old requests. Genuine closing root evidence
and normalization of independent domain primitive offsets remain separate.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine

open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets (UniformPathCertificates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Algebra.FiniteSum
open Purelib.Algebra.FiniteSum.Fin (sumFin sumProduct)
open Purelib.Riemann.Integration.PreparedConstantModels.PreparedEdge (RootedSpine)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath.Primitive.Spine (Sewing)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Topology

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {count floor : Nat} {sheet : Fin 2} {ambient : Geometry.Rational.Box}
variable {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets originalPath stage} {accuracy : AccuracyRequest}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] ownerRootName

namespace Compared

variable {width : {start finish : Canonical} → ClearSegment (Paths.polynomial parameter) ambient start finish →
  AccuracyRequest}
variable {start finish : Canonical} {physicalPath : ClearPath (Paths.polynomial parameter) ambient start finish}
variable {within : physicalPath.WithinAmbient} {owner : Owner ((Paths.polynomial parameter).eval start)}
variable {row : Row} {retained : Acquisition width physicalPath within owner}
variable {observed : OwnerPath.Primitive.Spine (row.expression parameter) accuracy retained.covered.traced.trace.get}
variable {views : Acquisition.Observations retained observed}
variable {sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
  (targets := targets) width physicalPath within owner retained.spine}
variable {allocation : targets.endpoint = 4 * accuracy.tolerance}
variable {gridAmbient : Geometry.Rational.Box}
variable {grid : Polynomial.Geometry.Grid.ClearGrid (Fibre.frameCurve frame).polynomial gridAmbient}
variable (axes : PrimitiveAxes grid)
variable (compared : Compared row retained views sources allocation)

namespace Refinement

variable {axes compared} {splits : Splits axes compared} {comparisonRequest requested : AccuracyRequest}
variable (refined : Refinement axes compared splits comparisonRequest requested)

namespace Sewn

/-- One original centered parent with the exact scalar sample paid by its actual rooted primitive Spine. -/
@[expose] def Parent (parent : CenteredEdge (Fibre.frameCurve frame) basis) :=
  Σ sample : Canonical,
    RootedSpine (curve := Fibre.frameCurve frame) (differential := basis)
      parent.edge (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3)
      0 1 parent.edge.baseInside (of_decide_eq_true rfl) sample

/-- Read the unchanged original Segment parent words, preserving empty and repeated occurrences. -/
@[expose] def parentWords :=
  Sources.parentWords width physicalPath within owner retained.spine refined.original.prepared

/-- Keep one actual parent-primitive product at each literal original Segment occurrence, including empty products. -/
@[expose] def Parents :=
  DependentProduct (parentWords refined) (fun outer =>
    DependentProduct ((parentWords refined)[outer.val]'outer.isLt) (fun inner =>
      Parent (row := row) (requested := requested)
        (((parentWords refined)[outer.val]'outer.isLt)[inner.val]'inner.isLt)))

/-- Read only the actual stored sample from one original parent-primitive cache. -/
private def readSample (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    (actual : Parent (row := row) (requested := requested) parent) : Canonical := actual.1

/-- Read only the number of new handoffs retained inside one SAME original parent primitive cache. -/
private def readCount (parent : CenteredEdge (Fibre.frameCurve frame) basis)
    (actual : Parent (row := row) (requested := requested) parent) : Nat :=
  RootedSpine.junctionCount (curve := Fibre.frameCurve frame) (differential := basis)
    (edge := parent.edge) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3)
    (lower := 0) (upper := 1) (lowerInside := parent.edge.baseInside)
    (upperInside := (of_decide_eq_true rfl)) (sample := actual.1) actual.2

/-- Build the original parent primitive Spines on one SAME retained Segment crop bank, without replaying any crop. -/
private def segmentParents (outer : Fin (parentWords refined).length) :
    DependentProduct ((parentWords refined)[outer.val]'outer.isLt) (fun inner =>
      Parent (row := row) (requested := requested)
        (((parentWords refined)[outer.val]'outer.isLt)[inner.val]'inner.isLt)) :=
  let stored := Segments.entry axes refined.original refined.segments outer
  let bank := DependentProduct.ofFn
    (Sources.segmentAt width physicalPath within owner retained.spine
      refined.original.prepared outer).parents.covered.parents
    (fun inner =>
      ((⟨(stored.lifted.original.children inner).rowSample,
        (stored.lifted.original.children inner).primitive
        (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (row := row) (accuracy := accuracy) (comparisonRequest := comparisonRequest)
        (requested := requested)⟩) :
        Parent (row := row) (requested := requested)
          ((Sources.segmentAt width physicalPath within owner retained.spine refined.original.prepared
            outer).parents.covered.parents[inner.val]'inner.isLt)))
  DependentProduct.castItems
    (Sources.segmentAt_parents_eq width physicalPath within owner retained.spine refined.original.prepared outer).symm
    bank
    (resultFamily := fun index => Parent (row := row) (requested := requested)
      (((parentWords refined)[outer.val]'outer.isLt)[index.val]'index.isLt))
    (sameFamily := DependentProduct.castItems_family
      (family := Parent (row := row) (requested := requested))
      (Sources.segmentAt_parents_eq width physicalPath within owner retained.spine
        refined.original.prepared outer).symm)

/-- Construct each actual parent primitive once, retaining the original outer product even for empty Segment words. -/
def buildParents : Parents refined :=
  DependentProduct.ofFn (parentWords refined) (segmentParents refined)

/-- Exact whole-assembly identity retains its literal original flattened parent word. -/
private theorem assemblyParents_eq
    (assembly : Sources.Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish)
    (factory : assembly = Sources.assemble width physicalPath within owner retained.spine refined.original.prepared) :
    assembly.geometry.parents = (parentWords refined).flatten :=
  (congrArg (fun actual : Sources.Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish => actual.geometry.parents) factory).trans
    (Sources.assemble_parents width physicalPath within owner retained.spine refined.original.prepared)

/-- Flatten only the SAME stored nested parent products along exact original whole-parent-list identity. -/
def flattenParents
    (assembly : Sources.Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish)
    (factory : assembly = Sources.assemble width physicalPath within owner retained.spine refined.original.prepared)
    (parents : Parents refined) :
    DependentProduct assembly.geometry.parents (fun index =>
      Parent (row := row) (requested := requested) (assembly.geometry.parents[index.val]'index.isLt)) :=
  DependentProduct.castItems (assemblyParents_eq refined assembly factory)
    (DependentProduct.flattenItems (family := Parent (row := row) (requested := requested))
      (parentWords refined) parents)
    (resultFamily := fun index => Parent (row := row) (requested := requested)
      (assembly.geometry.parents[index.val]'index.isLt))
    (sameFamily := DependentProduct.castItems_family
      (family := Parent (row := row) (requested := requested)) (assemblyParents_eq refined assembly factory))

/-- The actual retained per-Segment primitive bank preserves its original full row sample exactly. -/
private theorem segmentParents_sum (outer : Fin (parentWords refined).length) :
    sumProduct ((parentWords refined)[outer.val]'outer.isLt) (segmentParents refined outer)
      (readSample (row := row) (requested := requested)) =
      (Segments.entry axes refined.original refined.segments outer).lifted.original.rowSample := by
  let stored := Segments.entry axes refined.original refined.segments outer
  let items := (Sources.segmentAt width physicalPath within owner retained.spine refined.original.prepared
    outer).parents.covered.parents
  let entries := fun inner : Fin items.length =>
    ((⟨(stored.lifted.original.children inner).rowSample,
        (stored.lifted.original.children inner).primitive
        (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (row := row) (accuracy := accuracy) (comparisonRequest := comparisonRequest)
        (requested := requested)⟩) :
      Parent (row := row) (requested := requested) (items[inner.val]'inner.isLt))
  have original := Fin.sumProduct_castItems (family := Parent (row := row) (requested := requested))
    (Sources.segmentAt_parents_eq width physicalPath within owner retained.spine refined.original.prepared outer)
    (DependentProduct.ofFn items entries) (readSample (row := row) (requested := requested))
  have samples := Fin.sumProduct_ofFn (family := Parent (row := row) (requested := requested))
    items entries
    (readSample (row := row) (requested := requested))
  exact original.trans (samples.trans stored.lifted.original.rowSample_eq.symm)

/-- The SAME stored Segment primitive bank contains exactly its original interval count plus its parent count. -/
private theorem segmentParents_count (outer : Fin (parentWords refined).length) :
    DependentProduct.sumItems ((parentWords refined)[outer.val]'outer.isLt) (segmentParents refined outer)
      (readCount (row := row) (requested := requested)) =
        (DependentProduct.get (parentWords refined) refined.splitting outer).count +
          ((parentWords refined)[outer.val]'outer.isLt).length := by
  let stored := Segments.entry axes refined.original refined.segments outer
  let items := (Sources.segmentAt width physicalPath within owner retained.spine refined.original.prepared
    outer).parents.covered.parents
  let entries := fun inner : Fin items.length =>
    ((⟨(stored.lifted.original.children inner).rowSample,
        (stored.lifted.original.children inner).primitive
        (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (row := row) (accuracy := accuracy) (comparisonRequest := comparisonRequest)
        (requested := requested)⟩) :
      Parent (row := row) (requested := requested) (items[inner.val]'inner.isLt))
  let bank := DependentProduct.ofFn items entries
  let splitting := DependentProduct.get (parentWords refined) refined.splitting outer
  have original := DependentProduct.sumItems_castItems
    (family := Parent (row := row) (requested := requested))
    (Sources.segmentAt_parents_eq width physicalPath within owner retained.spine refined.original.prepared outer)
    bank (readCount (row := row) (requested := requested))
  have weights := DependentProduct.sum_congr items bank
    (fun index actual => readCount (row := row) (requested := requested) (items[index.val]'index.isLt) actual)
    (fun index _actual => (splitting.partitionAt index).intervals.length + 1)
    (fun index =>
      (congrArg (readCount (row := row) (requested := requested) (items[index.val]'index.isLt))
        (DependentProduct.get_ofFn items entries index)).trans
          (((stored.lifted.original.children index).primitive_count
            (frame := frame) (basis := basis) (count := count) (floor := floor)
            (sheet := sheet) (row := row) (accuracy := accuracy) (comparisonRequest := comparisonRequest)
            (requested := requested)).trans
              (congrArg (fun length : Nat => length + 1) (stored.lifted.original.partition_count index))))
  have addition := DependentProduct.sum_add items bank
    (fun index _actual => (splitting.partitionAt index).intervals.length) (fun _index _actual => 1)
  have counts := PrimitiveSplits.count_eq_sum splitting bank
  have cardinal := DependentProduct.sum_one items bank
  have sameLength := congrArg List.length
    (Sources.segmentAt_parents_eq width physicalPath within owner retained.spine refined.original.prepared outer)
  exact original.trans ((weights.trans (addition.trans (congrArg₂ Nat.add counts cardinal))).trans
    (congrArg (Nat.add splitting.count) sameLength))

/-- The actual cached nested parent bank has the count determined by its SAME original supplied split product. -/
private theorem parents_count (parents : Parents refined) (factory : parents = buildParents refined) :
    DependentProduct.sum (parentWords refined)
      (fun outer actual => DependentProduct.sumItems ((parentWords refined)[outer.val]'outer.isLt) actual
        (readCount (row := row) (requested := requested))) parents =
      Splits.intervalCount axes refined.original refined.splitting + (parentWords refined).flatten.length := by
  have same := congrArg (fun actual : Parents refined => DependentProduct.sum (parentWords refined)
    (fun outer entries => DependentProduct.sumItems ((parentWords refined)[outer.val]'outer.isLt) entries
      (readCount (row := row) (requested := requested))) actual) factory
  have entries := DependentProduct.sum_congr (parentWords refined) (buildParents refined)
    (fun outer actual => DependentProduct.sumItems ((parentWords refined)[outer.val]'outer.isLt) actual
      (readCount (row := row) (requested := requested)))
    (fun outer _actual => (DependentProduct.get (parentWords refined) refined.splitting outer).count +
      ((parentWords refined)[outer.val]'outer.isLt).length)
    (fun outer => (congrArg (fun actual =>
      DependentProduct.sumItems ((parentWords refined)[outer.val]'outer.isLt) actual
        (readCount (row := row) (requested := requested)))
      (DependentProduct.get_ofFn (parentWords refined) (segmentParents refined) outer)).trans
        (segmentParents_count refined outer))
  have addition := DependentProduct.sum_add (parentWords refined) (buildParents refined)
    (fun outer _actual => (DependentProduct.get (parentWords refined) refined.splitting outer).count)
    (fun outer _actual => ((parentWords refined)[outer.val]'outer.isLt).length)
  have splitting := DependentProduct.sum_independent (parentWords refined)
    (buildParents refined) refined.splitting
    (fun outer => (DependentProduct.get (parentWords refined) refined.splitting outer).count)
  have selected := DependentProduct.sum_congr (parentWords refined) refined.splitting
    (fun outer _actual => (DependentProduct.get (parentWords refined) refined.splitting outer).count)
    (fun _outer actual => actual.count) (fun _outer => rfl)
  have lengths := DependentProduct.sum_lengths (parentWords refined) (buildParents refined)
  exact same.trans (entries.trans (addition.trans (congrArg₂ Nat.add (splitting.trans selected) lengths)))

/-- Flattening the SAME actual primitive caches preserves their exact original nested handoff count. -/
private theorem flattenParents_count
    (assembly : Sources.Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish)
    (assemblyEq : assembly = Sources.assemble width physicalPath within owner retained.spine refined.original.prepared)
    (parents : Parents refined) (parentsEq : parents = buildParents refined) :
    DependentProduct.sumItems assembly.geometry.parents (flattenParents refined assembly assemblyEq parents)
      (readCount (row := row) (requested := requested)) =
        Splits.intervalCount axes refined.original refined.splitting + (parentWords refined).flatten.length :=
  (DependentProduct.sumItems_castItems (family := Parent (row := row) (requested := requested))
    (assemblyParents_eq refined assembly assemblyEq).symm
    (DependentProduct.flattenItems (family := Parent (row := row) (requested := requested))
      (parentWords refined) parents) (readCount (row := row) (requested := requested))).trans
    ((DependentProduct.sumItems_flattenItems (family := Parent (row := row) (requested := requested))
      (parentWords refined) parents (readCount (row := row) (requested := requested))).trans
        (parents_count refined parents parentsEq))

/-- The actual cached nested bank retains the original Segment/parent sample sum, including every empty word. -/
private theorem parents_sum (parents : Parents refined) (factory : parents = buildParents refined) :
    sumFin (fun outer => sumProduct ((parentWords refined)[outer.val]'outer.isLt)
      (DependentProduct.get (parentWords refined) parents outer) (readSample (row := row) (requested := requested))) =
        refined.rowSample := by
  have same := congrArg (fun actual : Parents refined => sumFin (fun outer =>
    sumProduct ((parentWords refined)[outer.val]'outer.isLt)
      (DependentProduct.get (parentWords refined) actual outer) (readSample (row := row) (requested := requested))))
    factory
  have entries := Fin.sumFin_congr (fun outer =>
    (congrArg (fun actual => sumProduct ((parentWords refined)[outer.val]'outer.isLt) actual
      (readSample (row := row) (requested := requested)))
      (DependentProduct.get_ofFn (parentWords refined) (segmentParents refined) outer)).trans
      (segmentParents_sum refined outer))
  exact same.trans (entries.trans refined.rowSample_eq.symm)

/-- The actual flattened primitive bank keeps the exact original full-Spine row sample. -/
private theorem flattenParents_sum
    (assembly : Sources.Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish)
    (assemblyEq : assembly = Sources.assemble width physicalPath within owner retained.spine refined.original.prepared)
    (parents : Parents refined) (parentsEq : parents = buildParents refined) :
    sumProduct assembly.geometry.parents (flattenParents refined assembly assemblyEq parents)
      (readSample (row := row) (requested := requested)) = refined.rowSample :=
  (Fin.sumProduct_castItems (family := Parent (row := row) (requested := requested))
    (assemblyParents_eq refined assembly assemblyEq).symm
    (DependentProduct.flattenItems (family := Parent (row := row) (requested := requested))
      (parentWords refined) parents) (readSample (row := row) (requested := requested))).trans
    ((Fin.sumProduct_flattenItems (family := Parent (row := row) (requested := requested))
      (parentWords refined) parents (readSample (row := row) (requested := requested))).trans
      (parents_sum refined parents parentsEq))

/-- A primitive Vertex at the original source Owner and actual common child accuracy. -/
@[expose] def SourceVertex :=
  Primitive.Vertex (row.expression parameter) start owner (OwnerPath.Primitive.localRequest requested 3)

/-- A primitive Vertex at the original paid finish Owner and actual common child accuracy. -/
@[expose] def TargetVertex :=
  Primitive.Vertex (row.expression parameter) finish retained.covered.traced.finishOwner
    (OwnerPath.Primitive.localRequest requested 3)

/-- Both actual old/new endpoint comparisons retain their distinct original request accuracies and exact factories. -/
@[expose] def EndpointComparisons
    (initial : SourceVertex (row := row) (requested := requested) (owner := owner))
    (terminal : TargetVertex (row := row) (requested := requested) (retained := retained)) :=
  let old := refined.original.observations.original
  {actual : Observation.Comparison old.first.observation initial.observation
      comparisonRequest.tolerance //
    actual = old.first.original.compare (radicand := Paths.polynomial parameter)
      (expression := row.expression parameter) initial.original
      (NamedEquivalent.refl (ownerName owner))
      old.first.observation initial.observation comparisonRequest} ×
  {actual : Observation.Comparison old.last.observation terminal.observation
      comparisonRequest.tolerance //
    actual = old.last.original.compare (radicand := Paths.polynomial parameter)
      (expression := row.expression parameter) terminal.original
      (NamedEquivalent.refl (ownerName retained.covered.traced.finishOwner))
      old.last.observation terminal.observation comparisonRequest}

/-- Compare both SAME old endpoint requests with the independent new common-accuracy observations. -/
def compareEndpoints
    (initial : SourceVertex (row := row) (requested := requested) (owner := owner))
    (terminal : TargetVertex (row := row) (requested := requested) (retained := retained)) :
    EndpointComparisons refined initial terminal :=
  let old := refined.original.observations.original
  let source := old.first.original.compare (radicand := Paths.polynomial parameter)
      (expression := row.expression parameter) initial.original
    (NamedEquivalent.refl (ownerName owner))
    old.first.observation initial.observation comparisonRequest
  let target := old.last.original.compare (radicand := Paths.polynomial parameter)
      (expression := row.expression parameter) terminal.original
    (NamedEquivalent.refl (ownerName retained.covered.traced.finishOwner))
    old.last.observation terminal.observation comparisonRequest
  ⟨⟨source, rfl⟩, ⟨target, rfl⟩⟩

/-- Sew only the actual cached primitive bank through the SAME original geometric and signed root chains. -/
def sewCore
    (assembly : Sources.Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish)
    (assemblyEq : assembly = Sources.assemble width physicalPath within owner retained.spine refined.original.prepared)
    (parents : Parents refined) (parentsEq : parents = buildParents refined)
    (initial : SourceVertex (row := row) (requested := requested) (owner := owner))
    (terminal : TargetVertex (row := row) (requested := requested) (retained := retained)) :
    Sewing (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
      (accuracy := OwnerPath.Primitive.localRequest requested 3) initial terminal refined.rowSample :=
  let actual := flattenParents refined assembly assemblyEq parents
  let samples := fun index => (DependentProduct.get assembly.geometry.parents actual index).1
  let pieces : CenteredPathChain.Primitive.Pieces (curve := Fibre.frameCurve frame) (differential := basis)
      (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3) assembly.geometry.parents samples :=
    DependentProduct.ofFn assembly.geometry.parents
      (fun index => (DependentProduct.get assembly.geometry.parents actual index).2)
  let sameParents := congrArg (fun source : Sources.Assembled (frame := frame) (basis := basis) (count := count)
    (floor := floor) (sheet := sheet) (targets := targets) start finish => source.geometry.parents) assemblyEq
  let roots := PreparedBankRootChains.RootChain.castChildren sameParents.symm refined.roots
  let namedRoots := PreparedBankRootChains.RootChain.castNames
    (show ownerRootName owner.parameterNonzero owner = ownerName owner from by
      unfold ownerRootName
      rfl)
    (show ownerRootName retained.covered.traced.finishOwner.parameterNonzero
        retained.covered.traced.finishOwner = ownerName retained.covered.traced.finishOwner from by
      unfold ownerRootName
      rfl) roots
  let joined := CenteredPathChain.Primitive.sewParents (curve := Fibre.frameCurve frame) (differential := basis)
    (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3)
    assembly.geometry.chain owner retained.covered.traced.finishOwner namedRoots samples pieces initial terminal
  Sewing.castSample (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3)
    (flattenParents_sum refined assembly assemblyEq parents parentsEq) joined
/-- Combine the original interval charge and the two literal parent-count contributions. -/
private theorem wholeCountStep (intervals parents : Nat) :
    (intervals + parents) + parents + 1 = intervals + 2 * parents + 1 := by
  omega0

/-- The actual full parent fold adds its original final comparison and exactly two handoffs per parent overall. -/
private theorem sewCore_count
    (assembly : Sources.Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish)
    (assemblyEq : assembly = Sources.assemble width physicalPath within owner retained.spine refined.original.prepared)
    (parents : Parents refined) (parentsEq : parents = buildParents refined)
    (initial : SourceVertex (row := row) (requested := requested) (owner := owner))
    (terminal : TargetVertex (row := row) (requested := requested) (retained := retained)) :
    (sewCore refined assembly assemblyEq parents parentsEq initial terminal).junctions.length =
      Splits.handoffCount axes refined.original refined.splitting := by
  let actual := flattenParents refined assembly assemblyEq parents
  let samples := fun index => (DependentProduct.get assembly.geometry.parents actual index).1
  let pieces : CenteredPathChain.Primitive.Pieces (curve := Fibre.frameCurve frame) (differential := basis)
      (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3) assembly.geometry.parents samples :=
    DependentProduct.ofFn assembly.geometry.parents
      (fun index => (DependentProduct.get assembly.geometry.parents actual index).2)
  let sameParents := congrArg (fun source : Sources.Assembled (frame := frame) (basis := basis) (count := count)
    (floor := floor) (sheet := sheet) (targets := targets) start finish => source.geometry.parents) assemblyEq
  let roots := PreparedBankRootChains.RootChain.castChildren sameParents.symm refined.roots
  let namedRoots := PreparedBankRootChains.RootChain.castNames
    (show ownerRootName owner.parameterNonzero owner = ownerName owner from by
      unfold ownerRootName
      rfl)
    (show ownerRootName retained.covered.traced.finishOwner.parameterNonzero
        retained.covered.traced.finishOwner = ownerName retained.covered.traced.finishOwner from by
      unfold ownerRootName
      rfl) roots
  let joined := CenteredPathChain.Primitive.sewParents (curve := Fibre.frameCurve frame) (differential := basis)
    (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3)
    assembly.geometry.chain owner retained.covered.traced.finishOwner namedRoots samples pieces initial terminal
  have originalCount := CenteredPathChain.Primitive.pieceCount_ofFn
    (curve := Fibre.frameCurve frame) (differential := basis)
    (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3) assembly.geometry.parents actual
  have childCount := originalCount.trans (flattenParents_count refined assembly assemblyEq parents parentsEq)
  have parentCount := congrArg List.length (assemblyParents_eq refined assembly assemblyEq)
  have joinedCount := CenteredPathChain.Primitive.sewParents_count
    (curve := Fibre.frameCurve frame) (differential := basis)
    (row.expression parameter) (OwnerPath.Primitive.localRequest requested 3)
    assembly.geometry.chain owner retained.covered.traced.finishOwner namedRoots samples pieces initial terminal
  have scalarCount : joined.junctions.length =
      Splits.handoffCount axes refined.original refined.splitting :=
    joinedCount.trans ((congrArg (fun value : Nat => value + 1)
      (congrArg₂ Nat.add childCount parentCount)).trans
        (wholeCountStep (Splits.intervalCount axes refined.original refined.splitting)
          (parentWords refined).flatten.length))
  change (Sewing.castSample (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3)
    (flattenParents_sum refined assembly assemblyEq parents parentsEq) joined).junctions.length = _
  exact (Sewing.castSample_count (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3)
    (flattenParents_sum refined assembly assemblyEq parents parentsEq) joined).trans scalarCount

end Sewn

/-- The SAME complete refinement and actual assembled source bank with all newly cached primitive sewing evidence.

The old source/finish observations remain inside the original refinement.
Separate new common-accuracy endpoint observations retain their actual
factories and old/new comparisons. The final actual owner path preserves
source and paid-finish Owners; no closing root comparison is assumed.
-/
@[expose] def Sewn :=
  Σ original : {value : Refinement axes compared splits comparisonRequest requested // value = refined},
  Σ assembly : {value : Sources.Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sheet := sheet) (targets := targets) start finish //
    value = Sources.assemble width physicalPath within owner retained.spine original.val.original.prepared},
  Σ parents : {value : Sewn.Parents original.val // value = Sewn.buildParents original.val},
  Σ initial : {value : Sewn.SourceVertex (row := row) (requested := requested) (owner := owner) //
    value = Primitive.Vertex.build (row.expression parameter) start owner
      (OwnerPath.Primitive.localRequest requested 3) (Row.defined parameter start row owner)},
  Σ terminal : {value : Sewn.TargetVertex (row := row) (requested := requested) (retained := retained) //
    value = Primitive.Vertex.build (row.expression parameter) finish retained.covered.traced.finishOwner
      (OwnerPath.Primitive.localRequest requested 3)
      (Row.defined parameter finish row retained.covered.traced.finishOwner)},
  Σ _compared : Sewn.EndpointComparisons original.val initial.val terminal.val,
    {actual : Sewing (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
        (accuracy := OwnerPath.Primitive.localRequest requested 3) initial.val terminal.val original.val.rowSample //
      actual = Sewn.sewCore original.val assembly.val assembly.property parents.val parents.property
        initial.val terminal.val}

namespace Sewn

/-- Pack abstract original inputs and completed new caches without normalizing any observation or source factory. -/
private def pack
    (original : {value : Refinement axes compared splits comparisonRequest requested // value = refined})
    (assembly : {value : Sources.Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
        (sheet := sheet) (targets := targets) start finish //
      value = Sources.assemble width physicalPath within owner retained.spine original.val.original.prepared})
    (parents : {value : Parents original.val // value = buildParents original.val})
    (initial : {value : SourceVertex (row := row) (requested := requested) (owner := owner) //
      value = Primitive.Vertex.build (row.expression parameter) start owner
        (OwnerPath.Primitive.localRequest requested 3) (Row.defined parameter start row owner)})
    (terminal : {value : TargetVertex (row := row) (requested := requested) (retained := retained) //
      value = Primitive.Vertex.build (row.expression parameter) finish retained.covered.traced.finishOwner
        (OwnerPath.Primitive.localRequest requested 3)
        (Row.defined parameter finish row retained.covered.traced.finishOwner)})
    (comparisons : EndpointComparisons original.val initial.val terminal.val)
    (actual : Sewing (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
      (accuracy := OwnerPath.Primitive.localRequest requested 3) initial.val terminal.val original.val.rowSample)
    (factory : actual = sewCore original.val assembly.val assembly.property parents.val parents.property
      initial.val terminal.val) : Sewn refined :=
  ⟨original, assembly, parents, initial, terminal, comparisons, ⟨actual, factory⟩⟩

/-- Construct the whole original-source primitive sewing from its SAME completed six-channel refinement.

Actual parent primitive factories run once at each original Segment/parent
occurrence. Later flattening and root-chain folds consume only those stored
values. The two new endpoint requests are selected before their comparisons;
neither old endpoint request is retagged to the new accuracy.
-/
def build : Sewn refined :=
  let original := refined
  let assembly := Sources.assemble width physicalPath within owner retained.spine original.original.prepared
  let parents := buildParents original
  let initial := Primitive.Vertex.build (row.expression parameter) start owner
    (OwnerPath.Primitive.localRequest requested 3) (Row.defined parameter start row owner)
  let terminal := Primitive.Vertex.build (row.expression parameter) finish retained.covered.traced.finishOwner
    (OwnerPath.Primitive.localRequest requested 3)
    (Row.defined parameter finish row retained.covered.traced.finishOwner)
  let comparisons := compareEndpoints original initial terminal
  let actual := sewCore original assembly rfl parents rfl initial terminal
  pack refined ⟨original, rfl⟩ ⟨assembly, rfl⟩ ⟨parents, rfl⟩
    ⟨initial, rfl⟩ ⟨terminal, rfl⟩ comparisons actual rfl

variable {refined} (sewn : Sewn refined)

/-- Read the SAME whole input refinement, including empty Segments and every original Query, Point and certificate. -/
@[expose] def original : Refinement axes compared splits comparisonRequest requested := sewn.1.val

/-- Read the actual original assembled geometry/cover/source product constructed and retained once. -/
@[expose] def assembly : Sources.Assembled (frame := frame) (basis := basis) (count := count) (floor := floor)
    (sheet := sheet) (targets := targets) start finish := sewn.2.1.val

/-- Read every actual parent primitive cache in its exact original Segment/parent product, including empty words. -/
@[expose] def parents : Parents sewn.original := sewn.2.2.1.val

/-- Read the independently selected new common-accuracy observation at the unchanged original source Owner. -/
@[expose] def first : SourceVertex (row := row) (requested := requested) (owner := owner) :=
  sewn.2.2.2.1.val

/-- Read the separate new common-accuracy observation at the unchanged literal paid finish Owner. -/
@[expose] def last : TargetVertex (row := row) (requested := requested) (retained := retained) :=
  sewn.2.2.2.2.1.val

/-- Read both actual old/new endpoint comparisons without selecting or retagging any request. -/
@[expose] def comparisons : EndpointComparisons sewn.original sewn.first sewn.last := sewn.2.2.2.2.2.1

/-- Read the actual sewn owner path, complete old/new observation Spine and all paid new handoff values. -/
@[expose] def actual : Sewing (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) sewn.first sewn.last sewn.original.rowSample :=
  sewn.2.2.2.2.2.2.val

/-- Read the actual whole source-to-paid-finish owner path independently of the labelled lifted path. -/
@[expose] def path : OwnerPath (Paths.polynomial parameter) start owner finish retained.covered.traced.finishOwner :=
  Sewing.path (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) sewn.actual

/-- Read the complete actual primitive Spine, including every retained local stationary comparison. -/
@[expose] def spine : OwnerPath.Primitive.Spine (row.expression parameter)
    (OwnerPath.Primitive.localRequest requested 3) sewn.path :=
  Sewing.observed (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) sewn.actual

/-- Read the exact new stationary handoff values in original occurrence order. -/
@[expose] def junctions : List Canonical :=
  Sewing.junctions (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) sewn.actual

/-- The complete original refinement is unchanged, not replaced by its root/coordinate/sample summaries. -/
theorem original_eq : sewn.original = refined := sewn.1.property

/-- The exact new handoff count is computable from the SAME original Splits before any crop acquisition. -/
theorem count_eq : sewn.junctions.length = Splits.handoffCount axes compared splits := by
  have factory := congrArg
    (fun actual : Sewing (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
      (accuracy := OwnerPath.Primitive.localRequest requested 3) sewn.first sewn.last sewn.original.rowSample =>
      actual.junctions.length) sewn.2.2.2.2.2.2.property
  have actualCount := factory.trans (sewCore_count sewn.original sewn.assembly sewn.2.1.property
    sewn.parents sewn.2.2.1.property sewn.first sewn.last)
  have originalInputs := congrArg
    (fun value : Acquisition width physicalPath within owner ×
      (Σ old : Compared row retained views sources allocation, Splits axes old) =>
      Splits.handoffCount axes value.2.1 value.2.2) sewn.original.inputs_eq
  exact actualCount.trans originalInputs

/-- All new comparisons pay the actual source-to-paid-finish increment against the SAME original row sample. -/
theorem increment_eq : sewn.last.value - sewn.first.value =
    sewn.original.rowSample + Norm.Sum.Basic.gaussianSum sewn.junctions :=
  Sewing.increment_eq (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) sewn.actual

/-- The exact retained number of new stationary comparisons pays the finite whole-Spine sewing error. -/
theorem error_le : Norm.Basic.normSq
    (sewn.last.value - sewn.first.value - sewn.original.rowSample) ≤
      (sewn.junctions.length : Rational) *
        ((sewn.junctions.length : Rational) * (OwnerPath.Primitive.localRequest requested 3).tolerance) :=
  Sewing.error_le (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) sewn.actual

/-- The common child request selected before observations pays the actual newly constructed handoff error.

Only the retained sewing residual is paid. Old endpoint comparisons, the
row-integrand remainder and independent primitive normalization retain their
separate original bounds and obligations.
-/
theorem error_lt (target : AccuracyRequest)
    (selected : requested = Splits.childRequest axes compared splits target) :
    Norm.Basic.normSq (sewn.last.value - sewn.first.value - sewn.original.rowSample) < target.tolerance := by
  have allowance := congrArg
    (fun request : AccuracyRequest => (OwnerPath.Primitive.localRequest request 3).tolerance) selected
  have paid := Splits.childRequest_payment axes compared splits target
  have count := sewn.count_eq
  have payment : (sewn.junctions.length : Rational) *
      ((sewn.junctions.length : Rational) * (OwnerPath.Primitive.localRequest requested 3).tolerance) <
        target.tolerance := by
    exact Eq.mpr (congrArg (fun length : Nat => (length : Rational) *
      ((length : Rational) * (OwnerPath.Primitive.localRequest requested 3).tolerance) < target.tolerance) count)
      (Eq.mpr (congrArg (fun tolerance : Rational =>
        (Splits.handoffCount axes compared splits : Rational) *
          ((Splits.handoffCount axes compared splits : Rational) * tolerance) < target.tolerance) allowance) paid)
  exact sewn.error_le.trans_lt payment

/-- The actual sewn primitive increment pays the SAME retained source row-integrand sample internally.

The first finite term pays new handoffs. The second is the original actual
crop-integral remainder bound, with every old endpoint comparison retained.
This concerns the row relation and does not identify it with a six-channel
period or assume normalization of independent domain primitive constants.
-/
theorem integral_error_le : Norm.Basic.normSq
    (sewn.last.value - sewn.first.value - (PathModel.mk sewn.original.relationCells).integralSample) ≤
      2 * ((sewn.junctions.length : Rational) *
        ((sewn.junctions.length : Rational) * (OwnerPath.Primitive.localRequest requested 3).tolerance) +
          sewn.original.rowBound) := by
  have decomposition :
      sewn.last.value - sewn.first.value - (PathModel.mk sewn.original.relationCells).integralSample =
        (sewn.last.value - sewn.first.value - sewn.original.rowSample) +
          (sewn.original.rowSample - (PathModel.mk sewn.original.relationCells).integralSample) := by ring1
  rewrite [decomposition]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct sewn.error_le sewn.original.row_integral_le)
      (of_decide_eq_true rfl : (0 : Rational) ≤ 2))

/-- The unchanged old source request and actual new source request pay their separate original accuracies. -/
theorem source_error_lt : Norm.Basic.normSq
    (sewn.original.original.observations.original.first.value - sewn.first.value) <
      16 * ((OwnerPath.Primitive.vertexRequest accuracy).tolerance +
        (OwnerPath.Primitive.vertexRequest (OwnerPath.Primitive.localRequest requested 3)).tolerance) +
      4 * comparisonRequest.tolerance :=
  Observation.Comparison.requested_error_lt
    (leftTarget := (OwnerPath.Primitive.vertexRequest accuracy).tolerance)
    (rightTarget := (OwnerPath.Primitive.vertexRequest (OwnerPath.Primitive.localRequest requested 3)).tolerance)
    (target := comparisonRequest.tolerance) sewn.original.original.observations.original.first.requested
    sewn.first.requested sewn.comparisons.1.val

/-- The unchanged old finish request and actual new finish request retain the same two-accuracy finite payment. -/
theorem target_error_lt : Norm.Basic.normSq
    (sewn.original.original.observations.original.last.value - sewn.last.value) <
      16 * ((OwnerPath.Primitive.vertexRequest accuracy).tolerance +
        (OwnerPath.Primitive.vertexRequest (OwnerPath.Primitive.localRequest requested 3)).tolerance) +
      4 * comparisonRequest.tolerance :=
  Observation.Comparison.requested_error_lt
    (leftTarget := (OwnerPath.Primitive.vertexRequest accuracy).tolerance)
    (rightTarget := (OwnerPath.Primitive.vertexRequest (OwnerPath.Primitive.localRequest requested 3)).tolerance)
    (target := comparisonRequest.tolerance) sewn.original.original.observations.original.last.requested
    sewn.last.requested sewn.comparisons.2.val

/-- Close only with an actual independent signed root-return certificate and exact original coordinate closure.

The supplied names belong to the literal paid finish and source Owners.
The SAME final/initial observations supply a new real closing join and its
stationary comparison. A geometric loop or sheet label alone cannot supply
this input. Independent domain primitive normalization remains separate.
-/
def close (same : finish = start)
    (returning : NamedEquivalent (ownerName retained.covered.traced.finishOwner) (ownerName owner)) :
    Sewing (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
      (accuracy := OwnerPath.Primitive.localRequest requested 3) sewn.first sewn.first sewn.original.rowSample :=
  let closing := Sewing.stationary (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) sewn.last sewn.first same returning
  Sewing.castSample (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3)
    ((Canonical.add_comm sewn.original.rowSample 0).trans (Canonical.zero_add sewn.original.rowSample))
    (Sewing.append (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
      (accuracy := OwnerPath.Primitive.localRequest requested 3) sewn.actual closing)
/-- The genuine signed closing comparison contributes one additional actual handoff. -/
theorem close_count (same : finish = start)
    (returning : NamedEquivalent (ownerName retained.covered.traced.finishOwner) (ownerName owner)) :
    (sewn.close same returning).junctions.length = Splits.handoffCount axes compared splits + 1 := by
  let closing := Sewing.stationary (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) sewn.last sewn.first same returning
  have transported := Sewing.castSample_count
    (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3)
    ((Canonical.add_comm sewn.original.rowSample 0).trans (Canonical.zero_add sewn.original.rowSample))
    (Sewing.append (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
      (accuracy := OwnerPath.Primitive.localRequest requested 3) sewn.actual closing)
  have appended := Sewing.append_count
    (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) sewn.actual closing
  have closed := Sewing.stationary_count
    (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) sewn.last sewn.first same returning
  exact transported.trans (appended.trans (congrArg₂ Nat.add sewn.count_eq closed))

/-- The actual signed closure is paid only by the separately preselected H + 1 request.

The exact geometric closure and genuine paid-finish-to-source root relation
remain required. The bound concerns this SAME closed row sewing alone;
old endpoints, model remainders and independent primitive normalization
remain outside this target.
-/
theorem close_error_lt (target : AccuracyRequest)
    (selected : requested = Splits.closingChildRequest axes compared splits target)
    (same : finish = start)
    (returning : NamedEquivalent (ownerName retained.covered.traced.finishOwner) (ownerName owner)) :
    Norm.Basic.normSq (sewn.first.value - sewn.first.value - sewn.original.rowSample) < target.tolerance := by
  have allowance := congrArg
    (fun request : AccuracyRequest => (OwnerPath.Primitive.localRequest request 3).tolerance) selected
  have paid := Splits.closingChildRequest_payment axes compared splits target
  have count := sewn.close_count same returning
  have payment : ((sewn.close same returning).junctions.length : Rational) *
      (((sewn.close same returning).junctions.length : Rational) *
        (OwnerPath.Primitive.localRequest requested 3).tolerance) < target.tolerance := by
    exact Eq.mpr (congrArg (fun length : Nat => (length : Rational) *
      ((length : Rational) * (OwnerPath.Primitive.localRequest requested 3).tolerance) < target.tolerance) count)
      (Eq.mpr (congrArg (fun tolerance : Rational =>
        ((Splits.handoffCount axes compared splits + 1 : Nat) : Rational) *
          (((Splits.handoffCount axes compared splits + 1 : Nat) : Rational) * tolerance) < target.tolerance)
        allowance) paid)
  exact (Sewing.error_le (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
    (accuracy := OwnerPath.Primitive.localRequest requested 3) (sewn.close same returning)).trans_lt payment

end Sewn

end Refinement
namespace Splits

/-- Choose the finite sewing request before executing and retaining the actual refinement and paid sewing once.

The original Compared and Splits remain input owners. The child request is
computed before Refinement.build acquires any crop or primitive observation.
Both actual whole factories are retained. The internally proved target pays
only new handoffs; old endpoint comparisons and row/model remainders keep
their original bounds, and no closing or primitive normalization is assumed.
-/
def sew (splits : Splits axes compared) (comparisonRequest target : AccuracyRequest) :
    Σ refined : {value : Refinement axes compared splits comparisonRequest
        (childRequest axes compared splits target) //
      value = Refinement.build axes compared splits comparisonRequest
        (childRequest axes compared splits target)},
    {sewn : Refinement.Sewn refined.val //
      sewn = Refinement.Sewn.build refined.val ∧
      Norm.Basic.normSq (sewn.last.value - sewn.first.value - sewn.original.rowSample) < target.tolerance} :=
  let requested := childRequest axes compared splits target
  let refined := Refinement.build axes compared splits comparisonRequest requested
  let sewn := Refinement.Sewn.build refined
  ⟨⟨refined, rfl⟩, ⟨sewn, rfl, sewn.error_lt target rfl⟩⟩

/-- Reserve the actual closing handoff before acquisition and retain the complete independently paid signed closure.

The genuine original root return and coordinate closure are supplied as
geometric evidence. The H + 1 request is computed before either refinement
or observation factories run. Actual refinement, sewing and closing values
are retained with their exact factories; no period or primitive-offset
normalization follows from these row-sewing bounds.
-/
def sewClosed (splits : Splits axes compared) (comparisonRequest target : AccuracyRequest)
    (same : finish = start)
    (returning : NamedEquivalent (ownerName retained.covered.traced.finishOwner) (ownerName owner)) :
    Σ refined : {value : Refinement axes compared splits comparisonRequest
        (closingChildRequest axes compared splits target) //
      value = Refinement.build axes compared splits comparisonRequest
        (closingChildRequest axes compared splits target)},
    Σ sewn : {value : Refinement.Sewn refined.val // value = Refinement.Sewn.build refined.val},
    {actual : Sewing (polynomial := Paths.polynomial parameter) (expression := row.expression parameter)
        (accuracy := OwnerPath.Primitive.localRequest (closingChildRequest axes compared splits target) 3)
        sewn.val.first sewn.val.first sewn.val.original.rowSample //
      actual = sewn.val.close same returning ∧
        Norm.Basic.normSq (sewn.val.first.value - sewn.val.first.value - sewn.val.original.rowSample) <
          target.tolerance} :=
  let requested := closingChildRequest axes compared splits target
  let refined := Refinement.build axes compared splits comparisonRequest requested
  let sewn := Refinement.Sewn.build refined
  let actual := sewn.close same returning
  let paid := sewn.close_error_lt target rfl same returning
  ⟨⟨refined, rfl⟩, ⟨sewn, rfl⟩, ⟨actual, rfl, paid⟩⟩

end Splits
end Compared

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Spine

end
