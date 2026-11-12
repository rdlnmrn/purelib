module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Preparation.Endpoint
public import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Refinement
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot

/-! # Original prepared-parent admissions from actual bank-owner comparisons

Each input comparison relates the original retained endpoint owner to the
actual selected bank owner. Existing common-refinement acquisition supplies
the strict geometric inclusions. The unchanged selected source and endpoint
attachments then derive the original local primitive and bank bounds.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
variable {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}

/-- Derive the existing cell admission from two genuine retained branch certificates at the actual bank lookups.

The original endpoint attachments are transported to this same cached cell.
Its exact displacement and computed target supply the quantitative inputs to
the existing admission producer; no endpoint or primitive estimate is added.
-/
def admitBranches (prepared : PreparedParent patch count floor covered targets)
    {bank : Vertex.Bank parameter targets.endpoint}
    (first : Vertex.Bank.Found bank (startPoint parent))
    (last : Vertex.Bank.Found bank (finishPoint parent))
    (firstBranch : RootBranch prepared.firstSample first.original.sample)
    (lastBranch : RootBranch prepared.lastSample last.original.sample) :
    Cell.Admission prepared.preparation.cell targets bank :=
  let starting := prepared.preparation.endpoint first prepared.firstPlan.val
    prepared.preparation.attached.firstAttachment firstBranch
  let finishing := prepared.preparation.endpoint last prepared.lastPlan.val
    prepared.preparation.attached.lastAttachment lastBranch
  Cell.Admission.build prepared.preparation.cell targets bank (cost parent)
    (by rewrite [prepared.displacement_eq]; exact Fraction.Order.Basic.le_refl _) prepared.target_eq starting finishing

/-- Both actual common-refinement caches and the existing admission of the identical retained original cell.

The real bank lookups and independently derived owner comparisons remain
indices. Each refinement keeps its actual index, common-owner factory and
both strict inclusions before that same owner is used by the admission.
-/
abbrev Admitted (prepared : PreparedParent patch count floor covered targets)
    {bank : Vertex.Bank parameter targets.endpoint}
    (first : Vertex.Bank.Found bank (startPoint parent))
    (last : Vertex.Bank.Found bank (finishPoint parent))
    (firstEquivalent : NamedEquivalent prepared.firstSample.certificate.value.name
      first.original.sample.certificate.value.name)
    (lastEquivalent : NamedEquivalent prepared.lastSample.certificate.value.name
      last.original.sample.certificate.value.name) :=
  (firstRefinement : RootBranch.Refinement prepared.firstSample first.original.sample firstEquivalent) ×
  (lastRefinement : RootBranch.Refinement prepared.lastSample last.original.sample lastEquivalent) ×
  { admission : Cell.Admission prepared.preparation.cell targets bank //
    admission = prepared.admitBranches first last firstRefinement.2.val lastRefinement.2.val }

namespace Admitted

variable {prepared : PreparedParent patch count floor covered targets}
variable {bank : Vertex.Bank parameter targets.endpoint}
variable {first : Vertex.Bank.Found bank (startPoint parent)}
variable {last : Vertex.Bank.Found bank (finishPoint parent)}
variable {firstEquivalent : NamedEquivalent prepared.firstSample.certificate.value.name
  first.original.sample.certificate.value.name}
variable {lastEquivalent : NamedEquivalent prepared.lastSample.certificate.value.name
  last.original.sample.certificate.value.name}

/-- Read the original source-to-bank common refinement with its actual selected refinement index. -/
@[expose] def firstRefinement (admitted : Admitted prepared first last firstEquivalent lastEquivalent) :
    RootBranch.Refinement prepared.firstSample first.original.sample firstEquivalent := admitted.1

/-- Read the independent finish-to-bank refinement without another refinement or endpoint query. -/
@[expose] def lastRefinement (admitted : Admitted prepared first last firstEquivalent lastEquivalent) :
    RootBranch.Refinement prepared.lastSample last.original.sample lastEquivalent := admitted.2.1

/-- Read the actual original cell admission with all internally computed endpoint comparisons and local bounds. -/
@[expose] def admission (admitted : Admitted prepared first last firstEquivalent lastEquivalent) :
    Cell.Admission prepared.preparation.cell targets bank := admitted.2.2.val

/-- The retained admission consumes the identical two cached common-owner branches and all original cell data. -/
theorem admission_eq (admitted : Admitted prepared first last firstEquivalent lastEquivalent) :
    admitted.admission = prepared.admitBranches first last
      admitted.firstRefinement.2.val admitted.lastRefinement.2.val := admitted.2.2.property

section RetainedRefinements

variable (prepared first last firstEquivalent lastEquivalent)

/-- Construct the original admission from two already retained complete refinement caches and the actual cell.

Both supplied acquisitions remain unchanged. Only the original numerical
admission is built, from this prepared cell, its actual bank readings,
endpoint plans and Targets; no Common refinement is acquired again.
-/
def ofRefinements
    (firstCache : RootBranch.Refinement prepared.firstSample first.original.sample firstEquivalent)
    (lastCache : RootBranch.Refinement prepared.lastSample last.original.sample lastEquivalent) :
    Admitted prepared first last firstEquivalent lastEquivalent :=
  let admission := prepared.admitBranches first last firstCache.2.val lastCache.2.val
  ⟨firstCache, lastCache, ⟨admission, rfl⟩⟩

/-- The retained-refinement admission keeps the complete supplied starting acquisition. -/
theorem ofRefinements_first
    (firstCache : RootBranch.Refinement prepared.firstSample first.original.sample firstEquivalent)
    (lastCache : RootBranch.Refinement prepared.lastSample last.original.sample lastEquivalent) :
    (ofRefinements prepared first last firstEquivalent lastEquivalent firstCache lastCache).firstRefinement =
      firstCache := by
  unfold ofRefinements firstRefinement
  rfl

/-- The retained-refinement admission keeps the complete supplied finishing acquisition. -/
theorem ofRefinements_last
    (firstCache : RootBranch.Refinement prepared.firstSample first.original.sample firstEquivalent)
    (lastCache : RootBranch.Refinement prepared.lastSample last.original.sample lastEquivalent) :
    (ofRefinements prepared first last firstEquivalent lastEquivalent firstCache lastCache).lastRefinement =
      lastCache := by
  unfold ofRefinements lastRefinement
  rfl

end RetainedRefinements

end Admitted

/-- Compare the retained source-point certificate with the original prepared edge query at fraction zero. -/
def firstQueryEquivalent (prepared : PreparedParent patch count floor covered targets) :
    NamedEquivalent (parent.edge.rootName 0 (by decide +kernel))
      prepared.firstSample.certificate.value.name :=
  patch.point_equivalent_at count 0 (by decide +kernel) parent.edge.point_zero
    (start_inside patch count) prepared.firstSample

/-- Compare the independent finish certificate with the same original edge's actual fraction-one query. -/
def lastQueryEquivalent (prepared : PreparedParent patch count floor covered targets) :
    NamedEquivalent (parent.edge.rootName 1 (by decide +kernel))
      prepared.lastSample.certificate.value.name :=
  patch.point_equivalent_at count 1 (by decide +kernel) parent.edge.point_one
    (finish_inside patch count covered) prepared.lastSample

/-- Canonical source stages retain the entire same original first-endpoint operational comparison.

The original Point factory is independent of Targets and source floor.
Its exact readback identifies the complete comparison value, including its
operational witnesses; agreement of endpoint names alone is not used.
-/
theorem firstQueryEquivalent_prepareParent_heq
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    (patch : PreparedPatch parent) (count firstFloor lastFloor : Nat)
    (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
    {firstIndex lastIndex : Nat} (firstTargets : CellEndpoints.Targets firstPath firstIndex)
    (lastTargets : CellEndpoints.Targets lastPath lastIndex) :
    HEq (prepareParent (frame := frame) (basis := basis) patch count firstFloor
        covered firstTargets).firstQueryEquivalent
      (prepareParent (frame := frame) (basis := basis) patch count lastFloor
        covered lastTargets).firstQueryEquivalent := by
  have same :
      (prepareParent (frame := frame) (basis := basis) patch count firstFloor covered firstTargets).firstSample =
      (prepareParent (frame := frame) (basis := basis) patch count lastFloor covered lastTargets).firstSample :=
    (prepareParent_firstSample (frame := frame) (basis := basis) patch count firstFloor covered firstTargets).trans
      (prepareParent_firstSample (frame := frame) (basis := basis) patch count lastFloor covered lastTargets).symm
  have comparison_heq
      (first last : ContinuedNeighborhood.Point (patch.neighborhood count) (startPoint parent).coordinate)
      (equal : first = last) :
      HEq (patch.point_equivalent_at count 0 (by decide +kernel) parent.edge.point_zero
          (start_inside patch count) first)
        (patch.point_equivalent_at count 0 (by decide +kernel) parent.edge.point_zero
          (start_inside patch count) last) := by
    cases equal
    rfl
  unfold firstQueryEquivalent
  exact comparison_heq _ _ same

/-- Canonical source stages retain the entire same original last-endpoint operational comparison.

The original Point factory is independent of Targets and source floor.
Its exact readback identifies the complete comparison value, including its
operational witnesses; agreement of endpoint names alone is not used.
-/
theorem lastQueryEquivalent_prepareParent_heq
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    (patch : PreparedPatch parent) (count firstFloor lastFloor : Nat)
    (covered : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
    {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
    {firstIndex lastIndex : Nat} (firstTargets : CellEndpoints.Targets firstPath firstIndex)
    (lastTargets : CellEndpoints.Targets lastPath lastIndex) :
    HEq (prepareParent (frame := frame) (basis := basis) patch count firstFloor
        covered firstTargets).lastQueryEquivalent
      (prepareParent (frame := frame) (basis := basis) patch count lastFloor
        covered lastTargets).lastQueryEquivalent := by
  have same :
      (prepareParent (frame := frame) (basis := basis) patch count firstFloor covered firstTargets).lastSample =
      (prepareParent (frame := frame) (basis := basis) patch count lastFloor covered lastTargets).lastSample :=
    (prepareParent_lastSample (frame := frame) (basis := basis) patch count firstFloor covered firstTargets).trans
      (prepareParent_lastSample (frame := frame) (basis := basis) patch count lastFloor covered lastTargets).symm
  have comparison_heq
      (first last : ContinuedNeighborhood.Point (patch.neighborhood count) (finishPoint parent).coordinate)
      (equal : first = last) :
      HEq (patch.point_equivalent_at count 1 (by decide +kernel) parent.edge.point_one
          (finish_inside patch count covered) first)
        (patch.point_equivalent_at count 1 (by decide +kernel) parent.edge.point_one
          (finish_inside patch count covered) last) := by
    cases equal
    rfl
  unfold lastQueryEquivalent
  exact comparison_heq _ _ same

/-- Derive a retained original-cell admission from genuine prepared-query comparisons to both selected bank owners.

The original covering patch derives both query-to-source comparisons.
Common-owner acquisition and numerical comparisons are performed once. The
source cost, target and local endpoints come from the already paid parent
cache; no endpoint estimate or primitive bound is a constructor input.
-/
def admit (prepared : PreparedParent patch count floor covered targets)
    {bank : Vertex.Bank parameter targets.endpoint}
    (first : Vertex.Bank.Found bank (startPoint parent))
    (last : Vertex.Bank.Found bank (finishPoint parent))
    (firstQuery : NamedEquivalent (parent.edge.rootName 0 (by decide +kernel))
      first.original.sample.certificate.value.name)
    (lastQuery : NamedEquivalent (parent.edge.rootName 1 (by decide +kernel))
      last.original.sample.certificate.value.name) :
    Admitted prepared first last (prepared.firstQueryEquivalent.symm.trans firstQuery)
      (prepared.lastQueryEquivalent.symm.trans lastQuery) :=
  let firstEquivalent := prepared.firstQueryEquivalent.symm.trans firstQuery
  let lastEquivalent := prepared.lastQueryEquivalent.symm.trans lastQuery
  let firstRefinement := RootBranch.acquire prepared.firstSample first.original.sample firstEquivalent
  let lastRefinement := RootBranch.acquire prepared.lastSample last.original.sample lastEquivalent
  let admission := prepared.admitBranches first last firstRefinement.2.val lastRefinement.2.val
  ⟨firstRefinement, lastRefinement, ⟨admission, rfl⟩⟩

/-- Distinctness of the actual bank identifies its selected source vertex with the original retained source cache.

The requested entry occurs only in erased membership and equality proofs.
The returned equality concerns the actual selected original name; no bank
request, vertex producer or root continuation is executed by this law.
-/
theorem firstName_eq (prepared : PreparedParent patch count floor covered targets)
    {bank : Vertex.Bank parameter targets.endpoint} (distinct : Vertex.Bank.Distinct bank)
    {point : LiftedPoint 2} (found : Vertex.Bank.Found bank point)
    (point_eq : startPoint parent = point)
    (member : Vertex.Entry.request prepared.firstVertex.val targets.endpoint targets.endpoint_positive ∈ bank) :
    found.original.sample.certificate.value.name = prepared.firstSample.certificate.value.name := by
  cases point_eq
  have original := found.original_eq_entry distinct
    (Vertex.Entry.request prepared.firstVertex.val targets.endpoint targets.endpoint_positive) member rfl
  change found.original = prepared.firstVertex.val at original
  have names := congrArg (fun vertex : Vertex parameter (startPoint parent) =>
    vertex.sample.certificate.value.name) original
  rewrite [prepared.firstVertex.property, Vertex.ofPoint_sample] at names
  exact names

/-- Derive the original prepared source-query comparison to the actual selected source-bank owner.

Only exact source-vertex identity from distinctness is used after the
original patch's own point comparison. This does not identify two roots
merely from their coordinates or retained sheet labels.
-/
def firstQueryToFound (prepared : PreparedParent patch count floor covered targets)
    {bank : Vertex.Bank parameter targets.endpoint} (distinct : Vertex.Bank.Distinct bank)
    {point : LiftedPoint 2} (found : Vertex.Bank.Found bank point)
    (point_eq : startPoint parent = point)
    (member : Vertex.Entry.request prepared.firstVertex.val targets.endpoint targets.endpoint_positive ∈ bank) :
    NamedEquivalent (parent.edge.rootName 0 (by decide +kernel))
      found.original.sample.certificate.value.name :=
  prepared.firstQueryEquivalent.trans
    (NamedEquivalent.transport rfl (prepared.firstName_eq distinct found point_eq member).symm
      (NamedEquivalent.refl prepared.firstSample.certificate.value.name))

section SameEdge

open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)

variable {firstParent lastParent : CenteredEdge (Fibre.frameCurve frame) basis}
variable {firstPatch : PreparedPatch firstParent} {lastPatch : PreparedPatch lastParent}
variable {firstCount lastCount firstFloor lastFloor : Nat}
variable {firstCovered : (firstPatch.neighborhood firstCount).box.Contains (firstParent.edge.point 1)}
variable {lastCovered : (lastPatch.neighborhood lastCount).box.Contains (lastParent.edge.point 1)}
variable {firstStart firstFinish lastStart lastFinish : LiftedPoint 2}
variable {firstPath : LiftedPath 2 firstStart firstFinish} {lastPath : LiftedPath 2 lastStart lastFinish}
variable {firstStage lastStage : Nat}
variable {firstTargets : CellEndpoints.Targets firstPath firstStage}
variable {lastTargets : CellEndpoints.Targets lastPath lastStage}

/-- Compare independently prepared OLD source samples at the identical original signed prepared edge.

Each original patch supplies its own actual source-query comparison. The
literal edge equality identifies ONLY their common query name; it does not
identify either independently acquired preparation, endpoint Point, old
observation, request or allocation. No source or observation factory is replayed.
-/
def firstEquivalentOfEdgeEq
    (first : PreparedParent firstPatch firstCount firstFloor firstCovered firstTargets)
    (last : PreparedParent lastPatch lastCount lastFloor lastCovered lastTargets)
    (same : firstParent.edge = lastParent.edge) :
    NamedEquivalent first.firstSample.certificate.value.name last.firstSample.certificate.value.name := by
  have queryNames := congrArg (fun edge : PreparedEdge (Fibre.frameCurve frame) basis =>
    edge.rootName 0 edge.baseInside) same
  exact first.firstQueryEquivalent.symm.trans
    (NamedEquivalent.transport queryNames.symm rfl last.firstQueryEquivalent)

end SameEdge

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
