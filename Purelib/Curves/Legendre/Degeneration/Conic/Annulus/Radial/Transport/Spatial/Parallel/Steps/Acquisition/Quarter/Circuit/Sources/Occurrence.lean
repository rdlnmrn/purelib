module

import Purelib.Curves.Legendre.Periods.Fibre

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Assembly
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization.Sources.Occurrence
import Purelib.Data.Fin
import Purelib.Data.List.Flatten.Occurrence

/-! # Exact retained Block descent below the same global quarter occurrence

One literal quarter occurrence determines its original Block flattening.
The original locator runs once on that exact local index; every subsequent
getter consumes the stored location and reads the SAME whole original
cover/preparation pair. The actual quarter prepared-parent incidence is
retained heterogeneously without rebuilding a source or query.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Steps.Acquisition.Quarter.Input
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Observation

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes

section ActualInputs

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter} {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable {initial : Input.Realization firstInput sourceOwner agreement}
variable {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}
variable {execution : Execution.Cache initial secondInput thirdInput fourthInput}

variable {frame : Paths.Frame parameter} {basis : Differential 1}
variable {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Execution.Cache.Sources

variable (sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution)

/-- Read the SAME actual old-or-fine quarter's original ordered Block words. -/
@[expose] def blockWords : Fin 4 → List (List (CenteredEdge (Fibre.frameCurve frame) basis)) :=
  Data.Fin.cases (Realization.Sources.parentWords execution.first sources.1)
    (Data.Fin.cases (Realization.Sources.parentWords execution.second.paid sources.2.1)
      (Data.Fin.cases (Realization.Sources.parentWords execution.third.paid sources.2.2.1)
        (fun _ : Fin 1 => Realization.Sources.parentWords execution.fourth.paid sources.2.2.2)))

/-- Actual Block flattening is precisely the retained parent list of that SAME selected quarter. -/
theorem blockWords_flatten (quarter : Fin 4) :
    (blockWords sources quarter).flatten = (quarterSource sources quarter).2.geometry.parents := by
  refine Data.Fin.cases_induction ?_ (fun second => ?_) quarter
  · exact (Realization.Sources.assemble_parents execution.first sources.1).symm
  · refine Data.Fin.cases_induction ?_ (fun third => ?_) second
    · exact (Realization.Sources.assemble_parents execution.second.paid sources.2.1).symm
    · refine Data.Fin.cases_induction ?_ (fun _fourth => ?_) third
      · exact (Realization.Sources.assemble_parents execution.third.paid sources.2.2.1).symm
      · exact (Realization.Sources.assemble_parents execution.fourth.paid sources.2.2.2).symm

/-- Change only the local bound to the identical actual quarter Block flattening. -/
@[expose] def blockFlattenedIndex (quarter : Fin 4)
    (index : Fin (quarterSource sources quarter).2.geometry.parents.length) :
    Fin (blockWords sources quarter).flatten.length :=
  ⟨index.val, Eq.mpr (congrArg (fun parents => index.val < parents.length) (blockWords_flatten sources quarter))
    index.isLt⟩

/-- Execute the original finite locator once on the SAME actual selected quarter child. -/
def locateBlock (quarter : Fin 4) (index : Fin (quarterSource sources quarter).2.geometry.parents.length) :
    Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index) :=
  Flatten.locate (blockWords sources quarter) (blockFlattenedIndex sources quarter index)

/-- The retained actual Block position is exactly the whole original locator result on the SAME input. -/
theorem locateBlock_eq (quarter : Fin 4) (index : Fin (quarterSource sources quarter).2.geometry.parents.length) :
    locateBlock sources quarter index =
      Flatten.locate (blockWords sources quarter) (blockFlattenedIndex sources quarter index) := by
  unfold locateBlock
  rfl

/-- The actual selected quarter retains its original complete old-or-fine Block/source cache family. -/
@[expose] def BlockEntry : (quarter : Fin 4) → Fin (blockWords sources quarter).length → Type 1 :=
  Data.Fin.casesDependent
    (motive := fun q : Fin 4 => Fin (blockWords sources q).length → Type 1)
    (fun outer => Realization.Sources.BlockEntry execution.first sources.1 outer)
    (fun second => Data.Fin.casesDependent
      (motive := fun q : Fin 3 => Fin (blockWords sources q.succ).length → Type 1)
      (fun outer => Realization.Sources.BlockEntry execution.second.paid sources.2.1 outer)
      (fun third => Data.Fin.casesDependent
        (motive := fun q : Fin 2 => Fin (blockWords sources q.succ.succ).length → Type 1)
        (fun outer => Realization.Sources.BlockEntry execution.third.paid sources.2.2.1 outer)
        (fun _ : Fin 1 => fun outer =>
          Realization.Sources.BlockEntry execution.fourth.paid sources.2.2.2 outer) third) second)

/-- Read the SAME retained whole Block/source input without reconstructing a query, geometry or paid acquisition. -/
@[expose] def blockEntry : (quarter : Fin 4) → (outer : Fin (blockWords sources quarter).length) →
    BlockEntry sources quarter outer :=
  Data.Fin.casesDependent
    (motive := fun q : Fin 4 => (outer : Fin (blockWords sources q).length) → BlockEntry sources q outer)
    (fun outer => Realization.Sources.blockEntry execution.first sources.1 outer)
    (fun second => Data.Fin.casesDependent
      (motive := fun q : Fin 3 => (outer : Fin (blockWords sources q.succ).length) → BlockEntry sources q.succ outer)
      (fun outer => Realization.Sources.blockEntry execution.second.paid sources.2.1 outer)
      (fun third => Data.Fin.casesDependent
        (motive := fun q : Fin 2 => (outer : Fin (blockWords sources q.succ.succ).length) →
          BlockEntry sources q.succ.succ outer)
        (fun outer => Realization.Sources.blockEntry execution.third.paid sources.2.2.1 outer)
        (fun _ : Fin 1 => fun outer =>
          Realization.Sources.blockEntry execution.fourth.paid sources.2.2.2 outer) third) second)

/-- Read an actual supplied Block's SAME complete covering/preparation pair and original source cache equations. -/
@[expose] def entrySources : (quarter : Fin 4) → (outer : Fin (blockWords sources quarter).length) →
    BlockEntry sources quarter outer →
    Blocks.Sources.SourcePair (frame := frame) (basis := basis)
      (count := modelCount) (floor := floor) (sourceTargets := sourceTargets)
      ((blockWords sources quarter)[outer.val]'outer.isLt) :=
  Data.Fin.casesDependent
    (motive := fun q : Fin 4 => (outer : Fin (blockWords sources q).length) → BlockEntry sources q outer →
          Blocks.Sources.SourcePair (frame := frame) (basis := basis)
            (count := modelCount) (floor := floor) (sourceTargets := sourceTargets)
            ((blockWords sources q)[outer.val]'outer.isLt))
    (fun outer picked => Realization.Sources.blockSources execution.first sources.1 outer picked)
    (fun second => Data.Fin.casesDependent
      (motive := fun q : Fin 3 => (outer : Fin (blockWords sources q.succ).length) → BlockEntry sources q.succ outer →
          Blocks.Sources.SourcePair (frame := frame) (basis := basis)
            (count := modelCount) (floor := floor) (sourceTargets := sourceTargets)
            ((blockWords sources q.succ)[outer.val]'outer.isLt))
      (fun outer picked => Realization.Sources.blockSources execution.second.paid sources.2.1 outer picked)
      (fun third => Data.Fin.casesDependent
        (motive := fun q : Fin 2 => (outer : Fin (blockWords sources q.succ.succ).length) →
        BlockEntry sources q.succ.succ outer →
          Blocks.Sources.SourcePair (frame := frame) (basis := basis)
            (count := modelCount) (floor := floor) (sourceTargets := sourceTargets)
            ((blockWords sources q.succ.succ)[outer.val]'outer.isLt))
        (fun outer picked => Realization.Sources.blockSources execution.third.paid sources.2.2.1 outer picked)
        (fun _ : Fin 1 => fun outer picked =>
          Realization.Sources.blockSources execution.fourth.paid sources.2.2.2 outer picked) third) second)

/-- Read the SAME complete selected Block source pair at the supplied literal quarter/child occurrence.

Only actual existing source families and the retained position are read.
The second L-edge's previous Reading/Samples remain in the selected Block;
no older origin is retagged and no source acquisition or observer is replayed.
-/
@[expose] def blockSources (quarter : Fin 4)
    (index : Fin (quarterSource sources quarter).2.geometry.parents.length)
    (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index)) :
    Blocks.Sources.SourcePair (frame := frame) (basis := basis)
      (count := modelCount) (floor := floor) (sourceTargets := sourceTargets)
      ((blockWords sources quarter)[position.1.val]'position.1.isLt) :=
  entrySources sources quarter position.1 (blockEntry sources quarter position.1)

/-- The actual selected Block child is the identical quarter parent with its complete original query/Step data. -/
theorem blockParent_eq (quarter : Fin 4) (index : Fin (quarterSource sources quarter).2.geometry.parents.length)
    (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index)) :
    (quarterSource sources quarter).2.geometry.parents[index.val]'index.isLt =
      ((blockWords sources quarter)[position.1.val]'position.1.isLt)[position.2.val.val]'position.2.val.isLt :=
  (getElem_congr (i := index.val) (j := index.val)
    (blockWords_flatten sources quarter).symm rfl index.isLt).trans position.2.property.1

/-- The literal quarter PreparedParent is the WHOLE same original selected Block cache in all old/fine branches. -/
theorem blockPrepared_heq (quarter : Fin 4) (index : Fin (quarterSource sources quarter).2.geometry.parents.length)
    (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index)) :
    HEq ((quarterSource sources quarter).2.prepared.entry index)
      ((blockSources sources quarter index position).2.entry position.2.val) := by
  revert index position
  refine Data.Fin.cases_induction ?_ (fun second => ?_) quarter
  · intro index position
    exact Realization.Sources.prepared_heq execution.first sources.1 index position
  · refine Data.Fin.cases_induction ?_ (fun third => ?_) second
    · intro index position
      exact Realization.Sources.prepared_heq execution.second.paid sources.2.1 index position
    · refine Data.Fin.cases_induction ?_ (fun _fourth => ?_) third
      · intro index position
        exact Realization.Sources.prepared_heq execution.third.paid sources.2.2.1 index position
      · intro index position
        exact Realization.Sources.prepared_heq execution.fourth.paid sources.2.2.2 index position

end Execution.Cache.Sources

end ActualInputs

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter}
variable {firstReading : ReadingAt circuit.first.actual UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginalOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginal : Steps.Quarter circuit.first.actual circuit.first.regular
  UniformPrimitiveMesh.firstEndpoint firstReading firstOriginalOwner}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {agreement : InitialAgreement UniformPrimitiveMesh.firstEndpoint firstReading sourceOwner}
variable {initial : Quarter firstOriginal sourceOwner agreement}
variable {secondReading : ReadingAt circuit.second.actual UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginalOwner : OwnerAt site parameter .second (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginal : Steps.Quarter circuit.second.actual circuit.second.regular
  UniformPrimitiveMesh.firstEndpoint secondReading secondOriginalOwner}
variable {thirdReading : ReadingAt circuit.third.actual UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginalOwner : OwnerAt site parameter .third (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginal : Steps.Quarter circuit.third.actual circuit.third.regular
  UniformPrimitiveMesh.firstEndpoint thirdReading thirdOriginalOwner}
variable {fourthReading : ReadingAt circuit.fourth.actual UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginalOwner : OwnerAt site parameter .fourth (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginal : Steps.Quarter circuit.fourth.actual circuit.fourth.regular
  UniformPrimitiveMesh.firstEndpoint fourthReading fourthOriginalOwner}
variable {execution : Execution initial secondOriginal thirdOriginal fourthOriginal}

variable {frame : Paths.Frame parameter} {basis : Differential 1}
variable {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Execution.Sources

variable (sources : Execution.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution)

/-- The original old-input Block words are the SAME shared actual source-family words. -/
@[expose] def blockWords : Fin 4 → List (List (CenteredEdge (Fibre.frameCurve frame) basis)) :=
  Cache.Sources.blockWords (execution := execution) sources

/-- The original old-input facade preserves the SAME literal quarter parent flattening. -/
theorem blockWords_flatten (quarter : Fin 4) :
    (blockWords sources quarter).flatten = (quarterSource sources quarter).2.geometry.parents :=
  Cache.Sources.blockWords_flatten (execution := execution) sources quarter

/-- The old-input occurrence transport preserves its literal natural coordinate in the SAME Block words. -/
@[expose] def blockFlattenedIndex (quarter : Fin 4)
    (index : Fin (quarterSource sources quarter).2.geometry.parents.length) :
    Fin (blockWords sources quarter).flatten.length :=
  Cache.Sources.blockFlattenedIndex (execution := execution) sources quarter index

/-- Read the original old-input Block position through the SAME shared finite lookup worker. -/
def locateBlock (quarter : Fin 4) (index : Fin (quarterSource sources quarter).2.geometry.parents.length) :
    Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index) :=
  Cache.Sources.locateBlock (execution := execution) sources quarter index

/-- The original old-input position remains the whole original locator result on the unchanged occurrence. -/
theorem locateBlock_eq (quarter : Fin 4) (index : Fin (quarterSource sources quarter).2.geometry.parents.length) :
    locateBlock sources quarter index =
      Flatten.locate (blockWords sources quarter) (blockFlattenedIndex sources quarter index) :=
  Cache.Sources.locateBlock_eq (execution := execution) sources quarter index

/-- Read the SAME old-input selected source pair through the single shared actual Block dispatch. -/
@[expose] def blockSources (quarter : Fin 4)
    (index : Fin (quarterSource sources quarter).2.geometry.parents.length)
    (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index)) :
    Blocks.Sources.SourcePair (frame := frame) (basis := basis)
      (count := modelCount) (floor := floor) (sourceTargets := sourceTargets)
      ((blockWords sources quarter)[position.1.val]'position.1.isLt) :=
  Cache.Sources.blockSources (execution := execution) sources quarter index position

/-- Read the complete original Steps source pair by its actual oriented quarter and retained child occurrence.

This comparison view retains the original four getter expressions and their
whole cover/preparation products. It reads the same supplied source families;
it does not execute a source acquisition or observation.
-/
@[expose] def stepsBlockSources (quarter : Fin 4)
    (index : Fin (quarterSource sources quarter).2.geometry.parents.length)
    (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index)) :
    Blocks.Sources.SourcePair (frame := frame) (basis := basis)
      (count := modelCount) (floor := floor) (sourceTargets := sourceTargets)
      ((blockWords sources quarter)[position.1.val]'position.1.isLt) :=
  (Data.Fin.casesDependent
    (motive := fun quarter =>
      (index : Fin (quarterSource sources quarter).2.geometry.parents.length) →
      (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index)) →
      Blocks.Sources.SourcePair (frame := frame) (basis := basis)
        (count := modelCount) (floor := floor) (sourceTargets := sourceTargets)
        ((blockWords sources quarter)[position.1.val]'position.1.isLt))
    (fun index position => Quarter.Sources.selectedSources execution.first sources.1
          (Realization.Sources.ofStepsIndex rfl execution.first sources.1 index) position)
    (fun second => Data.Fin.casesDependent
        (motive := fun q : Fin 3 =>
          (index : Fin (quarterSource sources q.succ).2.geometry.parents.length) →
          (position : Flatten.Occurrence (blockWords sources q.succ)
            (blockFlattenedIndex sources q.succ index)) →
          Blocks.Sources.SourcePair (frame := frame) (basis := basis)
            (count := modelCount) (floor := floor) (sourceTargets := sourceTargets)
            ((blockWords sources q.succ)[position.1.val]'position.1.isLt))
      (fun index position => Quarter.Sources.selectedSources execution.second.paid sources.2.1
          (Realization.Sources.ofStepsIndex rfl execution.second.paid sources.2.1 index) position)
      (fun third => Data.Fin.casesDependent
        (motive := fun q : Fin 2 =>
          (index : Fin (quarterSource sources q.succ.succ).2.geometry.parents.length) →
          (position : Flatten.Occurrence (blockWords sources q.succ.succ)
            (blockFlattenedIndex sources q.succ.succ index)) →
          Blocks.Sources.SourcePair (frame := frame) (basis := basis)
            (count := modelCount) (floor := floor) (sourceTargets := sourceTargets)
            ((blockWords sources q.succ.succ)[position.1.val]'position.1.isLt))
        (fun index position => Quarter.Sources.selectedSources execution.third.paid sources.2.2.1
          (Realization.Sources.ofStepsIndex rfl execution.third.paid sources.2.2.1 index) position)
        (fun _fourth : Fin 1 => fun index position =>
          Quarter.Sources.selectedSources execution.fourth.paid sources.2.2.2
            (Realization.Sources.ofStepsIndex rfl execution.fourth.paid sources.2.2.2 index) position)
          third) second)) quarter index position

/-- Shared Block descent preserves the complete original Steps source pair at every actual retained occurrence. -/
theorem blockSources_eq_original (quarter : Fin 4)
    (index : Fin (quarterSource sources quarter).2.geometry.parents.length)
    (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index)) :
    blockSources sources quarter index position = stepsBlockSources sources quarter index position := by
  revert index position
  refine Data.Fin.cases_induction ?_ (fun second => ?_) quarter
  · intro index position
    exact Realization.Sources.selectedSources_ofSteps rfl execution.first sources.1 index position
  · refine Data.Fin.cases_induction ?_ (fun third => ?_) second
    · intro index position
      exact Realization.Sources.selectedSources_ofSteps rfl execution.second.paid sources.2.1 index position
    · refine Data.Fin.cases_induction ?_ (fun _fourth => ?_) third
      · intro index position
        exact Realization.Sources.selectedSources_ofSteps rfl execution.third.paid sources.2.2.1 index position
      · intro index position
        exact Realization.Sources.selectedSources_ofSteps rfl execution.fourth.paid sources.2.2.2 index position

/-- The original old-input parent remains exactly its actual selected Block child, including query data. -/
theorem blockParent_eq (quarter : Fin 4) (index : Fin (quarterSource sources quarter).2.geometry.parents.length)
    (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index)) :
    (quarterSource sources quarter).2.geometry.parents[index.val]'index.isLt =
      ((blockWords sources quarter)[position.1.val]'position.1.isLt)[position.2.val.val]'position.2.val.isLt :=
  Cache.Sources.blockParent_eq (execution := execution) sources quarter index position

/-- The old-input facade retains the WHOLE exact original selected Block PreparedParent through shared incidence. -/
theorem blockPrepared_heq (quarter : Fin 4) (index : Fin (quarterSource sources quarter).2.geometry.parents.length)
    (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index)) :
    HEq ((quarterSource sources quarter).2.prepared.entry index)
      ((blockSources sources quarter index position).2.entry position.2.val) :=
  Cache.Sources.blockPrepared_heq (execution := execution) sources quarter index position

end Execution.Sources

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
