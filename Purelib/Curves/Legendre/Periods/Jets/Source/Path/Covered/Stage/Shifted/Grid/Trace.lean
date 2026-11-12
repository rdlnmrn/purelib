module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Initial
import Purelib.Data.Rat.Fraction
import Purelib.Data.Fin
import Purelib.Data.Vector.Basic

/-! # Complete finite parameter samples on the retained source and positive-node table

The sample vector starts with the literal incoming completed source and
continues with the same stored node programmes. One integral aggregation of
the already-stored first ValueBlocks supplies the initial edge. The other
edges read the original positive-positive certificates. All edge certificates
are only reindexed to the equal original uniform Gaussian increment.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

namespace PositiveGridNode

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Vector (DependentVector)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry
  (ValueBlocks BetweenRows Position)
open Purelib.Calculus.Jet

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat}
    (intervals : Nat) (positive : 0 < intervals) (direction : Canonical) (moving : direction ≠ 0)
    (spatial : AccuracyRequest)
    (source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving))))
    (member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt })
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (targetCurrent targetFloor targetRootStage : Nat)

variable {intervals positive direction moving spatial source member ranges allocation admitted widths roots
    targetCurrent targetFloor targetRootStage}
    (table : Table intervals positive direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)

namespace Table

/-- The literal six-channel samples in original order, with the retained completed source at node zero. -/
@[expose] def sampleAt (index : Fin (intervals + 1)) (channel : Fin 6) : Canonical :=
  Data.Fin.cases (sourceSample source member channel) (fun node => table.positiveSample node channel) index

/-- Node zero is the literal same completed source sample, without a zero-offset acquisition. -/
theorem sampleAt_zero (channel : Fin 6) : table.sampleAt 0 channel = sourceSample source member channel :=
  Data.Fin.cases_zero _ _

/-- Each successor is the same stored positive node's original selected programme sample. -/
theorem sampleAt_succ (index : Fin intervals) (channel : Fin 6) :
    table.sampleAt index.succ channel = table.positiveSample index channel :=
  Data.Fin.cases_succ _ _ index

section Certificates

variable (initial : table.FirstIntegral)

/-- Select an original initial or positive-positive certificate, retaining its data at the equal uniform increment.

Only the first branch reads the first-node integral aggregate. Every later
branch reads the table's same stored adjacent certificate. The finite index
bounds derive the original neighbouring positions; no additional edge,
node, preparation, query or programme factory executes.
-/
@[expose] def certificateAt (index : Fin intervals) (order coordinate : Fin 2) :
    Quadratic.Basic.Certificate (Sampling.gridIncrement intervals direction) :=
  if zero : index.val = 0 then
    table.firstCertificate initial order coordinate
  else
    (table.certificate (Sampling.gridInnerEdge intervals index zero) order coordinate).castIncrement
      (Sampling.gridPositiveOffset_difference intervals
        (Sampling.gridPairIndex intervals (Sampling.gridInnerEdge intervals index zero))
        (Sampling.gridPairFollowing intervals (Sampling.gridInnerEdge intervals index zero)) direction)

/-- The selected original certificate base is the preceding literal grid sample. -/
private theorem certificateAt_base (index : Fin intervals) (order coordinate : Fin 2) :
    (table.certificateAt initial index order coordinate).base =
      table.sampleAt index.castSucc (Specification.Table.baseIndex order coordinate) := by
  unfold certificateAt
  split
  · rename_i zero
    exact ((initial.certificate order coordinate).castIncrement_base
      (Sampling.gridOffset_first intervals positive direction)).trans
        ((table.first_base initial order coordinate).trans
          ((table.sampleAt_zero (Specification.Table.baseIndex order coordinate)).symm.trans
            (congrArg (fun position => table.sampleAt position
              (Specification.Table.baseIndex order coordinate))
                (Sampling.gridIndex_zero intervals index zero).symm)))
  · rename_i nonzero
    let inner := Sampling.gridInnerEdge intervals index nonzero
    exact ((table.certificate inner order coordinate).castIncrement_base
      (Sampling.gridPositiveOffset_difference intervals (Sampling.gridPairIndex intervals inner)
        (Sampling.gridPairFollowing intervals inner) direction)).trans
      ((table.base inner order coordinate).trans
        ((table.sampleAt_succ (Sampling.gridPairIndex intervals inner)
          (Specification.Table.baseIndex order coordinate)).symm.trans
          (congrArg (fun position => table.sampleAt position
            (Specification.Table.baseIndex order coordinate))
              (Sampling.gridInnerEdge_first intervals index nonzero))))

/-- The selected original certificate slope is the preceding literal derivative-channel sample. -/
private theorem certificateAt_slope (index : Fin intervals) (order coordinate : Fin 2) :
    (table.certificateAt initial index order coordinate).slope =
      table.sampleAt index.castSucc (Specification.Table.slopeIndex order coordinate) := by
  unfold certificateAt
  split
  · rename_i zero
    exact ((initial.certificate order coordinate).castIncrement_slope
      (Sampling.gridOffset_first intervals positive direction)).trans
        ((table.first_slope initial order coordinate).trans
          ((table.sampleAt_zero (Specification.Table.slopeIndex order coordinate)).symm.trans
            (congrArg (fun position => table.sampleAt position
              (Specification.Table.slopeIndex order coordinate))
                (Sampling.gridIndex_zero intervals index zero).symm)))
  · rename_i nonzero
    let inner := Sampling.gridInnerEdge intervals index nonzero
    exact ((table.certificate inner order coordinate).castIncrement_slope
      (Sampling.gridPositiveOffset_difference intervals (Sampling.gridPairIndex intervals inner)
        (Sampling.gridPairFollowing intervals inner) direction)).trans
      ((table.slope inner order coordinate).trans
        ((table.sampleAt_succ (Sampling.gridPairIndex intervals inner)
          (Specification.Table.slopeIndex order coordinate)).symm.trans
          (congrArg (fun position => table.sampleAt position
            (Specification.Table.slopeIndex order coordinate))
              (Sampling.gridInnerEdge_first intervals index nonzero))))

/-- The selected original certificate output is the literal following grid sample. -/
private theorem certificateAt_output (index : Fin intervals) (order coordinate : Fin 2) :
    (table.certificateAt initial index order coordinate).output =
      table.sampleAt index.succ (Specification.Table.baseIndex order coordinate) := by
  unfold certificateAt
  split
  · rename_i zero
    exact ((initial.certificate order coordinate).castIncrement_output
      (Sampling.gridOffset_first intervals positive direction)).trans
        ((table.first_output initial order coordinate).trans
          ((congrArg (fun node => table.positiveSample node
            (Specification.Table.baseIndex order coordinate))
              (Sampling.gridIndex_first intervals positive index zero).symm).trans
                (table.sampleAt_succ index (Specification.Table.baseIndex order coordinate)).symm))
  · rename_i nonzero
    let inner := Sampling.gridInnerEdge intervals index nonzero
    exact ((table.certificate inner order coordinate).castIncrement_output
      (Sampling.gridPositiveOffset_difference intervals (Sampling.gridPairIndex intervals inner)
        (Sampling.gridPairFollowing intervals inner) direction)).trans
      ((table.output inner order coordinate).trans
        ((congrArg (fun node => table.positiveSample node
          (Specification.Table.baseIndex order coordinate))
            (Sampling.gridInnerEdge_last intervals index nonzero)).trans
              (table.sampleAt_succ index (Specification.Table.baseIndex order coordinate)).symm))

/-- The original fixed-parent factor is unchanged on the initial edge and every retained interior edge. -/
private theorem certificateAt_factor (index : Fin intervals) (order coordinate : Fin 2) :
    (table.certificateAt initial index order coordinate).factor =
      ValueBlocks.factor (covered := covered) order coordinate := by
  unfold certificateAt
  split
  · exact ((initial.certificate order coordinate).castIncrement_factor
      (Sampling.gridOffset_first intervals positive direction)).trans (initial.factor_eq order coordinate)
  · rename_i nonzero
    let inner := Sampling.gridInnerEdge intervals index nonzero
    exact ((table.certificate inner order coordinate).castIncrement_factor
      (Sampling.gridPositiveOffset_difference intervals (Sampling.gridPairIndex intervals inner)
        (Sampling.gridPairFollowing intervals inner) direction)).trans
      ((table.edge inner).actual.factor_eq order coordinate)

end Certificates

/-- The complete literal sample vector, first integral aggregate and ordered original row-certificate vector.

Existing Sigma/Subtype containers retain all three whole factory equations.
The first aggregate consumes the table's existing programme entry at zero;
no ValueBlocks, positive node or programme is built a second time. For one
interval the only certificate is the initial one and Fin 0 is never read.
-/
@[expose] def Trace :=
  (_samples : { value : Data.Vector (Data.Vector Canonical 6) (intervals + 1) //
    value = Data.Vector.Basic.vectorOfFn (fun index =>
      Data.Vector.Basic.vectorOfFn (fun channel => table.sampleAt index channel)) }) ×
  (initial : { value : table.FirstIntegral // value = ValueBlocks.Integral.build
    (next := table.firstNode.next) (table.programmes.entry (Sampling.gridFirstIndex intervals positive)) }) ×
  { value : Data.Vector (Data.Vector (Data.Vector
      (Quadratic.Basic.Certificate (Sampling.gridIncrement intervals direction)) 2) 2) intervals //
    value = Data.Vector.Basic.vectorOfFn (fun index => Data.Vector.Basic.vectorOfFn (fun order =>
      Data.Vector.Basic.vectorOfFn (fun coordinate => table.certificateAt initial.val index order coordinate))) }

namespace Trace

/-- Materialize the literal original samples, one first-node integral aggregate and all ordered edge views once. -/
def build : Trace table :=
  let samples : Data.Vector (Data.Vector Canonical 6) (intervals + 1) :=
    Data.Vector.Basic.vectorOfFn (fun index => Data.Vector.Basic.vectorOfFn (fun channel =>
      table.sampleAt index channel))
  let initial : table.FirstIntegral := ValueBlocks.Integral.build (next := table.firstNode.next)
    (table.programmes.entry (Sampling.gridFirstIndex intervals positive))
  let certificates : Data.Vector (Data.Vector (Data.Vector
      (Quadratic.Basic.Certificate (Sampling.gridIncrement intervals direction)) 2) 2) intervals :=
    Data.Vector.Basic.vectorOfFn (fun index => Data.Vector.Basic.vectorOfFn (fun order =>
      Data.Vector.Basic.vectorOfFn (fun coordinate => table.certificateAt initial index order coordinate)))
  ⟨⟨samples, rfl⟩, ⟨initial, rfl⟩, ⟨certificates, rfl⟩⟩

variable {table} (trace : Trace table)

/-- Read the same complete original-order six-channel sample vector. -/
@[expose] def samples : Data.Vector (Data.Vector Canonical 6) (intervals + 1) := trace.1.val

/-- Read the same integral aggregate on the first stored node's original programme blocks. -/
@[expose] def initial : table.FirstIntegral := trace.2.1.val

/-- Read the same ordered vector of four original certificates at the equal uniform increment. -/
@[expose] def certificates : Data.Vector (Data.Vector (Data.Vector
    (Quadratic.Basic.Certificate (Sampling.gridIncrement intervals direction)) 2) 2) intervals := trace.2.2.val

/-- The whole sample cache retains its literal original source/positive-programme factory. -/
theorem samples_eq : trace.samples = Data.Vector.Basic.vectorOfFn (fun index =>
    Data.Vector.Basic.vectorOfFn (fun channel => table.sampleAt index channel)) := trace.1.property

/-- The first integral cache is its original factory on the same existing programme blocks. -/
theorem initial_eq : trace.initial = ValueBlocks.Integral.build (next := table.firstNode.next)
    (table.programmes.entry (Sampling.gridFirstIndex intervals positive)) := trace.2.1.property

/-- The whole certificate vector retains the exact original initial/interior selection factory. -/
theorem certificates_eq : trace.certificates = Data.Vector.Basic.vectorOfFn (fun index =>
    Data.Vector.Basic.vectorOfFn (fun order => Data.Vector.Basic.vectorOfFn (fun coordinate =>
      table.certificateAt trace.initial index order coordinate))) := trace.2.2.property

/-- Read one literal retained six-channel grid sample. -/
@[expose] def sample (index : Fin (intervals + 1)) (channel : Fin 6) : Canonical := trace.samples index channel

/-- Read one same retained edge certificate without executing any numerical or geometric factory. -/
@[expose] def certificate (index : Fin intervals) (order coordinate : Fin 2) :
    Quadratic.Basic.Certificate (Sampling.gridIncrement intervals direction) := trace.certificates index order
      coordinate

/-- Every stored sample reads the corresponding literal original completed-source or selected target reading. -/
theorem sample_eq (index : Fin (intervals + 1)) (channel : Fin 6) :
    trace.sample index channel = table.sampleAt index channel := by
  have whole := congrArg (fun values : Data.Vector (Data.Vector Canonical 6) (intervals + 1) => values index channel)
    trace.samples_eq
  exact whole.trans (by rewrite [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]; rfl)

/-- Every complete stored certificate is exactly its original initial or positive-positive increment view. -/
theorem certificate_eq (index : Fin intervals) (order coordinate : Fin 2) :
    trace.certificate index order coordinate = table.certificateAt trace.initial index order coordinate := by
  have whole := congrArg (fun values : Data.Vector (Data.Vector (Data.Vector
    (Quadratic.Basic.Certificate (Sampling.gridIncrement intervals direction)) 2) 2) intervals =>
      values index order coordinate) trace.certificates_eq
  exact whole.trans (by
    rewrite [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply,
      Data.Vector.Basic.vectorOfFn_apply]
    rfl)

/-- The first stored certificate is the same first-node integral certificate at its exactly equal increment. -/
theorem certificate_initial (order coordinate : Fin 2) :
    trace.certificate (Sampling.gridFirstIndex intervals positive) order coordinate =
      table.firstCertificate trace.initial order coordinate := by
  have selected := trace.certificate_eq (Sampling.gridFirstIndex intervals positive) order coordinate
  exact selected.trans rfl

/-- A later stored certificate is the same original positive-positive edge at its exactly equal increment. -/
theorem certificate_inner (index : Fin intervals) (nonzero : index.val ≠ 0) (order coordinate : Fin 2) :
    trace.certificate index order coordinate =
      (table.certificate (Sampling.gridInnerEdge intervals index nonzero) order coordinate).castIncrement
        (Sampling.gridPositiveOffset_difference intervals
          (Sampling.gridPairIndex intervals (Sampling.gridInnerEdge intervals index nonzero))
          (Sampling.gridPairFollowing intervals (Sampling.gridInnerEdge intervals index nonzero)) direction) := by
  exact (trace.certificate_eq index order coordinate).trans (by
    unfold certificateAt
    rewrite [dif_neg nonzero]
    rfl)

/-- The zero sample is the same actual original completed source Stage sample. -/
theorem sample_zero (channel : Fin 6) : trace.sample 0 channel = sourceSample source member channel :=
  (trace.sample_eq 0 channel).trans (table.sampleAt_zero channel)

/-- Each positive sample is the same original target programme at that node's own selected stage. -/
theorem sample_succ (index : Fin intervals) (channel : Fin 6) :
    trace.sample index.succ channel = table.positiveSample index channel :=
  (trace.sample_eq index.succ channel).trans (table.sampleAt_succ index channel)

/-- Each original edge base is the preceding literal stored sample. -/
theorem base (index : Fin intervals) (order coordinate : Fin 2) :
    (trace.certificate index order coordinate).base =
      trace.sample index.castSucc (Specification.Table.baseIndex order coordinate) :=
  (congrArg (fun certificate => certificate.base) (trace.certificate_eq index order coordinate)).trans
    ((table.certificateAt_base trace.initial index order coordinate).trans
      (trace.sample_eq index.castSucc (Specification.Table.baseIndex order coordinate)).symm)

/-- Each original edge slope is the preceding literal stored derivative-channel sample. -/
theorem slope (index : Fin intervals) (order coordinate : Fin 2) :
    (trace.certificate index order coordinate).slope =
      trace.sample index.castSucc (Specification.Table.slopeIndex order coordinate) :=
  (congrArg (fun certificate => certificate.slope) (trace.certificate_eq index order coordinate)).trans
    ((table.certificateAt_slope trace.initial index order coordinate).trans
      (trace.sample_eq index.castSucc (Specification.Table.slopeIndex order coordinate)).symm)

/-- Each original edge output is the following literal stored sample. -/
theorem output (index : Fin intervals) (order coordinate : Fin 2) :
    (trace.certificate index order coordinate).output =
      trace.sample index.succ (Specification.Table.baseIndex order coordinate) :=
  (congrArg (fun certificate => certificate.output) (trace.certificate_eq index order coordinate)).trans
    ((table.certificateAt_output trace.initial index order coordinate).trans
      (trace.sample_eq index.succ (Specification.Table.baseIndex order coordinate)).symm)

/-- Every edge retains exactly the original fixed-parent factor, including constant physical parents. -/
theorem factor_eq (index : Fin intervals) (order coordinate : Fin 2) :
    (trace.certificate index order coordinate).factor = ValueBlocks.factor (covered := covered) order coordinate :=
  (congrArg (fun certificate => certificate.factor) (trace.certificate_eq index order coordinate)).trans
    (table.certificateAt_factor trace.initial index order coordinate)

/-- All literal stored grid edges satisfy their original four-row quadratic remainder estimate.

The same original certificate supplies the bound. Only its exact scalar
base, output, slope and factor readbacks transport the formula to the actual
sample vector. No final error estimate, target Completion or canonical cycle
attachment is assumed, and no original loose factor is replaced.
-/
theorem remainder_le (index : Fin intervals) (order coordinate : Fin 2) :
    Canonical.normSq
      (trace.sample index.succ (Specification.Table.baseIndex order coordinate) -
        trace.sample index.castSucc (Specification.Table.baseIndex order coordinate) -
        Sampling.gridIncrement intervals direction *
          trace.sample index.castSucc (Specification.Table.slopeIndex order coordinate)) ≤
      ValueBlocks.factor (covered := covered) order coordinate *
        Canonical.normSq (Sampling.gridIncrement intervals direction) ^ 2 := by
  let actual := trace.certificate index order coordinate
  have expansion :=
    (congrArg₂ (fun output base : Canonical => output - base - Sampling.gridIncrement intervals direction *
      trace.sample index.castSucc (Specification.Table.slopeIndex order coordinate))
      (trace.output index order coordinate).symm (trace.base index order coordinate).symm).trans
      ((congrArg (fun slope : Canonical => actual.output - actual.base -
        Sampling.gridIncrement intervals direction * slope)
          (trace.slope index order coordinate).symm).trans actual.expansion)
  exact (congrArg Canonical.normSq expansion).trans_le
    (actual.remainder_le.trans_eq (congrArg (fun factor : Rational =>
      factor * Canonical.normSq (Sampling.gridIncrement intervals direction) ^ 2)
        (trace.factor_eq index order coordinate)))

end Trace

end Table

end PositiveGridNode

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
