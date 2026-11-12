module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Block
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Cells
public import Purelib.Calculus.Jet.Quadratic.Weighted
public import Purelib.Data.List.Flatten.Table
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Indexed
import Purelib.Data.List.OfFn.Basic
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Whole-global finite row integral Taylor assembly on the same retained source owners

Each original parent contributes one stored ValueBlock. Exact original
prefix positions identify its unchanged target cells in the actual global
Request. The original weighted certificate sum gives a factor depending on
fixed ORIGINAL parent geometry, with no adaptive-child-count multiplier.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib.Calculus.Jet.Quadratic.Basic (Certificate)

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent
  (startPoint)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : Riemann.Topology.PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}

/-- The materialized value-integral block cache at each SAME original parent occurrence. -/
@[expose] def ValueBlocks := DependentProduct (parent :: parents)
  (fun index => ValueBlock (next := next) index)

namespace ValueBlocks

/-- Construct and store each original parent's ValueBlock once in the original retained parent order. -/
def build : ValueBlocks (next := next) :=
  DependentProduct.ofFn (parent :: parents) (fun index => ValueBlock.build (next := next) index)

variable (retained : ValueBlocks (next := next))

/-- Read the SAME original parent's stored block cache without executing any child producer. -/
@[expose] def block (index : Fin (parent :: parents).length) :=
  DependentProduct.get (parent :: parents) retained index

/-- The actual global source-cell word at any one of the six original row indices. -/
@[expose] def oldCells (channel : Fin 6) : List CellModel := List.ofFn (fun index : Fin (parent :: parents).length =>
  (source.prepared.entry index).preparation.cell.models.cell channel)

/-- The actual target global source-cell word in its original unaltered Request order. -/
@[expose] def targetCells (order coordinate : Fin 2) : List CellModel := List.ofFn
  (fun index : Fin (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).length =>
    ((next.requested.prepared.entry index).preparation.cell.models.cell
      (Specification.Table.baseIndex order coordinate)))

/-- The original source word view equals the literal row list of the SAME retained covered/source chain. -/
theorem oldCells_eq_sources (channel : Fin 6) : oldCells (source := source) channel =
    (sources covered source.prepared chain).cells channel :=
  (cells_eq_ofFn covered source.prepared chain channel).symm

/-- The target word view equals the literal selected base-channel list of the SAME actual global Request source
chain. -/
theorem targetCells_eq_sources (order coordinate : Fin 2) : (targetCells (next := next) order coordinate) =
    (sources next.requested.request.covered next.requested.prepared next.requested.request.chain).cells
      (Specification.Table.baseIndex order coordinate) :=
  (cells_eq_ofFn next.requested.request.covered next.requested.prepared next.requested.request.chain
      (Specification.Table.baseIndex order coordinate)).symm

/-- The SAME original target global cell word is the exact ordered flattening of the retained block cell views.

Whole geometry and Request-shape identities supply the global length. Each
stored original Position supplies its full prefix offset. The abstract
finite-table law preserves every repeated occurrence without unfolding a
root, source or query factory.
-/
theorem targetCells_eq_blocks (order coordinate : Fin 2) : (targetCells (next := next) order coordinate) =
    (List.ofFn (fun index => ((retained.block index).targetCells order coordinate))).flatten := by
  let words := fun index : Fin (parent :: parents).length => ValueBlock.children (next := next) index
  have joined : (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2) =
      (List.ofFn words).flatten :=
    next.requested.request.shape.property.symm.trans
      ((congrArg (fun result => result.parents) next.geometry_eq).trans
        (build_parents source.prepared ranges allocation admitted widths next.blocks chain roots))
  let values := fun index : Fin (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).length =>
    ((next.requested.prepared.entry index).preparation.cell.models.cell
      (Specification.Table.baseIndex order coordinate))
  let positions := fun outer : Fin (parent :: parents).length =>
    fun inner : Fin (words outer).length => ((retained.block outer).position inner).sourceIndex
  have offset (outer : Fin (parent :: parents).length) (inner : Fin (words outer).length) :
      (positions outer inner).val = ((List.ofFn words).take outer.val).flatten.length + inner.val :=
    ((retained.block outer).position inner).property.2
  exact List.Flatten.ofFn_grouped words (congrArg List.length joined) values positions offset

/-- The actual whole global target sample is the sum of the SAME stored original-parent block samples. -/
theorem targetSample_eq (order coordinate : Fin 2) : (PathModel.mk ((targetCells (next := next) order
    coordinate))).integralSample =
    Algebra.FiniteSum.Fin.sumFin (fun index =>
      (PathModel.mk ((retained.block index).targetCells order coordinate)).integralSample) := by
  rewrite [retained.targetCells_eq_blocks order coordinate]
  exact PathModel.integralSample_flatten_ofFn _

/-- The computed global factor uses only the original parent count and original fixed patch/displacement densities. -/
@[expose] def factor (order coordinate : Fin 2) : Rational :=
  ((parent :: parents).length : Rational) *
    Algebra.FiniteSum.Fin.sumFin (fun index : Fin (parent :: parents).length =>
      ValueBlock.density (covered := covered) index order coordinate)

/-- The computed fixed-geometry global factor is nonnegative, independently of all query/allocation stages. -/
theorem factor_nonnegative (order coordinate : Fin 2) : 0 ≤ factor (covered := covered) order coordinate :=
  Data.Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
    (Data.Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le (parent :: parents).length))
    (Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative _
      (fun index => ValueBlock.density_nonnegative (covered := covered) index order coordinate))

/-- The SAME retained parent certificates, unit weights and their original weighted-sum certificate.

Each parent certificate is assembled once from its stored child integral
caches. The original dependent pairs retain the complete finite vector,
unit weights and weighted-sum factory equations. Every stored certificate
uses those same earlier materialized vectors.
-/
@[expose] def Integral :=
  (entries : { value : Data.Vector (Data.Vector
      (Data.Vector (Certificate increment) (parent :: parents).length) 2) 2 //
    value = Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
      Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
        Data.Vector.Basic.vectorOfFn (fun index => (retained.block index).certificate order coordinate))) }) ×
  (weights : { value : Data.Vector Canonical (parent :: parents).length //
    value = Data.Vector.Basic.vectorOfFn (fun _ : Fin (parent :: parents).length => (1 : Canonical)) }) ×
  { value : Data.Vector (Data.Vector (Certificate increment) 2) 2 //
    value = Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
      Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
        Certificate.weightedSum weights.val (entries.val order coordinate))) }

namespace Integral

/-- Materialize the original parent certificates and unit vector once, then construct their actual weighted sum. -/
def build : Integral retained :=
  let entries := Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
    Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
      Data.Vector.Basic.vectorOfFn (fun index => (retained.block index).certificate order coordinate)))
  let weights := Data.Vector.Basic.vectorOfFn (fun _ : Fin (parent :: parents).length => (1 : Canonical))
  let certificate := Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
    Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
      Certificate.weightedSum weights (entries order coordinate)))
  ⟨⟨entries, rfl⟩, ⟨weights, rfl⟩, ⟨certificate, rfl⟩⟩

variable {retained} (actual : Integral retained)

/-- Read the same once-materialized four original parent-certificate vectors. -/
@[expose] def entries := actual.1.val

/-- The entire stored parent-certificate vector is its original block-projection factory. -/
theorem entries_eq : actual.entries = Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
    Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
      Data.Vector.Basic.vectorOfFn (fun index => (retained.block index).certificate order coordinate))) :=
  actual.1.property

/-- Read the same once-materialized unit vector shared by all four rows. -/
@[expose] def weights := actual.2.1.val

/-- The entire stored weight vector is its original exact unit factory. -/
theorem weights_eq : actual.weights =
    Data.Vector.Basic.vectorOfFn (fun _ : Fin (parent :: parents).length => (1 : Canonical)) :=
  actual.2.1.property

/-- Read the same once-materialized four weighted-sum certificates. -/
@[expose] def certificate := actual.2.2.val

/-- The entire stored certificate vector uses the same earlier materialized entries and weights. -/
theorem certificate_eq : actual.certificate = Data.Vector.Basic.vectorOfFn (fun order : Fin 2 =>
    Data.Vector.Basic.vectorOfFn (fun coordinate : Fin 2 =>
      Certificate.weightedSum actual.weights (actual.entries order coordinate))) :=
  actual.2.2.property

/-- Reading a stored certificate-vector entry returns that SAME original parent block's assembled certificate. -/
theorem entry_eq (index : Fin (parent :: parents).length) (order coordinate : Fin 2) :
    actual.entries order coordinate index = (retained.block index).certificate order coordinate := by
  rewrite [actual.entries_eq, Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply,
    Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- Every stored weight is exactly its original unit Gaussian value. -/
theorem weight_eq (index : Fin (parent :: parents).length) : actual.weights index = 1 := by
  rewrite [actual.weights_eq, Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- Each selected SAME stored certificate is the original weighted factory on its retained row entries. -/
theorem certificate_factory (order coordinate : Fin 2) :
    actual.certificate order coordinate =
      Certificate.weightedSum actual.weights (actual.entries order coordinate) := by
  have original := congrArg
    (fun values : Data.Vector (Data.Vector (Certificate increment) 2) 2 => values order coordinate)
    actual.certificate_eq
  rewrite [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply] at original
  exact original

/-- The selected global Taylor base is the SAME complete original base-channel source-word integral. -/
theorem base (order coordinate : Fin 2) : (actual.certificate order coordinate).base = (PathModel.mk (oldCells
    (source := source) (Specification.Table.baseIndex order coordinate))).integralSample := by
  have original := (congrArg (fun certificate : Certificate increment => certificate.base)
    (actual.certificate_factory order coordinate)).trans (Certificate.weightedSum_base
        actual.weights (actual.entries order coordinate))
  calc
    _ = Algebra.FiniteSum.Fin.sumFin (fun index => actual.weights index * (actual.entries order coordinate
        index).base) := original
    _ = Algebra.FiniteSum.Fin.sumFin (fun index : Fin (parent :: parents).length =>
        ((source.prepared.entry index).preparation.cell.models.cell
          (Specification.Table.baseIndex order coordinate)).integralSample) := by
      apply Algebra.FiniteSum.Fin.sumFin_congr
      intro index
      rewrite [actual.weight_eq index, actual.entry_eq index order coordinate, (retained.block
          index).certificate_base order coordinate]
      exact Data.Gaussian.Basic.one_mul _
    _ = _ := (PathModel.integralSample_ofFn_eq_sumFin _).symm

/-- The selected global Taylor slope is the SAME complete independent derivative-channel source-word integral. -/
theorem slope (order coordinate : Fin 2) : (actual.certificate order coordinate).slope = (PathModel.mk (oldCells
    (source := source) (Specification.Table.slopeIndex order coordinate))).integralSample := by
  have original := (congrArg (fun certificate : Certificate increment => certificate.slope)
    (actual.certificate_factory order coordinate)).trans (Certificate.weightedSum_slope
        actual.weights (actual.entries order coordinate))
  calc
    _ = Algebra.FiniteSum.Fin.sumFin (fun index => actual.weights index * (actual.entries order coordinate
        index).slope) := original
    _ = Algebra.FiniteSum.Fin.sumFin (fun index : Fin (parent :: parents).length =>
        ((source.prepared.entry index).preparation.cell.models.cell
          (Specification.Table.slopeIndex order coordinate)).integralSample) := by
      apply Algebra.FiniteSum.Fin.sumFin_congr
      intro index
      rewrite [actual.weight_eq index, actual.entry_eq index order coordinate, (retained.block
          index).certificate_slope order coordinate]
      exact Data.Gaussian.Basic.one_mul _
    _ = _ := (PathModel.integralSample_ofFn_eq_sumFin _).symm

/-- The actual global Taylor output is the SAME whole flattened global target Request cell-word integral sample. -/
theorem output (order coordinate : Fin 2) : (actual.certificate order coordinate).output = (PathModel.mk
    ((targetCells (next := next) order coordinate))).integralSample := by
  have original := (congrArg (fun certificate : Certificate increment => certificate.output)
    (actual.certificate_factory order coordinate)).trans (Certificate.weightedSum_output
        actual.weights (actual.entries order coordinate))
  calc
    _ = Algebra.FiniteSum.Fin.sumFin (fun index => actual.weights index * (actual.entries order coordinate
        index).output) := original
    _ = Algebra.FiniteSum.Fin.sumFin (fun index =>
        (PathModel.mk ((retained.block index).targetCells order coordinate)).integralSample) := by
      apply Algebra.FiniteSum.Fin.sumFin_congr
      intro index
      rewrite [actual.weight_eq index, actual.entry_eq index order coordinate, (retained.block
          index).certificate_targetSample order coordinate]
      exact Data.Gaussian.Basic.one_mul _
    _ = _ := (retained.targetSample_eq order coordinate).symm

/-- The computed actual global factor is exactly the original-parent-count times the same fixed geometry density sum. -/
theorem factor_eq (order coordinate : Fin 2) : (actual.certificate order coordinate).factor = factor (covered :=
    covered) order coordinate := by
  have original := (congrArg (fun certificate : Certificate increment => certificate.factor)
    (actual.certificate_factory order coordinate)).trans (Certificate.weightedSum_factor
        actual.weights (actual.entries order coordinate))
  calc
    _ = Certificate.weightedFactor actual.weights (actual.entries order coordinate) := original
    _ = _ := by
      unfold Certificate.weightedFactor factor
      apply congrArg (fun total : Rational => ((parent :: parents).length : Rational) * total)
      apply Algebra.FiniteSum.Fin.sumFin_congr
      intro index
      rewrite [actual.weight_eq index, Norm.Basic.normSq_one, actual.entry_eq index order coordinate,
        (retained.block index).certificate_factor order coordinate]
      exact (Data.Rat.Fraction.Field.mul_comm _ _).trans (Data.Rat.Fraction.Field.mul_one_direct _)

include actual in
/-- Actual old/global source-word integrals obey a parameter-fourth remainder with fixed geometry factor.

The factor uses only ORIGINAL parent count, patches/count and endpoints.
All adaptive child counts, actual global Target allocations, signed query
owners and independent arithmetic observations remain the stored originals.
No bank Distinct, completed Stage or canonical-period identity is asserted.
-/
theorem remainder_le (order coordinate : Fin 2) :
    Canonical.normSq
      ((PathModel.mk ((targetCells (next := next) order coordinate))).integralSample -
        (PathModel.mk (oldCells (source := source) (Specification.Table.baseIndex order coordinate))).integralSample -
        increment * (PathModel.mk (oldCells (source := source) (Specification.Table.slopeIndex order
            coordinate))).integralSample) ≤
      factor (covered := covered) order coordinate * Canonical.normSq increment ^ 2 := by
  have original := (actual.certificate order coordinate).remainder_le
  rewrite [← (actual.certificate order coordinate).expansion, actual.output order coordinate, actual.base order
      coordinate, actual.slope order coordinate, actual.factor_eq order coordinate] at original
  exact original

end Integral

/-- Cache each original parent block once, then retain the SAME actual global weighted integral certificate assembly. -/
def buildIntegral :
    (retained : { value : ValueBlocks (next := next) // value = build (next := next) }) × Integral retained.val :=
  let retained := build (next := next)
  let integral := Integral.build retained
  ⟨⟨retained, rfl⟩, integral⟩

end ValueBlocks

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
