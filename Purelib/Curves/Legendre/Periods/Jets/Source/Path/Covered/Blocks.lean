module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
public import Purelib.Curves.Legendre.Periods.Jets.Source.Stage
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Blocks
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Integration.CertifiedProgram.Comparison
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Geometric.Comparison
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Data.Vector.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

/-! # Original source programmes on a retained covered-block spine

Every block keeps its complete original parent cache. Its six actual
programmes may use an independently selected allocation path and floor;
their cell readbacks retain the original preparation callback. Reading
the ordered programme table never prepares a source or rebuilds a programme.
Stationary owner handoffs forward the unchanged tail without a summand.
-/

public section

attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath (Blocks)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational.Geometric.Basic
  (quarterRadius quarterRadius_eq_mul_pow quarterRadius_nonneg)
open Purelib.Riemann.Periods

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
variable {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
variable {start finish : LiftedPoint 2}

/-- Six actual source programmes retaining their allocation, floor, preparation family and source-cell readbacks.

The exact dependent tuple retains the supplied whole programme table and
its common original source family. Pointwise cell ownership also admits
staged model wrappers. The allocation path may differ from the physical
centered chain and from the allocations at other blocks.
-/
@[expose] def Programs (covered : CoveredParents count parents)
    (chain : CenteredPathChain parents (start := start) (finish := finish)) :=
  Σ first : LiftedPoint 2, Σ last : LiftedPoint 2,
  Σ allocation : LiftedPath 2 first last, Σ floor : Nat,
  Σ prepared : (index : Nat) → PreparedParents covered floor (CellEndpoints.Targets.build allocation index),
  {values : Data.Vector RefinementProgram 6 //
    (∀ channel index, ((values channel).model index).cells = (sources covered (prepared index) chain).cells channel) ∧
    ∀ channel, (values channel).errorScale = errorScale parents}

namespace Programs

variable {covered : CoveredParents count parents}
variable {chain : CenteredPathChain parents (start := start) (finish := finish)}

/-- Read the original allocation path retained by the six supplied programmes. -/
@[expose] def allocation (actual : Programs covered chain) : LiftedPath 2 actual.1 actual.2.1 := actual.2.2.1

/-- Read the common original source floor without executing a preparation. -/
@[expose] def floor (actual : Programs covered chain) : Nat := actual.2.2.2.1

/-- Read the exact original source callback at its retained allocation and floor. -/
@[expose] def prepared (actual : Programs covered chain) (index : Nat) :
    PreparedParents covered actual.floor (CellEndpoints.Targets.build actual.allocation index) :=
  actual.2.2.2.2.1 index

/-- Read one complete original supplied programme from its retained bounded table. -/
@[expose] def get (actual : Programs covered chain) (channel : Fin 6) : RefinementProgram :=
  actual.2.2.2.2.2.val channel

/-- Each original model retains exactly the source cells at its own preparation stage. -/
theorem get_cells (actual : Programs covered chain) (channel : Fin 6) (index : Nat) :
    ((actual.get channel).model index).cells = (sources covered (actual.prepared index) chain).cells channel :=
  actual.2.2.2.2.2.property.1 channel index

/-- Each retained programme sample reads its actual original source family at the same stage. -/
theorem sample_eq (actual : Programs covered chain) (channel : Fin 6) (index : Nat) :
    ((actual.get channel).model index).integralSample =
      (PathModel.mk ((sources covered (actual.prepared index) chain).cells channel)).integralSample :=
  congrArg (fun cells => (PathModel.mk cells).integralSample) (actual.get_cells channel index)

/-- The retained original programme keeps the movement scale of its same physical parent list. -/
theorem errorScale_eq (actual : Programs covered chain) (channel : Fin 6) :
    (actual.get channel).errorScale = errorScale parents := actual.2.2.2.2.2.property.2 channel

/-- Retain six supplied whole programmes with their original stage cells and movement scales.

The table stores the actual input values by reference. The pointwise
readbacks are ownership data; this constructor performs no source
preparation or replacement programme construction.
-/
def ofPrograms {first last : LiftedPoint 2} (allocation : LiftedPath 2 first last) (floor : Nat)
    (prepared : (index : Nat) → PreparedParents covered floor (CellEndpoints.Targets.build allocation index))
    (values : Data.Vector RefinementProgram 6)
    (cells : ∀ channel index,
      ((values channel).model index).cells = (sources covered (prepared index) chain).cells channel)
    (scales : ∀ channel, (values channel).errorScale = errorScale parents) : Programs covered chain :=
  ⟨first, last, allocation, floor, prepared, values, cells, scales⟩

/-- Each retained table entry is the same complete programme supplied to the constructor. -/
theorem ofPrograms_get {first last : LiftedPoint 2} (allocation : LiftedPath 2 first last) (floor : Nat)
    (prepared : (index : Nat) → PreparedParents covered floor (CellEndpoints.Targets.build allocation index))
    (values : Data.Vector RefinementProgram 6)
    (cells : ∀ channel index,
      ((values channel).model index).cells = (sources covered (prepared index) chain).cells channel)
    (scales : ∀ channel, (values channel).errorScale = errorScale parents) (channel : Fin 6) :
    (ofPrograms allocation floor prepared values cells scales).get channel = values channel := (rfl)

/-- Retain supplied whole programmes through their actual original Stage source lists.

The source family, Stage ownership and pointwise model-cell readbacks link
the same original values to their preparations. The constructor forwards
the supplied programme table; it constructs no Stage, model, observation or
replacement programme, and it assumes no sample comparison inequality.
-/
def ofStages {point : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := point) (finish := point))
    {first last : LiftedPoint 2} (allocation : LiftedPath 2 first last) (floor : Nat)
    (prepared : (index : Nat) → PreparedParents covered floor (CellEndpoints.Targets.build allocation index))
    (stages : (index : Nat) → Stage parameter ⟨point, chain.path⟩ index)
    (exactSources : ∀ index, (stages index).sources = sources covered (prepared index) chain)
    (values : Data.Vector RefinementProgram 6)
    (cells : ∀ channel index, ((values channel).model index).cells = (stages index).sources.cells channel)
    (scales : ∀ channel, (values channel).errorScale = errorScale parents) : Programs covered chain :=
  ofPrograms allocation floor prepared values
    (fun channel index => (cells channel index).trans
      (congrArg (fun sources => sources.cells channel) (exactSources index))) scales

/-- Stage ownership retains each complete original supplied programme at its same bounded position. -/
theorem ofStages_get {point : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := point) (finish := point))
    {first last : LiftedPoint 2} (allocation : LiftedPath 2 first last) (floor : Nat)
    (prepared : (index : Nat) → PreparedParents covered floor (CellEndpoints.Targets.build allocation index))
    (stages : (index : Nat) → Stage parameter ⟨point, chain.path⟩ index)
    (exactSources : ∀ index, (stages index).sources = sources covered (prepared index) chain)
    (values : Data.Vector RefinementProgram 6)
    (cells : ∀ channel index, ((values channel).model index).cells = (stages index).sources.cells channel)
    (scales : ∀ channel, (values channel).errorScale = errorScale parents) (channel : Fin 6) :
    (ofStages chain allocation floor prepared stages exactSources values cells scales).get channel = values channel :=
  ofPrograms_get allocation floor prepared values
    (fun channel index => (cells channel index).trans
      (congrArg (fun sources => sources.cells channel) (exactSources index))) scales channel

end Programs

/-- Independently allocated original six-programme products on the exact retained covered-block caches.

Each moving block keeps its own source allocation, preparation callback and
whole programme values. An empty chain contains no programme, and a
stationary owner handoff forwards the original tail without adding one.
-/
@[expose] def BlockPrograms {sheet : Fin 2} :
    ∀ {first last : Canonical} {source : Owner ((Fibre.frameCurve frame).polynomial.eval first)}
      {target : Owner ((Fibre.frameCurve frame).polynomial.eval last)}
      {blocks : Blocks (Fibre.frameCurve frame).polynomial first source last target},
      Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet blocks → Type 1
  | _, _, _, _, .nil _ _, _ => PUnit
  | _, _, _, _, .cons _ _, caches =>
      Programs caches.1.covered caches.1.centeredChain × BlockPrograms caches.2
  | _, _, _, _, .handoff _ tail, caches => BlockPrograms (blocks := tail) caches
termination_by structural _ _ _ _ blocks _ => blocks

namespace BlockPrograms

variable {sheet : Fin 2}

/-- Materialize the original six-programme rows in their retained covered-block order.

Only bounded reads of supplied programme values occur. The structural tail
is reused directly, and stationary handoffs do not create rows or rerun
any source or programme factory.
-/
@[expose] def values :
    ∀ {first last : Canonical} {source : Owner ((Fibre.frameCurve frame).polynomial.eval first)}
      {target : Owner ((Fibre.frameCurve frame).polynomial.eval last)}
      {blocks : Blocks (Fibre.frameCurve frame).polynomial first source last target}
      {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet blocks},
      BlockPrograms caches → List (Data.Vector RefinementProgram 6)
  | _, _, _, _, .nil _ _, _, _ => []
  | _, _, _, _, .cons _ tail, caches, actual =>
      Data.Vector.Basic.vectorOfFn (fun channel : Fin 6 => actual.1.get channel) ::
        values (blocks := tail) (caches := caches.2) actual.2
  | _, _, _, _, .handoff _ tail, caches, actual => values (blocks := tail) (caches := caches) actual
termination_by structural _ _ _ _ blocks _ _ => blocks

/-- The retained programme rows contain exactly one entry per original moving block. -/
theorem values_length :
    ∀ {first last : Canonical} {source : Owner ((Fibre.frameCurve frame).polynomial.eval first)}
      {target : Owner ((Fibre.frameCurve frame).polynomial.eval last)}
      {blocks : Blocks (Fibre.frameCurve frame).polynomial first source last target}
      {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet blocks}
      (actual : BlockPrograms caches), (values actual).length = blocks.length
  | _, _, _, _, .nil point owner, _, _ => (Blocks.length_nil point owner).symm
  | _, _, _, _, .cons covered tail, caches, actual => by
      change (values (blocks := tail) (caches := caches.2) actual.2).length + 1 = _
      rewrite [values_length actual.2, Blocks.length_cons]
      rfl
  | _, _, _, _, .handoff join tail, caches, actual => by
      exact (values_length (blocks := tail) (caches := caches) actual).trans
        (Blocks.length_handoff join.2 tail).symm
termination_by structural _ _ _ _ blocks _ _ => blocks

/-- Sum the actual same-stage geometric views of one retained programme channel.

The ordered source-programme table is materialized before constructing the
finite sum. The existing geometric sum reads the actual original programme
caches and preserves its common sample index.
-/
def geometric
    {first last : Canonical} {source : Owner ((Fibre.frameCurve frame).polynomial.eval first)}
    {target : Owner ((Fibre.frameCurve frame).polynomial.eval last)}
    {blocks : Blocks (Fibre.frameCurve frame).polynomial first source last target}
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet blocks}
    (actual : BlockPrograms caches) (channel : Fin 6) : GeometricApproximation :=
  let rows := values actual
  GeometricApproximation.sum (fun index : Fin rows.length =>
    ((rows[index.val]'index.isLt) channel).certifiedView.program.geometric)

/-- An empty retained block spine has the original exact-zero geometric sum. -/
theorem geometric_nil (point : Canonical) (owner : Owner ((Fibre.frameCurve frame).polynomial.eval point))
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet (.nil point owner)}
    (actual : BlockPrograms caches) (channel : Fin 6) :
    actual.geometric channel = GeometricApproximation.exact 0 := (rfl)

/-- Prepending an actual block adds its supplied programme's geometric view to the original retained tail. -/
theorem geometric_cons {first middle last : Canonical} {ambient : Geometry.Rational.Box}
    {path : Polynomial.Geometry.ClearPath (Fibre.frameCurve frame).polynomial ambient first middle}
    {source : Owner ((Fibre.frameCurve frame).polynomial.eval first)}
    {target : Owner ((Fibre.frameCurve frame).polynomial.eval last)}
    (covered : Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath path source)
    (tail : Blocks (Fibre.frameCurve frame).polynomial middle covered.traced.finishOwner last target)
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet (.cons covered tail)}
    (actual : BlockPrograms caches) (channel : Fin 6) :
    actual.geometric channel =
      (actual.1.get channel).certifiedView.program.geometric.add (actual.2.geometric channel) := by
  change
    (((Data.Vector.Basic.vectorOfFn
      (fun channel : Fin 6 => actual.1.get channel)) channel).certifiedView.program.geometric).add
        (actual.2.geometric channel) = _
  rewrite [Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- A stationary handoff retains the identical geometric sum of the supplied tail programmes. -/
theorem geometric_handoff {point last : Canonical}
    {source : Owner ((Fibre.frameCurve frame).polynomial.eval point)}
    {target : Owner ((Fibre.frameCurve frame).polynomial.eval last)}
    (join : Blocks.Join source)
    (tail : Blocks (Fibre.frameCurve frame).polynomial point join.1 last target)
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet (.handoff join tail)}
    (actual : BlockPrograms caches) (channel : Fin 6) :
    actual.geometric channel = geometric (blocks := tail) (caches := caches) actual channel := (rfl)

/-- Independently allocated block programmes approach the same original global source sample.

Every head comparison uses the original saved source slice and that
block's actual preparation callback, with their separate floors and
allocation paths. The existing geometric sum's retained movement scale
pays the finite aggregate discrepancy. Stationary handoffs contribute
neither a sample nor an extra comparison term.
-/
theorem samples_close {allocationStart allocationFinish : LiftedPoint 2}
    {allocation : LiftedPath 2 allocationStart allocationFinish} {wholeFloor index : Nat} :
    ∀ {first last : Canonical} {source : Owner ((Fibre.frameCurve frame).polynomial.eval first)}
      {target : Owner ((Fibre.frameCurve frame).polynomial.eval last)}
      {blocks : Blocks (Fibre.frameCurve frame).polynomial first source last target}
      (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet blocks)
      (actual : BlockPrograms caches)
      (whole : OnBlocks (floor := wholeFloor) (targets := CellEndpoints.Targets.build allocation index) caches)
      (channel : Fin 6),
      Norm.Basic.normSq
        ((PathModel.mk ((sources caches.covered whole caches.centeredChain).cells channel)).integralSample -
          (actual.geometric channel).sample index) ≤ quarterRadius (actual.geometric channel).errorScale index
  | _, _, _, _, .nil point owner, caches, actual, whole, channel => by
      rewrite [geometric_nil point owner (caches := caches)]
      change Norm.Basic.normSq
        ((PathModel.mk
          ((sources (.nil : CoveredParents 1 []) whole caches.centeredChain).cells channel)).integralSample - 0) ≤
          quarterRadius 0 index
      rewrite [sources_cells]
      cases whole
      rewrite [cells_nil]
      change Norm.Basic.normSq ((0 : Canonical) - 0) ≤ quarterRadius 0 index
      rewrite [Basic.sub_self, Norm.Basic.normSq_zero]
      exact quarterRadius_nonneg (by decide) index
  | _, _, _, _, .cons covered tail, caches, actual, whole, channel => by
      let divided := split caches.1.covered (Blocks.ParentCaches.covered caches.2) whole
      have sampled := split_integralSample caches.1.covered (Blocks.ParentCaches.covered caches.2)
        caches.centeredChain caches.1.centeredChain caches.2.centeredChain whole channel
      have headBound := later_close caches.1.covered caches.1.centeredChain
        (actual.1.prepared index) divided.1 channel (Nat.le_refl index)
      rewrite [← actual.1.sample_eq channel index, ← actual.1.errorScale_eq channel] at headBound
      have tailBound := samples_close (blocks := tail) caches.2 actual.2 divided.2 channel
      change Norm.Basic.normSq
        ((PathModel.mk ((sources
          (Riemann.Integration.PreparedCoveredParentLists.CoveredParents.append
            caches.1.covered (Blocks.ParentCaches.covered caches.2))
          whole caches.centeredChain).cells channel)).integralSample -
          (actual.geometric channel).sample index) ≤ quarterRadius (actual.geometric channel).errorScale index
      rewrite [sampled, geometric_cons covered tail actual channel]
      change Norm.Basic.normSq
        (((PathModel.mk ((sources caches.1.covered divided.1 caches.1.centeredChain).cells channel)).integralSample +
            (PathModel.mk ((sources (Blocks.ParentCaches.covered caches.2)
              divided.2 caches.2.centeredChain).cells channel)).integralSample) -
          (((actual.1.get channel).model index).integralSample + (actual.2.geometric channel).sample index)) ≤
        quarterRadius (2 * ((actual.1.get channel).errorScale + (actual.2.geometric channel).errorScale)) index
      have difference :
          ((PathModel.mk ((sources caches.1.covered divided.1 caches.1.centeredChain).cells channel)).integralSample +
            (PathModel.mk ((sources (Blocks.ParentCaches.covered caches.2)
              divided.2 caches.2.centeredChain).cells channel)).integralSample) -
          (((actual.1.get channel).model index).integralSample + (actual.2.geometric channel).sample index) =
          ((PathModel.mk ((sources caches.1.covered divided.1 caches.1.centeredChain).cells channel)).integralSample -
            ((actual.1.get channel).model index).integralSample) +
          ((PathModel.mk ((sources (Blocks.ParentCaches.covered caches.2)
            divided.2 caches.2.centeredChain).cells channel)).integralSample -
            (actual.2.geometric channel).sample index) := by ring1
      rewrite [difference]
      exact ((Norm.Bounds.normSq_add_le_two _ _).trans
        (Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct headBound tailBound) (by decide))).trans_eq (by
            rewrite [quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow, quarterRadius_eq_mul_pow]
            ring1)
  | _, _, _, _, .handoff join tail, caches, actual, whole, channel => by
      have retained := samples_close (blocks := tail) caches actual whole channel
      rewrite [sources_cells] at retained
      rewrite [geometric_handoff join tail actual channel, sources_cells]
      exact retained
termination_by structural _ _ _ _ blocks _ _ _ _ => blocks

/-- Compare the supplied whole programme with the actual ordered sum of the supplied block outputs.

Every block may use its own allocation and floor. Pointwise ownership
reads the supplied global and local model cells; the finite comparison
is derived internally from their original preparation laws. No source
builder, replacement programme or stage-zero model is evaluated here.
-/
def output_equivalent
    {first last : Canonical} {source : Owner ((Fibre.frameCurve frame).polynomial.eval first)}
    {target : Owner ((Fibre.frameCurve frame).polynomial.eval last)}
    {blocks : Blocks (Fibre.frameCurve frame).polynomial first source last target}
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet blocks}
    (whole : Programs caches.covered caches.centeredChain) (actual : BlockPrograms caches) (channel : Fin 6) :
    NamedEquivalent (whole.get channel).output.name
      (PeriodMatrix.sumNamed (fun entry : Fin (values actual).length =>
        (((values actual)[entry.val]'entry.isLt) channel).output)).name := by
  let rows := values actual
  let original := (whole.get channel).certifiedView.program
  let combined := actual.geometric channel
  have distance (index : Nat) : Norm.Basic.normSq (original.geometric.sample index - combined.sample index) ≤
      quarterRadius combined.errorScale index := by
    change Norm.Basic.normSq (((whole.get channel).model index).integralSample - combined.sample index) ≤ _
    rewrite [whole.sample_eq channel index]
    exact samples_close caches actual (whole.prepared index) channel
  let compared := Sequence.Name.Equivalence.approximationEquivalent_toNamed
    (original.geometric.equivalentOfSamplesClose combined combined.errorScale combined.errorScale_nonneg distance)
  let summed := PeriodMatrix.sumNamed_equivalent_geometricSum
    (fun entry : Fin rows.length => ((rows[entry.val]'entry.isLt) channel).output)
    (fun entry : Fin rows.length => ((rows[entry.val]'entry.isLt) channel).certifiedView.program.geometric)
    (fun entry => ((rows[entry.val]'entry.isLt) channel).certifiedView.program.output_equivalent_geometric)
  exact original.output_equivalent_geometric.trans (compared.trans summed.symm)

end BlockPrograms

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
