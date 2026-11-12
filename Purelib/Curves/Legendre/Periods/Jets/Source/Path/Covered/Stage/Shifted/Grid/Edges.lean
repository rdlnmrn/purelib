module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Nodes
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Ordered positive-node programme and common-dyadic comparison tables

A single original common source/member and strip allocation feed every
positive node. The stored common-view alignments precede the ordered edge
producer. Each positive-positive edge constructs original positions,
BetweenRows and its four weighted integral certificates on those SAME node
values. Original programme caches stay attached to their own actual nodes.
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
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

/-- The original strip payment pays the local unit condition for every actual positive-positive grid edge.

The identical retained original range at parent zero has its factory's
min-one cap. No finer-mesh range or selected-node minimum is constructed.
The statement permits constant physical parents and every moving direction.
-/
theorem pair_unit
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    (direction : Canonical) (admitted : Norm.Basic.normSq direction ≤ allocation.bound)
    (intervals : Nat) (positive : 0 < intervals) (edge : Fin (intervals - 1)) :
    Norm.Basic.normSq (Sampling.gridPositiveIncrement intervals (Sampling.gridPairIndex intervals edge)
      (Sampling.gridPairFollowing intervals edge) direction) ≤ 1 := by
  have capped : (ranges.entry 0).bound ≤ 1 := by
    change min 1 _ ≤ 1
    exact Order.Basic.min_le_left _ _
  have directionUnit : Norm.Basic.normSq direction ≤ 1 :=
    admitted.trans (allocation.bound_le_bound.trans ((ranges.bound_le_entry 0).trans capped))
  exact (Sampling.gridPositiveIncrement_normSq_le intervals positive (Sampling.gridPairIndex intervals edge)
    (Sampling.gridPairFollowing intervals edge) direction).trans directionUnit

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

section StoredNodes

variable (nodes : Nodes intervals positive direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)

namespace Nodes

/-- Actual original first-side Position products at the computed local-difference request view. -/
@[expose] def FirstPositions (edge : Fin (intervals - 1)) :=
  Position.Family (nodes.node (Sampling.gridPairIndex intervals edge)).common.blocks
    (firstRequested (following := Sampling.gridPairFollowing intervals edge) (nodes.node (Sampling.gridPairIndex
      intervals edge))).request

/-- Actual original second-side Position products at the computed local-difference request view. -/
@[expose] def LastPositions (edge : Fin (intervals - 1)) :=
  Position.Family (nodes.node (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
    (Sampling.gridPairFollowing intervals edge))).common.blocks
    (lastRequested (index := Sampling.gridPairIndex intervals edge) (following := Sampling.gridPairFollowing intervals
      edge) (nodes.node (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
      (Sampling.gridPairFollowing intervals edge)))).request

/-- The original BetweenRows application on the SAME two stored nodes and once-retained alignment products. -/
@[expose] def PairRows (aligned : Alignments nodes) (edge : Fin (intervals - 1))
    (firstPositions : nodes.FirstPositions edge) (lastPositions : nodes.LastPositions edge) :=
  AdjacentRows (index := Sampling.gridPairIndex intervals edge)
    (following := Sampling.gridPairFollowing intervals edge) (firstNode := nodes.node (Sampling.gridPairIndex
      intervals edge)) (lastNode := nodes.node
    (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing intervals
    edge)))
    (unit := pair_unit ranges allocation direction admitted intervals positive edge) (firstPositions :=
      firstPositions) (lastPositions := lastPositions)
    (firstAligned := aligned.entry (Sampling.gridPairIndex intervals edge))
    (lastAligned := aligned.entry (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
      (Sampling.gridPairFollowing intervals edge)))

end Nodes

/-- Actual two-sided positions, original global rows and their SAME four weighted integral certificates.

All three original builders are linked by whole-value factory equalities.
Both target Requests are only equality views of the stored original nodes.
The original global occurrence products derive their full prefix and parent
identities from each common.geometry_eq; no signed or model relation is an
input. Bounded Sample callbacks acquire their own original query work when
invoked, and are not claimed to cache infinitely many observations.
-/
@[expose] def Adjacent (aligned : Nodes.Alignments nodes) (edge : Fin (intervals - 1)) :=
  (firstPositions : { value : nodes.FirstPositions edge // value =
    Position.Family.build (nodes.node (Sampling.gridPairIndex intervals edge)).common.blocks
      (firstRequested (following := Sampling.gridPairFollowing intervals edge) (nodes.node (Sampling.gridPairIndex
        intervals edge))).request (nodes.node (Sampling.gridPairIndex intervals edge)).common.geometry_eq }) ×
  (lastPositions : { value : nodes.LastPositions edge // value =
    Position.Family.build (nodes.node (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
      (Sampling.gridPairFollowing intervals edge))).common.blocks
      (lastRequested (index := Sampling.gridPairIndex intervals edge) (following := Sampling.gridPairFollowing
        intervals edge) (nodes.node (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
        (Sampling.gridPairFollowing intervals edge)))).request (nodes.node (Sampling.gridNextIndex intervals
        (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing intervals edge))).common.geometry_eq }) ×
  (rows : { value : nodes.PairRows aligned edge firstPositions.val lastPositions.val // value =
    BetweenRows.build source.prepared ranges allocation
      ((Sampling.gridOffset_normSq_le intervals positive (Sampling.gridPairIndex intervals edge).succ direction).trans
        admitted)
      ((Sampling.gridOffset_normSq_le intervals positive (Sampling.gridNextIndex intervals (Sampling.gridPairIndex
        intervals edge) (Sampling.gridPairFollowing intervals edge)).succ direction).trans admitted)
      widths widths (nodes.node (Sampling.gridPairIndex intervals edge)).common.blocks (nodes.node
        (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing
        intervals edge))).common.blocks
      (pair_unit ranges allocation direction admitted intervals positive edge)
      (Sampling.gridPositiveDifference_nonzero intervals positive (Sampling.gridPairIndex intervals edge)
        (Sampling.gridPairFollowing intervals edge) direction moving) spatial
      (firstRequested (following := Sampling.gridPairFollowing intervals edge) (nodes.node (Sampling.gridPairIndex
        intervals edge))) (lastRequested (index := Sampling.gridPairIndex intervals edge) (following :=
        Sampling.gridPairFollowing intervals edge) (nodes.node (Sampling.gridNextIndex intervals
        (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing intervals edge))))
      firstPositions.val lastPositions.val (aligned.entry (Sampling.gridPairIndex intervals edge)) (aligned.entry
        (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing
        intervals edge))) }) ×
  { actual : BetweenRows.Integral rows.val // actual = BetweenRows.Integral.build rows.val }

namespace Adjacent

/-- Construct one actual edge using only its two SAME stored node values and common-view alignment products. -/
def build (aligned : Nodes.Alignments nodes) (edge : Fin (intervals - 1)) : Adjacent nodes aligned edge :=
  let firstPositions : nodes.FirstPositions edge := Position.Family.build (nodes.node (Sampling.gridPairIndex
    intervals edge)).common.blocks
      (firstRequested (following := Sampling.gridPairFollowing intervals edge) (nodes.node (Sampling.gridPairIndex
        intervals edge))).request (nodes.node (Sampling.gridPairIndex intervals edge)).common.geometry_eq
  let lastPositions : nodes.LastPositions edge := Position.Family.build (nodes.node (Sampling.gridNextIndex intervals
    (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing intervals edge))).common.blocks
      (lastRequested (index := Sampling.gridPairIndex intervals edge) (following := Sampling.gridPairFollowing
        intervals edge) (nodes.node (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
        (Sampling.gridPairFollowing intervals edge)))).request (nodes.node (Sampling.gridNextIndex intervals
        (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing intervals edge))).common.geometry_eq
  let rows : nodes.PairRows aligned edge firstPositions lastPositions := BetweenRows.build source.prepared ranges
    allocation
      ((Sampling.gridOffset_normSq_le intervals positive (Sampling.gridPairIndex intervals edge).succ direction).trans
        admitted)
      ((Sampling.gridOffset_normSq_le intervals positive (Sampling.gridNextIndex intervals (Sampling.gridPairIndex
        intervals edge) (Sampling.gridPairFollowing intervals edge)).succ direction).trans admitted)
      widths widths (nodes.node (Sampling.gridPairIndex intervals edge)).common.blocks (nodes.node
        (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing
        intervals edge))).common.blocks
      (pair_unit ranges allocation direction admitted intervals positive edge)
      (Sampling.gridPositiveDifference_nonzero intervals positive (Sampling.gridPairIndex intervals edge)
        (Sampling.gridPairFollowing intervals edge) direction moving) spatial
      (firstRequested (following := Sampling.gridPairFollowing intervals edge) (nodes.node (Sampling.gridPairIndex
        intervals edge))) (lastRequested (index := Sampling.gridPairIndex intervals edge) (following :=
        Sampling.gridPairFollowing intervals edge) (nodes.node (Sampling.gridNextIndex intervals
        (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing intervals edge))))
      firstPositions lastPositions (aligned.entry (Sampling.gridPairIndex intervals edge)) (aligned.entry
        (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing
        intervals edge)))
  let actual : BetweenRows.Integral rows := BetweenRows.Integral.build rows
  ⟨⟨firstPositions, rfl⟩, ⟨lastPositions, rfl⟩, ⟨rows, rfl⟩, ⟨actual, rfl⟩⟩

variable {nodes} {aligned : Nodes.Alignments nodes} {edge : Fin (intervals - 1)}
    (retained : Adjacent nodes aligned edge)

/-- Read the SAME first target's original ordered Position product. -/
@[expose, macro_inline] def firstPositions : nodes.FirstPositions edge := retained.1.val

/-- Read the SAME last target's original ordered Position product. -/
@[expose, macro_inline] def lastPositions : nodes.LastPositions edge := retained.2.1.val

/-- Read all SAME original parent/pair/restriction/Sample/row caches for the actual edge. -/
@[expose, macro_inline] def rows : nodes.PairRows aligned edge retained.firstPositions retained.lastPositions :=
  retained.2.2.1.val

/-- Read the SAME original weighted global integral certificates on those stored rows. -/
@[expose, macro_inline] def actual : BetweenRows.Integral retained.rows := retained.2.2.2.val

/-- The whole first Position product is its original factory, including complete parent and prefix equations. -/
theorem firstPositions_eq : retained.firstPositions = Position.Family.build (nodes.node (Sampling.gridPairIndex
  intervals edge)).common.blocks
      (firstRequested (following := Sampling.gridPairFollowing intervals edge) (nodes.node (Sampling.gridPairIndex
        intervals edge))).request (nodes.node (Sampling.gridPairIndex intervals edge)).common.geometry_eq :=
        retained.1.property

/-- The whole last Position product is its original factory, including complete parent and prefix equations. -/
theorem lastPositions_eq : retained.lastPositions = Position.Family.build (nodes.node (Sampling.gridNextIndex
  intervals (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing intervals edge))).common.blocks
      (lastRequested (index := Sampling.gridPairIndex intervals edge) (following := Sampling.gridPairFollowing
        intervals edge) (nodes.node (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
        (Sampling.gridPairFollowing intervals edge)))).request (nodes.node (Sampling.gridNextIndex intervals
        (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing intervals edge))).common.geometry_eq :=
        retained.2.1.property

/-- The whole edge row product is the original builder on these SAME stored positions and alignments. -/
theorem rows_eq : retained.rows = BetweenRows.build source.prepared ranges allocation
      ((Sampling.gridOffset_normSq_le intervals positive (Sampling.gridPairIndex intervals edge).succ direction).trans
        admitted)
      ((Sampling.gridOffset_normSq_le intervals positive (Sampling.gridNextIndex intervals (Sampling.gridPairIndex
        intervals edge) (Sampling.gridPairFollowing intervals edge)).succ direction).trans admitted)
      widths widths (nodes.node (Sampling.gridPairIndex intervals edge)).common.blocks (nodes.node
        (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing
        intervals edge))).common.blocks
      (pair_unit ranges allocation direction admitted intervals positive edge)
      (Sampling.gridPositiveDifference_nonzero intervals positive (Sampling.gridPairIndex intervals edge)
        (Sampling.gridPairFollowing intervals edge) direction moving) spatial
      (firstRequested (following := Sampling.gridPairFollowing intervals edge) (nodes.node (Sampling.gridPairIndex
        intervals edge))) (lastRequested (index := Sampling.gridPairIndex intervals edge) (following :=
        Sampling.gridPairFollowing intervals edge) (nodes.node (Sampling.gridNextIndex intervals
        (Sampling.gridPairIndex intervals edge) (Sampling.gridPairFollowing intervals edge))))
      retained.firstPositions retained.lastPositions (aligned.entry (Sampling.gridPairIndex intervals edge))
        (aligned.entry (Sampling.gridNextIndex intervals (Sampling.gridPairIndex intervals edge)
        (Sampling.gridPairFollowing intervals edge))) :=
  retained.2.2.1.property

/-- The whole integral cache is the original weighted-sum factory on these SAME stored edge rows. -/
theorem actual_eq : retained.actual = BetweenRows.Integral.build retained.rows := retained.2.2.2.property

end Adjacent

namespace Nodes

/-- The exact original ordered edge-cache vector on these same nodes and retained alignments.

Each original Adjacent value keeps its complete factory equation, including
both Position products and the same row/integral caches. This family names
the existing dependent vector without constructing or changing any edge.
-/
@[expose] def Edges (aligned : Alignments nodes) : Type _ :=
  DependentVector (fun edge : Fin (intervals - 1) =>
    { value : Adjacent nodes aligned edge // value = Adjacent.build nodes aligned edge })

namespace Edges

variable (aligned : Alignments nodes)

/-- Construct the original ordered edge-cache vector on these same retained nodes and alignments.

Each existing Adjacent builder runs once at its literal finite position,
retaining the same complete Position, row and integral factories. This
separate compilation boundary does not construct nodes or alignments.
-/
@[expose, noinline] def build : Edges nodes aligned :=
  DependentVector.ofFn (fun edge => ⟨Adjacent.build nodes aligned edge, rfl⟩)

/-- The entire ordered edge cache has its exact original dependent-vector factory. -/
theorem build_eq : build nodes aligned =
    DependentVector.ofFn (fun edge => ⟨Adjacent.build nodes aligned edge, rfl⟩) := rfl

end Edges

end Nodes

end StoredNodes

end PositiveGridNode

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
