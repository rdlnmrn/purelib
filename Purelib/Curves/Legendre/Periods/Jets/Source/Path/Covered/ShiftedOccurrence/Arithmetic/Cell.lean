module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Sample
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Restriction
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Restriction
public import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Arithmetic.Taylor.Integral
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Fin
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Transport
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Actual same-child integral Taylor data on one retained global occurrence

A real old-source-first joint acquisition pays both actual source allocations.
The selected global occurrence retains its six original restrictions and
one actual signed alignment before bounded-time queries. Every bounded-time
answer stores both original bundles, its precise Point.Step, original Joint,
independently paid arithmetic bank, direct Query and ten shared comparisons once.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Calculus.Jet
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation (Reading RootObservation)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets.UniformObservation (ArithmeticComparison)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.RootContinuation
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent
  (startPoint finishPoint liftedCell ShiftedAcquisition)

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
    {sourceIndex : Fin (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).length}
    (located : Occurrence next.blocks next.requested.request sourceIndex)

namespace ValueCell

/-- The six SAME original cached polynomial restrictions at this global occurrence. -/
@[expose] def Restrictions := ShiftedAcquisition.Restrictions
  (child := (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2)[
    sourceIndex.val]'sourceIndex.isLt) (source.prepared.entry located.block)

/-- The original signed alignment type on this occurrence's SAME retained trace and reference owner. -/
@[expose] def PathAlignment := Acquisition.Segment.RootComparisons.Alignment
  (DependentProduct.get (parent :: parents) next.blocks located.block).comparison.paths
  (DependentProduct.get (parent :: parents) next.blocks located.block).comparison.firstReference

end ValueCell

/-- Cache original child restrictions and one signed Alignment before any actual bounded-time query callback.

The nominal owners are the same real old/target source requests. Stored
whole factory identities retain the original child polynomial caches and
actual path-comparison alignment; no source, trace or continuation replays.
-/
@[expose] def ValueCell :=
  (_ : { value : ValueCell.Restrictions located //
    value = ShiftedAcquisition.Restrictions.build }) ×
  { value : ValueCell.PathAlignment located //
    value = (DependentProduct.get (parent :: parents) next.blocks located.block).comparison.align }

namespace ValueCell

/-- Retain the supplied original child restrictions and signed Alignment with their complete factory equations.

No factory executes here. A block consumer can pass its one stored Alignment
to every actual child while each child retains its independently materialized
six-table restriction bank. Both exact nominal parent and whole factory identities stay
in the original ValueCell representation.
-/
def ofRetained (restriction : Restrictions located)
    (restriction_eq : restriction = ShiftedAcquisition.Restrictions.build)
    (aligned : PathAlignment located)
    (aligned_eq : aligned = (DependentProduct.get (parent :: parents) next.blocks located.block).comparison.align) :
    ValueCell located :=
  ⟨⟨restriction, restriction_eq⟩, ⟨aligned, aligned_eq⟩⟩

/-- Compile the six child restrictions and original signed alignment exactly once, then retain those same caches. -/
def build : ValueCell located :=
  let restriction : Restrictions located := ShiftedAcquisition.Restrictions.build
    (source := source.prepared.entry located.block)
    (child := (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2)[
      sourceIndex.val]'sourceIndex.isLt)
  let aligned : PathAlignment located :=
    (DependentProduct.get (parent :: parents) next.blocks located.block).comparison.align
  ofRetained located restriction rfl aligned rfl

variable {located} (cell : ValueCell located)

/-- Read the SAME materialized six original polynomial child restrictions. -/
@[expose] def restriction := cell.1.val

/-- Read the SAME retained actual signed alignment of the original block's materialized trace. -/
@[expose] def aligned := cell.2.val

section Retained

variable (restriction : Restrictions located)
    (restriction_eq : restriction = ShiftedAcquisition.Restrictions.build)
    (aligned : PathAlignment located)
    (aligned_eq : aligned = (DependentProduct.get (parent :: parents) next.blocks located.block).comparison.align)

/-- Retaining original caches reads back the same supplied restriction bank at every original dependent index.

The closed proposition retains all nominal parent requests, occurrence bounds
and complete restriction/alignment factory equations of the constructor.
-/
abbrev RetainedRestriction : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
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
    {sourceIndex : Fin (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).length}
    {located : Occurrence next.blocks next.requested.request sourceIndex}
    (restriction : Restrictions located)
    (restriction_eq : restriction = ShiftedAcquisition.Restrictions.build)
    (aligned : PathAlignment located)
    (aligned_eq : aligned = (DependentProduct.get (parent :: parents) next.blocks located.block).comparison.align),
    (ofRetained located restriction restriction_eq aligned aligned_eq).restriction = restriction

/-- Retaining existing caches reads back the same original child polynomial six-table restriction bank. -/
theorem ofRetained_restriction : RetainedRestriction := by
  intro parameter increment frame basis target count parent parents covered chain ranges allocation admitted widths
    root roots spatial nonzero sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage
    source next sourceIndex located restriction restriction_eq aligned aligned_eq
  unfold ofRetained
  rfl

/-- Retaining original caches reads back the same supplied alignment at every original dependent index.

The closed proposition retains all nominal parent requests, occurrence bounds
and complete restriction/alignment factory equations of the constructor.
-/
abbrev RetainedAligned : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
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
    {sourceIndex : Fin (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).length}
    {located : Occurrence next.blocks next.requested.request sourceIndex}
    (restriction : Restrictions located)
    (restriction_eq : restriction = ShiftedAcquisition.Restrictions.build)
    (aligned : PathAlignment located)
    (aligned_eq : aligned = (DependentProduct.get (parent :: parents) next.blocks located.block).comparison.align),
    (ofRetained located restriction restriction_eq aligned aligned_eq).aligned = aligned

/-- Retaining existing caches reads back the identical shared block Alignment without executing its factory. -/
theorem ofRetained_aligned : RetainedAligned := by
  intro parameter increment frame basis target count parent parents covered chain ranges allocation admitted widths
    root roots spatial nonzero sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage
    source next sourceIndex located restriction restriction_eq aligned aligned_eq
  unfold ofRetained
  rfl

end Retained

/-- The six polynomial restrictions retain their complete actual original cache factory. -/
theorem restriction_eq : cell.restriction = ShiftedAcquisition.Restrictions.build := cell.1.property

/-- Every retained cell reads back its exact original signed comparison factory at all original indices.

The complete proposition retains the original source/target requests,
occurrence bounds and the whole retained cell, including both actual caches.
-/
abbrev AlignmentFactory : Prop :=
  ∀ {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
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
    {sourceIndex : Fin (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).length}
    {located : Occurrence next.blocks next.requested.request sourceIndex}
    (cell : ValueCell located),
    cell.aligned = (DependentProduct.get (parent :: parents) next.blocks located.block).comparison.align

/-- The alignment retains the complete actual original comparison factory, without a new walk. -/
theorem aligned_eq : AlignmentFactory := by
  intro parameter increment frame basis target count parent parents covered chain ranges allocation admitted widths
    root roots spatial nonzero sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage
    source next sourceIndex located cell
  exact cell.2.property

/-- The original query-level sample specialized to this same retained child and exact stored block Alignment.

The seven cache fields and whole factory equalities belong to the original
Occurrence.Sample. This exact type view introduces no owner, observation,
request, evaluator bank or polynomial restriction.
-/
@[expose] def Sample (time : { input : Rational // Primitive.unitInterval.Contains input }) :=
  Occurrence.Sample located cell.aligned nonzero spatial time

/-- Query the original occurrence once through its minimal query-level constructor and same stored Alignment. -/
def sampleAt (time : { input : Rational // Primitive.unitInterval.Contains input }) : Sample cell time :=
  Occurrence.Sample.build located cell.aligned nonzero spatial time

namespace Sample

variable {cell} {time : { input : Rational // Primitive.unitInterval.Contains input }}
    (answer : Sample cell time)

/-- The exact retained child occurrence derives the SAME original source/child starting sheet. -/
theorem sameSheet :
    (startPoint ((parent :: parents)[located.block.val]'located.block.isLt)).sheet =
      (startPoint ((next.requested.request.shape.val.1 :: next.requested.request.shape.val.2)[
        sourceIndex.val]'sourceIndex.isLt)).sheet :=
  ((DependentProduct.get (parent :: parents) next.blocks located.block).shifted.child_sheet
    located.child located.parent_eq).symm

/-- The endpoint-preserving old request time is exactly the original polynomial restriction's affine time. -/
theorem mappedTime : located.sourceInput time.val =
    Restriction.parameter
      ((next.requested.request.shape.val.1 :: next.requested.request.shape.val.2)[
        sourceIndex.val]'sourceIndex.isLt).edge.left.parameter
      ((next.requested.request.shape.val.1 :: next.requested.request.shape.val.2)[
        sourceIndex.val]'sourceIndex.isLt).edge.request.endpoint.parameter time.val :=
  Riemann.Branches.PreparedSheetContinuation.parameterAt_eq_affine _ _ _

/-- Transport the selected actual old base observation to its SAME retained cached child restriction. -/
@[expose] def restrictedBase (order coordinate : Fin 2) := UniformObservation.restrictAt
  (liftedCell ((next.requested.request.shape.val.1 :: next.requested.request.shape.val.2)[
    sourceIndex.val]'sourceIndex.isLt))
  (cell.restriction.cache (Specification.Table.baseIndex order coordinate))
  (sameSheet (located := located)) (answer.old.1.channel (Specification.Table.baseIndex order coordinate))
  (mappedTime (located := located) (time := time))

/-- Transport the selected actual independent slope observation through its SAME stored child table. -/
@[expose] def restrictedSlope (order coordinate : Fin 2) := UniformObservation.restrictAt
  (liftedCell ((next.requested.request.shape.val.1 :: next.requested.request.shape.val.2)[
    sourceIndex.val]'sourceIndex.isLt))
  (cell.restriction.cache (Specification.Table.slopeIndex order coordinate))
  (sameSheet (located := located)) (answer.old.1.channel (Specification.Table.slopeIndex order coordinate))
  (mappedTime (located := located) (time := time))

/-- Preserve the selected SAME stored source comparison on the identical physical restricted base model. -/
@[expose] def baseComparison (order coordinate : Fin 2) :
    ArithmeticComparison (answer.restrictedBase order coordinate)
      (answer.numerics order coordinate).1 answer.sourceIdentity :=
  ArithmeticComparison.restrictAt
  (liftedCell ((next.requested.request.shape.val.1 :: next.requested.request.shape.val.2)[
    sourceIndex.val]'sourceIndex.isLt))
  (cell.restriction.cache (Specification.Table.baseIndex order coordinate))
  (sameSheet (located := located)) (answer.commonComparisons order coordinate).1
  (mappedTime (located := located) (time := time))

/-- Preserve the independent SAME stored slope comparison on its identical physical restricted model. -/
@[expose] def slopeComparison (order coordinate : Fin 2) :
    ArithmeticComparison (answer.restrictedSlope order coordinate)
      (answer.numerics order coordinate).2.2 answer.sourceIdentity :=
  ArithmeticComparison.restrictAt
  (liftedCell ((next.requested.request.shape.val.1 :: next.requested.request.shape.val.2)[
    sourceIndex.val]'sourceIndex.isLt))
  (cell.restriction.cache (Specification.Table.slopeIndex order coordinate))
  (sameSheet (located := located)) (answer.commonComparisons order coordinate).2.2
  (mappedTime (located := located) (time := time))

end Sample

/-- A same-child row integral certificate retains actual base/output/slope samples and its computed finite factor.

The six original child tables and their nominal endpoints stay indices.
These are readbacks of a constructed original Quadratic certificate, not
assumptions about a desired row or aggregate Taylor inequality.
-/
@[expose] def Integral (order coordinate : Fin 2) :=
  { certificate : Quadratic.Basic.Certificate increment //
    certificate.base =
      (cell.restriction.model (Specification.Table.baseIndex order coordinate)).integralSample ∧
    certificate.output =
      ((next.requested.prepared.entry sourceIndex).preparation.cell.models.cell
        (Specification.Table.baseIndex order coordinate)).integralSample ∧
    certificate.slope =
      (cell.restriction.model (Specification.Table.slopeIndex order coordinate)).integralSample ∧
    certificate.factor =
      2 * (4 * (Variation.Point.Step.Joint.rowCeiling
        (source.prepared.entry located.block).preparation.cell.patch increment order coordinate +
          7 / 2 + 7 / 2 + 7 / 2)) *
        Norm.Basic.normSq
          ((next.requested.prepared.entry sourceIndex).preparation.cell.models.cell
            (Specification.Table.baseIndex order coordinate)).displacement }

/-- All four actual row integral results on this SAME retained Cell, in original order and coordinate indices. -/
@[expose] def IntegralBank := Data.Vector.DependentVector (fun order : Fin 2 =>
  Data.Vector.DependentVector (fun coordinate : Fin 2 => Integral cell order coordinate))

end ValueCell

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.Occurrence

end
