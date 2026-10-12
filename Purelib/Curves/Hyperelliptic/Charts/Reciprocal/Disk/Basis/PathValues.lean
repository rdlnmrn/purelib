module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Data.Rat

open Purelib.Geometry.Rectangle.Partition

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Certified homogeneous source increments on the retained root polygon. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests (BasisSourceRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Point (ReadingView)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests (Reading)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths (Segment Path TreeReadings)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (Tree
    Mesh ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh (BasisEndpoints)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources (Plans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.BasisTreeSources.Plans (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh.BasisEndpoints (Plan)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (midpoint_between)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : ParameterEdge} {cell :
    Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    RootModel cell}
  {parameter target sourceTarget : Coordinate} {floor sourceFloor :
    Nat}
  {covers : BasisSourceCovers parent}

variable {index readingStage minimum : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {comparison : Data regular cell}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

namespace PathValues

set_option genInjectivity false in
/-- Paired source/chart increments on the actual retained segment list. The source total and every increment error are
certified without normalizing coefficients or suppressing the polygon's area. -/
structure BasisPathValues (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (sourceTarget :
      InverseRootPolynomial.Coordinate)
    (segments : List (VertexPaths.Segment regular model sample target floor readingStage))
    (firstSource lastSource : InverseRootPolynomial.Gaussian) where
  /-- The actual paired original-source and chart increments in retained segment order. -/ pairs : List
    (InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian)
  /-- The chart components are exactly the increment readings of the original retained root segment list. -/ chart_eq :
    pairs.map Prod.snd = segments.map (fun segment =>
    polynomials.value coefficients segment.last.root.coordinate - polynomials.value coefficients
      segment.first.root.coordinate)
  /-- The cached complete source increment summary on the actual retained pairs. -/ source : IncrementArea.Summary
    (pairs.map Prod.fst)
  /-- The cached source increment total equals the retained last source value minus the first. -/ source_total :
    source.total = lastSource - firstSource
  /-- Every actual paired increment satisfies the coefficient-weighted source/chart squared-error bound. -/ errors : ∀
    pair ∈ pairs, Data.Gaussian.Norm.Basic.normSq (pair.1 - pair.2) ≤ 40 * sourceTarget *
    PreparedObservationCoercivity.coefficientNormSq coefficients

constructive_injectivity BasisPathValues

end PathValues

namespace PathValues.BasisPathValues

variable {first last : Coordinate}

/-- Build one paired source/chart increment from its original endpoint readings.

The retained source values and accuracy certificates certify the exact ordered
pair, its source total, and its coefficient-weighted squared error. -/
@[expose] def leaf (before : VertexRequests.Reading regular model sample first target floor readingStage)
    (after : VertexRequests.Reading regular model sample last target floor readingStage) (ordered : first ≤ last)
    (firstSource lastSource : InverseRootPolynomial.Gaussian)
    (firstClose : Data.Gaussian.Norm.Basic.normSq (firstSource - polynomials.value coefficients
      before.root.coordinate) ≤ 10 * sourceTarget * PreparedObservationCoercivity.coefficientNormSq coefficients)
    (lastClose : Data.Gaussian.Norm.Basic.normSq (lastSource - polynomials.value coefficients
      after.root.coordinate) ≤ 10 * sourceTarget * PreparedObservationCoercivity.coefficientNormSq coefficients) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues.BasisPathValues polynomials coefficients sourceTarget
      (Path.leaf before after ordered).segments firstSource lastSource := by
  let pair := (lastSource - firstSource,
    polynomials.value coefficients after.root.coordinate - polynomials.value coefficients before.root.coordinate)
  refine ⟨[pair], rfl, IncrementArea.Summary.build [pair.1], ?_, ?_⟩
  · change (lastSource - firstSource) + 0 = _
    ring1
  · intro value member
    have equal := Purelib.Data.List.Membership.mem_singleton.mp member
    subst value
    have bound := (Data.Gaussian.Norm.Bounds.normSq_sub_le_two (lastSource - polynomials.value coefficients
      after.root.coordinate)
      (firstSource - polynomials.value coefficients before.root.coordinate)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct lastClose
        firstClose) (by decide))
    change Data.Gaussian.Norm.Basic.normSq ((lastSource - firstSource) -
      (polynomials.value coefficients after.root.coordinate - polynomials.value coefficients before.root.coordinate)) ≤
        _
    rw [show (lastSource - firstSource) -
      (polynomials.value coefficients after.root.coordinate - polynomials.value coefficients before.root.coordinate) =
      (lastSource - polynomials.value coefficients after.root.coordinate) -
        (firstSource - polynomials.value coefficients before.root.coordinate) by ring1]
    exact bound.trans_eq (by ring1)

/-- Concatenate two retained paired increment certificates sharing one middle source value.

Both ordered pair lists and their cached source summaries are retained. Their
exact middle-source identity makes the complete source increments telescope. -/
@[expose] def append {leftSegments rightSegments : List (VertexPaths.Segment regular model sample target floor
  readingStage)}
    {firstSource middleSource lastSource : InverseRootPolynomial.Gaussian}
    (left : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues.BasisPathValues polynomials coefficients
      sourceTarget leftSegments firstSource middleSource)
    (right : Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues.BasisPathValues polynomials coefficients
      sourceTarget rightSegments middleSource lastSource) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues.BasisPathValues polynomials coefficients sourceTarget
      (leftSegments ++ rightSegments) firstSource lastSource := by
  let source : IncrementArea.Summary ((left.pairs ++ right.pairs).map Prod.fst) := by
    rw [Purelib.Data.List.Map.map_append]
    exact left.source.append right.source
  refine ⟨left.pairs ++ right.pairs, ?_, source, ?_, ?_⟩
  · rw [Purelib.Data.List.Map.map_append, left.chart_eq, right.chart_eq, Purelib.Data.List.Map.map_append]
  · rw [source.total_eq, Purelib.Data.List.Map.map_append, IncrementArea.sum_append,
      ← left.source.total_eq, ← right.source.total_eq, left.source_total, right.source_total]
    ring1
  · intro pair member
    rcases Purelib.Data.List.Membership.mem_append.mp member with before | after
    · exact left.errors pair before
    · exact right.errors pair after

end PathValues.BasisPathValues

namespace PathValues.BasisTreeSources.Plans

/-- Evaluate each source combination once per retained midpoint and share it between the two children. No root or
inverse approximation is repeated. -/
@[expose] def pathValues (bank : BasisSourceLocations.SampleBank covers index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    {depth : Nat} → {first last : InverseRootPolynomial.Coordinate} → (tree : VertexTree.Tree regular model target floor
      depth first last) →
    (sources : EndpointSchedule.BasisTreeSources covers sourceTarget sourceFloor tree) →
    (plans : BasisTreeSources.Plans polynomials minimum tree sources) → (readings : VertexPaths.TreeReadings sample
      readingStage tree) →
    Plans.Evaluation bank tree sources plans readings →
    (before : VertexRequests.Reading regular model sample first target floor readingStage) →
    (after : VertexRequests.Reading regular model sample last target floor readingStage) → (ordered : first ≤ last) →
    (firstSource lastSource : InverseRootPolynomial.Gaussian) →
    Data.Gaussian.Norm.Basic.normSq (firstSource - polynomials.value coefficients before.root.coordinate) ≤ 10
      * sourceTarget * PreparedObservationCoercivity.coefficientNormSq coefficients →
    Data.Gaussian.Norm.Basic.normSq (lastSource - polynomials.value coefficients after.root.coordinate) ≤ 10 *
      sourceTarget * PreparedObservationCoercivity.coefficientNormSq coefficients →
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues.BasisPathValues polynomials coefficients sourceTarget
      (TreeReadings.path readings before after ordered).segments firstSource lastSource
  | _, _, _, .leaf _ _, _, _, _, _, before, after, ordered, firstSource, lastSource, firstClose, lastClose =>
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues.BasisPathValues.leaf before after ordered firstSource
        lastSource firstClose lastClose
  | _, _, _, .node _ left right, sources, plans, readings, evaluated, before, after, ordered,
      firstSource, lastSource, firstClose, lastClose =>
      let middle := FiniteSum.Fin.sumFin (fun row => coefficients row * evaluated.1.evaluated.sources row)
      let middleClose := evaluated.1.evaluated.accurate coefficients
      let between := PreparedBoxPartitions.midpoint_between ordered
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues.BasisPathValues.append
        (pathValues bank
          coefficients left sources.2.1 plans.2.1 readings.2.1 evaluated.2.1
          before readings.1.reading between.1 firstSource middle firstClose middleClose)
        (pathValues bank
          coefficients right sources.2.2 plans.2.2 readings.2.2 evaluated.2.2
          readings.1.reading after between.2 middle lastSource middleClose lastClose)

end PathValues.BasisTreeSources.Plans
section Mesh.BasisEndpoints.Plan

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.EndpointSchedule.Mesh.BasisEndpoints.Plan
    (Evaluation)

variable {depth : Nat} {mesh : Mesh regular model depth
  target floor}
  {charts : ChartMesh mesh capSample minimum}
  {sources : BasisEndpoints mesh covers
    sourceTarget sourceFloor}
  {plan : Plan sources
    charts polynomials}
  {bank : BasisSourceLocations.SampleBank
    covers index}
  {original : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths.ChartMesh.Evaluation charts sample
    readingStage}

set_option genInjectivity false in
/-- The extreme source combinations and complete increment certificate, owned by the original acquired mesh path. -/
structure PathValues (evaluated : Evaluation plan bank original)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) where
  /-- The cached coefficient-weighted source value at the original acquired first endpoint. -/ firstSource :
    InverseRootPolynomial.Gaussian
  /-- The first source cache reads the actual retained first endpoint comparison sources. -/ first_eq : firstSource =
    FiniteSum.Fin.sumFin (fun row => coefficients row * evaluated.first.evaluated.sources row)
  /-- The cached coefficient-weighted source value at the original acquired last endpoint. -/ lastSource :
    InverseRootPolynomial.Gaussian
  /-- The last source cache reads the actual retained last endpoint comparison sources. -/ last_eq : lastSource =
    FiniteSum.Fin.sumFin (fun row => coefficients row * evaluated.last.evaluated.sources row)
  /-- The complete paired increment certificate on the exact original acquired mesh path. -/ values :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues.BasisPathValues polynomials coefficients sourceTarget
    original.path.segments firstSource lastSource

constructive_injectivity PathValues

namespace PathValues.Mesh.BasisEndpoints.Plan.Evaluation

/-- Read both original extreme source combinations and recursively certify the exact acquired mesh path, sharing each
retained midpoint evaluation. -/
@[expose] def pathValues (evaluated : Evaluation plan bank original)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
      PathValues evaluated
      coefficients := by
  let firstSource := FiniteSum.Fin.sumFin (fun row => coefficients row * evaluated.first.evaluated.sources row)
  let lastSource := FiniteSum.Fin.sumFin (fun row => coefficients row * evaluated.last.evaluated.sources row)
  refine ⟨firstSource, rfl, lastSource, rfl, ?_⟩
  rw [original.path_eq]
  exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues.BasisTreeSources.Plans.pathValues bank coefficients
    mesh.tree sources.tree plan.tree original.readings
    evaluated.tree original.first original.last cell.ordered.le firstSource lastSource
    (evaluated.first.evaluated.accurate coefficients) (evaluated.last.evaluated.accurate coefficients)

end PathValues.Mesh.BasisEndpoints.Plan.Evaluation

end Mesh.BasisEndpoints.Plan
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis
