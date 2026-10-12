module
import Purelib.Data.List.Map
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedVertices
import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitivePrefixes
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedIncrements
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive
public import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitiveArea
import Purelib.RootIsolation.State.Raw
import Purelib.Topology.Polygon.Stokes

import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveTotals
public import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveIncrementArea
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Integration.PreparedPairedModelAccuracy
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedModelAccuracy

public section

/-! The count-cancelled increment area is the actual indexed local primitive area. -/
namespace Purelib.Riemann.Paths.PreparedPrimitivePaths

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Summing original mapped child increments equals the primitive increment sum of their exact models. -/
private theorem mapped_increment_sum (primitive : Basic.Canonical → Basic.Canonical) (children : List (CenteredEdge
  curve differential)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (children.map (fun child => primitive (child.edge.point 1) - primitive
      (child.edge.point 0))) =
      Primitive.incrementSum primitive (children.map CenteredEdge.model) := by
  induction children with
  | nil => rfl
  | cons child rest ih => exact congrArg (_ + ·) ih

open Purelib.Data.Gaussian in
/-- Read both original primitive increments at each retained child in order. -/
@[expose] def pairedPrimitiveIncrements (first second : Basic.Canonical → Basic.Canonical) (children : List
  (CenteredEdge curve differential)) :
    List PrimitivePoint := children.map fun child =>
      ⟨first (child.edge.point 1) - first (child.edge.point 0),
        second (child.edge.point 1) - second (child.edge.point 0)⟩

open Purelib.Data.Gaussian
open Purelib.Geometry.Path.Gaussian
open Purelib.Integration.Path
/-- The original paired prefix total equals both primitive endpoint differences.

The same retained direct-chain prefix point supplies both coordinates, preserving the original start and child order. -/
theorem pairedPrimitive_prefix (first second : Basic.Canonical → Basic.Canonical)
    {children : List (CenteredEdge curve differential)} {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : DirectPathChain children (start := start) (finish := finish)) (length : Nat) :
    PairedIncrementArea.total ((pairedPrimitiveIncrements first second children).take length) =
      (⟨first (prefixPoint start.coordinate children length) - first start.coordinate,
        second (prefixPoint start.coordinate children length) - second start.coordinate⟩ : PrimitivePoint) := by
  have scalar (primitive : Basic.Canonical → Basic.Canonical) := prefix_incrementSum primitive chain length
  have firstEq := scalar first
  have secondEq := scalar second
  simp only [← Data.List.Map.map_take, ← mapped_increment_sum, -eq_self, -iff_self] at firstEq secondEq
  apply congrArg₂ PrimitivePoint.mk
  · simpa only [pairedPrimitiveIncrements, PairedIncrementArea.total, ← Data.List.Map.map_take,
      Data.List.Map.map_map, Function.comp_def, -eq_self, -iff_self] using firstEq
  · simpa only [pairedPrimitiveIncrements, PairedIncrementArea.total, ← Data.List.Map.map_take,
      Data.List.Map.map_map, Function.comp_def, -eq_self, -iff_self] using secondEq

/-- The original paired total telescopes to both full-chain endpoint differences. -/
theorem pairedPrimitive_total (first second : Basic.Canonical → Basic.Canonical)
    {children : List (CenteredEdge curve differential)} {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : DirectPathChain children (start := start) (finish := finish)) :
    PairedIncrementArea.total (pairedPrimitiveIncrements first second children) =
      (⟨first finish.coordinate - first start.coordinate,
        second finish.coordinate - second start.coordinate⟩ : PrimitivePoint) := by
  apply congrArg₂ PrimitivePoint.mk
  · simp only [pairedPrimitiveIncrements, Data.List.Map.map_map, Function.comp_def, -eq_self, -iff_self]
    rw [mapped_increment_sum, incrementSum_eq _ chain]
  · simp only [pairedPrimitiveIncrements, Data.List.Map.map_map, Function.comp_def, -eq_self, -iff_self]
    rw [mapped_increment_sum, incrementSum_eq _ chain]

end Purelib.Riemann.Paths.PreparedPrimitivePaths

namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent.PairedBoundaryParent

open Purelib
open Purelib.Data.Rat
open Purelib.RootIsolation.Newton.Band
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent (PairedBoundaryParent)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank (PairedBoundaryParents)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.NewtonBandBounds (PairedParentPrimitives)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request (PrimitiveComparison)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
variable {genus count index : Nat} {curve : HyperellipticCurve genus} {differential
  other : Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target} {parent : CenteredEdge
    curve differential}

open Purelib.Integration.Path in
open Purelib.Riemann.Paths in
/-- The original primitive projection's prefix total reads back its retained paired primitive vertex. -/
theorem primitiveIncrementPairs_prefix (paired : PairedBoundaryParent request parent other)
    (first : PrimitiveComparison paired.refinement.first count index)
    (second : PrimitiveComparison paired.refinement.second count index) (length : Nat) :
    PairedIncrementArea.total (((paired.primitiveIncrementPairs first second).map Prod.fst).take length) =
      paired.primitiveVertex first second length := by
  have bounded := PreparedPrimitivePaths.pairedPrimitive_prefix first.2.1.primitive.value.eval
    second.2.1.primitive.value.eval paired.refinement.first.block.chain length
  simpa only [primitiveIncrementPairs, Data.List.Map.map_map, Function.comp_def, primitiveVertex,
    PreparedPrimitivePaths.pairedPrimitiveIncrements, parent.edge.point_zero, -eq_self, -iff_self] using bounded

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Riemann.RootContinuation in
open Purelib.Topology.Polygon in
/-- The original primitive increment area equals the area of its retained indexed prefix vertices.

Exact list lengths and pointwise prefix identities preserve the original oriented finite-area sum. -/
theorem primitiveIncrementPairs_area (paired : PairedBoundaryParent request parent other)
    (first : PrimitiveComparison paired.refinement.first count index)
    (second : PrimitiveComparison paired.refinement.second count index) :
    PairedIncrementArea.area ((paired.primitiveIncrementPairs first second).map Prod.fst) =
      CenteredBilinearPath.area
        (fun vertex : Fin ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length + 1) =>
          paired.primitiveVertex first second vertex.val) := by
  have lengthEq : ((paired.primitiveIncrementPairs first second).map Prod.fst).length =
    (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length := by
    simp only [primitiveIncrementPairs,
      PreparedNewtonPairedIncrements.PairedBoundaryParent.increments,
      Data.List.Map.length_map, -eq_self, -iff_self]
    rfl
  have readback := PairedIncrementArea.indexed_prefix_area
    ((paired.primitiveIncrementPairs first second).map Prod.fst) PrimitivePoint.zero
  rw [lengthEq] at readback
  have zeroAdd (value : PrimitivePoint) : PrimitivePoint.zero.add value = value := by
    cases value
    simp only [PrimitivePoint.zero, PrimitivePoint.add, Basic.zero_add, -eq_self, -iff_self]
    rfl
  have pointwise : CenteredBilinearPath.area
      (fun vertex : Fin ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length + 1) =>
        PrimitivePoint.zero.add
        (PairedIncrementArea.total
          (((paired.primitiveIncrementPairs first second).map Prod.fst).take vertex.val))) =
      CenteredBilinearPath.area
        (fun vertex : Fin ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length + 1) =>
          paired.primitiveVertex first second vertex.val) := by
    apply FiniteSum.Fin.sumFin_congr
    intro edge
    apply congrArg₂ Stokes.edgeArea
    · exact (congrArg PrimitivePoint.zero.add
        (paired.primitiveIncrementPairs_prefix first second edge.castSucc.val)).trans (zeroAdd _)
    · exact (congrArg PrimitivePoint.zero.add
        (paired.primitiveIncrementPairs_prefix first second edge.succ.val)).trans (zeroAdd _)
  exact (PairedIncrementArea.area_eq_trace _).trans (readback.symm.trans pointwise)

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- The original primitive vertex area satisfies the retained increment-area comparison bound.

The same maximum error density, summed numerical density and parent movement remain in the exact factor-16 payment. -/
theorem primitive_vertex_area_error_le (paired : PairedBoundaryParent request parent other)
    (otherProfile : DifferentialProfile profile other.exponent)
    (first : PrimitiveComparison paired.refinement.first count index)
    (second : PrimitiveComparison paired.refinement.second count index) :
    let error := max 0 (max first.errorDensity second.errorDensity)
    let density := PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
      PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error
    Data.Gaussian.Norm.Basic.normSq
      (CenteredBilinearPath.area
          (fun vertex : Fin ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length + 1) =>
            paired.primitiveVertex first second vertex.val) -
        PairedIncrementArea.traceArea PrimitivePoint.zero
          (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired)) ≤
      16 * error * (2 * (density + error)) * (PreparedPrimitiveRequests.movement parent)^2 := by
  have bounded := paired.primitive_increment_area_error_le otherProfile first second
  rw [paired.primitiveIncrementPairs_area first second, PairedIncrementArea.area_eq_trace] at bounded
  exact bounded

open Purelib.Integration.Path in
open Purelib.Riemann.Paths in
/-- The original primitive pair projection totals to its two stored comparison increments. -/
theorem primitiveIncrementPairs_total (paired : PairedBoundaryParent request parent other)
    (first : PrimitiveComparison paired.refinement.first count index)
    (second : PrimitiveComparison paired.refinement.second count index) :
    PairedIncrementArea.total ((paired.primitiveIncrementPairs first second).map Prod.fst) =
      (⟨first.2.2.increment, second.2.2.increment⟩ : PrimitivePoint) := by
  rw [first.2.2.increment_eq, second.2.2.increment_eq]
  change PairedIncrementArea.total _ =
    (⟨first.2.1.primitive.value.eval (parent.edge.point 1) - first.2.1.primitive.value.eval (parent.edge.point 0),
      second.2.1.primitive.value.eval (parent.edge.point 1) - second.2.1.primitive.value.eval (parent.edge.point 0)⟩ :
        PrimitivePoint)
  have exactTotal := PreparedPrimitivePaths.pairedPrimitive_total first.2.1.primitive.value.eval
    second.2.1.primitive.value.eval paired.refinement.first.block.chain
  simpa only [primitiveIncrementPairs, Data.List.Map.map_map, Function.comp_def,
    PreparedPrimitivePaths.pairedPrimitiveIncrements, parent.edge.point_zero, parent.edge.point_one, -eq_self,
      -iff_self] using exactTotal

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent.PairedBoundaryParent

namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.NewtonBandBounds.PairedParentPrimitives

open Purelib
open Purelib.Data.Rat
open Purelib.RootIsolation.Newton.Band
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent (PairedBoundaryParent)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank (PairedBoundaryParents)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.NewtonBandBounds (PairedParentPrimitives)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
variable {genus count index : Nat} {curve : HyperellipticCurve genus} {differential
  other : Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target}

/-- Read the original primitive increment blocks in retained parent order. -/
@[expose] def primitiveBlocks : {parents : List (CenteredEdge curve differential)} →
    {bank : PairedBoundaryParents request other parents} → PairedParentPrimitives count bank → List (List
      PrimitivePoint)
  | _, _, .nil => []
  | _, .cons head _, .cons first second rest =>
      (head.primitiveIncrementPairs first second).map Prod.fst :: rest.primitiveBlocks

/-- Read the original stored first/second increment pairs in retained parent order. -/
@[expose] def primitiveTotals : {parents : List (CenteredEdge curve differential)} →
    {bank : PairedBoundaryParents request other parents} → PairedParentPrimitives count bank → List PrimitivePoint
  | _, _, .nil => []
  | _, _, .cons first second rest => ⟨first.2.2.increment, second.2.2.increment⟩ :: rest.primitiveTotals

open Purelib.Integration.Path in
/-- The totals of the original primitive blocks read back the exact retained increment pairs. -/
theorem primitiveBlocks_totals {parents : List (CenteredEdge curve differential)}
    {bank : PairedBoundaryParents request other parents} (values : PairedParentPrimitives count bank) :
    values.primitiveBlocks.map PairedIncrementArea.total = values.primitiveTotals := by
  induction values with
  | nil => rfl
  | cons first second rest ih =>
    simp only [primitiveBlocks, primitiveTotals, List.map_cons, PairedBoundaryParent.primitiveIncrementPairs_total, ih,
      -eq_self, -iff_self]
    rfl

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- The original flattened primitive area splits into internal block areas and the polygon of block totals.

Both terms use the actual retained ordered blocks and their exact total readback. -/
theorem primitiveBlocks_area {parents : List (CenteredEdge curve differential)}
    {bank : PairedBoundaryParents request other parents} (values : PairedParentPrimitives count bank) :
    PairedIncrementArea.area values.primitiveBlocks.flatten =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.primitiveBlocks.map PairedIncrementArea.area) +
        PairedIncrementArea.area values.primitiveTotals := by
  rw [PairedAreaBlocks.area_flatten, values.primitiveBlocks_totals]

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.NewtonBandBounds.PairedParentPrimitives
