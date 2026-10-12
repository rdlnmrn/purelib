module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyBlocks
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementAreaReplacement
import Purelib.Integration.Path.IncrementRestoration
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-!
# Restored energy blocks from the actual chart and endpoint readings

Owner transport reuses the original chart roots. The literal path is the
existing corrected replacement, including the merged incoming connector.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyCells

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {owners :
    Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular cell}
  {comparison : Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell} {target energyTarget joining :
    Normalization.InverseRootPolynomial.Coordinate} {floor energyFloor pairFloor : Nat}
  {index depth stage minimum energyDepth : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {source :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest comparison owners target floor} {charts :
    Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartMesh request.mesh sample minimum}
  {original : Hyperelliptic.Charts.Reciprocal.Disk.ParentCells.ComparedCell comparison source sample depth}
  {pairRequest : Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest owners.bounds joining pairFloor}

/-- Restore the actual chart energy block with its original source and endpoint readings.

Reuse the retained radial roots, keep both endpoint corrections and preserve the literal replacement path. -/
@[expose] def ofEvaluation (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation
  charts original stage)
    (energy : Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.RequestedEnergy evaluated
      energyTarget energyFloor)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (sameDepth :
      energy.request.depth = energyDepth)
    (pair : Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Evaluation.EndpointPair evaluated pairRequest)
      (joinNonnegative : 0 ≤ joining) :
    Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock sample energyDepth target energyTarget
      joining := open Purelib.Data.Rat in by
  let raw := Hyperelliptic.Charts.Reciprocal.Disk.EnergyBlocks.EnergyBlock.build evaluated energy branch sameDepth
  have firstSource : original.sample.firstValue = evaluated.vertices.first.sourceValue := by
    rw [original.sample.firstValue_eq, evaluated.vertices.first.source_eq]
  have lastSource : original.sample.lastValue = evaluated.vertices.last.sourceValue := by
    rw [original.sample.lastValue_eq, evaluated.vertices.last.source_eq]
  have firstOffset : Data.Gaussian.Norm.Basic.normSq (raw.firstValue - pair.pair.firstValue) < request.tolerance :=
    by
    change Data.Gaussian.Norm.Basic.normSq (evaluated.vertices.first.chartValue - pair.pair.firstValue) < _
    rw [pair.first_value, show evaluated.vertices.first.chartValue - evaluated.vertices.first.root.value =
      -(evaluated.vertices.first.root.value - evaluated.vertices.first.chartValue) by ring1,
        Gaussian.Norm.Basic.normSq_neg]
    exact evaluated.vertices.first.chart_accurate
  have lastOffset : Data.Gaussian.Norm.Basic.normSq (raw.lastValue - pair.pair.lastValue) < request.tolerance := by
    change Data.Gaussian.Norm.Basic.normSq (evaluated.vertices.last.chartValue - pair.pair.lastValue) < _
    rw [pair.last_value, show evaluated.vertices.last.chartValue - evaluated.vertices.last.root.value =
      -(evaluated.vertices.last.root.value - evaluated.vertices.last.chartValue) by ring1,
        Gaussian.Norm.Basic.normSq_neg]
    exact evaluated.vertices.last.chart_accurate
  have firstChart : Data.Gaussian.Norm.Basic.normSq (raw.firstValue - original.sample.firstValue) ≤ 4 * target := by
    change Data.Gaussian.Norm.Basic.normSq (evaluated.vertices.first.chartValue - original.sample.firstValue) ≤ _
    rw [firstSource, show evaluated.vertices.first.chartValue - evaluated.vertices.first.sourceValue =
      -(evaluated.vertices.first.sourceValue - evaluated.vertices.first.chartValue) by ring1,
        Gaussian.Norm.Basic.normSq_neg]
    exact evaluated.vertices.first.accurate.le.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells.tolerance_le_target request) (by decide))
  have lastChart : Data.Gaussian.Norm.Basic.normSq (original.sample.lastValue - raw.lastValue) ≤ 4 * target := by
    rw [lastSource]
    exact evaluated.vertices.last.accurate.le.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells.tolerance_le_target request) (by decide))
  have lastOld : Data.Gaussian.Norm.Basic.normSq (pair.pair.lastValue - original.sample.lastValue) ≤ joining := by
    rw [show pair.pair.lastValue - original.sample.lastValue = -(original.sample.lastValue - pair.pair.lastValue) by
      ring1, Gaussian.Norm.Basic.normSq_neg]
    exact pair.pair.last_close.le.trans (Fraction.Order.Field.divide_le_self joinNonnegative (by
        decide : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4))
  exact ⟨raw, original.sample.firstValue, original.sample.lastValue, pair.pair.firstValue, pair.pair.lastValue,
    pair.pair.first_close.le.trans (Fraction.Order.Field.divide_le_self joinNonnegative (by
        decide : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)), lastOld, firstChart, lastChart,
    firstOffset.le.trans (Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells.tolerance_le_target request),
      lastOffset.le.trans (Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells.tolerance_le_target request),
    firstOffset.le.trans request.small, lastOffset.le.trans request.small,
    Path.IncrementRestoration.potential raw.firstRadial raw.firstValue pair.pair.firstValue,
      Path.IncrementRestoration.potential raw.lastRadial raw.lastValue pair.pair.lastValue, rfl, rfl,
    Path.IncrementAreaReplacement.bracket raw.summary (raw.firstValue - original.sample.firstValue)
      (original.sample.lastValue - raw.lastValue)⟩

/-- Readback is to the existing literal replacement path, including the
source vertices and the merged incoming connector. -/
theorem ofEvaluation_path (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest.Evaluation
  charts original stage)
    (energy : Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation.RequestedEnergy evaluated
      energyTarget energyFloor)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (sameDepth :
      energy.request.depth = energyDepth)
    (pair : Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Evaluation.EndpointPair evaluated pairRequest)
      (joinNonnegative : 0 ≤ joining) (previous : Normalization.InverseRootPolynomial.Gaussian) :
    (Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyCells.ofEvaluation evaluated energy branch sameDepth pair
      joinNonnegative).path previous =
      let old := Hyperelliptic.Charts.Reciprocal.Disk.CorrectedCells.CorrectedCell.build original pair.pair
        (pair.pair.firstValue - previous)
      let restored := Hyperelliptic.Charts.Reciprocal.Disk.ChartCorrectedCells.Restored.build evaluated
      old.first :: ((restored.first :: (evaluated.vertices.path.chartPath ++ [restored.last])) ++ [old.last]) := by
  have firstSource : original.sample.firstValue = evaluated.vertices.first.sourceValue := by
    rw [original.sample.firstValue_eq, evaluated.vertices.first.source_eq]
  have lastSource : original.sample.lastValue = evaluated.vertices.last.sourceValue := by
    rw [original.sample.lastValue_eq, evaluated.vertices.last.source_eq]
  change (original.sample.firstValue - previous) :: (((evaluated.vertices.first.chartValue - original.sample.firstValue)
    ::
      (evaluated.vertices.path.chartPath ++ [original.sample.lastValue - evaluated.vertices.last.chartValue])) ++
        [pair.pair.lastValue - original.sample.lastValue]) =
    (original.sample.firstValue - pair.pair.firstValue + (pair.pair.firstValue - previous)) ::
      (((evaluated.vertices.first.chartValue - evaluated.vertices.first.sourceValue) ::
        (evaluated.vertices.path.chartPath ++ [evaluated.vertices.last.sourceValue -
          evaluated.vertices.last.chartValue])) ++ [pair.pair.lastValue - original.sample.lastValue])
  rw [show original.sample.firstValue - pair.pair.firstValue + (pair.pair.firstValue - previous) =
    original.sample.firstValue - previous by ring1,
    firstSource, lastSource]

/-- Shifted potentials at adjacent retained endpoints obey the same finite
join comparison, with an explicit allowance for their chart offsets. -/
theorem join_bound (first last : Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock sample
  energyDepth target energyTarget joining)
    (joinSmall : joining ≤ 1)
    (base : Data.Gaussian.Norm.Basic.normSq (last.raw.firstRadial - first.raw.lastRadial - Path.BoundaryRibbon.area
      first.raw.lastValue last.raw.firstValue) ≤ joining)
    (gap : Data.Gaussian.Norm.Basic.normSq (last.firstValue - first.lastValue) ≤ joining) :
    Data.Gaussian.Norm.Basic.normSq (last.joinError first.lastValue first.lastPotential) ≤ 80 * target + 2 * joining
      := by
  rw [Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks.RestoredEnergyBlock.joinError, last.first_potential,
    first.last_potential]
  exact Path.IncrementRestoration.potential_join_bound base first.last_offset last.first_offset last.first_small
    (gap.trans joinSmall)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyCells
