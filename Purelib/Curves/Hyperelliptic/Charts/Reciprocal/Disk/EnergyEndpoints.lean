module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Integration.Path.IncrementRestoration
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedDisk
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Data.Rat

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartRefinementArea.AreaRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy

open Purelib.Integration.Path

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation

public section

/-!
# Energy boundary certificates for the retained endpoint readings

The certificates refer to cached potentials and the original root readings.
Their proofs recover the first and last cells of the existing energy spine;
no endpoint, polynomial value, or radial path is evaluated again.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ReciprocalDiskVertices

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.IncrementRestoration (potential)
open Purelib.Riemann.RootContinuation.RootRadialGeometry (radialArea)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {index : Nat} {box : Purelib.Geometry.Rational.Box}

open Purelib.Integration.Path.IncrementRestoration in
/-- An actual retained energy endpoint's radial potential, primitive offset and padded-domain certificate.

The original polynomial sample, root coordinate and cached reading determine the potential at the retained radial depth.
-/
structure EnergyEndpoint (sample : Primitives.Sample cap differential index box)
    (regular : RegularBounds.Data cap) (depth : Nat) (target : InverseRootPolynomial.Coordinate)
    (root value potential : InverseRootPolynomial.Gaussian) : Prop where
  /-- The retained potential is exactly the radial area corrected by the original polynomial value and cached endpoint
    reading. -/ potential_eq : potential = IncrementRestoration.potential
    (RootRadialGeometry.radialArea sample.primitive.value.eval depth root) (sample.primitive.value.eval root) value
  /-- The actual polynomial-to-reading squared-norm offset meets the retained target. -/ offset :
    Data.Gaussian.Norm.Basic.normSq (sample.primitive.value.eval root - value) ≤ target
  /-- The actual polynomial-to-reading squared-norm offset is at most one. -/ small :
    Data.Gaussian.Norm.Basic.normSq (sample.primitive.value.eval root - value) ≤ 1
  /-- The retained root square lies in the original padded reciprocal domain. -/ inside : regular.padded.Contains (root
    * root)

namespace RestoredEnergyBlock

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings.Evaluation (EndpointPair)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy.AreaRequest.Evaluation (RequestedEnergy)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs (PairRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest (AreaRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree (ChartMesh)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyCells (ofEvaluation)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)

variable {count : Nat} {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve
  differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {owners :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.OwnedEndpoints regular cell}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell} {target energyTarget
    joining : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor energyFloor pairFloor : Nat}
  {depth stage minimum energyDepth : Nat} {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample
    cap differential index box}
  {source : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
    {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest.AreaRequest comparison owners target
    floor}
  {charts : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree.ChartMesh request.mesh sample minimum}
  {original : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells.ComparedCell comparison source sample
    depth}
  {pairRequest : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest owners.bounds joining
    pairFloor}

/-- The actual first retained energy-block endpoint satisfies the original radial-potential and offset certificates. -/
theorem first_endpoint (evaluated : AreaRequest.Evaluation charts original stage)
    (energy : Evaluation.RequestedEnergy evaluated energyTarget energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (sameDepth : energy.request.depth = energyDepth)
    (pair : Evaluation.EndpointPair evaluated pairRequest) (nonnegative : 0 ≤ joining) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ReciprocalDiskVertices.EnergyEndpoint sample regular
      energyDepth target pair.pair.firstReading.coordinate pair.pair.firstValue
      (RestoredEnergyCells.ofEvaluation evaluated energy branch sameDepth pair nonnegative).firstPotential := by
  let block := RestoredEnergyCells.ofEvaluation evaluated energy branch sameDepth pair nonnegative
  rw [pair.first_coordinate]
  change Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ReciprocalDiskVertices.EnergyEndpoint sample
    regular energyDepth target block.raw.firstRoot block.firstValue block.firstPotential
  refine ⟨?_, ?_, ?_, Evaluation.square_inside request branch evaluated.vertices.first⟩
  · rw [block.first_potential, block.raw.first_radial, block.raw.first_value]
  · rw [← block.raw.first_value]; exact block.first_offset
  · rw [← block.raw.first_value]; exact block.first_small

/-- The actual terminal retained energy-block endpoint satisfies the original radial-potential and offset certificates.
-/
theorem last_endpoint (evaluated : AreaRequest.Evaluation charts original stage)
    (energy : Evaluation.RequestedEnergy evaluated energyTarget energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (sameDepth : energy.request.depth = energyDepth)
    (pair : Evaluation.EndpointPair evaluated pairRequest) (nonnegative : 0 ≤ joining) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ReciprocalDiskVertices.EnergyEndpoint sample regular
      energyDepth target pair.pair.lastReading.coordinate pair.pair.lastValue
      (RestoredEnergyCells.ofEvaluation evaluated energy branch sameDepth pair nonnegative).lastPotential := by
  let block := RestoredEnergyCells.ofEvaluation evaluated energy branch sameDepth pair nonnegative
  rw [pair.last_coordinate]
  change Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ReciprocalDiskVertices.EnergyEndpoint sample
    regular energyDepth target block.raw.lastRoot block.lastValue block.lastPotential
  refine ⟨?_, ?_, ?_, Evaluation.square_inside request branch evaluated.vertices.last⟩
  · rw [block.last_potential, block.raw.last_radial, block.raw.last_value]
  · rw [← block.raw.last_value]; exact block.last_offset
  · rw [← block.raw.last_value]; exact block.last_small

end RestoredEnergyBlock
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ReciprocalDiskVertices

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ChartPlans

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ReciprocalDiskVertices (EnergyEndpoint)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank (Bank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners (Owners)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths (ComparedCells)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests (ChartRequests ChartPlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans (EvaluationData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints (EndpointRequests)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests (EnergyData)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy (RequestedEnergy)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks (RestoredEnergyBlock)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy.EnergyData (restoredBlocks)

variable {genus count index depth readingIndex floor minimum : Nat} {curve :
  Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {collar :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {parent :
    Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {source :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives.SourcePrimitive data index}
  {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {target energyTarget tolerance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {energyFloor
    energyDepth pairFloor : Nat}

namespace EnergyData

variable (branch : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
  (nonnegative : 0 ≤ tolerance / 4)
  {edges : List Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {bank :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} {owners :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank}
  {requests : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners}
    (plans : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum
    requests)
  (cells : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank)
    (evaluated : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData
    readingIndex plans cells)
  (energies : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests.EnergyData energyTarget
    energyFloor energyDepth plans cells evaluated)
  (pairs : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests (tolerance / 4)
    pairFloor owners)
  (modelLater : pairs.maximum ≤ index) (readingLater : pairs.readingMaximum ≤ readingIndex) (nonempty : edges ≠ [])

include nonempty in
/-- The actual first retained energy-block endpoint satisfies the original radial-potential and offset certificates. -/
theorem first_endpoint :
    let readings := plans.endpointReadings cells evaluated pairs modelLater readingLater
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ReciprocalDiskVertices.EnergyEndpoint capSample regular
      energyDepth target (EndpointRequests.firstCoordinate pairs cells readings)
      (EndpointRequests.firstValue pairs cells readings)
      (RestoredEnergyBlock.initial (EnergyData.restoredBlocks branch nonnegative plans cells evaluated energies pairs
        modelLater readingLater)).2 := by
  cases plans with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
      cases cells with
      | cons cell cells =>
          cases pairs with
          | cons pair rest =>
              exact
                ReciprocalDiskVertices.RestoredEnergyBlock.first_endpoint
                evaluated.1 energies.1.val branch energies.1.property _ nonnegative

include nonempty in
/-- The actual terminal retained energy-block endpoint satisfies the original radial-potential and offset certificates.
-/
theorem last_endpoint (previousValue previousRoot previousPotential : InverseRootPolynomial.Gaussian) :
    let readings := plans.endpointReadings cells evaluated pairs modelLater readingLater
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ReciprocalDiskVertices.EnergyEndpoint capSample regular
      energyDepth target (EndpointRequests.lastCoordinate pairs cells readings previousRoot)
      (EndpointRequests.lastValue pairs cells readings previousValue)
      (RestoredEnergyBlock.terminalPotential (EnergyData.restoredBlocks branch nonnegative plans cells evaluated
        energies pairs modelLater readingLater) previousPotential) := by
  induction plans generalizing previousValue previousRoot previousPotential with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail ih =>
      cases cells with
      | cons cell cells =>
          cases pairs with
          | cons pair rest =>
              cases tail with
              | nil =>
                  cases cells; cases rest
                  exact
                    ReciprocalDiskVertices.RestoredEnergyBlock.last_endpoint
                    evaluated.1 energies.1.val branch energies.1.property _ nonnegative
              | cons next tail =>
                  exact ih cells evaluated.2 energies.2 rest ((Data.Nat.Order.le_max_right _ _).trans modelLater)
                    ((Data.Nat.Order.le_max_right _ _).trans readingLater) (by intro equal; cases equal) _ _ _

end EnergyData

namespace RequestedEnergy

variable {edges : List Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {bank :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges} {owners :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners.Owners bank}
  {requests : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartRequests target floor owners}
    {plans : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans capSample minimum
    requests}
  {cells : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths.ComparedCells source capSample depth bank}
    {evaluated : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests.ChartPlans.EvaluationData
    readingIndex plans cells}
  {pairs : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints.EndpointRequests (tolerance / 4)
    pairFloor owners}
  (energy : RequestedEnergy plans cells evaluated pairs energyTarget energyFloor)
  (branch : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) (nonempty :
    edges ≠ [])

include branch nonempty in
/-- The actual first retained energy-block endpoint satisfies the original radial-potential and offset certificates. -/
theorem first_endpoint :
    let readings := plans.endpointReadings cells evaluated pairs energy.model_later energy.reading_later
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ReciprocalDiskVertices.EnergyEndpoint capSample regular
      energy.depth target (EndpointRequests.firstCoordinate pairs cells readings) energy.firstValue
      energy.firstPotential := by
  rw [energy.first_value, show energy.firstPotential = (RestoredEnergyBlock.initial energy.blocks).2 from congrArg
    Prod.snd energy.first_eq,
    energy.blocks_eq branch]
  exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ChartPlans.EnergyData.first_endpoint branch
    energy.join_nonnegative plans cells evaluated energy.energies pairs energy.model_later energy.reading_later nonempty

include branch nonempty in
/-- The actual terminal retained energy-block endpoint satisfies the original radial-potential and offset certificates.
-/
theorem last_endpoint (previousValue previousRoot : InverseRootPolynomial.Gaussian) :
    let readings := plans.endpointReadings cells evaluated pairs energy.model_later energy.reading_later
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ReciprocalDiskVertices.EnergyEndpoint capSample regular
      energy.depth target (EndpointRequests.lastCoordinate pairs cells readings previousRoot)
      (EndpointRequests.lastValue pairs cells readings previousValue)
      (RestoredEnergyBlock.terminalPotential energy.blocks energy.firstPotential) := by
  rw [energy.blocks_eq branch]
  exact Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ChartPlans.EnergyData.last_endpoint branch
    energy.join_nonnegative plans cells evaluated energy.energies pairs energy.model_later energy.reading_later nonempty
    previousValue previousRoot energy.firstPotential

end RequestedEnergy
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndpoints.ChartPlans
