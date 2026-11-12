module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEndpointReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergyJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergy
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyCells
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcCoarsening
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentCells
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexTree
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedConstantModels

open Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib

open Purelib.Data.Rat

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-!
# The complete parent energy on the existing restored replacement path

Every block and endpoint comes from the original chart and endpoint spines.
The path readback is literal, so its area is the area already consumed by
the source comparison. Shifted endpoint potentials remain for later gluing.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count index depth readingIndex floor minimum : Nat} {curve : Basic.HyperellipticCurve
  genus}
  {differential : Differentials.Basic.Differential genus} {collar :
    ReciprocalExteriorCollar.Data curve}
  {cap : ReciprocalInnerInverse.Data curve collar} {parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {regular : RegularBounds.Data cap} {source :
    UniformReciprocalPrimitives.SourcePrimitive data index}
  {box : Rational.Box} {capSample : Cap.Primitives.Sample cap
    differential index box}
  {target energyTarget tolerance : Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth pairFloor
    joinFloor : Nat}

namespace EnergyData

/-- Rebuild the actual energy blocks along the original chart-plan spine using the retained endpoint pairs and evaluated
cells. -/
@[expose] def restoredBlocks (branch : HyperellipticReciprocal.originOrder curve = 1)
  (joinNonnegative : 0 ≤ tolerance / 4) :
    {edges : List Subdivision.ParameterEdge} → {bank :
      ParentBank.Bank regular data edges} → {owners :
      ParentOwners.Owners bank} →
    {requests : ParentChartRequests.ChartRequests target floor owners} → (plans :
      ParentChartRequests.ChartPlans capSample minimum requests) →
    (cells : ParentPaths.ComparedCells source capSample depth bank) → (evaluated :
      ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells) →
    ParentEnergyRequests.EnergyData energyTarget energyFloor energyDepth plans
      cells evaluated →
    (pairs : ParentEndpoints.EndpointRequests (tolerance / 4) pairFloor owners) →
      pairs.maximum ≤ index → pairs.readingMaximum ≤ readingIndex →
    List (RestoredEnergyBlocks.RestoredEnergyBlock capSample energyDepth target
      energyTarget (tolerance / 4))
  | _, _, _, _, .nil, .nil, _, _, .nil, _, _ => []
  | _, _, _, _, .cons _ tail, .cons _ cells, evaluated, energies, .cons pair rest, modelLater, readingLater =>
      RestoredEnergyCells.ofEvaluation evaluated.1 energies.1.val branch
        energies.1.property
        (ChartEndpointReadings.Evaluation.endpointPair evaluated.1 pair
          ((Data.Nat.Order.le_max_left _ _).trans modelLater) ((Data.Nat.Order.le_max_left _ _).trans readingLater))
          joinNonnegative ::
      EnergyData.restoredBlocks branch
        joinNonnegative tail cells evaluated.2 energies.2 rest
        ((Data.Nat.Order.le_max_right _ _).trans modelLater) ((Data.Nat.Order.le_max_right _ _).trans readingLater)

/-- The restored block count equals the original edge count. -/
theorem restoredBlocks_length (branch : HyperellipticReciprocal.originOrder curve = 1)
  (joinNonnegative : 0 ≤ tolerance / 4)
    {edges : List Subdivision.ParameterEdge} {bank :
      ParentBank.Bank regular data edges} {owners :
      ParentOwners.Owners bank}
    {requests : ParentChartRequests.ChartRequests target floor owners} (plans :
      ParentChartRequests.ChartPlans capSample minimum requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (evaluated :
      ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells)
    (energies : ParentEnergyRequests.EnergyData energyTarget energyFloor
      energyDepth plans cells evaluated)
    (pairs : ParentEndpoints.EndpointRequests (tolerance / 4) pairFloor owners)
      (modelLater : pairs.maximum ≤ index) (readingLater : pairs.readingMaximum ≤ readingIndex) :
    (restoredBlocks branch joinNonnegative plans
      cells evaluated energies pairs modelLater readingLater).length = edges.length := by
  induction plans with
  | nil => cases cells; cases pairs; rfl
  | cons head tail ih =>
      cases cells with
      | cons cell cells =>
          cases pairs with
          | cons pair rest => exact congrArg Nat.succ (ih cells evaluated.2 energies.2 rest
              ((Data.Nat.Order.le_max_right _ _).trans modelLater) ((Data.Nat.Order.le_max_right _ _).trans
                readingLater))

/-- The restored block paths are exactly the original joined-chart replacement paths, including their incoming
connectors. -/
theorem restored_paths (branch : HyperellipticReciprocal.originOrder curve = 1)
  (joinNonnegative : 0 ≤ tolerance / 4)
    {edges : List Subdivision.ParameterEdge} {bank :
      ParentBank.Bank regular data edges} {owners :
      ParentOwners.Owners bank}
    {requests : ParentChartRequests.ChartRequests target floor owners} (plans :
      ParentChartRequests.ChartPlans capSample minimum requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (evaluated :
      ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells)
    (energies : ParentEnergyRequests.EnergyData energyTarget energyFloor
      energyDepth plans cells evaluated)
    (pairs : ParentEndpoints.EndpointRequests (tolerance / 4) pairFloor owners)
      (modelLater : pairs.maximum ≤ index) (readingLater : pairs.readingMaximum ≤ readingIndex)
    (previous : Normalization.InverseRootPolynomial.Gaussian) :
    RestoredEnergyBlocks.RestoredEnergyBlock.paths
      (restoredBlocks branch joinNonnegative plans
      cells evaluated energies pairs modelLater readingLater) previous =
      JoinedCharts.replacementPaths plans cells evaluated pairs
        (plans.endpointReadings cells evaluated pairs modelLater readingLater) previous := by
  induction plans generalizing previous with
  | nil => cases cells; cases pairs; rfl
  | cons head tail ih =>
      cases cells with
      | cons cell cells =>
          cases pairs with
          | cons pair rest =>
              change _ :: _ = _ :: _
              apply congrArg₂ List.cons
              · exact RestoredEnergyCells.ofEvaluation_path evaluated.1
                  energies.1.val branch energies.1.property _ joinNonnegative previous
              · exact ih cells evaluated.2 energies.2 rest ((Data.Nat.Order.le_max_right _ _).trans modelLater)
                  ((Data.Nat.Order.le_max_right _ _).trans readingLater) _

/-- The initial restored block's gap and join-error bounds, with no obligation for an empty block list. -/
@[expose] def RestoredFirstBound (blocks : List
  (RestoredEnergyBlocks.RestoredEnergyBlock capSample energyDepth target
  energyTarget (tolerance / 4)))
    (previous previousPotential : Normalization.InverseRootPolynomial.Gaussian) : Prop :=
  match blocks with
  | [] => True
  | head :: _ => Gaussian.Norm.Basic.normSq (head.firstValue - previous) ≤ tolerance / 4 ∧
      Gaussian.Norm.Basic.normSq (head.joinError previous previousPotential) ≤ 80 * target + 2 * (tolerance /
        4)

/-- The restored blocks satisfy the original junction bounds from the supplied initial bound and retained radial
comparisons. -/
theorem restored_joins (branch : HyperellipticReciprocal.originOrder curve = 1)
  (joinNonnegative : 0 ≤ tolerance / 4)
    (joinSmall : tolerance / 4 ≤ 1)
    {edges : List Subdivision.ParameterEdge} {bank :
      ParentBank.Bank regular data edges} {owners :
      ParentOwners.Owners bank}
    {requests : ParentChartRequests.ChartRequests target floor owners} (plans :
      ParentChartRequests.ChartPlans capSample minimum requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (evaluated :
      ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells)
    (energies : ParentEnergyRequests.EnergyData energyTarget energyFloor
      energyDepth plans cells evaluated)
    (pairs : ParentEndpoints.EndpointRequests (tolerance / 4) pairFloor owners)
      (modelLater : pairs.maximum ≤ index) (readingLater : pairs.readingMaximum ≤ readingIndex)
    {links : ParentOwners.Owners.Links owners} (junctions :
      JoinedReadings.JunctionRequests (tolerance / 4) joinFloor owners links)
    (joinLater : junctions.maximum ≤ readingIndex) (previous previousPotential :
      Normalization.InverseRootPolynomial.Gaussian)
    (small : RestoredFirstBound
      (restoredBlocks branch joinNonnegative plans
      cells evaluated energies pairs modelLater readingLater) previous previousPotential) :
    RestoredEnergyBlocks.RestoredEnergyBlock.JoinsBounded
      (restoredBlocks branch joinNonnegative plans
      cells evaluated energies pairs modelLater readingLater) previous previousPotential := by
  induction plans generalizing previous previousPotential with
  | nil => cases cells; cases pairs; trivial
  | cons head tail ih =>
      cases cells with
      | cons cell cells =>
          cases pairs with
          | cons pair rest =>
              refine ⟨small.1, small.2, ?_⟩
              cases tail with
              | nil => cases cells; cases rest; trivial
              | cons next tail =>
                  cases cells with
                  | cons nextCell cells =>
                      cases rest with
                      | cons nextPair rest =>
                          apply ih (.cons nextCell cells) evaluated.2 energies.2 (.cons nextPair rest)
                            ((Data.Nat.Order.le_max_right _ _).trans modelLater) ((Data.Nat.Order.le_max_right _
                              _).trans readingLater)
                            junctions.2 ((Data.Nat.Order.le_max_right _ _).trans joinLater) _ _ ?_
                          let firstPair :=
                            ChartEndpointReadings.Evaluation.endpointPair
                            evaluated.1 pair ((Data.Nat.Order.le_max_left _ _).trans modelLater)
                            ((Data.Nat.Order.le_max_left _ _).trans readingLater)
                          let lastPair :=
                            ChartEndpointReadings.Evaluation.endpointPair
                            evaluated.2.1 nextPair
                            ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans
                              modelLater))
                            ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans
                              readingLater))
                          have gap : Gaussian.Norm.Basic.normSq (lastPair.pair.firstValue -
                            firstPair.pair.lastValue) ≤ tolerance / 4 := by
                            rw [lastPair.pair.firstValue_eq, firstPair.pair.lastValue_eq]
                            exact (junctions.1.accurate firstPair.pair.last lastPair.pair.first
                              ((Data.Nat.Order.le_max_left _ _).trans joinLater)
                              ((Data.Nat.Order.le_max_left _ _).trans joinLater)).le
                          refine ⟨gap, ?_⟩
                          let firstBlock := RestoredEnergyCells.ofEvaluation
                            evaluated.1 energies.1.val branch energies.1.property firstPair joinNonnegative
                          let lastBlock := RestoredEnergyCells.ofEvaluation
                            evaluated.2.1 energies.2.1.val branch energies.2.1.property lastPair joinNonnegative
                          apply RestoredEnergyCells.join_bound firstBlock lastBlock
                            joinSmall ?_ gap
                          exact
                            (ChartEnergyJoins.AreaRequest.Evaluation.join_radial_close
                            evaluated.1 evaluated.2.1 junctions.1 branch ((Data.Nat.Order.le_max_left _ _).trans
                            joinLater) ((Data.Nat.Order.le_max_left _ _).trans joinLater) energyDepth).le

/-- The first restored value is the original endpoint request's retained first value. -/
theorem restored_first (branch : HyperellipticReciprocal.originOrder curve = 1)
  (joinNonnegative : 0 ≤ tolerance / 4)
    {edges : List Subdivision.ParameterEdge} {bank :
      ParentBank.Bank regular data edges} {owners :
      ParentOwners.Owners bank}
    {requests : ParentChartRequests.ChartRequests target floor owners} (plans :
      ParentChartRequests.ChartPlans capSample minimum requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (evaluated :
      ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells)
    (energies : ParentEnergyRequests.EnergyData energyTarget energyFloor
      energyDepth plans cells evaluated)
    (pairs : ParentEndpoints.EndpointRequests (tolerance / 4) pairFloor owners)
      (modelLater : pairs.maximum ≤ index) (readingLater : pairs.readingMaximum ≤ readingIndex) :
    (RestoredEnergyBlocks.RestoredEnergyBlock.initial
      (restoredBlocks branch joinNonnegative plans
      cells evaluated energies pairs modelLater readingLater)).1 =
      JoinedReadings.EndpointRequests.firstValue pairs cells
        (plans.endpointReadings cells evaluated pairs modelLater readingLater) := by
  cases plans with
  | nil => cases cells; cases pairs; rfl
  | cons head tail => cases cells; cases pairs; rfl

end EnergyData

set_option genInjectivity false in
/-- The generated energy belongs to the literal existing restored path.
Only its two shifted exterior endpoint potentials remain for gluing. -/
structure RequestedEnergy {edges : List Subdivision.ParameterEdge} {bank :
  ParentBank.Bank regular data edges} {owners :
  ParentOwners.Owners bank}
    {requests : ParentChartRequests.ChartRequests target floor owners} (plans :
      ParentChartRequests.ChartPlans capSample minimum requests)
    (cells : ParentPaths.ComparedCells source capSample depth bank) (evaluated :
      ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells)
    (pairs : ParentEndpoints.EndpointRequests (tolerance / 4) pairFloor owners)
      (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (energyFloor : Nat)
    extends ParentEnergy.EnergyPreparation plans cells evaluated energyTarget
      energyFloor where
  /-- The common model stage meets the original energy request. -/ model_later : pairs.maximum ≤ index
  /-- The reading stage meets the original prepared bounds. -/ reading_later : pairs.readingMaximum ≤ readingIndex
  /-- The retained joining allowance is nonnegative. -/ join_nonnegative : 0 ≤ tolerance / 4
  /-- The shared radial subdivision depth. -/ depth : Nat
  /-- The depth meets every original radial request. -/ depth_ge : requests.maximum ≤ depth
  /-- The exact radial parameters at the retained depth. -/ parameters : Path.Dyadic.RadialTriangles.Parameters depth
  /-- The actual energy data on those original parameters. -/ energies :
    ParentEnergyRequests.EnergyData allowance energyFloor depth plans cells
    evaluated
  /-- The cached restored energy blocks. -/ blocks : List
    (RestoredEnergyBlocks.RestoredEnergyBlock capSample depth target allowance
    (tolerance / 4))
  /-- The blocks are exactly those restored from the original evaluated chart data. -/ blocks_eq : ∀ branch :
    HyperellipticReciprocal.originOrder curve = 1,
    blocks = EnergyData.restoredBlocks branch join_nonnegative
      plans cells evaluated energies pairs model_later reading_later
  /-- The actual block count equals the original edge count. -/ count_eq : blocks.length = edges.length
  /-- The retained first endpoint value. -/ firstValue : Normalization.InverseRootPolynomial.Gaussian
  /-- The retained first endpoint potential. -/ firstPotential : Normalization.InverseRootPolynomial.Gaussian
  /-- The retained initial pair is the first restored pair. -/ first_eq : (firstValue, firstPotential) =
    RestoredEnergyBlocks.RestoredEnergyBlock.initial blocks
  /-- The first value is the original endpoint request's value. -/ first_value : firstValue =
    JoinedReadings.EndpointRequests.firstValue pairs cells
    (plans.endpointReadings cells evaluated pairs model_later reading_later)
  /-- The joined actual energy connection. -/ connection :
    RestoredEnergyBlocks.RestoredEnergyBlock.Connection blocks firstValue
    firstPotential
  /-- The connection uses exactly the original joined-chart replacement paths. -/ paths_eq :
    RestoredEnergyBlocks.RestoredEnergyBlock.paths blocks firstValue =
    JoinedCharts.replacementPaths plans cells evaluated pairs
    (plans.endpointReadings cells evaluated pairs model_later reading_later) firstValue

constructive_injectivity RequestedEnergy

namespace EnergyPreparation

variable {edges : List Subdivision.ParameterEdge} {bank :
  ParentBank.Bank regular data edges} {owners :
  ParentOwners.Owners bank}
  {requests : ParentChartRequests.ChartRequests target floor owners} {plans :
    ParentChartRequests.ChartPlans capSample minimum requests}
  {cells : ParentPaths.ComparedCells source capSample depth bank} {evaluated :
    ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells}

/-- Evaluate the original prepared requests at the shared parameters and retain their exact restored blocks and joined
energy connection. -/
@[expose] def evaluate (prepared : ParentEnergy.EnergyPreparation plans cells
  evaluated energyTarget energyFloor)
    (pairs : ParentEndpoints.EndpointRequests (tolerance / 4) pairFloor owners)
      (modelLater : pairs.maximum ≤ index) (readingLater : pairs.readingMaximum ≤ readingIndex)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < Energy.AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (parameters : Path.Dyadic.RadialTriangles.Parameters energyDepth) (later : prepared.requests.maximum ≤ energyDepth)
    (targetNonnegative : 0 ≤ target) {links : ParentOwners.Owners.Links owners}
    (junctions : JoinedReadings.JunctionRequests (tolerance / 4) joinFloor owners
      links) (joinNonnegative : 0 ≤ tolerance / 4) (joinSmall : tolerance / 4 ≤ 1)
    (joinLater : junctions.maximum ≤ readingIndex) :
      RequestedEnergy plans cells evaluated pairs energyTarget
      energyFloor := open Purelib.Data.Rat in by
  let energies := prepared.requests.evaluate branch oriented parameters plans cells evaluated later
  let blocks := EnergyData.restoredBlocks branch
    joinNonnegative plans cells evaluated energies pairs modelLater readingLater
  let first := RestoredEnergyBlocks.RestoredEnergyBlock.initial blocks
  have firstBound : EnergyData.RestoredFirstBound blocks
    first.1 first.2 := by
    change EnergyData.RestoredFirstBound blocks
      (RestoredEnergyBlocks.RestoredEnergyBlock.initial blocks).1
      (RestoredEnergyBlocks.RestoredEnergyBlock.initial blocks).2
    cases blocks with
    | nil => trivial
    | cons head tail =>
        change Gaussian.Norm.Basic.normSq (head.firstValue - head.firstValue) ≤ tolerance / 4 ∧
          Gaussian.Norm.Basic.normSq (head.firstPotential - head.firstPotential - Path.BoundaryRibbon.area
            head.firstValue head.firstValue) ≤ 80 * target + 2 * (tolerance / 4)
        rw [Gaussian.Basic.sub_self, Gaussian.Basic.sub_self, Path.IncrementArea.area_self, Gaussian.Basic.sub_zero,
          Gaussian.Norm.Basic.normSq_zero]
        exact ⟨joinNonnegative, add_nonneg
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) targetNonnegative)
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) joinNonnegative)⟩
  let joins := EnergyData.restored_joins branch
    joinNonnegative joinSmall plans cells evaluated energies pairs modelLater readingLater junctions joinLater first.1
    first.2 firstBound
  let connection := RestoredEnergyBlocks.RestoredEnergyBlock.Connection.build
    targetNonnegative joinNonnegative joinSmall blocks first.1 first.2 joins
  exact ⟨prepared, modelLater, readingLater, joinNonnegative, energyDepth, later, parameters, energies, blocks, fun _ =>
    rfl,
    EnergyData.restoredBlocks_length branch joinNonnegative
      plans cells evaluated energies pairs modelLater readingLater,
    first.1, first.2, Prod.eta first,
      EnergyData.restored_first branch joinNonnegative plans
      cells evaluated energies pairs modelLater readingLater,
    connection, EnergyData.restored_paths branch
      joinNonnegative plans cells evaluated energies pairs modelLater readingLater first.1⟩

end EnergyPreparation

namespace RequestedEnergy

variable {edges : List Subdivision.ParameterEdge} {bank :
  ParentBank.Bank regular data edges} {owners :
  ParentOwners.Owners bank}
  {requests : ParentChartRequests.ChartRequests target floor owners} {plans :
    ParentChartRequests.ChartPlans capSample minimum requests}
  {cells : ParentPaths.ComparedCells source capSample depth bank} {evaluated :
    ParentChartRequests.ChartPlans.EvaluationData readingIndex plans cells}
  {pairs : ParentEndpoints.EndpointRequests (tolerance / 4) pairFloor owners}

/-- Prepare the original bounds and requests once, select their common depth and retain the evaluated energy connection.
-/
@[expose] def build (plans : ParentChartRequests.ChartPlans capSample minimum
  requests) (cells : ParentPaths.ComparedCells source capSample depth bank)
    (evaluated : ParentChartRequests.ChartPlans.EvaluationData readingIndex plans
      cells) (pairs : ParentEndpoints.EndpointRequests (tolerance / 4) pairFloor
      owners)
    (modelLater : pairs.maximum ≤ index) (readingLater : pairs.readingMaximum ≤ readingIndex)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < Energy.AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (targetNonnegative : 0 ≤ target) {links : ParentOwners.Owners.Links owners}
    (junctions : JoinedReadings.JunctionRequests (tolerance / 4) joinFloor owners
      links) (joinNonnegative : 0 ≤ tolerance / 4) (joinSmall : tolerance / 4 ≤ 1)
    (joinLater : junctions.maximum ≤ readingIndex) (energyTarget : Normalization.InverseRootPolynomial.Coordinate)
      (positive : 0 < energyTarget) (energyFloor : Nat) :
    RequestedEnergy plans cells evaluated pairs energyTarget
      energyFloor :=
  let bounds := Cap.EnergyBounds.build capSample
    RootContinuation.RootRadialGeometry.domain
  let prepared := ParentEnergy.EnergyPreparation.build plans cells evaluated bounds
    energyTarget positive energyFloor
  let parameters := Path.Dyadic.RadialTriangles.Parameters.build prepared.requests.maximum
  EnergyPreparation.evaluate prepared pairs modelLater
    readingLater branch oriented parameters le_rfl targetNonnegative junctions joinNonnegative joinSmall joinLater

/-- The actual connection energy differs from its trace and endpoint-potential expression by the original squared-count
allowance. -/
theorem boundary_error (energy : RequestedEnergy plans cells
  evaluated pairs energyTarget energyFloor) :
    Gaussian.Norm.Basic.normSq (energy.connection.energy - (-energy.connection.trace +
      RestoredEnergyBlocks.RestoredEnergyBlock.terminalPotential energy.blocks
        energy.firstPotential - energy.firstPotential)) ≤
      (edges.length : Normalization.InverseRootPolynomial.Coordinate) ^ 2 * (1024 * (target + tolerance / 4)) := by
  have bound := energy.connection.boundary_error
  rw [energy.count_eq] at bound
  exact bound

/-- The actual connection energy is strictly greater than the negative retained energy target. -/
theorem lower (energy : RequestedEnergy plans cells evaluated
  pairs energyTarget energyFloor) :
    -energyTarget < energy.connection.energy.im / 4 := open Purelib.Data.Rat in by
  have bound := energy.connection.lower
  rw [energy.count_eq] at bound
  exact (Fraction.Order.Arithmetic.neg_lt_neg_direct energy.allowance_paid).trans_le bound

end RequestedEnergy

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy
