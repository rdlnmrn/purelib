module
import Purelib.Algebra.NatCast
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReplacementRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyAllowance
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergyRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalAreaRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyAllowance

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentEnergy

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredEnergyBlocks

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy

open Purelib.Data.Rat

open Purelib.Integration.Energy

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation

public section

/-!
# Shared-depth energy on the synchronized exterior parent

The retained sample equality transports the shared polynomial-bound cache.
All requests precede fan generation, and the resulting energy uses the
literal chart replacement already acquired by the exterior side.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests (StageRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement (ChartReplacement)
open Purelib.Integration.Path.Dyadic.RadialTriangles (Parameters)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {cover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}
  {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover}
    {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget target :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
  {minimum index depth readingIndex : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest prepared sourceTarget
    reciprocalTarget coefficientTarget totalTarget areaTarget minimum}
  {replacement : ChartReplacementRequest
    prepared target minimum}
  {evaluated : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.StageRequest.Evaluation request sample
    depth readingIndex}

/-- Transport the retained energy-bound cache along equality of the original cap sample and its model index. -/
@[expose] def transportBounds {firstIndex lastIndex : Nat}
    {first : Primitives.Sample cap differential firstIndex box}
    {last : Primitives.Sample cap differential lastIndex box}
    (indices : firstIndex = lastIndex) (samples : HEq first last)
    (bounds : Cap.EnergyBounds last RootRadialGeometry.domain) : Cap.EnergyBounds first
      RootRadialGeometry.domain := by
  cases indices
  cases samples
  exact bounds

namespace ChartReplacement

/-- Reuse the shared cap-polynomial bound cache to prepare energy requests on the actual retained chart cells. -/
@[expose] def prepareEnergy (chart : StageChartReplacement.ChartReplacement replacement evaluated)
    (bounds : Cap.EnergyBounds sample RootRadialGeometry.domain)
    (energyTarget : InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
    ParentEnergy.EnergyPreparation chart.charts evaluated.cap.polynomial.cells chart.vertices energyTarget energyFloor
      :=
  EnergyPreparation.build chart.charts evaluated.cap.polynomial.cells chart.vertices
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergy.transportBounds evaluated.original_index
      evaluated.capSample_eq bounds) energyTarget positive energyFloor

variable {energyTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth : Nat}

/-- Evaluate the original energy preparation at the supplied shared radial depth and parameters, reusing all retained
endpoint and junction requests. -/
@[expose] def evaluateEnergy (chart : StageChartReplacement.ChartReplacement replacement evaluated)
    (prepared : ParentEnergy.EnergyPreparation chart.charts evaluated.cap.polynomial.cells chart.vertices energyTarget
      energyFloor)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (oriented : 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    (parameters : RadialTriangles.Parameters energyDepth) (later : prepared.requests.maximum ≤ energyDepth) :
    RestoredParentEnergy.RequestedEnergy chart.charts evaluated.cap.polynomial.cells chart.vertices
      request.cap.endpoints energyTarget energyFloor :=
  EnergyPreparation.evaluate prepared request.cap.endpoints chart.model_later chart.reading_later branch oriented
    parameters later
    replacement.localPositive.le request.cap.junctions
    (Fraction.Order.Field.div_nonneg_direct request.cap.budget.positive.le (by decide)) (JoinedRequest.energy_join_small
      request.cap) chart.junction_later

variable (chart : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageChartReplacement.ChartReplacement replacement
  evaluated)
  (energy : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RestoredParentEnergy.RequestedEnergy chart.charts
    evaluated.cap.polynomial.cells chart.vertices request.cap.endpoints energyTarget energyFloor)

/-- The actual retained energy chain starts at the same first reading as the original cap comparison. -/
theorem energy_first : energy.firstValue = evaluated.cap.firstValue := by
  rw [energy.first_value, evaluated.cap.firstValue_eq, chart.readings_eq]

/-- The actual restored energy-block paths are exactly the original cached chart-replacement paths. -/
theorem energy_paths :
    RestoredEnergyBlock.paths energy.blocks energy.firstValue = chart.replacement.paths := by
  rw [energy.paths_eq, chart.replacement.paths_eq, chart.readings_eq,
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergy.ChartReplacement.energy_first chart energy]

/-- The actual energy trace equals the original replacement area plus its retained first-value and total endpoint term.
-/
theorem energy_trace : energy.connection.trace = chart.replacement.summary.area +
    BoundaryRibbon.area evaluated.cap.firstValue chart.replacement.summary.total := by
  rw [energy.connection.trace_eq, Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergy.ChartReplacement.energy_paths
    chart energy, Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergy.ChartReplacement.energy_first chart energy,
    IncrementArea.traceArea_eq, ← chart.replacement.summary.area_eq, ← chart.replacement.summary.total_eq]

/-- This allowance uses the original source/join request and the independent replacement request; neither is reacquired
for energy. -/
theorem energy_boundary_close :
    Data.Gaussian.Norm.Basic.normSq (energy.connection.energy - (-chart.replacement.summary.area -
      BoundaryRibbon.area evaluated.cap.firstValue chart.replacement.summary.total +
      RestoredEnergyBlock.terminalPotential energy.blocks energy.firstPotential - energy.firstPotential)) <
        256 * (4 * target + totalTarget / 4) := by
  have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 256)
    (ChartReplacementRequest.energy_allowance replacement request.cap)
  have paid : (cover.mesh.edges.length : InverseRootPolynomial.Coordinate) ^ 2 * (1024 *
      (replacement.localTarget + request.cap.budget.tolerance / 4)) < 256 * (4 * target + totalTarget / 4) :=
    (show _ = 256 * (((2 * cover.mesh.edges.length : Nat) : InverseRootPolynomial.Coordinate) ^ 2 *
      (replacement.localTarget + request.cap.budget.tolerance / 4)) by
          simp only [Algebra.NatCast.mul, Nat.cast_ofNat];
          ring1).trans_lt scaled
  have close := (RequestedEnergy.boundary_error energy).trans_lt paid
  rw [Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergy.ChartReplacement.energy_trace chart energy] at close
  refine (congrArg Data.Gaussian.Norm.Basic.normSq ?_).trans_lt close
  ring1

end ChartReplacement
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.StageEnergy
