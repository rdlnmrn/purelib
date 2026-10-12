module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic

import Purelib.Approximation.Budget.SynchronizedSamples
import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.FamilyReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.Topology.Surface.Chord.Spanning
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.ChordFamily
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FamilyLateRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ScalarBudgets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedStandardPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.BoundaryReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.PeriodReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.SharedPeriods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

public section

/-! One retained common stage for the standard periods and all component
streams. The existing finite movement request pays synchronization before
any actual integer-weighted row is compared. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : Meshes.FramedPuncturedGrid curve (Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve
    branches).branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {index differential : Fin genus} {row : Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection.IntersectionRow
    lifted integral index} {source : Hyperelliptic.Differentials.Basic.Differential genus}
  {prepared : Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutChordPrograms lifted source} {components :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples prepared.programs differential}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {family : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily prepared.programs.programs domains
    differential}
  {targets : Data.Vector Fraction.Rational lifted.cutBoundaryWord.alphabet.count}
  {floor : Nat} {budget : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Budget family targets
    floor}
  {minimumStages : Data.Vector Nat lifted.cutBoundaryWord.alphabet.count}
  {minimum : Nat} {target : Fraction.Rational} {extraPoints : List Gaussian.Basic.Canonical}

/-- Type of the common-stage cache, retaining the family's parameters. -/
@[expose] def CommonStage (readings : FamilyReadings row
  budget minimumStages minimum target extraPoints)
    (components : Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples prepared.programs differential)
      (sampleFloor : Nat) :=
  Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples.CommonSamples components readings.requested (max
    sampleFloor readings.standard.original.comparison.stage)

/-- Retain the existing common-stage cache. Including the standard floor
also covers an empty component bank without choosing a component index. -/
@[expose] def commonSamples (readings : FamilyReadings row
  budget minimumStages minimum target extraPoints)
    (components : Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ComponentSamples prepared.programs differential)
      (sampleFloor : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.CommonStage readings components sampleFloor :=
  Hyperelliptic.Meshes.PuncturedGrid.SynchronizedPeriodSamples.CommonSamples.build components readings.requested (max
    sampleFloor readings.standard.original.comparison.stage)

/-- The common cached stage is at least the original standard comparison stage. -/
@[expose] def CommonStandardLater
    {readings : FamilyReadings row budget minimumStages
      minimum target extraPoints} {sampleFloor : Nat}
    (common : Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.CommonStage readings components sampleFloor) :
      Prop :=
    readings.standard.original.comparison.stage ≤ common.common.stage

/-- The retained common-stage floor includes the original standard comparison floor, including an empty component bank.
-/
theorem common_standard_later
    {readings : FamilyReadings row budget minimumStages
      minimum target extraPoints} {sampleFloor : Nat}
    (common : Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.CommonStage readings components sampleFloor) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.CommonStandardLater common :=
  (Data.Nat.Order.le_max_right _ _).trans common.common.floor_le

/-- Combine the retained component values without rerunning their models. -/
@[expose] def CachedWeightedEq
    {readings : FamilyReadings row budget minimumStages
      minimum target extraPoints} {sampleFloor : Nat}
    (common : Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.CommonStage readings components sampleFloor)
    {weights : Data.Vector Int lifted.cutBoundaryWord.alphabet.count}
    (period : Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod components weights) : Prop :=
    period.coefficients.combine common.common.values = period.approximation.sample common.common.stage

/-- Combining the cached component values with the retained integer coefficients gives the original weighted sample at
that same common stage. -/
theorem cached_weighted_eq
    {readings : FamilyReadings row budget minimumStages
      minimum target extraPoints} {sampleFloor : Nat}
    (common : Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.CommonStage readings components sampleFloor)
    {weights : Data.Vector Int lifted.cutBoundaryWord.alphabet.count}
    (period : Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod components weights) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.CachedWeightedEq common period := open Purelib.Algebra in
      by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.CachedWeightedEq]
  rw [period.sample_eq]
  unfold Periods.WeightedPeriods.Coefficients.combine
  exact FiniteSum.Fin.sumFin_congr fun entry => congrArg
    (fun value => period.coefficients.values entry * value) (common.common.values_eq entry)

variable (segments : Data.Vector.DependentVector (fun entry =>
  Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks.SegmentBank (prepared.programs.programs entry).period))
  {budget : Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.Budget
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.PeriodFamilies.PrimitiveFamily.ofSegments segments domains differential)
    targets floor}
  {movementTarget : Fraction.Rational} {floors : Data.Vector Nat lifted.cutBoundaryWord.alphabet.count}
  (movement : Budget.SynchronizedSamples.StageRequest components.streams movementTarget floors)
  (readings : FamilyReadings row budget movement.stages
    minimum target extraPoints) {sampleFloor : Nat}
  (common : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.CommonStage readings components
    sampleFloor)

/-- The retained standard cochain reading meets its component bound against the cached common-stage value. -/
@[expose] def CochainCommonAccurate (entry : Fin lifted.cutBoundaryWord.alphabet.count) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.standard.triangles.values)
        (prepared.programs.programs entry).cycle.path.surfaceEdges - common.common.values entry) <
      2 * (4 * targets entry + movementTarget)

/-- The original movement request transports each retained cochain comparison to the common cached stage. -/
theorem cochain_common_accurate (entry : Fin lifted.cutBoundaryWord.alphabet.count) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.CochainCommonAccurate segments movement readings common
      entry := by
  apply common.common.comparison movement (fun next => ?_)
    (fun next => Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.standard.triangles.values)
      (prepared.programs.programs next).cycle.path.surfaceEdges) (fun next => 4 * targets next) (fun next => ?_) entry
  · rw [common.stages_eq]
    exact readings.requested_stage_later next
  · rw [common.earlier_eq_programs]
    exact (readings.cochain_component_accurate segments next).le

/-- The retained cochain reading meets its component bound against the original program sample at the common stage. -/
@[expose] def CochainCommonProgramAccurate (entry : Fin lifted.cutBoundaryWord.alphabet.count) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.standard.triangles.values)
        (prepared.programs.programs entry).cycle.path.surfaceEdges -
      (((prepared.programs.programs entry).program differential).integral.model common.common.stage).integralSample) <
      2 * (4 * targets entry + movementTarget)

/-- The cached common-stage component comparison is the corresponding original program comparison. -/
theorem cochain_common_program_accurate (entry : Fin lifted.cutBoundaryWord.alphabet.count) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.CochainCommonProgramAccurate segments movement readings
      common entry := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.CochainCommonProgramAccurate]
  rw [← common.values_eq_programs entry]
  exact Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.cochain_common_accurate segments movement readings
    common entry

/-- The actual cached integer coefficients pay the common-stage component
errors. No unit amplification or analytic component bound is assumed. -/
@[expose] def WeightedCommonBound
    {weights : Data.Vector Int lifted.cutBoundaryWord.alphabet.count}
    (period : Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod components weights) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Chord.Spanning.CutCycleChain.edgeValue period.chain
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.standard.triangles.values) -
      period.approximation.sample common.common.stage) ≤
      period.coefficients.charge (fun entry => 2 * (4 * targets entry + movementTarget))

/-- The original integer coefficient charge bounds the complete weighted cochain error at the retained common stage.

Each component contributes its actual primitive and movement allowance; the cached coefficient bank supplies the
amplification. -/
theorem weighted_common_bound
    {weights : Data.Vector Int lifted.cutBoundaryWord.alphabet.count}
    (period : Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod components weights) :
    Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.WeightedCommonBound segments movement readings common
      period := by
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.WeightedCommonBound]
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.Cut.ChainPeriods.ChainPeriod.chain,
    Topology.Surface.Chord.Spanning.CutCycleChain.edgeValue]
  have comparison := period.comparison_bound
    (fun entry => Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      readings.standard.triangles.values)
      (prepared.routes.cycles entry).path.surfaceEdges) common.common.stage
    (fun entry => 2 * (4 * targets entry + movementTarget)) (fun entry => by
      have bound := (Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily.cochain_common_program_accurate segments
        movement readings common entry).le
      have equal := congrArg (fun cycle => Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
          readings.standard.triangles.values) cycle.path.surfaceEdges)
        (prepared.programs.cycles_eq entry)
      exact (congrArg (fun value => Data.Gaussian.Norm.Basic.normSq (value -
        (((prepared.programs.programs entry).program differential).integral.model common.common.stage).integralSample))
          equal).symm.trans_le bound)
  rw [period.coefficients.combine_eq] at comparison
  exact comparison

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.CommonFamily
