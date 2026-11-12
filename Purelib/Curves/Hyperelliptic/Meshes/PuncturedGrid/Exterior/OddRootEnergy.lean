module
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSamples
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.EnergyEndAssembly
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib

open Purelib.Data.Rat

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Riemann

public section

/-!
# Acquire the actual odd surface energy after all original root-join stages

The canonical odd exterior has one root-closed component. Its retained
component supplies every join request before the shared chart readings.
The resulting energy and endpoint bank refer to the same samples.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation (Entry)

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {localTarget localArea chartTarget : InverseRootPolynomial.Coordinate} {floor index depth readingIndex :
    Nat} {box : Rational.Box}
  {sample : Charts.Reciprocal.Cap.Primitives.Sample cap differential index box} {shared :
    Face.PrimitiveData.FacePrimitiveBank differential index domains}

/-- Select the existing component, without preparing its program again. -/
@[expose] def singleComponent (prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential) (one : prepared.components.length = 1) :
    { component :
      ExteriorProgram.SurfaceComponent
      regular domains differential // prepared.components = [component] } :=
  match equal : prepared.components with
  | [] => by rw [equal] at one; cases one
  | [component] => ⟨component, rfl⟩
  | _ :: _ :: tail => by
      have impossible : tail.length + 2 = 1 := by simpa only [equal, List.length_cons] using one
      omega

/-- The original all-surface preparation has exactly one component when the reciprocal origin has order one. -/
theorem build_odd_component_count (regular : Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (domains : Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars)
      (differential : Differentials.Basic.Differential genus)
    (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :

      (ExteriorProgram.AllSurfacePreparation.build
      regular domains differential).components.length = 1 := by
  change ((PeriodPrograms.exteriorPrograms lifted differential).map
    (ExteriorProgram.SurfaceComponent.build
    regular domains)).length = 1
  rw [List.Map.length_map]
  cases shape : curve.degreeShape with
  | even degree =>
      have empty : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0 := by rw
        [Charts.Reciprocal.HyperellipticReciprocal.originOrder, shape]
      exact Nat.noConfusion (empty.symm.trans branch)
  | odd degree => rw [PeriodPrograms.exteriorPrograms, shape]; rfl

namespace Request.ChartRequest

variable {prepared :
  ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target areaTarget : InverseRootPolynomial.Coordinate}
  {request : AllSurfacePreparation.Request prepared target
    areaTarget floor} {charts :
    AllSurfacePreparation.Request.ChartRequest request
    chartTarget}

set_option genInjectivity false in
/-- The actual odd surface energy and endpoint bank acquired after all original root-join stages.

The shared sample, face primitives and chart readings retain their exact component occurrences and a certified residual
bound. -/
structure RootEnergyAcquisition (charts :
  AllSurfacePreparation.Request.ChartRequest request
  chartTarget)
    (component :
      ExteriorProgram.SurfaceComponent
      regular domains differential) (joining energyTarget : InverseRootPolynomial.Coordinate)
    (depthFloor energyFloor : Nat) where
  /-- The original component's retained junction and closing root-return request. -/ roots :
    ExteriorProgram.SurfacePreparation.EnergyRootRequest
    component.prepared joining floor
  /-- The retained common polynomial sample index. -/ index : Nat
  /-- The retained sample index meets the original chart request. -/ later : charts.index ≤ index
  /-- The actual cap primitive sample at the retained common index. -/ sample :
    Charts.Reciprocal.Cap.Primitives.Sample cap differential index collar.box
  /-- The original face primitive bank at that same index. -/ shared :
    Face.PrimitiveData.FacePrimitiveBank differential index domains
  /-- The original chart plan for the retained cap sample. -/ plan :
    AllSurfacePreparation.Request.ChartRequest.Plan charts
    sample
  /-- The retained common source refinement depth. -/ depth : Nat
  /-- The depth is exactly the maximum of the supplied floor and original chart depth. -/ depth_eq : depth = max
    depthFloor charts.depth
  /-- The retained endpoint reading index after chart and root-return preparation. -/ readingIndex : Nat
  /-- The reading index is exactly the maximum of the original chart stage and root-return index. -/ readingIndex_eq :
    readingIndex = max plan.stage roots.index
  /-- The actual shared chart evaluation on the retained samples and stages. -/ evaluated :
    AllSurfacePreparation.Request.ChartRequest.Plan.Evaluation
    plan shared depth readingIndex
  /-- The cached shared energy on that exact original chart evaluation. -/ energy :
    AllSurfacePreparation.Request.ChartRequest.Plan.SharedEnergy
    evaluated energyTarget energyFloor
  /-- The evaluated entries retain exactly the original component's ordered occurrences. -/ occurrences_eq :
    evaluated.samples.values.map (fun entry => entry.entry.occurrence) = component.prepared.occurrences
  /-- The actual endpoint bank on the retained joined component spine. -/ ends :
    Charts.Reciprocal.Disk.EnergyEndBank sample readingIndex energy.depth
    charts.localChart roots.joined.spine.bank
  /-- The endpoint bank is exactly the original root request's readback of the same energy data. -/ ends_eq : ∀ branch :
    Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1,
    ends = roots.endBank evaluated.samples.values energy.data branch occurrences_eq
  /-- The endpoint residual satisfies the original parent-count and allocated chart/root-return bound. -/ residual_bound
    : Gaussian.Norm.Basic.normSq ends.residual ≤
    2 * ((component.program.cache.parents.length : InverseRootPolynomial.Coordinate) *
      ((component.program.cache.parents.length : InverseRootPolynomial.Coordinate) * (80 *
        charts.localChart + 2 * roots.allowance)) +
        (80 * charts.localChart + 2 * roots.allowance))

constructive_injectivity RootEnergyAcquisition

/-- Choose the original cross-segment and closing requests first; every
later endpoint and fan belongs to the supplied shared bank. Its numerical
stage may already have been raised by the standard-period requests. -/
@[expose] def acquireRootEnergy (charts :
  AllSurfacePreparation.Request.ChartRequest request
  chartTarget)
    (component :
      ExteriorProgram.SurfaceComponent
      regular domains differential) (single : prepared.components = [component])
    (branch : Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (joining energyTarget : InverseRootPolynomial.Coordinate) (joinPositive : 0 < joining) (energyPositive
      : 0 < energyTarget)
    (depthFloor energyFloor : Nat) {index : Nat}
    (sample : Charts.Reciprocal.Cap.Primitives.Sample cap differential index collar.box)
    (shared : Face.PrimitiveData.FacePrimitiveBank differential index domains) (later
      : charts.index ≤ index) :
    RootEnergyAcquisition charts
      component joining energyTarget depthFloor energyFloor := open Approximation in by
  let roots :=
    ExteriorProgram.SurfacePreparation.EnergyRootRequest.build
    component.prepared joining joinPositive floor
  let plan :=
    AllSurfacePreparation.Request.ChartRequest.Plan.build
    charts sample
  let depth := max depthFloor charts.depth
  let readingIndex := max plan.stage roots.index
  let evaluated := plan.evaluate shared depth readingIndex later (Nat.Order.le_max_right _ _)
    (Nat.Order.le_max_left _ _)
  let energy := evaluated.energy branch energyTarget energyPositive energyFloor
  have occurrences : evaluated.samples.values.map (fun entry => entry.entry.occurrence) = component.prepared.occurrences
    := by
    calc
      _ = (evaluated.samples.values.map ChartSamples.ChartedEntry.entry).map
        Entry.occurrence := by
        rw [List.Map.map_map];
        rfl
      _ = component.prepared.occurrences := by
        rw [evaluated.samples.entries_eq, request.occurrences_eq, prepared.occurrences_eq, single]
        change component.prepared.occurrences ++ [] = component.prepared.occurrences
        exact List.Append.append_nil _
  let ends := roots.endBank evaluated.samples.values energy.data branch occurrences
  have nonnegative : 0 ≤ charts.localChart := charts.localChart_eq ▸ (Rational.Budget.Aggregate.perTerm_positive
    charts.positive _).le
  have bound := roots.endBank_bound evaluated.samples.values energy.data branch occurrences nonnegative
    (Nat.Order.le_max_right _ _)
  have counted : ((component.prepared.occurrences.map (fun item => item.compared.entered.cache.parents)).flatten.length
    : Nat) =
      component.program.cache.parents.length := congrArg List.length component.prepared.parents_eq
  rw [counted] at bound
  exact ⟨roots, index, later, sample, shared, plan, depth, rfl, readingIndex, rfl, evaluated, energy, occurrences, ends,
    (fun _ => rfl), bound⟩

end Request.ChartRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.OddRootEnergy
