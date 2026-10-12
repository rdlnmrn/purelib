module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement
import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SideRemainders
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Mesh.RetracingWords
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.ExteriorBoundary
import Purelib.Riemann.Periods.NewtonStandardExteriorPeriods
public import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Tactic.QuotientFreeOmega

public section

open Purelib.Data

/-! Each original one-sheet exterior integral in even degree inherits the
reciprocal-patch bound from the automatic Newton boundary preparation. -/

namespace Purelib.Riemann.Periods.NewtonOriginalExteriorPeriods

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth (ExteriorSourceRequest)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder (ComponentCanonicalPeriodBound)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation SurfaceComponent)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (PhysicalLoopSplit)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest (Readings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Riemann.Normalization
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {first second : Fin genus}
  {target radius : Rational} {floor : Nat}

open Purelib.Riemann in
/-- Each original one-sheet exterior word occurs in the lifted exterior boundary list in even degree.

The retained curve degree excludes the odd case, and the two explicit sheet labels exhaust the actual boundary
components. -/
private theorem even_boundary_member {next : FramedPuncturedGrid curve branches higher}
    (lifted : LiftedPuncturedGrid next) (degree : curve.polynomial.natDegree = 2 * genus + 2) (sheet : Fin 2) :
    lifted.edges.indexedEdges lifted.vertices next.bank.exterior sheet ∈ lifted.exteriorBoundaries := by
  cases shape : curve.degreeShape with
  | odd oddDegree =>
      exfalso
      omega
  | even _ =>
      rw [Meshes.LiftedPuncturedGrid.exteriorBoundaries, shape]
      change _ ∈ [_, _]
      rcases sheet with ⟨value, bound⟩
      cases value with
      | zero => exact List.Membership.mem_cons.mpr (Or.inl rfl)
      | succ value =>
        cases value with
        | zero =>
          exact List.Membership.mem_cons.mpr
            (Or.inr (List.Membership.mem_cons.mpr (Or.inl rfl)))
        | succ value =>
          exact False.elim (Nat.not_lt_zero value
            (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound)))

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal in
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face in
/-- The automatic exterior preparation's indexed component words equal the retained lifted exterior boundaries. -/
private theorem canonical_components {next : FramedPuncturedGrid curve branches higher}
    {lifted : LiftedPuncturedGrid next} {collar : ReciprocalExteriorCollar.Data curve}
    {cap : ReciprocalInnerInverse.Data curve collar} (regular : RegularBounds.Data cap)
    (domains : DomainBanks.FaceDomainBank lifted.frames next.faces.regulars) (source : Basic.Differential genus) :
    (AllSurfacePreparation.build regular domains source).components.map
      (fun component => component.program.indexed) = lifted.exteriorBoundaries := by
  change ((PeriodPrograms.exteriorPrograms lifted source).map (SurfaceComponent.build regular domains)).map _ = _
  rw [List.Map.map_map]
  exact PeriodPrograms.exteriorPrograms_indexed lifted source

open Purelib.Topology.Surface.Sewing.SewingRetraction in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy in
open Purelib.Data in
/-- The original exterior chain and its retained Newton refinement have the same antisymmetric edge valuation.

The comparison uses the original ambient frame, cached root edges and reference loops, preserving the incoming sheet and
actual resplit exterior walk. -/
private theorem original_exterior_value
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (sheet : Fin 2) (value : OrientedEdge prepared.lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    prepared.lifted.edges.chainValue prepared.lifted.vertices value
      (prepared.fine.family.single.grid.shrunk.included.resplit base.bank.exterior (FramedBranchCellBank.baseMember
        base.bank)) sheet =
    wordValue value (prepared.lifted.edges.indexedEdges prepared.lifted.vertices
      prepared.fine.family.single.grid.punctured.bank.exterior sheet) :=
  (prepared.fine.family.single.grid.shrunk.included.exterior_comparison base.bank.frame
    prepared.fine.family.single.grid.punctured.bank.frame prepared.lifted.edges prepared.lifted.vertices
    (fun point member => (BranchCellBank.referenceAt prepared.fine.family.single.grid.punctured.bank.toBranchCellBank
      point member).toLoop)).values value anti sheet

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing in
open Purelib.Data in
open Purelib.Data.Gaussian.Norm in
open Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement in
/-- Both original exterior readings obey the reciprocal request and endpoint remainder bounds.

Every sufficiently late shared triangle cache supplies two standard-differential readings on the same retained Newton
boundary and original incoming sheet; each squared norm is at most twice the sum of the two requested errors. -/
@[expose] def OriginalExteriorPeriodsBound
    (prepared : BoundaryPreparation preparation first second target radius floor) (sheet : Fin 2) : Prop :=
    ∀ {requested : Rat.Fraction.Rational} {minimum : Nat} (result : ExteriorSourceRequest prepared requested minimum)
      {endpointTarget : Rat.Fraction.Rational}
      (endpoints : AllSurfacePreparation.SideRemainderRequest
        (BoundaryPreparation.atDepth prepared result.depth).exterior.prepared (BoundaryPreparation.atDepth prepared
          result.depth).paid.cut.fixed first second endpointTarget)
      {stage : Nat} {cache : RegularMeshes.Numerics prepared.domains stage}
      (readings : CutPairingRequest.Readings (BoundaryPreparation.atDepth prepared result.depth).paid.cut cache),
      result.index ≤ stage → endpoints.endpoints.index ≤ stage →
      let refined := BoundaryPreparation.atDepth prepared result.depth
      let walk := refined.fine.family.single.grid.shrunk.included.resplit base.bank.exterior
        (FramedBranchCellBank.baseMember base.bank)
      Data.Gaussian.Norm.Basic.normSq (refined.lifted.edges.chainValue refined.lifted.vertices
        (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.left.values) walk sheet) ≤ 2 * (requested +
          endpointTarget) ∧
      Data.Gaussian.Norm.Basic.normSq (refined.lifted.edges.chainValue refined.lifted.vertices
        (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.right.values) walk sheet) ≤ 2 * (requested +
          endpointTarget)

open Purelib.Topology.Surface.Sewing.SewingRetraction in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid in
open Purelib.Data in
open Purelib.Data.Gaussian in
open Purelib.Data.Gaussian.Norm in
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder in
/-- Transfer canonical component bounds to the original one-sheet exterior in even degree.

The exact component-list equality selects the retained component for the requested sheet. Word-valuation agreement
transports both bounds to the original resplit exterior without changing the request or triangle cache. -/
theorem original_exterior_periods_bound
    (prepared : BoundaryPreparation preparation first second target radius floor)
    (canonical : prepared.exterior.prepared.components.map (fun component => component.program.indexed) =
      prepared.lifted.exteriorBoundaries)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) (sheet : Fin 2) : OriginalExteriorPeriodsBound prepared sheet
      := by
  intro requested minimum result endpointTarget endpoints stage cache readings later endpointLater refined walk
  have member := even_boundary_member prepared.lifted degree sheet
  rw [← canonical] at member
  obtain ⟨component, present, equal⟩ := List.Map.mem_map.mp member
  obtain ⟨index, inRange, atIndex⟩ := List.getElem_of_mem present
  have bounded := ExteriorSourceRequest.canonical_period_bound prepared result ⟨index, inRange⟩ endpoints readings later
    endpointLater
  unfold ComponentCanonicalPeriodBound at bounded
  rw [Purelib.Topology.Mesh.RetracingWords.paired_total_map_eq_wordValue] at bounded
  have indexed := (congrArg (fun component => component.program.indexed) atIndex).trans equal
  have left := (original_exterior_value refined sheet _
    (CanonicalEdgeValues.edgeValuation_reverse refined.lifted.mesh readings.left.values)).trans
    (congrArg (wordValue (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.left.values)) indexed.symm)
  have right := (original_exterior_value refined sheet _
    (CanonicalEdgeValues.edgeValuation_reverse refined.lifted.mesh readings.right.values)).trans
    (congrArg (wordValue (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.right.values)) indexed.symm)
  change Basic.Canonical.normSq _ ≤ _ ∧
    Basic.Canonical.normSq _ ≤ _ at bounded
  constructor
  · rw [Basic.normSq_eq_canonical]
    exact (congrArg Basic.Canonical.normSq left).trans_le bounded.1
  · rw [Basic.normSq_eq_canonical]
    exact (congrArg Basic.Canonical.normSq right).trans_le bounded.2

open Purelib.Data in
/-- The automatic Newton boundary preparation bounds each original exterior sheet in even degree.

Its literal component list supplies the canonical comparison. Both standard differential readings consume the same
reciprocal request, endpoint remainders and retained triangle cache. -/
theorem automatic_original_exterior_periods_small
    (preparation : NewtonPreparation base.bank.toBranchCellBank) (first second : Fin genus)
    (target radius : Rat.Fraction.Rational) (positive : 0 < target) (radiusPositive : 0 < radius) (floor : Nat)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) (sheet : Fin 2) :
    OriginalExteriorPeriodsBound (BoundaryPreparation.build preparation first second target radius positive
      radiusPositive floor) sheet := by
  exact original_exterior_periods_bound
    (BoundaryPreparation.build preparation first second target radius positive radiusPositive floor)
    (canonical_components _ _ _) degree sheet

end Purelib.Riemann.Periods.NewtonOriginalExteriorPeriods
