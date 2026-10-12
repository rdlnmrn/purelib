module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Riemann.Branches.NewtonRequestedCutComparison
import Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement
import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth
import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder

import Purelib.Curves.Hyperelliptic.Meshes.Newton.LocalPairedPeriodComparison
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.TerminalExteriorBound
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.TerminalExteriorBudget
public import Purelib.Riemann.RootContinuation.NewtonOrderedExteriorCancellation
import Purelib.Tactic.Ring

public section

open Purelib.Data

/-! Requested decay of the corrected ordered resplit determinant. Both
exterior degree shapes use the same retained Newton and reciprocal cache. -/
namespace Purelib.Riemann.Normalization.NewtonResplitDeterminantBound

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton (TerminalExteriorBudget)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.TerminalExteriorBound (terminal_exterior_bound)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth (ExteriorSourceRequest)
open Purelib.Riemann.RootContinuation.NewtonRequestedExteriorRemainder (JoiningEndpointRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.LocalPairedPeriodComparison (resplitWordDeterminant)
open Purelib.Riemann.RootContinuation.NewtonOrderedExteriorCancellation (exteriorAdjustedRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal (resplitPhysicalExteriorCorrection)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
  {preparation : NewtonPreparation base.bank.toBranchCellBank}
  {target radius : Rational} {i j : Fin genus} {floor : Nat}

open Purelib.Curves.Hyperelliptic.Meshes.Newton in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs in
open Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement in
set_option genInjectivity false in
/-- Retained exterior requests paying the ordered resplit determinant correction.

The canonical exterior equation ties the boundary components to the original lifted mesh. The terminal budget, source
depth and joining endpoints share the same retained allowance. -/
structure ResplitExteriorPreparation (paired : Ordered.Paired ordered)
    (boundary : BoundaryPreparation preparation i j target radius floor) where
  /-- The retained indexed exterior components are the original lifted exterior boundaries. -/ canonical :
    boundary.exterior.prepared.components.map (fun component => component.program.indexed) =
    boundary.lifted.exteriorBoundaries
  /-- The terminal exterior budget for the original paired bank and boundary. -/ budget :
    Curves.Hyperelliptic.Meshes.Newton.TerminalExteriorBudget paired boundary
  /-- The retained source request at the terminal budget's allowance and original floor. -/ source :
    ExteriorSourceRequest boundary budget.allowance floor
  /-- The joining endpoint request at the exact retained source depth and allowance. -/ endpoints :
    JoiningEndpointRequest (BoundaryPreparation.atDepth boundary source.depth) budget.allowance

constructive_injectivity ResplitExteriorPreparation

namespace ResplitExteriorPreparation

variable {boundary : BoundaryPreparation preparation i j target radius floor}

open Purelib.Curves.Hyperelliptic.Meshes.Newton.TerminalExteriorBudget in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs in
open Purelib.Riemann in
open Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement in
/-- Acquire the terminal budget, exterior sources and joining endpoints for the original canonical boundary.

The source depth determines the refined boundary used by the endpoint request, preserving the same terminal allowance.
-/
@[expose] def build (paired : Ordered.Paired ordered) (boundary : BoundaryPreparation preparation i j target radius
  floor)
    (canonical : boundary.exterior.prepared.components.map (fun component => component.program.indexed) =
      boundary.lifted.exteriorBoundaries) :
    ResplitExteriorPreparation paired boundary :=
  let budget := TerminalExteriorBudget.build paired boundary
  let source := RootContinuation.NewtonRequestedExteriorDepth.prepareExteriorSources boundary budget.allowance
    budget.positive floor
  ⟨canonical, budget, source, RootContinuation.NewtonRequestedExteriorRemainder.prepareJoiningEndpoints
    (BoundaryPreparation.atDepth boundary source.depth) budget.allowance budget.positive⟩

open Purelib.Data in
open Purelib.Data.Gaussian.Norm in

open Purelib.Data in
open Purelib.Data.Gaussian.Norm in

open Purelib.Curves.Hyperelliptic.Meshes.Newton in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes in
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing in
open Purelib.Data in
open Purelib.Data.Gaussian.Norm in
open Purelib.Data.Rat.Fraction.Cast in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Riemann in
open Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement in
/-- Choose a stage bounding the original ordered resplit determinant by 816 times the target.

The threshold pays all cached source, endpoint and terminal magnitude requests and respects the requested minimum. The
retained physical exterior correction supplies the final determinant estimate. -/
@[expose] def determinantRequest (data : ResplitExteriorPreparation paired boundary) (prepared : PeriodPrograms.Prepared
  paired)
    (newSheet : Fin 2) (minimum : Nat) :
    let refined := BoundaryPreparation.atDepth boundary data.source.depth
    {threshold : Nat // minimum ≤ threshold ∧
      ∀ stage (cache : RegularMeshes.Numerics boundary.domains stage)
        (readings : CutPairingRequest.Readings refined.paid.cut cache)
        (_cached : Branches.NewtonRequestedCutComparison.CutAnnularReadings refined.comparison readings), threshold ≤
          stage →
        Data.Gaussian.Norm.Basic.normSq (LocalPairedPeriodComparison.resplitWordDeterminant prepared (current :=
          refined.lifted)
          newSheet
          (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.left.values)
            (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.right.values)) < 816 * target} := by
  intro refined
  let adjusted := exteriorAdjustedRequest prepared newSheet boundary data.canonical data.source data.endpoints minimum
  let threshold := max adjusted.val (max (max data.source.index data.endpoints.val.endpoints.index)
    (max data.budget.first.index data.budget.second.index))
  refine ⟨threshold, adjusted.property.1.trans (Nat.Order.le_max_left _ _), ?_⟩
  intro stage cache readings cached later
  have otherLater := (Nat.Order.le_max_right _ _).trans later
  have referenceLater := (Nat.Order.le_max_left _ _).trans otherLater
  have magnitudeLater := (Nat.Order.le_max_right _ _).trans otherLater
  have reduced := adjusted.property.2 stage cache readings cached ((Nat.Order.le_max_left _ _).trans later)
  have terminal := TerminalExteriorBound.terminal_exterior_bound (paired := paired) newSheet boundary data.canonical
    data.budget.first data.budget.second
    data.source data.endpoints.val readings ((Nat.Order.le_max_left _ _).trans referenceLater) ((Nat.Order.le_max_right
      _ _).trans referenceLater)
      ((Nat.Order.le_max_left _ _).trans magnitudeLater) ((Nat.Order.le_max_right _ _).trans magnitudeLater)
  let determinant := LocalPairedPeriodComparison.resplitWordDeterminant prepared (current := refined.lifted) newSheet
    (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.left.values) (CanonicalEdgeValues.edgeValuation
      refined.lifted.mesh readings.right.values)
  let correction := BilinearPolarization.extract (fun coefficient => ExteriorTotal.resplitPhysicalExteriorCorrection
    (paired := paired)
    refined.fine.family.single.grid.shrunk.included refined.lifted.edges refined.lifted.vertices newSheet
    (BilinearPolarization.mix (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.left.values)
      (CanonicalEdgeValues.edgeValuation refined.lifted.mesh readings.right.values) coefficient))
  have paid : Data.Gaussian.Norm.Basic.normSq correction ≤ target := by
    have weight := data.budget.weight_eq
    have bound := (congrArg (fun weight => weight * (2 * (data.budget.allowance + data.budget.allowance))) weight).symm
    exact terminal.trans (bound.trans_le data.budget.paid)
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct data.budget.allowance_le (Order.natCast_pos_direct (n :=
    40) (by decide)).le
  have allowanceBound : 2 * (180 * target + 2 * (target + 2 *
      (2 * (data.budget.allowance + data.budget.allowance) + data.budget.allowance))) ≤ 404 * target :=
    (show _ = 364 * target + 40 * data.budget.allowance by ring1).trans_le
      ((Arithmetic.add_le_add_direct (le_refl (364 * target)) scaled).trans_eq (by ring1))
  change Data.Gaussian.Norm.Basic.normSq ((determinant - correction) + (determinant - correction)) < _ at reduced
  have reduced := reduced.trans_le allowanceBound
  have doubled : Data.Gaussian.Norm.Basic.normSq (correction + correction) ≤ 4 * target :=
    (Basic.normSq_double correction).trans_le (Arithmetic.mul_le_mul_of_nonneg_left_direct paid (by decide))
  have estimate := (Bounds.normSq_add_le_two ((determinant - correction) + (determinant - correction)) (correction +
    correction)).trans_lt
    (Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Rat.Fraction.Rational) < 2)
      ((Arithmetic.add_lt_add_right_direct reduced _).trans_le (Arithmetic.add_le_add_direct (le_refl _) doubled)))
  rw [show (determinant - correction) + (determinant - correction) + (correction + correction) = determinant +
    determinant by ring1] at estimate
  have smaller : Data.Gaussian.Norm.Basic.normSq determinant ≤ Data.Gaussian.Norm.Basic.normSq (determinant +
    determinant) :=
    (show Data.Gaussian.Norm.Basic.normSq determinant = 1 * Data.Gaussian.Norm.Basic.normSq determinant by
      ring1).le.trans
      ((Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide : (1 : Rat.Fraction.Rational) ≤ 4) (Basic.normSq_nonneg
        determinant)).trans_eq
        (Basic.normSq_double determinant).symm)
  exact smaller.trans_lt (estimate.trans_eq (by ring1))

end ResplitExteriorPreparation
end Purelib.Riemann.Normalization.NewtonResplitDeterminantBound
