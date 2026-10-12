module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Rat

open Purelib.Riemann.Periods

@[expose] public section

/-! Exact area and endpoint accounting for the complete crossing bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests (HorizontalPrepared
  VerticalPrepared)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    VertexBank bank.grid} {edges :
    RootEdgeBank frames}
  {faces : PuncturedFaces bank} {domains :
    FaceDomainBank frames faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {target : Rational}
  {mesh : LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : TwoSheetRequest (fun sheet
  => RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target}

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Rational} {floor
  stage : Nat}
  {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

open Purelib.Algebra.FiniteSum.Fin (sumFin)

section CrossingRequests
variable {retained : CrossingBank request mesh}
  {allocated : CrossingRequests
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential i)
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential j)
    firstParent secondParent tolerance floor retained}
  {cache : Numerics domains stage}

/-- The complete signed crossing-area difference, summed over both face indices and sheets with vertical terms positive.
-/
def
  CrossingSamples.CrossingRequests.Samples.areaDifference
  (samples : CrossingRequests.Samples allocated cache) : Data.Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    VerticalPrepared.Sample.areaDifference (prepared := (((allocated.vertical.get a).get b).get c)) (cache := cache)
      (((samples.vertical.get a).get b).get c))))
  - FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    HorizontalPrepared.Sample.areaDifference (prepared := (((allocated.horizontal.get a).get b).get c)) (cache := cache)
      (((samples.horizontal.get a).get b).get c))))

/-- The complete signed crossing endpoint difference on the actual sample bank. -/
def
  CrossingSamples.CrossingRequests.Samples.endpointDifference
  (samples : CrossingRequests.Samples allocated cache) : Data.Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    VerticalPrepared.Sample.endpointDifference (prepared := (((allocated.vertical.get a).get b).get c)) (cache := cache)
      (((samples.vertical.get a).get b).get c))))
  - FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    HorizontalPrepared.Sample.endpointDifference (prepared := (((allocated.horizontal.get a).get b).get c)) (cache :=
      cache)
      (((samples.horizontal.get a).get b).get c))))

/-- The complete signed crossing endpoint jump on the actual sample bank. -/
def
  CrossingSamples.CrossingRequests.Samples.endpointJump
  (samples : CrossingRequests.Samples allocated cache) : Data.Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    VerticalPrepared.Sample.endpointJump (prepared := (((allocated.vertical.get a).get b).get c)) (cache := cache)
      (((samples.vertical.get a).get b).get c))))
  - FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    HorizontalPrepared.Sample.endpointJump (prepared := (((allocated.horizontal.get a).get b).get c)) (cache := cache)
      (((samples.horizontal.get a).get b).get c))))

/-- The complete signed error between crossing endpoint increments and their retained jumps. -/
def
  CrossingSamples.CrossingRequests.Samples.endpointIncrementError
  (samples : CrossingRequests.Samples allocated cache) : Data.Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    VerticalPrepared.Sample.endpointIncrementError (prepared := (((allocated.vertical.get a).get b).get c)) (cache :=
      cache)
      (((samples.vertical.get a).get b).get c))))
  - FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    HorizontalPrepared.Sample.endpointIncrementError (prepared := (((allocated.horizontal.get a).get b).get c)) (cache
      := cache)
      (((samples.horizontal.get a).get b).get c))))

/-- The actual endpoint difference splits exactly into its retained jump and increment error. -/
theorem
  CrossingSamples.CrossingRequests.Samples.endpointDifference_eq_jump
  (samples : CrossingRequests.Samples allocated cache) :
    samples.endpointDifference = samples.endpointJump + samples.endpointIncrementError := by
  simp only
    [Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples.endpointDifference,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples.endpointJump,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples.endpointIncrementError,
    HorizontalPrepared.Sample.endpointDifference_eq_jump, VerticalPrepared.Sample.endpointDifference_eq_jump,
    FiniteSum.Fin.sumFin_add]
  ring1

/-- Canonical endpoint sum; downstream calculations read `Accounting.endpoints`. -/
def CrossingAccounting.CrossingRequests.endpointSpecification (allocated : CrossingRequests
  (PeriodMatrix.standardDifferential i)
    (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor retained)
    (cache : RegularMeshes.Numerics domains stage) : Data.Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    VerticalPrepared.endpointSpecification (((allocated.vertical.get a).get b).get c) cache))) -
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    HorizontalPrepared.endpointSpecification (((allocated.horizontal.get a).get b).get c) cache)))

/-- The sampled endpoint difference reads the canonical endpoint specification on the same request and cache. -/
theorem
  CrossingSamples.CrossingRequests.Samples.endpointDifference_eq_specification
  (samples : CrossingRequests.Samples allocated cache) :
    samples.endpointDifference =
      CrossingAccounting.CrossingRequests.endpointSpecification allocated cache := by
  unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples.endpointDifference
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting.CrossingRequests.endpointSpecification
  simp only [HorizontalPrepared.Sample.endpointDifference_eq_specification,
    VerticalPrepared.Sample.endpointDifference_eq_specification, -eq_self, -iff_self]
  try rfl

/-- The canonical signed endpoint-jump sum on the retained crossing requests and numerical cache. -/
def CrossingAccounting.CrossingRequests.jumpSpecification (allocated : CrossingRequests
  (PeriodMatrix.standardDifferential i)
    (PeriodMatrix.standardDifferential j) firstParent secondParent tolerance floor retained)
    (cache : RegularMeshes.Numerics domains stage) : Data.Gaussian.Basic.Canonical :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    VerticalPrepared.jumpSpecification (((allocated.vertical.get a).get b).get c) cache))) -
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    HorizontalPrepared.jumpSpecification (((allocated.horizontal.get a).get b).get c) cache)))

/-- The sampled endpoint jump equals its canonical retained specification. -/
theorem
  CrossingSamples.CrossingRequests.Samples.endpointJump_eq_specification
  (samples : CrossingRequests.Samples allocated cache) :
    samples.endpointJump =
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting.CrossingRequests.jumpSpecification
      allocated cache := by
  unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples.endpointJump
    CrossingAccounting.CrossingRequests.jumpSpecification
  simp only [HorizontalPrepared.Sample.endpointJump_eq_specification,
    VerticalPrepared.Sample.endpointJump_eq_specification, -eq_self, -iff_self]
  try rfl

/-- The actual signed crossing residual total is its area difference minus its endpoint difference. -/
theorem
  CrossingSamples.CrossingRequests.Samples.total_eq
  (samples : CrossingRequests.Samples allocated cache) :
    samples.total = samples.areaDifference - samples.endpointDifference := by
  simp only [Samples.total, Samples.horizontalTotal, Samples.verticalTotal,
    HorizontalPrepared.Sample.residual_eq, VerticalPrepared.Sample.residual_eq,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples.areaDifference,
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples.CrossingRequests.Samples.endpointDifference,
      FiniteSum.Fin.sumFin_sub]
  ring1

set_option genInjectivity false in
/-- Cached complete crossing-area and endpoint accounting on one retained sample bank.

The corrected total retains its exact signed decomposition into area minus endpoints. -/
structure CrossingAccounting.CrossingRequests.Accounting (samples : CrossingRequests.Samples allocated cache) where
  /-- The cached signed crossing-area difference. -/ area : Data.Gaussian.Basic.Canonical
  /-- The area cache reads the actual crossing sample bank. -/ area_eq : area = samples.areaDifference
  /-- The cached signed crossing endpoint difference. -/ endpoints : Data.Gaussian.Basic.Canonical
  /-- The endpoint cache reads the actual crossing sample bank. -/ endpoints_eq : endpoints = samples.endpointDifference
  /-- The cached complete corrected crossing total. -/ corrected : Data.Gaussian.Basic.Canonical
  /-- The corrected cache equals the actual signed residual total. -/ corrected_eq : corrected = samples.total
  /-- The retained corrected total is the area cache minus the endpoint cache. -/ decomposition : corrected = area -
    endpoints

constructive_injectivity CrossingAccounting.CrossingRequests.Accounting

/-- Cache the actual crossing-area and endpoint totals with their exact corrected decomposition. -/
def CrossingAccounting.CrossingRequests.Accounting.build (samples : CrossingRequests.Samples allocated cache) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting.CrossingRequests.Accounting samples :=
  let area := samples.areaDifference
  let endpoints := samples.endpointDifference
  ⟨area, rfl, endpoints, rfl, area - endpoints, samples.total_eq.symm, rfl⟩

/-- The cached endpoint total equals the canonical request-and-cache specification. -/
theorem CrossingAccounting.CrossingRequests.Accounting.endpoints_eq_specification {samples : CrossingRequests.Samples
  allocated cache} (accounting :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting.CrossingRequests.Accounting samples) :
    accounting.endpoints =
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting.CrossingRequests.endpointSpecification
      allocated cache :=
  accounting.endpoints_eq.trans samples.endpointDifference_eq_specification

/-- The cached endpoint total splits into the sampled jump and increment error. -/
theorem CrossingAccounting.CrossingRequests.Accounting.endpoints_eq_jump {samples : CrossingRequests.Samples allocated
  cache} (accounting :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting.CrossingRequests.Accounting samples) :
    accounting.endpoints = samples.endpointJump + samples.endpointIncrementError :=
  accounting.endpoints_eq.trans samples.endpointDifference_eq_jump

/-- At a paid request stage, the cached area-minus-endpoint discrepancy satisfies the aggregate target. -/
theorem CrossingAccounting.CrossingRequests.TotalRequest.accounting_bound {target : Fraction.Rational}
    (total : CrossingRequests.TotalRequest retained i j firstParent secondParent target floor)
    {samples : CrossingRequests.Samples total.allocated cache} (accounting :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingAccounting.CrossingRequests.Accounting samples)
    (later : total.allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (accounting.area - accounting.endpoints) ≤ target := by
  rw [← accounting.decomposition, accounting.corrected_eq]
  exact TotalRequest.bound total samples later

end CrossingRequests
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
