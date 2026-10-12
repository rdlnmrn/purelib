module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectBound
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectBound

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceDefectRequest

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides

open Purelib.Data.Gaussian.Norm.Sum

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Riemann.Readings

open Purelib.Riemann.Topology

open Purelib.Topology.BranchedCover.Double

public section

/-! All complete-face defects are paid at one coefficient-independent
numerical index, preserving the homogeneous surface energy lower bound. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters FaceAssemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest (energyAllowanceTarget
  energyAllowanceTarget_positive energyAllowanceTarget_paid)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Topology.BranchedCover.Double.Attachment (Face)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational} {grid :
    NewtonGrid preparation target radius}
  {observations : ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {sheet : Fin 2}
  {partitions : SurfacePartitions observations grid}
  {surfaceCuts : SurfaceCuts partitions domains}
    {depth : Nat}
  {fixed : Preflights domains sheet} {error :
    Rational}
  {energy : SurfaceRequest partitions
    (Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
    sheet depth) fixed error}
  {position : Fin grid.faces.regulars.length}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Integration.Energy.Polygon (energyPrimitivePoint)
open Purelib.Integration.Path.BoundaryRibbon (Ribbon)

variable {pieceError : Rational} {minimum : Nat}

namespace DefectRequest

/-- The dependent bank of actual matched seam traces on every original regular face. -/
@[expose] def SurfaceSeamTraces (energy : NewtonRequestedSurfaceEnergy.SurfaceRequest partitions
  (MeshCompatibility.surfaceMeshes partitions domains surfaceCuts sheet depth) fixed error) :=
  Data.Vector.DependentVector (fun position : Fin grid.faces.regulars.length => MatchedSides.SeamTraces energy position)

/-- The complete original face-defect request bank on those same retained seam traces. -/
@[expose] def SurfaceFaceRequests (base : ExteriorRequest energy pieceError minimum)
    (traces : SurfaceSeamTraces energy) (perFace :
      Fraction.Rational) :=
  Data.Vector.DependentVector (fun position : Fin grid.faces.regulars.length => FaceDefectRequest base
    (traces.get position) perFace)

end DefectRequest

namespace DefectRequest.SurfaceFaceRequests

/-- The supplied common stage pays every original retained face request. -/
@[expose] def IndexBound {base : ExteriorRequest energy pieceError minimum}
    {traces : Curves.Hyperelliptic.Meshes.Newton.Surface.DefectRequest.SurfaceSeamTraces energy} {perFace :
      Fraction.Rational}
    (entries : Curves.Hyperelliptic.Meshes.Newton.Surface.DefectRequest.SurfaceFaceRequests base traces perFace) (index
      : Nat) : Prop :=
  ∀ position, (entries.get position).index ≤ index

end DefectRequest.SurfaceFaceRequests

set_option genInjectivity false in
/-- The request retains the actual matched traces and all local requests. Its index works for every coefficient vector
and every later sample. -/
structure DefectRequest (base : ExteriorRequest energy pieceError minimum) (allowance :
  Fraction.Rational) where
  /-- The original total defect allowance is strictly positive. -/ positive : 0 < allowance
  /-- The complete original matched seam trace bank. -/ traces :
    Curves.Hyperelliptic.Meshes.Newton.Surface.DefectRequest.SurfaceSeamTraces energy
  /-- The retained common allowance for each original face defect. -/ perFace : Fraction.Rational
  /-- The per-face allowance is exactly the aggregate share of the total target over the original face count. -/
    perFace_eq : perFace = Aggregate.perTerm allowance grid.faces.regulars.length
  /-- The original complete local defect requests on the retained seam traces. -/ entries :
    Curves.Hyperelliptic.Meshes.Newton.Surface.DefectRequest.SurfaceFaceRequests base traces perFace
  /-- The cached common stage paying all original face-defect and base requests. -/ index : Nat
  /-- The common stage pays the original base exterior request. -/ base_le : base.index ≤ index
  /-- The common stage pays every retained original face-defect request. -/ index_ge : entries.IndexBound index

constructive_injectivity DefectRequest

namespace DefectRequest

variable {base : ExteriorRequest energy pieceError
  minimum} {allowance : Rational}

/-- Construct the original matched seam traces and local requests, then cache one stage paying their complete bank and
base request. -/
@[expose] def build (base : ExteriorRequest energy pieceError minimum) (allowance : Fraction.Rational)
  (positive : 0 < allowance) :
    DefectRequest base allowance := by
  let traces : SurfaceSeamTraces energy := DependentVector.ofFn
    (SeamTraces.build energy)
  let perFace := Aggregate.perTerm allowance grid.faces.regulars.length
  let entries : SurfaceFaceRequests base traces perFace :=
    DependentVector.ofFn fun position =>
    FaceDefectRequest.build base (traces.get position) perFace (Aggregate.perTerm_positive positive _)
  let index := max base.index (entries.maximum fun _ request => request.index)
  refine ⟨positive, traces, perFace, rfl, entries, index, Nat.Order.le_max_left _ _, ?_⟩
  intro position
  exact (entries.get_le_maximum (fun _ request => request.index) position).trans (Nat.Order.le_max_right _ _)

variable {stage : Nat} {cache : Numerics
  domains stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {assemblies : ExteriorRequest.Assemblies energy
    cache coefficients} {perimeters : Perimeters
    assemblies}

/-- At the paid common stage, the actual complete surface defect obeys the original allowance with its homogeneous
coefficient factor. -/
theorem error_bound (request : DefectRequest base allowance)
  (later : request.index ≤ stage)
    (faces : FaceAssembly.FaceAssemblies perimeters) :
    Data.Gaussian.Norm.Basic.normSq faces.defect ≤ (genus : Fraction.Rational) ^ 2 *
      PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 * allowance := by
  have bound := Indexed.normSq_sumFin_le
    (fun position => (faces.get position).seams + (faces.get position).cornerTotal)
    ((genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
      request.perFace)
    (fun position => FaceDefectRequest.accurate (request.entries.get position) ((request.index_ge position).trans later)
      (faces.get position))
  have payment : (grid.faces.regulars.length : Fraction.Rational) ^ 2 * request.perFace ≤ allowance := by
    rw [request.perFace_eq]
    exact (le_of_eq (by ring1)).trans (Aggregate.count_mul_perTerm_lt request.positive _).le
  apply bound.trans
  calc
    _ = ((genus : Fraction.Rational) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2) *
      ((grid.faces.regulars.length : Fraction.Rational) ^ 2 * request.perFace) := by ring1
    _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct payment
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
        (Fraction.Order.Arithmetic.sq_nonneg_direct _))

/-- Prepare the original complete defect request at the allowance required for the supplied homogeneous energy loss. -/
@[expose] def forEnergyAllowance (base : ExteriorRequest energy pieceError minimum)
    (allowance : Fraction.Rational) (positive : 0 < allowance) :
    DefectRequest base (ConjugateRequest.energyAllowanceTarget
      genus allowance) :=
  build base _
    (ConjugateRequest.energyAllowanceTarget_positive positive)

/-- The complete regular-face exterior inherits the independent observation lower bound after all internal ownership,
seam and corner losses are paid. -/
theorem energy_lower {ownershipAllowance exteriorAllowance faceAllowance : Fraction.Rational}
    (ownership : ConjugateRequest energy (ConjugateRequest.energyAllowanceTarget genus
      ownershipAllowance))
    (base : ExteriorRequest energy (ConjugateRequest.energyAllowanceTarget genus exteriorAllowance)
      ownership.index)
    (request : DefectRequest base
      (ConjugateRequest.energyAllowanceTarget genus faceAllowance))
    (ownershipPositive : 0 < ownershipAllowance) (exteriorPositive : 0 < exteriorAllowance)
    (facePositive : 0 < faceAllowance) (later : request.index ≤ stage) (samples : energy.Readings cache)
    (face : Attachment.Face) (faces : FaceAssembly.FaceAssemblies perimeters) :
    (NewtonObservationSurfaceLower.surfaceLowerConstant observations - error - ownershipAllowance - exteriorAllowance -
      faceAllowance) *
        PreparedObservationCoercivity.coefficientNormSq coefficients ≤ faces.exterior.im / 4 := by
  have close := request.error_bound later faces
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational)) _
      (fun row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row))
    exact (FiniteSum.Fin.sumFin_zero).symm.trans_le bound
  have difference : ExteriorRequest.exterior assemblies - faces.exterior = faces.defect := by
    rw [faces.decomposition]
    ring1
  have squared : Data.Gaussian.Norm.Basic.normSq (ExteriorRequest.exterior assemblies - faces.exterior) ≤
      (4 * (faceAllowance * PreparedObservationCoercivity.coefficientNormSq coefficients)) ^ 2 := by
    rw [difference]
    apply close.trans
    calc
      _ = ((genus : Fraction.Rational) ^ 2 * ConjugateRequest.energyAllowanceTarget genus faceAllowance) *
        PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 := by
        ring1
      _ ≤ (4 * faceAllowance) ^ 2 * PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (ConjugateRequest.energyAllowanceTarget_paid facePositive) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = _ := by ring1
  have comparison := PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le
    (ExteriorRequest.exterior assemblies) faces.exterior (faceAllowance *
      PreparedObservationCoercivity.coefficientNormSq coefficients)
    (Fraction.Order.Arithmetic.mul_nonneg_direct facePositive.le normNonnegative) squared
  have lower := base.energy_lower ownership ownershipPositive exteriorPositive (request.base_le.trans later)
    samples coefficients face assemblies
  have paid := (Fraction.Order.Arithmetic.sub_le_sub_direct lower
    (le_rfl (a := faceAllowance * PreparedObservationCoercivity.coefficientNormSq coefficients))).trans comparison
  exact (le_of_eq (by ring1)).trans paid

end DefectRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface
