module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

public section

/-! Both sheets and all regular faces share the already selected energy
meshes and one later numerical bank when paying ownership errors. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest

open Purelib
open Purelib.Algebra
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Topology.Polygon

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Preflights Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainClippedRequest (ClippedBasisRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List
    (RegularFace bank)} {domains :
    FaceDomainBank frames faces}
  {coarse : (sheet : Fin 2) → RegularMeshes
    domains sheet}
  {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {energyTarget : Rational}

set_option genInjectivity false in
/-- The shared two-sheet request paying every original regular face's clipped ownership discrepancy.

The retained energy meshes and per-face requests determine one common later numerical stage. -/
structure ClippedRequest (energy : TwoSheetBilinearRequest.TwoSheetRequest coarse fixed energyTarget) (target :
  Fraction.Rational) where
  /-- The original whole ownership-error target is strictly positive. -/ positive : 0 < target
  /-- The retained local squared-norm allowance for one face on one sheet. -/ perFace : Fraction.Rational
  /-- The local allowance is the nested two-sheet and face-count allocation of the original target. -/ perFace_eq :
    perFace = Aggregate.perTerm (Aggregate.perTerm target 2) faces.length
  /-- The dependent bank of actual clipped ownership requests on the original energy meshes. -/ entries :
    Data.Vector.DependentVector (fun sheet : Fin 2 => Data.Vector.DependentVector (fun position : Fin faces.length =>
    DomainClippedRequest.ClippedBasisRequest ((fixed sheet).get position).get
      ((energy.entries.get sheet).meshes.entries.get position) perFace))
  /-- The retained common stage paying both energy and all local clipped requests. -/ index : Nat
  /-- The common stage meets the original energy request. -/ energy_le : energy.index ≤ index
  /-- Every actual face and sheet request is paid at the retained common stage. -/ index_ge : ∀ sheet position,
    ((entries.get sheet).get position).index ≤ index

constructive_injectivity ClippedRequest

namespace ClippedRequest

variable {energy : TwoSheetRequest coarse
  fixed energyTarget} {target : Rational}

/-- Allocate the original target across both sheets and all faces, retaining their actual energy meshes and common
maximum stage. -/
@[expose] def build (energy : TwoSheetBilinearRequest.TwoSheetRequest coarse fixed energyTarget) (target :
  Fraction.Rational) (positive : 0 < target) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest.ClippedRequest energy target :=
  let perFace := Aggregate.perTerm (Aggregate.perTerm target 2) faces.length
  let entries := DependentVector.ofFn fun sheet : Fin 2 => DependentVector.ofFn fun position : Fin faces.length =>
    ClippedBasisRequest.build ((fixed sheet).get position).get
      ((energy.entries.get sheet).meshes.entries.get position) perFace
      (Aggregate.perTerm_positive (Aggregate.perTerm_positive positive 2) faces.length)
  let floor := entries.maximum (fun _ row => row.maximum (fun _ request => request.index))
  ⟨positive, perFace, rfl, entries, max energy.index floor, Data.Nat.Order.le_max_left _ _, fun sheet position =>
    (((entries.get sheet).get_le_maximum (fun _ request => request.index) position).trans
      (entries.get_le_maximum (fun _ row => row.maximum (fun _ request => request.index)) sheet)).trans
        (Data.Nat.Order.le_max_right _ _)⟩

/-- The error compares the shared exterior with the retained local owners. It does not remove seams between distinct
face domains. -/
@[expose] def pairError {stage : Nat} {cache : RegularMeshes.Numerics domains stage}
    (samples : TwoSheetRequest.Samples energy cache) (first second : Fin genus) (sheet : Fin 2) (position : Fin
      faces.length) : Gaussian :=
  let mesh := (energy.entries.get sheet).meshes.entries.get position
  let readings := (samples.get sheet).readings.get position
  Stokes.edgeListArea
    (fun vertex : Fin mesh.surface.mesh.vertices.length =>
      ⟨(readings.rows.get first).values vertex, (readings.rows.get second).values vertex⟩)
    mesh.surface.mesh.triangulation.boundary -
  mesh.pieces.localBoundary (fun column row point =>
    ⟨(cache.atDomain position sheet first).primitives.value column row point,
      (cache.atDomain position sheet second).primitives.value column row point⟩) mesh.depth

/-- Each actual shared-exterior versus local-owner discrepancy satisfies its retained per-face allowance. -/
theorem pairError_bound (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest.ClippedRequest energy
  target) {stage : Nat} {cache : RegularMeshes.Numerics domains stage}
    (later : request.index ≤ stage) (samples : TwoSheetRequest.Samples energy cache)
    (first second : Fin genus) (sheet : Fin 2) (position : Fin faces.length) :
    Data.Gaussian.Norm.Basic.normSq
      (pairError samples first second
      sheet position) < request.perFace :=
  ((request.entries.get sheet).get position).accurate ((request.index_ge sheet position).trans later)
    (cache.atDomain position sheet) ((samples.get sheet).readings.get position) first second

/-- The full actual two-sheet sum of face ownership discrepancies satisfies the original whole target. -/
theorem total_pairError_bound (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest.ClippedRequest
  energy target) {stage : Nat} {cache : RegularMeshes.Numerics domains stage}
    (later : request.index ≤ stage) (samples : TwoSheetRequest.Samples energy cache) (first second : Fin genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin
      (fun position : Fin faces.length =>
        pairError samples first second
        sheet position))) < target := by
  have perSheetPositive := Aggregate.perTerm_positive request.positive 2
  have facePaid : (faces.length : Fraction.Rational) ^ 2 * request.perFace <
      Aggregate.perTerm target 2 := by
    rw [request.perFace_eq]
    convert Aggregate.count_mul_perTerm_lt perSheetPositive faces.length using 1
    ring1
  have perSheet (sheet : Fin 2) :
      Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun position : Fin faces.length =>
        pairError samples first second
        sheet position)) ≤
        Aggregate.perTerm target 2 :=
    ((Indexed.normSq_sumFin_le _ request.perFace
      (fun position => (request.pairError_bound later samples first second sheet position).le)).trans_lt facePaid).le
  have estimate := Indexed.normSq_sumFin_le _
    (Aggregate.perTerm target 2) perSheet
  have payment := Aggregate.count_mul_perTerm_lt request.positive 2
  have equal : ((2 : Nat) : Fraction.Rational) ^ 2 * Aggregate.perTerm target 2 =
      ((2 : Nat) : Fraction.Rational) * (((2 : Nat) : Fraction.Rational) * Aggregate.perTerm target 2) := by ring1
  exact estimate.trans_lt (equal.trans_lt payment)

end ClippedRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest

end
