module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularBilinearRequest
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedPartitionBoundary
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! Both occurrences of every regular face, synchronized on one supplied
standard-differential numerical bank. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List (Meshes.PuncturedGridFaces.RegularFace
      bank)}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces}

set_option genInjectivity false in
/-- Two sheetwise bilinear requests with one common subdivision depth and reading stage.

Each sheet receives half the positive target; the retained requests use the same original coarse faces. -/
structure TwoSheetRequest (coarse : (sheet : Fin 2) →
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet)
    (fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
      sheet) (target : Fraction.Rational) where
  /-- The original two requests, each with half the scalar target. -/ entries : Data.Vector.DependentVector (fun sheet :
    Fin 2 => Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request (coarse sheet) (fixed sheet)
    (target / 2))
  /-- The common subdivision depth. -/ depth : Nat
  /-- Every original requested face uses exactly the common depth. -/ depth_eq : ∀ sheet position, ((entries.get
    sheet).entries.get position).depth = depth
  /-- The retained common numerical stage. -/ index : Nat
  /-- The common stage meets both original request indices. -/ index_ge : ∀ sheet, (entries.get sheet).index ≤ index

constructive_injectivity TwoSheetRequest

namespace TwoSheetRequest

variable {coarse : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}

/-- Prepare both sheet requests, raise their face depths to a common maximum and retain a shared sufficient stage. -/
def build (coarse : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains
  sheet)
    (fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
      sheet) (target : Fraction.Rational) (positive : 0 < target) :
    Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target :=
  let initial := Data.Vector.DependentVector.ofFn fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request.build (coarse sheet) (fixed sheet)
    (target / 2)
    (Fraction.Order.Field.div_pos_direct positive (by decide))
  let depths := Data.Vector.DependentVector.ofFn fun sheet : Fin 2 =>
    (initial.get sheet).entries.maximum (fun _ entry => entry.depth)
  let depth := depths.maximum (fun _ value => value)
  have later (sheet : Fin 2) (position : Fin faces.length) :
      ((initial.get sheet).entries.get position).depth ≤ depth := by
    have faceLe := (initial.get sheet).entries.get_le_maximum (fun _ entry => entry.depth) position
    have sheetLe := depths.get_le_maximum (fun _ value => value) sheet
    dsimp only [depths] at sheetLe
    rw [Data.Vector.DependentVector.ofFn_get] at sheetLe
    exact faceLe.trans sheetLe
  let entries := Data.Vector.DependentVector.ofFn fun sheet => (initial.get sheet).atDepth depth (later sheet)
  ⟨entries, depth, (fun sheet position => by
      dsimp only [entries]
      rw [Data.Vector.DependentVector.ofFn_get]
      exact (initial.get sheet).atDepth_entry_depth depth (later sheet) position),
    entries.maximum (fun _ request => request.index), entries.get_le_maximum (fun _ request => request.index)⟩

/-- Every actual face mesh on either sheet has the retained common depth. -/
theorem mesh_depth (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed
  target) (sheet : Fin 2) (position : Fin faces.length) :
    ((request.entries.get sheet).meshes.entries.get position).depth = request.depth := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request.mesh_eq,
    Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest.mesh_depth]
  exact request.depth_eq sheet position

/-- The actual requested meshes retain identical coarse intervals and the
same dyadic depth on matching x-spans. -/
theorem shared_x_mesh {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
      sheet}
    (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      target)
    (firstSheet lastSheet : Fin 2) (first last : Fin faces.length)
    (lowerEq : faces[first.val].cell.box.xLower = faces[last.val].cell.box.xLower)
    (upperEq : faces[first.val].cell.box.xUpper = faces[last.val].cell.box.xUpper) :
    ((request.entries.get firstSheet).meshes.entries.get first).partition.x.intervals =
      ((request.entries.get lastSheet).meshes.entries.get last).partition.x.intervals ∧
    ((request.entries.get firstSheet).meshes.entries.get first).depth =
      ((request.entries.get lastSheet).meshes.entries.get last).depth := by
  constructor
  · rw [(request.entries.get firstSheet).mesh_eq first, (request.entries.get lastSheet).mesh_eq last,
      ((request.entries.get firstSheet).entries.get first).mesh_eq,
      ((request.entries.get lastSheet).entries.get last).mesh_eq]
    exact Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build_x_compatible
      domains cuts firstSheet lastSheet coarseDepth coarseDepth first last lowerEq upperEq
  · rw [request.mesh_depth, request.mesh_depth]

/-- The actual requested meshes retain identical coarse intervals and the
same dyadic depth on matching y-spans. -/
theorem shared_y_mesh {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
  {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
      sheet}
    (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
      target)
    (firstSheet lastSheet : Fin 2) (first last : Fin faces.length)
    (lowerEq : faces[first.val].cell.box.yLower = faces[last.val].cell.box.yLower)
    (upperEq : faces[first.val].cell.box.yUpper = faces[last.val].cell.box.yUpper) :
    ((request.entries.get firstSheet).meshes.entries.get first).partition.y.intervals =
      ((request.entries.get lastSheet).meshes.entries.get last).partition.y.intervals ∧
    ((request.entries.get firstSheet).meshes.entries.get first).depth =
      ((request.entries.get lastSheet).meshes.entries.get last).depth := by
  constructor
  · rw [(request.entries.get firstSheet).mesh_eq first, (request.entries.get lastSheet).mesh_eq last,
      ((request.entries.get firstSheet).entries.get first).mesh_eq,
      ((request.entries.get lastSheet).entries.get last).mesh_eq]
    exact Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build_y_compatible
      domains cuts firstSheet lastSheet coarseDepth coarseDepth first last lowerEq upperEq
  · rw [request.mesh_depth, request.mesh_depth]

/-- The two dependent families of actual face samples from the same retained numerical readings. -/
abbrev Samples (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed
  target) {stage : Nat} (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
  stage) :=
  Data.Vector.DependentVector (fun sheet : Fin 2 =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Samples (request.entries.get sheet).meshes
    cache)

/-- Evaluate both original sheet requests using the supplied common numerical readings. -/
def samples (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse fixed target)
  {stage : Nat} (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage) :
  Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.Samples request cache :=
  Data.Vector.DependentVector.ofFn fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Samples.ofNumerics (request.entries.get
    sheet).meshes cache

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
/-- The two sheetwise finite bilinear errors satisfy the retained coefficient-norm bound with constant 64. -/
theorem bilinear_bound (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse
  fixed target) {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  domains stage}
    (later : request.index ≤ stage) (samples :
      Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.Samples request cache) (left right :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun sheet => FiniteSum.Fin.sumFin (fun position =>
      Topology.Polygon.Stokes.edgeListArea
      (fun vertex => ⟨((samples.get sheet).readings.get position).affine.value left vertex,
        ((samples.get sheet).readings.get position).affine.value right vertex⟩)
      ((request.entries.get sheet).meshes.entries.get position).surface.mesh.triangulation.boundary))) ≤
      Readings.PreparedObservationCoercivity.coefficientNormSq left *
        Readings.PreparedObservationCoercivity.coefficientNormSq right * (64 * target ^ 2) := by
  let value (sheet : Fin 2) : Gaussian := FiniteSum.Fin.sumFin (fun position => Topology.Polygon.Stokes.edgeListArea
    (fun vertex => ⟨((samples.get sheet).readings.get position).affine.value left vertex,
      ((samples.get sheet).readings.get position).affine.value right vertex⟩)
    ((request.entries.get sheet).meshes.entries.get position).surface.mesh.triangulation.boundary)
  let scale := Readings.PreparedObservationCoercivity.coefficientNormSq left *
    Readings.PreparedObservationCoercivity.coefficientNormSq right
  have bounded (sheet : Fin 2) : Data.Gaussian.Norm.Basic.normSq (value sheet) ≤ scale * (64 * (target / 2) ^ 2) :=
    Hyperelliptic.Meshes.PuncturedGrid.RegularBilinearRequest.bilinear_bound
      (request.entries.get sheet) ((request.index_ge sheet).trans later) (samples.get sheet) left right
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin value
    (fun _ => scale * (64 * (target / 2) ^ 2)) bounded
  have half : target / 2 * 2 = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  apply estimate.trans_eq
  rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
  simp only [Nat.cast_ofNat]
  change 2 * (scale * (64 * (target / 2) ^ 2) + (scale * (64 * (target / 2) ^ 2) + 0)) = _
  calc
    _ = scale * (64 * (target / 2 * 2) ^ 2) := by ring1
    _ = _ := by rw [half]

/-- The original partition boundary satisfies the same bilinear bound by exact affine readback. -/
theorem exterior_bound (request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest coarse
  fixed target) {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
  domains stage}
    (later : request.index ≤ stage) (samples :
      Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.Samples request cache) (left right :
      LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun sheet => FiniteSum.Fin.sumFin (fun position =>
      ((request.entries.get sheet).meshes.entries.get position).partition.boundary
        (fun point => ⟨((samples.get sheet).readings.get position).atPoint left point,
          ((samples.get sheet).readings.get position).atPoint right point⟩)
        ((request.entries.get sheet).meshes.entries.get position).depth))) ≤
      Readings.PreparedObservationCoercivity.coefficientNormSq left *
        Readings.PreparedObservationCoercivity.coefficientNormSq right * (64 * target ^ 2) := by
  have estimate := request.bilinear_bound later samples left right
  have equal := FiniteSum.Fin.sumFin_congr (fun sheet : Fin 2 => FiniteSum.Fin.sumFin_congr
    (fun position : Fin faces.length => ((samples.get sheet).readings.get position).bilinear_boundary_eq_exterior left
      right))
  rw [equal] at estimate
  exact estimate

end TwoSheetRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
