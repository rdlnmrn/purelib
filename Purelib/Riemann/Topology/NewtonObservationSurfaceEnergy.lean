module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
public import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Polynomial.Dense.Basic
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Readings.RectangularObservationEnergy
import Mathlib.Order.Basic

@[expose] public section

/-!
# Homogeneous error bounds on complete regular-face subdivisions

The same retained face domains and numerical bank used by observation and
period requests supply every piece, including the complementary pieces.
Their affine energies are nonnegative. Thus each complementary boundary
energy is bounded below by its paid homogeneous approximation error; no
complementary region is silently discarded.
-/

namespace Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationMesh)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero sumFin_mul_left)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonObservationSurfacePartition (SurfacePartition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {position : Fin grid.faces.regulars.length}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
set_option genInjectivity false in
/-- Retained observation meshes on all pieces of one original regular-face partition.

Each mesh uses the same original face domain and sheet, preserving its exact cut-box index and domain-cut owner. -/
structure LocalMeshes (partition : SurfacePartition observations grid position)
    (domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars) (sheet : Fin 2) where
  /-- The dependent meshes on the exact original cut boxes of this retained regular face. -/ entries :
    Vector.DependentVector (fun piece : Fin partition.cuts.boxes.length =>
    ObservationMesh ((domains.get position).domain sheet).cuts (partition.cuts.boxes[piece.val]'piece.isLt))

constructive_injectivity LocalMeshes

namespace LocalMeshes

variable {partition : SurfacePartition observations grid position} {sheet : Fin 2}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Gaussian in
/-- Build all original local surface meshes with one retained point list and common depth.

The supplied inclusion proof covers each exact piece's original rectangle points; the construction preserves the face
domain and partition containment certificates. -/
def build (partition : SurfacePartition observations grid position)
    (domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars) (sheet : Fin 2)
    (points : List Basic.Canonical)
    (includes : ∀ (piece : Fin partition.cuts.boxes.length) point,
      point ∈ ((domains.get position).domain sheet).cuts.rectanglePoints (partition.cuts.boxes[piece.val]'piece.isLt) →
        point ∈ points) (depth : Nat) :
    LocalMeshes partition domains sheet :=
  ⟨Vector.DependentVector.ofFn fun piece =>
    let box := partition.cuts.boxes[piece.val]'piece.isLt
    let domain := (domains.get position).domain sheet
    ObservationMesh.build domain.cuts box (partition.cuts.proper (List.getElem_mem piece.isLt))
      (fun _ inside => domain.covers ((partition.cuts.refines (List.getElem_mem piece.isLt)).contains inside))
      points (includes piece) depth⟩

variable {stage : Nat}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
set_option genInjectivity false in
/-- The original basis readings on retained partition-piece meshes from one shared numerical cache. -/
structure Samples (meshes : LocalMeshes partition domains sheet) (cache : Numerics domains stage) where
  /-- The cached basis readings from the original numerical bank on each exact piece surface. -/ readings :
    Vector.DependentVector (fun piece : Fin partition.cuts.boxes.length =>
    Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings (cache.atDomain position sheet) (meshes.entries.get
      piece).surface)

constructive_injectivity Samples

namespace Samples

variable {meshes : LocalMeshes partition domains sheet} {cache : Numerics domains stage}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- Cache each exact piece's basis readings from the same original face-domain numerical bank. -/
def ofNumerics (meshes : LocalMeshes partition domains sheet) (cache : Numerics domains stage) : Samples meshes cache :=
  ⟨Vector.DependentVector.ofFn fun piece => Meshes.PuncturedGrid.DomainBasisEnergy.BasisReadings.build
    (cache.atDomain position sheet) (meshes.entries.get piece).surface⟩

variable {samples : Samples meshes cache}

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Readings in
/-- The original sampled affine energy on one retained partition piece is nonnegative. -/
theorem piece_affine_nonnegative (samples : Samples meshes cache) (piece : Fin partition.cuts.boxes.length)
    (budget : AffineBasisEnergy.AffineBasis.SurfaceBudget (samples.readings.get piece).affine)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    0 ≤ (budget.sample coefficients).affineEnergy := by
  rw [(budget.sample coefficients).affineEnergy_eq]
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => (0 : Fraction.Rational)) _
    (fun face => Fraction.Order.Arithmetic.mul_nonneg_direct
    ((meshes.entries.get piece).faceArea_positive face).le
    (Norm.Basic.normSq_nonneg ((budget.sample coefficients).faceCoefficient face)))
  exact (FiniteSum.Fin.sumFin_zero).symm.trans_le bound

open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Readings in
/-- A retained piece's signed boundary energy is bounded below by its negative homogeneous error budget. -/
theorem piece_lower (samples : Samples meshes cache) (piece : Fin partition.cuts.boxes.length)
    (budget : AffineBasisEnergy.AffineBasis.SurfaceBudget (samples.readings.get piece).affine)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    -(coefficientNormSq coefficients * budget.total) ≤ (budget.sample coefficients).boundaryArea.im / 4 := by
  have nonnegative := samples.piece_affine_nonnegative piece budget coefficients
  have bound := Fraction.Order.Arithmetic.sub_le_sub_direct nonnegative
    (le_rfl (a := coefficientNormSq coefficients * budget.total))
  rw [zero_sub] at bound
  exact bound.trans (budget.energy_lower coefficients)

open Purelib.Algebra in
open Purelib.Data in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Riemann.Readings in
/-- The selected original pieces' boundary energies pay the negative sum of their retained homogeneous errors.

The supplied finite selection and dependent budget bank keep the same original piece indices, numerical readings and
coefficient vector. -/
theorem selected_lower (samples : Samples meshes cache) {count : Nat}
    (pieces : Fin count → Fin partition.cuts.boxes.length)
    (budgets : Vector.DependentVector (fun index => AffineBasisEnergy.AffineBasis.SurfaceBudget (samples.readings.get
      (pieces index)).affine))
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    -(coefficientNormSq coefficients * FiniteSum.Fin.sumFin (fun index => (budgets.get index).total)) ≤
      FiniteSum.Fin.sumFin (fun index => ((budgets.get index).sample coefficients).boundaryArea.im / 4) := by
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono _ _
    (fun index => samples.piece_lower (pieces index) (budgets.get index) coefficients)
  apply le_trans (le_of_eq ?_) bound
  rw [FiniteSum.Fin.sumFin_neg, FiniteSum.Fin.sumFin_mul_left]

end Samples
end LocalMeshes
end Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
