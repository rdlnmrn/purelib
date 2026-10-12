module
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Approximation.Rational.Budget.Weighted
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
public import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

public section

/-!
# Requested homogeneous error on the complete regular surface

Allocate the target over every regular face and every retained piece. The
fixed face preflights are shared with observation requests. Spatial meshes
are selected once, and any later common numerical bank supplies the actual
readings and certified budgets, with no coefficient-dependent request.
-/

namespace Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainEnergyRequest (EnergyRequest)
open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_left sumFin_neg)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.Topology.NewtonObservationSurfacePartition (SurfacePartition)
open Purelib.Approximation.Rational.Budget
open Purelib.Algebra
open Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy (LocalMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational} {grid : NewtonGrid
    preparation target radius}
  {observations : ProtectedObservations original} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars} {sheet : Fin 2}

open Purelib.Data in
/-- The dependent surface partitions at the exact original regular-face indices. -/
@[expose] def SurfacePartitions (observations : ProtectedObservations original) (grid : NewtonGrid preparation target
  radius) :=
  Vector.DependentVector (fun position : Fin grid.faces.regulars.length => SurfacePartition observations grid position)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
/-- The dependent local mesh banks owned by the original surface partitions and retained domains. -/
@[expose] def SurfaceMeshes (partitions : SurfacePartitions observations grid)
    (domains : Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars) (sheet : Fin 2) :=
  Vector.DependentVector (fun position => LocalMeshes (partitions.get position) domains sheet)

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
/-- The original face's piece requests at their count-adjusted share of its retained allowance. -/
@[expose] def SurfacePieceRequests (partitions : SurfacePartitions observations grid)
    (coarse : SurfaceMeshes partitions domains sheet) (fixed : Preflights domains sheet)
    (perFace : Fraction.Rational) (position : Fin grid.faces.regulars.length) :=
  Vector.DependentVector (fun piece : Fin (partitions.get position).cuts.boxes.length =>
    Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest (fixed.get position).get ((coarse.get position).entries.get
      piece)
      (Weighted.allowance perFace (Aggregate.countCoordinate (partitions.get position).cuts.boxes.length)))

open Purelib.Data in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A paid surface-wide bank of original piece requests at a common depth and stage.

The nested entries retain their original regular-face and piece indices, preflights and coarse meshes. Exact depth
equalities and stage bounds cover every retained request. -/
structure SurfaceRequest (partitions : SurfacePartitions observations grid)
    (coarse : SurfaceMeshes partitions domains sheet) (fixed : Preflights domains sheet) (error : Fraction.Rational)
      where
  /-- The retained common allowance for every original regular face. -/ perFace : Fraction.Rational
  /-- The retained per-face allowance is strictly positive. -/ positive : 0 < perFace
  /-- The exact original regular-face count times its allowance is below the requested error. -/ paid :
    (grid.faces.regulars.length : Fraction.Rational) * perFace < error
  /-- The original nested energy requests indexed by exact regular-face positions and retained cut-box indices. -/
    entries : Vector.DependentVector (SurfacePieceRequests partitions coarse fixed perFace)
  /-- The retained common refinement depth for every original piece request. -/ depth : Nat
  /-- Each exact retained face-piece request has the same common depth. -/ depth_eq : ∀ position piece, ((entries.get
    position).get piece).depth = depth
  /-- The common retained model stage of the original nested request bank. -/ index : Nat
  /-- Each original face-piece model request is covered by the common stage. -/ index_ge : ∀ position piece,
    ((entries.get position).get piece).modelRequest.index ≤ index

constructive_injectivity SurfaceRequest

namespace SurfaceRequest

variable {partitions : SurfacePartitions observations grid} {coarse : SurfaceMeshes partitions domains sheet}
  {fixed : Preflights domains sheet} {error : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
/-- Allocate and synchronize the original nested surface energy requests.

The target is paid first per face, then per original piece. All initial requests are refined to their exact maximum
depth before the common model stage is computed from the resulting retained bank. -/
@[expose] def build (partitions : SurfacePartitions observations grid) (coarse : SurfaceMeshes partitions domains sheet)
    (fixed : Preflights domains sheet) (error : Fraction.Rational) (positive : 0 < error) :
    SurfaceRequest partitions coarse fixed error := by
  let perFace := Weighted.allowance error (Aggregate.countCoordinate grid.faces.regulars.length)
  have perFacePositive := Weighted.allowance_positive (weight := Aggregate.countCoordinate grid.faces.regulars.length)
    positive (by
    rewrite [Aggregate.countCoordinate_eq]
    exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le grid.faces.regulars.length))
  let initial : Vector.DependentVector (SurfacePieceRequests partitions coarse fixed perFace) :=
    Vector.DependentVector.ofFn fun position => Vector.DependentVector.ofFn fun piece =>
      Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest.build (fixed.get position).get ((coarse.get
        position).entries.get piece)
        (Weighted.allowance perFace (Aggregate.countCoordinate (partitions.get position).cuts.boxes.length))
        (Weighted.allowance_positive perFacePositive (by
          rewrite [Aggregate.countCoordinate_eq]
          exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
  let depth := initial.maximum fun _ row => row.maximum fun _ entry => entry.depth
  have depthGe (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length) :
      ((initial.get position).get piece).depth ≤ depth :=
    ((initial.get position).get_le_maximum (fun _ entry => entry.depth) piece).trans
      (initial.get_le_maximum (fun _ row => row.maximum fun _ entry => entry.depth) position)
  let entries : Vector.DependentVector (SurfacePieceRequests partitions coarse fixed perFace) :=
    Vector.DependentVector.ofFn fun position => Vector.DependentVector.ofFn fun piece =>
      ((initial.get position).get piece).refineDepth depth (depthGe position piece)
  let index := entries.maximum fun _ row => row.maximum fun _ entry => entry.modelRequest.index
  refine ⟨perFace, perFacePositive, Aggregate.count_mul_weighted_allowance_lt positive _, entries, depth, ?_, index, ?_⟩
  · intro position piece
    dsimp only [entries]
    rw [Vector.DependentVector.ofFn_get, Vector.DependentVector.ofFn_get]
    rfl
  · intro position piece
    exact ((entries.get position).get_le_maximum (fun _ entry => entry.modelRequest.index) piece).trans
      (entries.get_le_maximum (fun _ row => row.maximum fun _ entry => entry.modelRequest.index) position)

section
open Purelib.Data
/-- Read the exact refined mesh banks from the retained original surface requests. -/
@[expose] def meshes (request : SurfaceRequest partitions coarse fixed error) : SurfaceMeshes partitions domains sheet
  :=
  Vector.DependentVector.ofFn fun position =>
    ⟨Vector.DependentVector.ofFn fun piece => ((request.entries.get position).get piece).mesh⟩

/-- Each original face-piece mesh is the exact mesh stored by the corresponding retained request. -/
theorem mesh_eq (request : SurfaceRequest partitions coarse fixed error)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length) :
    ((request.meshes.get position).entries.get piece) = ((request.entries.get position).get piece).mesh := by
  unfold meshes
  rw [Vector.DependentVector.ofFn_get, Vector.DependentVector.ofFn_get]

end

open Purelib.Curves.Hyperelliptic in
/-- Every original retained piece mesh has the request's exact common depth. -/
theorem mesh_depth (request : SurfaceRequest partitions coarse fixed error)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length) :
    ((request.meshes.get position).entries.get piece).depth = request.depth := by
  rw [request.mesh_eq, Meshes.PuncturedGrid.DomainEnergyRequest.EnergyRequest.mesh_depth, request.depth_eq]

/-- Refine the original face-piece request to a stage covering its retained common index. -/
@[expose] def atStage (request : SurfaceRequest partitions coarse fixed error) (stage : Nat) (later : request.index ≤
  stage)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length) :=
  ((request.entries.get position).get piece).refineIndex stage ((request.index_ge position piece).trans later)

variable {stage : Nat}

section
open Purelib.Data
open Purelib.Riemann.Topology
/-- The dependent basis-reading banks on the exact retained request meshes and one original numerical cache. -/
@[expose] def Readings (request : SurfaceRequest partitions coarse fixed error) (cache : Numerics domains stage) :=
  Vector.DependentVector (fun position => NewtonObservationSurfaceEnergy.LocalMeshes.Samples (request.meshes.get
    position) cache)

/-- Cache each original face's piece readings from the same retained numerical bank. -/
@[expose] def readings (request : SurfaceRequest partitions coarse fixed error) (cache : Numerics domains stage) :
  request.Readings cache :=
  Vector.DependentVector.ofFn fun position => NewtonObservationSurfaceEnergy.LocalMeshes.Samples.ofNumerics
    (request.meshes.get position) cache

end

variable {cache : Numerics domains stage}

open Purelib.Data in
open Purelib.Riemann.Readings in
/-- The original face's dependent surface budgets on its exact retained basis readings. -/
@[expose] def PieceBudgets (request : SurfaceRequest partitions coarse fixed error) (samples : request.Readings cache)
    (position : Fin grid.faces.regulars.length) :=
  Vector.DependentVector (fun piece : Fin (partitions.get position).cuts.boxes.length =>
    AffineBasisEnergy.AffineBasis.SurfaceBudget ((samples.get position).readings.get piece).affine)

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- The nested original piece budgets with their cached finite surface total.

The entries preserve every retained face and piece index and the exact sampled affine basis; the total equation names
those same nested entries. -/
structure Budget (request : SurfaceRequest partitions coarse fixed error) (samples : request.Readings cache) where
  /-- The dependent nested surface budgets owned by the exact original retained face-piece basis readings. -/ entries :
    Vector.DependentVector (request.PieceBudgets samples)
  /-- The cached total of the exact original nested surface budget entries. -/ total : Fraction.Rational
  /-- The total equals the finite face-by-piece sum of those retained budget totals. -/ total_eq : total =
    FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece => ((entries.get position).get piece).total))

constructive_injectivity Budget

section
open Purelib.Algebra
open Purelib.Data
/-- Cache all exact piece budgets using their retained mesh identities and later original stage. -/
@[expose] def budget (request : SurfaceRequest partitions coarse fixed error) (later : request.index ≤ stage)
    (samples : request.Readings cache) : request.Budget samples :=
  let entries : Vector.DependentVector (request.PieceBudgets samples) :=
    Vector.DependentVector.ofFn fun position => Vector.DependentVector.ofFn fun piece =>
      (request.atStage stage later position piece).surfaceBudgetOn rfl (request.mesh_eq position piece)
        ((samples.get position).readings.get piece)
  ⟨entries, FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece => ((entries.get position).get
    piece).total)), rfl⟩

/-- The nested surface budget total is strictly below its original requested error. -/
theorem budget_total_lt (request : SurfaceRequest partitions coarse fixed error) (later : request.index ≤ stage)
    (samples : request.Readings cache) : (request.budget later samples).total < error := by
  rw [(request.budget later samples).total_eq]
  have faceBound (position : Fin grid.faces.regulars.length) :
      FiniteSum.Fin.sumFin (fun piece => (((request.budget later samples).entries.get position).get piece).total) ≤
        request.perFace := by
    have pieceBound (piece : Fin (partitions.get position).cuts.boxes.length) :
        (((request.budget later samples).entries.get position).get piece).total ≤
          Weighted.allowance request.perFace (Aggregate.countCoordinate (partitions.get position).cuts.boxes.length) :=
            by
      dsimp only [budget]
      rw [Vector.DependentVector.ofFn_get, Vector.DependentVector.ofFn_get]
      exact ((request.atStage stage later position piece).surfaceBudgetOn_total_lt rfl
        (request.mesh_eq position piece) ((samples.get position).readings.get piece)).le
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono _ (fun _ => Weighted.allowance request.perFace
      (Aggregate.countCoordinate (partitions.get position).cuts.boxes.length)) pieceBound
    rw [FiniteSum.Fin.Rational.sum_constant] at bound
    exact bound.trans (Aggregate.count_mul_weighted_allowance_lt request.positive _).le
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono _ (fun _ => request.perFace) faceBound
  rw [FiniteSum.Fin.Rational.sum_constant] at bound
  exact bound.trans_lt request.paid

end

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.LinearAlgebra.Gaussian in
/-- The original signed surface boundary energy is bounded below by the negative requested homogeneous error.

The estimate sums the exact retained face-piece sample budgets at a stage covering all original model requests, using
the same coefficient vector throughout. -/
theorem energy_lower (request : SurfaceRequest partitions coarse fixed error) (later : request.index ≤ stage)
    (samples : request.Readings cache) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    -(coefficientNormSq coefficients * error) ≤
      FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
        ((((request.budget later samples).entries.get position).get piece).sample coefficients).boundaryArea.im / 4)) :=
          by
  let budget := request.budget later samples
  have lower := FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun position =>
    (samples.get position).selected_lower (fun piece => piece) (budget.entries.get position) coefficients)
  have equal : -(coefficientNormSq coefficients * budget.total) =
      FiniteSum.Fin.sumFin (fun position => -(coefficientNormSq coefficients * FiniteSum.Fin.sumFin (fun piece =>
        ((budget.entries.get position).get piece).total))) := by
    rw [budget.total_eq, FiniteSum.Fin.sumFin_neg, FiniteSum.Fin.sumFin_mul_left]
  have normNonnegative : 0 ≤ coefficientNormSq coefficients := by
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational))
      (fun row => Basic.Canonical.normSq (coefficients row))
      (fun row => by
        have scalar := Norm.Basic.normSq_nonneg (coefficients row)
        rw [Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar)
    exact (FiniteSum.Fin.sumFin_zero).symm.trans_le bound
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (request.budget_total_lt later samples).le
    normNonnegative
  have negative := Fraction.Order.Arithmetic.sub_le_sub_left_direct paid 0
  rw [zero_sub, zero_sub] at negative
  exact negative.trans ((le_of_eq equal).trans lower)

end SurfaceRequest
end Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
