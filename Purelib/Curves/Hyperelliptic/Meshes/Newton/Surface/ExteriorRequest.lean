module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Polynomial.Rectangle.ClippedExteriorTolerance
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-!
# Requested stitched exteriors of every regular-surface piece

All model seams and corner errors are paid before the complete surface is
replaced by its piece exteriors. Joining edges on those exteriors remain in
the cached assemblies. A minimum index keeps prior ownership requests valid.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational} {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {observations : RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames grid.faces.regulars} {sheet : Fin
    2}
  {partitions : Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid} {coarse :
    Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {energyTarget :
    Fraction.Rational}

namespace ExteriorRequest

/-- The dependent vector of original piece exterior requests at one retained face allowance. -/
@[expose] def ExteriorPieces (energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed
  energyTarget)
    (perFace : Fraction.Rational) (position : Fin grid.faces.regulars.length) :=
  Data.Vector.DependentVector (fun piece : Fin (partitions.get position).cuts.boxes.length =>
    Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest.ConjugateExteriorRequest (fixed.get position).get
      ((energy.meshes.get position).entries.get piece)
      (Rational.Budget.Aggregate.perTerm perFace (partitions.get position).cuts.boxes.length))

end ExteriorRequest

set_option genInjectivity false in
/-- A count-paid request for all original regular-surface piece exteriors.

It retains each actual piece request and a common index above the energy stage, supplied floor and every local model
stage. -/
structure ExteriorRequest (energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed
  energyTarget) (error : Fraction.Rational) (minimum : Nat) where
  /-- The requested whole-surface error is positive. -/ positive : 0 < error
  /-- The retained local face allowance. -/ perFace : Fraction.Rational
  /-- The face allowance is the original face-count target allocation. -/ perFace_eq : perFace =
    Rational.Budget.Aggregate.perTerm error grid.faces.regulars.length
  /-- The actual retained exterior requests for every original face and piece. -/ entries : Data.Vector.DependentVector
    (Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest.ExteriorPieces energy perFace)
  /-- The cached common sufficient exterior stage. -/ index : Nat
  /-- The common stage is at least the original energy request stage. -/ energy_le : energy.index ≤ index
  /-- The common stage respects the supplied floor. -/ minimum_le : minimum ≤ index
  /-- Every retained piece request is valid at the common stage. -/ index_ge : ∀ position piece, ((entries.get
    position).get piece).models.index ≤ index

constructive_injectivity ExteriorRequest

namespace ExteriorRequest

variable {energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed energyTarget} {error :
  Fraction.Rational} {minimum : Nat}

/-- Allocate the original face and piece allowances and retain all local requests with one sufficient common stage. -/
@[expose] def build (energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed energyTarget)
  (error : Fraction.Rational) (positive : 0 < error)
    (minimum : Nat) : ExteriorRequest energy error minimum :=
  let perFace := Rational.Budget.Aggregate.perTerm error grid.faces.regulars.length
  let entries : Data.Vector.DependentVector (Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest.ExteriorPieces energy
    perFace) :=
    Data.Vector.DependentVector.ofFn fun position => Data.Vector.DependentVector.ofFn fun piece =>
      Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest.ConjugateExteriorRequest.build (fixed.get
        position).get ((energy.meshes.get position).entries.get piece)
        (Rational.Budget.Aggregate.perTerm perFace (partitions.get position).cuts.boxes.length)
        (Rational.Budget.Aggregate.perTerm_positive (Rational.Budget.Aggregate.perTerm_positive positive _) _)
  let floor := entries.maximum fun _ row => row.maximum fun _ request => request.models.index
  ⟨positive, perFace, rfl, entries, max (max energy.index minimum) floor,
    (Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_left _ _), (Nat.Order.le_max_right _ _).trans
      (Nat.Order.le_max_left _ _),
    fun position piece =>
      (((entries.get position).get_le_maximum (fun _ request => request.models.index) piece).trans
        (entries.get_le_maximum (fun _ row => row.maximum fun _ request => request.models.index) position)).trans
          (Nat.Order.le_max_right _ _)⟩

variable {stage : Nat} {cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage}

/-- The dependent vector of actual original piece energy assemblies at the retained numerical cache and coefficient
vector. -/
@[expose] def Assemblies (energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed
  energyTarget) (cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :=
  Data.Vector.DependentVector (fun position => Data.Vector.DependentVector (fun piece : Fin (partitions.get
    position).cuts.boxes.length =>
    Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest.ConjugateExteriorRequest.EnergyAssembly
      (cache.atDomain position sheet)
      ((energy.meshes.get position).entries.get piece) coefficients))

/-- Assemble each original piece once using the shared numerical cache and conjugate coefficient pair. -/
@[expose] def assemblies (energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed
  energyTarget) (cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
      Assemblies energy cache coefficients :=
  Data.Vector.DependentVector.ofFn fun position => Data.Vector.DependentVector.ofFn fun piece =>
    Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly.build ((energy.meshes.get
      position).entries.get piece)
      (fun column row point =>
        ⟨sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj ((cache.atDomain
          position sheet i).anchors.alignedValue
          (cache.atDomain position sheet i).offsets column row point)),
          FiniteSum.Fin.sumFin (fun i => coefficients i * (cache.atDomain position sheet i).anchors.alignedValue
            (cache.atDomain position sheet i).offsets column row point)⟩)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest in
/-- The boundary is assembled once from the retained side and corner caches. -/
@[expose] def exterior (assemblies : Assemblies
  energy cache coefficients) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece => ((assemblies.get position).get
    piece).exterior))

/-- The original count-squared local allocation fits its positive whole target. -/
private theorem payment {count : Nat} {target : Fraction.Rational} (positive : 0 < target) :
    (count : Fraction.Rational) ^ 2 * Rational.Budget.Aggregate.perTerm target count ≤ target :=
  (le_of_eq (by ring1)).trans (Rational.Budget.Aggregate.count_mul_perTerm_lt positive count).le

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest in
/-- The original local energy and retained piece exteriors differ by the paid homogeneous whole-surface bound. -/
theorem error_bound (request : ExteriorRequest energy error minimum)
  (later : request.index ≤ stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (assemblies :
      Assemblies energy cache coefficients) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.localEnergyArea energy cache
      coefficients - exterior assemblies) ≤
      (genus : Fraction.Rational) ^ 2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
        error := by
  let factor := (genus : Fraction.Rational) ^ 2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
    ^ 2
  have factorNonnegative : 0 ≤ factor := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.sq_nonneg_direct _) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have perFacePositive : 0 < request.perFace := by
    rw [request.perFace_eq]
    exact Rational.Budget.Aggregate.perTerm_positive request.positive _
  let difference := fun position piece =>
    ((assemblies.get position).get piece).localTotal - ((assemblies.get position).get piece).exterior
  have faceBound (position : Fin grid.faces.regulars.length) :
      Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (difference position)) ≤ factor * request.perFace := by
    have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le (difference position)
      (factor * Rational.Budget.Aggregate.perTerm request.perFace (partitions.get position).cuts.boxes.length)
      (fun piece =>
        Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest.ConjugateExteriorRequest.weighted_bound
        ((request.entries.get position).get piece) ((request.index_ge position piece).trans later)
        (cache.atDomain position sheet) coefficients ((assemblies.get position).get piece))
    apply estimate.trans
    calc
      _ = factor * (((partitions.get position).cuts.boxes.length : Fraction.Rational) ^ 2 *
        Rational.Budget.Aggregate.perTerm request.perFace (partitions.get position).cuts.boxes.length) := by ring1
      _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (payment perFacePositive) factorNonnegative
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ (factor * request.perFace) faceBound
  have paid : (grid.faces.regulars.length : Fraction.Rational) ^ 2 * (factor * request.perFace) ≤ factor * error := by
    rw [request.perFace_eq]
    calc
      _ = factor * ((grid.faces.regulars.length : Fraction.Rational) ^ 2 *
        Rational.Budget.Aggregate.perTerm error grid.faces.regulars.length) := by ring1
      _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (payment request.positive) factorNonnegative
  have total := estimate.trans paid
  have equal : FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (difference position)) =
    Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.localEnergyArea energy cache coefficients -
    exterior assemblies := by
    rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_sub _ _), FiniteSum.Fin.sumFin_sub]
    apply congrArg (fun localTotal => localTotal - _)
    apply FiniteSum.Fin.sumFin_congr
    intro position
    apply FiniteSum.Fin.sumFin_congr
    intro piece
    exact ((assemblies.get position).get piece).raw_localTotal_eq (cache.atDomain position sheet) coefficients
  rw [equal] at total
  exact total

/-- Prepare the original exterior requests at the homogeneous error target determined by the positive energy allowance.
-/
@[expose] def forEnergyAllowance (energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed
  energyTarget)
    (allowance : Fraction.Rational) (positive : 0 < allowance) (minimum : Nat) :
    ExteriorRequest energy
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus allowance) minimum
      :=
  build energy _
    (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_positive positive) minimum

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest in
/-- The positive surface margin survives both ownership and seam/corner
losses at one common numerical sample. Piece exteriors keep their joining
edges; joining different pieces and faces remains a separate comparison. -/
theorem energy_lower {ownershipAllowance exteriorAllowance : Fraction.Rational}
    (ownership : ConjugateRequest energy
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus ownershipAllowance))
    (request : ExteriorRequest energy
      (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus exteriorAllowance)
      ownership.index)
    (ownershipPositive : 0 < ownershipAllowance) (exteriorPositive : 0 < exteriorAllowance)
    (later : request.index ≤ stage) (samples : energy.Readings cache)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (face :
      Topology.BranchedCover.Double.Attachment.Face)
    (assemblies : Assemblies energy cache
      coefficients) :
    (Topology.NewtonObservationSurfaceLower.surfaceLowerConstant observations - energyTarget - ownershipAllowance -
      exteriorAllowance) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤
      (exterior assemblies).im / 4 := by
  have close := request.error_bound later coefficients assemblies
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row))
    exact (FiniteSum.Fin.sumFin_zero).symm.trans_le bound
  have squared : Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.localEnergyArea
    energy cache coefficients - exterior assemblies)
    ≤
      (4 * (exteriorAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)) ^ 2 := by
    apply close.trans
    calc
      _ = ((genus : Fraction.Rational) ^ 2 *
        Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget genus exteriorAllowance)
        * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 := by
        ring1
      _ ≤ (4 * exteriorAllowance) ^ 2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.energyAllowanceTarget_paid exteriorPositive)
            (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ = _ := by ring1
  have comparison := Topology.PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le
    (Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.localEnergyArea energy cache coefficients)
      (exterior assemblies) (exteriorAllowance *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
    (Fraction.Order.Arithmetic.mul_nonneg_direct exteriorPositive.le normNonnegative) squared
  have lower := Hyperelliptic.Meshes.Newton.Surface.LocalEnergy.ConjugateRequest.local_energy_lower ownership
    ownershipPositive (request.minimum_le.trans later) samples coefficients face
  have paid := (Fraction.Order.Arithmetic.sub_le_sub_direct lower
    (le_rfl (a := exteriorAllowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))).trans
      comparison
  exact (le_of_eq (by ring1)).trans paid

end ExteriorRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface
