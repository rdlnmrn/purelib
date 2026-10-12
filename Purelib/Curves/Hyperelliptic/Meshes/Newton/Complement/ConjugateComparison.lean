module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Integration.Energy.Polygon

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.BilinearCombination
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ObservationLower
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-! The existing shared ownership request pays the conjugate boundary error
on precisely the regular faces retained after Newton annulus excision. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ConjugateComparison

attribute [local congr] FiniteSum.Fin.sumFin_congr

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
  {fixed : RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {energyTarget error :
    Fraction.Rational}
  {lifted : Meshes.LiftedPuncturedGrid grid.punctured}
  {energy : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed energyTarget} {stage : Nat}
    {cache : RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains stage}

variable (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)

/-- Each original remaining-face pair error meets its retained local allowance; excised faces contribute zero. -/
private theorem masked_pairError_bound (request : Surface.ConjugateRequest
  energy error) (later : request.index ≤ stage)
    (samples : energy.Readings cache) (first second : Fin genus)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length) :
    Data.Gaussian.Norm.Basic.normSq (if Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask
      excision position then Surface.ConjugateRequest.pairError samples
      first second position piece else 0) ≤
      Purelib.Approximation.Rational.Budget.Aggregate.perTerm request.perFace (partitions.get
        position).cuts.boxes.length := open Purelib.Approximation in by
  cases Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position with
  | true =>
    exact (Surface.ConjugateRequest.pairError_bound request later samples
      first second position piece).le
  | false =>
      simp only [-eq_self, -iff_self, if_neg (by decide : ¬ false = true), Gaussian.Norm.Basic.normSq_zero]
      have positive : 0 < request.perFace := by
        rw [request.perFace_eq]
        exact Rational.Budget.Aggregate.perTerm_positive request.positive _
      exact (Rational.Budget.Aggregate.perTerm_positive positive _).le

/-- The aggregate original pair error over the actual unexcised faces is strictly below the retained target. -/
theorem remaining_pairError_bound (request : Surface.ConjugateRequest
  energy error) (later : request.index ≤ stage)
    (samples : energy.Readings cache) (first second : Fin genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece => (if
      Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
      Surface.ConjugateRequest.pairError samples first second position
      piece else 0)))) < error := open Purelib.Approximation in by
  have perFacePositive : 0 < request.perFace := by
    rw [request.perFace_eq]
    exact Rational.Budget.Aggregate.perTerm_positive request.positive _
  have faceBound (position : Fin grid.faces.regulars.length) :
      Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun piece => (if
        Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
        Surface.ConjugateRequest.pairError samples first second position
        piece else 0))) ≤ request.perFace := by
    have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _
      (Rational.Budget.Aggregate.perTerm request.perFace (partitions.get position).cuts.boxes.length)
      (fun piece => Hyperelliptic.Meshes.Newton.Complement.ConjugateComparison.masked_pairError_bound excision request
        later samples first second position piece)
    have payment := Rational.Budget.Aggregate.count_mul_perTerm_lt perFacePositive (partitions.get
      position).cuts.boxes.length
    have equal : ((partitions.get position).cuts.boxes.length : Fraction.Rational) ^ 2 *
        Rational.Budget.Aggregate.perTerm request.perFace (partitions.get position).cuts.boxes.length =
        ((partitions.get position).cuts.boxes.length : Fraction.Rational) *
          (((partitions.get position).cuts.boxes.length : Fraction.Rational) *
            Rational.Budget.Aggregate.perTerm request.perFace (partitions.get position).cuts.boxes.length) := by ring1
    exact (estimate.trans_lt (equal.trans_lt payment)).le
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le _ request.perFace faceBound
  have payment := Rational.Budget.Aggregate.count_mul_perTerm_lt request.positive grid.faces.regulars.length
  have equal : (grid.faces.regulars.length : Fraction.Rational) ^ 2 * request.perFace =
      (grid.faces.regulars.length : Fraction.Rational) * ((grid.faces.regulars.length : Fraction.Rational) *
        Rational.Budget.Aggregate.perTerm error grid.faces.regulars.length) := by rw [request.perFace_eq]; ring1
  exact estimate.trans_lt (equal.trans_lt payment)

/-- The original masked combined error equals the conjugate-weighted sum of its retained component-pair errors. -/
theorem remaining_combinedError_eq (samples : energy.Readings cache) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (position : Fin grid.faces.regulars.length) (piece : Fin (partitions.get position).cuts.boxes.length) :
    (if Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
      Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.combinedError samples coefficients position piece else 0)
      =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients
        first) * coefficients second *
        (if Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
          Surface.ConjugateRequest.pairError samples first second position
          piece else 0))) := by
  cases Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position with
  | true =>
    exact Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.combinedError_eq samples coefficients position piece
  | false =>
      change (0 : Gaussian.Basic.Canonical) =
        FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin
          (fun second => Data.Gaussian.Basic.conj (coefficients first) * coefficients second * 0))
      have each (first : Fin genus) : FiniteSum.Fin.sumFin
          (fun second => Data.Gaussian.Basic.conj (coefficients first) * coefficients second * 0) = 0 :=
        (FiniteSum.Fin.sumFin_congr (fun second => Gaussian.Basic.mul_zero _)).trans
          FiniteSum.Fin.sumFin_zero
      exact ((FiniteSum.Fin.sumFin_congr each).trans FiniteSum.Fin.sumFin_zero).symm

/-- The complete original remaining-face error equals the finite coefficient combination of the actual pair-error
totals. -/
theorem remaining_total_combinedError_eq (samples : energy.Readings cache) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece => (if
      Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
      Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.combinedError samples coefficients position piece else
      0))) =
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj (coefficients
        first) * coefficients second *
        FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece => (if
          Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
          Surface.ConjugateRequest.pairError samples first second position
          piece else 0))))) := by
  rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_congr (fun piece =>
    Hyperelliptic.Meshes.Newton.Complement.ConjugateComparison.remaining_combinedError_eq excision samples coefficients
    position piece))]
  rw [FiniteSum.Fin.sumFin_congr (fun position => Periods.BilinearCombination.sumFin_combination
    (fun row => Data.Gaussian.Basic.conj (coefficients row)) coefficients (fun piece first second => (if
      Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
      Surface.ConjugateRequest.pairError samples first second position
      piece else 0)))]
  exact Periods.BilinearCombination.sumFin_combination (fun row => Data.Gaussian.Basic.conj (coefficients row))
    coefficients _

/-- The original remaining-face combined error is bounded by genus squared, the squared coefficient norm and the
retained target. -/
theorem remaining_combinedError_bound (request : Surface.ConjugateRequest
  energy error) (later : request.index ≤ stage)
    (samples : energy.Readings cache) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece => (if
      Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
      Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.combinedError samples coefficients position piece else
      0)))) ≤
      (genus : Fraction.Rational) ^ 2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
        error := by
  rw [Hyperelliptic.Meshes.Newton.Complement.ConjugateComparison.remaining_total_combinedError_eq excision]
  have estimate := Periods.BilinearCombination.combination_bound (fun row => Data.Gaussian.Basic.conj (coefficients
    row)) coefficients
    (fun first second => FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece => (if
      Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
      Surface.ConjugateRequest.pairError samples first second position
      piece else 0))))
    (fun first second => (Hyperelliptic.Meshes.Newton.Complement.ConjugateComparison.remaining_pairError_bound excision
      request later samples first second).le)
  rw [FiniteSum.Fin.sumFin_congr (fun row => Gaussian.Norm.Basic.normSq_conj (coefficients row))] at estimate
  have coefficientNorm := FiniteSum.Fin.sumFin_congr
    (fun row : Fin genus => Gaussian.Norm.Basic.normSq_eq_canonical (coefficients row))
  rw [coefficientNorm] at estimate
  exact estimate.trans_eq (by unfold Readings.PreparedObservationCoercivity.coefficientNormSq; ring1)

/-- The actual cached energy boundaries and retained local-owner boundaries differ within the paid bound on precisely
the original unexcised faces. -/
theorem remaining_boundary_error_bound (request : Surface.ConjugateRequest
  energy error) (later : request.index ≤ stage)
    (samples : energy.Readings cache) (budget : Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest.Budget energy
      samples) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun piece =>
      if Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then
      (((budget.entries.get position).get piece).sample coefficients).boundaryArea -
        ((energy.meshes.get position).entries.get piece).pieces.localBoundary
          (fun column row point => Energy.Polygon.energyPrimitivePoint (FiniteSum.Fin.sumFin (fun rowIndex =>
            coefficients rowIndex * (cache.atDomain position sheet rowIndex).primitives.value column row point)))
          ((energy.meshes.get position).entries.get piece).depth else 0))) ≤
      (genus : Fraction.Rational) ^ 2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 *
        error := by
  rw [FiniteSum.Fin.sumFin_congr (fun position => FiniteSum.Fin.sumFin_congr (fun piece =>
    congrArg (fun value : Gaussian.Basic.Canonical => if
      Hyperelliptic.Meshes.Newton.Complement.ObservationLower.remainingFaceMask excision position then value else 0)
      (Hyperelliptic.Meshes.Newton.Surface.ConjugateCombination.sample_error_eq samples budget coefficients position
        piece)))]
  exact Hyperelliptic.Meshes.Newton.Complement.ConjugateComparison.remaining_combinedError_bound excision request later
    samples coefficients

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Complement.ConjugateComparison
