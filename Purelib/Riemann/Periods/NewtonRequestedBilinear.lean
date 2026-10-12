module
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Riemann.Integration.PrimitiveBasis
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearRequest
import Purelib.Tactic.Ring

@[expose] public section

/-! Requested two-function wedge control over every retained observation
piece. Both the growing local face counts and the complete piece count are
paid by the existing request on the same supplied numerical bank. -/

namespace Purelib.Riemann.Periods.NewtonRequestedBilinear

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Riemann.RootContinuation.NewtonObservationPartitions.ProtectedObservations (GridPartitions)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy (LocalMeshes)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics Samples)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights Request)
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
    grid.faces.regulars} {partitions : GridPartitions observations grid} {sheet : Fin 2}
  {coarse : LocalMeshes partitions domains sheet} {fixed : Preflights domains sheet} {totalTarget :
    Rational}
  {stage : Nat} {cache : Numerics domains stage}

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Topology in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Bound the sum of two-function wedge areas on every retained observation piece.

The existing request pays both each local face count and the complete piece count on the same numerical bank, giving 64
times the target squared times the two coefficient squared norms. -/
theorem bilinear_bound (request : Request coarse fixed totalTarget) (later : request.index ≤ stage)
    (samples : Samples request.meshes cache) (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun piece => Polygon.Stokes.edgeListArea
      (fun vertex => ⟨(samples.readings.get piece).affine.value left vertex,
        (samples.readings.get piece).affine.value right vertex⟩)
      (request.meshes.entries.get piece).surface.mesh.triangulation.boundary)) ≤
      coefficientNormSq left * coefficientNormSq right * (64 * totalTarget ^ 2) := by
  let value (piece : Fin partitions.indices.length) : Gaussian := Polygon.Stokes.edgeListArea
    (fun vertex => ⟨(samples.readings.get piece).affine.value left vertex,
      (samples.readings.get piece).affine.value right vertex⟩)
    (request.meshes.entries.get piece).surface.mesh.triangulation.boundary
  let scale := coefficientNormSq left * coefficientNormSq right
  have localBound (piece : Fin partitions.indices.length) :
      Data.Gaussian.Norm.Basic.normSq (value piece) ≤ scale * (64 * request.perPiece ^ 2) :=
    (request.atStage stage later piece).bilinear_bound_on rfl (request.mesh_eq piece)
      (samples.readings.get piece) left right
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin value
    (fun _ => scale * (64 * request.perPiece ^ 2)) localBound
  rw [FiniteSum.Fin.Rational.sum_constant] at estimate
  have nonnegative : 0 ≤ (partitions.indices.length : Rat.Fraction.Rational) * request.perPiece :=
    Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) request.positive.le
  have squares : ((partitions.indices.length : Rat.Fraction.Rational) * request.perPiece) ^ 2 ≤ totalTarget ^ 2 := by
    have bound := Rat.Fraction.Order.Arithmetic.mul_le_mul_direct request.paid.le request.paid.le
      nonnegative (nonnegative.trans request.paid.le)
    exact (le_of_eq (by ring1)).trans (bound.trans_eq (by ring1))
  have scaleNonnegative : 0 ≤ scale * 64 := Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (Integration.PrimitiveBasis.coefficientNorm_nonnegative left)
      (Integration.PrimitiveBasis.coefficientNorm_nonnegative right)) (by decide +kernel)
  exact estimate.trans ((le_of_eq (by ring1)).trans
    ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squares scaleNonnegative).trans_eq (by ring1)))

end Purelib.Riemann.Periods.NewtonRequestedBilinear
