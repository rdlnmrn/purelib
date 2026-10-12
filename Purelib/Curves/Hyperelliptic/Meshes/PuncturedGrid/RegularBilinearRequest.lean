module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PrimitiveBasis
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBilinearRequest

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! Requested two-function boundary control over every retained regular
face on the chosen sheet, using one supplied standard-differential bank. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularBilinearRequest

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List (Meshes.PuncturedGridFaces.RegularFace
      bank)}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces} {sheet : Fin 2}
  {coarse : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet} {fixed :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet} {target :
    Fraction.Rational}
  {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}

/-- The finite sum of a constant rational equals the count times that constant. -/
private theorem sum_constant (size : Nat) (value : Fraction.Rational) :
    FiniteSum.Fin.sumFin (fun _ : Fin size => value) = (size : Fraction.Rational) * value := by
  induction size with
  | zero => change 0 = 0 * value; ring1
  | succ size ih => rw [FiniteSum.Fin.sumFin_succ, ih, Nat.cast_succ]; ring1

/-- The aggregate original regular-face boundary area is bounded by the two coefficient norms times sixty-four squared
targets.

Use the supplied shared differential bank, the retained per-face payment and the actual face count. -/
theorem bilinear_bound (request : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Request coarse
  fixed target) (later : request.index ≤ stage)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Samples request.meshes cache) (left
      right : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun position => Topology.Polygon.Stokes.edgeListArea
      (fun vertex => ⟨(samples.readings.get position).affine.value left vertex,
        (samples.readings.get position).affine.value right vertex⟩)
      (request.meshes.entries.get position).surface.mesh.triangulation.boundary)) ≤
      Readings.PreparedObservationCoercivity.coefficientNormSq left *
        Readings.PreparedObservationCoercivity.coefficientNormSq right * (64 * target ^ 2) := by
  let value (position : Fin faces.length) : Gaussian := Topology.Polygon.Stokes.edgeListArea
    (fun vertex => ⟨(samples.readings.get position).affine.value left vertex,
      (samples.readings.get position).affine.value right vertex⟩)
    (request.meshes.entries.get position).surface.mesh.triangulation.boundary
  let scale := Readings.PreparedObservationCoercivity.coefficientNormSq left *
    Readings.PreparedObservationCoercivity.coefficientNormSq right
  have localBound (position : Fin faces.length) : Data.Gaussian.Norm.Basic.normSq (value position) ≤ scale * (64 *
    request.perFace ^ 2) :=
    (request.atStage stage later position).bilinear_bound_on rfl (request.mesh_eq position)
      (samples.readings.get position) left right
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin value
    (fun _ => scale * (64 * request.perFace ^ 2)) localBound
  rw [Hyperelliptic.Meshes.PuncturedGrid.RegularBilinearRequest.sum_constant] at estimate
  have nonnegative : 0 ≤ (faces.length : Fraction.Rational) * request.perFace :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) request.positive.le
  have squares : ((faces.length : Fraction.Rational) * request.perFace) ^ 2 ≤ target ^ 2 := by
    have bound := Fraction.Order.Arithmetic.mul_le_mul_direct request.paid.le request.paid.le
      nonnegative (nonnegative.trans request.paid.le)
    exact (le_of_eq (by ring1)).trans (bound.trans_eq (by ring1))
  have scaleNonnegative : 0 ≤ scale * 64 := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Riemann.Integration.PrimitiveBasis.coefficientNorm_nonnegative left)
      (Riemann.Integration.PrimitiveBasis.coefficientNorm_nonnegative right)) (by decide +kernel)
  exact estimate.trans ((le_of_eq (by ring1)).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squares scaleNonnegative).trans_eq (by ring1)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularBilinearRequest
