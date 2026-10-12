module
import Purelib.Algebra.FiniteSum.Fin.Rational
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedAssembly
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReadingTargetRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

public section

/-! One finite request controls the total stitched exterior on both sheets,
homogeneously in both coefficient vectors, using the supplied numerical bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest

open Purelib.Algebra
open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib
open Purelib.Riemann
open Purelib.RootIsolation

attribute [local congr] FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {faces : List (Meshes.PuncturedGridFaces.RegularFace
      bank)}
    {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces}

set_option genInjectivity false in
/-- A coefficient-independent request for the complete stitched exterior of both original sheets.

It retains the initial local boundary request, fixed exterior-reading caps and their exact refined preparation with a
paid total charge. -/
structure ExteriorBoundaryRequest (coarse : (sheet : Fin 2) →
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet)
    (fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
      sheet) (target : Fraction.Rational) where
  /-- The retained local boundary allowance. -/ localTarget : Fraction.Rational
  /-- The local boundary allowance is one quarter of the supplied target. -/ localTarget_eq : localTarget = target / 4
  /-- The retained positive basis-pair exterior allowance. -/ pairTarget : Fraction.Rational
  /-- The basis-pair allowance is positive. -/ pair_positive : 0 < pairTarget
  /-- The complete original face-count and genus-weighted charge fits the supplied target. -/ paid : 2 * localTarget + 8
    * (faces.length : Fraction.Rational) ^ 2 * (genus : Fraction.Rational) ^ 2 * pairTarget ≤ target
  /-- The initial local boundary request on the original coarse meshes and fixed preflights. -/ initial :
    Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest coarse fixed localTarget
  /-- The retained basis-pair reading caps for those original meshes. -/ caps :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.RegularMeshes.TwoSheetRequest.ExteriorCaps initial.energy
    pairTarget
  /-- The refined local request retaining the same original meshes. -/ prepared :
    Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest coarse fixed localTarget
  /-- The refined preparation is exactly the initial request tightened by the retained caps. -/ prepared_eq : prepared =
    initial.limitReadings caps.values caps.positive
  /-- Every original face and basis-pair exterior error meets the retained pair target at a sufficient stage. -/
    pair_bound : ∀ stage (later : prepared.energy.index ≤ stage) sheet position first second,
    Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.TwoSheetRequest.pairExteriorBound prepared.energy stage
      later sheet position first second ≤ pairTarget

constructive_injectivity ExteriorBoundaryRequest

namespace ExteriorBoundaryRequest

variable {coarse : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes domains sheet}
  {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}

/-- Allocate the original local and pair targets, retain their fixed reading caps and refine the original request with
its total payment certificate. -/
@[expose] def build (coarse : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes
  domains sheet)
    (fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
      sheet) (target : Fraction.Rational) (positive : 0 < target) :
    Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest coarse fixed target := by
  let localTarget := target / 4
  have localPositive : 0 < localTarget := Fraction.Order.Field.div_pos_direct positive (by decide)
  let weight := 8 * (Rational.Budget.Aggregate.countCoordinate faces.length) ^ 2 *
    (Rational.Budget.Aggregate.countCoordinate genus) ^ 2
  have weightEq : weight = 8 * (faces.length : Fraction.Rational) ^ 2 * (genus : Fraction.Rational) ^ 2 := by
    simp only [weight, Rational.Budget.Aggregate.countCoordinate_eq, -eq_self, -iff_self]
    rfl
  have weightNonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
      (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  let pairTarget := Rational.Budget.Weighted.allowance (target / 2) weight
  have pairPositive : 0 < pairTarget := Rational.Budget.Weighted.allowance_positive
    (Fraction.Order.Field.div_pos_direct positive (by decide)) weightNonnegative
  let initial := Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest.LocalBoundaryRequest.build
    coarse fixed localTarget localPositive
  let caps := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReadingCaps.RegularMeshes.TwoSheetRequest.ExteriorCaps.build
    initial.energy pairTarget pairPositive
  let prepared := initial.limitReadings caps.values caps.positive
  refine ⟨localTarget, rfl, pairTarget, pairPositive, ?_, initial, caps, prepared, rfl,
    fun stage later sheet position first second => caps.pair_bound stage later sheet position first second⟩
  rw [← weightEq]
  have pairPaid := Rational.Budget.Weighted.mul_allowance_le
    (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 2)).le weightNonnegative
  apply (add_le_add (le_refl (2 * localTarget)) pairPaid).trans_eq
  dsimp only [localTarget, -eq_self, -iff_self]
  have quarter : target / 4 * 4 = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  have half : target / 2 * 2 = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  apply Fraction.Field.mul_right_cancel_of_ne (by decide : (4 : Fraction.Rational) ≠ 0)
  calc
    (2 * (target / 4) + target / 2) * 4 = 2 * (target / 4 * 4) + 2 * (target / 2 * 2) := by ring1
    _ = target * 4 := by rw [quarter, half]; ring1

/-- The finite squared coefficient norm is nonnegative. -/
private theorem coefficient_nonnegative (values : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : 0 ≤
  Readings.PreparedObservationCoercivity.coefficientNormSq values := by
  have estimate := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => 0) (fun i =>
    Gaussian.Basic.Canonical.normSq (values i)) (fun i => Gaussian.Basic.Canonical.normSq_nonneg (values i))
  simpa only [FiniteSum.Fin.sumFin_zero, Readings.PreparedObservationCoercivity.coefficientNormSq, -eq_self, -iff_self]
    using estimate

/-- The complete original two-sheet stitched exterior satisfies the retained target homogeneously in both coefficient
vectors. -/
theorem bound (request : Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest coarse fixed
  target)
    {stage : Nat} {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
      (later : request.prepared.ownership.index ≤ stage)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest.Samples
      request.prepared.energy cache)
    (left right : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (assemblies : Hyperelliptic.Meshes.PuncturedGrid.RegularClippedAssembly.TwoSheetRequest.Assemblies
      request.prepared.energy cache left right) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun sheet : Fin 2 => FiniteSum.Fin.sumFin (fun position :
      Fin faces.length =>
      ((assemblies.get sheet).get position).exterior))) ≤ Readings.PreparedObservationCoercivity.coefficientNormSq left
        * Readings.PreparedObservationCoercivity.coefficientNormSq right * target := by
  let energyLater := request.prepared.ownership.energy_le.trans later
  let q := Readings.PreparedObservationCoercivity.coefficientNormSq left *
    Readings.PreparedObservationCoercivity.coefficientNormSq right
  have qNonnegative : 0 ≤ q := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest.coefficient_nonnegative left)
    (Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest.ExteriorBoundaryRequest.coefficient_nonnegative right)
  have leftNorm := FiniteSum.Fin.sumFin_congr
    (fun row : Fin genus => Gaussian.Norm.Basic.normSq_eq_canonical (left row))
  have rightNorm := FiniteSum.Fin.sumFin_congr
    (fun row : Fin genus => Gaussian.Norm.Basic.normSq_eq_canonical (right row))
  have weighted (sheet : Fin 2) (position : Fin faces.length) :
      FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Norm.Basic.normSq (left
        first) * Data.Gaussian.Norm.Basic.normSq (right second) *
      Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.TwoSheetRequest.pairExteriorBound
        request.prepared.energy stage energyLater sheet position first second)) ≤ q * request.pairTarget := by
    have estimate := FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun first : Fin genus =>
      FiniteSum.Rational.Order.Positivity.sumFin_mono _ _
      (fun second : Fin genus => Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (request.pair_bound stage
        energyLater sheet position first second)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (Gaussian.Norm.Basic.normSq_nonneg (left first))
          (Gaussian.Norm.Basic.normSq_nonneg (right second)))))
    apply estimate.trans_eq
    simp only [FiniteSum.Fin.sumFin_mul_left, FiniteSum.Fin.sumFin_mul_right, leftNorm, rightNorm, q,
      Readings.PreparedObservationCoercivity.coefficientNormSq, -eq_self, -iff_self]
    rfl
  have faceErrors := FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun sheet : Fin 2 =>
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun position : Fin faces.length =>
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (weighted sheet position)
          (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus))
            (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus)))))
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le faces.length)))
  have estimate := Hyperelliptic.Meshes.PuncturedGrid.RegularClippedErrorBound.LocalBoundaryRequest.exterior_bound
    request.prepared later samples left right assemblies
  apply estimate.trans
  have combined := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add (le_refl (q * request.localTarget)) (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      faceErrors (show (0 : Fraction.Rational) ≤ 2 by decide)))
    (show (0 : Fraction.Rational) ≤ 2 by decide)
  apply combined.trans
  apply le_trans (le_of_eq ?_) (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.paid qNonnegative)
  simp only [FiniteSum.Fin.Rational.sum_constant, -eq_self, -iff_self]
  ring1

end ExteriorBoundaryRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
