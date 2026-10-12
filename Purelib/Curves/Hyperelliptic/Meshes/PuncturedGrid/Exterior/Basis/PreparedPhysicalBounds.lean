module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedSelection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PreparedPhysicalRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CertifiedRunMagnitudes
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Requested area, endpoint and magnitude bounds for the actual physical parent paths. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PreparedPhysicalBounds

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {index : Nat} {inputs : retained.Inputs index}
  {outer : Fin prepared.occurrences.length} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {faceIndex depth capacity minimum : Nat} {sideArea : Normalization.InverseRootPolynomial.Gaussian} {requested
    allowance tolerance : Normalization.InverseRootPolynomial.Coordinate}

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {sourceAllowance coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor : Nat}
  {box : Rational.Box} {polynomials :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace PhysicalRunBank
variable (bank : PhysicalRunBank retained inputs outer
  coefficients faceIndex depth capacity sideArea allowance tolerance)
  (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).compared.entered.cache.parents.length)
  (source : Charts.Reciprocal.Disk.Basis.PreparedSelection
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer position)
    basis sourceAllowance coefficientTarget coverFloor floor polynomials coefficients)

open Purelib.Data.Rat.Fraction.Compatibility

namespace PreparedRun
variable {bank position source} {target : Normalization.InverseRootPolynomial.Coordinate} (run :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PreparedPhysicalRuns.PhysicalRunBank.PreparedRun bank position
  source target)

include run

/-- The original oriented physical path area approximates its prepared source area at the requested coefficient-weighted
quadratic bound. -/
theorem area_requested : Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (bank.physical position) -
  source.weighted.source.area) ≤
    target * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  cases run with
  | forward direction certified fragments =>
    have bound := certified.area_requested source.weighted
    rw [fragments] at bound
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.forward_physical bank
      position direction]
    exact bound
  | reverse direction certified fragments =>
    have bound := certified.oriented_area_requested source.weighted
    change Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (Path.PairedAreaReversal.reverseIncrements
      ((certified.run.fragments.map
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map Prod.fst).flatten) -
        source.weighted.source.area) ≤ _ at bound
    rw [fragments] at bound
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.reverse_physical bank
      position direction]
    exact bound

/-- The original physical endpoint sum approximates the prepared conjugate-diagonal source total at one quarter of the
requested tolerance. -/
theorem total_quarter_requested :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total (bank.physical position)).sub
      (Path.ConjugatePathReadback.conjugateDiagonal source.weighted.source.total))
      ((target / 4) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  cases run with
  | forward direction certified fragments =>
    have bound := certified.total_requested source.weighted
    rw [fragments] at bound
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.forward_physical bank
      position direction]
    exact bound
  | reverse direction certified fragments =>
    have bound := certified.oriented_total_requested source.weighted
    change Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total
      (Path.PairedAreaReversal.reverseIncrements
      ((certified.run.fragments.map
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map Prod.fst).flatten)).sub
      (Path.ConjugatePathReadback.conjugateDiagonal source.weighted.source.total)) _ at bound
    rw [fragments] at bound
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.reverse_physical bank
      position direction]
    exact bound

/-- For a nonnegative target, the original physical endpoint error satisfies the full requested coefficient-weighted
tolerance. -/
theorem total_requested (nonnegative : 0 ≤ target) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total (bank.physical position)).sub
      (Path.ConjugatePathReadback.conjugateDiagonal source.weighted.source.total))
      (target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := open Purelib.Algebra in by
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have quarter : target / 4 ≤ target := by
    rw [Fraction.Field.div_eq_mul_inv_direct]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by
        decide : (4 : Normalization.InverseRootPolynomial.Coordinate)⁻¹ ≤ 1) nonnegative).trans_eq (mul_one _)
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct quarter massNN
  have bounded :=
    total_quarter_requested
    run
  exact ⟨bounded.1.trans paid, bounded.2.trans paid⟩

/-- A certified target capped by one bounds the original physical endpoint sum using the retained source slope and
coefficient mass. -/
theorem total_bounded_requested (capped : target ≤ 1) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total (bank.physical position))
      (2 * (1 + Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
        position).sources) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  cases run with
  | forward direction certified fragments =>
    have bound := certified.total_bounded_requested capped source.weighted
    rw [fragments] at bound
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.forward_physical bank
      position direction]
    exact bound
  | reverse direction certified fragments =>
    have bound := certified.oriented_bounded_requested capped source.weighted
    change Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total
      (Path.PairedAreaReversal.reverseIncrements
      ((certified.run.fragments.map
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment.pair).map Prod.fst).flatten)) _
        at bound
    rw [fragments] at bound
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ScheduledPhysicalRuns.PhysicalRunBank.reverse_physical bank
      position direction]
    exact bound

end PreparedRun
end PhysicalRunBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PreparedPhysicalBounds
