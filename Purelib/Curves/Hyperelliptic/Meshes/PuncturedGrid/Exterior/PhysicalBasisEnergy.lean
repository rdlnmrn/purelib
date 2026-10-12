module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.BasisEnergyUpper
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAccuracy
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Readings

open Purelib.Riemann.Topology

@[expose] public section

/-! Transfer the actual cap energy bound to the cached physical basis samples. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisEnergy
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisBounds (RegularBasisBounds)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest (RegularBasisRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisAggregate (RegularBasisCap)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisSamples (PhysicalBasisArcSamples)
open Purelib.Riemann.Normalization
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {index depth minimum floor : Nat} {box : Purelib.Geometry.Rational.Box} {target :
  Rational}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} (attached :
    CapAttachment prepared)

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Algebra.FiniteSum.Fin (sumFin_zero)

namespace PhysicalBasisArcSamples
variable {bounds : RegularBasisBounds
  polynomials}
  {capTarget : Rational} {capMinimum : Nat}
  (request : RegularBasisRequest bounds
    attached.caps.length capTarget capMinimum)
  {geometry :
    Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached}
  {parameters : Purelib.Integration.Path.Dyadic.RadialTriangles.Parameters request.depth}

/-- The cached complete physical exterior areas, including their endpoint chords, inherit a homogeneous upper bound from
the actual regular cap. -/
theorem energy_upper
    (caps : CapBasisAggregate.RegularBasisCap geometry parameters polynomials)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (capSample : (request.certify caps).Evaluation coefficients)
    (samples : PhysicalBasisSamples.PhysicalBasisArcSamples (regular := regular) (domains := domains) polynomials target
      minimum floor request.depth)
    (allowance : Fraction.Rational) (nonnegative : 0 ≤ allowance)
    (paid : (genus : Fraction.Rational) ^ 2 * target ≤ 16 * allowance ^ 2) :
    (samples.energy coefficients).im / 4 ≤
      (capTarget + allowance) * PreparedObservationCoercivity.coefficientNormSq coefficients := by
  have normNonnegative : 0 ≤ PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 : Fraction.Rational))
      _
      (fun row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have close := PhysicalBasisArcSamples.accurate attached samples coefficients
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct paid
    (Fraction.Order.Arithmetic.sq_nonneg_direct (PreparedObservationCoercivity.coefficientNormSq coefficients))
  have errorPaid : (genus : Fraction.Rational)^2 * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 *
    target ≤
      (4 * (allowance * PreparedObservationCoercivity.coefficientNormSq coefficients))^2 :=
    (show (genus : Fraction.Rational)^2 * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 * target =
      ((genus : Fraction.Rational)^2 * target) * (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 by
        ring1).trans_le
      (scaled.trans_eq (by ring1))
  have comparison := PreparedSurfaceCoercivity.boundaryEnergy_sub_budget_le
    (samples.energy coefficients)
    (FiniteSum.Fin.sumFin (fun first => FiniteSum.Fin.sumFin (fun second => Data.Gaussian.Basic.conj
      (coefficients first) * coefficients second *
      polynomials.forwardBoundary attached request.depth first second)))
    (allowance * PreparedObservationCoercivity.coefficientNormSq coefficients)
      (Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative normNonnegative) (close.trans errorPaid)
  have capBound := request.forward_energy_upper caps coefficients capSample
  have result := Fraction.Order.Arithmetic.add_le_add_right_direct (comparison.trans capBound) (allowance *
    PreparedObservationCoercivity.coefficientNormSq coefficients)
  exact (show (samples.energy coefficients).im / 4 =
    ((samples.energy coefficients).im / 4 - allowance * PreparedObservationCoercivity.coefficientNormSq coefficients) +
      allowance * PreparedObservationCoercivity.coefficientNormSq coefficients by ring1).trans_le (result.trans_eq (by
        ring1))

end PhysicalBasisArcSamples
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalBasisEnergy
