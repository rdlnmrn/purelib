module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Readings.AffineBasisEnergy
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.Dyadic.RadialTriangles
public import Purelib.Riemann.RootContinuation.RootRadialRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest

@[expose] public section

/-! Cached homogeneous basis values on the actual oriented root-coordinate
fan. These are evaluations at the ramified coordinate, not its square. -/
namespace Purelib.Riemann.RootContinuation.RootRadialBasisEnergy

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_zero sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Riemann.Readings.AffineBasisEnergy (AffineBasis)
open Purelib.Integration.Energy.AffineTriangle (coordinateTriangleArea)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Normalization
open Purelib.Riemann.RootContinuation.RootRadialRefinement (Refinement)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {first last :
    Purelib.Data.Gaussian.Basic.Canonical} {depth : Nat}
  {parameters : Purelib.Integration.Path.Dyadic.RadialTriangles.Parameters depth}

open Purelib.Curves in
set_option genInjectivity false in
/-- Cache homogeneous primitive basis values on the actual oriented root-coordinate fan.

The retained affine basis reads both primitive values and face coefficients at the original ramified coordinates. -/
structure BasisValues (refinement : Refinement first last parameters)
    (polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      where
  /-- The cached affine basis on the original fan triangulation and refined coordinates. -/ basis : AffineBasis
    parameters.mesh.mesh.triangulation refinement.coordinates genus
  /-- Each cached basis value is the original primitive polynomial evaluated at the actual root coordinate. -/ values_eq
    : ∀ row vertex, basis.values row vertex = (polynomials.get row).primitive.value.eval (refinement.coordinates vertex)
  /-- Each cached face coefficient is the original coefficient polynomial at that face's first root-coordinate vertex.
  -/
  coefficients_eq : ∀ row face, basis.coefficients row face = (polynomials.get row).coefficient.eval
    (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first)

constructive_injectivity BasisValues

namespace BasisValues

variable {refinement : Refinement first last parameters} {polynomials :
  RegularBasisPolynomials cap index box}

open Purelib.Curves in
open Purelib.Data in
/-- Evaluate the retained basis polynomials once on the actual root-coordinate fan.

Separate value and face-coefficient vectors retain exact scalar readbacks to their original polynomials. -/
def build (refinement : Refinement first last parameters) (polynomials :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box) :
    BasisValues refinement polynomials := by
  let values := Vector.Basic.vectorOfFn (fun row : Fin genus => Vector.Basic.vectorOfFn (fun vertex =>
    (polynomials.get row).primitive.value.eval (refinement.coordinates vertex)))
  let coefficients := Vector.Basic.vectorOfFn (fun row : Fin genus => Vector.Basic.vectorOfFn (fun face =>
    (polynomials.get row).coefficient.eval (refinement.coordinates (parameters.mesh.mesh.triangulation.faces
      face).first)))
  refine ⟨⟨values, coefficients⟩, ?_, ?_⟩
  · intro row vertex
    change (values row) vertex = _
    rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
  · intro row face
    change (coefficients row) face = _
    rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.LinearAlgebra in
/-- A weighted affine sample reads exactly the original regular-basis primitive combination at the retained root
coordinate. -/
theorem value_readback (sample : BasisValues refinement polynomials) (budget : AffineBasis.SurfaceBudget sample.basis)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (vertex : Fin
      parameters.mesh.mesh.vertices.length) :
    (budget.sample coefficients).primitiveValue vertex =
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials.value polynomials coefficients
        (refinement.coordinates vertex) := by
  rw [budget.sample_value]
  unfold AffineBasis.value Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials.value
  exact FiniteSum.Fin.sumFin_congr fun row => congrArg (fun value => coefficients row * value) (sample.values_eq row
    vertex)

open Purelib.Algebra in
open Purelib.Integration in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- The fan boundary energy is bounded below by minus the retained homogeneous error budget.

Nonnegative actual oriented face areas supply the affine-energy lower bound for every coefficient vector. -/
theorem lower (sample : BasisValues refinement polynomials) (budget : AffineBasis.SurfaceBudget sample.basis)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    -(coefficientNormSq coefficients * budget.total) ≤ (budget.sample coefficients).boundaryArea.im / 4 := by
  have nonnegative : 0 ≤ (budget.sample coefficients).affineEnergy := by
    change 0 ≤ FiniteSum.Fin.sumFin (fun face => Energy.AffineTriangle.coordinateTriangleArea
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).first)
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).second)
      (refinement.coordinates (parameters.mesh.mesh.triangulation.faces face).third) * _)
    have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => (0 : Rat.Fraction.Rational)) _
      (fun face => Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (refinement.nonnegative face)
        (Gaussian.Norm.Basic.normSq_nonneg ((budget.sample coefficients).faceCoefficient face)))
    exact FiniteSum.Fin.sumFin_zero.symm.trans_le bound
  have bound := Rat.Fraction.Order.Arithmetic.sub_le_sub_direct nonnegative (le_refl (a := coefficientNormSq
    coefficients * budget.total))
  rw [zero_sub] at bound
  exact bound.trans (budget.energy_lower coefficients)

end BasisValues
end Purelib.Riemann.RootContinuation.RootRadialBasisEnergy
