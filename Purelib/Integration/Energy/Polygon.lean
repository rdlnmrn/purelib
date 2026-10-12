module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.LinearAlgebra.Gaussian.Energy
public import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring

open Purelib.LinearAlgebra.Gaussian.Energy.PreparedEnergySurface (GaussianVector)

section
@[expose] public section

/-!
# Triangulated finite surface energy

This module supplies the two-dimensional algebraic bridge for the second
Riemann bilinear relation.  A finite sample consists of a genuine oriented
triangulation, primitive values at its vertices, an exact identification of
its outer boundary with the displayed A/B period commutators, and a checked
lower-energy inequality on every face.  Incidence cancellation and finite
summation then derive the global surface lower theorem consumed by
`PreparedEnergy`; it is not repeated as an assumption.
-/

namespace Purelib.Integration.Energy.Polygon

open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
/-- Pair a Gaussian value's conjugate with the original value as an energy primitive point. -/
def energyPrimitivePoint (value : Basic.Canonical) : Stokes.PrimitivePoint :=
  ⟨Data.Gaussian.Basic.conj value, value⟩

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Topology.Polygon in
/-- Sum commutator boundary areas of the original paired period vectors through their energy primitive points. -/
def energyBoundaryArea {size : Nat}
    (aPeriods bPeriods : GaussianVector size) : Basic.Canonical :=
  FiniteSum.Fin.sumFin fun cycle =>
    Stokes.commutatorBoundaryArea
      Stokes.PrimitivePoint.zero
      (energyPrimitivePoint (aPeriods cycle))
      (energyPrimitivePoint (bPeriods cycle))

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Topology.Polygon in
/-- The original period pairing energy equals one quarter of the energy boundary area's imaginary part. -/
theorem periodPairingEnergy_eq_boundaryArea_im_div_four {size : Nat}
    (aPeriods bPeriods : GaussianVector size) :
    Energy.periodPairingEnergy aPeriods bPeriods =
      (energyBoundaryArea aPeriods bPeriods).im / 4 := by
  unfold energyBoundaryArea
  rw [FiniteSum.Fin.sumFin_congr
    (right := fun cycle => 2 *
      (bPeriods cycle * Data.Gaussian.Basic.conj
          (aPeriods cycle) -
        aPeriods cycle * Data.Gaussian.Basic.conj
          (bPeriods cycle)))
    (fun cycle => by
      rw [Stokes.commutatorBoundaryArea_eq]
      unfold energyPrimitivePoint
      dsimp only
      ring1)]
  rw [FiniteSum.Fin.sumFin_mul_left]
  rw [Basic.mul_im,
    show (2 : Basic.Canonical).re = (2 : Fraction.Rational) by decide,
    show (2 : Basic.Canonical).im = (0 : Fraction.Rational) by decide,
    Fraction.Field.zero_mul_direct, _root_.add_zero]
  rw [Energy.sumFin_im]
  unfold Energy.periodPairingEnergy
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  rw [show (2 : Fraction.Rational)⁻¹ = 2 * (4 : Fraction.Rational)⁻¹ by decide]
  ring1

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.LinearAlgebra.Gaussian in
open Purelib.Topology.Polygon in
/-- The energy boundary area equals twice the finite skew conjugate period sum. -/
theorem energyBoundaryArea_eq_two_mul_sum {size : Nat}
    (aPeriods bPeriods : GaussianVector size) :
    energyBoundaryArea aPeriods bPeriods =
      2 * FiniteSum.Fin.sumFin (fun cycle =>
        bPeriods cycle * Data.Gaussian.Basic.conj
            (aPeriods cycle) -
          aPeriods cycle * Data.Gaussian.Basic.conj
            (bPeriods cycle)) := by
  unfold energyBoundaryArea
  rw [FiniteSum.Fin.sumFin_congr
    (right := fun cycle => 2 *
      (bPeriods cycle * Data.Gaussian.Basic.conj
          (aPeriods cycle) -
        aPeriods cycle * Data.Gaussian.Basic.conj
          (bPeriods cycle)))
    (fun cycle => by
      rw [Stokes.commutatorBoundaryArea_eq]
      unfold energyPrimitivePoint
      dsimp only
      ring1)]
  rw [FiniteSum.Fin.sumFin_mul_left]

end Purelib.Integration.Energy.Polygon

end
