module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Content

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Topology.PreparedObservationSurface
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.EvaluationLower
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Integration.Energy

open Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared

open Purelib.Data.Rat

open Purelib.Geometry.Rational.Box

public section

/-! Decrease the densities of a retained separated surface family so that
its total energy fits the raw allowance. The exact capped energy preserves a
homogeneous lower bound; no coefficient-dependent choice of boxes is needed. -/
namespace Purelib.Curves.Hyperelliptic.Integration.Observation.RawCoercivityCells

open _root_.Purelib.LinearAlgebra.Gaussian.Energy (GaussianVector)
open Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared.PreparedEnergy (SurfaceCell)
open Purelib.Curves.Hyperelliptic.Integration.Energy.Prepared (surfaceEnergy)
open Purelib.Riemann.Topology.PreparedObservationSurface (ObservationBoxEnergy)

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_mul_left)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

/-- Decrease the density of the original checked surface cell by a factor between zero and one.

The face, box and denominator certificate remain the original retained data, and both density inequalities are
transported by the displayed factor. -/
@[expose] def SurfaceCell.scaleDensity (cell : PreparedEnergy.SurfaceCell curve coefficients)
    (factor : Fraction.Rational) (nonnegative : 0 ≤ factor) (bounded : factor ≤ 1) :
    PreparedEnergy.SurfaceCell curve coefficients :=
  let below : factor * cell.densityLower ≤ cell.densityLower := by
    have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct bounded cell.densityLower_nonnegative
    rwa [_root_.one_mul] at bound
  { cell with
    densityLower := factor * cell.densityLower
    densityLower_nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct nonnegative cell.densityLower_nonnegative
    density_below_numerator := fun point inside => below.trans (cell.density_below_numerator point inside)
    density_valid := fun point inside =>
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct below (Data.Gaussian.Norm.Basic.normSq_nonneg
        _)).trans
        (cell.density_valid point inside) }

/-- Scale every retained cell density by the same nonnegative factor at most one, preserving the original vector order.
-/
@[expose] def scaleSurfaceCells {count : Nat} (cells : Data.Vector (PreparedEnergy.SurfaceCell curve
  coefficients) count)
    (factor : Fraction.Rational) (nonnegative : 0 ≤ factor) (bounded : factor ≤ 1) :
    Data.Vector (PreparedEnergy.SurfaceCell curve coefficients) count :=
  Data.Vector.Basic.vectorOfFn fun index =>
    Curves.Hyperelliptic.Integration.Observation.RawCoercivityCells.SurfaceCell.scaleDensity (cells index) factor
    nonnegative bounded

/-- Density scaling retains each original surface-cell box exactly. -/
theorem scaleSurfaceCells_box {count : Nat} (cells : Data.Vector (PreparedEnergy.SurfaceCell curve
  coefficients) count)
    (factor : Fraction.Rational) (nonnegative : 0 ≤ factor) (bounded : factor ≤ 1) (index : Fin count) :
    (scaleSurfaceCells cells factor nonnegative bounded
      index).box = (cells index).box := by
  rw [scaleSurfaceCells,
    Data.Vector.Basic.vectorOfFn_apply]
  rfl

/-- Scaling all retained densities scales their exact finite surface energy by the same factor. -/
theorem scaleSurfaceCells_energy {count : Nat} (cells : Data.Vector (PreparedEnergy.SurfaceCell curve
  coefficients) count)
    (factor : Fraction.Rational) (nonnegative : 0 ≤ factor) (bounded : factor ≤ 1) :
    Prepared.surfaceEnergy (fun index =>
      scaleSurfaceCells cells factor nonnegative bounded
      index) =
      factor * Prepared.surfaceEnergy (fun index => cells index) := by
  change FiniteSum.Fin.sumFin (fun index =>
    Content.boxContent (scaleSurfaceCells cells factor
      nonnegative bounded index).box *
      (scaleSurfaceCells cells factor nonnegative
        bounded index).densityLower) = _
  calc
    _ = FiniteSum.Fin.sumFin (fun index => factor * (Content.boxContent (cells index).box *
        (cells index).densityLower)) := FiniteSum.Fin.sumFin_congr fun index => by
      rw [scaleSurfaceCells,
        Data.Vector.Basic.vectorOfFn_apply]
      change Content.boxContent (cells index).box *
        (factor * (cells index).densityLower) = _
      ring1
    _ = _ := FiniteSum.Fin.sumFin_mul_left _ _

/-- Clip the target-to-energy ratio at one. -/
@[expose] def capFactor (energy target : Fraction.Rational) : Fraction.Rational := min 1 (target / energy)

/-- Positive original energy and target give a positive clipping factor. -/
theorem capFactor_positive {energy target : Fraction.Rational} (energyPositive : 0 < energy)
    (targetPositive : 0 < target) : 0 < capFactor energy
      target :=
  Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Field.div_pos_direct targetPositive
    energyPositive)

/-- The energy clipping factor is at most one. -/
theorem capFactor_le_one (energy target : Fraction.Rational) :
  capFactor energy target ≤ 1 :=
  Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _

/-- For positive original energy, the clipped energy is exactly the minimum of that energy and the target. -/
theorem capFactor_energy {energy : Fraction.Rational} (positive : 0 < energy) (target : Fraction.Rational) :
    capFactor energy target * energy = min
      energy target := by
  unfold capFactor
  by_cases below : energy ≤ target
  · have divided : 1 ≤ target / energy := (Fraction.Order.Field.le_div_iff_pos positive).2 (by rwa [_root_.one_mul])
    rw [Purelib.Data.Rat.Fraction.Order.Basic.min_eq_left divided, Purelib.Data.Rat.Fraction.Order.Basic.min_eq_left
      below, _root_.one_mul]
  · have divided : target / energy ≤ 1 := (Fraction.Order.Field.div_le_iff_pos positive).2 (by
      rw [_root_.one_mul]
      exact (le_of_not_ge below))
    rw [Purelib.Data.Rat.Fraction.Order.Basic.min_eq_right divided, Purelib.Data.Rat.Fraction.Order.Basic.min_eq_right
      (le_of_not_ge below)]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ positive.ne'

end Purelib.Curves.Hyperelliptic.Integration.Observation.RawCoercivityCells
