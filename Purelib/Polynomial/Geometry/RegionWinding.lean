module
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Polynomial.Winding.Box.Residual
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.Subdivision.Raw.Request
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

open Purelib.Geometry.Rational

open Purelib.Polynomial

@[expose] public section

/-!
# Vanishing winding from full-region clearance

A nonzero-winding box can be refined finitely until its rational anchor
residual is smaller than the supplied region margin. This contradicts that
same margin at the retained anchor. No compactness, limiting root, squarefree
certificate, or caller-provided successful subdivision is used.
-/

namespace Purelib.Polynomial.Clearance.Box.Region.RegionClearance

variable {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box}

/-- Uniform clearance on a proper rectangle forces its raw winding to
vanish. The hypothetical refinement is confined to this erased proof. -/
theorem winding_zero (clearance :
  Clearance.Box.Region.RegionClearance p box)
    (degreePositive : 0 < p.natDegree) (proper : box.Proper) :
    Winding.Box.Basic.quadrupledBoxWinding p box = 0 := open Purelib.Data.Rat in open Purelib in by
  by_cases zero : Winding.Box.Basic.quadrupledBoxWinding p box = 0
  · exact zero
  · let elimination := Elimination.Axis.Separated.separatedAxisEliminationCertificate p
      (Dense.Gaussian.Degree.Global.isZero_false_of_natDegree_pos degreePositive) degreePositive
    let state : RootIsolation.State.Raw.RawWindingState p box :=
      ⟨box, Box.refines_refl box, proper, clearance.toBoundaryClearance, zero⟩
    let slope := Dense.Gaussian.Bounds.Box.denseLipschitzBound p box
    have slopePositive : 0 < slope := Dense.Gaussian.Bounds.Box.denseLipschitzBound_pos p box
    let target := (clearance.bound / 2) / slope
    have halfPositive : 0 < clearance.bound / 2 :=
      Fraction.Order.Field.div_pos_direct clearance.positive (by decide)
    have targetPositive : 0 < target := Fraction.Order.Field.div_pos_direct halfPositive slopePositive
    let small := RootIsolation.Subdivision.Raw.Request.refineTo elimination state target
    have residual := Winding.Box.Residual.anchor_residual_le_of_quadrupledBoxWinding_ne_zero
      p degreePositive small.refinesAmbient small.proper small.rawWinding_ne
    have width := RootIsolation.Subdivision.Raw.Request.refineTo_diagonalSq_le elimination state targetPositive
    have upper : Dense.Gaussian.Bounds.Box.Residual.anchorResidualBound p box small.box ≤ clearance.bound / 2 := by
      change slope * small.box.diagonalSq ≤ _
      calc
        _ ≤ slope * target := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct width slopePositive.le
        _ = clearance.bound / 2 := by
          rw [Fraction.Field.mul_comm]
          exact Fraction.Field.div_mul_cancel_of_ne _ _ slopePositive.ne'
    have lower := clearance.lower small.box.anchor (small.refinesAmbient.contains small.box.contains_anchor)
    have strict : clearance.bound / 2 < clearance.bound :=
      (Fraction.Order.Field.div_lt_iff_pos (by decide : (0 : Fraction.Rational) < 2)).2 (by
        have positive := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct clearance.positive
          (by decide : (1 : Fraction.Rational) < 2)
        simpa only [Fraction.Field.mul_one_direct] using positive)
    exact (not_lt_of_ge (lower.trans (residual.trans upper)) strict).elim

end Purelib.Polynomial.Clearance.Box.Region.RegionClearance
