module

public import Purelib.Polynomial.Approximation.Gaussian.Residual
public import Purelib.Polynomial.Power.Gaussian.Reality
public import Purelib.Approximation.Gaussian.Name.Coherent.Conjugation
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Original-channel reality certificates from measured polynomial residuals -/

public section

namespace Purelib.Polynomial.Approximation.Gaussian.Residual

open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Equivalent)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Geometry.Rational (Box)

/-- A quantitative conjugacy bound on one original retained geometric tail proves original-channel reality.

The comparison retains two independent starting indices. Its computed
geometric budget pays for both sample movement and the same-channel
conjugacy residual, and transports through the original channel link.
-/
def real_of_bound {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) (floor : Nat) (scale : Rational) (nonnegative : 0 ≤ scale)
    (bound : ∀ index, floor ≤ index → normSq (residual.source.sample index -
      (residual.source.sample index).conj) ≤ Basic.quarterRadius scale index) :
    NamedEquivalent channel.name (CoherentNamed.conj channel).name := by
  have direct : Equivalent residual.source.toApproximation residual.source.conj.toApproximation := by
    refine ⟨?_⟩
    intro firstStart secondStart target positive
    let quarter := target / 4
    have quarterPositive := Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
    let movement := (Equivalent.refl residual.source.toApproximation).compare
      firstStart secondStart quarter quarterPositive
    let start := Nat.max movement.rightIndex floor
    let index := Search.firstQuarterBelow scale start quarter
    have indexGe := Search.firstQuarterBelow_ge scale start quarter
    refine ⟨movement.leftIndex, index, movement.left_ge,
      movement.right_ge.trans ((Purelib.Data.Nat.Order.le_max_left _ _).trans indexGe), ?_⟩
    intro firstLater secondLater firstOrder secondOrder
    have originalSecondOrder := (Purelib.Data.Nat.Order.le_max_left _ _).trans (indexGe.trans secondOrder)
    have floorOrder := (Purelib.Data.Nat.Order.le_max_right _ _).trans (indexGe.trans secondOrder)
    have moved := movement.close firstOrder originalSecondOrder
    have imaginary := (bound secondLater floorOrder).trans_lt
      ((Basic.quarterRadius_antitone nonnegative secondOrder).trans_lt
        (Search.firstQuarterBelow_accurate scale nonnegative start quarter quarterPositive))
    change normSq (residual.source.sample firstLater - (residual.source.sample secondLater).conj) < target
    have via := Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_le_via
      (residual.source.sample firstLater) (residual.source.sample secondLater)
      (residual.source.sample secondLater).conj
    have sum := Arithmetic.add_lt_add_direct moved imaginary
    have paid := Arithmetic.mul_lt_mul_of_pos_left_direct (a := (2 : Rational)) (by decide) sum
    have total : 2 * (quarter + quarter) = target := by
      calc
        2 * (quarter + quarter) = quarter * 4 := by ring1
        _ = target := Purelib.Data.Rat.Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)
    rewrite [total] at paid
    exact via.trans_lt paid
  exact residual.equivalent.trans
    (direct.toNamed.trans (CoherentNamed.conj_geometric residual.source residual.equivalent).symm)

set_option genInjectivity false in
/-- One actual retained box and tail whose computed cubic gap certifies reality on the original residual channel. -/
structure CubicRegion {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) (parameter : Rational) (floor : Nat) (box : Box) : Type where
  /-- The original polynomial has exactly the displayed real cubic-power coefficients. -/
  polynomial_eq : polynomial = Power.Gaussian.rootPolynomial ⟨parameter, 0⟩ ⟨3, by decide⟩
  /-- The original box has nonnegative lower real endpoint. -/
  real_nonnegative : 0 ≤ box.xLower
  /-- The positive gap is computed from those same retained rational endpoints. -/
  gap_positive : 0 < Power.Gaussian.Reality.cubicGap box
  /-- Every original retained sample beyond the stated floor stays in this same box. -/
  inside : ∀ index, floor ≤ index → box.Contains (residual.source.sample index)

constructive_injectivity CubicRegion

/-- The original box gap and residual scale compute the conjugacy allowance. -/
@[expose] def CubicRegion.scale {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} {parameter : Rational} {floor : Nat} {box : Box}
    (_region : CubicRegion residual parameter floor box) : Rational :=
  (4 / Power.Gaussian.Reality.cubicGap box ^ 2) * residual.scale

/-- The computed allowance remains nonnegative on the original residual and box data. -/
theorem CubicRegion.scale_nonnegative {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} {parameter : Rational} {floor : Nat} {box : Box}
    (region : CubicRegion residual parameter floor box) : 0 ≤ region.scale :=
  Arithmetic.mul_nonneg_direct (Field.div_nonneg_direct (by decide)
    (Arithmetic.sq_nonneg_direct _)) residual.scale_nonnegative

/-- The computed cubic region allowance bounds conjugacy of every same retained original tail sample. -/
theorem CubicRegion.bound {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} {parameter : Rational} {floor : Nat} {box : Box}
    (region : CubicRegion residual parameter floor box) (index : Nat) (order : floor ≤ index) :
    normSq (residual.source.sample index - (residual.source.sample index).conj) ≤
      Basic.quarterRadius region.scale index := by
  have localBound := Power.Gaussian.Reality.cubic_box_conjugate_bound parameter box
    region.real_nonnegative region.gap_positive (region.inside index order)
  rewrite [← region.polynomial_eq] at localBound
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct (residual.bound index)
    (Field.div_nonneg_direct (by decide : (0 : Rational) ≤ 4)
      (Arithmetic.sq_nonneg_direct (Power.Gaussian.Reality.cubicGap box)))
  calc
    normSq (residual.source.sample index - (residual.source.sample index).conj) ≤
        (4 / Power.Gaussian.Reality.cubicGap box ^ 2) * normSq (polynomial.eval (residual.source.sample index)) :=
      localBound
    _ ≤ (4 / Power.Gaussian.Reality.cubicGap box ^ 2) * Basic.quarterRadius residual.scale index := paid
    _ = Basic.quarterRadius region.scale index := by
      rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
      exact (Purelib.Data.Rat.Fraction.Field.mul_assoc _ _ _).symm

/-- The original retained cubic region certifies actual original-channel conjugacy, rather than box intersection. -/
def CubicRegion.real {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} {parameter : Rational} {floor : Nat} {box : Box}
    (region : CubicRegion residual parameter floor box) :
    NamedEquivalent channel.name (CoherentNamed.conj channel).name :=
  residual.real_of_bound floor region.scale region.scale_nonnegative region.bound

set_option genInjectivity false in
/-- One actual retained box and tail whose computed quadratic gap certifies reality on the original residual channel. -/
structure QuadraticRegion {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    (residual : Residual polynomial channel) (parameter : Rational) (floor : Nat) (box : Box) : Type where
  /-- The original polynomial has exactly the displayed real quadratic-power coefficients. -/
  polynomial_eq : polynomial = Power.Gaussian.rootPolynomial ⟨parameter, 0⟩ ⟨2, by decide⟩
  /-- The original box has nonnegative lower real endpoint. -/
  real_nonnegative : 0 ≤ box.xLower
  /-- The positive gap is computed from those same retained rational endpoints. -/
  gap_positive : 0 < Power.Gaussian.Reality.quadraticGap box
  /-- Every original retained sample beyond the stated floor stays in this same box. -/
  inside : ∀ index, floor ≤ index → box.Contains (residual.source.sample index)

constructive_injectivity QuadraticRegion

/-- The original box gap and residual scale compute the conjugacy allowance. -/
@[expose] def QuadraticRegion.scale {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} {parameter : Rational} {floor : Nat} {box : Box}
    (_region : QuadraticRegion residual parameter floor box) : Rational :=
  (4 / Power.Gaussian.Reality.quadraticGap box ^ 2) * residual.scale

/-- The computed allowance remains nonnegative on the original residual and box data. -/
theorem QuadraticRegion.scale_nonnegative {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} {parameter : Rational} {floor : Nat} {box : Box}
    (region : QuadraticRegion residual parameter floor box) : 0 ≤ region.scale :=
  Arithmetic.mul_nonneg_direct (Field.div_nonneg_direct (by decide)
    (Arithmetic.sq_nonneg_direct _)) residual.scale_nonnegative

/-- The computed quadratic region allowance bounds conjugacy of every same retained original tail sample. -/
theorem QuadraticRegion.bound {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} {parameter : Rational} {floor : Nat} {box : Box}
    (region : QuadraticRegion residual parameter floor box) (index : Nat) (order : floor ≤ index) :
    normSq (residual.source.sample index - (residual.source.sample index).conj) ≤
      Basic.quarterRadius region.scale index := by
  have localBound := Power.Gaussian.Reality.quadratic_box_conjugate_bound parameter box
    region.gap_positive (region.inside index order)
  rewrite [← region.polynomial_eq] at localBound
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct (residual.bound index)
    (Field.div_nonneg_direct (by decide : (0 : Rational) ≤ 4)
      (Arithmetic.sq_nonneg_direct (Power.Gaussian.Reality.quadraticGap box)))
  calc
    normSq (residual.source.sample index - (residual.source.sample index).conj) ≤
        (4 / Power.Gaussian.Reality.quadraticGap box ^ 2) * normSq (polynomial.eval (residual.source.sample index)) :=
      localBound
    _ ≤ (4 / Power.Gaussian.Reality.quadraticGap box ^ 2) * Basic.quarterRadius residual.scale index := paid
    _ = Basic.quarterRadius region.scale index := by
      rewrite [Basic.quarterRadius_eq_mul_pow, Basic.quarterRadius_eq_mul_pow]
      exact (Purelib.Data.Rat.Fraction.Field.mul_assoc _ _ _).symm

/-- The original retained quadratic region certifies actual original-channel conjugacy, rather than box intersection. -/
def QuadraticRegion.real {polynomial : CoefficientPolynomial} {channel : CoherentNamed}
    {residual : Residual polynomial channel} {parameter : Rational} {floor : Nat} {box : Box}
    (region : QuadraticRegion residual parameter floor box) :
    NamedEquivalent channel.name (CoherentNamed.conj channel).name :=
  residual.real_of_bound floor region.scale region.scale_nonnegative region.bound

end Purelib.Polynomial.Approximation.Gaussian.Residual

end
