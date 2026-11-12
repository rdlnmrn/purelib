module

public import Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy
public import Purelib.Polynomial.Dense.Bivariate.Specialization.Affine
public import Purelib.Topology.Mesh.CoordinateTriangulation
public import Purelib.Data.Vector.Dependent
public import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.RootContinuation.SquareRootTraceBounds
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Dominance
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Geometry.Rational.Affine
import Purelib.Tactic.Ring
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Bivariate.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Power.Coordinate
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Comparison.Basic

/-! # Finite affine-root triangles over an actual bivariate radicand

The root values form one affine map; the two parameter coordinates form a
separate affine map. Genuine anchor distance, residual and whole-triangle
radicand bounds imply positive square-versus-radicand dominance. Every side
retains its own exact polynomial restriction. No exact root equality or
completed surface is an input or conclusion.
-/

public section

namespace Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy.Triangle

open Purelib.Polynomial.Dense.Gaussian
open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Algebra
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Bivariate.Basic (GaussianBivariate)
open Purelib.Polynomial.Dense.Rational.CauchyIndex
open Purelib.Polynomial.Clearance
open Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation.SquareRootTraceBounds

/-- The original closed barycentric triangle of rational parameters. -/
@[expose] def Inside (u v : Rational) : Prop := 0 ≤ u ∧ 0 ≤ v ∧ u + v ≤ 1

/-- The actual affine combination of three retained Gaussian values, with its original operation order. -/
@[expose] def value (first second third : Canonical) (u v : Rational) : Canonical :=
  first + Cast.Path.ofCoordinate u * (second - first) + Cast.Path.ofCoordinate v * (third - first)

/-- The finite bivariate coefficient table realizing the same affine combination. -/
def affine (first second third : Canonical) : GaussianBivariate :=
  ⟨[constant (second - first), ⟨[third - first, first]⟩]⟩

/-- The retained affine table evaluates to its literal Gaussian affine combination. -/
theorem affine_eval (first second third : Canonical) (u v : Rational) :
    Bivariate.Basic.eval (affine first second third) (Cast.Path.ofCoordinate u) (Cast.Path.ofCoordinate v) =
      value first second third u v := by
  change (0 * Cast.Path.ofCoordinate u + (0 * Cast.Path.ofCoordinate v + (second - first))) *
    Cast.Path.ofCoordinate u +
    ((0 * Cast.Path.ofCoordinate v + (third - first)) * Cast.Path.ofCoordinate v + first) = _
  unfold value
  ring1

/-- The same affine map in the rational parameter plane, without a curve-point or Frame cast. -/
@[expose] def point (triangle : CoordinateTriangle) (u v : Rational) : Canonical :=
  value triangle.first triangle.second triangle.third u v

/-- A three-term retained barycentric coordinate stays in the same scalar interval. -/
private theorem between_three {lower upper first second third : Rational}
    (firstInside : lower ≤ first ∧ first ≤ upper) (secondInside : lower ≤ second ∧ second ≤ upper)
    (thirdInside : lower ≤ third ∧ third ≤ upper) (u v : Rational) (inside : Inside u v) :
    lower ≤ first + u * (second - first) + v * (third - first) ∧
      first + u * (second - first) + v * (third - first) ≤ upper := by
  have complement : 0 ≤ 1 - u - v :=
    (Order.Arithmetic.sub_nonneg_direct inside.2.2).trans_eq (by ring1)
  constructor
  · calc
      lower = (1 - u - v) * lower + u * lower + v * lower := by ring1
      _ ≤ (1 - u - v) * first + u * second + v * third :=
        Order.Arithmetic.add_le_add_direct
          (Order.Arithmetic.add_le_add_direct
            (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct firstInside.1 complement)
            (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct secondInside.1 inside.1))
          (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct thirdInside.1 inside.2.1)
      _ = _ := by ring1
  · calc
      _ = (1 - u - v) * first + u * second + v * third := by ring1
      _ ≤ (1 - u - v) * upper + u * upper + v * upper :=
        Order.Arithmetic.add_le_add_direct
          (Order.Arithmetic.add_le_add_direct
            (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct firstInside.2 complement)
            (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct secondInside.2 inside.1))
          (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct thirdInside.2 inside.2.1)
      _ = upper := by ring1

/-- The same three actual parameter-plane vertices keep their whole affine triangle in a retained rational box. -/
theorem point_inside (box : Box) (triangle : CoordinateTriangle)
    (firstInside : box.Contains triangle.first) (secondInside : box.Contains triangle.second)
    (thirdInside : box.Contains triangle.third) (u v : Rational) (inside : Inside u v) :
    box.Contains (point triangle u v) := by
  have horizontal := between_three ⟨firstInside.1, firstInside.2.1⟩
    ⟨secondInside.1, secondInside.2.1⟩ ⟨thirdInside.1, thirdInside.2.1⟩ u v inside
  have vertical := between_three firstInside.2.2 secondInside.2.2 thirdInside.2.2 u v inside
  have realEq : (point triangle u v).re = triangle.first.re + u * (triangle.second.re - triangle.first.re) +
      v * (triangle.third.re - triangle.first.re) := by
    simp only [point, value, Cast.Path.ofCoordinate, Basic.add_re, Basic.mul_re, Basic.sub_re,
      Basic.sub_im, -eq_self, -iff_self]
    ring1
  have imagEq : (point triangle u v).im = triangle.first.im + u * (triangle.second.im - triangle.first.im) +
      v * (triangle.third.im - triangle.first.im) := by
    simp only [point, value, Cast.Path.ofCoordinate, Basic.add_im, Basic.mul_im, Basic.sub_re,
      Basic.sub_im, -eq_self, -iff_self]
    ring1
  exact ⟨Eq.mpr (congrArg (fun coordinate : Rational => box.xLower ≤ coordinate) realEq) horizontal.1,
    Eq.mpr (congrArg (fun coordinate : Rational => coordinate ≤ box.xUpper) realEq) horizontal.2,
    Eq.mpr (congrArg (fun coordinate : Rational => box.yLower ≤ coordinate) imagEq) vertical.1,
    Eq.mpr (congrArg (fun coordinate : Rational => coordinate ≤ box.yUpper) imagEq) vertical.2⟩

/-- Read the actual two real parameter coordinates in their separate bivariate slots. -/
@[expose] def radicand (polynomial : GaussianBivariate) (parameterPoint : Canonical) : Canonical :=
  Bivariate.Basic.eval polynomial (⟨parameterPoint.re, 0⟩ : Canonical) (⟨parameterPoint.im, 0⟩ : Canonical)

/-- A real scalar multiplies the original displacement quadrance by its exact square. -/
private theorem scaled_distance (weight : Rational) (root anchor : Canonical) {density : Rational}
    (bounded : Canonical.normSq (root - anchor) ≤ density) :
    Norm.Basic.normSq (Cast.Path.ofCoordinate weight * (root - anchor)) ≤ density * weight ^ 2 := by
  rewrite [Norm.Basic.normSq_eq_canonical, Canonical.normSq_mul]
  have scalar : Canonical.normSq (Cast.Path.ofCoordinate weight) = weight ^ 2 := by
    change weight * weight + 0 * 0 = weight ^ 2
    ring1
  rewrite [scalar]
  exact (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
    (Order.Arithmetic.sq_nonneg_direct weight)).trans_eq (by ring1)

/-- Three anchor-distance bounds control the whole affine root triangle while preserving its barycentric pairing. -/
theorem distance (anchor first second third : Canonical) (norm : Rational)
    (firstClose : Canonical.normSq (first - anchor) ≤ norm / 1024)
    (secondClose : Canonical.normSq (second - anchor) ≤ norm / 1024)
    (thirdClose : Canonical.normSq (third - anchor) ≤ norm / 1024)
    (u v : Rational) (inside : Inside u v) :
    Canonical.normSq (value first second third u v - anchor) ≤ norm / 1024 := by
  let weights : Fin 3 → Rational :=
    Fin.cases (1 - u - v) (Fin.cases u (Fin.cases v (fun index => Fin.elim0 index)))
  let terms : Fin 3 → Canonical :=
    Fin.cases (Cast.Path.ofCoordinate (1 - u - v) * (first - anchor))
      (Fin.cases (Cast.Path.ofCoordinate u * (second - anchor))
        (Fin.cases (Cast.Path.ofCoordinate v * (third - anchor)) (fun index => Fin.elim0 index)))
  have nonnegative : ∀ index, 0 ≤ weights index := by
    intro index
    refine Fin.cases ?_ (Fin.cases inside.1 (Fin.cases inside.2.1 (fun bad => Fin.elim0 bad))) index
    change 0 ≤ 1 - u - v
    exact (Order.Arithmetic.sub_nonneg_direct inside.2.2).trans_eq (by ring1)
  have bounded : ∀ index, Norm.Basic.normSq (terms index) ≤ (norm / 1024) * (weights index) ^ 2 := by
    intro index
    exact Fin.cases (scaled_distance _ _ _ firstClose)
      (Fin.cases (scaled_distance _ _ _ secondClose)
        (Fin.cases (scaled_distance _ _ _ thirdClose) (fun bad => Fin.elim0 bad))) index
  have totalWeight : FiniteSum.Fin.sumFin weights = 1 := by
    rewrite [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
    change (1 - u - v) + (u + (v + 0)) = 1
    ring1
  have complement : Cast.Path.ofCoordinate (1 - u - v) =
      (1 : Canonical) - Cast.Path.ofCoordinate u - Cast.Path.ofCoordinate v := by
    apply Basic.ext <;>
      simp only [Cast.Path.ofCoordinate, Basic.sub_re, Basic.sub_im, Basic.one_re, Basic.one_im,
        -eq_self, -iff_self] <;> ring1
  have totalTerms : FiniteSum.Fin.sumFin terms = value first second third u v - anchor := by
    rewrite [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
    change Cast.Path.ofCoordinate (1 - u - v) * (first - anchor) +
      (Cast.Path.ofCoordinate u * (second - anchor) +
        (Cast.Path.ofCoordinate v * (third - anchor) + 0)) = _
    rewrite [complement]
    unfold value
    ring1
  have weighted := Norm.Weighted.normSq_sumFin_weighted terms weights nonnegative bounded
  rewrite [Norm.Basic.normSq_eq_canonical] at weighted
  have scalar : (norm / 1024) * (FiniteSum.Fin.sumFin weights) ^ 2 = norm / 1024 := by
    rewrite [totalWeight]
    ring1
  exact (congrArg Canonical.normSq totalTerms).symm.trans_le (weighted.trans_eq scalar)

/-- The affine root triangle retains the anchor-norm-squared quarter lower bound for its square. -/
theorem square_lower (anchor first second third : Canonical) (norm : Rational)
    (norm_eq : norm = Canonical.normSq anchor)
    (firstClose : Canonical.normSq (first - anchor) ≤ norm / 1024)
    (secondClose : Canonical.normSq (second - anchor) ≤ norm / 1024)
    (thirdClose : Canonical.normSq (third - anchor) ≤ norm / 1024)
    (u v : Rational) (inside : Inside u v) :
    norm ^ 2 / 16 ≤ Canonical.normSq ((value first second third u v) ^ 2) := by
  have close := (distance anchor first second third norm firstClose secondClose thirdClose u v inside).trans_eq
    (congrArg (fun value : Rational => value / 1024) norm_eq)
  have lower := chord_square_lower close (time := 1)
    ⟨by decide +kernel, Order.Basic.le_refl _⟩
  have endpoint := Affine.line_one anchor (value first second third u v)
  exact (congrArg (fun value : Rational => value ^ 2 / 16) norm_eq).trans_le
    (lower.trans_eq (congrArg (fun value : Canonical => Canonical.normSq (value ^ 2)) endpoint))

/-- Actual anchor residual and whole-triangle radicand movement pay the uniform affine-root square residual. -/
theorem square_residual (polynomial : GaussianBivariate) (triangle : CoordinateTriangle)
    (anchor parameter first second third : Canonical) (norm : Rational)
    (norm_eq : norm = Canonical.normSq anchor)
    (firstClose : Canonical.normSq (first - anchor) ≤ norm / 1024)
    (secondClose : Canonical.normSq (second - anchor) ≤ norm / 1024)
    (thirdClose : Canonical.normSq (third - anchor) ≤ norm / 1024)
    (residual : Canonical.normSq (anchor ^ 2 - parameter) ≤ norm ^ 2 / 1024)
    (movement : ∀ u v, Inside u v →
      Canonical.normSq (radicand polynomial (point triangle u v) - parameter) ≤ norm ^ 2 / 1024)
    (u v : Rational) (inside : Inside u v) :
    Canonical.normSq ((value first second third u v) ^ 2 - radicand polynomial (point triangle u v)) ≤
      norm ^ 2 / 32 := by
  have close := (distance anchor first second third norm firstClose secondClose thirdClose u v inside).trans_eq
    (congrArg (fun value : Rational => value / 1024) norm_eq)
  have anchorResidual := residual.trans_eq (congrArg (fun value : Rational => value ^ 2 / 1024) norm_eq)
  have moved := (movement u v inside).trans_eq (congrArg (fun value : Rational => value ^ 2 / 1024) norm_eq)
  have bound := chord_square_residual close anchorResidual moved (time := 1)
    ⟨by decide +kernel, Order.Basic.le_refl _⟩
  have endpoint := Affine.line_one anchor (value first second third u v)
  exact ((congrArg (fun value : Canonical => Canonical.normSq
    (value ^ 2 - radicand polynomial (point triangle u v))) endpoint).symm.trans_le bound).trans_eq
      (congrArg (fun value : Rational => value ^ 2 / 32) norm_eq.symm)

/-- The two actual homogeneous bounds differ by their retained half margin. -/
private theorem margin_eq (norm : Rational) : norm ^ 2 / 16 - norm ^ 2 / 32 = norm ^ 2 / 32 := by
  rewrite [Field.div_eq_mul_inv_direct]
  have coefficients : (16 : Rational)⁻¹ - 32⁻¹ = 32⁻¹ := by decide +kernel
  exact (show norm ^ 2 * (16 : Rational)⁻¹ - norm ^ 2 * 32⁻¹ =
    norm ^ 2 * ((16 : Rational)⁻¹ - 32⁻¹) by ring1).trans (congrArg (fun value => norm ^ 2 * value) coefficients)

/-- The actual square and its error have the displayed positive homogeneous dominance margin. -/
theorem dominance (polynomial : GaussianBivariate) (triangle : CoordinateTriangle)
    (anchor parameter first second third : Canonical) (norm : Rational)
    (norm_eq : norm = Canonical.normSq anchor)
    (firstClose : Canonical.normSq (first - anchor) ≤ norm / 1024)
    (secondClose : Canonical.normSq (second - anchor) ≤ norm / 1024)
    (thirdClose : Canonical.normSq (third - anchor) ≤ norm / 1024)
    (residual : Canonical.normSq (anchor ^ 2 - parameter) ≤ norm ^ 2 / 1024)
    (movement : ∀ u v, Inside u v →
      Canonical.normSq (radicand polynomial (point triangle u v) - parameter) ≤ norm ^ 2 / 1024)
    (u v : Rational) (inside : Inside u v) :
    norm ^ 2 / 32 ≤ Canonical.normSq ((value first second third u v) ^ 2) -
      Canonical.normSq ((value first second third u v) ^ 2 - radicand polynomial (point triangle u v)) := by
  have lower := square_lower anchor first second third norm norm_eq firstClose secondClose thirdClose u v inside
  have upper := square_residual polynomial triangle anchor parameter first second third norm norm_eq
    firstClose secondClose thirdClose residual movement u v inside
  exact (margin_eq norm).symm.trans_le (Order.Arithmetic.sub_le_sub_direct lower upper)

/-- A strictly positive anchor norm makes the retained homogeneous face margin strictly positive. -/
theorem margin_positive {norm : Rational} (positive : 0 < norm) : 0 < norm ^ 2 / 32 :=
  Order.Field.div_pos_direct (Order.Arithmetic.pow_pos_direct positive 2)
    (Data.Rat.Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide +kernel))

/-- The starting root or parameter vertex of each original cyclic side occurrence. -/
@[expose] def sideFirst (first second third : Canonical) : Fin 3 → Canonical :=
  Fin.cases first (Fin.cases second (Fin.cases third (fun index => Fin.elim0 index)))

/-- The finishing root or parameter vertex of each original cyclic side occurrence. -/
@[expose] def sideLast (first second third : Canonical) : Fin 3 → Canonical :=
  Fin.cases second (Fin.cases third (Fin.cases first (fun index => Fin.elim0 index)))

/-- The exact three cyclic side maps in the original barycentric domain. -/
@[expose] def sideCoordinates : Fin 3 → Rational → Rational × Rational :=
  Fin.cases (fun time => (time, 0))
    (Fin.cases (fun time => (1 - time, time))
      (Fin.cases (fun time => (0, 1 - time)) (fun index => Fin.elim0 index)))

/-- Every original unit side parameter remains in the SAME closed barycentric triangle. -/
theorem side_inside (side : Fin 3) (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) :
    Inside (sideCoordinates side time).1 (sideCoordinates side time).2 := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun bad => Fin.elim0 bad))) side
  · exact ⟨inside.1, Order.Basic.le_refl _, (show time + 0 = time by ring1).trans_le inside.2⟩
  · exact ⟨Order.Arithmetic.sub_nonneg_direct inside.2, inside.1,
      (show 1 - time + time = (1 : Rational) by ring1).le⟩
  · exact ⟨Order.Basic.le_refl _, Order.Arithmetic.sub_nonneg_direct inside.2,
      (show 0 + (1 - time) = (1 : Rational) - time by ring1).trans_le
        ((Order.Arithmetic.sub_le_sub_left_direct inside.1 1).trans_eq (by ring1))⟩

/-- The actual real embedding preserves a retained complementary scalar. -/
private theorem embed_complement (time : Rational) : Cast.Path.ofCoordinate (1 - time) =
    (1 : Canonical) - Cast.Path.ofCoordinate time := by
  apply Basic.ext <;>
    simp only [Cast.Path.ofCoordinate, Basic.sub_re, Basic.sub_im, Basic.one_re, Basic.one_im,
      -eq_self, -iff_self] <;> ring1

/-- All three actual side restrictions are the original affine chords of their two retained vertex values. -/
theorem side_value (first second third : Canonical) (side : Fin 3) (time : Rational) :
    value first second third (sideCoordinates side time).1 (sideCoordinates side time).2 =
      Affine.line (sideFirst first second third side)
        (sideLast first second third side - sideFirst first second third side) time := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun bad => Fin.elim0 bad))) side
  · change value first second third time 0 = Affine.line first (second - first) time
    unfold value Affine.line
    change first + Cast.Path.ofCoordinate time * (second - first) + 0 * (third - first) = _
    ring1
  · change value first second third (1 - time) time = Affine.line second (third - second) time
    unfold value Affine.line
    rewrite [embed_complement]
    ring1
  · change value first second third 0 (1 - time) = Affine.line third (first - third) time
    unfold value Affine.line
    rewrite [embed_complement]
    change first + 0 * (second - first) + (1 - Cast.Path.ofCoordinate time) * (third - first) = _
    ring1

/-- The original bivariate polynomial restricted to one actual cyclic parameter-plane edge. -/
def sidePolynomial (polynomial : GaussianBivariate) (triangle : CoordinateTriangle) (side : Fin 3) :
    Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  let first := sideFirst triangle.first triangle.second triangle.third side
  let last := sideLast triangle.first triangle.second triangle.third side
  Bivariate.Specialization.Affine.composeLine polynomial
    (⟨first.re, 0⟩ : Canonical) (⟨last.re - first.re, 0⟩ : Canonical)
    (⟨first.im, 0⟩ : Canonical) (⟨last.im - first.im, 0⟩ : Canonical)

/-- The retained side polynomial evaluates at the SAME actual affine parameter-plane point. -/
theorem sidePolynomial_eval (polynomial : GaussianBivariate) (triangle : CoordinateTriangle)
    (side : Fin 3) (time : Rational) :
    (sidePolynomial polynomial triangle side).eval (Cast.Path.ofCoordinate time) =
      radicand polynomial (point triangle (sideCoordinates side time).1 (sideCoordinates side time).2) := by
  let first := sideFirst triangle.first triangle.second triangle.third side
  let last := sideLast triangle.first triangle.second triangle.third side
  have outer : (⟨first.re, 0⟩ : Canonical) + Cast.Path.ofCoordinate time * (⟨last.re - first.re, 0⟩ : Canonical) =
      (⟨(Affine.line first (last - first) time).re, 0⟩ : Canonical) := by
    apply Basic.ext <;>
      simp only [Affine.line, Cast.Path.ofCoordinate, Basic.add_re, Basic.add_im,
        Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, -eq_self, -iff_self] <;> ring1
  have inner : (⟨first.im, 0⟩ : Canonical) + Cast.Path.ofCoordinate time * (⟨last.im - first.im, 0⟩ : Canonical) =
      (⟨(Affine.line first (last - first) time).im, 0⟩ : Canonical) := by
    apply Basic.ext <;>
      simp only [Affine.line, Cast.Path.ofCoordinate, Basic.add_re, Basic.add_im,
        Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, -eq_self, -iff_self] <;> ring1
  have exactEval := Bivariate.Specialization.Affine.eval_composeLine polynomial
    (⟨first.re, 0⟩ : Canonical) (⟨last.re - first.re, 0⟩ : Canonical)
    (⟨first.im, 0⟩ : Canonical) (⟨last.im - first.im, 0⟩ : Canonical) (Cast.Path.ofCoordinate time)
  exact (exactEval.trans (congrArg₂ (Bivariate.Basic.eval polynomial) outer inner)).trans
    (congrArg (radicand polynomial) (side_value triangle.first triangle.second triangle.third side time).symm)

/-- Materialized original side polynomial tables with their complete affine-specialization factories. -/
@[expose] def Sides (polynomial : GaussianBivariate) (triangle : CoordinateTriangle) : Type _ :=
  Data.Vector.DependentVector (fun side : Fin 3 =>
    { value : Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial //
      value = sidePolynomial polynomial triangle side })

/-- Construct each of the three original restriction tables once before any side consumer uses them. -/
def sides (polynomial : GaussianBivariate) (triangle : CoordinateTriangle) : Sides polynomial triangle :=
  Data.Vector.DependentVector.ofFn (fun side =>
    let value := sidePolynomial polynomial triangle side
    ⟨value, rfl⟩)

/-- Every retained side table reads the SAME actual bivariate parameter-plane restriction. -/
theorem sides_eval {polynomial : GaussianBivariate} {triangle : CoordinateTriangle}
    (retained : Sides polynomial triangle) (side : Fin 3) (time : Rational) :
    (retained.get side).val.eval (Cast.Path.ofCoordinate time) =
      radicand polynomial (point triangle (sideCoordinates side time).1 (sideCoordinates side time).2) :=
  (congrArg (fun value => value.eval (Cast.Path.ofCoordinate time)) (retained.get side).property).trans
    (sidePolynomial_eval polynomial triangle side time)

/-- A retained triangle's actual side data uses the original coordinate-square and that SAME supplied restriction. -/
@[expose] def SideData {polynomial : GaussianBivariate} {triangle : CoordinateTriangle}
    (retained : Sides polynomial triangle) (first second third : Canonical) (side : Fin 3) : Prop :=
  Comparison.Basic.LineData
    (Path.Components.pathReal (Power.Coordinate.coordinatePositivePower 1)
      (sideFirst first second third side) (sideLast first second third side - sideFirst first second third side))
    (Path.Components.pathImag (Power.Coordinate.coordinatePositivePower 1)
      (sideFirst first second third side) (sideLast first second third side - sideFirst first second third side))
    (Path.Components.pathReal (retained.get side).val 0 1)
    (Path.Components.pathImag (retained.get side).val 0 1) 0 1

/-- The genuine homogeneous face margin constructs original finite comparison data on each SAME retained side table. -/
theorem sideData (polynomial : GaussianBivariate) (triangle : CoordinateTriangle)
    (retained : Sides polynomial triangle)
    (anchor parameter first second third : Canonical) (norm : Rational) (norm_eq : norm = Canonical.normSq anchor)
    (positive : 0 < norm)
    (firstClose : Canonical.normSq (first - anchor) ≤ norm / 1024)
    (secondClose : Canonical.normSq (second - anchor) ≤ norm / 1024)
    (thirdClose : Canonical.normSq (third - anchor) ≤ norm / 1024)
    (residual : Canonical.normSq (anchor ^ 2 - parameter) ≤ norm ^ 2 / 1024)
    (movement : ∀ u v, Inside u v →
      Canonical.normSq (radicand polynomial (point triangle u v) - parameter) ≤ norm ^ 2 / 1024)
    (side : Fin 3) : SideData retained first second third side := by
  let start := sideFirst first second third side
  let finish := sideLast first second third side
  let A := Path.Components.pathReal (Power.Coordinate.coordinatePositivePower 1)
    start (finish - start)
  let B := Path.Components.pathImag (Power.Coordinate.coordinatePositivePower 1)
    start (finish - start)
  let U := Path.Components.pathReal (retained.get side).val 0 1
  let V := Path.Components.pathImag (retained.get side).val 0 1
  let C := U - A
  let D := V - B
  have unitPoint (time : Rational) : Affine.line (0 : Canonical) 1 time = Cast.Path.ofCoordinate time := by
    unfold Affine.line
    ring1
  have sourceNorm (time : Rational) : A.eval time ^ 2 + B.eval time ^ 2 =
      Canonical.normSq ((Affine.line start (finish - start) time) ^ 2) := by
    simp only [A, B, Path.Components.eval_pathReal, Path.Components.eval_pathImag,
      Power.Coordinate.coordinatePositivePower_eval, Canonical.normSq, pow_two, -eq_self, -iff_self]
    exact congrArg Canonical.normSq (pow_two _)
  have errorNorm (time : Rational) : C.eval time ^ 2 + D.eval time ^ 2 =
      Canonical.normSq ((Affine.line start (finish - start) time) ^ 2 -
        (retained.get side).val.eval (Cast.Path.ofCoordinate time)) := by
    simp only [C, D, A, B, U, V, eval_sub, Path.Components.eval_pathReal,
      Path.Components.eval_pathImag, Power.Coordinate.coordinatePositivePower_eval, unitPoint,
      Canonical.normSq, Basic.sub_re, Basic.sub_im, pow_two, -eq_self, -iff_self]
    rewrite [show Affine.line start (finish - start) time ^ (1 + 1) =
      Affine.line start (finish - start) time * Affine.line start (finish - start) time from pow_two _]
    ring1
  have lower (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) : norm ^ 2 / 16 ≤ A.eval time ^ 2 + B.eval time ^ 2 :=
    (square_lower anchor first second third norm norm_eq firstClose secondClose thirdClose
      _ _ (side_inside side time inside)).trans_eq
        ((congrArg (fun value : Canonical => Canonical.normSq (value ^ 2)) (side_value _ _ _ side time)).trans
          (sourceNorm time).symm)
  have upper (time : Rational) (inside : 0 ≤ time ∧ time ≤ 1) : C.eval time ^ 2 + D.eval time ^ 2 ≤ norm ^ 2 / 32 :=
    (errorNorm time).trans_le
      ((congrArg₂ (fun root base : Canonical => Canonical.normSq (root ^ 2 - base))
        (side_value first second third side time).symm (sides_eval retained side time)).trans_le
          (square_residual polynomial triangle anchor parameter first second third norm norm_eq
            firstClose secondClose thirdClose residual movement _ _ (side_inside side time inside)))
  let source : Pair.Basic.Certificate A B parameterInterval :=
    ⟨norm ^ 2 / 16, Order.Field.div_pos_direct (Order.Arithmetic.pow_pos_direct positive 2)
      (Data.Rat.Fraction.Cast.Order.natCast_pos_direct (n := 16) (by decide +kernel)), lower⟩
  exact Comparison.Dominance.lineData_of_normDominance
    (C := C) (D := D) (by decide +kernel) source (norm ^ 2 / 32) (margin_positive positive)
    (fun time inside => (margin_eq norm).symm.trans_le
      (Order.Arithmetic.sub_le_sub_direct (lower time inside) (upper time inside)))
    (by intro time; change U.eval time = A.eval time + (U - A).eval time; rewrite [eval_sub]; ring1)
    (by intro time; change V.eval time = B.eval time + (V - B).eval time; rewrite [eval_sub]; ring1)

end Purelib.Riemann.RootContinuation.SquareRootTraceHomotopy.Triangle

end
