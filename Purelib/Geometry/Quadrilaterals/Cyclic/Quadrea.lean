module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Circles.Concyclic.Determinant
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Determinant
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Polygons.SignedArea.Basic
import Purelib.Geometry.Quadrilaterals.Basic
public import Purelib.Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial
import Purelib.Geometry.Quadrilaterals.Cyclic.Determinant
import Purelib.Geometry.Trigonometry.QuadTriple.Quadruple
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
public import Purelib.Geometry.Quadrilaterals.Cyclic.Basic
import Purelib.Algebra.Group.Negation
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Geometry.Plane.Point
open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Polygons

open Purelib.Geometry.Quadrilaterals.Basic

open Purelib.Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial

open Purelib.Geometry.Trigonometry.QuadTriple

section
@[expose] public section

/-!
# Divine Proportions, Theorem 112: cyclic quadrilateral quadrea

The source obtains the quadrea equation through two diagonal quotients and a
long circumquadrance elimination.  The finite polynomial underneath is much
shorter: for any four displayed points, the difference between the requested
quadrea polynomial and zero is `-64` times the square of their circle
determinant.  Cyclicity therefore proves Theorem 112 directly, without the
source's solvability and nonzero-product assumptions.
-/

namespace Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

/-- The side-quadrance coefficient in the cyclic quadrilateral quadrea equation.

It is the square of the sum of the four side quadrances minus twice their squared sum. -/
def cyclicQuadreaCoefficientM (q₁₂ q₂₃ q₃₄ q₁₄ : K) : K :=
  (q₁₂ + q₂₃ + q₃₄ + q₁₄) ^ 2 -
    2 * (q₁₂ ^ 2 + q₂₃ ^ 2 + q₃₄ ^ 2 + q₁₄ ^ 2)

/-- The quadrea residual from the six scalar Gram identities of three planar displacements.

Retaining squared norms, dot products and signed determinants prevents expanding their coordinate polynomials together.
-/
private theorem quadrea_of_gram_identities
    (a b c p q r x y z : K)
    (xx : x ^ 2 = a * b - p ^ 2) (yy : y ^ 2 = b * c - q ^ 2)
    (zz : z ^ 2 = a * c - r ^ 2) (xy : x * y = p * q - b * r)
    (xz : x * z = a * q - p * r) (yz : y * z = c * p - q * r) :
    let q₁₂ := a + b - 2 * p
    let q₂₃ := b + c - 2 * q
    let area := 4 * (x + y) ^ 2
    area ^ 2 - 2 * cyclicQuadreaCoefficientM q₁₂ q₂₃ c a * area +
      Quadrilateral.circumquadranceCoefficientP q₁₂ q₂₃ c a =
        -64 * (a * y - b * z + c * x) ^ 2 := by
  have areaEq : 4 * (x + y) ^ 2 =
      4 * (a * b + b * c - p ^ 2 - q ^ 2 + 2 * p * q - 2 * b * r) := by
    calc
      4 * (x + y) ^ 2 = 4 * (x ^ 2 + y ^ 2 + 2 * (x * y)) := by ring1
      _ = _ := by rw [xx, yy, xy]; ring1
  have determinantEq : (a * y - b * z + c * x) ^ 2 =
      a ^ 2 * (b * c - q ^ 2) + b ^ 2 * (a * c - r ^ 2) + c ^ 2 * (a * b - p ^ 2) -
        2 * a * b * (c * p - q * r) + 2 * a * c * (p * q - b * r) -
        2 * b * c * (a * q - p * r) := by
    calc
      (a * y - b * z + c * x) ^ 2 =
          a ^ 2 * y ^ 2 + b ^ 2 * z ^ 2 + c ^ 2 * x ^ 2 -
            2 * a * b * (y * z) + 2 * a * c * (x * y) - 2 * b * c * (x * z) := by ring1
      _ = _ := by rw [yy, zz, xx, yz, xy, xz]
  dsimp only
  unfold cyclicQuadreaCoefficientM Quadrilateral.circumquadranceCoefficientP
    Quadruple.quadrupleQuadFunction
  rw [areaEq, determinantEq]
  ring1

/-- The residual of the quadrea polynomial is minus sixty-four times the squared circle determinant.

This four-point identity measures the polynomial obstruction to cyclicity without assuming the points lie on a circle.
-/
theorem cyclicQuadrea_polynomial_identity
    (first second third fourth : Plane.Point K) :
    let area := SignedArea.Basic.polygonQuadrea [first, second, third, fourth]
    let q₁₂ := Quadrance.quadrance first second
    let q₂₃ := Quadrance.quadrance second third
    let q₃₄ := Quadrance.quadrance third fourth
    let q₁₄ := Quadrance.quadrance first fourth
    area ^ 2 -
        2 * cyclicQuadreaCoefficientM q₁₂ q₂₃ q₃₄ q₁₄ * area +
        Quadrilateral.circumquadranceCoefficientP q₁₂ q₂₃ q₃₄ q₁₄ =
      -64 * Quadrilateral.coordinateCircleDeterminant first second third fourth ^ 2 := by
  dsimp only
  let a := Quadrance.quadrance first fourth
  let b := Quadrance.quadrance second fourth
  let c := Quadrance.quadrance third fourth
  let p := (first.x - fourth.x) * (second.x - fourth.x) + (first.y - fourth.y) * (second.y - fourth.y)
  let q := (second.x - fourth.x) * (third.x - fourth.x) + (second.y - fourth.y) * (third.y - fourth.y)
  let r := (first.x - fourth.x) * (third.x - fourth.x) + (first.y - fourth.y) * (third.y - fourth.y)
  let x := Incidence.pointDeterminant fourth first second
  let y := Incidence.pointDeterminant fourth second third
  let z := Incidence.pointDeterminant fourth first third
  have xx : x ^ 2 = a * b - p ^ 2 := by
    dsimp only [x, a, b, p, Incidence.pointDeterminant, Quadrance.quadrance]
    ring1
  have yy : y ^ 2 = b * c - q ^ 2 := by
    dsimp only [y, b, c, q, Incidence.pointDeterminant, Quadrance.quadrance]
    ring1
  have zz : z ^ 2 = a * c - r ^ 2 := by
    dsimp only [z, a, c, r, Incidence.pointDeterminant, Quadrance.quadrance]
    ring1
  have xy : x * y = p * q - b * r := by
    dsimp only [x, y, p, q, b, r, Incidence.pointDeterminant, Quadrance.quadrance]
    ring1
  have xz : x * z = a * q - p * r := by
    dsimp only [x, z, a, q, p, r, Incidence.pointDeterminant, Quadrance.quadrance]
    ring1
  have yz : y * z = c * p - q * r := by
    dsimp only [y, z, c, p, q, r, Incidence.pointDeterminant, Quadrance.quadrance]
    ring1
  have firstSide : Quadrance.quadrance first second = a + b - 2 * p := by
    dsimp only [a, b, p, Quadrance.quadrance]
    ring1
  have secondSide : Quadrance.quadrance second third = b + c - 2 * q := by
    dsimp only [b, c, q, Quadrance.quadrance]
    ring1
  have doubleArea : SignedArea.Basic.polygonDoubleSignedArea [first, second, third, fourth] = x + y := by
    dsimp only [SignedArea.Basic.polygonDoubleSignedArea, SignedArea.Basic.polygonDoubleSignedAreaAux,
      Determinant.positionDeterminant, x, y, Incidence.pointDeterminant]
    ring1
  have areaEq : SignedArea.Basic.polygonQuadrea [first, second, third, fourth] = 4 * (x + y) ^ 2 :=
    congrArg (fun value : K => 4 * value ^ 2) doubleArea
  rw [areaEq, firstSide, secondSide,
    Quadrilateral.coordinateCircleDeterminant_eq_fourPointCircleDeterminant]
  exact quadrea_of_gram_identities a b c p q r x y z xx yy zz xy xz yz

/-- Theorem 112 (Cyclic quadrilateral quadrea), strengthened: every displayed cyclic quadrilateral satisfies the
equation, with no solvability or nonzero coefficient assumptions. -/
theorem cyclic_quadrilateral_quadrea
    (quadrilateral : Quadrilaterals.Basic.Quadrilateral K) (cyclic : quadrilateral.IsCyclic) :
    let area := SignedArea.Basic.polygonQuadrea [quadrilateral.first, quadrilateral.second,
      quadrilateral.third, quadrilateral.fourth]
    let q₁₂ := Quadrance.quadrance quadrilateral.first quadrilateral.second
    let q₂₃ := Quadrance.quadrance quadrilateral.second quadrilateral.third
    let q₃₄ := Quadrance.quadrance quadrilateral.third quadrilateral.fourth
    let q₁₄ := Quadrance.quadrance quadrilateral.first quadrilateral.fourth
    area ^ 2 -
        2 * cyclicQuadreaCoefficientM q₁₂ q₂₃ q₃₄ q₁₄ * area +
        Quadrilateral.circumquadranceCoefficientP q₁₂ q₂₃ q₃₄ q₁₄ = 0 := by
  dsimp only
  have determinantZero :=
    Quadrilateral.coordinateCircleDeterminant_eq_zero_of_isCyclic quadrilateral cyclic
  calc
    SignedArea.Basic.polygonQuadrea [quadrilateral.first, quadrilateral.second,
          quadrilateral.third, quadrilateral.fourth] ^ 2 -
        2 * cyclicQuadreaCoefficientM
          (Quadrance.quadrance quadrilateral.first quadrilateral.second)
          (Quadrance.quadrance quadrilateral.second quadrilateral.third)
          (Quadrance.quadrance quadrilateral.third quadrilateral.fourth)
          (Quadrance.quadrance quadrilateral.first quadrilateral.fourth) *
          SignedArea.Basic.polygonQuadrea [quadrilateral.first, quadrilateral.second,
            quadrilateral.third, quadrilateral.fourth] +
        Quadrilateral.circumquadranceCoefficientP
          (Quadrance.quadrance quadrilateral.first quadrilateral.second)
          (Quadrance.quadrance quadrilateral.second quadrilateral.third)
          (Quadrance.quadrance quadrilateral.third quadrilateral.fourth)
          (Quadrance.quadrance quadrilateral.first quadrilateral.fourth) =
      -64 * Quadrilateral.coordinateCircleDeterminant quadrilateral.first
        quadrilateral.second quadrilateral.third quadrilateral.fourth ^ 2 :=
      cyclicQuadrea_polynomial_identity quadrilateral.first
        quadrilateral.second quadrilateral.third quadrilateral.fourth
    _ = 0 := by rw [determinantZero]; ring1
end

end Purelib.Geometry.Quadrilaterals.Basic.Quadrilateral

end
