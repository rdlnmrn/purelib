module

public import Purelib.Riemann.RootContinuation.SquareRootTrace
public import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Affine
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic

/-! # Exact affine images of the same polynomial root-trace caches

An actual composeLine factory identifies the two scalar evaluations. The
root values, norms, displacement, residual and movement caches are kept;
only the original base vertices and their evaluation indices change.
This operation does not identify curves or Frames or acquire a new root.
-/

public section

namespace Purelib.Riemann.RootContinuation.SquareRootTrace

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Geometry.Rational

namespace AffineImage

/-- The exact Gaussian affine point used by the original composeLine evaluation law. -/
@[expose] def point (origin direction value : Canonical) : Canonical := origin + value * direction

/-- The actual cached composeLine polynomial evaluates at its SAME original affine image. -/
theorem eval (polynomial pullback : CoefficientPolynomial) (origin direction : Canonical)
    (factory : pullback = Substitution.Affine.composeLine polynomial origin direction) (value : Canonical) :
    pullback.eval value = polynomial.eval (point origin direction value) :=
  (congrArg (fun retained : CoefficientPolynomial => retained.eval value) factory).trans
    (Substitution.Affine.eval_composeLineGaussian polynomial origin direction value)

/-- The affine image of the parameter chord is exactly the chord of the two actual image endpoints. -/
theorem chord (origin direction first last : Canonical) (time : Rational) :
    point origin direction (Affine.line first (last - first) time) =
      Affine.line (point origin direction first)
        (point origin direction last - point origin direction first) time := by
  unfold point Affine.line
  ring1

end AffineImage

variable {polynomial pullback : CoefficientPolynomial} (origin direction : Canonical)
    (factory : pullback = Substitution.Affine.composeLine polynomial origin direction)
    {first last baseFirst baseLast : Canonical}

namespace EdgeData

/-- Map one GIVEN edge's base points through its actual affine polynomial factory, retaining every scalar cache. -/
def affineImage (data : EdgeData pullback first last baseFirst baseLast) :
    EdgeData polynomial first last (AffineImage.point origin direction baseFirst)
      (AffineImage.point origin direction baseLast) where
  rootNorm := data.rootNorm
  rootNorm_eq := data.rootNorm_eq
  distance := data.distance
  distance_eq := data.distance_eq
  residual := data.residual
  residual_eq := data.residual_eq.trans
    (congrArg (fun value : Canonical => Canonical.normSq (first ^ 2 - value))
      (AffineImage.eval polynomial pullback origin direction factory baseFirst))
  variation := data.variation
  variation_eq := by
    intro time
    have firstEq := AffineImage.eval polynomial pullback origin direction factory
      (Affine.line baseFirst (baseLast - baseFirst) time)
    have lastEq := AffineImage.eval polynomial pullback origin direction factory baseFirst
    have points := congrArg polynomial.eval (AffineImage.chord origin direction baseFirst baseLast time)
    exact (data.variation_eq time).trans
      (congrArg₂ (fun first last : Canonical => first - last) (firstEq.trans points) lastEq)
  movementBound := data.movementBound
  movementBound_valid := data.movementBound_valid

/-- The actual affine image keeps the original norm, distance, residual, variation polynomial and movement bound. -/
theorem affineImage_caches (data : EdgeData pullback first last baseFirst baseLast) :
    let mapped := data.affineImage origin direction factory
    mapped.rootNorm = data.rootNorm ∧ mapped.distance = data.distance ∧ mapped.residual = data.residual ∧
      mapped.variation = data.variation ∧ mapped.movementBound = data.movementBound := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

end EdgeData

namespace Edge

/-- Map the SAME checked trace edge through the exact original affine polynomial factory. -/
def affineImage (edge : Edge pullback first last baseFirst baseLast) :
    Edge polynomial first last (AffineImage.point origin direction baseFirst)
      (AffineImage.point origin direction baseLast) :=
  ⟨edge.data.affineImage origin direction factory, edge.checked⟩

end Edge

namespace Chain

/-- Map the GIVEN whole root/base trace while retaining its complete original ordered root list. -/
def affineImage : {first baseFirst : Canonical} → {roots bases : List Canonical} →
    Chain pullback first roots baseFirst bases →
      Chain polynomial first roots (AffineImage.point origin direction baseFirst)
        (bases.map (AffineImage.point origin direction))
  | _, _, _, _, .nil first base => .nil first (AffineImage.point origin direction base)
  | _, _, _, _, .cons edge remaining =>
      .cons (edge.affineImage origin direction factory) (affineImage remaining)
termination_by structural _ _ _ _ trace => trace

end Chain

end Purelib.Riemann.RootContinuation.SquareRootTrace

end
