module

import Purelib.Algebra.Quadratic.Pair.Gaussian.Rational
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Gaussian.Provenance.Power
import Purelib.Riemann.RootContinuation.SquareRootSidecar

/-!
# Original pair coordinates and independently retained root sheets

The pair multiplication certificate reduces the product of two shifted
generators to one from the supplied square equation. The concrete isolation
client retains each selected original sheet and passes its actual sidecar.
-/

namespace TestPurelib.Algebra.QuadraticPairGaussian

open Purelib.Algebra.Quadratic
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Riemann.RootContinuation

/-- The coordinates of the positive unit shift of the retained generator. -/
private def left : Pair Rational (-2) := ⟨1, 1⟩

/-- The coordinates of the negative unit shift of the same retained generator. -/
private def right : Pair Rational (-2) := ⟨-1, 1⟩

/-- The original pair ring's negative parameter convention gives the scalar product one. -/
private theorem product_coordinates : left * right = Pair.scalar 1 := by decide

/-- The supplied degree-two equation gives the rational result at the original interpreted product channel. -/
private def productSidecar (generator : CoherentNamed) (identity : PowerIdentity generator 2 2) :
    RationalSidecar (CoherentNamed.mul (Pair.Gaussian.denoteRational generator left)
      (Pair.Gaussian.denoteRational generator right)) := by
  have sign_eq : Cast.CoordinateTaylor.ofCoordinate (-(-2 : Rational)) = (2 : Basic.Canonical) := by
    apply Basic.ext
    · change -(-2 : Rational) = (2 : Basic.Canonical).re
      rewrite [_root_.neg_neg]
      exact (Cast.natCast_re 2).symm
    · exact (Cast.natCast_im 2).symm
  have retained : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate (-(-2 : Rational))) := by
    rewrite [sign_eq]
    exact identity
  have multiplication := Pair.Gaussian.denoteRational_mul (parameter := -2) generator retained left right
  rewrite [product_coordinates] at multiplication
  exact ⟨1, NamedEquivalent.trans multiplication (Pair.Gaussian.denoteRational_scalar generator 1)⟩

/-- The actual retained root sidecar supplies the equation used by the original pair product. -/
private def fromSidecar (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator)
    (parameter_eq : sidecar.parameter = 2) :
    RationalSidecar (CoherentNamed.mul (Pair.Gaussian.denoteRational generator left)
      (Pair.Gaussian.denoteRational generator right)) := by
  have identity : PowerIdentity generator 2 2 := by
    have retained := PowerIdentity.ofSquare sidecar.square
    rewrite [parameter_eq] at retained
    exact retained
  exact productSidecar generator identity

example (sheet : Fin 2) :
    let retained := SquareRootSidecar.isolated 2 sheet
    RationalSidecar (CoherentNamed.mul (Pair.Gaussian.denoteRational retained.1 left)
      (Pair.Gaussian.denoteRational retained.1 right)) :=
  let retained := SquareRootSidecar.isolated 2 sheet
  fromSidecar retained.1 retained.2 (SquareRootSidecar.isolated_parameter 2 sheet)

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 (-1))
    (first second : Pair Basic.Canonical 1) :
    NamedEquivalent (CoherentNamed.mul (Pair.Gaussian.denote id generator first)
      (Pair.Gaussian.denote id generator second)).name (Pair.Gaussian.denote id generator (first * second)).name :=
  Pair.Gaussian.denote_mul id (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    generator identity first second

end TestPurelib.Algebra.QuadraticPairGaussian
