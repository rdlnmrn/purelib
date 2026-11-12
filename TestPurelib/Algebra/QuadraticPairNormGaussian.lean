module

import Purelib.Algebra.Quadratic.Pair.Gaussian.Norm
import Purelib.Algebra.Quadratic.Pair.Norm.Rational
import Purelib.Data.Gaussian.Cast
import Purelib.Riemann.RootContinuation.SquareRootSidecar

/-!
# Operational inverse coordinates on either retained root sheet

Every nonzero original pair at parameter minus two has an interpreted inverse
whose product compares to the exact unit channel. The original supplied root
sidecar provides the degree-two equation on either isolated sheet.
-/

namespace TestPurelib.Algebra.QuadraticPairNormGaussian

open Purelib.Algebra.Quadratic (Pair)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Riemann.RootContinuation

/-- A retained generator equation certifies the product with the original pair's computed inverse. -/
private def inverseComparison (generator : CoherentNamed) (identity : PowerIdentity generator 2 2)
    (value : Pair Rational (-2)) (nonzero : value ≠ 0) :
    NamedEquivalent (CoherentNamed.mul
      (Pair.Gaussian.denote Cast.CoordinateTaylor.ofCoordinate generator value)
      (Pair.Gaussian.denote Cast.CoordinateTaylor.ofCoordinate generator value.inverse)).name
      (Coherence.exact 1).name := by
  have sign : -Cast.CoordinateTaylor.ofCoordinate (-2 : Rational) = (2 : Basic.Canonical) := by decide +kernel
  have retained : PowerIdentity generator 2 (-Cast.CoordinateTaylor.ofCoordinate (-2 : Rational)) := by
    rewrite [sign]
    exact identity
  exact Pair.Gaussian.denote_inverse Cast.CoordinateTaylor.ofCoordinate Cast.ofCoordinate_zero
    (by decide +kernel) Cast.ofCoordinate_add Cast.ofCoordinate_mul Cast.ofCoordinate_sub generator retained value
    (Pair.norm_ne_zero_of_inspection (Square.inspect 2) (by decide +kernel) nonzero)

/-- The same original root owner supplies the exact defining equation consumed by inverse interpretation. -/
private def inverseFromSidecar (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator)
    (parameter_eq : sidecar.parameter = 2) (value : Pair Rational (-2)) (nonzero : value ≠ 0) :
    NamedEquivalent (CoherentNamed.mul
      (Pair.Gaussian.denote Cast.CoordinateTaylor.ofCoordinate generator value)
      (Pair.Gaussian.denote Cast.CoordinateTaylor.ofCoordinate generator value.inverse)).name
      (Coherence.exact 1).name := by
  have identity := PowerIdentity.ofSquare sidecar.square
  rewrite [parameter_eq] at identity
  exact inverseComparison generator identity value nonzero

example (sheet : Fin 2) (value : Pair Rational (-2)) (nonzero : value ≠ 0) :
    let retained := SquareRootSidecar.isolated 2 sheet
    NamedEquivalent (CoherentNamed.mul
      (Pair.Gaussian.denote Cast.CoordinateTaylor.ofCoordinate retained.1 value)
      (Pair.Gaussian.denote Cast.CoordinateTaylor.ofCoordinate retained.1 value.inverse)).name
      (Coherence.exact 1).name :=
  let retained := SquareRootSidecar.isolated 2 sheet
  inverseFromSidecar retained.1 retained.2 (SquareRootSidecar.isolated_parameter 2 sheet) value nonzero

end TestPurelib.Algebra.QuadraticPairNormGaussian
