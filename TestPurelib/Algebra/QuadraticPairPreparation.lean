module

import Purelib.Algebra.Quadratic.Pair.Gaussian.Preparation
import Purelib.Algebra.Quadratic.Pair.Norm.Rational
import Purelib.Data.Gaussian.Cast
import Purelib.Riemann.RootContinuation.SquareRootSidecar

/-!
# Finite preparation and actual reciprocals on either supplied root sheet

The finite square exclusion for two certifies a nonzero norm for every nonzero
original pair. Norm factorization computes the original interpreted channel's
apart preparation, and its actual prepared division agrees with the original
interpreted inverse on either retained isolated sheet.
-/

namespace TestPurelib.Algebra.QuadraticPairPreparation

open Purelib.Algebra.Quadratic (Pair)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.Division
open Purelib.Riemann.RootContinuation

/-- Retain the sign convention of the original parameter-minus-two pair. -/
private theorem sign : -Cast.CoordinateTaylor.ofCoordinate (-2 : Rational) = (2 : Basic.Canonical) := by
  decide +kernel

/-- The original retained degree-two equation has the coefficient-map parameter convention. -/
private def mappedIdentity (generator : CoherentNamed) (identity : PowerIdentity generator 2 2) :
    PowerIdentity generator 2 (-Cast.CoordinateTaylor.ofCoordinate (-2 : Rational)) := by
  rewrite [sign]
  exact identity

/-- Exact real-axis embedding preserves the nonzero original pair norm. -/
private theorem mappedNorm_nonzero (value : Pair Rational (-2)) (nonzero : value ≠ 0) :
    Cast.CoordinateTaylor.ofCoordinate value.norm ≠ 0 := by
  intro zero
  have scalarZero : value.norm = 0 := congrArg Basic.re zero
  exact Pair.norm_ne_zero_of_inspection (Square.inspect 2) (by decide +kernel) nonzero scalarZero

/-- Compute and retain the actual two interpreted factor observations at the supplied original generator. -/
private def observation (generator : CoherentNamed) (identity : PowerIdentity generator 2 2)
    (value : Pair Rational (-2)) (nonzero : value ≠ 0) :
    Prepared.Factor.Observation (Pair.Gaussian.denote Cast.CoordinateTaylor.ofCoordinate generator value)
      (Pair.Gaussian.denote Cast.CoordinateTaylor.ofCoordinate generator value.conjugate)
      (Cast.CoordinateTaylor.ofCoordinate value.norm) :=
  Pair.Gaussian.observe_norm Cast.CoordinateTaylor.ofCoordinate Cast.ofCoordinate_zero
    Cast.ofCoordinate_add Cast.ofCoordinate_mul Cast.ofCoordinate_sub generator
    (mappedIdentity generator identity) value (mappedNorm_nonzero value nonzero)

/-- The computed finite norm preparation certifies agreement of the actual reciprocal with the original inverse. -/
private def reciprocalComparison (generator : CoherentNamed) (identity : PowerIdentity generator 2 2)
    (value : Pair Rational (-2)) (nonzero : value ≠ 0) :
    let retained := observation generator identity value nonzero
    NamedEquivalent (retained.prepare.quotient (Coherence.exact 1)).name
      (Pair.Gaussian.denote Cast.CoordinateTaylor.ofCoordinate generator value.inverse).name :=
  let retained := observation generator identity value nonzero
  Pair.Gaussian.reciprocal_equivalent Cast.CoordinateTaylor.ofCoordinate Cast.ofCoordinate_zero (by decide +kernel)
    Cast.ofCoordinate_add Cast.ofCoordinate_mul Cast.ofCoordinate_sub generator
    (mappedIdentity generator identity) value
    (Pair.norm_ne_zero_of_inspection (Square.inspect 2) (by decide +kernel) nonzero) retained.prepare

/-- The exact supplied root sidecar supplies the original equation used by finite reciprocal preparation. -/
private def fromSidecar (generator : CoherentNamed) (sidecar : SquareRootSidecar.Sidecar generator)
    (parameter_eq : sidecar.parameter = 2) (value : Pair Rational (-2)) (nonzero : value ≠ 0) :
    let identity : PowerIdentity generator 2 2 := parameter_eq ▸ PowerIdentity.ofSquare sidecar.square
    let retained := observation generator identity value nonzero
    NamedEquivalent (retained.prepare.quotient (Coherence.exact 1)).name
      (Pair.Gaussian.denote Cast.CoordinateTaylor.ofCoordinate generator value.inverse).name :=
  let identity : PowerIdentity generator 2 2 := parameter_eq ▸ PowerIdentity.ofSquare sidecar.square
  reciprocalComparison generator identity value nonzero

example (sheet : Fin 2) (value : Pair Rational (-2)) (nonzero : value ≠ 0) :
    let retained := SquareRootSidecar.isolated 2 sheet
    let identity : PowerIdentity retained.1 2 2 :=
      SquareRootSidecar.isolated_parameter 2 sheet ▸ PowerIdentity.ofSquare retained.2.square
    let prepared := observation retained.1 identity value nonzero
    NamedEquivalent (prepared.prepare.quotient (Coherence.exact 1)).name
      (Pair.Gaussian.denote Cast.CoordinateTaylor.ofCoordinate retained.1 value.inverse).name :=
  let retained := SquareRootSidecar.isolated 2 sheet
  fromSidecar retained.1 retained.2 (SquareRootSidecar.isolated_parameter 2 sheet) value nonzero

example (generator : CoherentNamed) (identity : PowerIdentity generator 2 2)
    (value : Pair Rational (-2)) (nonzero : value ≠ 0) :
    (observation generator identity value nonzero).first =
      Pair.Gaussian.denote Cast.CoordinateTaylor.ofCoordinate generator value :=
  (observation generator identity value nonzero).first_eq

end TestPurelib.Algebra.QuadraticPairPreparation
