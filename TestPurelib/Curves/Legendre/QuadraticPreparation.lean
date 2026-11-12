module

import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Quadratic
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Provenance
import Purelib.Algebra.Quadratic.Pair.Gaussian.Realization.Rational
import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Purelib.Curves.Legendre.GuaranteedFold
import Purelib.Curves.Legendre.FractionalWords.Periods
import Purelib.Topology.Knot.Braid.Word.Basic

/-!
# Finite preparation for real irrational quadratic word inputs

Either original sheet of the square root of two supplies preparation for
every invertible integer matrix and every finite dual braid word. The
construction takes no imaginary gap or caller-supplied denominator bound.
-/

namespace TestPurelib.Curves.Legendre.QuadraticPreparation

open Purelib.Algebra.Quadratic.Pair.Gaussian (Realization)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Power (PowerIdentity)
open Purelib.Approximation.Gaussian.FractionalAction.Integral
open Purelib.Data.Rat.Fraction
open Purelib.Data.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.LinearAlgebra.Matrix.Basic (IntegralMatrix)
open Purelib.LinearAlgebra.Matrix.Inverse
open Purelib.Curves.Legendre
open Purelib.Topology.Knot

/-- Realize the actual supplied generator using the single retained finite square inspection. -/
private def realized (generator : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2)) : Realization Rational :=
  Realization.rational 2 generator identity (Square.inspect 2) (by decide +kernel)

/-- Read the exact scalar map of this same original rational realization. -/
private theorem coefficients (generator : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2)) (value : Rational) :
    (realized generator identity).coefficient value = Cast.CoordinateTaylor.ofCoordinate value := rfl

/-- The actual generator sidecar has nonzero nominal generator coordinate. -/
private theorem irrational (generator : CoherentNamed)
    (identity : PowerIdentity generator 2 (Cast.CoordinateTaylor.ofCoordinate 2)) :
    (Realization.Sidecar.generator (realized generator identity)).value.im ≠ 0 := by
  rewrite [Realization.Sidecar.generator_value]
  change (1 : Rational) ≠ 0
  decide +kernel

example (sheet : Fin 2) :
    let retained := SquareRootSidecar.isolated (Cast.CoordinateTaylor.ofCoordinate 2) sheet
    (Preparation.Provenance.rootProvider retained.2).isSome = true :=
  let retained := SquareRootSidecar.isolated (Cast.CoordinateTaylor.ofCoordinate 2) sheet
  Preparation.Provenance.rootProvider_admitted retained.2 2
    (SquareRootSidecar.isolated_parameter (Cast.CoordinateTaylor.ofCoordinate 2) sheet)
    (by decide +kernel) (by decide +kernel)

example (sheet : Fin 2) (matrix : IntegralMatrix) (inverse : Right.RightInverse matrix) :
    let retained := SquareRootSidecar.isolated (Cast.CoordinateTaylor.ofCoordinate 2) sheet
    let identity := SquareRootSidecar.isolated_parameter (Cast.CoordinateTaylor.ofCoordinate 2) sheet ▸
      PowerIdentity.ofSquare retained.2.square
    let input := Realization.Sidecar.generator (realized retained.1 identity)
    Preparation.Quadratic.MatrixPreparation input matrix inverse :=
  let retained := SquareRootSidecar.isolated (Cast.CoordinateTaylor.ofCoordinate 2) sheet
  let identity := SquareRootSidecar.isolated_parameter (Cast.CoordinateTaylor.ofCoordinate 2) sheet ▸
    PowerIdentity.ofSquare retained.2.square
  let input := Realization.Sidecar.generator (realized retained.1 identity)
  Preparation.Quadratic.prepare input (coefficients retained.1 identity) (irrational retained.1 identity) matrix inverse

example (sheet : Fin 2) (word : Braid.Word 3) :
    let retained := SquareRootSidecar.isolated (Cast.CoordinateTaylor.ofCoordinate 2) sheet
    GuaranteedFold.Prepared retained.1 (FractionalWords.Periods.periodBraidMatrices word) :=
  let retained := SquareRootSidecar.isolated (Cast.CoordinateTaylor.ofCoordinate 2) sheet
  let identity := SquareRootSidecar.isolated_parameter (Cast.CoordinateTaylor.ofCoordinate 2) sheet ▸
    PowerIdentity.ofSquare retained.2.square
  let input := Realization.Sidecar.generator (realized retained.1 identity)
  GuaranteedFold.prepare retained.1
    (Preparation.Quadratic.provider input (coefficients retained.1 identity) (irrational retained.1 identity))
    (FractionalWords.Periods.periodBraidMatrices word) (GuaranteedFold.periodInverses word)

end TestPurelib.Curves.Legendre.QuadraticPreparation
