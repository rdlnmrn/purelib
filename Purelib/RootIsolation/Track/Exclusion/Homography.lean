module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Homography.Basic
public import Purelib.Geometry.Projective.Homography.Pole
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Outside
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Exclusion.Point
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.LinearAlgebra.Coordinates2.Matrix (GaussianMatrix)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.State.WindingOne.Basic (WindingOneState)

public section

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Finite separation from a CCL decoder pole

The inverse tail represented by a raw CCL prefix uses the affine denominator
`c * z + d` of the prefix matrix.  If `c` is nonzero, its only rational pole
is the displayed point `-d / c`.  Exact evaluation either returns that point
as a polynomial root or one winding-track refinement excludes it.  A concrete
outside side of the resulting rational box then supplies a positive lower
bound for the denominator norm throughout that box and every later subbox.

This is finite data: four rational comparisons, one exact polynomial
evaluation, and at most one call to the already-total winding refinement.
-/

namespace Purelib.RootIsolation.Track.Exclusion.Homography

set_option genInjectivity false in
/-- A refined winding state carrying a uniform positive lower bound for one
decoder denominator. -/
structure SeparationOutput
    (p : CoefficientPolynomial) (ambient : Box)
    (current : WindingOneState p ambient) (matrix :
      GaussianMatrix) where
  /-- The retained refined winding-one state with a separated decoder denominator. -/ state :
    WindingOneState p ambient
  /-- The returned state box refines the original current box. -/ refines : state.box.Refines current.box
  /-- The retained uniform rational lower bound for the squared decoder denominator. -/ margin : Fraction.Rational
  /-- The retained denominator margin is strictly positive. -/ margin_pos : 0 < margin
  /-- The retained positive margin bounds the decoder denominator at every point of the returned box. -/ lower : ∀
    {value : Gaussian.Basic.Canonical}, state.box.Contains value →
    margin ≤ Data.Gaussian.Norm.Basic.normSq (Geometry.Projective.Homography.Basic.denominator matrix value)

constructive_injectivity SeparationOutput

namespace SeparationOutput

/-- Restrict a denominator certificate to any later explicit subbox. -/
@[expose] def restrict
    {p : CoefficientPolynomial} {ambient : Box}
    {current : WindingOneState p ambient} {matrix :
      GaussianMatrix}
    (output : Track.Exclusion.Homography.SeparationOutput p ambient current matrix)
    (later : WindingOneState p ambient)
    (laterRefines : later.box.Refines output.state.box) :
    Track.Exclusion.Homography.SeparationOutput p ambient current matrix where
  state := later
  refines := laterRefines.trans output.refines
  margin := output.margin
  margin_pos := output.margin_pos
  lower := fun inside => output.lower (laterRefines.contains inside)

end SeparationOutput

/-- A constant nonzero lower row already has a uniform denominator margin. -/
@[expose] def separateConstant
    {p : CoefficientPolynomial} {ambient : Box}
    (current : WindingOneState p ambient) (matrix :
      GaussianMatrix)
    (lowerLeftZero : matrix.c = 0) (lowerRightNonzero : matrix.d ≠ 0) :
    SeparationOutput p ambient current matrix where
  state := current
  refines := Box.refines_refl current.box
  margin := Data.Gaussian.Norm.Basic.normSq matrix.d
  margin_pos := Gaussian.Norm.Basic.normSq_pos lowerRightNonzero
  lower := by
    intro value _inside
    simp only [Geometry.Projective.Homography.Basic.denominator, lowerLeftZero,
      Gaussian.Basic.zero_mul,
      Gaussian.Basic.zero_add, -eq_self, -iff_self]
    exact le_rfl

/-- An already-excluded pole yields an immediate positive denominator
margin, whether or not that pole is a different polynomial root. -/
@[expose] def separateOutside
    {p : CoefficientPolynomial} {ambient : Box}
    (current : WindingOneState p ambient) (matrix :
      GaussianMatrix)
    (lowerLeftNonzero : matrix.c ≠ 0)
    (outside : ¬current.box.Contains (Geometry.Projective.Homography.decoderPole matrix)) :
    SeparationOutput p ambient current matrix := by
  let side := Box.outsideSide outside
  refine
    { state := current
      refines := Box.refines_refl current.box
      margin := Data.Gaussian.Norm.Basic.normSq matrix.c * side.margin
      margin_pos := Fraction.Order.Arithmetic.mul_pos_direct
        (Gaussian.Norm.Basic.normSq_pos lowerLeftNonzero) side.margin_pos
      lower := ?_ }
  intro value inside
  have distance := side.margin_le_normSq_sub inside
  rw [Geometry.Projective.Homography.denominator_eq_mul_sub_pole matrix lowerLeftNonzero value,
    Gaussian.Norm.Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distance
    (Gaussian.Norm.Basic.normSq_nonneg matrix.c)

/-- One winding refinement excludes a nonroot pole and therefore supplies a
positive uniform denominator margin. -/
@[expose] def separateNonroot
    {p : CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Track.Basic.WindingOneTrack p ambient)
    (current : WindingOneState p ambient) (matrix :
      GaussianMatrix)
    (lowerLeftNonzero : matrix.c ≠ 0)
    (nonroot : p.eval (Geometry.Projective.Homography.decoderPole matrix) ≠ 0) :
    SeparationOutput p ambient current matrix := by
  let state := Track.Exclusion.Point.refinePastPoint
    track current (Geometry.Projective.Homography.decoderPole matrix) nonroot
  have refines :=
    Track.Exclusion.Point.refinePastPoint_refines
      track current (Geometry.Projective.Homography.decoderPole matrix) nonroot
  have outside :=
    Track.Exclusion.Point.refinePastPoint_excludes
      degreePositive track current (Geometry.Projective.Homography.decoderPole matrix) nonroot
  let side := Box.outsideSide outside
  refine
    { state := state
      refines := refines
      margin := Data.Gaussian.Norm.Basic.normSq matrix.c * side.margin
      margin_pos := Fraction.Order.Arithmetic.mul_pos_direct
        (Gaussian.Norm.Basic.normSq_pos lowerLeftNonzero) side.margin_pos
      lower := ?_ }
  intro value inside
  have distance := side.margin_le_normSq_sub inside
  rw [Geometry.Projective.Homography.denominator_eq_mul_sub_pole matrix lowerLeftNonzero value,
    Gaussian.Norm.Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct distance
    (Gaussian.Norm.Basic.normSq_nonneg matrix.c)

set_option genInjectivity false in
/-- Exact finite outcome: either the decoder pole is a displayed root in the
current box, or a refined state has a positive uniform denominator margin. -/
inductive Decision
    (p : CoefficientPolynomial) (ambient : Box)
    (current : WindingOneState p ambient) (matrix :
      GaussianMatrix) where
  /-- An exact polynomial root in the original box at which the decoder denominator vanishes. -/ | exact (point :
    Gaussian.Basic.Canonical) (root : p.eval point = 0)
      (inside : current.box.Contains point)
      (denominatorZero :
        Geometry.Projective.Homography.Basic.denominator matrix point = 0)
  /-- The retained refinement and its positive uniform decoder-denominator margin. -/ | separated (output :
    SeparationOutput p ambient current matrix)

constructive_injectivity Decision

/-- Decide the pole case using only the displayed lower-row nonzeroness and
one exact polynomial evaluation. -/
@[expose] def decide
    {p : CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Track.Basic.WindingOneTrack p ambient)
    (current : WindingOneState p ambient) (matrix :
      GaussianMatrix)
    (lowerRowNonzero : matrix.c ≠ 0 ∨ matrix.d ≠ 0) :
    Decision p ambient current matrix := by
  by_cases lowerLeftZero : matrix.c = 0
  · have lowerRightNonzero : matrix.d ≠ 0 :=
      lowerRowNonzero.resolve_left (fun nonzero => nonzero lowerLeftZero)
    exact .separated
      (separateConstant current matrix lowerLeftZero lowerRightNonzero)
  · by_cases root : p.eval (Geometry.Projective.Homography.decoderPole matrix) = 0
    · by_cases inside : current.box.Contains (Geometry.Projective.Homography.decoderPole matrix)
      · exact .exact (Geometry.Projective.Homography.decoderPole matrix) root inside
          (Geometry.Projective.Homography.denominator_at_decoderPole matrix lowerLeftZero)
      · exact .separated
          (separateOutside current matrix lowerLeftZero inside)
    · exact .separated
        (separateNonroot degreePositive track current matrix lowerLeftZero root)

end Purelib.RootIsolation.Track.Exclusion.Homography

end
