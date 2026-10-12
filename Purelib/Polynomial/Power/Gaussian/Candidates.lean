module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Power.Gaussian.ExactRoot
public import Purelib.Algebra.Power.Gaussian.ExactRoot.Check
import Purelib.Data.Gaussian.Constants
public import Purelib.Data.List.Deduplicate
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Rational.Power
public import Purelib.Polynomial.Dense.Rational.RootCandidates
public import Purelib.Polynomial.Elimination.Gaussian.PowerCoordinates

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Polynomial.Dense.Basic

open Purelib.Algebra.Power.Gaussian (ExactRoot)

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

namespace Purelib.Polynomial.Power.Gaussian.Candidates

/-- The first sparse equation is `S^q-N(input)`. -/
def radiusPolynomial (input : Gaussian.Basic.Canonical) (degree :
  Data.Nat.Positive.RootDegree) :
    (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Rational.Power.powerPolynomial
    (Data.Gaussian.Norm.Basic.normSq input) degree.value

/-- Every rational candidate for the squared norm, derived from the two
nonzero endpoint coefficients of the sparse norm equation. -/
def radiusCandidates (input : Gaussian.Basic.Canonical) (degree :
  Data.Nat.Positive.RootDegree) :
    List Fraction.Rational :=
  Dense.Rational.RootCandidates.candidates
    (radiusPolynomial input degree)

/-- The real-coordinate Lucas equation at one displayed radius. -/
def realCoordinatePolynomial (input : Gaussian.Basic.Canonical)
  (degree : Data.Nat.Positive.RootDegree)
    (radius : Fraction.Rational) : (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Elimination.Gaussian.PowerCoordinates.coordinatePolynomial radius input.re
    degree.value

/-- The imaginary-coordinate equation is the same recurrence after the fixed
quarter turn `-i`, which exposes the imaginary coordinate as a real one. -/
def imaginaryCoordinatePolynomial (input : Gaussian.Basic.Canonical)
  (degree : Data.Nat.Positive.RootDegree)
    (radius : Fraction.Rational) : (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Elimination.Gaussian.PowerCoordinates.coordinatePolynomial radius
    ((Gaussian.Constants.negativeImaginaryUnit ^
      degree.value * input).re) degree.value

/-- The sparse norm equation retains exactly degree plus one coefficients. -/
theorem radiusPolynomial_coefficients_length (input :
  Gaussian.Basic.Canonical)
    (degree : Data.Nat.Positive.RootDegree) :
    (radiusPolynomial input degree).coeffs.length = degree.value + 1 :=
  Dense.Rational.Power.powerPolynomial_coefficients_length
    (Data.Gaussian.Norm.Basic.normSq input) degree.value degree.positive

/-- The real-coordinate Lucas equation retains exactly degree plus one coefficients. -/
theorem realCoordinatePolynomial_coefficients_length (input :
  Gaussian.Basic.Canonical)
    (degree : Data.Nat.Positive.RootDegree) (radius : Fraction.Rational) :
    (realCoordinatePolynomial input degree radius).coeffs.length =
      degree.value + 1 :=
  Elimination.Gaussian.PowerCoordinates.coordinatePolynomial_coefficients_length
    radius input.re degree.value degree.positive

/-- The quarter-turned imaginary-coordinate equation retains exactly degree plus one coefficients. -/
theorem imaginaryCoordinatePolynomial_coefficients_length (input :
  Gaussian.Basic.Canonical)
    (degree : Data.Nat.Positive.RootDegree) (radius : Fraction.Rational) :
    (imaginaryCoordinatePolynomial input degree radius).coeffs.length =
      degree.value + 1 :=
  Elimination.Gaussian.PowerCoordinates.coordinatePolynomial_coefficients_length
    radius
      ((Gaussian.Constants.negativeImaginaryUnit ^
        degree.value * input).re) degree.value degree.positive

/-- Enumerate rational candidates from the finite real-coordinate equation at the retained radius. -/
def realCoordinateCandidates (input : Gaussian.Basic.Canonical)
  (degree : Data.Nat.Positive.RootDegree)
    (radius : Fraction.Rational) : List Fraction.Rational :=
  Dense.Rational.RootCandidates.candidates
    (realCoordinatePolynomial input degree radius)

/-- Enumerate rational candidates from the finite imaginary-coordinate equation at the retained radius. -/
def imaginaryCoordinateCandidates (input : Gaussian.Basic.Canonical)
  (degree : Data.Nat.Positive.RootDegree)
    (radius : Fraction.Rational) : List Fraction.Rational :=
  Dense.Rational.RootCandidates.candidates
    (imaginaryCoordinatePolynomial input degree radius)

/-- Cartesian coordinate candidates at one already-derived rational radius. -/
def candidatesAtRadius (input : Gaussian.Basic.Canonical) (degree :
  Data.Nat.Positive.RootDegree)
    (radius : Fraction.Rational) : List Gaussian.Basic.Canonical :=
  (realCoordinateCandidates input degree radius).flatMap fun real =>
    (imaginaryCoordinateCandidates input degree radius).map fun imaginary =>
      ({ re := real, im := imaginary } : Gaussian.Basic.Canonical)

/-- The finite union of the coordinate products over all derived radii before
duplicate removal. -/
def rawDerivedCandidates (input : Gaussian.Basic.Canonical) (degree
  : Data.Nat.Positive.RootDegree) :
    List Gaussian.Basic.Canonical :=
  (radiusCandidates input degree).flatMap
    (candidatesAtRadius input degree)

/-- The sparse candidate union with duplicates removed before exact power
filtering. -/
def derivedCandidates (input : Gaussian.Basic.Canonical) (degree :
  Data.Nat.Positive.RootDegree) :
    List Gaussian.Basic.Canonical :=
  Data.List.Deduplicate.deduplicateCandidates (rawDerivedCandidates input degree)

/-- Every displayed exact Gaussian-rational root occurs in the automatically
derived finite list.  The proof first selects its rational squared norm and
then its two Lucas-coordinate roots; no Sylvester eliminant is constructed. -/
theorem exactRoot_mem_derivedCandidates
    {input : Gaussian.Basic.Canonical} {degree : Data.Nat.Positive.RootDegree}
    (root : ExactRoot input degree) :
    root.point ∈ derivedCandidates input degree := by
  have radiusRoot :
      (radiusPolynomial input degree).eval (Data.Gaussian.Norm.Basic.normSq root.point) =
        0 :=
    Elimination.Gaussian.PowerCoordinates.powerPolynomial_norm_root
      degree.positive root.power_eq
  have radiusMember :
      Data.Gaussian.Norm.Basic.normSq root.point ∈ radiusCandidates input degree :=
    Dense.Rational.RootCandidates.root_mem_candidates
      (radiusPolynomial input degree)
      (Dense.Rational.Power.powerPolynomial_nonzero
        (Data.Gaussian.Norm.Basic.normSq input) degree.value degree.positive)
      (Data.Gaussian.Norm.Basic.normSq root.point) radiusRoot
  have realRoot :
      (realCoordinatePolynomial input degree (Data.Gaussian.Norm.Basic.normSq
        root.point)).eval
        root.point.re = 0 :=
    Elimination.Gaussian.PowerCoordinates.coordinatePolynomial_real_root
      degree.positive root.power_eq
  have imaginaryRoot :
      (imaginaryCoordinatePolynomial input degree (Data.Gaussian.Norm.Basic.normSq
        root.point)).eval
        root.point.im = 0 :=
    Elimination.Gaussian.PowerCoordinates.coordinatePolynomial_imaginary_root
      degree.positive root.power_eq
  have realMember :=
    Dense.Rational.RootCandidates.root_mem_candidates
      (realCoordinatePolynomial input degree (Data.Gaussian.Norm.Basic.normSq root.point))
      (Elimination.Gaussian.PowerCoordinates.coordinatePolynomial_nonzero
        (Data.Gaussian.Norm.Basic.normSq root.point) input.re degree.value degree.positive)
      root.point.re realRoot
  have imaginaryMember :=
    Dense.Rational.RootCandidates.root_mem_candidates
      (imaginaryCoordinatePolynomial input degree (Data.Gaussian.Norm.Basic.normSq
        root.point))
      (Elimination.Gaussian.PowerCoordinates.coordinatePolynomial_nonzero
        (Data.Gaussian.Norm.Basic.normSq root.point)
        ((Gaussian.Constants.negativeImaginaryUnit ^
          degree.value * input).re) degree.value degree.positive)
      root.point.im imaginaryRoot
  change root.point ∈ Data.List.Deduplicate.deduplicateCandidates
    (rawDerivedCandidates input degree)
  apply (Data.List.Deduplicate.mem_deduplicateCandidates root.point
    (rawDerivedCandidates input degree)).mpr
  change root.point ∈ (radiusCandidates input degree).flatMap
    (candidatesAtRadius input degree)
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨Data.Gaussian.Norm.Basic.normSq root.point, radiusMember, ?_⟩
  rw [candidatesAtRadius]
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨root.point.re, realMember, ?_⟩
  exact Data.List.Map.mem_map.mpr ⟨root.point.im, imaginaryMember, by
    cases root.point
    rfl⟩

/-- Automatically derive the complete finite sparse candidate family and
promote precisely the successful `q`th powers. -/
def automaticExactRoots (input : Gaussian.Basic.Canonical) (degree :
  Data.Nat.Positive.RootDegree) :
    List (ExactRoot input degree) :=
  ExactRoot.Check.promoteCandidates input degree (derivedCandidates
    input degree)

/-- Every displayed exact Gaussian root appears among the points of the automatically checked finite root family. -/
theorem exactRoot_mem_automaticExactRoots
    {input : Gaussian.Basic.Canonical} {degree : Data.Nat.Positive.RootDegree}
    (root : ExactRoot input degree) :
    root.point ∈
      (automaticExactRoots input degree).map ExactRoot.point
        := by
  unfold automaticExactRoots
  exact ExactRoot.Check.mem_promoteCandidates_of_mem input degree root.point root.power_eq
    (derivedCandidates input degree)
      (exactRoot_mem_derivedCandidates root)
end Purelib.Polynomial.Power.Gaussian.Candidates

end
