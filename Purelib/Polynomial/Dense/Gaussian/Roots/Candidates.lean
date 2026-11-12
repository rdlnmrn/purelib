module

public import Purelib.Polynomial.Elimination.Axis.Certificate
public import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
import Purelib.Polynomial.Dense.Rational.RootCandidates
import Purelib.Data.List.FilterMap
import Purelib.Data.List.Flatten
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic

/-!
# Exact Gaussian-rational roots from retained coordinate eliminants

The supplied original axis certificate retains two nonzero rational
coordinate polynomials. Their finite rational root lists provide the two
coordinate banks. Exact evaluation filters their ordered product into the
existing Gaussian root certificates without rebuilding either eliminant.
The list is complete for displayed Gaussian-rational roots; it does not
represent nonrational roots or assign source multiplicities.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Roots.Candidates

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Dense.Gaussian.Roots.Certificate (ExactRoot)
open Purelib.Polynomial.Dense.Rational

/-- Check one displayed coordinate pair against the same original Gaussian polynomial. -/
private def promote (p : CoefficientPolynomial) (point : Canonical) : Option (ExactRoot p) :=
  if root : p.eval point = 0 then some ⟨point, root⟩ else none

/-- A supplied original exact root survives its same point's evaluation check. -/
private theorem promote_root {p : CoefficientPolynomial} (root : ExactRoot p) :
    promote p root.point = some root := by
  cases root with
  | mk point equation =>
      unfold promote
      rewrite [dif_pos equation]
      rfl

/-- Enumerate every exact Gaussian-rational root from the actual retained coordinate eliminants.

Both rational coordinate lists are computed once before the ordered product
is traversed. Each surviving point retains its original exact evaluation
certificate; failed coordinate pairs are discarded and successful repeated
occurrences remain in their original order. No root isolation is performed.
-/
public def exactRoots {p : CoefficientPolynomial} {degreeBound : Nat}
    (certificate : AxisEliminationCertificate p degreeBound) : List (ExactRoot p) :=
  let reals := RootCandidates.candidates certificate.vertical
  let imaginaries := RootCandidates.candidates certificate.horizontal
  reals.flatMap fun real => imaginaries.filterMap fun imaginary => promote p ⟨real, imaginary⟩

/-- The product of the two actual endpoint-divisor search bounds bounds all inspected coordinate pairs. -/
public def searchSize {p : CoefficientPolynomial} {degreeBound : Nat}
    (certificate : AxisEliminationCertificate p degreeBound) : Nat :=
  RootCandidates.divisorCandidateSearchSize certificate.vertical *
    RootCandidates.divisorCandidateSearchSize certificate.horizontal

/-- Every exact Gaussian-rational root occurs in the computed list of original exact root certificates.

The original axis-certificate identities put both coordinates in their
respective complete rational candidate banks. The actual Gaussian evaluation
check then returns that same point with its root certificate.
-/
public theorem root_mem_exactRoots {p : CoefficientPolynomial} {degreeBound : Nat}
    (certificate : AxisEliminationCertificate p degreeBound) (root : ExactRoot p) :
    root ∈ exactRoots certificate := by
  unfold exactRoots
  apply Flatten.mem_flatMap.mpr
  refine ⟨root.point.re,
    RootCandidates.root_mem_candidates certificate.vertical certificate.vertical_nonzero root.point.re
      (certificate.vertical_eval_eq_zero_of_root root.point root.root), ?_⟩
  apply FilterMap.mem_filterMap.mpr
  refine ⟨root.point.im,
    RootCandidates.root_mem_candidates certificate.horizontal certificate.horizontal_nonzero root.point.im
      (certificate.horizontal_eval_eq_zero_of_root root.point root.root), ?_⟩
  have pointEq : (⟨root.point.re, root.point.im⟩ : Canonical) = root.point := by
    cases root.point
    rfl
  rewrite [pointEq]
  exact promote_root root

/-- Exact evaluation filtering cannot exceed the retained finite coordinate-search budget.

The ordered product has at most the product of its two rational candidate
lengths. Their original endpoint-divisor bounds retain the two actual
coordinate polynomials as separate factors of this same budget.
-/
public theorem exactRoots_length_le {p : CoefficientPolynomial} {degreeBound : Nat}
    (certificate : AxisEliminationCertificate p degreeBound) :
    (exactRoots certificate).length ≤ searchSize certificate := by
  have filtered := Flatten.length_flatMap_filterMap_le
    (RootCandidates.candidates certificate.horizontal)
    (fun real imaginary => promote p ⟨real, imaginary⟩)
    (RootCandidates.candidates certificate.vertical)
  exact filtered.trans (Nat.mul_le_mul
    (RootCandidates.candidates_length_le certificate.vertical)
    (RootCandidates.candidates_length_le certificate.horizontal))

end Purelib.Polynomial.Dense.Gaussian.Roots.Candidates
