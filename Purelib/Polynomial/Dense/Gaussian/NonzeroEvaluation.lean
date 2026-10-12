module
public import Purelib.Polynomial.Dense.RootBound
import Purelib.Data.List.Nodup
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Bool.Decide

import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite root bounds over constructive Gaussian rationals

A nonzero dense polynomial cannot vanish at as many distinct displayed
Gaussian rationals as it has normalized coefficient slots.  Synthetic
division proves this directly.  The resulting bounded scan supplies one
explicit nonzero evaluation without forming or quantifying over a root set.
-/

namespace Purelib.Polynomial.Dense.Gaussian

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical re)
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian.Basic
open Purelib.Data.List
open Purelib.Data.Bool

namespace NonzeroEvaluation

/-- Embed a natural number as a real-axis Gaussian rational. -/
@[expose] public def naturalPoint (n : Nat) : Canonical := (n : Canonical)

end NonzeroEvaluation

namespace NonzeroEvaluation

/-- Distinct natural numbers give distinct Gaussian probe points.

Their real-coordinate equality is the retained rational natural-cast equality.
Its direct injectivity identifies the original natural indices. -/
public theorem naturalPoint_injective : Function.Injective naturalPoint := open Purelib.Data.Rat in by
  intro left right equal
  have real := congrArg re equal
  change ((left : Canonical).re) = ((right : Canonical).re) at real
  rw [Cast.natCast_re,
    Cast.natCast_re] at real
  exact Fraction.Cast.Compatibility.natCast_injective_direct real

end NonzeroEvaluation

namespace NonzeroEvaluation

/-- The descending Gaussian natural-number probes below the polynomial coefficient count.

The finite list contains exactly that many candidates and is constructed by primitive recursion. -/
@[expose] public def candidates (p : Basic.CanonicalCoefficients.CoefficientPolynomial) : List Canonical :=
  (@Nat.rec (fun _ : Nat => List Nat) [] (fun count previous => count :: previous)
    p.degreeCount).map naturalPoint

end NonzeroEvaluation

namespace NonzeroEvaluation

/-- The coefficient-count candidate list contains no repeated points.

Each descending natural index is strictly greater than all indices in its
retained tail. Injective real-axis casting preserves those distinct indices. -/
public theorem candidates_nodup (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
    (candidates p).Nodup := by
  have memberBound : ∀ count value : Nat,
      value ∈ @Nat.rec (fun _ : Nat => List Nat) [] (fun index previous => index :: previous) count →
        value < count := by
    intro count
    induction count with
    | zero =>
        intro value member
        cases member
    | succ count inductionHypothesis =>
        intro value member
        change value ∈ count ::
          @Nat.rec (fun _ : Nat => List Nat) [] (fun index previous => index :: previous) count
          at member
        rcases Membership.mem_cons.mp member with equal | tailMember
        · cases equal
          exact Nat.lt_succ_self count
        · exact (inductionHypothesis value tailMember).trans (Nat.lt_succ_self count)
  have descendingNodup : ∀ count : Nat,
      (@Nat.rec (fun _ : Nat => List Nat) [] (fun index previous => index :: previous) count).Nodup := by
    intro count
    induction count with
    | zero => exact List.Pairwise.nil
    | succ count inductionHypothesis =>
        change (count ::
          @Nat.rec (fun _ : Nat => List Nat) [] (fun index previous => index :: previous) count).Nodup
        apply List.Pairwise.cons
        · intro value member equal
          subst value
          exact (Nat.lt_irrefl count (memberBound count count member)).elim
        · exact inductionHypothesis
  unfold candidates
  exact Data.List.Nodup.nodup_map_of_injective naturalPoint_injective
    (descendingNodup p.degreeCount)

end NonzeroEvaluation

namespace NonzeroEvaluation

/-- The candidate-list length equals the polynomial normalized coefficient count.

The original natural recursion contributes one probe at each successor.
Mapping the same list to Gaussian points preserves that exact finite length. -/
public theorem candidates_length (p : Basic.CanonicalCoefficients.CoefficientPolynomial) :
    (candidates p).length = p.degreeCount := by
  have descendingLength : ∀ count : Nat,
      (@Nat.rec (fun _ : Nat => List Nat) [] (fun index previous => index :: previous) count).length = count := by
    intro count
    induction count with
    | zero => rfl
    | succ count inductionHypothesis =>
        change (count ::
          @Nat.rec (fun _ : Nat => List Nat) [] (fun index previous => index :: previous) count).length =
            count + 1
        exact congrArg Nat.succ inductionHypothesis
  unfold candidates
  rewrite [Map.length_map]
  exact descendingLength p.degreeCount

end NonzeroEvaluation

namespace NonzeroEvaluation

/-- Candidate evaluations certify a zero finite coefficient difference.

The original difference determines the descending finite candidate list.
If it were nonzero, its root-count bound would exclude vanishing at every
displayed candidate. -/
public theorem difference_isZero_of_candidate_evals
    (p q : Basic.CanonicalCoefficients.CoefficientPolynomial)
    (equal : ∀ point ∈ candidates (p - q), p.eval point = q.eval point) :
    (p - q).isZero = true := by
  by_cases zero : (p - q).isZero = true
  · exact zero
  · have nonzero : (p - q).isZero = false := Decide.bool_eq_false_of_not_eq_true _ zero
    have candidateZeros : ∀ point ∈ candidates (p - q),
        (p - q).eval point = 0 := by
      intro point member
      rw [Basic.DensePolynomial.eval_sub, equal point member]
      exact sub_self _
    have tooMany := RootBound.Roots.nodup_zeros_length_lt_degreeCount (p - q) nonzero
      (candidates (p - q)) (candidates_nodup (p - q)) candidateZeros
    rw [candidates_length] at tooMany
    exact (Nat.lt_irrefl _ tooMany).elim

end NonzeroEvaluation

namespace NonzeroEvaluation

/-- Return the first displayed Gaussian candidate where the polynomial value is nonzero.

Return none if every candidate in the finite input list is a root. -/
@[expose] public def firstNonzero (p : Basic.CanonicalCoefficients.CoefficientPolynomial) : List Canonical → Option
  Canonical
  | [] => none
  | point :: remaining =>
      if p.eval point = 0 then Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation.firstNonzero p remaining else some
        point

end NonzeroEvaluation

namespace NonzeroEvaluation

/-- An unsuccessful candidate scan implies zero evaluation at every point in its input list.

The original zero-test branch advances to the retained tail. A nonzero head
would have returned a point, so a none result excludes that branch. -/
public theorem firstNonzero_none_zeros
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) : ∀ {points : List Canonical},
    firstNonzero p points = none → ∀ point ∈ points, p.eval point = 0
  | [], _, _, member => by cases member
  | head :: tail, outcome, point, member => by
      rw [firstNonzero] at outcome
      split at outcome
      · rename_i headZero
        rcases Membership.mem_cons.mp member with rfl | tailMember
        · exact headZero
        · exact Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation.firstNonzero_none_zeros p outcome point tailMember
      · cases outcome

end NonzeroEvaluation

namespace NonzeroEvaluation

/-- A successful scan returns a listed point with nonzero polynomial value.

A tail result retains its original membership witness. A head result
identifies the selected point and keeps the same negative zero-test witness. -/
public theorem firstNonzero_some_spec
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) : ∀ {points : List Canonical} {point : Canonical},
    firstNonzero p points = some point →
      point ∈ points ∧ p.eval point ≠ 0
  | [], _, outcome => by cases outcome
  | head :: tail, point, outcome => by
      rw [firstNonzero] at outcome
      split at outcome
      · rename_i headZero
        have recursive := Purelib.Polynomial.Dense.Gaussian.NonzeroEvaluation.firstNonzero_some_spec p outcome
        exact ⟨List.Mem.tail head recursive.1, recursive.2⟩
      · rename_i headNonzero
        have pointEq : point = head := Option.some.inj outcome.symm
        subst point
        exact ⟨List.Mem.head tail, headNonzero⟩

end NonzeroEvaluation

set_option genInjectivity false in
/-- One retained Gaussian point at which the original polynomial is nonzero.

The value witness refers to the original polynomial at that same displayed
point; it does not replace the polynomial by a normalized copy. -/
public structure NonzeroEvaluation (p : Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The retained Gaussian evaluation point. -/ point : Canonical
  /-- The original polynomial has nonzero value at the retained point. -/ valueNonzero : p.eval point ≠ 0

constructive_injectivity NonzeroEvaluation

namespace NonzeroEvaluation.mk

end NonzeroEvaluation.mk

namespace NonzeroEvaluation.mk

end NonzeroEvaluation.mk

namespace NonzeroEvaluation

/-- Bounded coefficient-count search for one displayed nonzero evaluation.

The scan consumes the original descending candidate list and retains its first
nonzero point. Exhausting that list contradicts the finite root-count bound. -/
@[expose] public def findNonzeroEvaluation
    (p : Basic.CanonicalCoefficients.CoefficientPolynomial) (nonzero : p.isZero = false) :
    NonzeroEvaluation p := by
  let points := candidates p
  match outcome : firstNonzero p points with
  | some point =>
      exact ⟨point, (firstNonzero_some_spec p outcome).2⟩
  | none =>
      have zeros := firstNonzero_none_zeros p outcome
      have tooMany := RootBound.Roots.nodup_zeros_length_lt_degreeCount p nonzero points
        (candidates_nodup p) zeros
      have exactLength := candidates_length p
      rw [exactLength] at tooMany
      exact (Nat.lt_irrefl _ tooMany).elim

end NonzeroEvaluation

end Purelib.Polynomial.Dense.Gaussian
