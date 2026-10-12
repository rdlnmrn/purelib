module
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.Power.Gaussian.ExactRoot
import Purelib.Algebra.Power.Gaussian.ExactRoot.Check
import Purelib.Data.List.Map
import Purelib.Data.List.Membership

import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Degree
import Purelib.Polynomial.Dense.RootBound
import Purelib.Polynomial.Power.Gaussian
public import Purelib.Polynomial.Power.Gaussian.Candidates

import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Power.Gaussian.ExactRoot

open Purelib.Data.Gaussian.Basic

open Purelib

open Purelib.Data.Nat.Positive

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial

open Purelib.Polynomial.Dense.RootBound
open _root_.Purelib.Polynomial.Dense.RootBound renaming CoefficientPolynomial -> Dense

open Purelib.Polynomial.Power.Gaussian

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

namespace Purelib.Algebra.Power.Gaussian.ExactRoot.Family

set_option genInjectivity false in
/-- A full finite family of distinct exact roots of one Gaussian power equation.

The retained roots share the input and positive degree, their points are duplicate-free, and their count equals the
degree. -/
structure ExactRootFamily (input : Canonical) (degree :
  RootDegree) where
  /-- The displayed roots, each with its exact power equation. -/ members : List (Algebra.Power.Gaussian.ExactRoot
    input degree)
  /-- The displayed root points are pairwise distinct. -/ pointsNodup : (members.map
    Algebra.Power.Gaussian.ExactRoot.point).Nodup
  /-- The number of displayed roots equals the positive degree. -/ count : members.length = degree.value

constructive_injectivity ExactRootFamily

namespace ExactRootFamily

open Purelib.Algebra.Power.Gaussian.ExactRoot.Family
/-- Check whether a candidate batch yields a full distinct exact-root family.

The promoted points must be duplicate-free and their count must equal the degree; none records failure of this finite
batch to pass those checks. -/
def ofCandidates? (input : Canonical) (degree :
  RootDegree)
    (candidates : List Canonical) : Option (ExactRootFamily input degree) :=
  let members := Check.promoteCandidates input degree candidates
  if nodup : (members.map Algebra.Power.Gaussian.ExactRoot.point).Nodup then
    if count : members.length = degree.value then
      some ⟨members, nodup, count⟩
    else
      none
  else
    none

/-- Check the derived finite Gaussian candidates for a full exact-root family.

The deterministic candidate list is promoted and accepted only when its distinct roots fill the prescribed degree. -/
def automatic? (input : Canonical) (degree :
  RootDegree) :
    Option (ExactRootFamily input degree) :=
  ofCandidates? input degree (Candidates.derivedCandidates input degree)

/-- Every additional displayed exact root belongs to a full distinct root family.

A degree-sized duplicate-free family leaves no room for another distinct root of the same nonzero power polynomial. -/
theorem containsDisplayed {input : Canonical}
  {degree : RootDegree}
    (family : ExactRootFamily input degree)
    (candidate : Algebra.Power.Gaussian.ExactRoot input degree) :
    candidate.point ∈ family.members.map Algebra.Power.Gaussian.ExactRoot.point := by
  by_cases absent : candidate.point ∈ family.members.map Algebra.Power.Gaussian.ExactRoot.point
  · exact absent
  exfalso
  let polynomial := Power.Gaussian.rootPolynomial input degree
  have nonzero : polynomial.isZero = false :=
    Dense.Gaussian.Degree.Linear.isZero_false_of_natDegree_pos (by
      rw [Power.Gaussian.rootPolynomial_degree input degree]
      exact degree.positive)
  have nodup :
      (candidate.point :: family.members.map Algebra.Power.Gaussian.ExactRoot.point).Nodup :=
    List.Pairwise.cons (by
      intro point member equal
      cases equal
      exact absent member) family.pointsNodup
  have zeros : ∀ point ∈
      candidate.point :: family.members.map Algebra.Power.Gaussian.ExactRoot.point,
      polynomial.eval point = 0 := by
    intro point member
    rcases Data.List.Membership.mem_cons.mp member with pointEqual | member
    · rw [pointEqual]
      exact candidate.polynomialRoot
    · rcases Data.List.Map.mem_map.mp member with
        ⟨root, _rootMember, pointEqual⟩
      rw [← pointEqual]
      exact root.polynomialRoot
  have bound :=
    Roots.nodup_zeros_length_lt_degreeCount
      polynomial nonzero
      (candidate.point :: family.members.map Algebra.Power.Gaussian.ExactRoot.point) nodup zeros
  have countSlots :=
    DensePolynomial.natDegree_add_one_eq_degreeCount
      nonzero
  rw [List.length_cons, Data.List.Map.length_map, family.count] at bound
  rw [Power.Gaussian.rootPolynomial_degree input degree] at countSlots
  omega

end ExactRootFamily
end Purelib.Algebra.Power.Gaussian.ExactRoot.Family

end
