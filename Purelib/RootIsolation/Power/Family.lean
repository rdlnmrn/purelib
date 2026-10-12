module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Product
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute
public import Purelib.Polynomial.Power.Gaussian

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data

open Purelib

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

namespace Purelib.RootIsolation.Power.Family

set_option genInjectivity false in
/-- The exact finite preprocessing behind the public multi-valued root
operation.  It contains no chosen roots: only a finite list of exact terminals
and degree-indexed shrinking tracks. -/
structure RootFamily (input : Canonical) (degree :
  RootDegree) where
  /-- The original positive-degree preprocessing of the displayed power polynomial. -/ preprocessing :
    Dense.Gaussian.Squarefree.Decomposition.Compute.PositivePreprocessing (Power.Gaussian.rootPolynomial input degree)

constructive_injectivity RootFamily

namespace RootFamily

open Purelib.RootIsolation
/-- Read the positive multiplicity entries from the retained power-polynomial decomposition. -/
def entries {input : Canonical} {degree :
  RootDegree}
    (family : Power.Family.RootFamily input degree) : List Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry :=
  family.preprocessing.decomposition.positiveMultiplicityEntries

/-- Sum the degree-weighted multiplicities of the retained positive entries. -/
def occurrenceCount {input : Canonical} {degree :
  RootDegree}
    (family : Power.Family.RootFamily input degree) : Nat :=
  Dense.Gaussian.Multiplicity.Basis.Product.positiveDegree family.entries

/-- The finite family has exactly the requested number of root occurrences.
For a nonzero radicand these are `q` distinct sites; for zero this records one
site with multiplicity `q`. -/
theorem occurrenceCount_eq_degree
    {input : Canonical} {degree : RootDegree}
    (family : Power.Family.RootFamily input degree) :
    family.occurrenceCount = degree.value := by
  calc
    family.occurrenceCount =
        (Power.Gaussian.rootPolynomial input degree).normalize.natDegree :=
      family.preprocessing.decomposition.positiveMultiplicityDegree
    _ = (Power.Gaussian.rootPolynomial input degree).natDegree := by
      rw [DensePolynomial.natDegree_normalize]
    _ = degree.value := Power.Gaussian.rootPolynomial_degree input degree
end RootFamily

open Purelib.RootIsolation in
/-- Run the total finite squarefree/multiplicity preprocessing for
`T^q-input`.  The positive-degree proof rules out the zero and constant
branches by inspection of the displayed coefficient list. -/
def roots (input : Canonical) (degree :
  RootDegree) :
    RootFamily input degree := by
  let polynomial := Power.Gaussian.rootPolynomial input degree
  have polynomialDegree : polynomial.natDegree = degree.value :=
    Power.Gaussian.rootPolynomial_degree input degree
  match outcome : Dense.Gaussian.Squarefree.Decomposition.Compute.preprocess polynomial with
  | .zero certificate =>
      have countZero :=
        DensePolynomial.degreeCount_eq_zero_of_isZero
          certificate
      have degreeZero : polynomial.natDegree = 0 := by
        simp only [DensePolynomial.natDegree,
          countZero, Nat.zero_sub, -eq_self, -iff_self]
        rfl
      rw [polynomialDegree] at degreeZero
      exact (Nat.ne_of_gt degree.positive degreeZero).elim
  | .constant _ degreeZero =>
      rw [polynomialDegree] at degreeZero
      exact (Nat.ne_of_gt degree.positive degreeZero).elim
  | .positive preprocessing =>
      exact ⟨by simpa only [polynomial] using preprocessing⟩
end Purelib.RootIsolation.Power.Family

end
