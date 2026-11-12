module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Insert
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Tactic.Ring.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic

open Purelib.Data

open Purelib.Polynomial

public section

/-!
# Finite multiplicity basis for general polynomials

The recursive derivative-gcd preprocessing returns squarefree occurrences.
Different composite occurrences may overlap.  This module refines such
overlaps by finite pairwise gcd computations.  Every split retains explicit
squarefree and coprimality certificates, so later isolation can run once per
distinct positive-degree basis factor and attach its exact occurrence count.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity

/-! ## Basis for a complete occurrence decomposition -/

namespace Basis.Build

/-- Sum the natural degrees of a finite squarefree occurrence list.

Repeated occurrences contribute separately, so this total records degree before the coprime multiplicity basis is
assembled. -/
@[expose] def occurrenceDegree : List Factor → Nat
  | [] => 0
  | factor :: factors =>
      factor.polynomial.natDegree + Build.occurrenceDegree factors

end Basis.Build

set_option genInjectivity false in
/-- Pairwise-coprime squarefree basis of a finite squarefree occurrence list.

The original entries retain their multiplicities, pointwise product identity
and exact weighted-degree balance against that same occurrence list. -/
structure Basis (source : List Factor) where
  /-- The retained squarefree basis entries with their multiplicities. -/ entries : List
    Basis.Basic.BasisEntry
  /-- Distinct retained entries carry pairwise coprimality certificates. -/ pairwise :
    Basis.Basic.BasisPairwise entries
  /-- The weighted basis value equals evaluation of the original occurrence product at every displayed point. -/
    valueIdentity : ∀ point : Gaussian.Basic.Canonical,
    Basis.Basic.basisValue entries point =
      (Squarefree.Decomposition.Basic.factorProduct source).eval point
  /-- The weighted basis degree equals the total degree of the original occurrence list. -/ degreeIdentity :
    Basis.Basic.basisDegree entries =
    Basis.Build.occurrenceDegree source

constructive_injectivity Basis

namespace Basis.Build

/-- Fold the certified insertion algorithm over every squarefree occurrence.

Each original head occurrence is inserted into the retained tail basis. The
result caches the selected entries with their product and degree certificates. -/
@[expose] def buildBasis : (source : List Factor) →
  Basis source
  | [] =>
      { entries := []
        pairwise := List.Pairwise.nil
        valueIdentity := by
          intro point
          simp only [Basic.basisValue,
            Squarefree.Decomposition.Basic.factorProduct, Basic.DensePolynomial.eval_constant,
              -eq_self, -iff_self]
          rfl
        degreeIdentity := rfl }
  | factor :: factors => by
      let tailBasis := Build.buildBasis factors
      let insertion := Insert.insertPart (Squarefree.Part.Factor.toPart
        factor) tailBasis.entries
        tailBasis.pairwise
      exact
        { entries := insertion.entries
          pairwise := insertion.pairwise
          valueIdentity := by
            intro point
            rw [insertion.valueIdentity point,
              tailBasis.valueIdentity point]
            simp only [Squarefree.Part.Factor.toPart,
              Squarefree.Decomposition.Basic.factorProduct, Basic.DensePolynomial.eval_mul,
                -eq_self, -iff_self]
            ring1
          degreeIdentity := by
            rw [insertion.degreeIdentity, tailBasis.degreeIdentity]
            simp only [Squarefree.Part.Factor.toPart,
              occurrenceDegree, -eq_self, -iff_self]
            ring1 }

end Basis.Build

namespace Basis.Build

/-- The recursive occurrence degree equals the list sum of the displayed factor degrees.

Both scans retain every original factor degree in the same list order,
including separately repeated occurrences. -/
theorem occurrenceDegree_eq_sum (source : List Factor) :
    occurrenceDegree source =
      (source.map fun factor => factor.polynomial.natDegree).sum := by
  induction source with
  | nil => rfl
  | cons factor factors inductionHypothesis =>
      simp only [occurrenceDegree, List.map_cons, List.sum_cons,
        inductionHypothesis, -eq_self, -iff_self]
      rfl

end Basis.Build

end Purelib.Polynomial.Dense.Gaussian.Multiplicity
