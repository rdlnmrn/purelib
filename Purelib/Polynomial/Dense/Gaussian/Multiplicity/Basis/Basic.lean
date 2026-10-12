module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite multiplicity basis for general polynomials

The recursive derivative-gcd preprocessing returns squarefree occurrences.
Different composite occurrences may overlap.  This module refines such
overlaps by finite pairwise gcd computations.  Every split retains explicit
squarefree and coprimality certificates, so later isolation can run once per
distinct positive-degree basis factor and attach its exact occurrence count.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Basic

/-! ## Pairwise-coprime multiplicity basis -/

set_option genInjectivity false in
/-- One squarefree basis part with its strictly positive occurrence count. -/
structure BasisEntry where
  /-- The retained normalized nonzero squarefree polynomial part. -/ part : Dense.Gaussian.Squarefree.Part
  /-- The displayed occurrence count of this basis part. -/ multiplicity : Nat
  /-- The retained occurrence count is strictly positive. -/ multiplicityPositive : 0 < multiplicity

constructive_injectivity BasisEntry

/-- The retained squarefree basis parts have pairwise constant-degree Euclidean gcds. -/
def BasisPairwise (entries : List
  BasisEntry) : Prop :=
  entries.Pairwise fun left right => Dense.Gaussian.Multiplicity.CoprimeRelation left.part right.part

/-- A displayed external squarefree part has constant-degree gcd with every retained basis part. -/
def AllCoprime (external :
  Dense.Gaussian.Squarefree.Part) (entries : List BasisEntry) : Prop :=
  ∀ entry ∈ entries, Dense.Gaussian.Multiplicity.CoprimeRelation external entry.part

/-- Evaluated product of the pairwise-coprime basis, with each part raised to
its displayed occurrence count. -/
def basisValue : List
  BasisEntry → Gaussian.Basic.Canonical → Gaussian.Basic.Canonical
  | [], _ => 1
  | entry :: entries, point =>
      entry.part.polynomial.eval point ^ entry.multiplicity *
        basisValue entries point

/-- Degree of the weighted basis product. -/
def basisDegree : List
  BasisEntry → Nat
  | [] => 0
  | entry :: entries =>
      entry.multiplicity * entry.part.polynomial.natDegree +
        basisDegree entries
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Basic

end
