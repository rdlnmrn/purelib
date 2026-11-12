module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
public import Purelib.Data.Vector.DependentMatrix
import Purelib.Data.List.Pairwise
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached coprimality of original positive multiplicity factors

Each ordered pair keeps its two original bounded factor indices. Equal indices
retain their identity; distinct indices retain the coefficient-computed Bézout
certificate. The dependent matrix materializes these certificates once.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive

open Purelib.Data.Vector (DependentMatrix)
open Purelib.Data.List.Pairwise
open Purelib.Polynomial.Dense.Gaussian

set_option genInjectivity false in
/-- The original identity or actual coprimality certificate of an ordered pair of retained factors. -/
inductive CoprimePair (entries : List PositiveEntry) (first second : Fin entries.length) where
  /-- Equal original factor-list indices retain their identity. -/
  | same (equal : first = second)
  /-- Distinct original factors retain their full ordered Bézout certificate. -/
  | coprime (certificate : Coprime.Basic.CoprimeCertificate
      (entries.get first).part.polynomial (entries.get second).part.polynomial)

constructive_injectivity CoprimePair

namespace CoprimePair

/-- Materialize an original ordered factor pair from the retained pairwise coprimality law. -/
def ofPairwise (entries : List PositiveEntry)
    (pairwise : entries.Pairwise fun left right => Multiplicity.CoprimeRelation left.part right.part)
    (first second : Fin entries.length) : CoprimePair entries first second := by
  if equal : first = second then
    exact .same equal
  else
    have relation : Multiplicity.CoprimeRelation (entries.get first).part (entries.get second).part := by
      if ordered : first.val < second.val then
        exact pairwise_get_of_val_lt pairwise first second ordered
      else
        have different : first.val ≠ second.val := fun same => equal (Fin.ext same)
        have reverse : second.val < first.val := by omega0
        exact Multiplicity.CoprimeRelation.coprimeRelation_symm
          (pairwise_get_of_val_lt pairwise second first reverse)
    exact .coprime (Multiplicity.CoprimeRelation.coprimeCertificateOfRelation _ _ relation)

/-- Read an already stored ordered Bézout certificate at distinct original factor indices. -/
@[expose] def certificate {entries : List PositiveEntry} {first second : Fin entries.length}
    (pair : CoprimePair entries first second) (different : first ≠ second) :
    Coprime.Basic.CoprimeCertificate (entries.get first).part.polynomial (entries.get second).part.polynomial :=
  match pair with
  | .same equal => (different equal).elim
  | .coprime certificate => certificate

end CoprimePair

/-- A dependent matrix of the actual ordered certificates on the original retained factor list. -/
abbrev CoprimePairs (entries : List PositiveEntry) :=
  DependentMatrix (fun first second => CoprimePair entries first second)

namespace CoprimePairs

/-- Compute and retain each original factor-pair certificate once in the same bounded order. -/
def ofPairwise (entries : List PositiveEntry)
    (pairwise : entries.Pairwise fun left right => Multiplicity.CoprimeRelation left.part right.part) :
    CoprimePairs entries :=
  DependentMatrix.ofFn (CoprimePair.ofPairwise entries pairwise)

/-- Read the actual stored ordered factor-pair entry without rerunning its Euclidean computation. -/
@[expose] def get {entries : List PositiveEntry} (pairs : CoprimePairs entries)
    (first second : Fin entries.length) : CoprimePair entries first second :=
  DependentMatrix.get pairs first second

/-- Reading the materialized factor-pair bank retains the complete original ordered producer certificate. -/
theorem ofPairwise_get (entries : List PositiveEntry)
    (pairwise : entries.Pairwise fun left right => Multiplicity.CoprimeRelation left.part right.part)
    (first second : Fin entries.length) :
    get (ofPairwise entries pairwise) first second = CoprimePair.ofPairwise entries pairwise first second :=
  DependentMatrix.ofFn_get (CoprimePair.ofPairwise entries pairwise) first second

end CoprimePairs

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive

end
