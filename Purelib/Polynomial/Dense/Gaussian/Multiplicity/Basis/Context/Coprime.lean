module
import Purelib.Data.List.Map
import Purelib.Data.List.Pairwise
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Power
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Product
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Power
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part

open Purelib.Polynomial

section
public section

/-!
# Winding of finite weighted multiplicity products

This module connects the executable multiplicity polynomial from
`ConstructiveMultiplicity` to the finite box product formula.  Powers are
structural recursion over a displayed natural number; no root collection or
factor evaluation over a completed carrier is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context

open Purelib.Data in
/-- Enumerating every focused position preserves the pairwise-coprime
relation carried by the source list. -/
theorem Coprime.positiveContexts_pairwise : ∀ {entries : List Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry},
    (entries.Pairwise fun left right =>
      CoprimeRelation left.part right.part) →
    (Dense.Gaussian.Multiplicity.Basis.Context.Basic.positiveContexts entries).Pairwise fun left right =>
      CoprimeRelation
        left.focus.part right.focus.part
  | [], _ => List.Pairwise.nil
  | head :: entries, pairwise => by
      have source := List.pairwise_cons.mp pairwise
      rw [Dense.Gaussian.Multiplicity.Basis.Context.Basic.positiveContexts]
      apply List.pairwise_cons.mpr
      constructor
      · intro context member
        rcases List.Map.mem_map.mp member with ⟨tailContext, tailMember, rfl⟩
        exact source.1 tailContext.focus tailContext.focus_mem
      · apply List.Pairwise.pairwise_map.mpr
        exact Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Coprime.positiveContexts_pairwise source.2
namespace Basic.PositiveContext

/-- The focused factor is coprime to every entry in its retained prefix or suffix.

The conclusion follows from the original list's pairwise coprimality and the exact context split. -/
theorem focus_coprime_other
    {entries : List Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry} (context :
      Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext entries)
    (pairwise : entries.Pairwise fun left right =>
      CoprimeRelation left.part right.part)
    {other : Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry}
    (member : other ∈ context.before ++ context.after) :
    CoprimeRelation
      context.focus.part other.part := open Purelib in by
  have pairwiseSplit :
      (context.before ++ context.focus :: context.after).Pairwise
        (fun left right =>
          CoprimeRelation left.part right.part) :=
    (congrArg (fun values : List Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry =>
      values.Pairwise (fun left right =>
        CoprimeRelation left.part right.part))
      context.split).mp pairwise
  have reordered :
      (context.focus :: context.before ++ context.after).Pairwise
        (fun left right =>
          CoprimeRelation left.part right.part) :=
    (Data.List.Pairwise.pairwise_middle
      (R := fun left right : Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry =>
        CoprimeRelation left.part right.part)
      (fun {_ _} relation =>
        Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_symm relation)).mp
          pairwiseSplit
  exact (List.pairwise_cons.mp reordered).1 other member

/-- A focused factor is coprime to the weighted polynomial of a list whose
every entry carries the displayed pairwise relation. -/
@[expose] def coprimePositivePolynomial
    (focus : Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry) :
    (others : List Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry) →
    (∀ other ∈ others,
      CoprimeRelation
        focus.part other.part) →
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate focus.part.polynomial
      (Dense.Gaussian.Multiplicity.Basis.Product.positivePolynomial others)
  | [], _ =>
      Dense.Gaussian.Coprime.Operations.CoprimeCertificate.constantRight
        focus.part.nonzero
  | other :: others, relations => by
      let factorCoprime :=
        Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeCertificateOfRelation
          focus.part other.part (relations other List.mem_cons_self)
      let powerCoprime := Dense.Gaussian.Coprime.Power.polynomialPowerRightCoprime focus.part.nonzero
        factorCoprime other.multiplicity
      let restCoprime :=
        Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext.coprimePositivePolynomial
        focus others
        (fun entry member => relations entry
          (List.mem_cons_of_mem other member))
      exact
        Dense.Gaussian.Coprime.Operations.CoprimeCertificate.mulRight
          focus.part.nonzero powerCoprime restCoprime
end Basic.PositiveContext

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context

end
