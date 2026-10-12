module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Algebra.Semiring.Normalization
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.List.Pairwise
import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CommonSplit
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part

import Purelib.Tactic.QuotientFreeOmega
public import Mathlib.Tactic.Ring.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib

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

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Insert

set_option genInjectivity false in
/-- Result of inserting one squarefree occurrence into an already pairwise-
coprime basis.  The external-preservation field is the induction invariant
that lets later gcd splits retain pairwise coprimality.

The retained entry list carries the original evaluation and degree identities and the same external coprimality
invariant. -/
structure Insertion (new : Squarefree.Part) (source : List
  Dense.Gaussian.Multiplicity.Basis.Basic.BasisEntry) where
  /-- The resulting retained multiplicity basis after inserting the new squarefree occurrence. -/ entries : List
    Dense.Gaussian.Multiplicity.Basis.Basic.BasisEntry
  /-- The resulting parts are pairwise coprime. -/ pairwise : Dense.Gaussian.Multiplicity.Basis.Basic.BasisPairwise
    entries
  /-- The resulting weighted evaluation product equals the source product times the inserted polynomial value. -/
    valueIdentity : ∀ point : Gaussian.Basic.Canonical,
    Dense.Gaussian.Multiplicity.Basis.Basic.basisValue entries point =
      Dense.Gaussian.Multiplicity.Basis.Basic.basisValue source point * new.polynomial.eval point
  /-- The resulting weighted degree is the source weighted degree plus the inserted polynomial degree. -/ degreeIdentity
    : Dense.Gaussian.Multiplicity.Basis.Basic.basisDegree entries =
    Dense.Gaussian.Multiplicity.Basis.Basic.basisDegree source + new.polynomial.natDegree
  /-- A part coprime to the inserted part and every source entry remains coprime to every resulting entry. -/
    preservesExternal : ∀ (external : Squarefree.Part),
    CoprimeRelation external new →
    Dense.Gaussian.Multiplicity.Basis.Basic.AllCoprime external source →
    Dense.Gaussian.Multiplicity.Basis.Basic.AllCoprime external entries

constructive_injectivity Insertion

/-- Insert one squarefree occurrence.  A coprime head is retained.  A
nonconstant common gcd receives one additional occurrence, the old head's
residual keeps its old multiplicity, and the new residual continues through
the tail.  Recursion is solely on the finite source list.

The original finite list recursion retains every coprime head and uses the same common-gcd factors, multiplicities and
residual insertion when overlap occurs. -/
@[expose] def insertPart : (new : Squarefree.Part) → (source : List
  Dense.Gaussian.Multiplicity.Basis.Basic.BasisEntry) →
    Dense.Gaussian.Multiplicity.Basis.Basic.BasisPairwise source → Insertion new source
  | new, [], _ => by
      exact
        { entries :=
            [{ part := new
               multiplicity := 1
               multiplicityPositive := Nat.zero_lt_succ 0 }]
          pairwise := Data.List.Pairwise.pairwise_singleton _ _
          valueIdentity := by
            intro point
            simp only [Dense.Gaussian.Multiplicity.Basis.Basic.basisValue, pow_one, mul_one, one_mul,
              -eq_self, -iff_self]
            rfl
          degreeIdentity := by
            simp only [Dense.Gaussian.Multiplicity.Basis.Basic.basisDegree, Nat.one_mul, Nat.add_zero,
              Nat.zero_add, -eq_self, -iff_self]
            rfl
          preservesExternal := by
            intro external externalNew _ entry member
            have same := Data.List.Membership.mem_singleton.mp member
            subst entry
            exact externalNew }
  | new, head :: tail, pairwise => by
      have pairwiseParts := List.pairwise_cons.mp pairwise
      have headTail : Dense.Gaussian.Multiplicity.Basis.Basic.AllCoprime head.part tail := pairwiseParts.1
      have tailPairwise : Dense.Gaussian.Multiplicity.Basis.Basic.BasisPairwise tail := pairwiseParts.2
      match outcome : Dense.Gaussian.Coprime.Decision.coprimeOutcome
          new.polynomial head.part.polynomial (Or.inl new.nonzero) with
      | .coprime certificate =>
          let recursive := Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Insert.insertPart new tail tailPairwise
          have newHead : CoprimeRelation new head.part :=
            Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelationOfCertificate certificate
          have headNew : CoprimeRelation head.part new :=
            Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_symm newHead
          have headRest : Dense.Gaussian.Multiplicity.Basis.Basic.AllCoprime head.part recursive.entries :=
            recursive.preservesExternal head.part headNew headTail
          exact
            { entries := head :: recursive.entries
              pairwise := List.pairwise_cons.mpr
                ⟨headRest, recursive.pairwise⟩
              valueIdentity := by
                intro point
                simp only [Dense.Gaussian.Multiplicity.Basis.Basic.basisValue, -eq_self, -iff_self]
                rw [recursive.valueIdentity point]
                ring1
              degreeIdentity := by
                simp only [Dense.Gaussian.Multiplicity.Basis.Basic.basisDegree, -eq_self, -iff_self]
                rw [recursive.degreeIdentity]
                ring1
              preservesExternal := by
                intro external externalNew externalSource entry member
                rcases Data.List.Membership.mem_cons.mp member with rfl | restMember
                · exact externalSource _ List.mem_cons_self
                · apply recursive.preservesExternal external externalNew
                    (fun tailEntry tailMember =>
                      externalSource tailEntry
                        (List.mem_cons_of_mem head tailMember))
                    entry restMember }
      | .commonDivisor common =>
          have newPositive : 0 < new.polynomial.natDegree :=
            common.positiveDegree.trans_le
              (common.result.degreeLeLeft new.nonzero)
          have headPositive : 0 < head.part.polynomial.natDegree :=
            common.positiveDegree.trans_le
              (common.result.degreeLeRight head.part.nonzero)
          let newFactor := new.toFactor newPositive
          let headFactor := head.part.toFactor headPositive
          let split := Dense.Gaussian.Multiplicity.CommonSplit.commonSplit newFactor headFactor common
          let recursive := Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Insert.insertPart split.leftRemainder
            tail tailPairwise
          let commonEntry : Dense.Gaussian.Multiplicity.Basis.Basic.BasisEntry :=
            { part := (Dense.Gaussian.Squarefree.Part.Factor.toPart split.common)
              multiplicity := head.multiplicity + 1
              multiplicityPositive := by omega }
          let rightEntry : Dense.Gaussian.Multiplicity.Basis.Basic.BasisEntry :=
            { part := split.rightRemainder
              multiplicity := head.multiplicity
              multiplicityPositive := head.multiplicityPositive }
          have commonLeft : CoprimeRelation commonEntry.part
              split.leftRemainder :=
            Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelationOfCertificate split.commonLeftCoprime
          have commonRight : CoprimeRelation commonEntry.part
              rightEntry.part :=
            Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelationOfCertificate split.commonRightCoprime
          have leftRight : CoprimeRelation split.leftRemainder
              rightEntry.part :=
            Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelationOfCertificate split.remaindersCoprime
          have rightLeft : CoprimeRelation rightEntry.part
              split.leftRemainder := Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_symm leftRight
          have commonTail : Dense.Gaussian.Multiplicity.Basis.Basic.AllCoprime commonEntry.part tail := by
            intro entry member
            have headEntry := headTail entry member
            have childEntry := Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_leftFactor
              (parent := head.part) (other := entry.part)
              (child := commonEntry.part) headEntry
                split.rightFactorization
            exact childEntry
          have rightTail : Dense.Gaussian.Multiplicity.Basis.Basic.AllCoprime rightEntry.part tail := by
            intro entry member
            have headEntry := headTail entry member
            exact Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_rightFactor
              (parent := head.part) (other := entry.part)
              (child := rightEntry.part) headEntry
                split.rightFactorization
          have commonRest : Dense.Gaussian.Multiplicity.Basis.Basic.AllCoprime commonEntry.part recursive.entries :=
            recursive.preservesExternal commonEntry.part commonLeft commonTail
          have rightRest : Dense.Gaussian.Multiplicity.Basis.Basic.AllCoprime rightEntry.part recursive.entries :=
            recursive.preservesExternal rightEntry.part rightLeft rightTail
          exact
            { entries := commonEntry :: rightEntry :: recursive.entries
              pairwise := by
                apply List.pairwise_cons.mpr
                constructor
                · intro entry member
                  rcases Data.List.Membership.mem_cons.mp member with rfl | restMember
                  · exact commonRight
                  · exact commonRest entry restMember
                · exact List.pairwise_cons.mpr ⟨rightRest,
                    recursive.pairwise⟩
              valueIdentity := by
                intro point
                have newValue :=
                  Dense.Gaussian.Factorization.Identity.eval_factorization
                    split.leftFactorization point
                have headValue :=
                  Dense.Gaussian.Factorization.Identity.eval_factorization
                    split.rightFactorization point
                have newValue' : new.polynomial.eval point =
                    split.common.polynomial.eval point *
                      split.leftRemainder.polynomial.eval point := by
                  exact newValue
                have headValue' : head.part.polynomial.eval point =
                    split.common.polynomial.eval point *
                      split.rightRemainder.polynomial.eval point := by
                  exact headValue
                simp only [Dense.Gaussian.Multiplicity.Basis.Basic.basisValue, -eq_self, -iff_self]
                rw [recursive.valueIdentity point]
                dsimp only [commonEntry, rightEntry, Dense.Gaussian.Squarefree.Part.Factor.toPart]
                rw [newValue', headValue',
                  Algebra.Semiring.Normalization.product_pow, pow_succ]
                ring1
              degreeIdentity := by
                have newDegree :
                    split.common.polynomial.natDegree +
                        split.leftRemainder.polynomial.natDegree =
                      new.polynomial.natDegree := by
                  exact split.leftDegreeSum
                have headDegree :
                    split.common.polynomial.natDegree +
                        split.rightRemainder.polynomial.natDegree =
                      head.part.polynomial.natDegree := by
                  exact split.rightDegreeSum
                simp only [Dense.Gaussian.Multiplicity.Basis.Basic.basisDegree, -eq_self, -iff_self]
                rw [recursive.degreeIdentity, ← newDegree, ← headDegree]
                dsimp only [commonEntry, rightEntry, Dense.Gaussian.Squarefree.Part.Factor.toPart]
                ring1
              preservesExternal := by
                intro external externalNew externalSource entry member
                have externalHead :
                    CoprimeRelation external head.part :=
                  externalSource head List.mem_cons_self
                have externalTail : Dense.Gaussian.Multiplicity.Basis.Basic.AllCoprime external tail :=
                  fun tailEntry tailMember => externalSource tailEntry
                    (List.mem_cons_of_mem head tailMember)
                have externalCommon :
                    CoprimeRelation external commonEntry.part := by
                  apply Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_symm
                  exact Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_leftFactor
                    (parent := new) (other := external)
                    (child := commonEntry.part)
                      (Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_symm externalNew)
                        split.leftFactorization
                have externalRight :
                    CoprimeRelation external rightEntry.part := by
                  apply Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_symm
                  exact Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_rightFactor
                    (parent := head.part) (other := external)
                    (child := rightEntry.part)
                      (Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_symm externalHead)
                        split.rightFactorization
                have externalLeft :
                    CoprimeRelation external split.leftRemainder := by
                  apply Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_symm
                  exact Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_rightFactor
                    (parent := new) (other := external)
                    (child := split.leftRemainder)
                      (Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_symm externalNew)
                        split.leftFactorization
                rcases Data.List.Membership.mem_cons.mp member with rfl | member
                · exact externalCommon
                · rcases Data.List.Membership.mem_cons.mp member with rfl | restMember
                  · exact externalRight
                  · exact recursive.preservesExternal external
                      externalLeft externalTail entry restMember }
termination_by structural _ source _ => source
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Insert

end
