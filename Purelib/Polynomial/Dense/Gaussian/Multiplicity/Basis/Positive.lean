module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Power
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Purelib.Tactic.Ring

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

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive

/-! ## Positive-degree basis exposed to root isolation -/

set_option genInjectivity false in
/-- One positive-degree pairwise-coprime squarefree factor with its exact
exponent in the weighted product. -/
structure PositiveEntry where
  /-- The original normalized nonzero squarefree polynomial part. -/ part : Squarefree.Part
  /-- The retained polynomial has strictly positive degree. -/ degreePositive : 0 < part.polynomial.natDegree
  /-- The exact occurrence count retained for this factor. -/ multiplicity : Nat
  /-- The retained occurrence count is strictly positive. -/ multiplicityPositive : 0 < multiplicity

constructive_injectivity PositiveEntry

/-- Read the retained positive-degree squarefree factor from a positive multiplicity entry. -/
@[expose] def PositiveEntry.factor (entry : Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry) :
  Dense.Gaussian.Squarefree.Decomposition.Basic.Factor :=
  entry.part.toFactor entry.degreePositive

/-- Remove only degree-zero unit parts from the exact multiplicity basis. -/
@[expose] def positiveEntries : List Dense.Gaussian.Multiplicity.Basis.Basic.BasisEntry → List
  Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry
  | [] => []
  | entry :: entries =>
      if degreeZero : entry.part.polynomial.natDegree = 0 then
        Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries entries
      else
        { part := entry.part
          degreePositive := Nat.pos_of_ne_zero degreeZero
          multiplicity := entry.multiplicity
          multiplicityPositive := entry.multiplicityPositive } ::
            Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries entries

/-- Weighted product of only the positive-degree factors sent to isolation. -/
@[expose] def positiveValue : List Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry → Gaussian.Basic.Canonical →
  Gaussian.Basic.Canonical
  | [], _ => 1
  | entry :: entries, point =>
      entry.part.polynomial.eval point ^ entry.multiplicity *
        Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive.positiveValue entries point

/-- Product of the omitted nonzero degree-zero parts, evaluated at zero.
Degree-zero normalization makes this independent of the queried point. -/
@[expose] def unitValue : List Dense.Gaussian.Multiplicity.Basis.Basic.BasisEntry → Gaussian.Basic.Canonical
  | [] => 1
  | entry :: entries =>
      if entry.part.polynomial.natDegree = 0 then
        entry.part.polynomial.eval 0 ^ entry.multiplicity *
          Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive.unitValue entries
      else
        Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive.unitValue entries

/-- Split the original weighted product into its constant unit factor and retained positive-degree factors.

The equality holds at every displayed Gaussian point, using exact normalization of each omitted degree-zero part. -/
theorem basisValue_eq_unitValue_mul_positiveValue
    (source : List Dense.Gaussian.Multiplicity.Basis.Basic.BasisEntry) (point : Gaussian.Basic.Canonical) :
    Dense.Gaussian.Multiplicity.Basis.Basic.basisValue source point =
      Dense.Gaussian.Multiplicity.Basis.Positive.unitValue source *
        Dense.Gaussian.Multiplicity.Basis.Positive.positiveValue
        (Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries source) point := by
  induction source with
  | nil =>
      simp only [Dense.Gaussian.Multiplicity.Basis.Basic.basisValue,
        Dense.Gaussian.Multiplicity.Basis.Positive.unitValue,
        Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries,
        Dense.Gaussian.Multiplicity.Basis.Positive.positiveValue,
        mul_one, -eq_self]
      rfl
  | cons entry entries inductionHypothesis =>
      rw [Dense.Gaussian.Multiplicity.Basis.Basic.basisValue, Dense.Gaussian.Multiplicity.Basis.Positive.unitValue,
        Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries]
      split
      · rename_i degreeZero
        have constantIdentity : entry.part.polynomial =
            Dense.Basic.DensePolynomial.constant entry.part.polynomial.leadingCoeff := by
          calc
            entry.part.polynomial = entry.part.polynomial.normalize :=
              entry.part.normalized.symm
            _ = Dense.Basic.DensePolynomial.constant entry.part.polynomial.leadingCoeff :=
              Dense.Basic.DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero
                entry.part.nonzero degreeZero
        rw [constantIdentity]
        simp only [Dense.Basic.DensePolynomial.eval_constant]
        rw [inductionHypothesis]
        ring1
      · simp only [Dense.Gaussian.Multiplicity.Basis.Positive.positiveValue]
        rw [inductionHypothesis]
        ring1

/-- The product of the omitted normalized degree-zero parts is nonzero. -/
theorem unitValue_ne_zero (source : List Dense.Gaussian.Multiplicity.Basis.Basic.BasisEntry) :
    Dense.Gaussian.Multiplicity.Basis.Positive.unitValue source ≠ 0 := by
  induction source with
  | nil =>
      simp only [Dense.Gaussian.Multiplicity.Basis.Positive.unitValue]
      exact one_ne_zero
  | cons entry entries inductionHypothesis =>
      rw [Dense.Gaussian.Multiplicity.Basis.Positive.unitValue]
      split
      · rename_i degreeZero
        have constantIdentity : entry.part.polynomial =
            Dense.Basic.DensePolynomial.constant entry.part.polynomial.leadingCoeff := by
          calc
            entry.part.polynomial = entry.part.polynomial.normalize :=
              entry.part.normalized.symm
            _ = Dense.Basic.DensePolynomial.constant entry.part.polynomial.leadingCoeff :=
              Dense.Basic.DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero
                entry.part.nonzero degreeZero
        have valueNonzero : entry.part.polynomial.eval 0 ≠ 0 := by
          rw [constantIdentity, Dense.Basic.DensePolynomial.eval_constant]
          exact Dense.Basic.DensePolynomial.leadingCoeff_ne_zero entry.part.nonzero
        exact Gaussian.Field.mul_ne_zero_direct
          (Gaussian.Power.pow_ne_zero_direct _
            valueNonzero _) inductionHypothesis
      · exact inductionHypothesis

/-- Every retained positive-degree part is the same part as an entry of the original basis. -/
theorem PositiveEntry.part_mem_of_mem_positiveEntries
    {entry : Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry} : ∀ {source : List
      Dense.Gaussian.Multiplicity.Basis.Basic.BasisEntry},
    entry ∈ Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries source →
    ∃ sourceEntry ∈ source, entry.part = sourceEntry.part
  | [], member => by
      change entry ∈ [] at member
      nomatch member
  | sourceEntry :: source, member => by
      rw [Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries] at member
      split at member
      · rcases entry.part_mem_of_mem_positiveEntries member with
          ⟨found, foundMember, same⟩
        exact ⟨found, List.Mem.tail sourceEntry foundMember, same⟩
      · rcases Data.List.Membership.mem_cons.mp member with rfl | tailMember
        · exact ⟨sourceEntry, List.Mem.head _, rfl⟩
        · rcases entry.part_mem_of_mem_positiveEntries tailMember with
            ⟨found, foundMember, same⟩
          exact ⟨found, List.Mem.tail sourceEntry foundMember, same⟩

/-- Removing unit parts preserves pairwise coprimality of every factor sent
to isolation. -/
theorem positiveEntries_pairwise : ∀ {source : List Dense.Gaussian.Multiplicity.Basis.Basic.BasisEntry},
    Dense.Gaussian.Multiplicity.Basis.Basic.BasisPairwise source →
    (Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries source).Pairwise fun left right =>
      CoprimeRelation left.part right.part
  | [], _ => List.Pairwise.nil
  | sourceEntry :: source, pairwise => by
      have pairwiseParts := List.pairwise_cons.mp pairwise
      rw [Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries]
      split
      · exact Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries_pairwise pairwiseParts.2
      · apply List.pairwise_cons.mpr
        constructor
        · intro entry member
          rcases entry.part_mem_of_mem_positiveEntries member with
            ⟨found, foundMember, same⟩
          rw [same]
          exact pairwiseParts.1 found foundMember
        · exact Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries_pairwise pairwiseParts.2

/-- A basis with no retained positive-degree entries has weighted degree zero. -/
theorem basisDegree_eq_zero_of_positiveEntries_eq_nil :
    ∀ (source : List Dense.Gaussian.Multiplicity.Basis.Basic.BasisEntry),
      Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries source = [] →
      Dense.Gaussian.Multiplicity.Basis.Basic.basisDegree source = 0
  | [], _ => rfl
  | entry :: entries, empty => by
      rw [Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries] at empty
      split at empty
      · rename_i degreeZero
        rw [Dense.Gaussian.Multiplicity.Basis.Basic.basisDegree, degreeZero, Nat.mul_zero, Nat.zero_add,
          Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive.basisDegree_eq_zero_of_positiveEntries_eq_nil
            entries empty]
      · exact (List.cons_ne_nil _ _ empty).elim

/-- A positive weighted basis degree guarantees a nonempty list of positive-degree entries. -/
theorem positiveEntries_ne_nil_of_basisDegree_positive
    {source : List Dense.Gaussian.Multiplicity.Basis.Basic.BasisEntry} (positive : 0 <
      Dense.Gaussian.Multiplicity.Basis.Basic.basisDegree source) :
    Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries source ≠ [] := by
  intro empty
  have zero := Dense.Gaussian.Multiplicity.Basis.Positive.basisDegree_eq_zero_of_positiveEntries_eq_nil source empty
  rw [zero] at positive
  exact Nat.lt_irrefl 0 positive
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive

end

public section

/-!
# Box-only general-polynomial isolation after squarefree preprocessing

This is the Paper-I general-polynomial layer.  It computes the exact
pairwise-coprime positive multiplicity basis and runs the standalone box
theorem once for every displayed basis factor.  No finite-name or cylinder
module is imported.
-/

end

public section

/-!
# General-polynomial finite isolation after squarefree preprocessing

This CCL-2 extension adds finite CCL data to the box-only general-polynomial
layer in `Purelib.RootIsolation.Isolation.GeneralBoxFTA`.
-/

end
