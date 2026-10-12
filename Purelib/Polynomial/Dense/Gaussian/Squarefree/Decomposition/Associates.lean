module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.Map
import Purelib.Data.List.Filter
import Purelib.Data.List.Pairwise
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic (Factor)

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# General finite squarefree-factor preprocessing

The executable squarefreeness decision either returns a finite Bézout
certificate or splits the input by its computed nonconstant gcd with the
derivative.  Both displayed factors then have strictly smaller positive
degree.  Recursing on those natural degrees produces a finite occurrence list
of squarefree factors whose evaluated product is the normalized input.

Repeated factors appear as repeated squarefree occurrences at this layer;
the following multiplicity layer canonically groups associates without
creating duplicate root-isolation machines.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition

/-! ## Associate grouping and multiplicities -/

namespace Basic.Factor

/-- Canonical monic key of a nonzero squarefree occurrence.  It is used only
for finite comparison; the original factor and its certificate remain the
paper-facing isolation input. -/
def monicKey (factor :
  Factor) : (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  DensePolynomial.scale factor.polynomial.leadingCoeff⁻¹ factor.polynomial

end Basic.Factor

namespace Basic.Factor

/-- Evaluate a monic key by scaling the original factor value.

The scalar is the inverse of the original leading coefficient. -/
theorem monicKey_eval (factor :
  Factor) (point : Gaussian.Basic.Canonical) :
    factor.monicKey.eval point =
      factor.polynomial.leadingCoeff⁻¹ * factor.polynomial.eval point := by
  exact DensePolynomial.eval_scale _ _ _

end Basic.Factor

section
namespace Associates

/-- Equal monic keys transport a zero between the original factors.

The retained nonzero leading coefficient permits cancellation of its inverse. -/
private theorem
  eval_eq_zero_of_monicKey_eq
    {left right : Factor} (same : left.monicKey = right.monicKey)
    {point : Gaussian.Basic.Canonical} (leftZero : left.polynomial.eval point = 0) :
    right.polynomial.eval point = 0 := open Purelib.Algebra.Field in by
  have keyValues := congrArg (fun polynomial : CoefficientPolynomial =>
    polynomial.eval point) same
  rw [left.monicKey_eval, right.monicKey_eval, leftZero, mul_zero] at keyValues
  have inverseNonzero : right.polynomial.leadingCoeff⁻¹ ≠ 0 :=
    ExplicitField.inv_ne_zero (DensePolynomial.leadingCoeff_ne_zero right.nonzero)
  by_cases rightZero : right.polynomial.eval point = 0
  · exact rightZero
  · have productNonzero :=
      Gaussian.Field.mul_ne_zero_direct inverseNonzero
        rightZero
    exact (productNonzero keyValues.symm).elim

end Associates

end

namespace Basic.Factor

/-- Equal monic keys are an exact finite certificate that two associate
squarefree occurrences have the same Gaussian-rational zeros. -/
theorem eval_eq_zero_iff_of_monicKey_eq
    {left right : Factor} (same : left.monicKey = right.monicKey)
    (point : Gaussian.Basic.Canonical) :
    left.polynomial.eval point = 0 ↔ right.polynomial.eval point = 0 := by
  constructor
  · exact Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Associates.eval_eq_zero_of_monicKey_eq same
  · exact Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Associates.eval_eq_zero_of_monicKey_eq same.symm

end Basic.Factor

namespace Associates

/-- Insert one factor only when no existing representative has its monic key. -/
def insertRepresentative (factor :
  Factor) : List Factor →
  List Factor
  | [] => [factor]
  | representative :: representatives =>
      if factor.monicKey = representative.monicKey then
        representative :: representatives
      else
        representative :: insertRepresentative
          factor representatives

end Associates

namespace Associates

/-- Existing representatives are never removed by insertion. -/
theorem mem_insertRepresentative_of_mem
    (factor : Factor) : ∀ {representatives : List
      Factor}
    {representative : Factor}, representative ∈ representatives →
    representative ∈ insertRepresentative factor representatives
  | [], _, member => by nomatch member
  | head :: tail, representative, member => by
      rw [insertRepresentative]
      split
      · exact member
      · cases member with
        | head => exact List.Mem.head _
        | tail _ member =>
          exact List.Mem.tail head
            (mem_insertRepresentative_of_mem
              factor member)

end Associates

namespace Associates

/-- Every inserted representative came from the old list or is the new
factor. -/
theorem mem_of_mem_insertRepresentative
    (factor : Factor) : ∀ {representatives : List
      Factor}
    {representative : Factor},
    representative ∈ insertRepresentative factor representatives →
    representative = factor ∨ representative ∈ representatives
  | [], representative, member => by
      change representative ∈ [factor]
        at member
      cases member with
      | head => exact Or.inl rfl
      | tail _ impossible => nomatch impossible
  | head :: tail, representative, member => by
      rw [insertRepresentative]
        at member
      split at member
      · exact Or.inr member
      · cases member with
        | head => exact Or.inr (List.Mem.head _)
        | tail _ member =>
          rcases mem_of_mem_insertRepresentative
            factor member with
            rfl | oldMember
          · exact Or.inl rfl
          · exact Or.inr (List.Mem.tail head oldMember)

end Associates

namespace Associates

/-- The inserted factor has an associate representative in the result. -/
theorem inserted_has_representative
    (factor : Factor) (representatives : List
      Factor) :
    ∃ representative ∈ insertRepresentative factor representatives,
      factor.monicKey = representative.monicKey := by
  induction representatives with
  | nil => exact ⟨factor, List.mem_cons_self, rfl⟩
  | cons representative representatives inductionHypothesis =>
      change ∃ found ∈
          (if factor.monicKey = representative.monicKey then
            representative :: representatives
          else
            representative :: insertRepresentative factor
              representatives),
        factor.monicKey = found.monicKey
      by_cases same : factor.monicKey = representative.monicKey
      · rw [if_pos same]
        exact ⟨representative, List.mem_cons_self, same⟩
      · rw [if_neg same]
        rcases inductionHypothesis with
          ⟨found, member, same⟩
        exact ⟨found, List.mem_cons_of_mem representative member, same⟩

end Associates

namespace Associates

/-- Select one representative of each monic associate class by a structural
fold over the finite occurrence list. -/
def representatives : List
  Factor → List Factor
  | [] => []
  | factor :: factors =>
      insertRepresentative factor
        (Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Associates.representatives factors)

end Associates

namespace Associates

/-- Every selected associate representative occurs in the original finite list. -/
theorem representative_mem_source : ∀
  (source : List Factor)
    {representative : Factor},
    representative ∈ Dense.Gaussian.Squarefree.Decomposition.Associates.representatives source → representative ∈ source
  | [], _, member => by
      change _ ∈ [] at member
      exact (List.not_mem_nil member).elim
  | factor :: factors, representative, member => by
      rcases mem_of_mem_insertRepresentative factor member with
        rfl | tailMember
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem factor
          (representative_mem_source factors
            tailMember)

end Associates

namespace Associates

/-- Every squarefree occurrence is represented by an associate in the finite
distinct list. -/
theorem source_has_representative : ∀
  (source : List Factor)
    {occurrence : Factor}, occurrence ∈ source →
    ∃ representative ∈ Dense.Gaussian.Squarefree.Decomposition.Associates.representatives source,
      occurrence.monicKey = representative.monicKey
  | [], _, member => by nomatch member
  | factor :: factors, occurrence, member => by
      cases member with
      | head =>
        exact inserted_has_representative factor
          (Dense.Gaussian.Squarefree.Decomposition.Associates.representatives factors)
      | tail _ member =>
        rcases source_has_representative factors member with
          ⟨representative, representativeMember, same⟩
        exact ⟨representative,
          mem_insertRepresentative_of_mem factor
            representativeMember, same⟩

end Associates

section
namespace Associates

/-- Insertion preserves pairwise distinct monic keys.

A factor is inserted only after it differs from every retained representative. -/
private theorem
  insertRepresentative_pairwise
    (factor : Factor) : ∀ {source : List
      Factor},
    source.Pairwise (fun left right => left.monicKey ≠ right.monicKey) →
    (insertRepresentative factor source).Pairwise
      (fun left right => left.monicKey ≠ right.monicKey)
  | [], _ => Purelib.Data.List.Pairwise.pairwise_singleton _ _
  | representative :: representatives, pairwise => by
      rw [insertRepresentative]
      split
      · exact pairwise
      · rename_i different
        apply List.pairwise_cons.mpr
        constructor
        · intro found member same
          rcases mem_of_mem_insertRepresentative factor member with
            rfl | oldMember
          · exact different same.symm
          · exact (List.pairwise_cons.mp pairwise).1 found oldMember same
        · exact
            insertRepresentative_pairwise
            factor
            (List.pairwise_cons.mp pairwise).2

end Associates

end

namespace Associates

/-- The selected representatives have pairwise different monic keys. -/
theorem representatives_pairwise : ∀ source
  : List Factor,
    (Dense.Gaussian.Squarefree.Decomposition.Associates.representatives source).Pairwise
      (fun left right => left.monicKey ≠ right.monicKey)
  | [] => List.Pairwise.nil
  | factor :: factors =>
      insertRepresentative_pairwise factor
        (representatives_pairwise factors)

end Associates

namespace Associates

/-- Inserting a factor always produces a nonempty representative list. -/
theorem insertRepresentative_ne_nil
    (factor : Factor) : ∀ representatives : List
      Factor,
    insertRepresentative factor representatives ≠ []
  | [] => List.cons_ne_nil factor []
  | representative :: representatives => by
      rw [insertRepresentative]
      split
      · exact List.cons_ne_nil representative representatives
      · exact List.cons_ne_nil representative
          (insertRepresentative factor representatives)

end Associates

namespace Associates

/-- A nonempty occurrence list has a nonempty representative list. -/
theorem representatives_ne_nil_of_ne_nil
    {source : List Factor} (nonempty : source ≠ []) :
    Dense.Gaussian.Squarefree.Decomposition.Associates.representatives source ≠ [] := by
  cases source with
  | nil => exact (nonempty rfl).elim
  | cons factor factors =>
      exact insertRepresentative_ne_nil factor
        (Dense.Gaussian.Squarefree.Decomposition.Associates.representatives factors)

end Associates

namespace Associates

/-- Number of squarefree occurrences associate to the displayed factor. -/
def multiplicity (source : List
  Factor) (factor : Factor)
  : Nat :=
  (source.filter fun occurrence =>
    decide (occurrence.monicKey = factor.monicKey)).length

end Associates

namespace Associates

/-- A factor occurring in the source has positive associate multiplicity. -/
theorem multiplicity_positive_of_mem
    {source : List Factor} {factor :
      Factor} (member : factor ∈ source) :
    0 < Dense.Gaussian.Squarefree.Decomposition.Associates.multiplicity source factor := by
  have filteredMember : factor ∈ source.filter fun occurrence =>
      decide (occurrence.monicKey = factor.monicKey) :=
    List.Filter.mem_filter.mpr ⟨member, decide_eq_true rfl⟩
  unfold Dense.Gaussian.Squarefree.Decomposition.Associates.multiplicity
  cases filteredEquation : source.filter (fun occurrence =>
      decide (occurrence.monicKey = factor.monicKey)) with
  | nil =>
      rw [filteredEquation] at filteredMember
      exact (List.not_mem_nil filteredMember).elim
  | cons occurrence occurrences =>
      exact Nat.zero_lt_succ _

end Associates

namespace Associates

set_option genInjectivity false in
/-- A squarefree factor paired with a natural multiplicity count.

The record stores the factor and count; the constructor from a source list establishes their occurrence interpretation
separately. -/
structure MultiplicityFactor where
  /-- The retained squarefree factor representing an associate class. -/ factor :
    Factor
  /-- The stored natural count associated with the factor. -/ multiplicity : Nat

constructive_injectivity MultiplicityFactor

end Associates

namespace Associates

/-- Attach the source occurrence count to each selected associate representative.

Representatives retain their original certified factors, and multiplicities count equality of their monic keys. -/
def multiplicityFactors (source : List
  Factor) : List
  MultiplicityFactor :=
  (Dense.Gaussian.Squarefree.Decomposition.Associates.representatives source).map fun factor =>
    { factor := factor
      multiplicity := Dense.Gaussian.Squarefree.Decomposition.Associates.multiplicity source factor }

end Associates

namespace Associates

/-- Every entry produced by associate grouping has positive multiplicity.

The selected representative belongs to the original occurrence list. -/
theorem multiplicityFactor_positive
    {source : List Factor} {entry :
      MultiplicityFactor}
    (member : entry ∈ multiplicityFactors source) :
    0 < entry.multiplicity := open Purelib in by
  rcases Data.List.Map.mem_map.mp member with ⟨factor, representativeMember, equal⟩
  have sourceMember := representative_mem_source source
    representativeMember
  subst entry
  exact multiplicity_positive_of_mem sourceMember

end Associates

/-- Group a decomposition's squarefree occurrences by their monic keys.

Each output retains a representative factor and its exact count in the original decomposition list. -/
def associateFactors {p :
  CoefficientPolynomial}
    (decomposition : Decomposition p) : List
      Dense.Gaussian.Squarefree.Decomposition.Associates.MultiplicityFactor :=
  Dense.Gaussian.Squarefree.Decomposition.Associates.multiplicityFactors decomposition.factors

/-- Every decomposition yields a nonempty list of associate factors. -/
theorem associateFactors_nonempty
    {p : CoefficientPolynomial} (decomposition :
      Decomposition p) :
    decomposition.associateFactors ≠ [] := by
  have representativesNonempty :=
    Dense.Gaussian.Squarefree.Decomposition.Associates.representatives_ne_nil_of_ne_nil decomposition.factorsNonempty
  change Dense.Gaussian.Squarefree.Decomposition.Associates.multiplicityFactors decomposition.factors ≠ []
  unfold Dense.Gaussian.Squarefree.Decomposition.Associates.multiplicityFactors
  cases representativesEquation : Dense.Gaussian.Squarefree.Decomposition.Associates.representatives
    decomposition.factors with
  | nil => exact (representativesNonempty representativesEquation).elim
  | cons factor factors =>
      exact List.cons_ne_nil _ _

end Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition

end
