import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeRing
import RFAP.Winding.Global
import RFAP.Polynomial.Multiplicity
import RFAP.Winding.Product

/-!
# Winding of finite weighted multiplicity products

This module connects the executable multiplicity polynomial from
`ConstructiveMultiplicity` to the finite box product formula.  Powers are
structural recursion over a displayed natural number; no root collection or
factor evaluation over a completed carrier is introduced.
-/

namespace RFAP.MultiplicityWinding

abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev BoundaryClearance := RFAP.BoxClearance.BoundaryClearance
abbrev CoprimeCertificate :=
  RFAP.Squarefree.CoprimeCertificate
abbrev PositiveEntry := RFAP.Multiplicity.PositiveEntry
abbrev Factorization := RFAP.Factorization.ProductIdentity

open RFAP.Winding
open RFAP.ComputablePolynomial.DensePolynomial

/-- A boundary clearance for one factor induces a clearance for every
displayed finite power. -/
def polynomialPower_boundaryClearance
    {p : GaussianPolynomial} {box : Box}
    (clearance : BoundaryClearance p box) :
    ∀ exponent : Nat, BoundaryClearance
      (RFAP.Multiplicity.polynomialPower p exponent) box
  | 0 => by
      exact RFAP.GlobalWinding.gaussianConstant_boundaryClearance
        one_ne_zero box
  | exponent + 1 =>
      RFAP.BoxClearance.BoundaryClearance.mul clearance
        (polynomialPower_boundaryClearance clearance exponent)

/-- Raw winding of a finite polynomial power is the displayed exponent
times the factor winding. -/
theorem quadrupledBoxWinding_polynomialPower
    {p : GaussianPolynomial} {box : Box} (proper : box.Proper)
    (clearance : BoundaryClearance p box) (exponent : Nat) :
    quadrupledBoxWinding
        (RFAP.Multiplicity.polynomialPower p exponent) box =
      (exponent : Int) * quadrupledBoxWinding p box := by
  induction exponent with
  | zero =>
      simp only [RFAP.Multiplicity.polynomialPower, Nat.cast_zero,
        zero_mul]
      exact RFAP.GlobalWinding.quadrupledBoxWinding_gaussianConstant
        one_ne_zero box
  | succ exponent inductionHypothesis =>
      have product :=
        RFAP.WindingProduct.quadrupledBoxWinding_mul_of_boundaryClearances
          p (RFAP.Multiplicity.polynomialPower p exponent) box
          proper clearance (polynomialPower_boundaryClearance clearance exponent)
      rw [RFAP.Multiplicity.polynomialPower, product,
        inductionHypothesis]
      rw [Nat.cast_succ]
      ring1

/-- Coprimality with one right factor extends to every displayed finite
power of that factor. -/
def polynomialPowerRightCoprime
    {p q : GaussianPolynomial} (pNonzero : p.isZero = false)
    (coprime : CoprimeCertificate p q) : ∀ exponent : Nat,
    CoprimeCertificate p
      (RFAP.Multiplicity.polynomialPower q exponent)
  | 0 =>
      RFAP.SquarefreeFactors.CoprimeCertificate.constantRight
        pNonzero
  | exponent + 1 =>
      RFAP.SquarefreeFactors.CoprimeCertificate.mulRight pNonzero
        coprime (polynomialPowerRightCoprime pNonzero coprime exponent)

/-! ## One focused entry of a weighted multiplicity list -/

/-- A displayed split of a finite positive multiplicity list around one
focused factor. -/
structure PositiveContext (entries : List PositiveEntry) where
  before : List PositiveEntry
  focus : PositiveEntry
  after : List PositiveEntry
  split : entries = before ++ focus :: after

def PositiveContext.lift
    (head : PositiveEntry) {entries : List PositiveEntry}
    (context : PositiveContext entries) :
    PositiveContext (head :: entries) where
  before := head :: context.before
  focus := context.focus
  after := context.after
  split := by
    calc
      head :: entries =
          head :: (context.before ++ context.focus :: context.after) :=
        congrArg (head :: ·) context.split
      _ = (head :: context.before) ++ context.focus :: context.after := rfl

/-- Enumerate every focused position by structural recursion on the finite
entry list. -/
def positiveContexts : (entries : List PositiveEntry) →
    List (PositiveContext entries)
  | [] => []
  | head :: entries =>
      { before := []
        focus := head
        after := entries
        split := rfl } ::
      (positiveContexts entries).map (PositiveContext.lift head)

theorem positiveContexts_length : ∀ entries : List PositiveEntry,
    (positiveContexts entries).length = entries.length
  | [] => rfl
  | head :: entries => by
      simp only [positiveContexts, List.length_cons, List.length_map,
        positiveContexts_length entries]

theorem PositiveContext.focus_mem
    {entries : List PositiveEntry} (context : PositiveContext entries) :
    context.focus ∈ entries := by
  have member : context.focus ∈
      context.before ++ context.focus :: context.after :=
    List.mem_append_right _ List.mem_cons_self
  exact (congrArg (fun values : List PositiveEntry =>
    context.focus ∈ values) context.split).symm.mp member

/-- Enumerating every focused position preserves the pairwise-coprime
relation carried by the source list. -/
theorem positiveContexts_pairwise : ∀ {entries : List PositiveEntry},
    (entries.Pairwise fun left right =>
      RFAP.Multiplicity.CoprimeRelation left.part right.part) →
    (positiveContexts entries).Pairwise fun left right =>
      RFAP.Multiplicity.CoprimeRelation
        left.focus.part right.focus.part
  | [], _ => List.Pairwise.nil
  | head :: entries, pairwise => by
      have source := List.pairwise_cons.mp pairwise
      rw [positiveContexts]
      apply List.pairwise_cons.mpr
      constructor
      · intro context member
        rw [QuotientFreeList.mem_map] at member
        rcases member with ⟨tailContext, tailMember, rfl⟩
        exact source.1 tailContext.focus tailContext.focus_mem
      · rw [QuotientFreeList.pairwise_map]
        simpa only [PositiveContext.lift] using
          positiveContexts_pairwise source.2

theorem positivePolynomial_append_eval
    (left right : List PositiveEntry)
    (point : RFAP.ConstructiveGaussian.Gaussian) :
    (RFAP.Multiplicity.positivePolynomial (left ++ right)).eval
        point =
      (RFAP.Multiplicity.positivePolynomial left).eval point *
        (RFAP.Multiplicity.positivePolynomial right).eval point := by
  induction left with
  | nil =>
      simp only [List.nil_append,
        RFAP.Multiplicity.positivePolynomial, eval_constant,
        one_mul]
  | cons entry entries inductionHypothesis =>
      simp only [List.cons_append,
        RFAP.Multiplicity.positivePolynomial, eval_mul,
        inductionHypothesis]
      ring1

namespace PositiveContext

theorem focus_coprime_other
    {entries : List PositiveEntry} (context : PositiveContext entries)
    (pairwise : entries.Pairwise fun left right =>
      RFAP.Multiplicity.CoprimeRelation left.part right.part)
    {other : PositiveEntry}
    (member : other ∈ context.before ++ context.after) :
    RFAP.Multiplicity.CoprimeRelation
      context.focus.part other.part := by
  have pairwiseSplit :
      (context.before ++ context.focus :: context.after).Pairwise
        (fun left right =>
          RFAP.Multiplicity.CoprimeRelation left.part right.part) :=
    (congrArg (fun values : List PositiveEntry =>
      values.Pairwise (fun left right =>
        RFAP.Multiplicity.CoprimeRelation left.part right.part))
      context.split).mp pairwise
  have reordered :
      (context.focus :: context.before ++ context.after).Pairwise
        (fun left right =>
          RFAP.Multiplicity.CoprimeRelation left.part right.part) :=
    (QuotientFreeList.pairwise_middle
      (R := fun left right : PositiveEntry =>
        RFAP.Multiplicity.CoprimeRelation left.part right.part)
      (fun {_ _} relation =>
        RFAP.Multiplicity.coprimeRelation_symm relation)).mp
          pairwiseSplit
  exact (List.pairwise_cons.mp reordered).1 other member

/-- A focused factor is coprime to the weighted polynomial of a list whose
every entry carries the displayed pairwise relation. -/
def coprimePositivePolynomial
    (focus : PositiveEntry) :
    (others : List PositiveEntry) →
    (∀ other ∈ others,
      RFAP.Multiplicity.CoprimeRelation
        focus.part other.part) →
    CoprimeCertificate focus.part.polynomial
      (RFAP.Multiplicity.positivePolynomial others)
  | [], _ =>
      RFAP.SquarefreeFactors.CoprimeCertificate.constantRight
        focus.part.nonzero
  | other :: others, relations => by
      let factorCoprime :=
        RFAP.Multiplicity.coprimeCertificateOfRelation
          focus.part other.part (relations other List.mem_cons_self)
      let powerCoprime := polynomialPowerRightCoprime focus.part.nonzero
        factorCoprime other.multiplicity
      let restCoprime := coprimePositivePolynomial focus others
        (fun entry member => relations entry
          (List.mem_cons_of_mem other member))
      exact
        RFAP.SquarefreeFactors.CoprimeCertificate.mulRight
          focus.part.nonzero powerCoprime restCoprime

/-- The polynomial containing every positive factor except the focused
factor, together with the nonzero unit omitted by positive preprocessing. -/
def otherPolynomial
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p)
    {entries : List PositiveEntry} (context : PositiveContext entries) :
    GaussianPolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial.constant
      (RFAP.Multiplicity.unitValue
        decomposition.multiplicityBasis.entries) *
    (RFAP.Multiplicity.positivePolynomial context.before *
      RFAP.Multiplicity.positivePolynomial context.after)

theorem otherPolynomial_nonzero
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p)
    {entries : List PositiveEntry} (context : PositiveContext entries) :
    (context.otherPolynomial decomposition).isZero = false := by
  apply isZero_mul_eq_false
  · exact (RFAP.ConstructivePolynomialLeading.LeadingTerm.constant
      decomposition.multiplicityUnit_ne_zero).nonzero
  · exact isZero_mul_eq_false
      (RFAP.Multiplicity.positivePolynomial_nonzero context.before)
      (RFAP.Multiplicity.positivePolynomial_nonzero context.after)

/-- Pairwise coprimality of the multiplicity basis supplies one finite
Bézout certificate between the focused factor and the product of every
other positive entry, including the omitted nonzero unit. -/
def otherCoprime
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p)
    {entries : List PositiveEntry} (context : PositiveContext entries)
    (pairwise : entries.Pairwise fun left right =>
      RFAP.Multiplicity.CoprimeRelation left.part right.part) :
    CoprimeCertificate context.focus.part.polynomial
      (context.otherPolynomial decomposition) := by
  let unitCoprime :=
    RFAP.SquarefreeFactors.CoprimeCertificate.constantRightOfNe
      context.focus.part.nonzero
      (RFAP.Multiplicity.unitValue
        decomposition.multiplicityBasis.entries)
      decomposition.multiplicityUnit_ne_zero
  let splitCoprime :=
    RFAP.SquarefreeFactors.CoprimeCertificate.mulRight
      context.focus.part.nonzero
      (coprimePositivePolynomial context.focus context.before
        (fun other member => context.focus_coprime_other pairwise
          (List.mem_append_left context.after member)))
      (coprimePositivePolynomial context.focus context.after
        (fun other member => context.focus_coprime_other pairwise
          (List.mem_append_right context.before member)))
  exact RFAP.SquarefreeFactors.CoprimeCertificate.mulRight
    context.focus.part.nonzero unitCoprime splitCoprime

/-- Cofactor after removing one copy, rather than the complete
multiplicity, of the focused factor. -/
def singleCofactor
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p)
    {entries : List PositiveEntry} (context : PositiveContext entries) :
    GaussianPolynomial :=
  RFAP.Multiplicity.polynomialPower
      context.focus.part.polynomial (context.focus.multiplicity - 1) *
    context.otherPolynomial decomposition

/-- The normalized source has the focused squarefree factor as an exact
finite coefficient divisor. -/
theorem focusFactorization
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p)
    (entriesEq : entries = decomposition.positiveMultiplicityEntries)
    (context : PositiveContext entries) :
    Factorization p context.focus.part.polynomial
      (context.singleCofactor decomposition) := by
  apply RFAP.Factorization.factorizationOfCandidateEvals
  intro point _
  have exponentIdentity :
      context.focus.multiplicity - 1 + 1 = context.focus.multiplicity :=
    Nat.sub_add_cancel context.focus.multiplicityPositive
  have powerIdentity :
      context.focus.part.polynomial.eval point ^ context.focus.multiplicity =
        context.focus.part.polynomial.eval point *
          context.focus.part.polynomial.eval point ^
            (context.focus.multiplicity - 1) := by
    rw [← exponentIdentity, pow_succ]
    exact RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
  rw [decomposition.eval_positivePolynomial point]
  have listSplit : decomposition.positiveMultiplicityEntries =
      context.before ++ context.focus :: context.after := by
    rw [← entriesEq]
    exact context.split
  rw [listSplit, positivePolynomial_append_eval]
  simp only [RFAP.Multiplicity.positivePolynomial,
    RFAP.Multiplicity.eval_polynomialPower, eval_mul,
    eval_constant, singleCofactor, otherPolynomial]
  rw [powerIdentity]
  ring1

/-- The same normalized source factors as the full displayed multiplicity
power times the polynomial of all other positive entries. -/
theorem multiplicityFactorization
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p)
    (entriesEq : entries = decomposition.positiveMultiplicityEntries)
    (context : PositiveContext entries) :
    Factorization p
      (RFAP.Multiplicity.polynomialPower
        context.focus.part.polynomial context.focus.multiplicity)
      (context.otherPolynomial decomposition) := by
  apply RFAP.Factorization.factorizationOfCandidateEvals
  intro point _
  rw [decomposition.eval_positivePolynomial point]
  have listSplit : decomposition.positiveMultiplicityEntries =
      context.before ++ context.focus :: context.after := by
    rw [← entriesEq]
    exact context.split
  rw [listSplit, positivePolynomial_append_eval]
  simp only [RFAP.Multiplicity.positivePolynomial,
    RFAP.Multiplicity.eval_polynomialPower, eval_mul,
    eval_constant, otherPolynomial]
  ring1

end PositiveContext

end RFAP.MultiplicityWinding
