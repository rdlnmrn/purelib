import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.RFAP.ConstructiveFiniteRoots
import RFAP.Polynomial.Squarefree

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

namespace RFAP.Factorization

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev SquarefreeCertificate :=
  RFAP.Squarefree.SquarefreeCertificate

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.ConstructivePolynomialLeading

/-- Exact finite coefficient factorization, represented by the decidable zero
test of the normalized coefficient difference. -/
abbrev ProductIdentity (p left right : GaussianPolynomial) : Prop :=
  (p - left * right).isZero = true

/-- A pointwise identity produced by a finite algorithm need only be queried
on the bounded candidate list to certify its coefficient factorization. -/
theorem factorizationOfCandidateEvals
    (p left right : GaussianPolynomial)
    (identity : ∀ point ∈
      RFAP.ConstructiveFiniteRoots.candidates (p - left * right),
      p.eval point = left.eval point * right.eval point) :
    ProductIdentity p left right := by
  apply RFAP.ConstructiveFiniteRoots.difference_isZero_of_candidate_evals
  intro point member
  rw [eval_mul]
  exact identity point member

/-- A nonzero normalized product target and nonzero left factor force the
displayed right factor to be nonzero. -/
theorem right_isZero_false
    {p left right : GaussianPolynomial}
    (pNonzero : p.isZero = false) (pNormalized : p.normalize = p)
    (factorization : ProductIdentity p left right) :
    right.isZero = false := by
  by_cases rightZero : right.isZero = true
  · have productZero : left * right = (0 : GaussianPolynomial) :=
      mul_eq_zero_of_isZero_right rightZero
    change (p - left * right).isZero = true at factorization
    rw [productZero] at factorization
    have targetZero : p.isZero = true := by
      change (p + -(0 : GaussianPolynomial)).isZero = true at factorization
      have negZero : -(0 : GaussianPolynomial) = 0 := rfl
      rw [negZero, add_zero_normalize, pNormalized] at factorization
      exact factorization
    rw [pNonzero] at targetZero
    exact Bool.noConfusion targetZero
  · simpa using rightZero

/-- Exact degree balance for a finite nonzero factorization. -/
theorem factor_natDegree_add
    {p left right : GaussianPolynomial}
    (pNonzero : p.isZero = false) (pNormalized : p.normalize = p)
    (leftNonzero : left.isZero = false) (rightNonzero : right.isZero = false)
    (factorization : ProductIdentity p left right) :
    left.natDegree + right.natDegree = p.natDegree := by
  have productNonzero := isZero_mul_eq_false leftNonzero rightNonzero
  have degree := LeadingTerm.natDegree_eq_of_sub_isZero pNonzero
    productNonzero pNormalized (normalize_mul left right) factorization
  rw [natDegree_mul leftNonzero rightNonzero] at degree
  exact degree.symm

/-- One positive-degree squarefree occurrence returned by preprocessing. -/
structure Factor where
  polynomial : GaussianPolynomial
  normalized : polynomial.normalize = polynomial
  nonzero : polynomial.isZero = false
  degreePositive : 0 < polynomial.natDegree
  squarefree : SquarefreeCertificate polynomial

/-- Finite product of the displayed squarefree occurrences. -/
def factorProduct : List Factor → GaussianPolynomial
  | [] => constant 1
  | factor :: factors => factor.polynomial * factorProduct factors

theorem factorProduct_append_eval (left right : List Factor) (point : Gaussian) :
    (factorProduct (left ++ right)).eval point =
      (factorProduct left).eval point * (factorProduct right).eval point := by
  induction left with
  | nil => simp only [List.nil_append, factorProduct, eval_constant, one_mul]
  | cons factor factors inductionHypothesis =>
      simp only [List.cons_append, factorProduct, eval_mul,
        inductionHypothesis]
      rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]

/-- A complete squarefree occurrence decomposition of a normalized positive-
degree polynomial. -/
structure Decomposition (p : GaussianPolynomial) where
  factors : List Factor
  factorsNonempty : factors ≠ []
  evalIdentity : ∀ point : Gaussian,
    p.eval point = (factorProduct factors).eval point
  degreeSum : (factors.map fun factor => factor.polynomial.natDegree).sum =
    p.natDegree

/-- Degree-recursive decomposition by the computed gcd with the derivative. -/
def decomposeNormalized
    (p : GaussianPolynomial) (pNormalized : p.normalize = p)
    (pNonzero : p.isZero = false) (pPositive : 0 < p.natDegree) :
    Decomposition p := by
  match outcome : RFAP.Squarefree.squarefreeOutcome p pNonzero with
  | .coprime certificate =>
      exact
        { factors :=
            [{ polynomial := p
               normalized := pNormalized
               nonzero := pNonzero
               degreePositive := pPositive
               squarefree := certificate }]
          factorsNonempty := by simp
          evalIdentity := by
            intro point
            simp only [factorProduct, eval_mul, eval_constant, mul_one]
          degreeSum := by simp }
  | .commonDivisor common =>
      let divisor := common.divisor
      let cofactor := common.leftFactor
      have derivativeNonzero :
          (RFAP.ConstructiveGCD.derivative p).isZero = false :=
        RFAP.ConstructiveDerivativeDegree.derivative_isZero_false pNonzero
          pPositive
      have derivativeDegree :
          (RFAP.ConstructiveGCD.derivative p).natDegree < p.natDegree := by
        exact RFAP.ComputableDerivative.derivative_natDegree_lt pNonzero pPositive
      have divisorProper : divisor.natDegree < p.natDegree :=
        (common.result.degreeLeRight derivativeNonzero).trans_lt derivativeDegree
      have factorization : ProductIdentity p divisor cofactor := by
        apply factorizationOfCandidateEvals
        intro point _
        exact common.leftIdentity point
      have cofactorNonzero : cofactor.isZero = false :=
        right_isZero_false pNonzero pNormalized factorization
      have degreeBalance :
          divisor.natDegree + cofactor.natDegree = p.natDegree :=
        factor_natDegree_add pNonzero pNormalized common.nonzero
          cofactorNonzero factorization
      have divisorPositive : 0 < divisor.natDegree := by
        exact common.positiveDegree
      have cofactorPositive : 0 < cofactor.natDegree := by
        apply Nat.pos_of_ne_zero
        intro cofactorZero
        rw [cofactorZero, Nat.add_zero] at degreeBalance
        exact (Nat.ne_of_lt divisorProper) degreeBalance
      have cofactorProper : cofactor.natDegree < p.natDegree := by
        calc
          cofactor.natDegree < divisor.natDegree + cofactor.natDegree :=
            Nat.lt_add_of_pos_left divisorPositive
          _ = p.natDegree := degreeBalance
      let leftDecomposition := decomposeNormalized divisor
        common.result.normalized common.nonzero common.positiveDegree
      let rightDecomposition := decomposeNormalized cofactor
        common.result.pFactorNormalized cofactorNonzero cofactorPositive
      exact
        { factors := leftDecomposition.factors ++ rightDecomposition.factors
          factorsNonempty := by
            cases factorsEquation : leftDecomposition.factors with
            | nil => exact
                (leftDecomposition.factorsNonempty factorsEquation).elim
            | cons factor factors => simp
          evalIdentity := by
            intro point
            calc
              p.eval point = divisor.eval point * cofactor.eval point :=
                common.leftIdentity point
              _ = (factorProduct leftDecomposition.factors).eval point *
                    (factorProduct rightDecomposition.factors).eval point := by
                  rw [← leftDecomposition.evalIdentity,
                    ← rightDecomposition.evalIdentity]
              _ = (factorProduct
                    (leftDecomposition.factors ++
                      rightDecomposition.factors)).eval point :=
                (factorProduct_append_eval _ _ point).symm
          degreeSum := by
            simp only [List.map_append, List.sum_append,
              leftDecomposition.degreeSum, rightDecomposition.degreeSum]
            exact degreeBalance }
termination_by p.natDegree
decreasing_by
  · exact divisorProper
  · exact cofactorProper

/-- Positive-degree branch of total general-polynomial preprocessing. -/
structure PositivePreprocessing (p : GaussianPolynomial) where
  nonzero : p.isZero = false
  degreePositive : 0 < p.natDegree
  decomposition : Decomposition p.normalize

/-- Total finite preprocessing distinguishes zero, a nonzero constant, and a
positive-degree polynomial with its complete squarefree occurrence
decomposition. -/
inductive Preprocessing (p : GaussianPolynomial) where
  | zero (certificate : p.isZero = true)
  | constant (nonzero : p.isZero = false) (degreeZero : p.natDegree = 0)
  | positive (result : PositivePreprocessing p)

def preprocess (p : GaussianPolynomial) : Preprocessing p := by
  if zero : p.isZero = true then
    exact .zero zero
  else
    have nonzero : p.isZero = false := by simpa using zero
    if degreeZero : p.natDegree = 0 then
      exact .constant nonzero degreeZero
    else
      have degreePositive : 0 < p.natDegree := Nat.pos_of_ne_zero degreeZero
      exact .positive
        { nonzero := nonzero
          degreePositive := degreePositive
          decomposition := decomposeNormalized p.normalize
            (normalize_normalize p) (by simpa only [isZero_normalize])
              (by simpa only [natDegree_normalize]) }

/-! ## Associate grouping and multiplicities -/

/-- Canonical monic key of a nonzero squarefree occurrence.  It is used only
for finite comparison; the original factor and its certificate remain the
paper-facing isolation input. -/
def Factor.monicKey (factor : Factor) : GaussianPolynomial :=
  scale factor.polynomial.leadingCoeff⁻¹ factor.polynomial

theorem Factor.monicKey_eval (factor : Factor) (point : Gaussian) :
    factor.monicKey.eval point =
      factor.polynomial.leadingCoeff⁻¹ * factor.polynomial.eval point := by
  exact eval_scale _ _ _

private theorem eval_eq_zero_of_monicKey_eq
    {left right : Factor} (same : left.monicKey = right.monicKey)
    {point : Gaussian} (leftZero : left.polynomial.eval point = 0) :
    right.polynomial.eval point = 0 := by
  have keyValues := congrArg (fun polynomial : GaussianPolynomial =>
    polynomial.eval point) same
  rw [left.monicKey_eval, right.monicKey_eval, leftZero, mul_zero] at keyValues
  have inverseNonzero : right.polynomial.leadingCoeff⁻¹ ≠ 0 :=
    RFAP.ExplicitField.inv_ne_zero (leadingCoeff_ne_zero right.nonzero)
  by_cases rightZero : right.polynomial.eval point = 0
  · exact rightZero
  · have productNonzero :=
      RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct inverseNonzero
        rightZero
    exact (productNonzero keyValues.symm).elim

/-- Equal monic keys are an exact finite certificate that two associate
squarefree occurrences have the same Gaussian-rational zeros. -/
theorem Factor.eval_eq_zero_iff_of_monicKey_eq
    {left right : Factor} (same : left.monicKey = right.monicKey)
    (point : Gaussian) :
    left.polynomial.eval point = 0 ↔ right.polynomial.eval point = 0 := by
  constructor
  · exact eval_eq_zero_of_monicKey_eq same
  · exact eval_eq_zero_of_monicKey_eq same.symm

/-- Insert one factor only when no existing representative has its monic key. -/
def insertRepresentative (factor : Factor) : List Factor → List Factor
  | [] => [factor]
  | representative :: representatives =>
      if factor.monicKey = representative.monicKey then
        representative :: representatives
      else
        representative :: insertRepresentative factor representatives

/-- Existing representatives are never removed by insertion. -/
theorem mem_insertRepresentative_of_mem
    (factor : Factor) : ∀ {representatives : List Factor}
    {representative : Factor}, representative ∈ representatives →
    representative ∈ insertRepresentative factor representatives
  | [], _, member => by simp at member
  | head :: tail, representative, member => by
      rw [insertRepresentative]
      split
      · exact member
      · rcases List.mem_cons.mp member with rfl | member
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem head
            (mem_insertRepresentative_of_mem factor member)

/-- Every inserted representative came from the old list or is the new
factor. -/
theorem mem_of_mem_insertRepresentative
    (factor : Factor) : ∀ {representatives : List Factor}
    {representative : Factor},
    representative ∈ insertRepresentative factor representatives →
    representative = factor ∨ representative ∈ representatives
  | [], representative, member => by
      simp only [insertRepresentative, List.mem_singleton] at member
      exact Or.inl member
  | head :: tail, representative, member => by
      rw [insertRepresentative] at member
      split at member
      · exact Or.inr member
      · rcases List.mem_cons.mp member with rfl | member
        · exact Or.inr List.mem_cons_self
        · rcases mem_of_mem_insertRepresentative factor member with
            rfl | oldMember
          · exact Or.inl rfl
          · exact Or.inr (List.mem_cons_of_mem head oldMember)

/-- The inserted factor has an associate representative in the result. -/
theorem inserted_has_representative
    (factor : Factor) (representatives : List Factor) :
    ∃ representative ∈ insertRepresentative factor representatives,
      factor.monicKey = representative.monicKey := by
  induction representatives with
  | nil => exact ⟨factor, List.mem_cons_self, rfl⟩
  | cons representative representatives inductionHypothesis =>
      change ∃ found ∈
          (if factor.monicKey = representative.monicKey then
            representative :: representatives
          else
            representative :: insertRepresentative factor representatives),
        factor.monicKey = found.monicKey
      by_cases same : factor.monicKey = representative.monicKey
      · rw [if_pos same]
        exact ⟨representative, List.mem_cons_self, same⟩
      · rw [if_neg same]
        rcases inductionHypothesis with
          ⟨found, member, same⟩
        exact ⟨found, List.mem_cons_of_mem representative member, same⟩

/-- Select one representative of each monic associate class by a structural
fold over the finite occurrence list. -/
def representatives : List Factor → List Factor
  | [] => []
  | factor :: factors =>
      insertRepresentative factor (representatives factors)

theorem representative_mem_source : ∀ (source : List Factor)
    {representative : Factor},
    representative ∈ representatives source → representative ∈ source
  | [], _, member => by
      change _ ∈ [] at member
      exact (List.not_mem_nil member).elim
  | factor :: factors, representative, member => by
      rcases mem_of_mem_insertRepresentative factor member with
        rfl | tailMember
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem factor
          (representative_mem_source factors tailMember)

/-- Every squarefree occurrence is represented by an associate in the finite
distinct list. -/
theorem source_has_representative : ∀ (source : List Factor)
    {occurrence : Factor}, occurrence ∈ source →
    ∃ representative ∈ representatives source,
      occurrence.monicKey = representative.monicKey
  | [], _, member => by simp at member
  | factor :: factors, occurrence, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact inserted_has_representative occurrence (representatives factors)
      · rcases source_has_representative factors member with
          ⟨representative, representativeMember, same⟩
        exact ⟨representative,
          mem_insertRepresentative_of_mem factor representativeMember, same⟩

private theorem insertRepresentative_pairwise
    (factor : Factor) : ∀ {source : List Factor},
    source.Pairwise (fun left right => left.monicKey ≠ right.monicKey) →
    (insertRepresentative factor source).Pairwise
      (fun left right => left.monicKey ≠ right.monicKey)
  | [], _ => QuotientFreeList.pairwise_singleton _ _
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
        · exact insertRepresentative_pairwise factor
            (List.pairwise_cons.mp pairwise).2

/-- The selected representatives have pairwise different monic keys. -/
theorem representatives_pairwise : ∀ source : List Factor,
    (representatives source).Pairwise
      (fun left right => left.monicKey ≠ right.monicKey)
  | [] => List.Pairwise.nil
  | factor :: factors =>
      insertRepresentative_pairwise factor
        (representatives_pairwise factors)

theorem insertRepresentative_ne_nil
    (factor : Factor) : ∀ representatives : List Factor,
    insertRepresentative factor representatives ≠ []
  | [] => by simp [insertRepresentative]
  | representative :: representatives => by
      rw [insertRepresentative]
      split
      · exact List.cons_ne_nil representative representatives
      · exact List.cons_ne_nil representative
          (insertRepresentative factor representatives)

theorem representatives_ne_nil_of_ne_nil
    {source : List Factor} (nonempty : source ≠ []) :
    representatives source ≠ [] := by
  cases source with
  | nil => exact (nonempty rfl).elim
  | cons factor factors =>
      exact insertRepresentative_ne_nil factor (representatives factors)

/-- Number of squarefree occurrences associate to the displayed factor. -/
def multiplicity (source : List Factor) (factor : Factor) : Nat :=
  (source.filter fun occurrence =>
    decide (occurrence.monicKey = factor.monicKey)).length

theorem multiplicity_positive_of_mem
    {source : List Factor} {factor : Factor} (member : factor ∈ source) :
    0 < multiplicity source factor := by
  have filteredMember : factor ∈ source.filter fun occurrence =>
      decide (occurrence.monicKey = factor.monicKey) :=
    List.mem_filter.mpr ⟨member, by simp⟩
  unfold multiplicity
  cases filteredEquation : source.filter (fun occurrence =>
      decide (occurrence.monicKey = factor.monicKey)) with
  | nil =>
      rw [filteredEquation] at filteredMember
      exact (List.not_mem_nil filteredMember).elim
  | cons occurrence occurrences =>
      exact Nat.zero_lt_succ _

/-- One distinct squarefree factor together with its exact occurrence count. -/
structure MultiplicityFactor where
  factor : Factor
  multiplicity : Nat

def multiplicityFactors (source : List Factor) : List MultiplicityFactor :=
  (representatives source).map fun factor =>
    { factor := factor
      multiplicity := multiplicity source factor }

theorem multiplicityFactor_positive
    {source : List Factor} {entry : MultiplicityFactor}
    (member : entry ∈ multiplicityFactors source) :
    0 < entry.multiplicity := by
  rcases QuotientFreeList.mem_map.mp member with ⟨factor, representativeMember, equal⟩
  have sourceMember := representative_mem_source source representativeMember
  subst entry
  exact multiplicity_positive_of_mem sourceMember

def Decomposition.associateFactors {p : GaussianPolynomial}
    (decomposition : Decomposition p) : List MultiplicityFactor :=
  multiplicityFactors decomposition.factors

theorem Decomposition.associateFactors_nonempty
    {p : GaussianPolynomial} (decomposition : Decomposition p) :
    decomposition.associateFactors ≠ [] := by
  have representativesNonempty :=
    representatives_ne_nil_of_ne_nil decomposition.factorsNonempty
  change multiplicityFactors decomposition.factors ≠ []
  unfold multiplicityFactors
  cases representativesEquation : representatives decomposition.factors with
  | nil => exact (representativesNonempty representativesEquation).elim
  | cons factor factors =>
      exact List.cons_ne_nil _ _

end RFAP.Factorization
