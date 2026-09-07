import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.SquarefreeFactors

/-!
# Finite multiplicity basis for general polynomials

The recursive derivative-gcd preprocessing returns squarefree occurrences.
Different composite occurrences may overlap.  This module refines such
overlaps by finite pairwise gcd computations.  Every split retains explicit
squarefree and coprimality certificates, so later isolation can run once per
distinct positive-degree basis factor and attach its exact occurrence count.
-/

namespace RFAP.Multiplicity

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Factor := RFAP.Factorization.Factor
abbrev Factorization := RFAP.Factorization.ProductIdentity
abbrev CoprimeCertificate :=
  RFAP.Squarefree.CoprimeCertificate
abbrev SquarefreeCertificate :=
  RFAP.Squarefree.SquarefreeCertificate

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.ConstructivePolynomialLeading

/-- A nonzero normalized squarefree polynomial, which may be constant. -/
structure Part where
  polynomial : GaussianPolynomial
  normalized : polynomial.normalize = polynomial
  nonzero : polynomial.isZero = false
  squarefree : SquarefreeCertificate polynomial

def Factor.toPart (factor : Factor) : Part :=
  { polynomial := factor.polynomial
    normalized := factor.normalized
    nonzero := factor.nonzero
    squarefree := factor.squarefree }

def Part.toFactor (part : Part) (degreePositive : 0 < part.polynomial.natDegree) :
    Factor :=
  { polynomial := part.polynomial
    normalized := part.normalized
    nonzero := part.nonzero
    degreePositive := degreePositive
    squarefree := part.squarefree }

/-- The finite Euclidean gcd has degree zero.  Both polynomials are supplied
as nonzero factors, so this proposition can always be converted back into
the full finite coprimality data. -/
def CoprimeRelation (left right : Part) : Prop :=
  (RFAP.ConstructiveGCD.extendedGCD left.polynomial right.polynomial).gcd.natDegree =
    0

def coprimeCertificateOfRelation
    (left right : Part) (coprime : CoprimeRelation left right) :
    CoprimeCertificate left.polynomial right.polynomial :=
  RFAP.Squarefree.certificateOfConstantGCD
    left.polynomial right.polynomial
      ((RFAP.ConstructiveGCD.extendedGCD left.polynomial right.polynomial).nonzero
        (Or.inl left.nonzero)) coprime

theorem coprimeRelationOfCertificate
    {left right : Part}
    (coprime : CoprimeCertificate left.polynomial right.polynomial) :
    CoprimeRelation left right := by
  unfold CoprimeRelation
  rw [coprime.gcd_eq_constant]
  exact (LeadingTerm.constant coprime.unit_ne_zero).degree_eq

theorem coprimeRelation_symm
    {left right : Part} (coprime : CoprimeRelation left right) :
    CoprimeRelation right left :=
  coprimeRelationOfCertificate
    (RFAP.SquarefreeFactors.CoprimeCertificate.symm
      (coprimeCertificateOfRelation left right coprime))

/-- One nonconstant gcd split of two squarefree factors.  The common factor,
both residual factors, and all three relevant coprimality certificates are
kept explicitly. -/
structure CommonSplit (left right : Factor) where
  common : Factor
  leftRemainder : Part
  rightRemainder : Part
  leftFactorization :
    Factorization left.polynomial common.polynomial leftRemainder.polynomial
  rightFactorization :
    Factorization right.polynomial common.polynomial rightRemainder.polynomial
  commonLeftCoprime :
    CoprimeCertificate common.polynomial leftRemainder.polynomial
  commonRightCoprime :
    CoprimeCertificate common.polynomial rightRemainder.polynomial
  remaindersCoprime :
    CoprimeCertificate leftRemainder.polynomial rightRemainder.polynomial
  leftDegreeSum :
    common.polynomial.natDegree + leftRemainder.polynomial.natDegree =
      left.polynomial.natDegree
  rightDegreeSum :
    common.polynomial.natDegree + rightRemainder.polynomial.natDegree =
      right.polynomial.natDegree

/-- Turn the displayed nonconstant gcd of two squarefree factors into the
fully certified three-way split. -/
def commonSplit
    (left right : Factor)
    (common : RFAP.Squarefree.NonconstantCommonDivisor
      left.polynomial right.polynomial) :
    CommonSplit left right := by
  let divisor := common.divisor
  let leftRemainder := common.leftFactor
  let rightRemainder := common.rightFactor
  have leftFactorization :
      Factorization left.polynomial divisor leftRemainder := by
    apply RFAP.Factorization.factorizationOfCandidateEvals
    intro point _
    exact common.leftIdentity point
  have rightFactorization :
      Factorization right.polynomial divisor rightRemainder := by
    apply RFAP.Factorization.factorizationOfCandidateEvals
    intro point _
    exact common.rightIdentity point
  have leftRemainderNonzero : leftRemainder.isZero = false :=
    RFAP.Factorization.right_isZero_false
      left.nonzero left.normalized leftFactorization
  have rightRemainderNonzero : rightRemainder.isZero = false :=
    RFAP.Factorization.right_isZero_false
      right.nonzero right.normalized rightFactorization
  have divisorSquarefree : SquarefreeCertificate divisor :=
    RFAP.SquarefreeFactors.leftFactorSquarefree
      left.squarefree common.nonzero leftFactorization
  have leftRemainderSquarefree : SquarefreeCertificate leftRemainder :=
    RFAP.SquarefreeFactors.rightFactorSquarefree
      left.squarefree leftRemainderNonzero leftFactorization
  have rightRemainderSquarefree : SquarefreeCertificate rightRemainder :=
    RFAP.SquarefreeFactors.rightFactorSquarefree
      right.squarefree rightRemainderNonzero rightFactorization
  let commonFactor : Factor :=
    { polynomial := divisor
      normalized := common.result.normalized
      nonzero := common.nonzero
      degreePositive := common.positiveDegree
      squarefree := divisorSquarefree }
  let leftPart : Part :=
    { polynomial := leftRemainder
      normalized := common.result.pFactorNormalized
      nonzero := leftRemainderNonzero
      squarefree := leftRemainderSquarefree }
  let rightPart : Part :=
    { polynomial := rightRemainder
      normalized := common.result.qFactorNormalized
      nonzero := rightRemainderNonzero
      squarefree := rightRemainderSquarefree }
  have commonLeftCoprime :
      CoprimeCertificate divisor leftRemainder :=
    RFAP.SquarefreeFactors.factorsCoprime
      left.squarefree common.nonzero leftFactorization
  have commonRightCoprime :
      CoprimeCertificate divisor rightRemainder :=
    RFAP.SquarefreeFactors.factorsCoprime
      right.squarefree common.nonzero rightFactorization
  have remaindersCoprime :
      CoprimeCertificate leftRemainder rightRemainder :=
    RFAP.SquarefreeFactors.coprimeCertificateOfIdentity
      leftRemainder rightRemainder (Or.inl leftRemainderNonzero)
        common.result.factorLeft common.result.factorRight
          common.result.factorIdentity
  exact
    { common := commonFactor
      leftRemainder := leftPart
      rightRemainder := rightPart
      leftFactorization := leftFactorization
      rightFactorization := rightFactorization
      commonLeftCoprime := commonLeftCoprime
      commonRightCoprime := commonRightCoprime
      remaindersCoprime := remaindersCoprime
      leftDegreeSum :=
        RFAP.Factorization.factor_natDegree_add
          left.nonzero left.normalized common.nonzero leftRemainderNonzero
            leftFactorization
      rightDegreeSum :=
        RFAP.Factorization.factor_natDegree_add
          right.nonzero right.normalized common.nonzero rightRemainderNonzero
            rightFactorization }

/-- A nonzero displayed left divisor inherits the factor-level coprimality
relation with the other factor. -/
theorem coprimeRelation_leftFactor
    {parent other child : Part} {cofactor : GaussianPolynomial}
    (coprime : CoprimeRelation parent other)
    (factorization : Factorization parent.polynomial
      child.polynomial cofactor) :
    CoprimeRelation child other :=
  coprimeRelationOfCertificate
    (RFAP.SquarefreeFactors.coprimeLeftFactor
      (coprimeCertificateOfRelation parent other coprime)
        child.nonzero factorization)

/-- A nonzero displayed right divisor inherits the factor-level coprimality
relation with the other factor. -/
theorem coprimeRelation_rightFactor
    {parent other child : Part} {cofactor : GaussianPolynomial}
    (coprime : CoprimeRelation parent other)
    (factorization : Factorization parent.polynomial
      cofactor child.polynomial) :
    CoprimeRelation child other :=
  coprimeRelationOfCertificate
    (RFAP.SquarefreeFactors.coprimeRightFactor
      (coprimeCertificateOfRelation parent other coprime)
        child.nonzero factorization)

/-! ## Pairwise-coprime multiplicity basis -/

/-- One squarefree basis part with its strictly positive occurrence count. -/
structure BasisEntry where
  part : Part
  multiplicity : Nat
  multiplicityPositive : 0 < multiplicity

def BasisPairwise (entries : List BasisEntry) : Prop :=
  entries.Pairwise fun left right => CoprimeRelation left.part right.part

def AllCoprime (external : Part) (entries : List BasisEntry) : Prop :=
  ∀ entry ∈ entries, CoprimeRelation external entry.part

/-- Evaluated product of the pairwise-coprime basis, with each part raised to
its displayed occurrence count. -/
def basisValue : List BasisEntry → Gaussian → Gaussian
  | [], _ => 1
  | entry :: entries, point =>
      entry.part.polynomial.eval point ^ entry.multiplicity *
        basisValue entries point

/-- Degree of the weighted basis product. -/
def basisDegree : List BasisEntry → Nat
  | [] => 0
  | entry :: entries =>
      entry.multiplicity * entry.part.polynomial.natDegree +
        basisDegree entries

/-- Result of inserting one squarefree occurrence into an already pairwise-
coprime basis.  The external-preservation field is the induction invariant
that lets later gcd splits retain pairwise coprimality. -/
structure Insertion (new : Part) (source : List BasisEntry) where
  entries : List BasisEntry
  pairwise : BasisPairwise entries
  valueIdentity : ∀ point : Gaussian,
    basisValue entries point =
      basisValue source point * new.polynomial.eval point
  degreeIdentity : basisDegree entries =
    basisDegree source + new.polynomial.natDegree
  preservesExternal : ∀ (external : Part),
    CoprimeRelation external new →
    AllCoprime external source →
    AllCoprime external entries

/-- Insert one squarefree occurrence.  A coprime head is retained.  A
nonconstant common gcd receives one additional occurrence, the old head's
residual keeps its old multiplicity, and the new residual continues through
the tail.  Recursion is solely on the finite source list. -/
def insertPart : (new : Part) → (source : List BasisEntry) →
    BasisPairwise source → Insertion new source
  | new, [], _ => by
      exact
        { entries :=
            [{ part := new
               multiplicity := 1
               multiplicityPositive := Nat.zero_lt_succ 0 }]
          pairwise := QuotientFreeList.pairwise_singleton _ _
          valueIdentity := by
            intro point
            simp only [basisValue, pow_one, mul_one, one_mul]
          degreeIdentity := by
            simp only [basisDegree, Nat.one_mul, Nat.add_zero,
              Nat.zero_add]
          preservesExternal := by
            intro external externalNew _ entry member
            simp only [List.mem_singleton] at member
            subst entry
            exact externalNew }
  | new, head :: tail, pairwise => by
      have pairwiseParts := List.pairwise_cons.mp pairwise
      have headTail : AllCoprime head.part tail := pairwiseParts.1
      have tailPairwise : BasisPairwise tail := pairwiseParts.2
      match outcome : RFAP.Squarefree.coprimeOutcome
          new.polynomial head.part.polynomial (Or.inl new.nonzero) with
      | .coprime certificate =>
          let recursive := insertPart new tail tailPairwise
          have newHead : CoprimeRelation new head.part :=
            coprimeRelationOfCertificate certificate
          have headNew : CoprimeRelation head.part new :=
            coprimeRelation_symm newHead
          have headRest : AllCoprime head.part recursive.entries :=
            recursive.preservesExternal head.part headNew headTail
          exact
            { entries := head :: recursive.entries
              pairwise := List.pairwise_cons.mpr
                ⟨headRest, recursive.pairwise⟩
              valueIdentity := by
                intro point
                simp only [basisValue]
                rw [recursive.valueIdentity point]
                ring1
              degreeIdentity := by
                simp only [basisDegree]
                rw [recursive.degreeIdentity]
                ring1
              preservesExternal := by
                intro external externalNew externalSource entry member
                rcases List.mem_cons.mp member with rfl | restMember
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
          let split := commonSplit newFactor headFactor common
          let recursive := insertPart split.leftRemainder tail tailPairwise
          let commonEntry : BasisEntry :=
            { part := split.common.toPart
              multiplicity := head.multiplicity + 1
              multiplicityPositive := by omega }
          let rightEntry : BasisEntry :=
            { part := split.rightRemainder
              multiplicity := head.multiplicity
              multiplicityPositive := head.multiplicityPositive }
          have commonLeft : CoprimeRelation commonEntry.part
              split.leftRemainder :=
            coprimeRelationOfCertificate split.commonLeftCoprime
          have commonRight : CoprimeRelation commonEntry.part
              rightEntry.part :=
            coprimeRelationOfCertificate split.commonRightCoprime
          have leftRight : CoprimeRelation split.leftRemainder
              rightEntry.part :=
            coprimeRelationOfCertificate split.remaindersCoprime
          have rightLeft : CoprimeRelation rightEntry.part
              split.leftRemainder := coprimeRelation_symm leftRight
          have commonTail : AllCoprime commonEntry.part tail := by
            intro entry member
            have headEntry := headTail entry member
            have childEntry := coprimeRelation_leftFactor
              (parent := head.part) (other := entry.part)
              (child := commonEntry.part) headEntry
                split.rightFactorization
            exact childEntry
          have rightTail : AllCoprime rightEntry.part tail := by
            intro entry member
            have headEntry := headTail entry member
            exact coprimeRelation_rightFactor
              (parent := head.part) (other := entry.part)
              (child := rightEntry.part) headEntry
                split.rightFactorization
          have commonRest : AllCoprime commonEntry.part recursive.entries :=
            recursive.preservesExternal commonEntry.part commonLeft commonTail
          have rightRest : AllCoprime rightEntry.part recursive.entries :=
            recursive.preservesExternal rightEntry.part rightLeft rightTail
          exact
            { entries := commonEntry :: rightEntry :: recursive.entries
              pairwise := by
                apply List.pairwise_cons.mpr
                constructor
                · intro entry member
                  rcases List.mem_cons.mp member with rfl | restMember
                  · exact commonRight
                  · exact commonRest entry restMember
                · exact List.pairwise_cons.mpr ⟨rightRest,
                    recursive.pairwise⟩
              valueIdentity := by
                intro point
                have newValue :=
                  RFAP.SquarefreeFactors.eval_factorization
                    split.leftFactorization point
                have headValue :=
                  RFAP.SquarefreeFactors.eval_factorization
                    split.rightFactorization point
                have newValue' : new.polynomial.eval point =
                    split.common.polynomial.eval point *
                      split.leftRemainder.polynomial.eval point := by
                  exact newValue
                have headValue' : head.part.polynomial.eval point =
                    split.common.polynomial.eval point *
                      split.rightRemainder.polynomial.eval point := by
                  exact headValue
                simp only [basisValue]
                rw [recursive.valueIdentity point]
                dsimp only [commonEntry, rightEntry, Factor.toPart]
                rw [newValue', headValue',
                  mul_pow, pow_succ]
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
                simp only [basisDegree]
                rw [recursive.degreeIdentity, ← newDegree, ← headDegree]
                dsimp only [commonEntry, rightEntry, Factor.toPart]
                ring1
              preservesExternal := by
                intro external externalNew externalSource entry member
                have externalHead :
                    CoprimeRelation external head.part :=
                  externalSource head List.mem_cons_self
                have externalTail : AllCoprime external tail :=
                  fun tailEntry tailMember => externalSource tailEntry
                    (List.mem_cons_of_mem head tailMember)
                have externalCommon :
                    CoprimeRelation external commonEntry.part := by
                  apply coprimeRelation_symm
                  exact coprimeRelation_leftFactor
                    (parent := new) (other := external)
                    (child := commonEntry.part)
                      (coprimeRelation_symm externalNew)
                        split.leftFactorization
                have externalRight :
                    CoprimeRelation external rightEntry.part := by
                  apply coprimeRelation_symm
                  exact coprimeRelation_rightFactor
                    (parent := head.part) (other := external)
                    (child := rightEntry.part)
                      (coprimeRelation_symm externalHead)
                        split.rightFactorization
                have externalLeft :
                    CoprimeRelation external split.leftRemainder := by
                  apply coprimeRelation_symm
                  exact coprimeRelation_rightFactor
                    (parent := new) (other := external)
                    (child := split.leftRemainder)
                      (coprimeRelation_symm externalNew)
                        split.leftFactorization
                rcases List.mem_cons.mp member with rfl | member
                · exact externalCommon
                · rcases List.mem_cons.mp member with rfl | restMember
                  · exact externalRight
                  · exact recursive.preservesExternal external
                      externalLeft externalTail entry restMember }
termination_by structural _ source _ => source

/-! ## Basis for a complete occurrence decomposition -/

def occurrenceDegree : List Factor → Nat
  | [] => 0
  | factor :: factors =>
      factor.polynomial.natDegree + occurrenceDegree factors

/-- Pairwise-coprime squarefree basis of a finite squarefree occurrence
list, with an exact weighted-product identity and exact degree balance. -/
structure Basis (source : List Factor) where
  entries : List BasisEntry
  pairwise : BasisPairwise entries
  valueIdentity : ∀ point : Gaussian,
    basisValue entries point =
      (RFAP.Factorization.factorProduct source).eval point
  degreeIdentity : basisDegree entries = occurrenceDegree source

/-- Fold the certified insertion algorithm over every squarefree occurrence. -/
def buildBasis : (source : List Factor) → Basis source
  | [] =>
      { entries := []
        pairwise := List.Pairwise.nil
        valueIdentity := by
          intro point
          simp only [basisValue,
            RFAP.Factorization.factorProduct, eval_constant]
        degreeIdentity := rfl }
  | factor :: factors => by
      let tailBasis := buildBasis factors
      let insertion := insertPart factor.toPart tailBasis.entries
        tailBasis.pairwise
      exact
        { entries := insertion.entries
          pairwise := insertion.pairwise
          valueIdentity := by
            intro point
            rw [insertion.valueIdentity point,
              tailBasis.valueIdentity point]
            simp only [Factor.toPart,
              RFAP.Factorization.factorProduct, eval_mul]
            ring1
          degreeIdentity := by
            rw [insertion.degreeIdentity, tailBasis.degreeIdentity]
            simp only [Factor.toPart, occurrenceDegree]
            ring1 }

def _root_.RFAP.Factorization.Decomposition.multiplicityBasis
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p) :
    Basis decomposition.factors :=
  buildBasis decomposition.factors

/-- The original normalized polynomial is exactly the weighted product of
the pairwise-coprime squarefree basis at every displayed finite argument. -/
theorem _root_.RFAP.Factorization.Decomposition.eval_multiplicityBasis
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p)
    (point : Gaussian) :
    p.eval point =
      basisValue decomposition.multiplicityBasis.entries point := by
  rw [decomposition.evalIdentity point,
    decomposition.multiplicityBasis.valueIdentity point]

theorem occurrenceDegree_eq_sum (source : List Factor) :
    occurrenceDegree source =
      (source.map fun factor => factor.polynomial.natDegree).sum := by
  induction source with
  | nil => rfl
  | cons factor factors inductionHypothesis =>
      simp only [occurrenceDegree, List.map_cons, List.sum_cons,
        inductionHypothesis]

/-- Weighted multiplicity degrees sum to the original normalized degree. -/
theorem _root_.RFAP.Factorization.Decomposition.multiplicityDegree
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p) :
    basisDegree decomposition.multiplicityBasis.entries = p.natDegree := by
  rw [decomposition.multiplicityBasis.degreeIdentity,
    occurrenceDegree_eq_sum, decomposition.degreeSum]

/-! ## Positive-degree basis exposed to root isolation -/

/-- One positive-degree pairwise-coprime squarefree factor with its exact
exponent in the weighted product. -/
structure PositiveEntry where
  part : Part
  degreePositive : 0 < part.polynomial.natDegree
  multiplicity : Nat
  multiplicityPositive : 0 < multiplicity

def PositiveEntry.factor (entry : PositiveEntry) : Factor :=
  entry.part.toFactor entry.degreePositive

/-- Remove only degree-zero unit parts from the exact multiplicity basis. -/
def positiveEntries : List BasisEntry → List PositiveEntry
  | [] => []
  | entry :: entries =>
      if degreeZero : entry.part.polynomial.natDegree = 0 then
        positiveEntries entries
      else
        { part := entry.part
          degreePositive := Nat.pos_of_ne_zero degreeZero
          multiplicity := entry.multiplicity
          multiplicityPositive := entry.multiplicityPositive } ::
            positiveEntries entries

/-- Weighted product of only the positive-degree factors sent to isolation. -/
def positiveValue : List PositiveEntry → Gaussian → Gaussian
  | [], _ => 1
  | entry :: entries, point =>
      entry.part.polynomial.eval point ^ entry.multiplicity *
        positiveValue entries point

/-- Product of the omitted nonzero degree-zero parts, evaluated at zero.
Degree-zero normalization makes this independent of the queried point. -/
def unitValue : List BasisEntry → Gaussian
  | [] => 1
  | entry :: entries =>
      if entry.part.polynomial.natDegree = 0 then
        entry.part.polynomial.eval 0 ^ entry.multiplicity * unitValue entries
      else
        unitValue entries

theorem basisValue_eq_unitValue_mul_positiveValue
    (source : List BasisEntry) (point : Gaussian) :
    basisValue source point =
      unitValue source * positiveValue (positiveEntries source) point := by
  induction source with
  | nil =>
      simp only [basisValue, unitValue, positiveEntries, positiveValue,
        mul_one]
  | cons entry entries inductionHypothesis =>
      rw [basisValue, unitValue, positiveEntries]
      split
      · rename_i degreeZero
        have constantIdentity : entry.part.polynomial =
            constant entry.part.polynomial.leadingCoeff := by
          calc
            entry.part.polynomial = entry.part.polynomial.normalize :=
              entry.part.normalized.symm
            _ = constant entry.part.polynomial.leadingCoeff :=
              normalize_eq_constant_leadingCoeff_of_degree_zero
                entry.part.nonzero degreeZero
        rw [constantIdentity]
        simp only [eval_constant]
        rw [inductionHypothesis]
        ring1
      · simp only [positiveValue]
        rw [inductionHypothesis]
        ring1

theorem unitValue_ne_zero (source : List BasisEntry) :
    unitValue source ≠ 0 := by
  induction source with
  | nil =>
      simp only [unitValue]
      exact one_ne_zero
  | cons entry entries inductionHypothesis =>
      rw [unitValue]
      split
      · rename_i degreeZero
        have constantIdentity : entry.part.polynomial =
            constant entry.part.polynomial.leadingCoeff := by
          calc
            entry.part.polynomial = entry.part.polynomial.normalize :=
              entry.part.normalized.symm
            _ = constant entry.part.polynomial.leadingCoeff :=
              normalize_eq_constant_leadingCoeff_of_degree_zero
                entry.part.nonzero degreeZero
        have valueNonzero : entry.part.polynomial.eval 0 ≠ 0 := by
          rw [constantIdentity, eval_constant]
          exact leadingCoeff_ne_zero entry.part.nonzero
        exact RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct
          (RFAP.ConstructiveGaussian.Gaussian.pow_ne_zero_direct _
            valueNonzero _) inductionHypothesis
      · exact inductionHypothesis

theorem PositiveEntry.part_mem_of_mem_positiveEntries
    {entry : PositiveEntry} : ∀ {source : List BasisEntry},
    entry ∈ positiveEntries source →
    ∃ sourceEntry ∈ source, entry.part = sourceEntry.part
  | [], member => by simp [positiveEntries] at member
  | sourceEntry :: source, member => by
      rw [positiveEntries] at member
      split at member
      · rcases entry.part_mem_of_mem_positiveEntries member with
          ⟨found, foundMember, same⟩
        exact ⟨found, List.mem_cons_of_mem sourceEntry foundMember, same⟩
      · rcases List.mem_cons.mp member with rfl | tailMember
        · exact ⟨sourceEntry, List.mem_cons_self, rfl⟩
        · rcases entry.part_mem_of_mem_positiveEntries tailMember with
            ⟨found, foundMember, same⟩
          exact ⟨found, List.mem_cons_of_mem sourceEntry foundMember, same⟩

/-- Removing unit parts preserves pairwise coprimality of every factor sent
to isolation. -/
theorem positiveEntries_pairwise : ∀ {source : List BasisEntry},
    BasisPairwise source →
    (positiveEntries source).Pairwise fun left right =>
      CoprimeRelation left.part right.part
  | [], _ => List.Pairwise.nil
  | sourceEntry :: source, pairwise => by
      have pairwiseParts := List.pairwise_cons.mp pairwise
      rw [positiveEntries]
      split
      · exact positiveEntries_pairwise pairwiseParts.2
      · apply List.pairwise_cons.mpr
        constructor
        · intro entry member
          rcases entry.part_mem_of_mem_positiveEntries member with
            ⟨found, foundMember, same⟩
          rw [same]
          exact pairwiseParts.1 found foundMember
        · exact positiveEntries_pairwise pairwiseParts.2

theorem basisDegree_eq_zero_of_positiveEntries_eq_nil :
    ∀ (source : List BasisEntry), positiveEntries source = [] →
      basisDegree source = 0
  | [], _ => rfl
  | entry :: entries, empty => by
      rw [positiveEntries] at empty
      split at empty
      · rename_i degreeZero
        rw [basisDegree, degreeZero, Nat.mul_zero, Nat.zero_add,
          basisDegree_eq_zero_of_positiveEntries_eq_nil entries empty]
      · exact (List.cons_ne_nil _ _ empty).elim

theorem positiveEntries_ne_nil_of_basisDegree_positive
    {source : List BasisEntry} (positive : 0 < basisDegree source) :
    positiveEntries source ≠ [] := by
  intro empty
  have zero := basisDegree_eq_zero_of_positiveEntries_eq_nil source empty
  rw [zero] at positive
  exact Nat.lt_irrefl 0 positive

def _root_.RFAP.Factorization.Decomposition.positiveMultiplicityEntries
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p) :
    List PositiveEntry :=
  positiveEntries decomposition.multiplicityBasis.entries

theorem _root_.RFAP.Factorization.Decomposition.positiveMultiplicityEntries_pairwise
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p) :
    decomposition.positiveMultiplicityEntries.Pairwise fun left right =>
      CoprimeRelation left.part right.part :=
  positiveEntries_pairwise decomposition.multiplicityBasis.pairwise

/-- Exact multiplicity factorization after deleting only a displayed nonzero
unit scalar. -/
theorem _root_.RFAP.Factorization.Decomposition.eval_positiveMultiplicityEntries
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p)
    (point : Gaussian) :
    p.eval point =
      unitValue decomposition.multiplicityBasis.entries *
        positiveValue decomposition.positiveMultiplicityEntries point := by
  calc
    p.eval point = basisValue decomposition.multiplicityBasis.entries point :=
      decomposition.eval_multiplicityBasis point
    _ = unitValue decomposition.multiplicityBasis.entries *
        positiveValue decomposition.positiveMultiplicityEntries point :=
      basisValue_eq_unitValue_mul_positiveValue _ _

theorem _root_.RFAP.Factorization.Decomposition.multiplicityUnit_ne_zero
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p) :
    unitValue decomposition.multiplicityBasis.entries ≠ 0 :=
  unitValue_ne_zero _

theorem _root_.RFAP.Factorization.Decomposition.positiveMultiplicityEntries_nonempty
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p) :
    decomposition.positiveMultiplicityEntries ≠ [] := by
  apply positiveEntries_ne_nil_of_basisDegree_positive
  rw [decomposition.multiplicityDegree]
  cases factorsEquation : decomposition.factors with
  | nil => exact (decomposition.factorsNonempty factorsEquation).elim
  | cons factor factors =>
      rw [← decomposition.degreeSum, factorsEquation]
      simp only [List.map_cons, List.sum_cons]
      exact factor.degreePositive.trans_le (Nat.le_add_right _ _)

/-! ## Displayed weighted polynomials and positive degree totals -/

/-- Finite polynomial power, kept local to the dense executable polynomial
representation rather than importing a broader polynomial monoid. -/
def polynomialPower (p : GaussianPolynomial) : Nat → GaussianPolynomial
  | 0 => constant 1
  | exponent + 1 => p * polynomialPower p exponent

@[simp] theorem eval_polynomialPower
    (p : GaussianPolynomial) (exponent : Nat) (point : Gaussian) :
    (polynomialPower p exponent).eval point = p.eval point ^ exponent := by
  induction exponent with
  | zero => simp only [polynomialPower, eval_constant, pow_zero]
  | succ exponent inductionHypothesis =>
      rw [polynomialPower, eval_mul, inductionHypothesis, pow_succ]
      exact RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _

theorem polynomialPower_nonzero
    {p : GaussianPolynomial} (nonzero : p.isZero = false) :
    ∀ exponent : Nat, (polynomialPower p exponent).isZero = false
  | 0 => (LeadingTerm.constant one_ne_zero).nonzero
  | exponent + 1 =>
      isZero_mul_eq_false nonzero
        (polynomialPower_nonzero nonzero exponent)

/-- The displayed dense polynomial represented by a positive multiplicity
list. -/
def positivePolynomial : List PositiveEntry → GaussianPolynomial
  | [] => constant 1
  | entry :: entries =>
      polynomialPower entry.part.polynomial entry.multiplicity *
        positivePolynomial entries

@[simp] theorem positivePolynomial_eval
    (entries : List PositiveEntry) (point : Gaussian) :
    (positivePolynomial entries).eval point = positiveValue entries point := by
  induction entries with
  | nil => simp only [positivePolynomial, positiveValue, eval_constant]
  | cons entry entries inductionHypothesis =>
      simp only [positivePolynomial, positiveValue, eval_mul,
        eval_polynomialPower, inductionHypothesis]

theorem positivePolynomial_nonzero : ∀ entries : List PositiveEntry,
    (positivePolynomial entries).isZero = false
  | [] => (LeadingTerm.constant one_ne_zero).nonzero
  | entry :: entries =>
      isZero_mul_eq_false
        (polynomialPower_nonzero entry.part.nonzero entry.multiplicity)
        (positivePolynomial_nonzero entries)

/-- Weighted degree of the positive-degree entries only. -/
def positiveDegree : List PositiveEntry → Nat
  | [] => 0
  | entry :: entries =>
      entry.multiplicity * entry.part.polynomial.natDegree +
        positiveDegree entries

theorem basisDegree_eq_positiveDegree_positiveEntries :
    ∀ source : List BasisEntry,
      basisDegree source = positiveDegree (positiveEntries source)
  | [] => rfl
  | entry :: entries => by
      rw [basisDegree, positiveEntries]
      split
      · rename_i degreeZero
        rw [degreeZero, Nat.mul_zero, Nat.zero_add,
          basisDegree_eq_positiveDegree_positiveEntries entries]
      · simp only [positiveDegree]
        rw [basisDegree_eq_positiveDegree_positiveEntries entries]

/-- The positive signed multiplicities, weighted by their squarefree factor
degrees, add exactly to the original positive-degree polynomial degree. -/
theorem _root_.RFAP.Factorization.Decomposition.positiveMultiplicityDegree
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p) :
    positiveDegree decomposition.positiveMultiplicityEntries = p.natDegree := by
  calc
    positiveDegree decomposition.positiveMultiplicityEntries =
        basisDegree decomposition.multiplicityBasis.entries :=
      (basisDegree_eq_positiveDegree_positiveEntries
        decomposition.multiplicityBasis.entries).symm
    _ = p.natDegree := decomposition.multiplicityDegree

/-- The normalized source evaluates as one explicit nonzero unit times the
displayed weighted positive polynomial. -/
theorem _root_.RFAP.Factorization.Decomposition.eval_positivePolynomial
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p)
    (point : Gaussian) :
    p.eval point =
      unitValue decomposition.multiplicityBasis.entries *
        (positivePolynomial
          decomposition.positiveMultiplicityEntries).eval point := by
  rw [decomposition.eval_positiveMultiplicityEntries point,
    positivePolynomial_eval]

/-- The multiplicity basis is an exact finite polynomial factorization:
the normalized coefficient difference between the source and the displayed
unit times the weighted positive polynomial is zero. -/
theorem _root_.RFAP.Factorization.Decomposition.positiveMultiplicityProductIdentity
    {p : GaussianPolynomial}
    (decomposition : RFAP.Factorization.Decomposition p) :
    RFAP.Factorization.ProductIdentity p
      (constant (unitValue decomposition.multiplicityBasis.entries))
      (positivePolynomial decomposition.positiveMultiplicityEntries) := by
  apply RFAP.Factorization.factorizationOfCandidateEvals
  intro point _
  rw [eval_constant]
  exact decomposition.eval_positivePolynomial point

end RFAP.Multiplicity
