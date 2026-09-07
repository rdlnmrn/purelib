import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.Curve.RationalDerivativeDegree
import RFAP.Isolation.SafeCandidates

/-!
# Finite squarefree decomposition of coordinate polynomials

A boundary-curve gcd can have repeated parameter factors even when the
original Gaussian polynomial is squarefree.  This module removes that
special-case obligation: finite extended Euclid recursively decomposes any
nonzero positive-degree constructive-rational polynomial into displayed
squarefree occurrences.  The product identity and root coverage are proved
from finite coefficient candidates, never from evaluation over a carrier.
-/

namespace CCL.CoordinateFactorization

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev SquarefreeCertificate (p : Polynomial) :=
  RFAP.PathClearance.CoprimeCertificate p
    (RFAP.ComputableDerivative.derivative p)

open RFAP.ComputablePolynomial.DensePolynomial
open RFAP.ConstructivePolynomialLeading

/-- Exact finite coefficient factorization. -/
abbrev Factorization (p left right : Polynomial) : Prop :=
  (p - left * right).isZero = true

/-- A pointwise identity need only be checked on one explicit finite list
longer than the represented difference polynomial. -/
theorem factorizationOfEvals
    (p left right : Polynomial)
    (identity : ∀ point : Coordinate,
      p.eval point = left.eval point * right.eval point) :
    Factorization p left right := by
  let difference := p - left * right
  let points := RFAP.SafeCandidates.interiorCandidates
    (0 : Coordinate) 1 difference.degreeCount
  by_cases zero : difference.isZero = true
  · exact zero
  · have nonzero : difference.isZero = false := by simpa using zero
    have allZero : ∀ point ∈ points, difference.eval point = 0 := by
      intro point _member
      dsimp only [difference]
      rw [eval_sub, eval_mul, identity point]
      ring1
    have tooMany :=
      RFAP.SafeCandidates.nodup_zeros_length_lt_degreeCount
        difference nonzero points
        (RFAP.SafeCandidates.interiorCandidates_nodup
          (show (0 : Coordinate) < 1 by decide) difference.degreeCount)
        allZero
    have pointCount : points.length = difference.degreeCount + 1 := by
      exact RFAP.SafeCandidates.interiorCandidates_length
        0 1 difference.degreeCount
    rw [pointCount] at tooMany
    exact (Nat.not_lt_of_ge (Nat.le_succ difference.degreeCount) tooMany).elim

theorem eval_factorization
    {p left right : Polynomial}
    (factorization : Factorization p left right) (point : Coordinate) :
    p.eval point = left.eval point * right.eval point := by
  have differenceZero := eval_eq_zero_of_isZero factorization point
  rw [eval_sub, eval_mul] at differenceZero
  calc
    p.eval point =
        (p.eval point - left.eval point * right.eval point) +
          left.eval point * right.eval point := by ring1
    _ = 0 + left.eval point * right.eval point := by rw [differenceZero]
    _ = left.eval point * right.eval point :=
      RFAP.ConstructiveFraction.zero_add _

/-- The finite coefficient factorization also identifies the automatic
derivatives pointwise. -/
theorem eval_derivative_factorization
    {p left right : Polynomial}
    (factorization : Factorization p left right) (point : Coordinate) :
    (RFAP.ComputableDerivative.derivative p).eval point =
      (RFAP.ComputableDerivative.derivative (left * right)).eval point :=
  RFAP.ComputableDerivative.eval_derivative_eq_of_sub_isZero
    factorization point

/-- Exchange the two displayed factors without polynomial extensionality. -/
theorem factorization_swap
    {p left right : Polynomial}
    (factorization : Factorization p left right) :
    Factorization p right left := by
  apply factorizationOfEvals
  intro point
  rw [eval_factorization factorization point]
  exact RFAP.ConstructiveFraction.mul_comm _ _

/-- Every displayed nonzero left factor of a squarefree coordinate
polynomial is squarefree.  The certificate is obtained by rearranging the
finite Bézout identity and the explicit derivative product rule. -/
def leftFactorSquarefree
    {p left right : Polynomial}
    (squarefree : SquarefreeCertificate p)
    (_leftNonzero : left.isZero = false)
    (factorization : Factorization p left right) :
    SquarefreeCertificate left := by
  let leftCoefficient :=
    squarefree.left * right +
      squarefree.right * RFAP.ComputableDerivative.derivative right
  let derivativeCoefficient := squarefree.right * right
  exact
    { left := leftCoefficient
      right := derivativeCoefficient
      identity := by
        intro point
        have valueIdentity := eval_factorization factorization point
        have derivativeIdentity :=
          eval_derivative_factorization factorization point
        have original := squarefree.identity point
        rw [valueIdentity, derivativeIdentity] at original
        rw [RFAP.ComputableDerivative.eval_derivative_mul] at original
        dsimp only [leftCoefficient, derivativeCoefficient]
        simp only [eval_add, eval_mul]
        calc
          1 = squarefree.left.eval point *
                (left.eval point * right.eval point) +
              squarefree.right.eval point *
                ((RFAP.ComputableDerivative.derivative left).eval point *
                    right.eval point +
                  left.eval point *
                    (RFAP.ComputableDerivative.derivative right).eval point) :=
            original
          _ = (squarefree.left.eval point * right.eval point +
                squarefree.right.eval point *
                  (RFAP.ComputableDerivative.derivative right).eval point) *
                  left.eval point +
              (squarefree.right.eval point * right.eval point) *
                (RFAP.ComputableDerivative.derivative left).eval point := by
            ring1 }

/-- The two nonzero displayed factors of a squarefree coordinate polynomial
are coprime. -/
def factorsCoprime
    {p left right : Polynomial}
    (squarefree : SquarefreeCertificate p)
    (_leftNonzero : left.isZero = false)
    (factorization : Factorization p left right) :
    RFAP.PathClearance.CoprimeCertificate left right := by
  let leftCoefficient :=
    squarefree.left * right +
      squarefree.right * RFAP.ComputableDerivative.derivative right
  let rightCoefficient :=
    squarefree.right * RFAP.ComputableDerivative.derivative left
  exact
    { left := leftCoefficient
      right := rightCoefficient
      identity := by
        intro point
        have valueIdentity := eval_factorization factorization point
        have derivativeIdentity :=
          eval_derivative_factorization factorization point
        have original := squarefree.identity point
        rw [valueIdentity, derivativeIdentity] at original
        rw [RFAP.ComputableDerivative.eval_derivative_mul] at original
        dsimp only [leftCoefficient, rightCoefficient]
        simp only [eval_add, eval_mul]
        calc
          1 = squarefree.left.eval point *
                (left.eval point * right.eval point) +
              squarefree.right.eval point *
                ((RFAP.ComputableDerivative.derivative left).eval point *
                    right.eval point +
                  left.eval point *
                    (RFAP.ComputableDerivative.derivative right).eval point) :=
            original
          _ = (squarefree.left.eval point * right.eval point +
                squarefree.right.eval point *
                  (RFAP.ComputableDerivative.derivative right).eval point) *
                  left.eval point +
              (squarefree.right.eval point *
                  (RFAP.ComputableDerivative.derivative left).eval point) *
                right.eval point := by
            ring1 }

/-- Coprimality with a second polynomial descends to a displayed nonzero
left factor. -/
def coprimeLeftFactor
    {p q left right : Polynomial}
    (coprime : RFAP.PathClearance.CoprimeCertificate p q)
    (_leftNonzero : left.isZero = false)
    (factorization : Factorization p left right) :
    RFAP.PathClearance.CoprimeCertificate left q := by
  let leftCoefficient := coprime.left * right
  exact
    { left := leftCoefficient
      right := coprime.right
      identity := by
        intro point
        have original := coprime.identity point
        rw [eval_factorization factorization point] at original
        dsimp only [leftCoefficient]
        simp only [eval_mul]
        calc
          1 = coprime.left.eval point *
                (left.eval point * right.eval point) +
              coprime.right.eval point * q.eval point := original
          _ = (coprime.left.eval point * right.eval point) *
                left.eval point +
              coprime.right.eval point * q.eval point := by ring1 }

/-- Coprimality with a second polynomial descends to a displayed nonzero
right factor. -/
def coprimeRightFactor
    {p q left right : Polynomial}
    (coprime : RFAP.PathClearance.CoprimeCertificate p q)
    (rightNonzero : right.isZero = false)
    (factorization : Factorization p left right) :
    RFAP.PathClearance.CoprimeCertificate right q :=
  coprimeLeftFactor coprime rightNonzero
    (factorization_swap factorization)

/-- Every displayed nonzero right factor of a squarefree coordinate
polynomial is squarefree. -/
def rightFactorSquarefree
    {p left right : Polynomial}
    (squarefree : SquarefreeCertificate p)
    (rightNonzero : right.isZero = false)
    (factorization : Factorization p left right) :
    SquarefreeCertificate right :=
  leftFactorSquarefree squarefree rightNonzero
    (factorization_swap factorization)

theorem right_isZero_false
    {p left right : Polynomial}
    (pNonzero : p.isZero = false) (pNormalized : p.normalize = p)
    (factorization : Factorization p left right) :
    right.isZero = false := by
  by_cases rightZero : right.isZero = true
  · have productZero : left * right = (0 : Polynomial) :=
      mul_eq_zero_of_isZero_right rightZero
    change (p - left * right).isZero = true at factorization
    rw [productZero] at factorization
    have targetZero : p.isZero = true := by
      change (p + -(0 : Polynomial)).isZero = true at factorization
      have negZero : -(0 : Polynomial) = 0 := rfl
      rw [negZero, add_zero_normalize, pNormalized] at factorization
      exact factorization
    rw [pNonzero] at targetZero
    exact Bool.noConfusion targetZero
  · simpa using rightZero

theorem factor_natDegree_add
    {p left right : Polynomial}
    (pNonzero : p.isZero = false) (pNormalized : p.normalize = p)
    (leftNonzero : left.isZero = false) (rightNonzero : right.isZero = false)
    (factorization : Factorization p left right) :
    left.natDegree + right.natDegree = p.natDegree := by
  have productNonzero := isZero_mul_eq_false leftNonzero rightNonzero
  have degree := LeadingTerm.natDegree_eq_of_sub_isZero pNonzero
    productNonzero pNormalized (normalize_mul left right) factorization
  rw [natDegree_mul leftNonzero rightNonzero] at degree
  exact degree.symm

/-- Normalize a checked constant Euclidean gcd into explicit coordinate
Bézout data. -/
def certificateOfConstantGCD
    (p q : Polynomial)
    (gcdNonzero : (RFAP.ComputableGCD.extendedGCD p q).gcd.isZero = false)
    (degreeZero :
      (RFAP.ComputableGCD.extendedGCD p q).gcd.natDegree = 0) :
    RFAP.PathClearance.CoprimeCertificate p q := by
  let result := RFAP.ComputableGCD.extendedGCD p q
  let unit := result.gcd.leadingCoeff
  have unitNonzero : unit ≠ 0 := leadingCoeff_ne_zero gcdNonzero
  have gcdConstant : result.gcd = constant unit := by
    calc
      result.gcd = result.gcd.normalize := result.normalized.symm
      _ = constant result.gcd.leadingCoeff :=
        normalize_eq_constant_leadingCoeff_of_degree_zero gcdNonzero degreeZero
  exact
    { left := scale unit⁻¹ result.left
      right := scale unit⁻¹ result.right
      identity := by
        intro point
        have raw := result.identity point
        rw [gcdConstant, eval_constant] at raw
        simp only [eval_scale]
        calc
          1 = unit⁻¹ * unit := by
            rw [RFAP.ConstructiveFraction.mul_comm]
            exact (RFAP.ExplicitField.mul_inv_cancel unit unitNonzero).symm
          _ = unit⁻¹ *
              (result.left.eval point * p.eval point +
                result.right.eval point * q.eval point) := by rw [← raw]
          _ = unit⁻¹ * (result.left.eval point * p.eval point) +
              unit⁻¹ * (result.right.eval point * q.eval point) :=
            RFAP.ConstructiveFraction.left_distrib _ _ _
          _ = (unit⁻¹ * result.left.eval point) * p.eval point +
              (unit⁻¹ * result.right.eval point) * q.eval point := by
            rw [RFAP.ConstructiveFraction.mul_assoc,
              RFAP.ConstructiveFraction.mul_assoc] }

/-- One positive-degree squarefree occurrence. -/
structure Factor where
  polynomial : Polynomial
  normalized : polynomial.normalize = polynomial
  nonzero : polynomial.isZero = false
  degreePositive : 0 < polynomial.natDegree
  squarefree : SquarefreeCertificate polynomial

/-- How one squarefree factor meets one displayed condition polynomial.
The equality branch retains the explicit finite cofactor identity, from which
root equality and quantitative near-root bounds can both be recovered; the
apart branch retains explicit finite Bézout separation. -/
inductive ConditionRelation (condition : Polynomial) (factor : Factor) where
  | equality (cofactor : Polynomial)
      (factorization : Factorization condition factor.polynomial cofactor)
  | apart (coprime :
      RFAP.PathClearance.CoprimeCertificate
        factor.polynomial condition)

/-- One squarefree piece produced by splitting a source factor against a
condition.  Its displayed cofactor lets earlier condition certificates descend
through later splits. -/
structure ConditionPiece (source : Factor) (condition : Polynomial) where
  factor : Factor
  cofactor : Polynomial
  factorization : Factorization source.polynomial factor.polynomial cofactor
  relation : ConditionRelation condition factor

/-- Finite root-exact partition of one squarefree factor against one
condition polynomial.  Executable gcd yields at most two pieces. -/
structure ConditionPartition (factor : Factor) (condition : Polynomial) where
  pieces : List (ConditionPiece factor condition)
  nonempty : pieces ≠ []
  rootCoverage : ∀ point : Coordinate,
    factor.polynomial.eval point = 0 ↔
      ∃ piece ∈ pieces, piece.factor.polynomial.eval point = 0

/-- A relation already known for the source factor descends through any
later displayed factor piece. -/
def ConditionRelation.descend
    {source : Factor} {condition nextCondition : Polynomial}
  (relation : ConditionRelation condition source)
  (piece : ConditionPiece source nextCondition) :
  ConditionRelation condition piece.factor := by
  cases relation with
  | equality cofactor factorization =>
      exact .equality (piece.cofactor * cofactor) (by
        apply factorizationOfEvals
        intro point
        rw [eval_factorization factorization point,
          eval_factorization piece.factorization point, eval_mul]
        ring1)
  | apart coprime =>
      exact .apart
        (coprimeLeftFactor coprime piece.factor.nonzero piece.factorization)

/-- If a polynomial is normalized, nonzero, and degree zero, every displayed
evaluation is nonzero. -/
theorem eval_ne_zero_of_normalized_degree_zero
    {polynomial : Polynomial}
    (normalized : polynomial.normalize = polynomial)
    (nonzero : polynomial.isZero = false)
    (degreeZero : polynomial.natDegree = 0)
    (point : Coordinate) : polynomial.eval point ≠ 0 := by
  have polynomialConstant :
      polynomial = constant polynomial.leadingCoeff := by
    calc
      polynomial = polynomial.normalize := normalized.symm
      _ = constant polynomial.leadingCoeff :=
        normalize_eq_constant_leadingCoeff_of_degree_zero nonzero degreeZero
  rw [polynomialConstant, eval_constant]
  exact leadingCoeff_ne_zero nonzero

/-- If one polynomial is coprime to each of two displayed factors, it is
coprime to their product. -/
def coprimeWithProduct
    {p left right product : Polynomial}
    (leftCoprime :
      RFAP.PathClearance.CoprimeCertificate p left)
    (rightCoprime :
      RFAP.PathClearance.CoprimeCertificate p right)
    (factorization : Factorization product left right) :
    RFAP.PathClearance.CoprimeCertificate p product := by
  let pCoefficient :=
    leftCoprime.left * rightCoprime.left * p +
      leftCoprime.left * rightCoprime.right * right +
      leftCoprime.right * rightCoprime.left * left
  let productCoefficient := leftCoprime.right * rightCoprime.right
  exact
    { left := pCoefficient
      right := productCoefficient
      identity := by
        intro point
        have leftIdentity := leftCoprime.identity point
        have rightIdentity := rightCoprime.identity point
        have productIdentity := eval_factorization factorization point
        dsimp only [pCoefficient, productCoefficient]
        simp only [eval_add, eval_mul]
        calc
          1 = 1 * 1 := by ring1
          _ = (leftCoprime.left.eval point * p.eval point +
                leftCoprime.right.eval point * left.eval point) *
              (rightCoprime.left.eval point * p.eval point +
                rightCoprime.right.eval point * right.eval point) := by
            rw [← leftIdentity, ← rightIdentity]
          _ = ((leftCoprime.left.eval point *
                    rightCoprime.left.eval point * p.eval point +
                  leftCoprime.left.eval point *
                    rightCoprime.right.eval point * right.eval point) +
                leftCoprime.right.eval point *
                  rightCoprime.left.eval point * left.eval point) *
                p.eval point +
              (leftCoprime.right.eval point *
                  rightCoprime.right.eval point) *
                (left.eval point * right.eval point) := by ring1
          _ = ((leftCoprime.left.eval point *
                    rightCoprime.left.eval point * p.eval point +
                  leftCoprime.left.eval point *
                    rightCoprime.right.eval point * right.eval point) +
                leftCoprime.right.eval point *
                  rightCoprime.left.eval point * left.eval point) *
                p.eval point +
              (leftCoprime.right.eval point *
                  rightCoprime.right.eval point) * product.eval point := by
            rw [productIdentity] }

/-- Executable gcd split of one squarefree factor against one condition.
The common-divisor piece is equality-owned; the complementary piece carries
an explicit finite coprimality certificate with the whole condition. -/
def splitAgainstCondition
    (factor : Factor) (condition : Polynomial) :
    ConditionPartition factor condition := by
  by_cases conditionZero : condition.isZero = true
  · let zeroPiece : ConditionPiece factor condition :=
      { factor := factor
        cofactor := constant 1
        factorization := by
          apply factorizationOfEvals
          intro point
          simp only [eval_constant,
            RFAP.ConstructiveFraction.mul_one_direct]
        relation := .equality (constant 0) (by
          apply factorizationOfEvals
          intro point
          rw [eval_eq_zero_of_isZero conditionZero point, eval_constant,
            RFAP.ConstructiveFraction.mul_zero_direct]) }
    exact
      { pieces := [zeroPiece]
        nonempty := List.cons_ne_nil _ _
        rootCoverage := by
          intro point
          constructor
          · intro factorZero
            exact ⟨zeroPiece, List.mem_cons_self, factorZero⟩
          · rintro ⟨piece, member, pieceZero⟩
            have equal : piece = zeroPiece := List.mem_singleton.mp member
            subst piece
            exact pieceZero }
  · have conditionNonzero : condition.isZero = false := by
      simpa using conditionZero
    let result := RFAP.ComputableGCD.extendedGCD
      factor.polynomial condition
    have gcdNonzero : result.gcd.isZero = false :=
      result.nonzero (Or.inl factor.nonzero)
    by_cases gcdDegreeZero : result.gcd.natDegree = 0
    · let coprime := certificateOfConstantGCD factor.polynomial condition
        gcdNonzero gcdDegreeZero
      let apartPiece : ConditionPiece factor condition :=
        { factor := factor
          cofactor := constant 1
          factorization := by
            apply factorizationOfEvals
            intro point
            simp only [eval_constant,
              RFAP.ConstructiveFraction.mul_one_direct]
          relation := .apart coprime }
      exact
        { pieces := [apartPiece]
          nonempty := List.cons_ne_nil _ _
          rootCoverage := by
            intro point
            constructor
            · intro factorZero
              exact ⟨apartPiece, List.mem_cons_self, factorZero⟩
            · rintro ⟨piece, member, pieceZero⟩
              have equal : piece = apartPiece := List.mem_singleton.mp member
              subst piece
              exact pieceZero }
    · have gcdDegreePositive : 0 < result.gcd.natDegree :=
        Nat.pos_of_ne_zero gcdDegreeZero
      have originalFactorization : Factorization factor.polynomial
          result.gcd result.pFactor := by
        apply factorizationOfEvals
        exact result.pIdentity
      have remainingNonzero : result.pFactor.isZero = false :=
        right_isZero_false factor.nonzero factor.normalized
          originalFactorization
      have degreeBalance : result.gcd.natDegree +
          result.pFactor.natDegree = factor.polynomial.natDegree :=
        factor_natDegree_add factor.nonzero factor.normalized gcdNonzero
          remainingNonzero originalFactorization
      let equalityFactor : Factor :=
        { polynomial := result.gcd
          normalized := result.normalized
          nonzero := gcdNonzero
          degreePositive := gcdDegreePositive
          squarefree := leftFactorSquarefree factor.squarefree gcdNonzero
            originalFactorization }
      have conditionFactorization : Factorization condition
          result.gcd result.qFactor := by
        apply factorizationOfEvals
        exact result.qIdentity
      let equalityPiece : ConditionPiece factor condition :=
        { factor := equalityFactor
          cofactor := result.pFactor
          factorization := originalFactorization
          relation := .equality result.qFactor conditionFactorization }
      by_cases remainingDegreeZero : result.pFactor.natDegree = 0
      · have remainingEvalNonzero :=
          eval_ne_zero_of_normalized_degree_zero
            result.pFactorNormalized remainingNonzero remainingDegreeZero
        exact
          { pieces := [equalityPiece]
            nonempty := List.cons_ne_nil _ _
            rootCoverage := by
              intro point
              constructor
              · intro factorZero
                rw [eval_factorization originalFactorization point] at factorZero
                by_cases gcdZero : result.gcd.eval point = 0
                · refine ⟨equalityPiece, List.mem_cons_self, ?_⟩
                  change result.gcd.eval point = 0
                  exact gcdZero
                · exact (RFAP.ConstructiveFraction.mul_ne_zero_direct gcdZero
                    (remainingEvalNonzero point) factorZero).elim
              · rintro ⟨piece, member, pieceZero⟩
                have equal : piece = equalityPiece :=
                  List.mem_singleton.mp member
                subst piece
                change result.gcd.eval point = 0 at pieceZero
                rw [eval_factorization originalFactorization point, pieceZero,
                  RFAP.ConstructiveFraction.zero_mul_direct]
                }
      · have remainingDegreePositive : 0 < result.pFactor.natDegree :=
          Nat.pos_of_ne_zero remainingDegreeZero
        let remainingFactor : Factor :=
          { polynomial := result.pFactor
            normalized := result.pFactorNormalized
            nonzero := remainingNonzero
            degreePositive := remainingDegreePositive
            squarefree := rightFactorSquarefree factor.squarefree
              remainingNonzero originalFactorization }
        let factorCoprime :
            RFAP.PathClearance.CoprimeCertificate
              result.gcd result.pFactor :=
          factorsCoprime factor.squarefree gcdNonzero originalFactorization
        let remainingGcdCoprime :
            RFAP.PathClearance.CoprimeCertificate
              result.pFactor result.gcd := factorCoprime.swap
        let remainingReducedCoprime :
            RFAP.PathClearance.CoprimeCertificate
              result.pFactor result.qFactor :=
          { left := result.factorLeft
            right := result.factorRight
            identity := result.factorIdentity }
        let remainingConditionCoprime := coprimeWithProduct
          remainingGcdCoprime remainingReducedCoprime conditionFactorization
        let remainingPiece : ConditionPiece factor condition :=
          { factor := remainingFactor
            cofactor := result.gcd
            factorization := factorization_swap originalFactorization
            relation := .apart remainingConditionCoprime }
        exact
          { pieces := [equalityPiece, remainingPiece]
            nonempty := List.cons_ne_nil _ _
            rootCoverage := by
              intro point
              constructor
              · intro factorZero
                have productZero : result.gcd.eval point *
                    result.pFactor.eval point = 0 := by
                  rw [← eval_factorization originalFactorization point]
                  exact factorZero
                by_cases gcdZero : result.gcd.eval point = 0
                · refine ⟨equalityPiece, List.mem_cons_self, ?_⟩
                  change result.gcd.eval point = 0
                  exact gcdZero
                · by_cases remainingZero : result.pFactor.eval point = 0
                  · refine ⟨remainingPiece,
                      List.mem_cons_of_mem equalityPiece List.mem_cons_self, ?_⟩
                    change result.pFactor.eval point = 0
                    exact remainingZero
                  · exact (RFAP.ConstructiveFraction.mul_ne_zero_direct gcdZero
                      remainingZero productZero).elim
              · rintro ⟨piece, member, pieceZero⟩
                rw [eval_factorization originalFactorization point]
                rcases List.mem_cons.mp member with equality | remaining
                · subst piece
                  change result.gcd.eval point = 0 at pieceZero
                  rw [pieceZero, RFAP.ConstructiveFraction.zero_mul_direct]
                · have pieceEq : piece = remainingPiece :=
                    List.mem_singleton.mp remaining
                  subst piece
                  change result.pFactor.eval point = 0 at pieceZero
                  rw [pieceZero,
                    RFAP.ConstructiveFraction.mul_zero_direct] }

/-- One squarefree factor together with its displayed cofactor in the source
factor and its exact equality/apart relation to every condition already
processed. -/
structure ConditionProfile (source : Factor) (conditions : List Polynomial)
    where
  factor : Factor
  cofactor : Polynomial
  factorization : Factorization source.polynomial factor.polynomial cofactor
  relations : List (Sigma fun condition : Polynomial =>
    ConditionRelation condition factor)
  conditions_eq : relations.map Sigma.fst = conditions

namespace ConditionProfile

/-- Descend an existing profile through one newly computed condition piece,
and prepend the new condition relation. -/
def extendPiece
    {source : Factor} {conditions : List Polynomial}
    (profile : ConditionProfile source conditions)
    (condition : Polynomial)
    (piece : ConditionPiece profile.factor condition) :
    ConditionProfile source (condition :: conditions) where
  factor := piece.factor
  cofactor := piece.cofactor * profile.cofactor
  factorization := by
    apply factorizationOfEvals
    intro point
    rw [eval_factorization profile.factorization point,
      eval_factorization piece.factorization point, eval_mul]
    ring1
  relations := ⟨condition, piece.relation⟩ ::
    profile.relations.map fun entry =>
      ⟨entry.1, entry.2.descend piece⟩
  conditions_eq := by
    have mapped :
        (profile.relations.map fun entry =>
          (⟨entry.1, entry.2.descend piece⟩ :
            Sigma fun queried : Polynomial =>
              ConditionRelation queried piece.factor)).map Sigma.fst =
          profile.relations.map Sigma.fst := by
      induction profile.relations with
      | nil => rfl
      | cons entry remaining inductionHypothesis =>
          simp only [List.map_cons]
          exact congrArg (List.cons entry.1) inductionHypothesis
    simp only [List.map_cons]
    rw [mapped, profile.conditions_eq]

/-- Split one profile against the next condition. -/
def extend
    {source : Factor} {conditions : List Polynomial}
    (profile : ConditionProfile source conditions)
    (condition : Polynomial) :
    List (ConditionProfile source (condition :: conditions)) :=
  let partition := splitAgainstCondition profile.factor condition
  partition.pieces.map fun piece => profile.extendPiece condition piece

theorem extend_nonempty
    {source : Factor} {conditions : List Polynomial}
    (profile : ConditionProfile source conditions)
    (condition : Polynomial) : profile.extend condition ≠ [] := by
  let partition := splitAgainstCondition profile.factor condition
  intro empty
  have piecesEmpty : partition.pieces = [] := by
    simpa only [extend, partition, List.map_eq_nil_iff] using empty
  exact partition.nonempty piecesEmpty

theorem extend_rootCoverage
    {source : Factor} {conditions : List Polynomial}
    (profile : ConditionProfile source conditions)
    (condition : Polynomial) (point : Coordinate) :
    profile.factor.polynomial.eval point = 0 ↔
      ∃ next ∈ profile.extend condition,
        next.factor.polynomial.eval point = 0 := by
  let partition := splitAgainstCondition profile.factor condition
  rw [partition.rootCoverage point]
  constructor
  · rintro ⟨piece, pieceMember, pieceZero⟩
    refine ⟨profile.extendPiece condition piece, ?_, ?_⟩
    · exact QuotientFreeList.mem_map.mpr ⟨piece, pieceMember, rfl⟩
    · exact pieceZero
  · rintro ⟨next, nextMember, nextZero⟩
    rw [extend, QuotientFreeList.mem_map] at nextMember
    rcases nextMember with ⟨piece, pieceMember, nextEq⟩
    subst next
    exact ⟨piece, pieceMember, nextZero⟩

end ConditionProfile

/-- Complete finite profile family after processing a displayed list of
conditions. -/
structure ConditionProfiles (factor : Factor) (conditions : List Polynomial)
    where
  profiles : List (ConditionProfile factor conditions)
  nonempty : profiles ≠ []
  rootCoverage : ∀ point : Coordinate,
    factor.polynomial.eval point = 0 ↔
      ∃ profile ∈ profiles, profile.factor.polynomial.eval point = 0

/-- Repeated executable gcd splitting.  Every final squarefree piece is
classified as equality-owned or explicitly coprime for every input
condition, and the finite family has exactly the original roots. -/
def classifyConditions (factor : Factor) :
    (conditions : List Polynomial) → ConditionProfiles factor conditions
  | [] => by
      let baseProfile : ConditionProfile factor [] :=
        { factor := factor
          cofactor := constant 1
          factorization := by
            apply factorizationOfEvals
            intro point
            simp only [eval_constant,
              RFAP.ConstructiveFraction.mul_one_direct]
          relations := []
          conditions_eq := rfl }
      exact
        { profiles := [baseProfile]
          nonempty := List.cons_ne_nil _ _
          rootCoverage := by
            intro point
            constructor
            · intro factorZero
              exact ⟨baseProfile, List.mem_cons_self, factorZero⟩
            · rintro ⟨profile, member, profileZero⟩
              have equal : profile = baseProfile :=
                List.mem_singleton.mp member
              subst profile
              exact profileZero }
  | condition :: remaining => by
      let prior := classifyConditions factor remaining
      let profiles := prior.profiles.flatMap fun profile =>
        profile.extend condition
      have profilesNonempty : profiles ≠ [] := by
        cases priorProfilesEq : prior.profiles with
        | nil => exact (prior.nonempty priorProfilesEq).elim
        | cons profile otherProfiles =>
            cases extensionEq : profile.extend condition with
            | nil =>
                exact (profile.extend_nonempty condition extensionEq).elim
            | cons next otherExtensions =>
                intro empty
                have profileMember : profile ∈ prior.profiles := by
                  rw [priorProfilesEq]
                  exact List.mem_cons_self
                have nextMember : next ∈ profile.extend condition := by
                  rw [extensionEq]
                  exact List.mem_cons_self
                have flattenedMember : next ∈ profiles :=
                  QuotientFreeList.mem_flatMap.mpr
                    ⟨profile, profileMember, nextMember⟩
                rw [empty] at flattenedMember
                exact List.not_mem_nil flattenedMember
      exact
        { profiles := profiles
          nonempty := profilesNonempty
          rootCoverage := by
            intro point
            constructor
            · intro factorZero
              rcases (prior.rootCoverage point).mp factorZero with
                ⟨profile, profileMember, profileZero⟩
              rcases (profile.extend_rootCoverage condition point).mp
                  profileZero with ⟨next, nextMember, nextZero⟩
              exact ⟨next,
                QuotientFreeList.mem_flatMap.mpr
                  ⟨profile, profileMember, nextMember⟩,
                nextZero⟩
            · rintro ⟨next, nextMember, nextZero⟩
              dsimp only [profiles] at nextMember
              rw [QuotientFreeList.mem_flatMap] at nextMember
              rcases nextMember with
                ⟨profile, profileMember, nextMember⟩
              have profileZero :=
                (profile.extend_rootCoverage condition point).mpr
                  ⟨next, nextMember, nextZero⟩
              exact (prior.rootCoverage point).mpr
                ⟨profile, profileMember, profileZero⟩ }

/-! ## Extending an existing profile by further finite conditions -/

/-- Prepend one displayed finite condition list without relying on reassociation
of generic list append in dependent profile types. -/
def prependConditions : List Polynomial → List Polynomial → List Polynomial
  | [], existing => existing
  | condition :: remaining, existing =>
      condition :: prependConditions remaining existing

/-- Complete finite refinements of one existing condition profile by an
additional displayed list.  Every output keeps the old relations, descended
through the new gcd pieces, and prepends the new relations. -/
structure ConditionProfileExtensions
    {source : Factor} {existing : List Polynomial}
    (profile : ConditionProfile source existing)
    (conditions : List Polynomial) where
  profiles : List
    (ConditionProfile source (prependConditions conditions existing))
  nonempty : profiles ≠ []
  rootCoverage : ∀ point : Coordinate,
    profile.factor.polynomial.eval point = 0 ↔
      ∃ next ∈ profiles, next.factor.polynomial.eval point = 0

/-- Repeatedly split one existing profile against further conditions.  This
is the finite composition operation used to add cleared CCL-formula atoms
after denominator and box-edge profiling. -/
def extendProfileConditions
    {source : Factor} {existing : List Polynomial}
    (profile : ConditionProfile source existing) :
    (conditions : List Polynomial) →
      ConditionProfileExtensions profile conditions
  | [] =>
      { profiles := [profile]
        nonempty := List.cons_ne_nil _ _
        rootCoverage := by
          intro point
          constructor
          · intro zero
            exact ⟨profile, List.mem_cons_self, zero⟩
          · rintro ⟨next, member, zero⟩
            have equal : next = profile := List.mem_singleton.mp member
            subst next
            exact zero }
  | condition :: remaining => by
      let prior := extendProfileConditions profile remaining
      let profiles := prior.profiles.flatMap fun priorProfile =>
        priorProfile.extend condition
      have profilesNonempty : profiles ≠ [] := by
        cases priorProfilesEq : prior.profiles with
        | nil => exact (prior.nonempty priorProfilesEq).elim
        | cons priorProfile otherProfiles =>
            cases extensionEq : priorProfile.extend condition with
            | nil =>
                exact (priorProfile.extend_nonempty condition extensionEq).elim
            | cons next otherExtensions =>
                intro empty
                have priorMember : priorProfile ∈ prior.profiles := by
                  rw [priorProfilesEq]
                  exact List.mem_cons_self
                have nextMember : next ∈ priorProfile.extend condition := by
                  rw [extensionEq]
                  exact List.mem_cons_self
                have flattenedMember : next ∈ profiles :=
                  QuotientFreeList.mem_flatMap.mpr
                    ⟨priorProfile, priorMember, nextMember⟩
                rw [empty] at flattenedMember
                exact List.not_mem_nil flattenedMember
      exact
        { profiles := profiles
          nonempty := profilesNonempty
          rootCoverage := by
            intro point
            constructor
            · intro profileZero
              rcases (prior.rootCoverage point).mp profileZero with
                ⟨priorProfile, priorMember, priorZero⟩
              rcases (priorProfile.extend_rootCoverage condition point).mp
                  priorZero with ⟨next, nextMember, nextZero⟩
              exact ⟨next,
                QuotientFreeList.mem_flatMap.mpr
                  ⟨priorProfile, priorMember, nextMember⟩,
                nextZero⟩
            · rintro ⟨next, nextMember, nextZero⟩
              change ConditionProfile source
                (condition :: prependConditions remaining existing) at next
              simp only [prependConditions] at nextMember
              have flattenedMember : next ∈ profiles := nextMember
              rw [QuotientFreeList.mem_flatMap] at flattenedMember
              rcases flattenedMember with
                ⟨priorProfile, priorMember, nextMember⟩
              have priorZero :=
                (priorProfile.extend_rootCoverage condition point).mpr
                  ⟨next, nextMember, nextZero⟩
              exact (prior.rootCoverage point).mpr
                ⟨priorProfile, priorMember, priorZero⟩ }

/-! ## Executable lookup in the final condition profiles -/

/-- Find the first final condition profile whose factor vanishes at the
displayed rational parameter. -/
def findRootProfileIndex
    {source : Factor} {conditions : List Polynomial}
    (point : Coordinate) :
    (profiles : List (ConditionProfile source conditions)) →
      Option (Fin profiles.length)
  | [] => none
  | profile :: remaining =>
      if profile.factor.polynomial.eval point = 0 then some 0
      else
        match findRootProfileIndex point remaining with
        | none => none
        | some index => some index.succ

theorem findRootProfileIndex_sound
    {source : Factor} {conditions : List Polynomial}
    (point : Coordinate) :
    ∀ (profiles : List (ConditionProfile source conditions))
      (index : Fin profiles.length),
      findRootProfileIndex point profiles = some index →
        (profiles.get index).factor.polynomial.eval point = 0
  | [], index, _ => Fin.elim0 index
  | profile :: remaining, index, found => by
      by_cases headZero : profile.factor.polynomial.eval point = 0
      · rw [findRootProfileIndex, if_pos headZero] at found
        have indexZero : index = 0 := Option.some.inj found.symm
        subst index
        exact headZero
      · rw [findRootProfileIndex, if_neg headZero] at found
        cases recursive : findRootProfileIndex point remaining with
        | none => rw [recursive] at found; contradiction
        | some tailIndex =>
            rw [recursive] at found
            have indexSucc : index = tailIndex.succ :=
              Option.some.inj found.symm
            subst index
            exact findRootProfileIndex_sound point remaining tailIndex
              recursive

theorem findRootProfileIndex_ne_none_of_exists
    {source : Factor} {conditions : List Polynomial}
    (point : Coordinate) :
    ∀ (profiles : List (ConditionProfile source conditions)),
      (∃ profile ∈ profiles,
        profile.factor.polynomial.eval point = 0) →
        findRootProfileIndex point profiles ≠ none := by
  intro profiles witness
  induction profiles with
  | nil =>
      rcases witness with ⟨profile, member, _⟩
      exact (List.not_mem_nil member).elim
  | cons profile remaining inductionHypothesis =>
      by_cases headZero : profile.factor.polynomial.eval point = 0
      · simp [findRootProfileIndex, headZero]
      · have tailExists : ∃ tailProfile ∈ remaining,
            tailProfile.factor.polynomial.eval point = 0 := by
          rcases witness with ⟨found, member, zero⟩
          rcases List.mem_cons.mp member with rfl | tailMember
          · exact (headZero zero).elim
          · exact ⟨found, tailMember, zero⟩
        have recursive := inductionHypothesis tailExists
        rw [findRootProfileIndex, if_neg headZero]
        cases found : findRootProfileIndex point remaining with
        | none => exact (recursive found).elim
        | some index => simp

/-- Proof-bearing output of the executable condition-profile scan. -/
structure LocatedConditionProfile
    {source : Factor} {conditions : List Polynomial}
    (profiles : ConditionProfiles source conditions)
    (point : Coordinate) where
  profile : ConditionProfile source conditions
  member : profile ∈ profiles.profiles
  zero : profile.factor.polynomial.eval point = 0

namespace ConditionProfiles

/-- Assign a displayed rational source-factor root to the first final
condition profile containing it. -/
def locateRoot
    {source : Factor} {conditions : List Polynomial}
    (profiles : ConditionProfiles source conditions)
    (point : Coordinate) (sourceZero : source.polynomial.eval point = 0) :
    LocatedConditionProfile profiles point := by
  have existsProfile := (profiles.rootCoverage point).mp sourceZero
  have foundNonempty := findRootProfileIndex_ne_none_of_exists point
    profiles.profiles existsProfile
  cases found : findRootProfileIndex point profiles.profiles with
  | none => exact (foundNonempty found).elim
  | some index =>
      exact
        { profile := profiles.profiles.get index
          member := List.get_mem profiles.profiles index
          zero := findRootProfileIndex_sound point profiles.profiles index
            found }

end ConditionProfiles

def factorProduct : List Factor → Polynomial
  | [] => constant 1
  | factor :: factors => factor.polynomial * factorProduct factors

/-- Remove the first occurrence of a displayed factor polynomial from a
finite factor product.  Matching only the polynomial data avoids requiring
decidable equality on the proof-bearing `Factor` record. -/
def factorCofactor (target : Polynomial) : List Factor → Polynomial
  | [] => constant 1
  | factor :: factors =>
      if factor.polynomial = target then factorProduct factors
      else factor.polynomial * factorCofactor target factors

/-- A factor selected from the finite decomposition can be split from the
product with an explicitly computed remaining cofactor. -/
theorem factorProduct_eval_eq_factor_mul_cofactor
    (factor : Factor) (factors : List Factor)
    (member : factor ∈ factors) (point : Coordinate) :
    (factorProduct factors).eval point =
      factor.polynomial.eval point *
        (factorCofactor factor.polynomial factors).eval point := by
  induction factors with
  | nil => simp at member
  | cons head factors inductionHypothesis =>
      by_cases samePolynomial : head.polynomial = factor.polynomial
      · simp only [factorProduct, factorCofactor, samePolynomial, if_pos,
          eval_mul]
      · have tailMember : factor ∈ factors := by
          rcases List.mem_cons.mp member with sameFactor | tailMember
          · subst factor
            exact (samePolynomial rfl).elim
          · exact tailMember
        simp only [factorProduct, factorCofactor, samePolynomial, if_false,
          eval_mul]
        rw [inductionHypothesis tailMember]
        ring1

theorem factorProduct_eval_eq_zero_iff
    (factors : List Factor) (point : Coordinate) :
    (factorProduct factors).eval point = 0 ↔
      ∃ factor ∈ factors, factor.polynomial.eval point = 0 := by
  induction factors with
  | nil =>
      constructor
      · intro productZero
        simp only [factorProduct, eval_constant] at productZero
        exact (RFAP.ConstructiveFraction.zero_ne_one productZero.symm).elim
      · rintro ⟨factor, member, _zero⟩
        exact (List.not_mem_nil member).elim
  | cons factor factors inductionHypothesis =>
      rw [factorProduct, eval_mul]
      constructor
      · intro productZero
        by_cases headZero : factor.polynomial.eval point = 0
        · exact ⟨factor, List.mem_cons_self, headZero⟩
        · have tailZero : (factorProduct factors).eval point = 0 := by
            by_cases tailZero : (factorProduct factors).eval point = 0
            · exact tailZero
            · exact (RFAP.ConstructiveFraction.mul_ne_zero_direct
                headZero tailZero productZero).elim
          rcases inductionHypothesis.mp tailZero with
            ⟨found, member, zero⟩
          exact ⟨found, List.mem_cons_of_mem factor member, zero⟩
      · rintro ⟨found, member, zero⟩
        rcases List.mem_cons.mp member with rfl | tailMember
        · rw [zero, RFAP.ConstructiveFraction.zero_mul_direct]
        · rw [(inductionHypothesis.mpr ⟨found, tailMember, zero⟩),
            RFAP.ConstructiveFraction.mul_zero_direct]

/-- Proof-bearing output of the executable first-zero-factor scan. -/
structure LocatedFactor (factors : List Factor) (point : Coordinate) where
  factor : Factor
  member : factor ∈ factors
  zero : factor.polynomial.eval point = 0

def locateFactor
    (factors : List Factor) (point : Coordinate)
    (productZero : (factorProduct factors).eval point = 0) :
    LocatedFactor factors point := by
  match factors with
  | [] =>
      simp only [factorProduct, eval_constant] at productZero
      exact (RFAP.ConstructiveFraction.zero_ne_one productZero.symm).elim
  | factor :: remaining =>
      by_cases headZero : factor.polynomial.eval point = 0
      · exact ⟨factor, List.mem_cons_self, headZero⟩
      · have tailZero : (factorProduct remaining).eval point = 0 := by
          rw [factorProduct, eval_mul] at productZero
          by_cases tailZero : (factorProduct remaining).eval point = 0
          · exact tailZero
          · exact (RFAP.ConstructiveFraction.mul_ne_zero_direct
              headZero tailZero productZero).elim
        let located := locateFactor remaining point tailZero
        exact ⟨located.factor, List.mem_cons_of_mem factor located.member,
          located.zero⟩

/-- Complete positive-degree squarefree occurrence decomposition. -/
structure Decomposition (p : Polynomial) where
  factors : List Factor
  factorsNonempty : factors ≠ []
  evalIdentity : ∀ point : Coordinate,
    p.eval point = (factorProduct factors).eval point
  degreeSum : (factors.map fun factor => factor.polynomial.natDegree).sum =
    p.natDegree

namespace Decomposition

def locateRoot
    {p : Polynomial} (decomposition : Decomposition p)
    (point : Coordinate) (root : p.eval point = 0) :
    LocatedFactor decomposition.factors point := by
  apply locateFactor decomposition.factors point
  rw [← decomposition.evalIdentity point]
  exact root

theorem eval_eq_zero_iff
    {p : Polynomial} (decomposition : Decomposition p)
    (point : Coordinate) :
    p.eval point = 0 ↔
      ∃ factor ∈ decomposition.factors,
        factor.polynomial.eval point = 0 := by
  rw [decomposition.evalIdentity point]
  exact factorProduct_eval_eq_zero_iff decomposition.factors point

end Decomposition

/-- Degree-recursive decomposition by the displayed derivative gcd. -/
def decomposeNormalized
    (p : Polynomial) (pNormalized : p.normalize = p)
    (pNonzero : p.isZero = false) (pPositive : 0 < p.natDegree) :
    Decomposition p := by
  let derivative := RFAP.ComputableDerivative.derivative p
  let result := RFAP.ComputableGCD.extendedGCD p derivative
  have derivativeNonzero : derivative.isZero = false := by
    exact CCL.RationalDerivativeDegree.derivative_isZero_false
      pNonzero pPositive
  have gcdNonzero : result.gcd.isZero = false :=
    result.nonzero (Or.inl pNonzero)
  if degreeZero : result.gcd.natDegree = 0 then
    let squarefree : SquarefreeCertificate p :=
      certificateOfConstantGCD p derivative gcdNonzero degreeZero
    exact
      { factors :=
          [{ polynomial := p
             normalized := pNormalized
             nonzero := pNonzero
             degreePositive := pPositive
             squarefree := squarefree }]
        factorsNonempty := by simp
        evalIdentity := by
          intro point
          simp only [factorProduct, eval_mul, eval_constant,
            RFAP.ConstructiveFraction.mul_one_direct]
        degreeSum := by simp }
  else
    let divisor := result.gcd
    let cofactor := result.pFactor
    have derivativeDegree : derivative.natDegree < p.natDegree :=
      RFAP.ComputableDerivative.derivative_natDegree_lt pNonzero pPositive
    have divisorProper : divisor.natDegree < p.natDegree :=
      (result.degreeLeRight derivativeNonzero).trans_lt derivativeDegree
    have divisorPositive : 0 < divisor.natDegree :=
      Nat.pos_of_ne_zero degreeZero
    have factorization : Factorization p divisor cofactor := by
      apply factorizationOfEvals
      exact result.pIdentity
    have cofactorNonzero : cofactor.isZero = false :=
      right_isZero_false pNonzero pNormalized factorization
    have degreeBalance :
        divisor.natDegree + cofactor.natDegree = p.natDegree :=
      factor_natDegree_add pNonzero pNormalized gcdNonzero cofactorNonzero
        factorization
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
    let leftDecomposition := decomposeNormalized divisor result.normalized
      gcdNonzero divisorPositive
    let rightDecomposition := decomposeNormalized cofactor
      result.pFactorNormalized cofactorNonzero cofactorPositive
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
              result.pIdentity point
            _ = (factorProduct leftDecomposition.factors).eval point *
                (factorProduct rightDecomposition.factors).eval point := by
              rw [← leftDecomposition.evalIdentity,
                ← rightDecomposition.evalIdentity]
            _ = (factorProduct
                (leftDecomposition.factors ++
                  rightDecomposition.factors)).eval point := by
              induction leftDecomposition.factors with
              | nil => simp [factorProduct]
              | cons factor factors inductionHypothesis =>
                  simp only [List.cons_append, factorProduct, eval_mul]
                  calc
                    (factor.polynomial.eval point *
                        (factorProduct factors).eval point) *
                          (factorProduct rightDecomposition.factors).eval point =
                      factor.polynomial.eval point *
                        ((factorProduct factors).eval point *
                          (factorProduct rightDecomposition.factors).eval
                            point) := by ring1
                    _ = factor.polynomial.eval point *
                        (factorProduct
                          (factors ++ rightDecomposition.factors)).eval point :=
                      congrArg (factor.polynomial.eval point * ·)
                        inductionHypothesis
        degreeSum := by
          simp only [List.map_append, List.sum_append,
            leftDecomposition.degreeSum, rightDecomposition.degreeSum]
          exact degreeBalance }
termination_by p.natDegree
decreasing_by
  · exact divisorProper
  · exact cofactorProper

/-- Total decomposition of a represented nonzero positive-degree coordinate
polynomial. -/
def decompose
    (p : Polynomial) (pNonzero : p.isZero = false)
    (pPositive : 0 < p.natDegree) : Decomposition p.normalize :=
  decomposeNormalized p.normalize (normalize_normalize p)
    (by simpa only [isZero_normalize])
    (by simpa only [natDegree_normalize])

end CCL.CoordinateFactorization
