import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.SpreadChebyshev
import mathlib.RFAP.FiniteBinomial
import mathlib.RFAP.QuadraticPair

/-!
# Divine Proportions, Chapter 8: the alternating binomial formula

Exercise 8.6 is proved by expanding the two finite powers in Theorem 59 and
pairing their even and odd terms.  Every sum below has an explicit natural
bound and is implemented by primitive recursion.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem neg_pow_even {R : Type*} [CommRing R]
    (value : R) (half : Nat) :
    (-value) ^ (half + half) = value ^ (half + half) := by
  calc
    (-value) ^ (half + half) = (-value) ^ (2 * half) := by
      congr 1
      omega0
    _ = ((-value) ^ 2) ^ half := by rw [pow_mul]
    _ = (value ^ 2) ^ half := by
      congr 1
      ring1
    _ = value ^ (2 * half) := by rw [pow_mul]
    _ = value ^ (half + half) := by
      congr 1
      omega0

private theorem neg_pow_odd {R : Type*} [CommRing R]
    (value : R) (half : Nat) :
    (-value) ^ (half + half + 1) = -value ^ (half + half + 1) := by
  calc
    (-value) ^ (half + half + 1) =
        (-value) ^ (half + half) * (-value) := by rw [pow_succ]
    _ = value ^ (half + half) * (-value) := by rw [neg_pow_even]
    _ = -(value ^ (half + half) * value) := by ring1
    _ = -value ^ (half + half + 1) := by rw [pow_succ]

private def binomialTerm {R : Type*} [CommRing R]
    (exponent : Nat) (center offset : R) (index : Nat) : R :=
  offset ^ index * center ^ (exponent - index) *
    (exponent.choose index : R)

private theorem pairedBinomialTerm_even
    {R : Type*} [CommRing R]
    (exponent half : Nat) (center offset : R) :
    binomialTerm exponent center offset (half + half) +
        binomialTerm exponent center (-offset) (half + half) =
      2 * binomialTerm exponent center offset (half + half) := by
  unfold binomialTerm
  rw [neg_pow_even]
  ring1

private theorem pairedBinomialTerm_odd
    {R : Type*} [CommRing R]
    (exponent half : Nat) (center offset : R) :
    binomialTerm exponent center offset (half + half + 1) +
        binomialTerm exponent center (-offset) (half + half + 1) = 0 := by
  unfold binomialTerm
  rw [neg_pow_odd]
  ring1

/-- The symmetric binomial expansion in even degree, with every odd term
cancelled and every even term retained exactly once. -/
theorem symmetric_binomial_even
    {R : Type*} [CommRing R]
    (half : Nat) (center offset : R) :
    (center + offset) ^ (half + half) +
        (center - offset) ^ (half + half) =
      2 * RFAP.finitePrefixSum (half + 1) (fun index =>
        binomialTerm (half + half) center offset (index + index)) := by
  let exponent := half + half
  let combined := fun index : Nat =>
    binomialTerm exponent center offset index +
      binomialTerm exponent center (-offset) index
  let evenTerm := fun index : Nat =>
    binomialTerm exponent center offset (index + index)
  have expansion :
      (center + offset) ^ exponent + (center - offset) ^ exponent =
        RFAP.finitePrefixSum (exponent + 1) combined := by
    calc
      (center + offset) ^ exponent + (center - offset) ^ exponent =
          (center + offset) ^ exponent +
            (center + -offset) ^ exponent := by
              congr 2
              ring1
      _ = RFAP.finiteBinomialExpansion exponent center offset +
          RFAP.finiteBinomialExpansion exponent center (-offset) := by
            rw [RFAP.finite_binomial_theorem,
              RFAP.finite_binomial_theorem]
      _ = RFAP.finitePrefixSum (exponent + 1) combined := by
        unfold RFAP.finiteBinomialExpansion combined binomialTerm
        rw [RFAP.finitePrefixSum_add]
  have grouped :
      RFAP.finitePrefixSum half (fun index =>
          combined (index + index) + combined (index + index + 1)) =
        RFAP.finitePrefixSum half (fun index => 2 * evenTerm index) := by
    apply RFAP.finitePrefixSum_congr
    intro index indexBound
    unfold combined evenTerm
    rw [pairedBinomialTerm_even, pairedBinomialTerm_odd]
    ring1
  calc
    (center + offset) ^ (half + half) +
        (center - offset) ^ (half + half) =
      RFAP.finitePrefixSum (exponent + 1) combined := expansion
    _ = RFAP.finitePrefixSum half (fun index =>
          combined (index + index) + combined (index + index + 1)) +
        combined (half + half) := by
          unfold exponent
          rw [RFAP.finitePrefixSum_pairs_and_last]
    _ = RFAP.finitePrefixSum half (fun index => 2 * evenTerm index) +
        2 * evenTerm half := by
          rw [grouped]
          unfold combined evenTerm
          rw [pairedBinomialTerm_even]
    _ = 2 * RFAP.finitePrefixSum half evenTerm +
        2 * evenTerm half := by
          rw [RFAP.finitePrefixSum_mul_left]
    _ = 2 * RFAP.finitePrefixSum (half + 1) evenTerm := by
          rw [RFAP.finitePrefixSum_succ_last]
          ring1
    _ = 2 * RFAP.finitePrefixSum (half + 1) (fun index =>
        binomialTerm (half + half) center offset (index + index)) := rfl

/-- The matching symmetric expansion in odd degree. -/
theorem symmetric_binomial_odd
    {R : Type*} [CommRing R]
    (half : Nat) (center offset : R) :
    (center + offset) ^ (half + half + 1) +
        (center - offset) ^ (half + half + 1) =
      2 * RFAP.finitePrefixSum (half + 1) (fun index =>
        binomialTerm (half + half + 1) center offset (index + index)) := by
  let exponent := half + half + 1
  let combined := fun index : Nat =>
    binomialTerm exponent center offset index +
      binomialTerm exponent center (-offset) index
  let evenTerm := fun index : Nat =>
    binomialTerm exponent center offset (index + index)
  have expansion :
      (center + offset) ^ exponent + (center - offset) ^ exponent =
        RFAP.finitePrefixSum (exponent + 1) combined := by
    calc
      (center + offset) ^ exponent + (center - offset) ^ exponent =
          (center + offset) ^ exponent +
            (center + -offset) ^ exponent := by
              congr 2
              ring1
      _ = RFAP.finiteBinomialExpansion exponent center offset +
          RFAP.finiteBinomialExpansion exponent center (-offset) := by
            rw [RFAP.finite_binomial_theorem,
              RFAP.finite_binomial_theorem]
      _ = RFAP.finitePrefixSum (exponent + 1) combined := by
        unfold RFAP.finiteBinomialExpansion combined binomialTerm
        rw [RFAP.finitePrefixSum_add]
  have grouped :
      RFAP.finitePrefixSum (half + 1) (fun index =>
          combined (index + index) + combined (index + index + 1)) =
        RFAP.finitePrefixSum (half + 1)
          (fun index => 2 * evenTerm index) := by
    apply RFAP.finitePrefixSum_congr
    intro index indexBound
    unfold combined evenTerm
    rw [pairedBinomialTerm_even, pairedBinomialTerm_odd]
    ring1
  calc
    (center + offset) ^ (half + half + 1) +
        (center - offset) ^ (half + half + 1) =
      RFAP.finitePrefixSum (exponent + 1) combined := expansion
    _ = RFAP.finitePrefixSum (half + 1) (fun index =>
        combined (index + index) + combined (index + index + 1)) := by
          unfold exponent
          rw [show half + half + 1 + 1 =
            (half + 1) + (half + 1) by omega0]
          rw [RFAP.finitePrefixSum_pairs]
    _ = RFAP.finitePrefixSum (half + 1)
        (fun index => 2 * evenTerm index) := grouped
    _ = 2 * RFAP.finitePrefixSum (half + 1) evenTerm := by
          rw [RFAP.finitePrefixSum_mul_left]
    _ = 2 * RFAP.finitePrefixSum (half + 1) (fun index =>
        binomialTerm (half + half + 1) center offset (index + index)) := rfl

private theorem pairedBinomialTerm_even_difference
    {R : Type*} [CommRing R]
    (exponent half : Nat) (center offset : R) :
    binomialTerm exponent center offset (half + half) -
        binomialTerm exponent center (-offset) (half + half) = 0 := by
  unfold binomialTerm
  rw [neg_pow_even]
  ring1

private theorem pairedBinomialTerm_odd_difference
    {R : Type*} [CommRing R]
    (exponent half : Nat) (center offset : R) :
    binomialTerm exponent center offset (half + half + 1) -
        binomialTerm exponent center (-offset) (half + half + 1) =
      2 * offset *
        (offset ^ (half + half) *
          center ^ (exponent - (half + half + 1)) *
            (exponent.choose (half + half + 1) : R)) := by
  unfold binomialTerm
  rw [neg_pow_odd, pow_succ]
  ring1

/-- The antisymmetric odd-degree binomial expansion.  Pairing adjacent
indices cancels every even term and extracts one explicit offset from every
odd term. -/
theorem antisymmetric_binomial_odd
    {R : Type*} [CommRing R]
    (half : Nat) (center offset : R) :
    (center + offset) ^ (half + half + 1) -
        (center - offset) ^ (half + half + 1) =
      2 * offset * RFAP.finitePrefixSum (half + 1) (fun index =>
        offset ^ (index + index) *
          center ^ (half + half + 1 - (index + index + 1)) *
            ((half + half + 1).choose (index + index + 1) : R)) := by
  let exponent := half + half + 1
  let difference := fun index : Nat =>
    binomialTerm exponent center offset index -
      binomialTerm exponent center (-offset) index
  let oddCore := fun index : Nat =>
    offset ^ (index + index) *
      center ^ (exponent - (index + index + 1)) *
        (exponent.choose (index + index + 1) : R)
  have expansion :
      (center + offset) ^ exponent - (center - offset) ^ exponent =
        RFAP.finitePrefixSum (exponent + 1) difference := by
    calc
      (center + offset) ^ exponent - (center - offset) ^ exponent =
          (center + offset) ^ exponent -
            (center + -offset) ^ exponent := by
              congr 2
              ring1
      _ = RFAP.finiteBinomialExpansion exponent center offset -
          RFAP.finiteBinomialExpansion exponent center (-offset) := by
            rw [RFAP.finite_binomial_theorem,
              RFAP.finite_binomial_theorem]
      _ = RFAP.finitePrefixSum (exponent + 1) difference := by
        unfold RFAP.finiteBinomialExpansion difference binomialTerm
        rw [RFAP.finitePrefixSum_sub]
  have grouped :
      RFAP.finitePrefixSum (half + 1) (fun index =>
          difference (index + index) + difference (index + index + 1)) =
        RFAP.finitePrefixSum (half + 1)
          (fun index => 2 * offset * oddCore index) := by
    apply RFAP.finitePrefixSum_congr
    intro index indexBound
    unfold difference oddCore
    rw [pairedBinomialTerm_even_difference,
      pairedBinomialTerm_odd_difference]
    ring1
  calc
    (center + offset) ^ (half + half + 1) -
        (center - offset) ^ (half + half + 1) =
      RFAP.finitePrefixSum (exponent + 1) difference := expansion
    _ = RFAP.finitePrefixSum (half + 1) (fun index =>
        difference (index + index) + difference (index + index + 1)) := by
          unfold exponent
          rw [show half + half + 1 + 1 =
            (half + 1) + (half + 1) by omega0]
          rw [RFAP.finitePrefixSum_pairs]
    _ = RFAP.finitePrefixSum (half + 1)
        (fun index => 2 * offset * oddCore index) := grouped
    _ = 2 * offset * RFAP.finitePrefixSum (half + 1) oddCore := by
          rw [RFAP.finitePrefixSum_mul_left]
    _ = 2 * offset * RFAP.finitePrefixSum (half + 1) (fun index =>
        offset ^ (index + index) *
          center ^ (half + half + 1 - (index + index + 1)) *
            ((half + half + 1).choose (index + index + 1) : R)) := rfl

/-- The `k`th displayed term in Exercise 8.6. -/
def spreadBinomialTerm
    (exponent : Nat) (center radialSquare : K) (index : Nat) : K :=
  (-radialSquare) ^ index *
    center ^ (exponent - (index + index)) *
      (exponent.choose (index + index) : K)

/-- The explicitly bounded alternating even-binomial prefix in Exercise 8.6. -/
def spreadBinomialExpansion
    (exponent termCount : Nat) (center radialSquare : K) : K :=
  RFAP.finitePrefixSum termCount
    (spreadBinomialTerm exponent center radialSquare)

private theorem eq_of_mul_eq_mul_left
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = 1 * left := by rw [one_mul]
    _ = (factor * factor⁻¹) * left := by rw [factorCancel]
    _ = factor⁻¹ * (factor * left) := by ring1
    _ = factor⁻¹ * (factor * right) := by rw [productsEqual]
    _ = (factor * factor⁻¹) * right := by ring1
    _ = right := by rw [factorCancel, one_mul]

theorem finitePrefixSum_quadraticPair_scalar
    {R : Type*} [CommRing R]
    (radialSquare : R) (count : Nat) (term : Nat → R) :
    RFAP.finitePrefixSum count (fun index =>
        RFAP.QuadraticPair.scalar (radialSquare := radialSquare)
          (term index)) =
      RFAP.QuadraticPair.scalar
        (RFAP.finitePrefixSum count term) := by
  induction count generalizing term with
  | zero =>
      simp only [RFAP.finitePrefixSum_zero,
        RFAP.QuadraticPair.scalar_zero]
  | succ count inductionHypothesis =>
      change
        RFAP.QuadraticPair.scalar (term 0) +
            RFAP.finitePrefixSum count (fun index =>
              RFAP.QuadraticPair.scalar (term (index + 1))) =
          RFAP.QuadraticPair.scalar
            (term 0 + RFAP.finitePrefixSum count
              (fun index => term (index + 1)))
      rw [inductionHypothesis, RFAP.QuadraticPair.scalar_add]

private theorem binomialTerm_quadraticPair
    (exponent index : Nat) (center radialSquare : K) :
    binomialTerm exponent
        (RFAP.QuadraticPair.scalar (radialSquare := radialSquare) center)
        (RFAP.QuadraticPair.generator (K := K)
          (radialSquare := radialSquare))
        (index + index) =
      RFAP.QuadraticPair.scalar
        (spreadBinomialTerm exponent center radialSquare index) := by
  unfold binomialTerm spreadBinomialTerm
  rw [RFAP.QuadraticPair.generator_even_power]
  rw [← RFAP.QuadraticPair.scalar_pow]
  rw [RFAP.QuadraticPair.natCast_eq_scalar]
  rw [← RFAP.QuadraticPair.scalar_mul,
    ← RFAP.QuadraticPair.scalar_mul]

private theorem quadraticPair_power_recurrence
    {R : Type*} [CommRing R] (root center : R)
    (quadratic : root ^ 2 = 2 * center * root - 1)
    (index : Nat) :
    root ^ (index + 2) =
      2 * center * root ^ (index + 1) - root ^ index := by
  calc
    root ^ (index + 2) = root ^ index * root ^ 2 := by rw [pow_add]
    _ = root ^ index * (2 * center * root - 1) := by rw [quadratic]
    _ = 2 * center * (root ^ index * root) - root ^ index := by ring1
    _ = 2 * center * root ^ (index + 1) - root ^ index := by rw [pow_succ]

private theorem quadraticPair_chebyshev_trace
    (index : Nat) (center radialSquare : K)
    (radialEquation : radialSquare = 1 - center ^ 2) :
    let scalar :=
      RFAP.QuadraticPair.scalar (radialSquare := radialSquare)
    let generator :=
      RFAP.QuadraticPair.generator (K := K)
        (radialSquare := radialSquare)
    (scalar center + generator) ^ index +
        (scalar center - generator) ^ index =
      scalar (2 * chebyshevFirst index center) := by
  dsimp only
  let scalar :=
    RFAP.QuadraticPair.scalar (radialSquare := radialSquare)
  let generator :=
    RFAP.QuadraticPair.generator (K := K)
      (radialSquare := radialSquare)
  let positive := scalar center + generator
  let negative := scalar center - generator
  have positiveQuadratic :
      positive ^ 2 = 2 * scalar center * positive - 1 := by
    unfold positive scalar generator
    rw [RFAP.QuadraticPair.two_eq_scalar]
    apply RFAP.QuadraticPair.ext <;>
      simp only [pow_two, RFAP.QuadraticPair.mul_re,
        RFAP.QuadraticPair.mul_im, RFAP.QuadraticPair.add_re,
        RFAP.QuadraticPair.add_im, RFAP.QuadraticPair.sub_re,
        RFAP.QuadraticPair.sub_im, RFAP.QuadraticPair.scalar_re,
        RFAP.QuadraticPair.scalar_im, RFAP.QuadraticPair.generator_re,
        RFAP.QuadraticPair.generator_im, RFAP.QuadraticPair.one_re,
        RFAP.QuadraticPair.one_im]
    all_goals rw [radialEquation]
    all_goals ring1
  have negativeQuadratic :
      negative ^ 2 = 2 * scalar center * negative - 1 := by
    unfold negative scalar generator
    rw [RFAP.QuadraticPair.two_eq_scalar]
    apply RFAP.QuadraticPair.ext <;>
      simp only [pow_two, RFAP.QuadraticPair.mul_re,
        RFAP.QuadraticPair.mul_im, RFAP.QuadraticPair.sub_re,
        RFAP.QuadraticPair.sub_im, RFAP.QuadraticPair.scalar_re,
        RFAP.QuadraticPair.scalar_im, RFAP.QuadraticPair.generator_re,
        RFAP.QuadraticPair.generator_im, RFAP.QuadraticPair.one_re,
        RFAP.QuadraticPair.one_im]
    all_goals rw [radialEquation]
    all_goals ring1
  let traceAt := fun current : Nat =>
    positive ^ current + negative ^ current =
      scalar (2 * chebyshevFirst current center)
  have allPairs : ∀ current : Nat,
      traceAt current ∧ traceAt (current + 1) := by
    intro current
    induction current with
    | zero =>
        constructor
        · unfold traceAt positive negative scalar generator chebyshevFirst
          apply RFAP.QuadraticPair.ext <;>
            simp only [pow_zero, RFAP.QuadraticPair.add_re,
              RFAP.QuadraticPair.add_im, RFAP.QuadraticPair.one_re,
              RFAP.QuadraticPair.one_im, RFAP.QuadraticPair.scalar_re,
              RFAP.QuadraticPair.scalar_im]
          all_goals ring1
        · unfold traceAt positive negative scalar generator chebyshevFirst
          apply RFAP.QuadraticPair.ext <;>
            simp only [Nat.zero_add, pow_one, RFAP.QuadraticPair.add_re,
              RFAP.QuadraticPair.add_im, RFAP.QuadraticPair.sub_re,
              RFAP.QuadraticPair.sub_im, RFAP.QuadraticPair.scalar_re,
              RFAP.QuadraticPair.scalar_im,
              RFAP.QuadraticPair.generator_re,
              RFAP.QuadraticPair.generator_im]
          all_goals ring1
    | succ current inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · unfold traceAt
          rw [show Nat.succ current + 1 = current + 2 by omega0]
          rw [quadraticPair_power_recurrence positive (scalar center)
              positiveQuadratic,
            quadraticPair_power_recurrence negative (scalar center)
              negativeQuadratic]
          calc
            (2 * scalar center * positive ^ (current + 1) -
                  positive ^ current) +
                (2 * scalar center * negative ^ (current + 1) -
                  negative ^ current) =
              2 * scalar center *
                  (positive ^ (current + 1) + negative ^ (current + 1)) -
                (positive ^ current + negative ^ current) := by ring1
            _ = 2 * scalar center *
                  scalar (2 * chebyshevFirst (current + 1) center) -
                scalar (2 * chebyshevFirst current center) := by
                  rw [inductionHypothesis.1, inductionHypothesis.2]
            _ = scalar
                (2 * center * (2 * chebyshevFirst (current + 1) center) -
                  2 * chebyshevFirst current center) := by
                  rw [RFAP.QuadraticPair.two_eq_scalar]
                  rw [← RFAP.QuadraticPair.scalar_mul,
                    ← RFAP.QuadraticPair.scalar_mul,
                    ← RFAP.QuadraticPair.scalar_sub]
            _ = scalar (2 * chebyshevFirst (current + 2) center) := by
                  rw [chebyshevFirst_succ_succ]
                  congr 1
                  ring1
  exact (allPairs index).1

/-- The finite quadratic-pair trace formula for the first Chebyshev
polynomial.  It exposes the constructive two-coordinate calculation used by
the spread-binomial formulas, so later finite-field arguments can supply
explicit powers of the two norm-one conjugates without choosing roots. -/
theorem chebyshevFirst_quadraticPair_trace
    (index : Nat) (center radialSquare : K)
    (radialEquation : radialSquare = 1 - center ^ 2) :
    let scalar :=
      RFAP.QuadraticPair.scalar (radialSquare := radialSquare)
    let generator :=
      RFAP.QuadraticPair.generator (K := K)
        (radialSquare := radialSquare)
    (scalar center + generator) ^ index +
        (scalar center - generator) ^ index =
      scalar (2 * chebyshevFirst index center) :=
  quadraticPair_chebyshev_trace index center radialSquare radialEquation

private theorem chebyshev_eq_spreadBinomialExpansion
    (exponent termCount : Nat) (center radialSquare : K)
    (twoNonzero : (2 : K) ≠ 0)
    (radialEquation : radialSquare = 1 - center ^ 2)
    (symmetricExpansion :
      let scalar :=
        RFAP.QuadraticPair.scalar (radialSquare := radialSquare)
      let generator :=
        RFAP.QuadraticPair.generator (K := K)
          (radialSquare := radialSquare)
      (scalar center + generator) ^ exponent +
          (scalar center - generator) ^ exponent =
        2 * RFAP.finitePrefixSum termCount (fun index =>
          binomialTerm exponent (scalar center) generator
            (index + index))) :
    chebyshevFirst exponent center =
      spreadBinomialExpansion exponent termCount center radialSquare := by
  dsimp only at symmetricExpansion
  let scalar :=
    RFAP.QuadraticPair.scalar (radialSquare := radialSquare)
  let generator :=
    RFAP.QuadraticPair.generator (K := K)
      (radialSquare := radialSquare)
  have termConversion :
      RFAP.finitePrefixSum termCount (fun index =>
          binomialTerm exponent (scalar center) generator
            (index + index)) =
        scalar (spreadBinomialExpansion exponent termCount center
          radialSquare) := by
    unfold spreadBinomialExpansion
    calc
      RFAP.finitePrefixSum termCount (fun index =>
          binomialTerm exponent (scalar center) generator
            (index + index)) =
        RFAP.finitePrefixSum termCount (fun index =>
          scalar (spreadBinomialTerm exponent center radialSquare index)) := by
            apply RFAP.finitePrefixSum_congr
            intro index indexBound
            exact binomialTerm_quadraticPair exponent index center radialSquare
      _ = scalar (RFAP.finitePrefixSum termCount
          (spreadBinomialTerm exponent center radialSquare)) :=
        finitePrefixSum_quadraticPair_scalar radialSquare termCount _
  have trace := quadraticPair_chebyshev_trace exponent center radialSquare
    radialEquation
  have scalarProducts :
      scalar (2 * chebyshevFirst exponent center) =
        scalar (2 * spreadBinomialExpansion exponent termCount center
          radialSquare) := by
    calc
      scalar (2 * chebyshevFirst exponent center) =
          (scalar center + generator) ^ exponent +
            (scalar center - generator) ^ exponent := trace.symm
      _ = 2 * RFAP.finitePrefixSum termCount (fun index =>
          binomialTerm exponent (scalar center) generator
            (index + index)) := symmetricExpansion
      _ = 2 * scalar (spreadBinomialExpansion exponent termCount center
          radialSquare) := by rw [termConversion]
      _ = scalar (2 * spreadBinomialExpansion exponent termCount center
          radialSquare) := by
            rw [RFAP.QuadraticPair.two_eq_scalar]
            rw [← RFAP.QuadraticPair.scalar_mul]
  have productsEqual :
      2 * chebyshevFirst exponent center =
        2 * spreadBinomialExpansion exponent termCount center radialSquare :=
    congrArg RFAP.QuadraticPair.re scalarProducts
  exact eq_of_mul_eq_mul_left twoNonzero productsEqual

private theorem exercise_8_6_unconditional_core
    (exponent termCount : Nat) (value : K)
    (twoNonzero : (2 : K) ≠ 0)
    (symmetricExpansion :
      let center := 1 - 2 * value
      let radialSquare := 4 * value * (1 - value)
      let scalar :=
        RFAP.QuadraticPair.scalar (radialSquare := radialSquare)
      let generator :=
        RFAP.QuadraticPair.generator (K := K)
          (radialSquare := radialSquare)
      (scalar center + generator) ^ exponent +
          (scalar center - generator) ^ exponent =
        2 * RFAP.finitePrefixSum termCount (fun index =>
          binomialTerm exponent (scalar center) generator
            (index + index))) :
    1 - 2 * spreadPolynomial exponent value =
      spreadBinomialExpansion exponent termCount
        (1 - 2 * value) (4 * value * (1 - value)) := by
  dsimp only at symmetricExpansion
  have radialEquation :
      4 * value * (1 - value) = 1 - (1 - 2 * value) ^ 2 := by ring1
  have binomialFormula := chebyshev_eq_spreadBinomialExpansion
    exponent termCount (1 - 2 * value) (4 * value * (1 - value))
    twoNonzero radialEquation symmetricExpansion
  have cleared := exercise_8_4_cleared exponent value
  calc
    1 - 2 * spreadPolynomial exponent value =
        chebyshevFirst exponent (1 - 2 * value) := by rw [cleared]; ring1
    _ = spreadBinomialExpansion exponent termCount
        (1 - 2 * value) (4 * value * (1 - value)) := binomialFormula

/-- Exercise 8.6 for the even index `n=2l`; the final requested term is
`(-b)^l`.  The finite quadratic-pair proof removes all root hypotheses. -/
theorem exercise_8_6_even
    (half : Nat) (value : K) (twoNonzero : (2 : K) ≠ 0) :
    1 - 2 * spreadPolynomial (half + half) value =
      spreadBinomialExpansion (half + half) (half + 1)
        (1 - 2 * value) (4 * value * (1 - value)) :=
  exercise_8_6_unconditional_core (half + half) (half + 1) value twoNonzero
    (symmetric_binomial_even half
      (RFAP.QuadraticPair.scalar
        (radialSquare := 4 * value * (1 - value)) (1 - 2 * value))
      (RFAP.QuadraticPair.generator (K := K)
        (radialSquare := 4 * value * (1 - value))))

/-- Exercise 8.6 for the odd index `n=2l+1`; the final requested term is
`n*a*(-b)^l`.  The finite quadratic-pair proof removes all root hypotheses. -/
theorem exercise_8_6_odd
    (half : Nat) (value : K) (twoNonzero : (2 : K) ≠ 0) :
    1 - 2 * spreadPolynomial (half + half + 1) value =
      spreadBinomialExpansion (half + half + 1) (half + 1)
        (1 - 2 * value) (4 * value * (1 - value)) :=
  exercise_8_6_unconditional_core (half + half + 1) (half + 1) value
    twoNonzero
    (symmetric_binomial_odd half
      (RFAP.QuadraticPair.scalar
        (radialSquare := 4 * value * (1 - value)) (1 - 2 * value))
      (RFAP.QuadraticPair.generator (K := K)
        (radialSquare := 4 * value * (1 - value))))

/-- The last term of the even expansion is exactly `(-b)^l`. -/
theorem spreadBinomialTerm_even_last
    (half : Nat) (center radialSquare : K) :
    spreadBinomialTerm (half + half) center radialSquare half =
      (-radialSquare) ^ half := by
  unfold spreadBinomialTerm
  rw [show half + half - (half + half) = 0 by omega0,
    RFAP.finite_choose_self, pow_zero, Nat.cast_one]
  ring1

/-- The last term of the odd expansion is exactly `(2l+1)a(-b)^l`. -/
theorem spreadBinomialTerm_odd_last
    (half : Nat) (center radialSquare : K) :
    spreadBinomialTerm (half + half + 1) center radialSquare half =
      (half + half + 1 : K) * center * (-radialSquare) ^ half := by
  unfold spreadBinomialTerm
  rw [show half + half + 1 - (half + half) = 1 by omega0,
    show (half + half + 1).choose (half + half) = half + half + 1 by
      exact RFAP.finite_choose_succ_self_right (half + half),
    pow_one, Nat.cast_add, Nat.cast_add, Nat.cast_one]
  ring1

end DivineProportions
