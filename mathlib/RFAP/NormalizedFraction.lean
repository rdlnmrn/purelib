import mathlib.RFAP.ConstructiveFraction

/-!
# Normalized constructive rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components without forming the square used
by the quotient-level total inverse.  A final constructive normalization is
retained at each boundary so that every returned record carries its reducedness
certificate directly.
-/

namespace RFAP.NormalizedFraction

abbrev Rational := RFAP.ConstructiveFraction.Rational
abbrev Fraction := RFAP.ConstructiveFraction.Fraction
abbrev ReducedFraction := RFAP.ConstructiveFraction.ReducedFraction

open RFAP.ConstructiveFraction

/-- A reduced working record is already the semantic rational value. -/
def value (fraction : ReducedFraction) : Rational := fraction

/-- Construct the unique gcd-reduced working record for a rational value. -/
def ofRational (source : Rational) : ReducedFraction := source

theorem value_ofRational (source : Rational) :
    value (ofRational source) = source := rfl

theorem representative_value (source : ReducedFraction) :
    representative (value source) = source := rfl

theorem normalize_value (fraction : Fraction) :
    value (ReducedFraction.normalize fraction) = ofFraction fraction := rfl

/-! ## Reduction-aware raw operation records -/

private def rawToFraction
    (fraction : RFAP.CanonicalFraction.RawFraction) : Fraction :=
  ⟨fraction.num, (fraction.den : Int),
    Int.natCast_pos.mpr fraction.den_pos⟩

/-- The denominator gcd used by reduction-aware addition. -/
def additionCommon (left right : ReducedFraction) : Nat :=
  RFAP.CanonicalFraction.additionCommon left right

/-- Left denominator after removing the shared denominator gcd. -/
def additionLeftQuotient (left right : ReducedFraction) : Nat :=
  RFAP.CanonicalFraction.additionLeftQuotient left right

/-- Right denominator after removing the shared denominator gcd. -/
def additionRightQuotient (left right : ReducedFraction) : Nat :=
  RFAP.CanonicalFraction.additionRightQuotient left right

theorem additionCommon_pos (left right : ReducedFraction) :
    0 < additionCommon left right :=
  RFAP.CanonicalFraction.additionCommon_pos left right

theorem additionLeftQuotient_pos (left right : ReducedFraction) :
    0 < additionLeftQuotient left right :=
  RFAP.CanonicalFraction.additionLeftQuotient_pos left right

/-- Addition uses an lcm-sized denominator before the final normalization,
instead of multiplying the two displayed denominators unconditionally. -/
def addRaw (left right : ReducedFraction) : Fraction :=
  rawToFraction (RFAP.CanonicalFraction.addRaw left right)

private theorem addition_left_reconstruct (left right : ReducedFraction) :
    additionLeftQuotient left right * additionCommon left right = left.den := by
  exact RFAP.CanonicalFraction.additionLeftReconstruct left right

private theorem addition_right_reconstruct (left right : ReducedFraction) :
    additionRightQuotient left right * additionCommon left right = right.den := by
  exact RFAP.CanonicalFraction.additionRightReconstruct left right

theorem addRaw_equivalent (left right : ReducedFraction) :
    Equivalent (addRaw left right)
      (addFraction left.toFraction right.toFraction) := by
  simpa only [Equivalent, addRaw, rawToFraction, addFraction,
    ReducedFraction.toFraction, RFAP.CanonicalFraction.Equivalent,
    RFAP.CanonicalFraction.addRaw, RFAP.CanonicalFraction.referenceAddRaw,
    RFAP.CanonicalFraction.Rational.toRaw, Int.natCast_mul] using
      RFAP.CanonicalFraction.addRaw_equivalent left right

/-- First cross-cancellation divisor for multiplication. -/
def multiplicationLeftCommon (left right : ReducedFraction) : Nat :=
  RFAP.CanonicalFraction.multiplicationLeftCommon left right

/-- Second cross-cancellation divisor for multiplication. -/
def multiplicationRightCommon (left right : ReducedFraction) : Nat :=
  RFAP.CanonicalFraction.multiplicationRightCommon left right

theorem multiplicationLeftCommon_pos (left right : ReducedFraction) :
    0 < multiplicationLeftCommon left right :=
  RFAP.CanonicalFraction.multiplicationLeftCommon_pos left right

theorem multiplicationRightCommon_pos (left right : ReducedFraction) :
    0 < multiplicationRightCommon left right :=
  RFAP.CanonicalFraction.multiplicationRightCommon_pos left right

private def cancelInteger (value : Int) (divisor : Nat) : Int :=
  value / (divisor : Int)

private def cancelNatural (value divisor : Nat) : Nat :=
  value / divisor

private theorem cancelInteger_reconstruct {value : Int} {divisor : Nat}
    (divides : divisor ∣ value.natAbs) :
    cancelInteger value divisor * (divisor : Int) = value := by
  apply Int.ediv_mul_cancel
  rw [← Int.dvd_natAbs, Int.ofNat_dvd]
  exact divides

private theorem cancelNatural_reconstruct {value divisor : Nat}
    (divides : divisor ∣ value) :
    cancelNatural value divisor * divisor = value :=
  Nat.div_mul_cancel divides

/-- Cross-cancelled multiplication record.  Its two products are formed only
after removing factors which are certain to disappear. -/
def mulRaw (left right : ReducedFraction) : Fraction := by
  exact rawToFraction (RFAP.CanonicalFraction.mulRaw left right)

theorem mulRaw_equivalent (left right : ReducedFraction) :
    Equivalent (mulRaw left right)
      (mulFraction left.toFraction right.toFraction) := by
  simpa only [Equivalent, mulRaw, rawToFraction, mulFraction,
    ReducedFraction.toFraction, RFAP.CanonicalFraction.Equivalent,
    RFAP.CanonicalFraction.mulRaw, RFAP.CanonicalFraction.referenceMulRaw,
    RFAP.CanonicalFraction.Rational.toRaw, Int.natCast_mul] using
      RFAP.CanonicalFraction.mulRaw_equivalent left right

/-- Sign-canonical reciprocal record, before the final normalization. -/
def invRaw (source : ReducedFraction) : Fraction :=
  (source⁻¹).toFraction

theorem invRaw_equivalent (source : ReducedFraction) :
    Equivalent (invRaw source) (invFraction source.toFraction) := by
  rw [← ofFraction_eq_iff]
  calc
    ofFraction (invRaw source) = source⁻¹ := representative_spec _
    _ = (ofFraction source.toFraction)⁻¹ := by
      exact congrArg (fun value : Rational => value⁻¹)
        (representative_spec source).symm
    _ = ofFraction (invFraction source.toFraction) :=
      (ofFraction_invFraction source.toFraction).symm

/-! ## Normalized working operations -/

def add (left right : ReducedFraction) : ReducedFraction :=
  left + right

def neg (source : ReducedFraction) : ReducedFraction :=
  -source

def sub (left right : ReducedFraction) : ReducedFraction :=
  left - right

def mul (left right : ReducedFraction) : ReducedFraction :=
  left * right

def inv (source : ReducedFraction) : ReducedFraction :=
  source⁻¹

def div (left right : ReducedFraction) : ReducedFraction :=
  left / right

theorem value_add (left right : ReducedFraction) :
    value (add left right) = value left + value right := rfl

theorem value_neg (source : ReducedFraction) :
    value (neg source) = -value source := rfl

theorem value_sub (left right : ReducedFraction) :
    value (sub left right) = value left - value right := rfl

theorem value_mul (left right : ReducedFraction) :
    value (mul left right) = value left * value right := rfl

theorem value_inv (source : ReducedFraction) :
    value (inv source) = (value source)⁻¹ := rfl

theorem value_div (left right : ReducedFraction) :
    value (div left right) = value left / value right := rfl

/-! ## Component bounds

The following bounds account for the integer records which are actually
formed before the final gcd normalization.  In particular, they do not hide
the multiplication which precedes that last reduction. -/

theorem normalize_numerator_le (fraction : Fraction) :
    (ReducedFraction.normalize fraction).num.natAbs ≤ fraction.num.natAbs := by
  exact RFAP.CanonicalFraction.normalize_numerator_le fraction.toRaw

theorem normalize_denominator_le (fraction : Fraction) :
    (ReducedFraction.normalize fraction).den ≤ fraction.den.toNat := by
  exact RFAP.CanonicalFraction.normalize_denominator_le fraction.toRaw

theorem additionLeftQuotient_le (left right : ReducedFraction) :
    additionLeftQuotient left right ≤ left.den :=
  Nat.div_le_self _ _

theorem additionRightQuotient_le (left right : ReducedFraction) :
    additionRightQuotient left right ≤ right.den :=
  Nat.div_le_self _ _

theorem addRaw_denominator_le (left right : ReducedFraction) :
    (addRaw left right).den.toNat ≤ left.den * right.den := by
  change additionLeftQuotient left right * right.den ≤ left.den * right.den
  exact Nat.mul_le_mul_right right.den (additionLeftQuotient_le left right)

theorem addRaw_numerator_le (left right : ReducedFraction) :
    (addRaw left right).num.natAbs ≤
      left.num.natAbs * right.den + right.num.natAbs * left.den := by
  change
    (left.num * (additionRightQuotient left right : Int) +
      right.num * (additionLeftQuotient left right : Int)).natAbs ≤ _
  calc
    _ ≤
        (left.num * (additionRightQuotient left right : Int)).natAbs +
          (right.num * (additionLeftQuotient left right : Int)).natAbs :=
      Int.natAbs_add_le _ _
    _ = left.num.natAbs * additionRightQuotient left right +
        right.num.natAbs * additionLeftQuotient left right := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ left.num.natAbs * right.den + right.num.natAbs * left.den :=
      Nat.add_le_add
        (Nat.mul_le_mul_left left.num.natAbs
          (additionRightQuotient_le left right))
        (Nat.mul_le_mul_left right.num.natAbs
          (additionLeftQuotient_le left right))

theorem mulRaw_denominator_le (left right : ReducedFraction) :
    (mulRaw left right).den.toNat ≤ left.den * right.den := by
  change
    cancelNatural left.den (multiplicationRightCommon left right) *
        cancelNatural right.den (multiplicationLeftCommon left right) ≤
      left.den * right.den
  exact Nat.mul_le_mul (Nat.div_le_self _ _) (Nat.div_le_self _ _)

theorem mulRaw_numerator_le (left right : ReducedFraction) :
    (mulRaw left right).num.natAbs ≤
      left.num.natAbs * right.num.natAbs := by
  change
    (cancelInteger left.num (multiplicationLeftCommon left right) *
      cancelInteger right.num (multiplicationRightCommon left right)).natAbs ≤ _
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul
    (Int.natAbs_ediv_le_natAbs _ _)
    (Int.natAbs_ediv_le_natAbs _ _)

theorem add_denominator_le (left right : ReducedFraction) :
    (add left right).den ≤ left.den * right.den := by
  exact RFAP.CanonicalFraction.add_denominator_le left right

theorem add_numerator_le (left right : ReducedFraction) :
    (add left right).num.natAbs ≤
      left.num.natAbs * right.den + right.num.natAbs * left.den := by
  exact RFAP.CanonicalFraction.add_numerator_le left right

theorem mul_denominator_le (left right : ReducedFraction) :
    (mul left right).den ≤ left.den * right.den := by
  exact RFAP.CanonicalFraction.mul_denominator_le left right

theorem mul_numerator_le (left right : ReducedFraction) :
    (mul left right).num.natAbs ≤
      left.num.natAbs * right.num.natAbs := by
  exact RFAP.CanonicalFraction.mul_numerator_le left right

theorem neg_denominator_le (source : ReducedFraction) :
    (neg source).den ≤ source.den := by
  exact Nat.le_refl source.den

theorem neg_numerator_le (source : ReducedFraction) :
    (neg source).num.natAbs ≤ source.num.natAbs := by
  change (-source.num).natAbs ≤ source.num.natAbs
  rw [Int.natAbs_neg]

theorem invRaw_denominator_le (source : ReducedFraction) :
    (invRaw source).den.toNat ≤ max source.num.natAbs source.den := by
  simpa only [invRaw, ReducedFraction.toFraction, Int.toNat_natCast,
    RFAP.CanonicalFraction.componentMagnitude] using
    ((RFAP.CanonicalFraction.denominator_le_componentMagnitude source⁻¹).trans
      (RFAP.CanonicalFraction.componentMagnitude_inv_le source))

theorem invRaw_numerator_le (source : ReducedFraction) :
    (invRaw source).num.natAbs ≤ max source.num.natAbs source.den := by
  simpa only [invRaw, ReducedFraction.toFraction,
    RFAP.CanonicalFraction.componentMagnitude] using
    ((RFAP.CanonicalFraction.numerator_le_componentMagnitude source⁻¹).trans
      (RFAP.CanonicalFraction.componentMagnitude_inv_le source))

theorem inv_denominator_le (source : ReducedFraction) :
    (inv source).den ≤ max source.num.natAbs source.den := by
  exact (RFAP.CanonicalFraction.denominator_le_componentMagnitude
      (inv source)).trans
    (RFAP.CanonicalFraction.componentMagnitude_inv_le source)

theorem inv_numerator_le (source : ReducedFraction) :
    (inv source).num.natAbs ≤ max source.num.natAbs source.den := by
  exact (RFAP.CanonicalFraction.numerator_le_componentMagnitude
      (inv source)).trans
    (RFAP.CanonicalFraction.componentMagnitude_inv_le source)

/-! ## Euclidean-clause budgets -/

/-- Number of logical clauses in the reference Euclidean recursion used by
`Nat.gcd`, including its terminal zero clause.  The compiler may execute its
equivalent primitive implementation more efficiently; this is the explicit
finite recursion audited by the kernel. -/
def gcdClausesAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | _ + 1, 0, _ => 1
  | fuel + 1, first + 1, second =>
      1 + gcdClausesAux fuel (second % (first + 1)) (first + 1)

/-- Exact logical clause count, evaluated by a structurally recursive fuel
argument rather than a well-founded equation theorem. -/
def gcdClauses (first second : Nat) : Nat :=
  gcdClausesAux (first + 1) first second

theorem gcdClauses_pos (first second : Nat) :
    0 < gcdClauses first second := by
  cases first with
  | zero => exact Nat.zero_lt_succ 0
  | succ first =>
      change 0 < 1 + gcdClausesAux (first + 1)
        (second % (first + 1)) (first + 1)
      rw [Nat.one_add]
      exact Nat.zero_lt_succ _

/-- A deliberately elementary bound for the Euclidean recursion.  It is
coarse in magnitude but already rules out an unaccounted or infinite gcd
phase; sharper logarithmic Lamé bounds can replace it without changing the
working representation. -/
theorem gcdClauses_le (first second : Nat) :
    gcdClauses first second ≤ first + 1 := by
  have auxiliary : ∀ fuel left right,
      gcdClausesAux fuel left right ≤ fuel := by
    intro fuel
    induction fuel with
    | zero =>
        intro left right
        exact Nat.le_refl 0
    | succ fuel inductionHypothesis =>
        intro left right
        cases left with
        | zero => exact Nat.succ_le_succ (Nat.zero_le fuel)
        | succ left =>
            change 1 + gcdClausesAux fuel (right % (left + 1)) (left + 1) ≤
              fuel + 1
            simpa only [Nat.add_comm fuel 1] using
              Nat.add_le_add_left
                (inductionHypothesis (right % (left + 1)) (left + 1)) 1
  exact auxiliary (first + 1) first second

/-- Euclidean clauses executed by reduction-aware addition: one denominator
gcd and the final numerator/denominator normalization. -/
def addGcdClauses (left right : ReducedFraction) : Nat :=
  gcdClauses left.den right.den +
    gcdClauses (addRaw left right).num.natAbs (addRaw left right).den.toNat

theorem addGcdClauses_le (left right : ReducedFraction) :
    addGcdClauses left right ≤
      left.den + left.num.natAbs * right.den +
        right.num.natAbs * left.den + 2 := by
  unfold addGcdClauses
  have first := gcdClauses_le left.den right.den
  have final := gcdClauses_le (addRaw left right).num.natAbs
    (addRaw left right).den.toNat
  have numerator := addRaw_numerator_le left right
  calc
    gcdClauses left.den right.den +
          gcdClauses (addRaw left right).num.natAbs
            (addRaw left right).den.toNat ≤
        (left.den + 1) + ((addRaw left right).num.natAbs + 1) :=
      Nat.add_le_add first final
    _ ≤ (left.den + 1) +
          (left.num.natAbs * right.den +
            right.num.natAbs * left.den + 1) :=
      Nat.add_le_add_left (Nat.add_le_add_right numerator 1) _
    _ = left.den + left.num.natAbs * right.den +
          right.num.natAbs * left.den + 2 := by
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Euclidean clauses executed by reduction-aware multiplication: two
cross-cancellation gcds and the final normalization. -/
def mulGcdClauses (left right : ReducedFraction) : Nat :=
  gcdClauses left.num.natAbs right.den +
    gcdClauses right.num.natAbs left.den +
      gcdClauses (mulRaw left right).num.natAbs
        (mulRaw left right).den.toNat

theorem mulGcdClauses_le (left right : ReducedFraction) :
    mulGcdClauses left right ≤
      left.num.natAbs + right.num.natAbs +
        left.num.natAbs * right.num.natAbs + 3 := by
  unfold mulGcdClauses
  have first := gcdClauses_le left.num.natAbs right.den
  have second := gcdClauses_le right.num.natAbs left.den
  have final := gcdClauses_le (mulRaw left right).num.natAbs
    (mulRaw left right).den.toNat
  have numerator := mulRaw_numerator_le left right
  calc
    gcdClauses left.num.natAbs right.den +
          gcdClauses right.num.natAbs left.den +
          gcdClauses (mulRaw left right).num.natAbs
            (mulRaw left right).den.toNat ≤
        (left.num.natAbs + 1) + (right.num.natAbs + 1) +
          ((mulRaw left right).num.natAbs + 1) :=
      Nat.add_le_add (Nat.add_le_add first second) final
    _ ≤ (left.num.natAbs + 1) + (right.num.natAbs + 1) +
          (left.num.natAbs * right.num.natAbs + 1) :=
      Nat.add_le_add_left (Nat.add_le_add_right numerator 1) _
    _ = left.num.natAbs + right.num.natAbs +
          left.num.natAbs * right.num.natAbs + 3 := by
      simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Largest displayed natural component of a reduced scalar record. -/
def componentMagnitude (source : ReducedFraction) : Nat :=
  max source.num.natAbs source.den

theorem numerator_le_componentMagnitude (source : ReducedFraction) :
    source.num.natAbs ≤ componentMagnitude source :=
  le_max_left _ _

theorem denominator_le_componentMagnitude (source : ReducedFraction) :
    source.den ≤ componentMagnitude source :=
  le_max_right _ _

/-- Uniform source-magnitude envelope for addition and subtraction. -/
def additiveMagnitudeEnvelope (left right : Nat) : Nat :=
  left * right + left * right

/-- Uniform source-magnitude envelope for multiplication and division. -/
def multiplicativeMagnitudeEnvelope (left right : Nat) : Nat :=
  left * right

/-- Source-only component envelope for normalized addition. -/
def addComponentEnvelope (left right : ReducedFraction) : Nat :=
  max (left.num.natAbs * right.den + right.num.natAbs * left.den)
    (left.den * right.den)

/-- Source-only component envelope for normalized multiplication. -/
def mulComponentEnvelope (left right : ReducedFraction) : Nat :=
  max (left.num.natAbs * right.num.natAbs) (left.den * right.den)

theorem add_componentMagnitude_le (left right : ReducedFraction) :
    componentMagnitude (add left right) ≤ addComponentEnvelope left right := by
  apply max_le
  · exact (add_numerator_le left right).trans (le_max_left _ _)
  · exact (add_denominator_le left right).trans (le_max_right _ _)

theorem mul_componentMagnitude_le (left right : ReducedFraction) :
    componentMagnitude (mul left right) ≤ mulComponentEnvelope left right := by
  apply max_le
  · exact (mul_numerator_le left right).trans (le_max_left _ _)
  · exact (mul_denominator_le left right).trans (le_max_right _ _)

theorem addComponentEnvelope_le_magnitudeEnvelope
    (left right : ReducedFraction) :
    addComponentEnvelope left right ≤
      additiveMagnitudeEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  apply max_le
  · apply Nat.add_le_add
    · exact Nat.mul_le_mul (numerator_le_componentMagnitude left)
        (denominator_le_componentMagnitude right)
    · calc
        right.num.natAbs * left.den ≤
            componentMagnitude right * componentMagnitude left :=
          Nat.mul_le_mul (numerator_le_componentMagnitude right)
            (denominator_le_componentMagnitude left)
        _ = componentMagnitude left * componentMagnitude right :=
          Nat.mul_comm _ _
  · have productBound := Nat.mul_le_mul
      (denominator_le_componentMagnitude left)
      (denominator_le_componentMagnitude right)
    exact productBound.trans (Nat.le_add_right _ _)

theorem mulComponentEnvelope_le_magnitudeEnvelope
    (left right : ReducedFraction) :
    mulComponentEnvelope left right ≤
      multiplicativeMagnitudeEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  apply max_le
  · exact Nat.mul_le_mul
      (numerator_le_componentMagnitude left)
      (numerator_le_componentMagnitude right)
  · exact Nat.mul_le_mul
      (denominator_le_componentMagnitude left)
      (denominator_le_componentMagnitude right)

theorem componentMagnitude_add_le (left right : ReducedFraction) :
    componentMagnitude (add left right) ≤
      additiveMagnitudeEnvelope (componentMagnitude left)
        (componentMagnitude right) :=
  (add_componentMagnitude_le left right).trans
    (addComponentEnvelope_le_magnitudeEnvelope left right)

theorem componentMagnitude_mul_le (left right : ReducedFraction) :
    componentMagnitude (mul left right) ≤
      multiplicativeMagnitudeEnvelope (componentMagnitude left)
        (componentMagnitude right) :=
  (mul_componentMagnitude_le left right).trans
    (mulComponentEnvelope_le_magnitudeEnvelope left right)

theorem componentMagnitude_neg_le (source : ReducedFraction) :
    componentMagnitude (neg source) ≤ componentMagnitude source := by
  apply max_le
  · exact (neg_numerator_le source).trans
      (numerator_le_componentMagnitude source)
  · exact (neg_denominator_le source).trans
      (denominator_le_componentMagnitude source)

theorem componentMagnitude_inv_le (source : ReducedFraction) :
    componentMagnitude (inv source) ≤ componentMagnitude source := by
  apply max_le
  · exact inv_numerator_le source
  · exact inv_denominator_le source

theorem additiveMagnitudeEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    additiveMagnitudeEnvelope left right ≤
      additiveMagnitudeEnvelope leftBound rightBound := by
  exact Nat.add_le_add (Nat.mul_le_mul leftLe rightLe)
    (Nat.mul_le_mul leftLe rightLe)

theorem multiplicativeMagnitudeEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    multiplicativeMagnitudeEnvelope left right ≤
      multiplicativeMagnitudeEnvelope leftBound rightBound :=
  Nat.mul_le_mul leftLe rightLe

theorem componentMagnitude_sub_le (left right : ReducedFraction) :
    componentMagnitude (sub left right) ≤
      additiveMagnitudeEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  exact (componentMagnitude_add_le left (neg right)).trans
    (additiveMagnitudeEnvelope_mono (le_refl _)
      (componentMagnitude_neg_le right))

theorem componentMagnitude_div_le (left right : ReducedFraction) :
    componentMagnitude (div left right) ≤
      multiplicativeMagnitudeEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  exact (componentMagnitude_mul_le left (inv right)).trans
    (multiplicativeMagnitudeEnvelope_mono (le_refl _)
      (componentMagnitude_inv_le right))

/-! ## Arithmetic-step envelopes -/

/-- Audited arithmetic clauses for normalized addition: its two gcd
recursions plus the fixed quotient, product, sum, and reduction work. -/
def addSteps (left right : ReducedFraction) : Nat :=
  addGcdClauses left right + 8

/-- Audited arithmetic clauses for normalized multiplication: its three gcd
recursions plus the fixed cancellation, product, and reduction work. -/
def mulSteps (left right : ReducedFraction) : Nat :=
  mulGcdClauses left right + 8

def negSteps (source : ReducedFraction) : Nat :=
  gcdClauses source.num.natAbs source.den + 3

def invSteps (source : ReducedFraction) : Nat :=
  gcdClauses (invRaw source).num.natAbs (invRaw source).den.toNat + 6

def subSteps (left right : ReducedFraction) : Nat :=
  negSteps right + addSteps left (neg right)

def divSteps (left right : ReducedFraction) : Nat :=
  invSteps right + mulSteps left (inv right)

def addStepEnvelope (left right : Nat) : Nat :=
  left + additiveMagnitudeEnvelope left right + 10

def mulStepEnvelope (left right : Nat) : Nat :=
  left + right + multiplicativeMagnitudeEnvelope left right + 11

def negStepEnvelope (source : Nat) : Nat := source + 4

def invStepEnvelope (source : Nat) : Nat := source + 7

def subStepEnvelope (left right : Nat) : Nat :=
  negStepEnvelope right + addStepEnvelope left right

def divStepEnvelope (left right : Nat) : Nat :=
  invStepEnvelope right + mulStepEnvelope left right

theorem addStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    addStepEnvelope left right ≤ addStepEnvelope leftBound rightBound := by
  unfold addStepEnvelope
  exact Nat.add_le_add
    (Nat.add_le_add leftLe
      (additiveMagnitudeEnvelope_mono leftLe rightLe))
    (le_refl _)

theorem mulStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    mulStepEnvelope left right ≤ mulStepEnvelope leftBound rightBound := by
  unfold mulStepEnvelope
  exact Nat.add_le_add
    (Nat.add_le_add (Nat.add_le_add leftLe rightLe)
      (multiplicativeMagnitudeEnvelope_mono leftLe rightLe))
    (le_refl _)

theorem negStepEnvelope_mono {source bound : Nat} (sourceLe : source ≤ bound) :
    negStepEnvelope source ≤ negStepEnvelope bound :=
  Nat.add_le_add_right sourceLe 4

theorem invStepEnvelope_mono {source bound : Nat} (sourceLe : source ≤ bound) :
    invStepEnvelope source ≤ invStepEnvelope bound :=
  Nat.add_le_add_right sourceLe 7

theorem subStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    subStepEnvelope left right ≤ subStepEnvelope leftBound rightBound := by
  unfold subStepEnvelope
  exact Nat.add_le_add (negStepEnvelope_mono rightLe)
    (addStepEnvelope_mono leftLe rightLe)

theorem divStepEnvelope_mono
    {left right leftBound rightBound : Nat}
    (leftLe : left ≤ leftBound) (rightLe : right ≤ rightBound) :
    divStepEnvelope left right ≤ divStepEnvelope leftBound rightBound := by
  unfold divStepEnvelope
  exact Nat.add_le_add (invStepEnvelope_mono rightLe)
    (mulStepEnvelope_mono leftLe rightLe)

theorem addSteps_le_envelope (left right : ReducedFraction) :
    addSteps left right ≤
      addStepEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  have gcdBound := addGcdClauses_le left right
  have numeratorBound :
      left.num.natAbs * right.den + right.num.natAbs * left.den ≤
        additiveMagnitudeEnvelope (componentMagnitude left)
          (componentMagnitude right) := by
    exact (le_max_left _ _).trans
      (addComponentEnvelope_le_magnitudeEnvelope left right)
  unfold addSteps addStepEnvelope
  have denominatorBound := denominator_le_componentMagnitude left
  have components :
      left.den +
          (left.num.natAbs * right.den + right.num.natAbs * left.den) ≤
        componentMagnitude left +
          additiveMagnitudeEnvelope (componentMagnitude left)
            (componentMagnitude right) :=
    Nat.add_le_add denominatorBound numeratorBound
  have gcdToComponents :
      addGcdClauses left right ≤
        componentMagnitude left +
          additiveMagnitudeEnvelope (componentMagnitude left)
            (componentMagnitude right) + 2 :=
    gcdBound.trans (by
      simpa only [Nat.add_assoc] using Nat.add_le_add_right components 2)
  have withFixedWork := Nat.add_le_add_right gcdToComponents 8
  simpa only [Nat.add_assoc] using withFixedWork

theorem mulSteps_le_envelope (left right : ReducedFraction) :
    mulSteps left right ≤
      mulStepEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  have gcdBound := mulGcdClauses_le left right
  have leftNumerator := numerator_le_componentMagnitude left
  have rightNumerator := numerator_le_componentMagnitude right
  have productBound := Nat.mul_le_mul leftNumerator rightNumerator
  unfold mulSteps mulStepEnvelope multiplicativeMagnitudeEnvelope
  have components :
      left.num.natAbs + right.num.natAbs +
          left.num.natAbs * right.num.natAbs ≤
        componentMagnitude left + componentMagnitude right +
          componentMagnitude left * componentMagnitude right :=
    Nat.add_le_add (Nat.add_le_add leftNumerator rightNumerator) productBound
  have gcdToComponents :
      mulGcdClauses left right ≤
        componentMagnitude left + componentMagnitude right +
          componentMagnitude left * componentMagnitude right + 3 :=
    gcdBound.trans (Nat.add_le_add_right components 3)
  have withFixedWork := Nat.add_le_add_right gcdToComponents 8
  simpa only [Nat.add_assoc] using withFixedWork

theorem negSteps_le_envelope (source : ReducedFraction) :
    negSteps source ≤ negStepEnvelope (componentMagnitude source) := by
  have gcdBound := gcdClauses_le source.num.natAbs source.den
  have numeratorBound := numerator_le_componentMagnitude source
  unfold negSteps negStepEnvelope
  have gcdToMagnitude :
      gcdClauses source.num.natAbs source.den ≤
        componentMagnitude source + 1 :=
    gcdBound.trans (Nat.add_le_add_right numeratorBound 1)
  have withFixedWork := Nat.add_le_add_right gcdToMagnitude 3
  simpa only [Nat.add_assoc] using withFixedWork

theorem invSteps_le_envelope (source : ReducedFraction) :
    invSteps source ≤ invStepEnvelope (componentMagnitude source) := by
  have gcdBound := gcdClauses_le (invRaw source).num.natAbs
    (invRaw source).den.toNat
  have numeratorBound := invRaw_numerator_le source
  have gcdToMagnitude :
      gcdClauses (invRaw source).num.natAbs (invRaw source).den.toNat ≤
        componentMagnitude source + 1 :=
    gcdBound.trans (Nat.add_le_add_right numeratorBound 1)
  unfold invSteps invStepEnvelope
  exact Nat.add_le_add_right gcdToMagnitude 6

theorem subSteps_le_envelope (left right : ReducedFraction) :
    subSteps left right ≤
      subStepEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  have negBound := negSteps_le_envelope right
  have addBound := addSteps_le_envelope left (neg right)
  have addEnvelopeBound := addStepEnvelope_mono
    (left := componentMagnitude left)
    (right := componentMagnitude (neg right))
    (leftBound := componentMagnitude left)
    (rightBound := componentMagnitude right)
    (le_refl _) (componentMagnitude_neg_le right)
  unfold subSteps subStepEnvelope
  exact Nat.add_le_add negBound (addBound.trans addEnvelopeBound)

theorem divSteps_le_envelope (left right : ReducedFraction) :
    divSteps left right ≤
      divStepEnvelope (componentMagnitude left)
        (componentMagnitude right) := by
  have invBound := invSteps_le_envelope right
  have mulBound := mulSteps_le_envelope left (inv right)
  have mulEnvelopeBound := mulStepEnvelope_mono
    (left := componentMagnitude left)
    (right := componentMagnitude (inv right))
    (leftBound := componentMagnitude left)
    (rightBound := componentMagnitude right)
    (le_refl _) (componentMagnitude_inv_le right)
  unfold divSteps divStepEnvelope
  exact Nat.add_le_add invBound (mulBound.trans mulEnvelopeBound)

/-! ## Quotient-valued entry points

These functions make normalization available to existing RFAP algorithms
without replacing their algebraic statement type. -/

def normalizedAdd (left right : Rational) : Rational :=
  value (add (ofRational left) (ofRational right))

def normalizedNeg (source : Rational) : Rational :=
  value (neg (ofRational source))

def normalizedSub (left right : Rational) : Rational :=
  value (sub (ofRational left) (ofRational right))

def normalizedMul (left right : Rational) : Rational :=
  value (mul (ofRational left) (ofRational right))

def normalizedInv (source : Rational) : Rational :=
  value (inv (ofRational source))

def normalizedDiv (left right : Rational) : Rational :=
  value (div (ofRational left) (ofRational right))

@[simp] theorem normalizedAdd_eq (left right : Rational) :
    normalizedAdd left right = left + right := by
  rw [normalizedAdd, value_add, value_ofRational, value_ofRational]

@[simp] theorem normalizedNeg_eq (source : Rational) :
    normalizedNeg source = -source := by
  rw [normalizedNeg, value_neg, value_ofRational]

@[simp] theorem normalizedSub_eq (left right : Rational) :
    normalizedSub left right = left - right := by
  rw [normalizedSub, value_sub, value_ofRational, value_ofRational]

@[simp] theorem normalizedMul_eq (left right : Rational) :
    normalizedMul left right = left * right := by
  rw [normalizedMul, value_mul, value_ofRational, value_ofRational]

@[simp] theorem normalizedInv_eq (source : Rational) :
    normalizedInv source = source⁻¹ := by
  rw [normalizedInv, value_inv, value_ofRational]

@[simp] theorem normalizedDiv_eq (left right : Rational) :
    normalizedDiv left right = left / right := by
  rw [normalizedDiv, value_div, value_ofRational, value_ofRational]

theorem ofRational_normalizedAdd (left right : Rational) :
    ofRational (normalizedAdd left right) =
      add (ofRational left) (ofRational right) := by
  exact representative_value _

theorem ofRational_normalizedNeg (source : Rational) :
    ofRational (normalizedNeg source) = neg (ofRational source) := by
  exact representative_value _

theorem ofRational_normalizedSub (left right : Rational) :
    ofRational (normalizedSub left right) =
      sub (ofRational left) (ofRational right) := by
  exact representative_value _

theorem ofRational_normalizedMul (left right : Rational) :
    ofRational (normalizedMul left right) =
      mul (ofRational left) (ofRational right) := by
  exact representative_value _

theorem ofRational_normalizedInv (source : Rational) :
    ofRational (normalizedInv source) = inv (ofRational source) := by
  exact representative_value _

theorem ofRational_normalizedDiv (left right : Rational) :
    ofRational (normalizedDiv left right) =
      div (ofRational left) (ofRational right) := by
  exact representative_value _

/-- Canonical denominator-one record for a natural cast. -/
def ofNat (source : Nat) : ReducedFraction :=
  RFAP.CanonicalFraction.fromInt (source : Int)

theorem ofRational_natCast (source : Nat) :
    ofRational (source : Rational) = ofNat source := by
  exact RFAP.CanonicalFraction.natCast_eq_fromInt source

@[simp] theorem componentMagnitude_ofNat (source : Nat) :
    componentMagnitude (ofNat source) = max source 1 := by
  rfl

theorem componentMagnitude_natCast_mono {left right : Nat}
    (order : left ≤ right) :
    componentMagnitude (ofRational (left : Rational)) ≤
      componentMagnitude (ofRational (right : Rational)) := by
  rw [ofRational_natCast, ofRational_natCast,
    componentMagnitude_ofNat, componentMagnitude_ofNat]
  exact max_le_max order (le_refl 1)

end RFAP.NormalizedFraction
