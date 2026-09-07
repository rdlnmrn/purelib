import mathlib.Tactic.QuotientFreeRing
import RFAP.Polynomial.Multiplicity
import RFAP.Geometry.Chordal

/-!
# Residual bounds for finite multiplicity bases

The exact multiplicity basis gives two complementary finite statements.
First, a sufficiently small residual of the original polynomial selects at
least one displayed squarefree basis factor with small residual.  Second, for
a preselected factor, an explicit positive lower bound on the remaining
unit/cofactor product transfers its residual bound back to the original
polynomial in an integer-power form.

No rational root, real exponent, root collection, or completed value occurs:
all powers are natural powers of displayed rational quadrances.
-/

namespace RFAP.MultiplicityResidual

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev PositiveEntry := RFAP.Multiplicity.PositiveEntry
abbrev Decomposition := RFAP.Factorization.Decomposition

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.Multiplicity

/-- Total number of displayed squarefree occurrences, counting positive
multiplicity. -/
def multiplicityCount : List PositiveEntry → Nat
  | [] => 0
  | entry :: entries => entry.multiplicity + multiplicityCount entries

/-- Squared norm of the finite weighted product is the product of the
displayed factor residual quadrances. -/
theorem normSq_positiveValue : ∀ (entries : List PositiveEntry)
    (point : Gaussian),
    normSq (positiveValue entries point) =
      match entries with
      | [] => 1
      | entry :: tail =>
          normSq (entry.part.polynomial.eval point) ^ entry.multiplicity *
            normSq (positiveValue tail point)
  | [], point => by
      simp only [positiveValue, normSq_one]
  | entry :: entries, point => by
      rw [positiveValue, normSq_mul, normSq_pow]

/-- If every displayed factor residual is at least `delta`, the whole finite
weighted product is at least `delta` to the total multiplicity. -/
theorem power_le_normSq_positiveValue_of_all
    (delta : Coordinate) (deltaNonnegative : 0 ≤ delta) :
    ∀ (entries : List PositiveEntry) (point : Gaussian),
      (∀ entry ∈ entries,
        delta ≤ normSq (entry.part.polynomial.eval point)) →
      delta ^ multiplicityCount entries ≤
        normSq (positiveValue entries point)
  | [], point, _ => by
      simp only [multiplicityCount, pow_zero, positiveValue, normSq_one]
      exact le_rfl
  | entry :: entries, point, lower => by
      have headLower := lower entry (List.mem_cons_self)
      have headPower : delta ^ entry.multiplicity ≤
          normSq (entry.part.polynomial.eval point) ^ entry.multiplicity :=
        RFAP.ConstructiveFraction.pow_le_pow_direct deltaNonnegative
          headLower entry.multiplicity
      have tailLower := power_le_normSq_positiveValue_of_all delta
        deltaNonnegative entries point (fun tail member =>
          lower tail (List.mem_cons_of_mem entry member))
      rw [multiplicityCount, pow_add, normSq_positiveValue]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct headPower tailLower
        (RFAP.ConstructiveFraction.pow_nonneg_direct deltaNonnegative
          (multiplicityCount entries))
        (RFAP.ConstructiveFraction.pow_nonneg_direct
          (normSq_nonneg (entry.part.polynomial.eval point))
          entry.multiplicity)

/-- Squared norm of the omitted degree-zero unit. -/
def unitQuadrance {p : GaussianPolynomial}
    (decomposition : Decomposition p) : Coordinate :=
  normSq (unitValue decomposition.multiplicityBasis.entries)

theorem unitQuadrance_pos {p : GaussianPolynomial}
    (decomposition : Decomposition p) :
    0 < unitQuadrance decomposition :=
  normSq_pos decomposition.multiplicityUnit_ne_zero

/-- Exact residual product identity for the displayed multiplicity basis. -/
theorem residual_product_identity
    {p : GaussianPolynomial} (decomposition : Decomposition p)
    (point : Gaussian) :
    normSq (p.eval point) = unitQuadrance decomposition *
      normSq (positiveValue decomposition.positiveMultiplicityEntries
        point) := by
  rw [decomposition.eval_positiveMultiplicityEntries point, normSq_mul]
  rfl

/-- Bounded finite scan for the first positive-degree factor whose displayed
residual quadrance is strictly below `delta`. -/
def findSmallIndex (point : Gaussian) (delta : Coordinate) :
    (entries : List PositiveEntry) → Option (Fin entries.length)
  | [] => none
  | entry :: entries =>
      if normSq (entry.part.polynomial.eval point) < delta then some 0
      else
        match findSmallIndex point delta entries with
        | none => none
        | some index => some index.succ

theorem findSmallIndex_sound
    (point : Gaussian) (delta : Coordinate) :
    ∀ (entries : List PositiveEntry) (index : Fin entries.length),
      findSmallIndex point delta entries = some index →
      normSq ((entries.get index).part.polynomial.eval point) < delta
  | [], index, _ => Fin.elim0 index
  | entry :: entries, index, found => by
      by_cases headSmall : normSq (entry.part.polynomial.eval point) < delta
      · rw [findSmallIndex, if_pos headSmall] at found
        have indexZero : index = 0 := Option.some.inj found.symm
        subst index
        exact headSmall
      · rw [findSmallIndex, if_neg headSmall] at found
        cases recursive : findSmallIndex point delta entries with
        | none => rw [recursive] at found; contradiction
        | some tailIndex =>
            rw [recursive] at found
            have indexSucc : index = tailIndex.succ :=
              Option.some.inj found.symm
            subst index
            exact findSmallIndex_sound point delta entries tailIndex recursive

theorem all_lower_of_findSmallIndex_eq_none
    (point : Gaussian) (delta : Coordinate) :
    ∀ (entries : List PositiveEntry),
      findSmallIndex point delta entries = none →
      ∀ entry ∈ entries,
        delta ≤ normSq (entry.part.polynomial.eval point)
  | [], _, entry, member => by simp at member
  | head :: entries, found, entry, member => by
      by_cases headSmall : normSq (head.part.polynomial.eval point) < delta
      · rw [findSmallIndex, if_pos headSmall] at found
        contradiction
      · rw [findSmallIndex, if_neg headSmall] at found
        cases recursive : findSmallIndex point delta entries with
        | some index => rw [recursive] at found; contradiction
        | none =>
            rcases List.mem_cons.mp member with rfl | tailMember
            · exact le_of_not_gt headSmall
            · exact all_lower_of_findSmallIndex_eq_none point delta entries
                recursive entry tailMember

/-- Proof-bearing selected squarefree factor. -/
structure SmallFactor
    {p : GaussianPolynomial} (decomposition : Decomposition p)
    (point : Gaussian) (delta : Coordinate) where
  index : Fin decomposition.positiveMultiplicityEntries.length
  residualSmall :
    normSq ((decomposition.positiveMultiplicityEntries.get index).part.polynomial.eval
      point) < delta

/-- A small original residual constructively selects one small squarefree
factor.  The threshold displays both the exact omitted-unit quadrance and the
finite total multiplicity. -/
def selectSmallFactor
    {p : GaussianPolynomial} (decomposition : Decomposition p)
    (point : Gaussian) {delta : Coordinate} (deltaPositive : 0 < delta)
    (small : normSq (p.eval point) <
      unitQuadrance decomposition *
        delta ^ multiplicityCount
          decomposition.positiveMultiplicityEntries) :
    SmallFactor decomposition point delta := by
  let entries := decomposition.positiveMultiplicityEntries
  match found : findSmallIndex point delta entries with
  | some index =>
      exact
        { index := index
          residualSmall := findSmallIndex_sound point delta entries index found }
  | none =>
      have allLower : ∀ entry ∈ entries,
          delta ≤ normSq (entry.part.polynomial.eval point) :=
        all_lower_of_findSmallIndex_eq_none point delta entries found
      have productLower : delta ^ multiplicityCount entries ≤
          normSq (positiveValue entries point) :=
        power_le_normSq_positiveValue_of_all delta deltaPositive.le
          entries point allLower
      have scaledLower : unitQuadrance decomposition *
          delta ^ multiplicityCount entries ≤
          unitQuadrance decomposition *
            normSq (positiveValue entries point) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          productLower (unitQuadrance_pos decomposition).le
      have residualIdentity := residual_product_identity decomposition point
      have contradiction : normSq (p.eval point) < normSq (p.eval point) := by
        calc
          normSq (p.eval point) < unitQuadrance decomposition *
              delta ^ multiplicityCount entries := by
            simpa only [entries] using small
          _ ≤ unitQuadrance decomposition *
              normSq (positiveValue entries point) := scaledLower
          _ = normSq (p.eval point) := residualIdentity.symm
      exact (lt_irrefl _ contradiction).elim

/-! ## A preselected factor and its explicit cofactor -/

/-- The remaining positive-factor value after exposing one selected entry in
a displayed list split. -/
def cofactorValue (before after : List PositiveEntry)
    (point : Gaussian) : Gaussian :=
  positiveValue before point * positiveValue after point

theorem positiveValue_split
    (before after : List PositiveEntry) (entry : PositiveEntry)
    (point : Gaussian) :
    positiveValue (before ++ entry :: after) point =
      entry.part.polynomial.eval point ^ entry.multiplicity *
        cofactorValue before after point := by
  induction before with
  | nil =>
      simp only [List.nil_append, positiveValue, cofactorValue]
      rw [RFAP.ConstructiveGaussian.Gaussian.one_mul]
  | cons head before inductionHypothesis =>
      simp only [List.cons_append, positiveValue]
      rw [inductionHypothesis]
      dsimp only [cofactorValue]
      rw [positiveValue]
      ring1

/-- Explicit positive lower certificate for the omitted unit and all other
factor values at one displayed sample. -/
structure CofactorLower
    {p : GaussianPolynomial} (decomposition : Decomposition p)
    (before after : List PositiveEntry) (point : Gaussian) where
  bound : Coordinate
  positive : 0 < bound
  lower : bound ≤ unitQuadrance decomposition *
    normSq (cofactorValue before after point)

/-- Exact norm factorization at a displayed selected multiplicity entry. -/
theorem selected_residual_identity
    {p : GaussianPolynomial} (decomposition : Decomposition p)
    (before after : List PositiveEntry) (entry : PositiveEntry)
    (split : decomposition.positiveMultiplicityEntries =
      before ++ entry :: after) (point : Gaussian) :
    normSq (p.eval point) =
      (unitQuadrance decomposition *
        normSq (cofactorValue before after point)) *
      normSq (entry.part.polynomial.eval point) ^ entry.multiplicity := by
  rw [residual_product_identity decomposition point, split,
    positiveValue_split, normSq_mul, normSq_pow]
  ring1

/-- A cofactor lower bound transfers the selected factor's integer-power
residual to the original residual without extracting an `m`-th root. -/
theorem cofactor_mul_factorResidualPow_le_sourceResidual
    {p : GaussianPolynomial} (decomposition : Decomposition p)
    (before after : List PositiveEntry) (entry : PositiveEntry)
    (split : decomposition.positiveMultiplicityEntries =
      before ++ entry :: after) (point : Gaussian)
    (cofactor : CofactorLower decomposition before after point) :
    cofactor.bound *
        normSq (entry.part.polynomial.eval point) ^ entry.multiplicity ≤
      normSq (p.eval point) := by
  rw [selected_residual_identity decomposition before after entry split point]
  exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    cofactor.lower
    (RFAP.ConstructiveFraction.pow_nonneg_direct
      (normSq_nonneg (entry.part.polynomial.eval point)) entry.multiplicity)

/-- Rational constant absorbing a positive cofactor lower bound into every
positive natural multiplicity. -/
def integerPowerConstant (localConstant cofactorLower : Coordinate) :
    Coordinate :=
  localConstant * max 1 cofactorLower⁻¹

/-- Integer-power chordal transfer for a preselected repeated factor.  The
input `localBound` may come from either local residual-to-chordal theorem.
The conclusion contains only natural powers and the original displayed
polynomial residual quadrance. -/
theorem chordalPow_le_integerPowerConstant_mul_sourceResidual
    {p : GaussianPolynomial} (decomposition : Decomposition p)
    (before after : List PositiveEntry) (entry : PositiveEntry)
    (split : decomposition.positiveMultiplicityEntries =
      before ++ entry :: after) (point : Gaussian)
    (cofactor : CofactorLower decomposition before after point)
    {chordal localConstant : Coordinate}
    (chordalNonnegative : 0 ≤ chordal)
    (localConstantNonnegative : 0 ≤ localConstant)
    (localBound : chordal ≤ localConstant *
      normSq (entry.part.polynomial.eval point)) :
    chordal ^ entry.multiplicity ≤
      integerPowerConstant localConstant cofactor.bound ^ entry.multiplicity *
        normSq (p.eval point) := by
  let residual := normSq (entry.part.polynomial.eval point)
  let inverseScale := max 1 cofactor.bound⁻¹
  have inversePositive : 0 < cofactor.bound⁻¹ :=
    RFAP.ConstructiveFraction.inv_pos_direct cofactor.positive
  have inverseScaleOne : (1 : Coordinate) ≤ inverseScale :=
    le_max_left _ _
  have inverseScalePositive : 0 < inverseScale :=
    (by decide : (0 : Coordinate) < 1).trans_le inverseScaleOne
  have inverseLeScale : cofactor.bound⁻¹ ≤ inverseScale :=
    le_max_right _ _
  have scaleLePower : inverseScale ≤
      inverseScale ^ entry.multiplicity := by
    obtain ⟨tail, multiplicityEq⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt entry.multiplicityPositive)
    rw [multiplicityEq, pow_succ]
    have oneLeTailPower : (1 : Coordinate) ≤ inverseScale ^ tail := by
      have onePower : (1 : Coordinate) ^ tail ≤ inverseScale ^ tail :=
        RFAP.ConstructiveFraction.pow_le_pow_direct (by decide)
          inverseScaleOne tail
      simpa only [one_pow] using onePower
    calc
      inverseScale = 1 * inverseScale := by ring1
      _ ≤ inverseScale ^ tail * inverseScale :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          oneLeTailPower inverseScalePositive.le
  have inverseLePower : cofactor.bound⁻¹ ≤
      inverseScale ^ entry.multiplicity :=
    inverseLeScale.trans scaleLePower
  have localPower : chordal ^ entry.multiplicity ≤
      localConstant ^ entry.multiplicity * residual ^ entry.multiplicity := by
    have powered := RFAP.ConstructiveFraction.pow_le_pow_direct
      chordalNonnegative localBound entry.multiplicity
    simpa only [mul_pow, residual] using powered
  have cofactorTransfer :=
    cofactor_mul_factorResidualPow_le_sourceResidual decomposition before
      after entry split point cofactor
  have residualPowerBound : residual ^ entry.multiplicity ≤
      cofactor.bound⁻¹ * normSq (p.eval point) := by
    have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      cofactorTransfer
      (RFAP.ConstructiveFraction.inv_pos_direct cofactor.positive).le
    calc
      residual ^ entry.multiplicity =
          cofactor.bound⁻¹ *
            (cofactor.bound * residual ^ entry.multiplicity) := by
        rw [← RFAP.ConstructiveFraction.mul_assoc,
          RFAP.ConstructiveFraction.inv_mul_cancel cofactor.bound
            cofactor.positive.ne',
          RFAP.ConstructiveFraction.one_mul]
      _ ≤ cofactor.bound⁻¹ * normSq (p.eval point) := scaled
  have absorbed : residual ^ entry.multiplicity ≤
      inverseScale ^ entry.multiplicity * normSq (p.eval point) :=
    residualPowerBound.trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        inverseLePower (normSq_nonneg (p.eval point)))
  calc
    chordal ^ entry.multiplicity ≤
        localConstant ^ entry.multiplicity *
          residual ^ entry.multiplicity := localPower
    _ ≤ localConstant ^ entry.multiplicity *
          (inverseScale ^ entry.multiplicity * normSq (p.eval point)) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct absorbed
        (RFAP.ConstructiveFraction.pow_nonneg_direct localConstantNonnegative
          entry.multiplicity)
    _ = integerPowerConstant localConstant cofactor.bound ^
          entry.multiplicity * normSq (p.eval point) := by
      dsimp only [integerPowerConstant, inverseScale]
      rw [mul_pow]
      ring1

end RFAP.MultiplicityResidual
