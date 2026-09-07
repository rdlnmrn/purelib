import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.RFAP.ComputablePolynomial
import mathlib.RFAP.NormalizedField

/-!
# Resource envelopes for normalized dense-polynomial arithmetic

This module supplies a common finite accounting layer for dense polynomials
whose coefficients are canonical reduced rational or Gaussian-rational
records.  A single arithmetic operation advances a monotone component
envelope.  Iterating that envelope along the actual Horner and long-division
recursions gives source-only bounds for every coefficient record they carry.
-/

namespace RFAP.NormalizedPolynomialResource

open RFAP.ComputablePolynomial.DensePolynomial

abbrev DensePolynomial (K : Type*) :=
  RFAP.ComputablePolynomial.DensePolynomial K

/-- The finite facts needed to account for one normalized field operation. -/
structure MagnitudeModel (K : Type*) [RFAP.ExplicitField K] [DecidableEq K] where
  magnitude : K → Nat
  operationEnvelope : Nat → Nat
  expansive : ∀ bound, bound ≤ operationEnvelope bound
  monotone : ∀ {left right}, left ≤ right →
    operationEnvelope left ≤ operationEnvelope right
  add_le : ∀ {left right bound}, magnitude left ≤ bound →
    magnitude right ≤ bound → magnitude (left + right) ≤ operationEnvelope bound
  neg_le : ∀ {source bound}, magnitude source ≤ bound →
    magnitude (-source) ≤ operationEnvelope bound
  sub_le : ∀ {left right bound}, magnitude left ≤ bound →
    magnitude right ≤ bound → magnitude (left - right) ≤ operationEnvelope bound
  mul_le : ∀ {left right bound}, magnitude left ≤ bound →
    magnitude right ≤ bound → magnitude (left * right) ≤ operationEnvelope bound
  inv_le : ∀ {source bound}, magnitude source ≤ bound →
    magnitude source⁻¹ ≤ operationEnvelope bound
  div_le : ∀ {left right bound}, magnitude left ≤ bound →
    magnitude right ≤ bound → magnitude (left / right) ≤ operationEnvelope bound

variable {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]

/-- Iterate the one-operation envelope a displayed number of times. -/
def grow (model : MagnitudeModel K) : Nat → Nat → Nat
  | bound, 0 => bound
  | bound, steps + 1 => model.operationEnvelope (grow model bound steps)

@[simp] theorem grow_zero (model : MagnitudeModel K) (bound : Nat) :
    grow model bound 0 = bound := rfl

@[simp] theorem grow_succ (model : MagnitudeModel K) (bound steps : Nat) :
    grow model bound (steps + 1) =
      model.operationEnvelope (grow model bound steps) := rfl

theorem bound_le_grow (model : MagnitudeModel K) (bound steps : Nat) :
    bound ≤ grow model bound steps := by
  induction steps with
  | zero => exact le_refl _
  | succ steps inductionHypothesis =>
      exact inductionHypothesis.trans (model.expansive _)

theorem grow_mono_bound (model : MagnitudeModel K) {left right : Nat}
    (order : left ≤ right) (steps : Nat) :
    grow model left steps ≤ grow model right steps := by
  induction steps with
  | zero => exact order
  | succ steps inductionHypothesis =>
      exact model.monotone inductionHypothesis

theorem grow_mono_steps (model : MagnitudeModel K) (bound : Nat)
    {first second : Nat} (order : first ≤ second) :
    grow model bound first ≤ grow model bound second := by
  obtain ⟨extra, equation⟩ := Nat.le.dest order
  subst second
  clear order
  induction extra with
  | zero => simp
  | succ extra inductionHypothesis =>
      exact inductionHypothesis.trans (model.expansive _)

theorem grow_add (model : MagnitudeModel K) (bound first second : Nat) :
    grow model (grow model bound first) second =
      grow model bound (first + second) := by
  induction second with
  | zero => simp
  | succ second inductionHypothesis =>
      rw [grow_succ, inductionHypothesis, Nat.add_succ, grow_succ]

/-- Every member of a finite coefficient list fits one common component
envelope. -/
def ListWithin (model : MagnitudeModel K) (values : List K)
    (bound : Nat) : Prop :=
  ∀ value ∈ values, model.magnitude value ≤ bound

def PolynomialWithin (model : MagnitudeModel K)
    (polynomial : DensePolynomial K) (bound : Nat) : Prop :=
  ListWithin model polynomial.coeffs bound

theorem listWithin_mono (model : MagnitudeModel K) {values : List K}
    {left right : Nat} (bounded : ListWithin model values left)
    (order : left ≤ right) : ListWithin model values right := by
  intro value member
  exact (bounded value member).trans order

theorem polynomialWithin_mono (model : MagnitudeModel K)
    {polynomial : DensePolynomial K} {left right : Nat}
    (bounded : PolynomialWithin model polynomial left)
    (order : left ≤ right) : PolynomialWithin model polynomial right :=
  listWithin_mono model bounded order

theorem listWithin_dropWhile (model : MagnitudeModel K) {values : List K}
    {bound : Nat} (bounded : ListWithin model values bound)
    (predicate : K → Bool) :
    ListWithin model (values.dropWhile predicate) bound := by
  intro value member
  exact bounded value ((List.dropWhile_sublist predicate).subset member)

theorem normalize_within (model : MagnitudeModel K)
    {polynomial : DensePolynomial K} {bound : Nat}
    (bounded : PolynomialWithin model polynomial bound) :
    PolynomialWithin model polynomial.normalize bound :=
  listWithin_dropWhile model bounded _

theorem zero_within (model : MagnitudeModel K) (bound : Nat) :
    PolynomialWithin model (0 : DensePolynomial K) bound := by
  intro value member
  simp at member

theorem constant_within (model : MagnitudeModel K) {value : K} {bound : Nat}
    (bounded : model.magnitude value ≤ bound) :
    PolynomialWithin model (constant value) bound := by
  intro candidate member
  have equal : candidate = value := by
    simpa only [constant_coeffs, List.mem_singleton] using member
  subst candidate
  exact bounded

private theorem evalFold_within (model : MagnitudeModel K) {point : K}
    (pointWithin : model.magnitude point ≤ bound) :
    ∀ (coefficients : List K) (accumulator : K),
      ListWithin model coefficients bound →
      model.magnitude accumulator ≤ bound →
      model.magnitude
          (coefficients.foldl (fun current coefficient =>
            current * point + coefficient) accumulator) ≤
        grow model bound (2 * coefficients.length)
  | [], _, _, accumulatorWithin => by
      simpa using accumulatorWithin
  | coefficient :: remaining, accumulator, coefficientsWithin,
      accumulatorWithin => by
      simp only [List.foldl_cons, List.length_cons]
      have productWithin := model.mul_le accumulatorWithin pointWithin
      have coefficientWithin :=
        (coefficientsWithin coefficient List.mem_cons_self).trans
          (model.expansive bound)
      have nextWithin := model.add_le productWithin
        coefficientWithin
      have remainingWithin : ListWithin model remaining bound :=
        fun value member => coefficientsWithin value
          (List.mem_cons_of_mem coefficient member)
      have recursive := evalFold_within model
        (pointWithin := pointWithin.trans
          (bound_le_grow model bound 2))
        remaining (accumulator * point + coefficient)
        (listWithin_mono model remainingWithin
          (bound_le_grow model bound 2)) nextWithin
      rw [grow_add] at recursive
      apply recursive.trans
      apply grow_mono_steps model bound
      have stepsEqual :
          2 + 2 * remaining.length = 2 * (remaining.length + 1) := by
        rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      exact Nat.le_of_eq stepsEqual

/-- Every normalized Horner accumulator, and in particular its result, fits
the twice-per-coefficient operation envelope. -/
theorem eval_within (model : MagnitudeModel K)
    {polynomial : DensePolynomial K} {point : K} {bound : Nat}
    (zeroWithin : model.magnitude 0 ≤ bound)
    (pointWithin : model.magnitude point ≤ bound)
    (polynomialWithin : PolynomialWithin model polynomial bound) :
    model.magnitude (polynomial.eval point) ≤
      grow model bound (2 * polynomial.coeffs.length) := by
  exact evalFold_within model pointWithin polynomial.coeffs 0
    polynomialWithin zeroWithin

theorem padLeft_within (model : MagnitudeModel K) {values : List K}
    {bound : Nat} (zeroBound : model.magnitude 0 ≤ bound)
    (bounded : ListWithin model values bound) (padding : Nat) :
    ListWithin model (padLeft padding values) bound := by
  intro value member
  rw [padLeft, List.mem_append] at member
  rcases member with paddingMember | valueMember
  · rw [List.eq_of_mem_replicate paddingMember]
    exact zeroBound
  · exact bounded value valueMember

private theorem zipWith_add_within (model : MagnitudeModel K) :
    ∀ {left right : List K} {bound : Nat},
      ListWithin model left bound → ListWithin model right bound →
      ListWithin model (List.zipWith (· + ·) left right)
        (model.operationEnvelope bound)
  | [], _, _, _, _ => by
      intro value member
      simp at member
  | _ :: _, [], _, _, _ => by
      intro value member
      simp at member
  | left :: leftTail, right :: rightTail, bound, leftWithin, rightWithin => by
      intro value member
      simp only [List.zipWith_cons_cons, List.mem_cons] at member
      rcases member with head | tail
      · rw [head]
        exact model.add_le
          (leftWithin left (List.mem_cons_self))
          (rightWithin right (List.mem_cons_self))
      · exact zipWith_add_within model
          (fun candidate candidateMember => leftWithin candidate
            (List.mem_cons_of_mem left candidateMember))
          (fun candidate candidateMember => rightWithin candidate
            (List.mem_cons_of_mem right candidateMember)) value tail

theorem add_within (model : MagnitudeModel K)
    {left right : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (leftWithin : PolynomialWithin model left bound)
    (rightWithin : PolynomialWithin model right bound) :
    PolynomialWithin model (left + right) (grow model bound 1) := by
  unfold PolynomialWithin
  change ListWithin model (add left right).coeffs _
  unfold add
  apply listWithin_dropWhile
  apply zipWith_add_within model
  · exact padLeft_within model zeroBound leftWithin _
  · exact padLeft_within model zeroBound rightWithin _

theorem neg_within (model : MagnitudeModel K)
    {polynomial : DensePolynomial K} {bound : Nat}
    (bounded : PolynomialWithin model polynomial bound) :
    PolynomialWithin model (-polynomial) (grow model bound 1) := by
  intro value member
  rw [neg_coeffs, QuotientFreeList.mem_map] at member
  rcases member with ⟨source, sourceMember, rfl⟩
  exact model.neg_le (normalize_within model bounded source sourceMember)

theorem sub_within (model : MagnitudeModel K)
    {left right : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (leftWithin : PolynomialWithin model left bound)
    (rightWithin : PolynomialWithin model right bound) :
    PolynomialWithin model (left - right) (grow model bound 2) := by
  change PolynomialWithin model (left + -right) _
  have negated := neg_within model rightWithin
  have leftOne := polynomialWithin_mono model leftWithin
    (bound_le_grow model bound 1)
  have added := add_within model
    (zeroBound.trans (bound_le_grow model bound 1)) leftOne negated
  rw [grow_add] at added
  simpa using added

theorem shift_within (model : MagnitudeModel K)
    {polynomial : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (bounded : PolynomialWithin model polynomial bound) (amount : Nat) :
    PolynomialWithin model (shift amount polynomial) bound := by
  rw [shift]
  split
  · exact zero_within model bound
  · intro value member
    rw [List.mem_append] at member
    rcases member with source | padding
    · exact normalize_within model bounded value source
    · rw [List.eq_of_mem_replicate padding]
      exact zeroBound

theorem scale_within (model : MagnitudeModel K)
    {scalar : K} {polynomial : DensePolynomial K} {bound : Nat}
    (scalarWithin : model.magnitude scalar ≤ bound)
    (bounded : PolynomialWithin model polynomial bound) :
    PolynomialWithin model (scale scalar polynomial) (grow model bound 1) := by
  intro value member
  unfold scale at member
  have rawMember := (List.dropWhile_sublist (fun x : K => decide (x = 0))).subset member
  change value ∈ polynomial.coeffs.map (scalar * ·) at rawMember
  rw [QuotientFreeList.mem_map] at rawMember
  rcases rawMember with ⟨source, sourceMember, rfl⟩
  exact model.mul_le scalarWithin (bounded source sourceMember)

private theorem mulFold_within (model : MagnitudeModel K)
    {right : DensePolynomial K} {source : List K}
    {accumulator : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (sourceWithin : ListWithin model source bound)
    (rightWithin : PolynomialWithin model right bound)
    (accumulatorWithin : PolynomialWithin model accumulator bound) :
    PolynomialWithin model
      (source.foldl (fun value coefficient =>
        shift 1 value + scale coefficient right) accumulator)
      (grow model bound (2 * source.length)) := by
  induction source generalizing accumulator bound with
  | nil => simpa using accumulatorWithin
  | cons coefficient remaining inductionHypothesis =>
      simp only [List.foldl_cons, List.length_cons]
      have sourceHead := sourceWithin coefficient (List.mem_cons_self)
      have sourceTail : ListWithin model remaining bound := by
        intro value member
        exact sourceWithin value (List.mem_cons_of_mem coefficient member)
      let nextBound := grow model bound 2
      have boundLe : bound ≤ nextBound := bound_le_grow model bound 2
      have nextWithin : PolynomialWithin model
          (shift 1 accumulator + scale coefficient right) nextBound := by
        have shifted := shift_within model zeroBound accumulatorWithin 1
        have scaled := scale_within model sourceHead rightWithin
        have zeroNext : model.magnitude 0 ≤ grow model bound 1 :=
          zeroBound.trans (bound_le_grow model bound 1)
        exact add_within model zeroNext
          (polynomialWithin_mono model shifted (bound_le_grow model bound 1))
          scaled
      have recursive := inductionHypothesis
        (bound := nextBound)
        (zeroBound.trans boundLe)
        (listWithin_mono model sourceTail boundLe)
        (polynomialWithin_mono model rightWithin boundLe)
        nextWithin
      rw [grow_add] at recursive
      simpa only [List.length_cons, Nat.mul_add, Nat.mul_one,
        show 2 * (remaining.length + 1) = 2 + 2 * remaining.length by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_comm],
        Nat.add_comm 2 (2 * remaining.length)] using recursive

theorem mul_within (model : MagnitudeModel K)
    {left right : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (leftWithin : PolynomialWithin model left bound)
    (rightWithin : PolynomialWithin model right bound) :
    PolynomialWithin model (left * right)
      (grow model bound (2 * left.coeffs.length)) := by
  change PolynomialWithin model (mulPolynomial left right) _
  unfold mulPolynomial
  exact mulFold_within model zeroBound leftWithin rightWithin
    (zero_within model bound)

theorem leadingCoeff_le (model : MagnitudeModel K)
    {polynomial : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (bounded : PolynomialWithin model polynomial bound) :
    model.magnitude polynomial.leadingCoeff ≤ bound := by
  unfold leadingCoeff
  cases coefficients : polynomial.normalize.coeffs with
  | nil => simpa only [coefficients, List.headD_nil] using zeroBound
  | cons head tail =>
      apply normalize_within model bounded head
      rw [coefficients]
      exact List.mem_cons_self

theorem leadQuotient_within (model : MagnitudeModel K)
    {left right : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (leftWithin : PolynomialWithin model left bound)
    (rightWithin : PolynomialWithin model right bound) :
    PolynomialWithin model (leadQuotient left right) (grow model bound 1) := by
  unfold leadQuotient
  apply shift_within model
  · exact zeroBound.trans (bound_le_grow model bound 1)
  · apply constant_within
    exact model.div_le
      (leadingCoeff_le model zeroBound leftWithin)
      (leadingCoeff_le model zeroBound rightWithin)

theorem cancelLead_within (model : MagnitudeModel K)
    {left right : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (leftWithin : PolynomialWithin model left bound)
    (rightWithin : PolynomialWithin model right bound) :
    PolynomialWithin model (cancelLead left right) (grow model bound 4) := by
  unfold cancelLead
  have quotient : model.magnitude (left.leadingCoeff / right.leadingCoeff) ≤
      grow model bound 1 :=
    model.div_le (leadingCoeff_le model zeroBound leftWithin)
      (leadingCoeff_le model zeroBound rightWithin)
  have rightOne := polynomialWithin_mono model rightWithin
    (bound_le_grow model bound 1)
  have scaled := scale_within model quotient rightOne
  rw [grow_add] at scaled
  have shifted := shift_within model
    (zeroBound.trans (bound_le_grow model bound 2)) scaled
    (left.natDegree - right.natDegree)
  have leftTwo := polynomialWithin_mono model leftWithin
    (bound_le_grow model bound 2)
  have difference := sub_within model
    (zeroBound.trans (bound_le_grow model bound 2)) leftTwo shifted
  rw [grow_add] at difference
  simpa using difference

/-- Both polynomials returned by a fuel-bounded normalized long division fit
the same source-only envelope. -/
theorem divLoop_within (model : MagnitudeModel K)
    (fuel : Nat) {left right quotient : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (leftWithin : PolynomialWithin model left bound)
    (rightWithin : PolynomialWithin model right bound)
    (quotientWithin : PolynomialWithin model quotient bound) :
    PolynomialWithin model (divLoop fuel left right quotient).quotient
        (grow model bound (4 * fuel)) ∧
      PolynomialWithin model (divLoop fuel left right quotient).remainder
        (grow model bound (4 * fuel)) := by
  induction fuel generalizing left quotient bound with
  | zero => exact ⟨quotientWithin, leftWithin⟩
  | succ fuel inductionHypothesis =>
      rw [divLoop_succ]
      split
      · exact ⟨polynomialWithin_mono model quotientWithin
            (bound_le_grow model bound (4 * (fuel + 1))),
          polynomialWithin_mono model leftWithin
            (bound_le_grow model bound (4 * (fuel + 1)))⟩
      · dsimp only
        let nextBound := grow model bound 4
        have boundLe : bound ≤ nextBound := bound_le_grow model bound 4
        have nextLeft := cancelLead_within model zeroBound leftWithin rightWithin
        have term := leadQuotient_within model zeroBound leftWithin rightWithin
        have nextQuotient : PolynomialWithin model
            (quotient + leadQuotient left right) nextBound := by
          have quotientTwo := polynomialWithin_mono model quotientWithin
            (bound_le_grow model bound 2)
          have termTwo := polynomialWithin_mono model term
            (grow_mono_steps model bound (by decide : 1 ≤ 2))
          have added := add_within model
            (zeroBound.trans (bound_le_grow model bound 2))
            quotientTwo termTwo
          rw [grow_add] at added
          exact polynomialWithin_mono model added
            (grow_mono_steps model bound (by decide : 3 ≤ 4))
        have recursive := inductionHypothesis
          (bound := nextBound)
          (zeroBound.trans boundLe) nextLeft
          (polynomialWithin_mono model rightWithin boundLe) nextQuotient
        rw [grow_add] at recursive
        simpa only [Nat.mul_add, Nat.mul_one,
          show 4 * (fuel + 1) = 4 + 4 * fuel by
            rw [Nat.mul_add, Nat.mul_one, Nat.add_comm],
          Nat.add_comm 4 (4 * fuel)] using recursive

/-- Executable normalized long division has at most `degreeCount + 1`
cancellation rounds, and every returned coefficient fits the corresponding
three-operation-per-round envelope. -/
theorem divMod_within (model : MagnitudeModel K)
    {left right : DensePolynomial K} {bound : Nat}
    (zeroBound : model.magnitude 0 ≤ bound)
    (leftWithin : PolynomialWithin model left bound)
    (rightWithin : PolynomialWithin model right bound) :
    PolynomialWithin model (divMod left right).quotient
        (grow model bound (4 * (left.degreeCount + 1))) ∧
      PolynomialWithin model (divMod left right).remainder
        (grow model bound (4 * (left.degreeCount + 1))) := by
  unfold divMod
  exact divLoop_within model _ zeroBound
    (normalize_within model leftWithin)
    (normalize_within model rightWithin) (zero_within model bound)

/-! ## Concrete normalized coefficient models -/

def rationalOperationEnvelope (bound : Nat) : Nat :=
  max bound (max
    (RFAP.NormalizedFraction.additiveMagnitudeEnvelope bound bound)
    (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope bound bound))

theorem rationalOperationEnvelope_mono {left right : Nat}
    (order : left ≤ right) :
    rationalOperationEnvelope left ≤ rationalOperationEnvelope right := by
  unfold rationalOperationEnvelope
  exact max_le_max order (max_le_max
    (RFAP.NormalizedFraction.additiveMagnitudeEnvelope_mono order order)
    (RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono order order))

def rationalModel : MagnitudeModel RFAP.NormalizedFraction.ReducedFraction where
  magnitude := RFAP.NormalizedFraction.componentMagnitude
  operationEnvelope := rationalOperationEnvelope
  expansive := fun bound => le_max_left _ _
  monotone := rationalOperationEnvelope_mono
  add_le := by
    intro left right bound leftLe rightLe
    exact (RFAP.NormalizedFraction.componentMagnitude_add_le left right).trans
      ((RFAP.NormalizedFraction.additiveMagnitudeEnvelope_mono leftLe rightLe).trans
        ((le_max_left _ _).trans (le_max_right _ _)))
  neg_le := by
    intro source bound sourceLe
    exact (RFAP.NormalizedFraction.componentMagnitude_neg_le source).trans
      (sourceLe.trans (le_max_left _ _))
  sub_le := by
    intro left right bound leftLe rightLe
    exact (RFAP.NormalizedFraction.componentMagnitude_sub_le left right).trans
      ((RFAP.NormalizedFraction.additiveMagnitudeEnvelope_mono leftLe rightLe).trans
        ((le_max_left _ _).trans (le_max_right _ _)))
  mul_le := by
    intro left right bound leftLe rightLe
    exact (RFAP.NormalizedFraction.componentMagnitude_mul_le left right).trans
      ((RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono leftLe rightLe).trans
        ((le_max_right _ _).trans (le_max_right _ _)))
  inv_le := by
    intro source bound sourceLe
    exact (RFAP.NormalizedFraction.componentMagnitude_inv_le source).trans
      (sourceLe.trans (le_max_left _ _))
  div_le := by
    intro left right bound leftLe rightLe
    exact (RFAP.NormalizedFraction.componentMagnitude_div_le left right).trans
      ((RFAP.NormalizedFraction.multiplicativeMagnitudeEnvelope_mono leftLe rightLe).trans
        ((le_max_right _ _).trans (le_max_right _ _)))

def gaussianOperationEnvelope (bound : Nat) : Nat :=
  max bound (max
    (RFAP.NormalizedGaussian.addMagnitudeEnvelope bound bound)
    (max (RFAP.NormalizedGaussian.mulMagnitudeEnvelope bound bound)
      (max (RFAP.NormalizedGaussian.invMagnitudeEnvelope bound)
        (RFAP.NormalizedGaussian.divMagnitudeEnvelope bound bound))))

theorem gaussianOperationEnvelope_mono {left right : Nat}
    (order : left ≤ right) :
    gaussianOperationEnvelope left ≤ gaussianOperationEnvelope right := by
  unfold gaussianOperationEnvelope
  exact max_le_max order (max_le_max
    (RFAP.NormalizedGaussian.addMagnitudeEnvelope_mono order order)
    (max_le_max (RFAP.NormalizedGaussian.mulMagnitudeEnvelope_mono order order)
      (max_le_max (RFAP.NormalizedGaussian.invMagnitudeEnvelope_mono order)
        (RFAP.NormalizedGaussian.divMagnitudeEnvelope_mono order order))))

def gaussianModel : MagnitudeModel RFAP.NormalizedGaussian.Gaussian where
  magnitude := RFAP.NormalizedGaussian.componentMagnitude
  operationEnvelope := gaussianOperationEnvelope
  expansive := fun bound => le_max_left _ _
  monotone := gaussianOperationEnvelope_mono
  add_le := by
    intro left right bound leftLe rightLe
    exact (RFAP.NormalizedGaussian.componentMagnitude_add_le left right).trans
      ((RFAP.NormalizedGaussian.addMagnitudeEnvelope_mono leftLe rightLe).trans
        ((le_max_left _ _).trans (le_max_right _ _)))
  neg_le := by
    intro source bound sourceLe
    exact (RFAP.NormalizedGaussian.componentMagnitude_neg_le source).trans
      (sourceLe.trans (le_max_left _ _))
  sub_le := by
    intro left right bound leftLe rightLe
    exact (RFAP.NormalizedGaussian.componentMagnitude_sub_le left right).trans
      ((RFAP.NormalizedGaussian.addMagnitudeEnvelope_mono leftLe rightLe).trans
        ((le_max_left _ _).trans (le_max_right _ _)))
  mul_le := by
    intro left right bound leftLe rightLe
    exact (RFAP.NormalizedGaussian.componentMagnitude_mul_le left right).trans
      ((RFAP.NormalizedGaussian.mulMagnitudeEnvelope_mono leftLe rightLe).trans
        ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))
  inv_le := by
    intro source bound sourceLe
    exact (RFAP.NormalizedGaussian.componentMagnitude_inv_le source).trans
      ((RFAP.NormalizedGaussian.invMagnitudeEnvelope_mono sourceLe).trans
        ((le_max_left _ _).trans ((le_max_right _ _).trans
          ((le_max_right _ _).trans (le_max_right _ _)))))
  div_le := by
    intro left right bound leftLe rightLe
    exact (RFAP.NormalizedGaussian.componentMagnitude_div_le left right).trans
      ((RFAP.NormalizedGaussian.divMagnitudeEnvelope_mono leftLe rightLe).trans
        ((le_max_right _ _).trans ((le_max_right _ _).trans
          ((le_max_right _ _).trans (le_max_right _ _)))))

end RFAP.NormalizedPolynomialResource
