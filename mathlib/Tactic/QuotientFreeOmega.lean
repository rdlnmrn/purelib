import mathlib.Tactic.QuotientFreeRing
import Lean.Elab.Tactic.Omega

/-!
# Quotient-free Omega proof reconstruction

Lean's Omega procedure computes a finite contradiction certificate.  Some of
the small checker lemmas used to turn that certificate into a kernel proof
currently inherit `Quot.sound` through generic list and function
extensionality.  This module gives those finite lemmas direct structural
proofs and substitutes them into the generated certificate.
-/

namespace QuotientFreeOmega

open Lean.Omega

local macro "coordinate_rfl" : tactic =>
  `(tactic|
    simp only [LinearCombo.eval, LinearCombo.coordinate, Coeffs.ofList,
      Coeffs.set, Coeffs.dot, IntList.set, IntList.dot, IntList.mul_def,
      IntList.sum, List.foldr, List.zipWith, Int.one_mul, Int.zero_mul, Int.add_zero,
      Int.zero_add])

theorem coordinate_eval_0 :
    (LinearCombo.coordinate 0).eval (.ofList (a0 :: tail)) = a0 := by
  coordinate_rfl

theorem coordinate_eval_1 :
    (LinearCombo.coordinate 1).eval (.ofList (a0 :: a1 :: tail)) = a1 := by
  coordinate_rfl

theorem coordinate_eval_2 :
    (LinearCombo.coordinate 2).eval (.ofList (a0 :: a1 :: a2 :: tail)) = a2 := by
  coordinate_rfl

theorem coordinate_eval_3 :
    (LinearCombo.coordinate 3).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: tail)) = a3 := by
  coordinate_rfl

theorem coordinate_eval_4 :
    (LinearCombo.coordinate 4).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: tail)) = a4 := by
  coordinate_rfl

theorem coordinate_eval_5 :
    (LinearCombo.coordinate 5).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: tail)) = a5 := by
  coordinate_rfl

theorem coordinate_eval_6 :
    (LinearCombo.coordinate 6).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: tail)) = a6 := by
  coordinate_rfl

theorem coordinate_eval_7 :
    (LinearCombo.coordinate 7).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: tail)) = a7 := by
  coordinate_rfl

theorem coordinate_eval_8 :
    (LinearCombo.coordinate 8).eval
      (.ofList (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: tail)) = a8 := by
  coordinate_rfl

theorem coordinate_eval_9 :
    (LinearCombo.coordinate 9).eval
      (.ofList
        (a0 :: a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: a7 :: a8 :: a9 :: tail)) = a9 := by
  coordinate_rfl

theorem coordinate_eval (index : Nat) (values : Coeffs) :
    (LinearCombo.coordinate index).eval values = values.get index := by
  induction index generalizing values with
  | zero =>
      cases values with
      | nil =>
          rw [LinearCombo.eval_nil]
          rfl
      | cons head tail =>
          exact coordinate_eval_0
  | succ index inductionHypothesis =>
      cases values with
      | nil =>
          rw [LinearCombo.eval_nil]
          rfl
      | cons head tail =>
          simp only [LinearCombo.eval, LinearCombo.coordinate, Coeffs.set,
            Coeffs.dot, Coeffs.get, IntList.set, IntList.dot,
            IntList.mul_def, IntList.sum, List.foldr, List.zipWith,
            IntList.get_cons_succ, Int.zero_mul, Int.zero_add]
          simpa only [LinearCombo.eval, LinearCombo.coordinate, Coeffs.set,
            Coeffs.dot, IntList.dot, IntList.mul_def, IntList.sum,
            List.foldr, List.zipWith, Int.zero_add] using
              inductionHypothesis tail

/-- Right-zero law for Omega's padded pointwise list addition, proved by
structural recursion rather than function extensionality. -/
theorem intList_add_nil : ∀ values : IntList, values + [] = values
  | [] => rfl
  | head :: tail => by
      change List.map (fun value : Int => value + 0) (head :: tail) =
        head :: tail
      have tailEquality := intList_add_nil tail
      rw [IntList.add_def, List.zipWithAll_nil] at tailEquality
      change List.map (fun value : Int => value + 0) tail = tail at tailEquality
      rw [List.map, Int.add_zero, tailEquality]

/-- Left-zero law for Omega's padded pointwise list addition. -/
theorem intList_nil_add : ∀ values : IntList, [] + values = values
  | [] => rfl
  | head :: tail => by
      change (0 + head) :: ([] + tail) = head :: tail
      rw [Int.zero_add, intList_nil_add tail]

theorem intList_sub_nil : ∀ values : IntList, values - [] = values
  | [] => rfl
  | head :: tail => by
      change List.map (fun value : Int => value - 0) (head :: tail) =
        head :: tail
      have tailEquality := intList_sub_nil tail
      rw [IntList.sub_def, List.zipWithAll_nil] at tailEquality
      change List.map (fun value : Int => value - 0) tail = tail at tailEquality
      rw [List.map, Int.sub_zero, tailEquality]

/-- Pointwise subtraction is addition of pointwise negation, proved directly
on the finite coefficient lists. -/
theorem intList_sub_eq_add_neg : ∀ left right : IntList,
    left - right = left + -right
  | [], [] => rfl
  | [], head :: tail => by
      change (0 - head) :: ([] - tail) =
        (0 + -head) :: ([] + -tail)
      rw [Int.zero_sub, Int.zero_add, intList_sub_eq_add_neg [] tail]
  | head :: tail, [] => by
      rw [intList_sub_nil, show -([] : IntList) = [] from rfl,
        intList_add_nil]
  | left :: leftTail, right :: rightTail => by
      change (left - right) :: (leftTail - rightTail) =
        (left + -right) :: (leftTail + -rightTail)
      rw [Int.sub_eq_add_neg,
        intList_sub_eq_add_neg leftTail rightTail]

/-- Dot product distributes over Omega's padded coefficient addition. -/
theorem intList_dot_distrib_left : ∀ left right values : IntList,
    IntList.dot (left + right) values =
      IntList.dot left values + IntList.dot right values
  | [], right, values => by
      rw [intList_nil_add]
      change IntList.dot right values = 0 + IntList.dot right values
      rw [Int.zero_add]
  | left, [], values => by
      rw [intList_add_nil]
      change IntList.dot left values = IntList.dot left values + 0
      rw [Int.add_zero]
  | left :: leftTail, right :: rightTail, [] => by
      change 0 = 0 + 0
      rw [Int.zero_add]
  | left :: leftTail, right :: rightTail, value :: valueTail => by
      change (left + right) * value +
          IntList.dot (leftTail + rightTail) valueTail =
        (left * value + IntList.dot leftTail valueTail) +
          (right * value + IntList.dot rightTail valueTail)
      rw [intList_dot_distrib_left leftTail rightTail valueTail]
      ring1

/-- Updating one displayed coefficient changes its dot product by exactly
the corresponding coordinate correction.  This is the structural finite-list
argument needed by Omega's modular-elimination certificate. -/
theorem intList_dot_set_left : ∀ (source values : IntList)
    (index : Nat) (replacement : Int),
    IntList.dot (IntList.set source index replacement) values =
      IntList.dot source values +
        (replacement - IntList.get source index) *
          IntList.get values index
  | [], [], 0, replacement => by
      change 0 = 0 + (replacement - 0) * 0
      ring1
  | [], value :: values, 0, replacement => by
      change replacement * value + 0 =
        0 + (replacement - 0) * value
      ring1
  | [], [], index + 1, replacement => by
      change 0 = 0 + (replacement - 0) * 0
      ring1
  | [], value :: values, index + 1, replacement => by
      change 0 * value +
          IntList.dot (IntList.set [] index replacement) values =
        0 + (replacement - 0) * IntList.get values index
      rw [Int.zero_mul, Int.zero_add,
        intList_dot_set_left [] values index replacement]
      rfl
  | sourceHead :: sourceTail, [], 0, replacement => by
      change 0 = 0 + (replacement - sourceHead) * 0
      ring1
  | sourceHead :: sourceTail, value :: values, 0, replacement => by
      change replacement * value + IntList.dot sourceTail values =
        (sourceHead * value + IntList.dot sourceTail values) +
          (replacement - sourceHead) * value
      ring1
  | sourceHead :: sourceTail, [], index + 1, replacement => by
      change 0 = 0 +
        (replacement - IntList.get sourceTail index) * 0
      ring1
  | sourceHead :: sourceTail, value :: values, index + 1, replacement => by
      change sourceHead * value +
          IntList.dot (IntList.set sourceTail index replacement) values =
        (sourceHead * value + IntList.dot sourceTail values) +
          (replacement - IntList.get sourceTail index) *
            IntList.get values index
      rw [intList_dot_set_left sourceTail values index replacement]
      ring1

/-- `Coeffs` is the same finite integer-list representation, so the direct
update calculation applies without the upstream extensional list lemma. -/
theorem coeffs_dot_set_left (source values : Coeffs) (index : Nat)
    (replacement : Int) :
    Coeffs.dot (Coeffs.set source index replacement) values =
      Coeffs.dot source values +
        (replacement - Coeffs.get source index) * Coeffs.get values index :=
  intList_dot_set_left source values index replacement

/-- Evaluation commutes with addition of finite linear combinations. -/
theorem add_eval (left right : LinearCombo) (values : Coeffs) :
    (left + right).eval values = left.eval values + right.eval values := by
  rcases left with ⟨leftConstant, leftCoefficients⟩
  rcases right with ⟨rightConstant, rightCoefficients⟩
  change (leftConstant + rightConstant) +
      IntList.dot (leftCoefficients + rightCoefficients) values =
    (leftConstant + IntList.dot leftCoefficients values) +
      (rightConstant + IntList.dot rightCoefficients values)
  rw [intList_dot_distrib_left]
  ring1

/-- Evaluation commutes with subtraction of finite linear combinations. -/
theorem sub_eval (left right : LinearCombo) (values : Coeffs) :
    (left - right).eval values = left.eval values - right.eval values := by
  rcases left with ⟨leftConstant, leftCoefficients⟩
  rcases right with ⟨rightConstant, rightCoefficients⟩
  change (leftConstant - rightConstant) +
      IntList.dot (leftCoefficients - rightCoefficients) values =
    (leftConstant + IntList.dot leftCoefficients values) -
      (rightConstant + IntList.dot rightCoefficients values)
  rw [intList_sub_eq_add_neg, intList_dot_distrib_left,
    IntList.dot_neg_left]
  ring1

theorem mul_eval_of_const_left (left right : LinearCombo) (values : Coeffs)
    (constantLeft : left.coeffs.isZero) :
    (LinearCombo.mul left right).eval values =
      left.eval values * right.eval values := by
  have zeroDot : IntList.dot left.coeffs values = 0 :=
    IntList.dot_of_left_zero constantLeft
  change left.coeffs.dot values = 0 at zeroDot
  unfold LinearCombo.mul
  rw [sub_eval, add_eval, LinearCombo.smul_eval,
    LinearCombo.smul_eval]
  simp only [LinearCombo.eval, IntList.dot_nil_left, Int.add_zero]
  rw [zeroDot]
  ring1

theorem mul_eval_of_const_right (left right : LinearCombo) (values : Coeffs)
    (constantRight : right.coeffs.isZero) :
    (LinearCombo.mul left right).eval values =
      left.eval values * right.eval values := by
  have zeroDot : IntList.dot right.coeffs values = 0 :=
    IntList.dot_of_left_zero constantRight
  change right.coeffs.dot values = 0 at zeroDot
  unfold LinearCombo.mul
  rw [sub_eval, add_eval, LinearCombo.smul_eval,
    LinearCombo.smul_eval]
  simp only [LinearCombo.eval, IntList.dot_nil_left, Int.add_zero]
  rw [zeroDot]
  ring1

theorem mul_eval (left right : LinearCombo) (values : Coeffs)
    (oneConstant : left.coeffs.isZero ∨ right.coeffs.isZero) :
    (LinearCombo.mul left right).eval values =
      left.eval values * right.eval values := by
  rcases oneConstant with constantLeft | constantRight
  · exact mul_eval_of_const_left left right values constantLeft
  · exact mul_eval_of_const_right left right values constantRight

/-- The map used by the empty-right branch of `IntList.combo` reduces
pointwise to scalar multiplication. -/
theorem intList_combo_map_nil_right (leftScale rightScale : Int) :
    ∀ left : List Int,
      List.map (fun value => leftScale * value + rightScale * 0) left =
        List.map (fun value => leftScale * value) left
  | [] => rfl
  | left :: leftTail => by
      change (leftScale * left + rightScale * 0) ::
          List.map (fun value => leftScale * value + rightScale * 0) leftTail =
        leftScale * left :: List.map (fun value => leftScale * value) leftTail
      rw [intList_combo_map_nil_right leftScale rightScale leftTail,
        Int.mul_zero, Int.add_zero]

/-- Combining a coefficient list with an empty right-hand list is just scalar
multiplication.  This branch of `List.zipWithAll` is a map over the whole
left-hand list, so we expose that finite recursion explicitly. -/
theorem intList_combo_nil_right (leftScale rightScale : Int)
    (left : IntList) :
    IntList.combo leftScale left rightScale [] = leftScale * left := by
  rw [IntList.combo, List.zipWithAll_nil, IntList.smul_def]
  exact intList_combo_map_nil_right leftScale rightScale left

/-- Omega's coefficient combination is the displayed sum of two scalar
multiples, by recursion on the two finite lists. -/
theorem intList_combo_eq_smul_add_smul (leftScale : Int) :
    ∀ left : IntList, ∀ rightScale : Int, ∀ right : IntList,
      IntList.combo leftScale left rightScale right =
        leftScale * left + rightScale * right
  | [], rightScale, [] => rfl
  | [], rightScale, right :: rightTail => by
      change (leftScale * 0 + rightScale * right) ::
          IntList.combo leftScale [] rightScale rightTail =
        [] + rightScale * (right :: rightTail)
      rw [Int.mul_zero, Int.zero_add, intList_nil_add]
      change rightScale * right ::
          IntList.combo leftScale [] rightScale rightTail =
        rightScale * right :: rightScale * rightTail
      rw [intList_combo_eq_smul_add_smul leftScale [] rightScale rightTail,
        show leftScale * ([] : IntList) = [] from rfl,
        intList_nil_add]
  | left :: leftTail, rightScale, [] => by
      rw [intList_combo_nil_right,
        show rightScale * ([] : IntList) = [] from rfl,
        intList_add_nil]
  | left :: leftTail, rightScale, right :: rightTail => by
      change (leftScale * left + rightScale * right) ::
          IntList.combo leftScale leftTail rightScale rightTail =
        (leftScale * left + rightScale * right) ::
          (leftScale * leftTail + rightScale * rightTail)
      rw [intList_combo_eq_smul_add_smul leftScale leftTail rightScale rightTail]

/-- Soundness of combining two finite Omega constraints, using the direct
coefficient identities above. -/
theorem combo_sat' (leftConstraint rightConstraint : Constraint)
    (leftScale : Int) (leftCoefficients : Coeffs)
    (rightScale : Int) (rightCoefficients values : Coeffs)
    (leftSatisfies : leftConstraint.sat' leftCoefficients values)
    (rightSatisfies : rightConstraint.sat' rightCoefficients values) :
    (Constraint.combo leftScale leftConstraint rightScale rightConstraint).sat'
      (Coeffs.combo leftScale leftCoefficients rightScale rightCoefficients)
      values := by
  rw [Constraint.sat']
  change (Constraint.combo leftScale leftConstraint rightScale rightConstraint).sat
      (IntList.dot
        (IntList.combo leftScale leftCoefficients rightScale rightCoefficients)
        values) = true
  rw [
    intList_combo_eq_smul_add_smul,
    intList_dot_distrib_left,
    IntList.dot_smul_left, IntList.dot_smul_left]
  exact Constraint.combo_sat leftScale leftSatisfies rightScale rightSatisfies

/-- Soundness of Omega's finite modular-elimination step, with the changed
dot-product coordinate justified by structural recursion above. -/
theorem bmod_sat (modulus : Nat) (remainder : Int) (index : Nat)
    (source values : Coeffs)
    (indexBeyondSource : source.length ≤ index)
    (newCoordinate :
      Coeffs.get values index = bmod_div_term modulus source values)
    (sourceSatisfies :
      (Constraint.exact remainder).sat' source values) :
    (Constraint.exact (Int.bmod remainder modulus)).sat'
      (bmod_coeffs modulus index source) values := by
  simp at sourceSatisfies
  simp only [newCoordinate, bmod_coeffs, Constraint.exact_sat,
    coeffs_dot_set_left, decide_eq_true_eq]
  replace indexBeyondSource :=
    Nat.le_trans (Coeffs.bmod_length source modulus) indexBeyondSource
  rw [Coeffs.get_of_length_le indexBeyondSource, Int.sub_zero,
    Int.mul_ediv_cancel'
      (Coeffs.dvd_bmod_dot_sub_dot_bmod _ _ _), sourceSatisfies,
    ← Int.add_sub_assoc, Int.add_comm, Int.add_sub_assoc,
    Int.sub_self, Int.add_zero]

/-- Division of a displayed constraint is sound when the old finite
coefficient vector is explicitly certified to be the divisor times the new
one.  This certificate replaces the generic `Nat.gcd` proof API. -/
theorem div_sat_of_scaled (constraint : Constraint)
    (source target values : Coeffs) (divisor : Nat)
    (divisorNonzero : divisor ≠ 0)
    (scaled : source = (divisor : Int) * target)
    (sourceSatisfies : constraint.sat' source values) :
    (constraint.div divisor).sat' target values := by
  have divisorCastNonzero : (divisor : Int) ≠ 0 := by
    intro castZero
    exact divisorNonzero (Int.ofNat.inj castZero)
  have dotScale : IntList.dot source values =
      (divisor : Int) * IntList.dot target values := by
    rw [scaled, IntList.dot_smul_left]
  have dividesDot : (divisor : Int) ∣ IntList.dot source values :=
    ⟨IntList.dot target values, dotScale⟩
  have divided := Constraint.div_sat constraint
    (IntList.dot source values) divisor divisorNonzero dividesDot
    sourceSatisfies
  have quotient : IntList.dot source values / (divisor : Int) =
      IntList.dot target values := by
    rw [dotScale, Int.mul_ediv_cancel_left _ divisorCastNonzero]
  rw [quotient] at divided
  exact divided

/-- Negating both the constraint and its displayed coefficient vector
preserves satisfaction. -/
theorem neg_sat_coeffs (constraint : Constraint) (source values : Coeffs)
    (sourceSatisfies : constraint.sat' source values) :
    constraint.neg.sat' (-source) values := by
  change constraint.neg.sat (IntList.dot (-source) values) = true
  rw [IntList.dot_neg_left]
  exact Constraint.neg_sat sourceSatisfies

/-- The negative-leading branch followed by certified division. -/
theorem neg_div_sat_of_scaled (constraint : Constraint)
    (source target values : Coeffs) (divisor : Nat)
    (divisorNonzero : divisor ≠ 0)
    (scaled : -source = (divisor : Int) * target)
    (sourceSatisfies : constraint.sat' source values) :
    ((constraint.neg).div divisor).sat' target values :=
  div_sat_of_scaled constraint.neg (-source) target values divisor
    divisorNonzero scaled
    (neg_sat_coeffs constraint source values sourceSatisfies)

/-- A zero coefficient vector has zero dot product with every valuation,
proved by recursion on the displayed finite vectors. -/
theorem intList_dot_eq_zero_of_isZero : ∀ source values : Coeffs,
    source.isZero → IntList.dot source values = 0
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | head :: tail, value :: values, allZero => by
      have headZero : head = 0 := by
        apply allZero head
        exact List.mem_cons_self
      have tailZero : Coeffs.isZero tail := by
        intro entry member
        apply allZero entry
        exact List.mem_cons_of_mem head member
      rw [headZero]
      change 0 * value + IntList.dot tail values = 0
      rw [Int.zero_mul, Int.zero_add,
        intList_dot_eq_zero_of_isZero tail values tailZero]

/-- Soundness of Omega's all-zero normalization branch.  The finite source
certificate makes the reduction to the trivial constraint explicit. -/
theorem tidy_sat_of_zero (constraint : Constraint) (source values : Coeffs)
    (sourceZero : source.isZero) (leadingZero : source.leading = 0)
    (gcdZero : source.gcd = 0)
    (sourceSatisfies : constraint.sat' source values) :
    (tidyConstraint constraint source).sat'
      (tidyCoeffs constraint source) values := by
  have dotZero : IntList.dot source values = 0 :=
    intList_dot_eq_zero_of_isZero source values sourceZero
  have satisfiesZero : constraint.sat 0 := by
    change constraint.sat (IntList.dot source values) at sourceSatisfies
    rw [dotZero] at sourceSatisfies
    exact sourceSatisfies
  have positivizeNone : positivize? (constraint, source) = none := by
    unfold positivize?
    change (if 0 ≤ source.leading then none
      else some (constraint.neg, source.smul (-1))) = none
    rw [leadingZero]
    rfl
  have normalizeSome :
      normalize? (constraint, source) = some (Constraint.trivial, source) := by
    unfold normalize?
    change (if source.gcd = 0 then
        if constraint.sat 0 then some (Constraint.trivial, source)
        else some (Constraint.impossible, source)
      else if source.gcd = 1 then none
      else some (constraint.div source.gcd, source.sdiv source.gcd)) =
        some (Constraint.trivial, source)
    rw [gcdZero]
    simp only [satisfiesZero, ↓reduceIte]
  have tidyResult : tidy (constraint, source) = (Constraint.trivial, source) := by
    unfold tidy tidy?
    dsimp only
    rw [positivizeNone, normalizeSome]
    rfl
  change ((tidy (constraint, source)).1).sat'
    ((tidy (constraint, source)).2) values
  rw [tidyResult]
  rfl

open Nat.Linear in
/-- Reflection for the primitive natural-number Boolean equality test, by
structural recursion and without a `LawfulBEq` instance. -/
theorem nat_eq_of_beq : ∀ left right : Nat,
    (left == right) = true → left = right
  | _, _, equality => of_decide_eq_true equality

open Nat.Linear in
/-- Evaluation of the structurally recursive natural-linear polynomial
conversion.  Equality tests are reflected directly, avoiding the generic
`LawfulBEq` proof carried by the upstream checker lemma. -/
theorem natExpr_denote_toPoly_go (context : Context) (expression : Expr) :
    (Expr.toPoly.go coefficient expression polynomial).denote context =
      coefficient * expression.denote context + polynomial.denote context := by
  induction expression generalizing coefficient polynomial with
  | num constant =>
      cases equality : (constant == 0) with
      | false =>
          rw [Expr.toPoly.go, equality]
          change
            coefficient * constant * Var.denote context fixedVar +
                polynomial.denote context =
              coefficient * constant + polynomial.denote context
          have fixedDenotation : Var.denote context fixedVar = 1 := by
            change Bool.rec (context.get fixedVar) 1
                (Nat.beq fixedVar fixedVar) = 1
            rw [Nat.beq_refl]
          rw [fixedDenotation, Nat.mul_one]
      | true =>
          have constantEquality := nat_eq_of_beq constant 0 equality
          subst constant
          rw [Expr.toPoly.go]
          change polynomial.denote context =
            coefficient * 0 + polynomial.denote context
          rw [Nat.mul_zero, Nat.zero_add]
  | var index => rfl
  | add left right leftHypothesis rightHypothesis =>
      change
        (Expr.toPoly.go coefficient left
            (Expr.toPoly.go coefficient right polynomial)).denote context =
          coefficient * (left.denote context + right.denote context) +
            polynomial.denote context
      calc
        (Expr.toPoly.go coefficient left
              (Expr.toPoly.go coefficient right polynomial)).denote context =
            coefficient * left.denote context +
              (Expr.toPoly.go coefficient right polynomial).denote context :=
          leftHypothesis
        _ = coefficient * left.denote context +
              (coefficient * right.denote context +
                polynomial.denote context) := by
          rw [rightHypothesis]
        _ = coefficient * (left.denote context + right.denote context) +
              polynomial.denote context := by
          rw [Nat.mul_add, Nat.add_assoc]
  | mulL constant expression inductionHypothesis =>
      cases equality : (constant == 0) with
      | false =>
          rw [Expr.toPoly.go, equality]
          change
            (Expr.toPoly.go (coefficient * constant) expression polynomial).denote
                context =
              coefficient * (constant * expression.denote context) +
                polynomial.denote context
          rw [inductionHypothesis, Nat.mul_assoc]
      | true =>
          have constantEquality := nat_eq_of_beq constant 0 equality
          subst constant
          rw [Expr.toPoly.go]
          change polynomial.denote context =
            coefficient * (0 * expression.denote context) +
              polynomial.denote context
          rw [Nat.zero_mul, Nat.mul_zero, Nat.zero_add]
  | mulR expression constant inductionHypothesis =>
      cases equality : (constant == 0) with
      | false =>
          rw [Expr.toPoly.go, equality]
          change
            (Expr.toPoly.go (coefficient * constant) expression polynomial).denote
                context =
              coefficient * (expression.denote context * constant) +
                polynomial.denote context
          rw [inductionHypothesis, Nat.mul_assoc,
            Nat.mul_comm constant (expression.denote context)]
      | true =>
          have constantEquality := nat_eq_of_beq constant 0 equality
          subst constant
          rw [Expr.toPoly.go]
          change polynomial.denote context =
            coefficient * (expression.denote context * 0) +
              polynomial.denote context
          rw [Nat.mul_zero, Nat.mul_zero, Nat.zero_add]

open Nat.Linear in
theorem natExpr_denote_toPoly (context : Context) (expression : Expr) :
    expression.toPoly.denote context = expression.denote context := by
  change (Expr.toPoly.go 1 expression []).denote context =
    expression.denote context
  rw [natExpr_denote_toPoly_go]
  change 1 * expression.denote context + 0 = expression.denote context
  rw [Nat.one_mul, Nat.add_zero]

attribute [local simp] natExpr_denote_toPoly

open Nat.Linear in
/-- Normalized natural-linear constraints preserve their denotation, using
the direct polynomial-conversion proof above. -/
theorem natExprCnstr_denote_toNormPoly (context : Context)
    (constraint : ExprCnstr) :
    constraint.toNormPoly.denote context = constraint.denote context := by
  cases constraint
  rename_i equality left right
  simp [ExprCnstr.denote, PolyCnstr.denote, ExprCnstr.toNormPoly]
  by_cases equalityTrue : equality = true <;> simp [equalityTrue]
  · rw [Poly.denote_eq_cancel_eq]
    simp [Poly.denote_eq, Expr.toNormPoly, Poly.denote_sort]
  · rw [Poly.denote_le_cancel_eq]
    simp [Poly.denote_le, Expr.toNormPoly, Poly.denote_sort]

open Nat.Linear in
/-- A syntactically valid natural-linear constraint denotes truth. -/
theorem natExprCnstr_eq_true_of_isValid (context : Context)
    (constraint : ExprCnstr) (valid : constraint.toNormPoly.isValid) :
    constraint.denote context = True := by
  calc
    constraint.denote context = constraint.toNormPoly.denote context :=
      (natExprCnstr_denote_toNormPoly context constraint).symm
    _ = True := PolyCnstr.eq_true_of_isValid context valid

open Lean Elab Tactic Meta

/-- Decode the literal integer lists emitted by Omega's `ToExpr Coeffs`
instance. -/
private meta def coefficientsOfExprAux : Nat → Lean.Expr → MetaM Coeffs
  | 0, expression =>
      throwError "Omega emitted an excessively deep coefficient vector: {expression}"
  | fuel + 1, expression => do
      match expression.getAppFnArgs with
      | (``List.nil, _) => return []
      | (``List.cons, #[_, head, tail]) =>
          let some value ← getIntValue? head |
            throwError "Omega emitted a non-literal coefficient: {head}"
          return value :: (← coefficientsOfExprAux fuel tail)
      | _ =>
          throwError "Omega emitted an unrecognized coefficient vector: {expression}"

private meta def coefficientsOfExpr (expression : Lean.Expr) :
    MetaM Coeffs :=
  coefficientsOfExprAux (expression.approxDepth.toNat + 1) expression

/-- Replace one concrete `tidy_sat` application by the divisor and scaling
certificate that the tactic has just calculated. -/
private meta def replaceTidyProof (constraint coefficients values proof :
    Lean.Expr) : MetaM Lean.Expr := do
  let source ← coefficientsOfExpr coefficients
  let nonnegativeLeading := decide (0 ≤ source.leading)
  let prepared := if nonnegativeLeading then source else -source
  let divisor := prepared.gcd
  if divisor = 0 then
    let sourceZeroType ← mkAppM ``Coeffs.isZero #[coefficients]
    let sourceZeroProof ← mkDecideProof sourceZeroType
    let leadingExpression ← mkAppM ``Coeffs.leading #[coefficients]
    let leadingZeroType ← mkAppM ``Eq
      #[leadingExpression, toExpr (0 : Int)]
    let leadingZeroProof ← mkDecideProof leadingZeroType
    let gcdExpression ← mkAppM ``Coeffs.gcd #[coefficients]
    let gcdZeroType ← mkAppM ``Eq #[gcdExpression, toExpr (0 : Nat)]
    let gcdZeroProof ← mkDecideProof gcdZeroType
    return mkAppN (.const ``QuotientFreeOmega.tidy_sat_of_zero [])
      #[constraint, coefficients, values, sourceZeroProof,
        leadingZeroProof, gcdZeroProof, proof]
  let target := prepared.sdiv divisor
  let targetExpression := toExpr target
  let divisorExpression := toExpr divisor
  let divisorIntExpression := toExpr (divisor : Int)
  let scaledExpression ←
    mkAppM ``HMul.hMul #[divisorIntExpression, targetExpression]
  let sourceExpression ← if nonnegativeLeading then
      pure coefficients
    else
      mkAppM ``Neg.neg #[coefficients]
  let scalingProof ←
    Lean.Elab.Tactic.Omega.mkEqReflWithExpectedType
      sourceExpression scaledExpression
  let nonzeroType ← mkAppM ``Ne #[divisorExpression, toExpr (0 : Nat)]
  let nonzeroProof ← mkDecideProof nonzeroType
  let checker := if nonnegativeLeading then
      ``QuotientFreeOmega.div_sat_of_scaled
    else
      ``QuotientFreeOmega.neg_div_sat_of_scaled
  return mkAppN (.const checker [])
    #[constraint, coefficients, targetExpression, values, divisorExpression,
      nonzeroProof, scalingProof, proof]

/-- Replace a single already-traversed proof node by its constructive finite
checker counterpart. -/
private meta def replaceProofRoot (proof : Lean.Expr) : MetaM Lean.Expr := do
  let function := proof.getAppFn
  if function.isConstOf ``Lean.Omega.tidy_sat then
    let arguments := proof.getAppArgs
    if h : arguments.size = 4 then
      return ← replaceTidyProof arguments[0] arguments[1] arguments[2]
        arguments[3]
  match proof with
  | .const ``Lean.Omega.LinearCombo.coordinate_eval levels =>
      return .const ``QuotientFreeOmega.coordinate_eval levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_0 levels =>
      return .const ``QuotientFreeOmega.coordinate_eval_0 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_1 levels =>
      return .const ``QuotientFreeOmega.coordinate_eval_1 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_2 levels =>
      return .const ``QuotientFreeOmega.coordinate_eval_2 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_3 levels =>
      return .const ``QuotientFreeOmega.coordinate_eval_3 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_4 levels =>
      return .const ``QuotientFreeOmega.coordinate_eval_4 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_5 levels =>
      return .const ``QuotientFreeOmega.coordinate_eval_5 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_6 levels =>
      return .const ``QuotientFreeOmega.coordinate_eval_6 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_7 levels =>
      return .const ``QuotientFreeOmega.coordinate_eval_7 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_8 levels =>
      return .const ``QuotientFreeOmega.coordinate_eval_8 levels
  | .const ``Lean.Omega.LinearCombo.coordinate_eval_9 levels =>
      return .const ``QuotientFreeOmega.coordinate_eval_9 levels
  | .const ``Lean.Omega.LinearCombo.add_eval levels =>
      return .const ``QuotientFreeOmega.add_eval levels
  | .const ``Lean.Omega.LinearCombo.sub_eval levels =>
      return .const ``QuotientFreeOmega.sub_eval levels
  | .const ``Lean.Omega.LinearCombo.mul_eval levels =>
      return .const ``QuotientFreeOmega.mul_eval levels
  | .const ``Lean.Omega.combo_sat' levels =>
      return .const ``QuotientFreeOmega.combo_sat' levels
  | .const ``Lean.Omega.bmod_sat levels =>
      return .const ``QuotientFreeOmega.bmod_sat levels
  | .const ``Nat.Linear.ExprCnstr.eq_true_of_isValid levels =>
      return .const ``QuotientFreeOmega.natExprCnstr_eq_true_of_isValid levels
  | _ => return proof

/-- Substitute the constructive finite checker lemmas before the generated
Omega proof is sealed in an auxiliary theorem.  Traversal is structural; the
separate root pass recognizes a complete `tidy_sat` application only after
its proof argument has itself been rewritten. -/
private meta def replaceProofRoots : Lean.Expr → MetaM Lean.Expr
  | .app function argument => do
      replaceProofRoot <| .app (← replaceProofRoots function)
        (← replaceProofRoots argument)
  | .lam name type body binderInfo => do
      replaceProofRoot <| .lam name (← replaceProofRoots type)
        (← replaceProofRoots body) binderInfo
  | .forallE name type body binderInfo => do
      replaceProofRoot <| .forallE name (← replaceProofRoots type)
        (← replaceProofRoots body) binderInfo
  | .letE name type value body nondependent => do
      replaceProofRoot <| .letE name (← replaceProofRoots type)
        (← replaceProofRoots value) (← replaceProofRoots body)
        nondependent
  | .mdata data body => do
      replaceProofRoot <| .mdata data (← replaceProofRoots body)
  | .proj structureName index body => do
      replaceProofRoot <| .proj structureName index
        (← replaceProofRoots body)
  | proof => replaceProofRoot proof

/-- Run Omega, rewrite its finite certificate proof, and only then package the
usually large proof in an auxiliary declaration. -/
private meta def omegaTactic
    (configuration : Lean.Meta.Omega.OmegaConfig) : TacticM Unit := do
  recordExtraModUse (isMeta := false) `Init.Omega
  liftMetaFinishingTactic fun goal => do
    if debug.terminalTacticsAsSorry.get (← getOptions) then
      goal.admit
    else
      let some goal ← goal.falseOrByContra | return ()
      goal.withContext do
        let target ← goal.getType
        let proofGoal ← mkFreshExprSyntheticOpaqueMVar target
        let hypotheses := (← getLocalHyps).toList
        Lean.Elab.Tactic.Omega.omega hypotheses proofGoal.mvarId! configuration
        let proof ← instantiateMVarsProfiling proofGoal
        let proof ← replaceProofRoots proof
        let auxiliary ← mkAuxTheorem target proof (zetaDelta := true)
        goal.assign auxiliary

/-! Importing this module upgrades existing `omega` source.  This later rule
takes precedence over Lean's frontend while retaining its syntax. -/
elab_rules : tactic
  | `(tactic| omega%$token $configuration:optConfig) => do
      Meta.withReducibleAndInstances (evalAssumption token) <|> do
      let configuration ←
        Lean.Elab.Tactic.Omega.elabOmegaConfig configuration
      omegaTactic configuration

/-- Explicit quotient-free spelling for use in modules where another import
registers an `omega` frontend after this one. -/
elab "omega0" configuration:optConfig : tactic => do
  let configuration ←
    Lean.Elab.Tactic.Omega.elabOmegaConfig configuration
  omegaTactic configuration

/-- Natural and integer regressions exercise preprocessing, coordinates,
linear combinations, multiplication by constants, and normalization. -/
theorem omega_nat_regression (left right : Nat)
    (separated : left + 2 ≤ right) : left < right := by
  omega

theorem omega_int_regression (left right : Int)
    (first : 2 * left + right ≤ 3)
    (second : 4 ≤ 2 * left + right) : False := by
  omega

end QuotientFreeOmega
