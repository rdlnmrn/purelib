module

import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Finite.Odd.Presentation
public import Purelib.Algebra.Field.Finite.Odd.SquareClasses
public import Purelib.Algebra.Field.SquareClass.Basic
public import Purelib.Geometry.Projective.Quaternion.Finite.Enumeration
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field

open Purelib.Algebra.Field.Finite.Odd

open Purelib.Algebra.Field.SquareClass.Basic

section
@[expose] public section

/-!
# Constructive finite-field rotation enumeration

Problem 69 asks for counts over a displayed odd finite field.  This module
provides the executable layer used by those counts.  Projective points are not
obtained from a `Fintype` or a quotient: the four standard first-nonzero
coordinate charts are listed directly, and representatives whose four-square
norm vanishes are removed by a finite test.
-/

namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

variable {K : Type*} [ExplicitField K]

section FiniteOddFieldPresentation

variable (presentation : Presentation.FiniteOddFieldPresentation K)

/-- Represent the trivial square class by the nonzero unit.

The presentation's nonzero-two certificate supplies nonzero one. -/
def trivialSquareClass :
  SquareClassRepresentative K where
  value := 1
  nonzero := Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.one_ne_zero presentation

/-- Represent the nontrivial square class by the retained chosen nonsquare.

The nonsquare certificate guarantees that the representative is nonzero. -/
def nontrivialSquareClass :
  SquareClassRepresentative K where
  value := (SquareClasses.FiniteOddFieldPresentation.chosenNonsquare presentation).value
  nonzero := SquareClasses.FiniteOddFieldPresentation.nonsquare_ne_zero
    (SquareClasses.FiniteOddFieldPresentation.chosenNonsquare presentation).noRoot

set_option genInjectivity false in
/-- Certify which of two displayed representatives matches a nonzero value.

The trivial case retains a square root; the nontrivial case retains the no-root proof and an explicit nonzero
equivalence factor. -/
inductive
  NonzeroSquareClassClassification
    (target : SquareClassRepresentative K) where
  /-- Retain a square root and equivalence with the unit representative. -/ | trivial (root : K) (rootSquare : root ^ 2
    = target.value)
      (equivalent : presentation.trivialSquareClass.Equivalent target)
  /-- Retain a no-root proof and an explicit nonzero factor proving equivalence with the chosen nonsquare. -/ |
    nontrivial (targetNoRoot : ∀ root : K, root ^ 2 ≠ target.value)
      (factor : K) (factorNonzero : factor ≠ 0)
      (equivalent : presentation.nontrivialSquareClass.Equivalent target)

constructive_injectivity NonzeroSquareClassClassification

open Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation in
/-- Classify a nonzero value relative to the unit and chosen nonsquare.

The cached square classification supplies the trivial case; a retained square witness for the product with the chosen
nonsquare constructs the other equivalence factor. -/
def classifyNonzeroSquareClass (target :
  SquareClassRepresentative K) :
    presentation.NonzeroSquareClassClassification target := by
  cases presentation.classifySquare target.value with
  | square root rootSquare =>
      refine NonzeroSquareClassClassification.trivial root rootSquare ?_
      refine ⟨root, ?_, ?_⟩
      · intro rootZero
        apply target.nonzero
        calc
          target.value = root ^ 2 := rootSquare.symm
          _ = 0 := by rw [rootZero]; ring1
      · change target.value = root ^ 2 * (1 : K)
        rw [rootSquare]
        ring1
  | nonsquare targetNoRoot =>
      let chosen := (SquareClasses.FiniteOddFieldPresentation.chosenNonsquare presentation)
      let witness := SquareClasses.FiniteOddFieldPresentation.nonsquareMulNonsquareSquareWitness presentation
        chosen.value target.value chosen.noRoot targetNoRoot
      have chosenNonzero : chosen.value ≠ 0 :=
        SquareClasses.FiniteOddFieldPresentation.nonsquare_ne_zero chosen.noRoot
      have witnessRootNonzero : witness.root ≠ 0 := by
        intro rootZero
        have productZero : chosen.value * target.value = 0 := by
          calc
            chosen.value * target.value = witness.root ^ 2 :=
              witness.equation.symm
            _ = 0 := by rw [rootZero]; ring1
        exact (ExplicitField.mul_ne_zero chosenNonzero target.nonzero)
          productZero
      let factor := witness.root / chosen.value
      have factorNonzero : factor ≠ 0 :=
        ExplicitField.div_ne_zero witnessRootNonzero chosenNonzero
      refine NonzeroSquareClassClassification.nontrivial targetNoRoot factor
        factorNonzero ?_
      refine ⟨factor, factorNonzero, ?_⟩
      change target.value = factor ^ 2 * chosen.value
      have chosenCancel := ExplicitField.mul_inv_cancel chosen.value
        chosenNonzero
      unfold factor
      rw [ExplicitField.div_eq_mul_inv]
      symm
      calc
        (witness.root * chosen.value⁻¹) ^ 2 * chosen.value =
            witness.root ^ 2 * chosen.value⁻¹ ^ 2 * chosen.value := by ring1
        _ =
            (chosen.value * target.value) * chosen.value⁻¹ ^ 2 *
              chosen.value := by rw [witness.equation]
        _ = target.value * (chosen.value * chosen.value⁻¹) ^ 2 := by ring1
        _ = target.value := by rw [chosenCancel]; ring1
end FiniteOddFieldPresentation

/-! ## Fully evaluated small-field regression presentations -/

end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end
