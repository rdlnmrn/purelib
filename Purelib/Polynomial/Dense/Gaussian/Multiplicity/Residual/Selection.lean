module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part

open Purelib.Polynomial.Dense.Gaussian.Multiplicity (Basis)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

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

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Selection

/-- Bounded finite scan for the first positive-degree factor whose displayed
residual quadrance is strictly below `delta`. -/
def findSmallIndex (point :
  Gaussian.Basic.Canonical) (delta : Fraction.Rational) :
    (entries : List PositiveEntry) → Option (Fin entries.length)
  | [] => none
  | entry :: entries =>
      if Data.Gaussian.Norm.Basic.normSq (entry.part.polynomial.eval point) < delta then some 0
      else
        match findSmallIndex point delta entries with
        | none => none
        | some index => some index.succ

/-- An index returned by the finite scan points to a factor whose residual quadrance is below the threshold. -/
theorem findSmallIndex_sound
    (point : Gaussian.Basic.Canonical) (delta : Fraction.Rational) :
    ∀ (entries : List PositiveEntry) (index : Fin entries.length),
      findSmallIndex point delta entries = some index →
      Data.Gaussian.Norm.Basic.normSq ((entries.get index).part.polynomial.eval point) < delta
  | [], index, _ => Fin.elim0 index
  | entry :: entries, index, found => by
      by_cases headSmall : Data.Gaussian.Norm.Basic.normSq (entry.part.polynomial.eval point) < delta
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
            exact findSmallIndex_sound point delta
              entries tailIndex recursive

/-- If the finite scan finds no small factor, every listed factor's residual quadrance is at least the threshold. -/
theorem all_lower_of_findSmallIndex_eq_none
    (point : Gaussian.Basic.Canonical) (delta : Fraction.Rational) :
    ∀ (entries : List PositiveEntry),
      findSmallIndex point delta entries = none →
      ∀ entry ∈ entries,
        delta ≤ Data.Gaussian.Norm.Basic.normSq (entry.part.polynomial.eval point)
  | [], _, entry, member => (List.not_mem_nil member).elim
  | head :: entries, found, entry, member => by
      by_cases headSmall : Data.Gaussian.Norm.Basic.normSq (head.part.polynomial.eval point) < delta
      · rw [findSmallIndex, if_pos headSmall] at found
        contradiction
      · rw [findSmallIndex, if_neg headSmall] at found
        cases recursive : findSmallIndex point delta entries with
        | some index => rw [recursive] at found; contradiction
        | none =>
            cases member with
            | head => exact Fraction.Order.Arithmetic.le_of_not_gt_direct headSmall
            | tail _ tailMember =>
                exact
                  all_lower_of_findSmallIndex_eq_none
                  point delta entries
                  recursive entry tailMember

set_option genInjectivity false in
/-- Proof-bearing selected squarefree factor. -/
structure SmallFactor
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (decomposition :
      Dense.Gaussian.Squarefree.Decomposition p)
    (point : Gaussian.Basic.Canonical) (delta : Fraction.Rational) where
  /-- The selected bounded index in the exact positive multiplicity list. -/ index : Fin
    decomposition.positiveMultiplicityEntries.length
  /-- The factor at the retained index has residual quadrance strictly below the requested threshold. -/ residualSmall :
    Data.Gaussian.Norm.Basic.normSq ((decomposition.positiveMultiplicityEntries.get index).part.polynomial.eval
      point) < delta

constructive_injectivity SmallFactor

/-- A small original residual constructively selects one small squarefree
factor.  The threshold displays both the exact omitted-unit quadrance and the
finite total multiplicity. -/
def selectSmallFactor
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (decomposition :
      Dense.Gaussian.Squarefree.Decomposition p)
    (point : Gaussian.Basic.Canonical) {delta : Fraction.Rational} (deltaPositive : 0 < delta)
    (small : Data.Gaussian.Norm.Basic.normSq (p.eval point) <
      Dense.Gaussian.Multiplicity.Residual.Basic.unitQuadrance decomposition *
        delta ^ Dense.Gaussian.Multiplicity.Residual.Basic.multiplicityCount
          decomposition.positiveMultiplicityEntries) :
    SmallFactor decomposition point delta := by
  let entries := decomposition.positiveMultiplicityEntries
  match found : findSmallIndex point delta entries with
  | some index =>
      exact
        { index := index
          residualSmall := findSmallIndex_sound point delta entries index
            found }
  | none =>
      have allLower : ∀ entry ∈ entries,
          delta ≤ Data.Gaussian.Norm.Basic.normSq (entry.part.polynomial.eval point) :=
        all_lower_of_findSmallIndex_eq_none point delta entries found
      have productLower : delta ^ Dense.Gaussian.Multiplicity.Residual.Basic.multiplicityCount entries ≤
          Data.Gaussian.Norm.Basic.normSq (Basis.Positive.positiveValue entries point)
            :=
        Dense.Gaussian.Multiplicity.Residual.Basic.power_le_normSq_positiveValue_of_all delta deltaPositive.le
          entries point allLower
      have scaledLower : Dense.Gaussian.Multiplicity.Residual.Basic.unitQuadrance decomposition *
          delta ^ Dense.Gaussian.Multiplicity.Residual.Basic.multiplicityCount entries ≤
          Dense.Gaussian.Multiplicity.Residual.Basic.unitQuadrance decomposition *
            Data.Gaussian.Norm.Basic.normSq (Basis.Positive.positiveValue entries point)
              :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          productLower (Dense.Gaussian.Multiplicity.Residual.Basic.unitQuadrance_pos decomposition).le
      have residualIdentity := Dense.Gaussian.Multiplicity.Residual.Basic.residual_product_identity decomposition point
      have contradiction : Data.Gaussian.Norm.Basic.normSq (p.eval point) < Data.Gaussian.Norm.Basic.normSq
        (p.eval point) := by
        calc
          Data.Gaussian.Norm.Basic.normSq (p.eval point) < Dense.Gaussian.Multiplicity.Residual.Basic.unitQuadrance
            decomposition *
              delta ^ Dense.Gaussian.Multiplicity.Residual.Basic.multiplicityCount entries := by
            simpa only [entries] using small
          _ ≤ Dense.Gaussian.Multiplicity.Residual.Basic.unitQuadrance decomposition *
              Data.Gaussian.Norm.Basic.normSq (Basis.Positive.positiveValue entries
                point) := scaledLower
          _ = Data.Gaussian.Norm.Basic.normSq (p.eval point) := residualIdentity.symm
      exact (lt_irrefl _ contradiction).elim
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Residual.Selection

end
