module

public import Purelib.Geometry.Rational.Box.Separation.Certificate
public import Purelib.Data.List.DependentProduct
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.OfFn.Pairwise
public import Purelib.Data.Rat.List.Minimum
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# A common quantitative gap for an original separated box family

The finite certificate bank stores the original coordinate-gap construction
once at each ordered pair of distinct occurrences. A positive minimum of
those same squared gaps then bounds every pair of displayed points retained
inside the corresponding original boxes.
-/

namespace Purelib.Geometry.Rational.Box.Separation

open Purelib.Data
open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.List
open Rat.Fraction (Rational)
open Rat.Fraction.Order

/-- The materialized original separation certificates at increasing box-list occurrences.

Each retained row relates the original head box to every occurrence of its
original tail. The recursive tail bank retains the remaining ordered pairs.
-/
@[expose] public def Certificates : List Box → Type
  | [] => PUnit
  | head :: remaining =>
      DependentProduct remaining (fun index => SeparationCertificate head (remaining.get index)) ×
        Certificates remaining

namespace Certificates

/-- Construct each original coordinate-gap certificate once in increasing occurrence order. -/
@[expose] public def prepare : (boxes : List Box) → boxes.Pairwise Box.Separated → Certificates boxes
  | [], _ => PUnit.unit
  | _ :: remaining, separated =>
      (DependentProduct.ofFn remaining (fun index => Box.separationCertificate
        ((List.pairwise_cons.mp separated).1 (remaining.get index) (List.get_mem _ _))),
       prepare remaining (List.pairwise_cons.mp separated).2)

/-- Read the common positive minimum from the same stored squared coordinate gaps. -/
@[expose] public def floor : (boxes : List Box) → Certificates boxes → Rational
  | [], _ => 1
  | _ :: remaining, certificates =>
      min (Minimum.positiveMinimum (List.ofFn (fun index : Fin remaining.length =>
        (DependentProduct.get remaining certificates.1 index).gap ^ 2)))
        (floor remaining certificates.2)

/-- Every finite stored certificate bank has a strictly positive common floor. -/
public theorem floor_positive : (boxes : List Box) → (certificates : Certificates boxes) →
    0 < floor boxes certificates
  | [], _ => by
      change (0 : Rational) < 1
      decide
  | _ :: remaining, certificates => by
      apply Fraction.Order.Basic.lt_min
      · apply Minimum.positiveMinimum_pos
        intro value member
        rcases List.OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
        rw [← equal]
        exact Arithmetic.pow_pos_direct (DependentProduct.get remaining certificates.1 index).positive 2
      · exact floor_positive remaining certificates.2

/-- The common stored floor bounds every increasing pair of original contained point occurrences. -/
public theorem floor_lower : (boxes : List Box) → (certificates : Certificates boxes) →
    (points : Fin boxes.length → Canonical) →
    (∀ index, (boxes.get index).Contains (points index)) →
    ∀ first second : Fin boxes.length, first.val < second.val →
      floor boxes certificates ≤ Gaussian.Norm.Basic.normSq (points first - points second)
  | [], _, _, _, first, _, _ => Fin.elim0 first
  | head :: remaining, certificates, points, inside, first, second, ordered => by
      revert ordered
      refine Fin.cases ?_ ?_ first
      · intro ordered
        revert ordered
        refine Fin.cases ?_ ?_ second
        · intro impossible
          exact False.elim (Nat.lt_irrefl _ impossible)
        · intro index _
          have member : (DependentProduct.get remaining certificates.1 index).gap ^ 2 ∈
              List.ofFn (fun other : Fin remaining.length =>
                (DependentProduct.get remaining certificates.1 other).gap ^ 2) :=
            List.OfFn.Basic.mem_ofFn.mpr ⟨index, rfl⟩
          exact (Fraction.Order.Basic.min_le_left _ _).trans
            ((Minimum.positiveMinimum_le_of_mem member).trans
              ((DependentProduct.get remaining certificates.1 index).lower (inside 0) (inside index.succ)))
      · intro firstTail ordered
        revert ordered
        refine Fin.cases ?_ ?_ second
        · intro impossible
          exact False.elim (Nat.not_lt_zero _ impossible)
        · intro secondTail ordered
          exact (Fraction.Order.Basic.min_le_right _ _).trans
            (floor_lower remaining certificates.2 (fun index => points index.succ)
              (fun index => inside index.succ) firstTail secondTail (Nat.lt_of_succ_lt_succ ordered))

end Certificates

set_option genInjectivity false in
/-- A common quantitative gap retained from the same original separated box list.

The original coordinate certificates are materialized once. The displayed
positive bound is the minimum of their actual squared gaps, with one as the
empty-bank initial value.
-/
public structure Family (boxes : List Box) (separated : boxes.Pairwise Box.Separated) where
  /-- The stored original increasing-pair coordinate certificates. -/
  certificates : Certificates boxes
  /-- The bank is the original deterministic coordinate-gap construction. -/
  certificates_eq : certificates = Certificates.prepare boxes separated
  /-- The once-computed uniform squared-distance floor. -/
  bound : Rational
  /-- The floor reads only the same stored certificate bank. -/
  bound_eq : bound = Certificates.floor boxes certificates
  /-- The retained common floor is strictly positive. -/
  positive : 0 < bound

constructive_injectivity Family

namespace Family

/-- Materialize all original coordinate gaps and cache their positive common floor. -/
@[expose] public def prepare (boxes : List Box) (separated : boxes.Pairwise Box.Separated) : Family boxes separated :=
  let certificates := Certificates.prepare boxes separated
  { certificates, certificates_eq := rfl
    bound := Certificates.floor boxes certificates, bound_eq := rfl
    positive := Certificates.floor_positive boxes certificates }

/-- Displayed points in the same original box occurrences share the retained pairwise distance floor. -/
public theorem points_separated {boxes : List Box} {separated : boxes.Pairwise Box.Separated}
    (family : Family boxes separated) (points : Fin boxes.length → Canonical)
    (inside : ∀ index, (boxes.get index).Contains (points index)) :
    (List.ofFn points).Pairwise (fun left right => family.bound ≤ Gaussian.Norm.Basic.normSq (left - right)) := by
  apply List.OfFn.Pairwise.pairwise_ofFn_direct
  intro first second ordered
  rw [family.bound_eq]
  exact Certificates.floor_lower boxes family.certificates points inside first second ordered

end Family
end Purelib.Geometry.Rational.Box.Separation
