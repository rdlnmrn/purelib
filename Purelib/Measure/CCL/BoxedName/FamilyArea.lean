module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.CCL.Name.Boxed.Basic
import Purelib.Data.CCL.Name.Boxed.Process
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Content
import Purelib.Measure.Box.Cover
public import Purelib.Measure.CCL.BoxedName.Area
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Tactic.Ring

open Purelib.Data.CCL.Name.Boxed.Basic (Certificate)
open Purelib.Data.CCL.Name.Boxed.Process (ProgressiveName)

section
@[expose] public section

/-!
# Finite measure observations of boxed CCL names

This module turns each boxed CCL certificate into a generic finite
observation and supplies arbitrarily small rational-area observations of a
progressive site.  The possible predicate is deliberately allowed to refine:
no intersection of all cylinders and no completed point is asserted.
-/

namespace Purelib.Measure.CCL.BoxedName

/-! ## Simultaneous observations of a finite family -/

section
open Purelib.Data.CCL.Name
section
open Purelib.Data.Rat
open Purelib.Measure
/-- Request one area certificate per original progressive name using recursive half-target allocation.

Each name starts at its retained initial state; the ordered tail receives the same halved target allocated to the
current name. -/
def familyCertificates : (names : List ProgressiveName) →
    (target : Fraction.Rational) → 0 < target → List Certificate
  | [], _, _ => []
  | name :: remaining, target, positive =>
      let half := target / 2
      let halfPositive := Fraction.Order.Field.div_pos_direct positive
        (by decide : (0 : Fraction.Rational) < 2)
      (CCL.BoxedName.ProgressiveName.areaCertificate name) name.initial half halfPositive ::
        familyCertificates remaining half halfPositive

/-- The requested certificate list retains exactly one entry for each original name occurrence. -/
@[simp] theorem familyCertificates_length (names : List
  ProgressiveName)
    (target : Fraction.Rational) (positive : 0 < target) :
    (familyCertificates names target positive).length = names.length := by
  induction names generalizing target with
  | nil => rfl
  | cons name remaining inductionHypothesis =>
      simp only [familyCertificates, List.length_cons]
      rw [inductionHypothesis]

end

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
/-- Sum the rectangular contents of the boxes in the exact retained certificate list. -/
def familyContent (certificates : List Certificate) : Fraction.Rational
  :=
  (certificates.map fun certificate =>
    Box.Content.boxContent certificate.box).sum

open Purelib.Data.Gaussian in
/-- Form the finite disjunction of the exact retained certificates' possible-point predicates. -/
def familyPossible : List Certificate → Basic.Canonical → Prop
  | [], _ => False
  | certificate :: remaining, point =>
      certificate.Possible point ∨ familyPossible remaining point

section
open Purelib.Measure
/-- Retain the exact ordered certificate boxes as a finite box cover. -/
def familyCover (certificates : List Certificate) :
  Box.Cover.BoxCover :=
  ⟨certificates.map fun certificate => certificate.box⟩

/-- The original certificate-box cover covers the finite union of those same certificates' possible points. -/
theorem familyCover_covers : ∀ certificates : List Certificate,
    (familyCover certificates).Covers (familyPossible certificates)
  | [] => by
      intro point impossible
      exact impossible.elim
  | certificate :: remaining => by
      intro point member
      rcases member with head | tail
      · exact ⟨certificate.box, List.mem_cons_self,
          certificate.possible_inside head⟩
      · rcases familyCover_covers remaining point tail with
          ⟨box, boxMember, inside⟩
        exact ⟨box, List.mem_cons_of_mem certificate.box boxMember, inside⟩

/-- The exact family cover has content equal to the original certificate-box content sum. -/
theorem familyCover_content (certificates : List Certificate) :
    (familyCover certificates).content = familyContent certificates := by
  induction certificates with
  | nil => rfl
  | cons certificate remaining inductionHypothesis =>
      simp only [familyCover, Box.Cover.BoxCover.content,
        familyContent, List.map_cons, List.sum_cons] at inductionHypothesis ⊢
      rw [inductionHypothesis]

end

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Measure in
/-- Recursive half-target requests produce an exact certificate family with total box content below the original
positive target. -/
theorem familyCertificates_content_lt :
    ∀ (names : List ProgressiveName) (target : Fraction.Rational)
      (positive : 0 < target),
      familyContent (familyCertificates names target positive) < target
  | [], target, positive => by
      simpa only [familyCertificates, familyContent, List.map_nil,
        List.sum_nil] using positive
  | name :: remaining, target, positive => by
      let half := target / 2
      have halfPositive : (0 : Fraction.Rational) < half :=
        Fraction.Order.Field.div_pos_direct positive (by decide)
      have headSmall :=
        (CCL.BoxedName.ProgressiveName.areaCertificate_content_lt name) name.initial half halfPositive
      have tailSmall :=
        familyCertificates_content_lt remaining half halfPositive
      dsimp only [familyCertificates, familyContent]
      rw [List.map_cons, List.sum_cons]
      calc
        Box.Content.boxContent
              ((CCL.BoxedName.ProgressiveName.areaCertificate name) name.initial half halfPositive).box +
            familyContent
              (familyCertificates remaining half halfPositive) <
            half + half :=
          Fraction.Order.Arithmetic.add_lt_add_direct headSmall tailSmall
        _ = target := by
          dsimp only [half]
          calc
            target / 2 + target / 2 = (target / 2) * 2 := by ring1
            _ = target :=
              Fraction.Field.div_mul_cancel_of_ne target 2
                (by decide)

open Purelib.Data.Rat
open Purelib.Measure
/-- The requested certificate-box list covers the union of those exact requested certificates' possible points. -/
theorem familyCertificates_cover (names : List ProgressiveName)
    (target : Fraction.Rational) (positive : 0 < target) :
    (familyCover (familyCertificates names target positive)).Covers
      (familyPossible (familyCertificates names target positive)) :=
  familyCover_covers _

/-- The cover retained from the requested certificate family has content below the original positive target. -/
theorem familyCertificates_cover_content_lt
    (names : List ProgressiveName) (target : Fraction.Rational)
    (positive : 0 < target) :
    (familyCover (familyCertificates names target positive)).content <
      target := by
  rw [familyCover_content]
  exact familyCertificates_content_lt names target positive

end

end Purelib.Measure.CCL.BoxedName

end
