module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
public import Purelib.Data.CCL.Name.Boxed.Basic
import Purelib.Data.List.Append
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Finite boxed CCL names

This module formalizes the operational boxed-name interface independently of
arithmetic.  A certificate contains one ordinary finite raw word, one
rational box, and one displayed nonzero rational witness.  A progressive
name returns only further finite certificates.  It never forms a completed
bitstream, a completed complex value, or an intersection of all boxes.
-/

namespace Purelib.Data.CCL.Name.Boxed.Refinement

open Purelib.Data.CCL.Name in
/-- Require the inner boxed name to extend the outer word while its exact box refines the outer box.

Both certificates keep their original words, boxes and witnesses. The word-prefix and box-containment directions refer
to those same two retained owners. -/
structure Refines (inner outer : Boxed.Basic.Certificate) : Prop where
  /-- The outer certificate's exact word prefixes the inner certificate's word. -/ word : outer.word.IsPrefix inner.word
  /-- The inner certificate's exact box refines the outer certificate's box. -/ box : inner.box.Refines outer.box

namespace Refines

open Purelib.Data.CCL.Name in
open Purelib.Geometry.Rational in
open Purelib.Data.List in
/-- Every boxed-name certificate refines itself through its exact word and box. -/
theorem refl (certificate : Boxed.Basic.Certificate) :
  Refines certificate certificate :=
  ⟨⟨[], Append.append_nil certificate.word⟩, Box.refines_refl _⟩

open Purelib.Data.CCL.Name in
open Purelib.Data.List in
/-- Compose boxed-name refinements through the same retained middle certificate. -/
theorem trans {inner middle outer : Boxed.Basic.Certificate}
    (innerMiddle : Refines inner middle)
    (middleOuter : Refines middle outer) : Refines inner outer :=
by
  obtain ⟨outerSuffix, outerMiddle⟩ := middleOuter.word
  obtain ⟨middleSuffix, middleInner⟩ := innerMiddle.word
  refine ⟨⟨outerSuffix ++ middleSuffix, ?_⟩,
    innerMiddle.box.trans middleOuter.box⟩
  exact (Append.append_assoc outer.word outerSuffix middleSuffix).symm.trans
    ((congrArg (fun word => word ++ middleSuffix) outerMiddle).trans middleInner)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.CCL.Name in
open Purelib.Data.Gaussian in
/-- Every possible value of the inner boxed name remains possible for its retained outer prefix. -/
theorem possible_persists {inner outer : Boxed.Basic.Certificate}
    (refines : Refines inner outer) {value : Basic.Canonical}
    (possible : inner.Possible value) : outer.Possible value :=
  ⟨possible.1,
    Parser.Semantics.Prefix.represented_of_prefix
      refines.word possible.2⟩

open Purelib.Data.CCL.Name in
open Purelib.Data.Gaussian in
/-- The squared distance between retained inner and outer witnesses is bounded by the outer box's squared diagonal. -/
theorem witness_distance_le {inner outer :
  Boxed.Basic.Certificate}
    (refines : Refines inner outer) :
    Data.Gaussian.Norm.Basic.normSq (inner.witness - outer.witness) ≤ outer.box.diagonalSq := by
  apply outer.box.normSq_sub_le_diagonalSq
  · exact refines.box.contains inner.witness_inside
  · exact outer.witness_inside

end Refines

open Purelib.Data.CCL.Name in
/-- Require each successive retained boxed-name certificate to refine its immediate predecessor. -/
def IsTrace : List Boxed.Basic.Certificate → Prop
  | [] => True
  | [_] => True
  | older :: newer :: remaining =>
      Refines newer older ∧ IsTrace (newer :: remaining)

end Purelib.Data.CCL.Name.Boxed.Refinement

end
