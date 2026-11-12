module

public import Purelib.Geometry.Rational.Box.Subdivision
public import Purelib.Geometry.Rational.Box.Sample
import Purelib.Data.List.Map
import Purelib.Data.List.Append

/-!
# Finite trees of separated rational boxes

Each branch retains its actual two separated children and both recursively
constructed subtrees. Leaves retain nonzero rational samples. Leaf identity
belongs to the same tree; its readback never rebuilds a child or a sample.
-/

public section

namespace Purelib.Geometry.Rational.Box

open Purelib.Data.Gaussian
open Purelib.Data.List

set_option genInjectivity false in
/-- A finite full binary tree retains nested separated boxes and a nonzero rational sample at each leaf. -/
inductive Tree : Box → Nat → Type where
  /-- A depth-zero tree retains one exact sample of its original box. -/ | leaf (box : Box)
      (sample : NonzeroSample box) : Tree box 0
  /-- A branch retains both actual separated child owners and their equal-depth trees. -/ | fork {box : Box}
      {depth : Nat} (children : SeparatedChildren box) (left : Tree children.left depth)
      (right : Tree children.right depth) : Tree box (depth + 1)

namespace Tree

/-- Build a finite tree by structural recursion on its requested depth, caching every child and sample once. -/
def build (box : Box) (proper : box.Proper) : (depth : Nat) → Tree box depth
  | 0 => .leaf box (box.nonzeroSample proper)
  | depth + 1 =>
      let children := SeparatedChildren.build box proper
      .fork children (build children.left children.leftProper depth) (build children.right children.rightProper depth)

/-- A leaf address is indexed by its actual retained tree, with a branch selecting the original child owner. -/
@[expose] def Leaf : {box : Box} → {depth : Nat} → Tree box depth → Type
  | _, _, .leaf _ _ => PUnit
  | _, _, .fork _ left right => Sum left.Leaf right.Leaf

/-- Read the original nonzero sample at an address of the same retained tree. -/
@[expose] def point : {box : Box} → {depth : Nat} → (tree : Tree box depth) → tree.Leaf → Basic.Canonical
  | _, _, .leaf _ sample => fun _ => sample.point
  | _, _, .fork _ left right => Sum.elim left.point right.point

/-- Read the actual cached final subbox at a leaf of the same original tree. -/
@[expose] def leafBox : {box : Box} → {depth : Nat} → (tree : Tree box depth) → tree.Leaf → Box
  | _, _, .leaf box _ => fun _ => box
  | _, _, .fork _ left right => Sum.elim left.leafBox right.leafBox

/-- Every cached leaf subbox refines the original box of the same retained tree. -/
theorem leafBox_refines {box : Box} {depth : Nat} (tree : Tree box depth) (address : tree.Leaf) :
    (tree.leafBox address).Refines box := by
  induction tree with
  | leaf box _ => exact refines_refl box
  | fork children left right leftInduction rightInduction =>
      cases address with
      | inl address => exact (leftInduction address).trans children.leftRefines
      | inr address => exact (rightInduction address).trans children.rightRefines

/-- Different leaf subboxes of the same retained tree share no Gaussian-rational point. -/
theorem leafBox_disjoint {box : Box} {depth : Nat} (tree : Tree box depth)
    (first second : tree.Leaf) (different : first ≠ second) (point : Basic.Canonical) :
    (tree.leafBox first).Contains point → ¬ (tree.leafBox second).Contains point := by
  induction tree with
  | leaf _ _ => cases first; cases second; exact (different rfl).elim
  | fork children left right leftInduction rightInduction =>
      cases first with
      | inl first =>
          cases second with
          | inl second =>
              exact leftInduction first second (fun equal => different (congrArg Sum.inl equal))
          | inr second =>
              intro leftInside rightInside
              have separated := children.points_separated
                ((left.leafBox_refines first).contains leftInside)
                ((right.leafBox_refines second).contains rightInside)
              exact lt_irrefl point.re separated
      | inr first =>
          cases second with
          | inl second =>
              intro rightInside leftInside
              have separated := children.points_separated
                ((left.leafBox_refines second).contains leftInside)
                ((right.leafBox_refines first).contains rightInside)
              exact lt_irrefl point.re separated
          | inr second =>
              exact rightInduction first second (fun equal => different (congrArg Sum.inr equal))

/-- Every leaf readback lies in the original box of its retained tree. -/
theorem point_inside {box : Box} {depth : Nat} (tree : Tree box depth) (address : tree.Leaf) :
    box.Contains (tree.point address) := by
  induction tree with
  | leaf _ sample => exact sample.inside
  | fork children left right leftInduction rightInduction =>
      cases address with
      | inl address => exact children.leftRefines.contains (leftInduction address)
      | inr address => exact children.rightRefines.contains (rightInduction address)

/-- Every original leaf sample is nonzero. -/
theorem point_nonzero {box : Box} {depth : Nat} (tree : Tree box depth) (address : tree.Leaf) :
    tree.point address ≠ 0 := by
  induction tree with
  | leaf _ sample => exact sample.nonzero
  | fork _ left right leftInduction rightInduction =>
      cases address with
      | inl address => exact leftInduction address
      | inr address => exact rightInduction address

/-- Equal Gaussian leaf readings identify the same address in the original retained tree. -/
theorem point_injective {box : Box} {depth : Nat} (tree : Tree box depth)
    (first second : tree.Leaf) (equal : tree.point first = tree.point second) : first = second := by
  induction tree with
  | leaf _ _ => cases first; cases second; rfl
  | fork children left right leftInduction rightInduction =>
      cases first with
      | inl first =>
          cases second with
          | inl second => exact congrArg Sum.inl (leftInduction first second equal)
          | inr second =>
              have separated := children.points_separated (left.point_inside first) (right.point_inside second)
              have realEqual := congrArg Basic.Canonical.re equal
              exact (separated.ne realEqual).elim
      | inr first =>
          cases second with
          | inl second =>
              have separated := children.points_separated (left.point_inside second) (right.point_inside first)
              have realEqual := congrArg Basic.Canonical.re equal
              exact (separated.ne realEqual.symm).elim
          | inr second => exact congrArg Sum.inr (rightInduction first second equal)

/-- Read every original leaf address in left-to-right order without repeating construction. -/
@[expose] def leaves : {box : Box} → {depth : Nat} → (tree : Tree box depth) → List tree.Leaf
  | _, _, .leaf _ _ => [PUnit.unit]
  | _, _, .fork _ left right => left.leaves.map Sum.inl ++ right.leaves.map Sum.inr

/-- A depth request retains exactly two to that power many leaf addresses. -/
theorem leaves_length {box : Box} {depth : Nat} (tree : Tree box depth) : tree.leaves.length = 2 ^ depth := by
  induction tree with
  | leaf _ _ => rfl
  | @fork box depth children left right leftInduction rightInduction =>
      change (left.leaves.map Sum.inl ++ right.leaves.map Sum.inr).length = _
      rewrite [Append.length_append, Map.length_map, Map.length_map, leftInduction, rightInduction, Nat.pow_succ]
      exact (Nat.mul_two _).symm

end Tree

/-- A proper rational box cannot uniformly fix one exact Gaussian point. -/
theorem not_uniform_singleton (box : Box) (proper : box.Proper) (point : Basic.Canonical) :
    ¬ (∀ sample, box.Contains sample → sample = point) := by
  intro uniform
  let children := SeparatedChildren.build box proper
  have left := uniform children.left.anchor (children.leftRefines.contains children.left.contains_anchor)
  have right := uniform children.right.anchor (children.rightRefines.contains children.right.contains_anchor)
  have separated := children.points_separated children.left.contains_anchor children.right.contains_anchor
  exact separated.ne (congrArg Basic.Canonical.re (left.trans right.symm))

end Purelib.Geometry.Rational.Box

end
