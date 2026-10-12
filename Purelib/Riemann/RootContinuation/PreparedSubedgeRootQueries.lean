module
import Purelib.Algebra.Group.Negation
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints

public import Purelib.Riemann.Integration.PreparedEndpointSafeRefinement
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Tactic.Ring

public section

/-!
# Root agreement throughout actual refined subedges

The retained start locations and connected child spine also locate each
finish.  Affine interpolation then locates every rational query, including
on stationary or reversed coordinate edges.  Finite root comparisons prove agreement at all those queries independently
of the integration subdivision depth.
-/

namespace Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries

open Purelib.Algebra.Group
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib.Data.Rat in
/-- The exact rational carrier for retained subedge parameters. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier for original subedge points. -/
private abbrev Gaussian := Basic.Canonical
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints (ParentBudget)
open Purelib.Riemann.Integration.PreparedEndpointSafeRefinement (EndpointSafeBlock)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge RootChildAt RootChildBlock)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- An exact retained parent-edge parameter representing the specified original point.

The record keeps the unit-interval witness and original point equality, so later query comparisons use the same
geometric point and parent owner. -/
structure Location (parent : CenteredEdge curve differential) (point : Basic.Canonical) where
  /-- The retained original parent parameter representing this exact point. -/ fraction : Fraction.Rational
  /-- The retained parameter lies in the closed unit interval. -/ inside : 0 ≤ fraction ∧ fraction ≤ 1
  /-- The original parent point at the retained fraction equals the specified point exactly. -/ point_eq :
    parent.edge.point fraction = point

constructive_injectivity Location

namespace Location

open Purelib.Data.Rat in
/-- Affine interpolation between two unit-interval parameters remains in that interval.

The complementary and original interpolation weights are nonnegative and sum
to one; their retained endpoint bounds give both scalar comparisons directly. -/
theorem interpolate_inside {left right fraction : Fraction.Rational}
    (leftInside : 0 ≤ left ∧ left ≤ 1) (rightInside : 0 ≤ right ∧ right ≤ 1)
    (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    0 ≤ (1 - fraction) * left + fraction * right ∧ (1 - fraction) * left + fraction * right ≤ 1 := by
  have complementary := Fraction.Order.Arithmetic.sub_nonneg_direct inside.2
  refine ⟨?_, ?_⟩
  · have added := Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct complementary leftInside.1)
      (Fraction.Order.Arithmetic.mul_nonneg_direct inside.1 rightInside.1)
    exact (Fraction.zero_add 0).symm.trans_le added
  calc
    _ ≤ (1 - fraction) * 1 + fraction * 1 := Fraction.Order.Arithmetic.add_le_add_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct leftInside.2 complementary)
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rightInside.2 inside.1)
    _ = 1 := by ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
/-- The original prepared-edge point map preserves exact affine interpolation.

Each Gaussian coordinate follows the retained segment formula, and scalar ring
identities identify the interpolated parameter without changing either endpoint. -/
private theorem point_interpolate (edge : PreparedEdge curve differential) (left right fraction : Fraction.Rational) :
    edge.point ((1 - fraction) * left + fraction * right) =
      edge.point left + Scale.scale fraction (edge.point right - edge.point left) := by
  apply Basic.ext <;>
    simp only [PreparedConstantModels.PreparedEdge.point, Geometry.ClearPath.ClearSegment.pointAt,
      Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Scale.scale_re, Scale.scale_im] <;> ring1

open Purelib.Data.Rat in
/-- Locate a retained child point in its original parent edge by interpolating the two retained endpoint locations.

The child and parent affine identities establish the exact point equation while preserving the original endpoint
fractions and unit-interval witnesses. -/
@[expose] def interpolate {parent child : CenteredEdge curve differential}
    (first : Location parent (child.edge.point 0)) (last : Location parent (child.edge.point 1))
    (fraction : Fraction.Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    Location parent (child.edge.point fraction) where
  fraction := (1 - fraction) * first.fraction + fraction * last.fraction
  inside := interpolate_inside first.inside last.inside inside
  point_eq := by
    rw [point_interpolate, first.point_eq, last.point_eq]
    have childAffine := point_interpolate child.edge 0 1 fraction
    rw [show (1 - fraction) * 0 + fraction * 1 = fraction by ring1] at childAffine
    exact childAffine.symm

end Location

set_option genInjectivity false in
open Purelib.Approximation.Gaussian in
/-- Pointwise retained parent locations and root-name equivalences for an original child edge.

Every child parameter retains its exact parent point equality and separate operational comparison between the original
parent and child root queries. -/
structure RootSubedge (parent child : CenteredEdge curve differential) : Type 2 where
  /-- The retained exact parent location of every original child point. -/ location : ∀ fraction, (inside : 0 ≤ fraction
    ∧ fraction ≤ 1) → Location parent (child.edge.point fraction)
  /-- The original parent and child root names at these exact retained locations are operationally equivalent. -/
    equivalent : ∀ fraction inside,
    Equivalence.NamedEquivalent (parent.edge.rootName (location fraction inside).fraction (location fraction
      inside).inside)
      (child.edge.rootName fraction inside)

constructive_injectivity RootSubedge

namespace RootSubedge

open Purelib.Approximation.Gaussian in
/-- Retain each original edge as its own subedge with the same parameters and reflexive root-name comparisons. -/
@[expose] def refl (parent : CenteredEdge curve differential) : RootSubedge parent parent where
  location := fun fraction inside => ⟨fraction, inside, rfl⟩
  equivalent := fun _ _ => Equivalence.NamedEquivalent.refl _

/-- Compose two retained subedge relations through their original middle edge.

Locations compose through the exact middle parameter and point equation; operational root-name comparisons compose
without replacing the original parent or child owners. -/
@[expose] def trans {parent middle child : CenteredEdge curve differential}
    (first : RootSubedge parent middle) (second : RootSubedge middle child) : RootSubedge parent child where
  location := fun fraction inside =>
    let inner := second.location fraction inside
    let outer := first.location inner.fraction inner.inside
    ⟨outer.fraction, outer.inside, outer.point_eq.trans inner.point_eq⟩
  equivalent := fun fraction inside =>
    (first.equivalent (second.location fraction inside).fraction (second.location fraction inside).inside).trans
      (second.equivalent fraction inside)

/-- Read the retained child-start location and root equivalence from an original subedge relation. -/
@[expose] def start {parent child : CenteredEdge curve differential} (relation : RootSubedge parent child) : RootChildAt
  parent child where
  fraction := (relation.location 0 child.edge.baseInside).fraction
  inside := (relation.location 0 child.edge.baseInside).inside
  point_eq := (relation.location 0 child.edge.baseInside).point_eq
  rootEquivalent := relation.equivalent 0 child.edge.baseInside

/-- Transport a retained middle-edge child-start relation through an original parent-to-middle subedge relation. -/
@[expose] def childAt {parent middle child : CenteredEdge curve differential}
    (first : RootSubedge parent middle) (second : RootChildAt middle child) : RootChildAt parent child where
  fraction := (first.location second.fraction second.inside).fraction
  inside := (first.location second.fraction second.inside).inside
  point_eq := (first.location second.fraction second.inside).point_eq.trans second.point_eq
  rootEquivalent := (first.equivalent second.fraction second.inside).trans second.rootEquivalent

open Purelib.Riemann.RootContinuation in
/-- Construct a pointwise root subedge relation from the retained start sheet comparison and exact finish location.

The original parent budget and endpoint interpolation supply each parent location; the retained finite continuation
comparison relates the original root queries. -/
@[expose] def ofEndpoints {parent child : CenteredEdge curve differential}
    (budget : ParentBudget parent.edge) (first : RootChildAt parent child)
    (last : Location parent (child.edge.point 1)) :
    RootSubedge parent child where
  location := Location.interpolate ⟨first.fraction, first.inside, first.point_eq⟩ last
  equivalent := fun fraction inside =>
    let point := Location.interpolate ⟨first.fraction, first.inside, first.point_eq⟩ last fraction inside
    PreparedRefinementRootEndpoints.queryEquivalent budget first fraction inside point.fraction point.inside
      point.point_eq

end RootSubedge

set_option genInjectivity false in
/-- An ordered list of retained pointwise root subedge relations to one original parent edge.

The indexed child list records the exact original order; each cons retains its
head comparison and the same-parent tail without reconstructing either edge. -/
inductive RootSubedgeBlock (parent : CenteredEdge curve differential) : List (CenteredEdge curve differential) → Type 2
  /-- The empty ordered refinement carries no child relations. -/ | nil : RootSubedgeBlock parent []
  /-- Prepend the retained pointwise relation for the original child to the same-parent subedge block. -/ | cons {child
    : CenteredEdge curve differential} {children : List (CenteredEdge curve differential)}
      (head : RootSubedge parent child) (tail : RootSubedgeBlock parent children) : RootSubedgeBlock parent (child ::
        children)

constructive_injectivity RootSubedgeBlock

namespace RootSubedgeBlock

/-- Read the original child-start root comparisons from the retained ordered subedge block. -/
@[expose] def roots {parent : CenteredEdge curve differential} : ∀ {children : List (CenteredEdge curve differential)},
    RootSubedgeBlock parent children → RootChildBlock parent children
  | _, .nil => .nil
  | _, .cons head tail => .cons head.start tail.roots

/-- Append two retained ordered subedge blocks for the same original parent. -/
@[expose] def append {parent : CenteredEdge curve differential} : ∀ {first second : List (CenteredEdge curve
  differential)},
    RootSubedgeBlock parent first → RootSubedgeBlock parent second → RootSubedgeBlock parent (first ++ second)
  | _, _, .nil, second => second
  | _, _, .cons head tail, second => .cons head (tail.append second)

/-- Transport every retained subedge relation through the same original parent-to-middle relation, preserving child
order. -/
@[expose] def through {parent middle : CenteredEdge curve differential} (relation : RootSubedge parent middle) :
    ∀ {children : List (CenteredEdge curve differential)}, RootSubedgeBlock middle children → RootSubedgeBlock parent
      children
  | _, .nil => .nil
  | _, .cons head tail => .cons (relation.trans head) (tail.through relation)

open Purelib.Geometry.Path.Gaussian
/-- Recover the path-chain start location from its retained child-start relations.

An empty chain uses the supplied final location; a nonempty chain reads the
first child witness and its original exact starting-point equation. -/
@[expose] def startLocation {parent : CenteredEdge curve differential} :
    ∀ {children : List (CenteredEdge curve differential)} {first last : Lifted.Basic.LiftedPoint 2},
      DirectPathChain children (start := first) (finish := last) → RootChildBlock parent children →
        Location parent last.coordinate → Location parent first.coordinate
  | _, _, _, .nil _, .nil, last => last
  | _, _, _, .cons child _, .cons head _, _ =>
      ⟨head.fraction, head.inside, head.point_eq.trans child.edge.point_zero⟩

/-- Build a retained pointwise subedge block from its original geometric chain, child-start comparisons and exact final
location.

Each original child finish is identified with the next retained start, and the parent budget extends its start
comparison to the entire child edge. -/
@[expose] def ofSpines {parent : CenteredEdge curve differential} (budget : ParentBudget parent.edge) :
    ∀ {children : List (CenteredEdge curve differential)} {first last : Lifted.Basic.LiftedPoint 2},
      DirectPathChain children (start := first) (finish := last) → RootChildBlock parent children →
      Location parent last.coordinate → RootSubedgeBlock parent children
  | _, _, _, .nil _, .nil, _ => .nil
  | _, _, _, .cons child chain, .cons head roots, last =>
      let next := startLocation chain roots last
      let relation := RootSubedge.ofEndpoints budget head
        ⟨next.fraction, next.inside, next.point_eq.trans child.edge.point_one.symm⟩
      .cons relation (ofSpines budget chain roots last)

end RootSubedgeBlock

/-- Read pointwise root subedge relations for every child of the retained endpoint-safe block. -/
@[expose] def EndpointSafeBlock.subedges {parent : CenteredEdge curve differential} (safe : EndpointSafeBlock parent) :
    RootSubedgeBlock parent safe.block.children :=
  RootSubedgeBlock.ofSpines safe.budget safe.block.chain safe.block.roots
    ⟨1, by decide, parent.edge.point_one⟩

set_option genInjectivity false in
/-- An ordered original parent list refined into concatenated child blocks with retained geometric chains and pointwise
root subedge relations.

Each block preserves its original parent's lifted endpoints and root comparisons, and the inductive tail retains the
remaining parent and child order. -/
inductive RootSubedgeRefinement : List (CenteredEdge curve differential) → List (CenteredEdge curve differential) → Type
  2
  /-- The empty ordered refinement carries no child relations. -/ | nil : RootSubedgeRefinement [] []
  /-- Retain one original parent with its exact child chain and pointwise subedge block, then concatenate the original
    tail refinement. -/ | cons {parent : CenteredEdge curve differential} {parents block children : List (CenteredEdge
    curve differential)}
      (chain : DirectPathChain block
        (start := ⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩)
        (finish := ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩))
      (head : RootSubedgeBlock parent block) (tail : RootSubedgeRefinement parents children) :
      RootSubedgeRefinement (parent :: parents) (block ++ children)

constructive_injectivity RootSubedgeRefinement

/-- Transport a retained root subedge refinement along an exact equality of its child list. -/
@[expose] def RootSubedgeRefinement.castChildren {parents first second : List (CenteredEdge curve differential)}
    (equal : first = second) (refinement : RootSubedgeRefinement parents first) : RootSubedgeRefinement parents second
      :=
  equal ▸ refinement

end Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries

end
