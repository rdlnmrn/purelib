module
import Purelib.Data.List.Membership
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedConstantModels

public import Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements
import Purelib.Tactic.Ring

public section

/-!
# Ordered source segments of retained prepared parents

Endpoint parameters refer to the original clear segment. Directed root
refinement preserves their order, including the stationary case, without
rebuilding any source or descendant owner.
-/

namespace Purelib.Riemann.Paths.PreparedSegmentSources

open Purelib.Data
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.Curves

open Purelib.Data.Rat
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
  (RootSubedge RootSubedgeBlock)
open Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements
  (SameDirection DirectedRefinement)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}

/-- A prepared parent has ordered endpoint parameters on the exact original clear segment.

Both parameters lie in the closed unit interval. Equality is allowed, retaining stationary parents without an extra
strict movement assumption. -/
@[expose] def SegmentSource (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (parent : CenteredEdge curve source) : Prop :=
  ∃ first last : Rat.Fraction.Rational, 0 ≤ first ∧ first ≤ last ∧ last ≤ 1 ∧
    parent.edge.point 0 = segment.pointAt first ∧ parent.edge.point 1 = segment.pointAt last

namespace SegmentSource

/-- Every prepared-edge point is the affine interpolation of its two endpoints. -/
private theorem parent_affine (parent : CenteredEdge curve source) (parameter : Rat.Fraction.Rational) :
    parent.edge.point parameter = parent.edge.point 0 + Gaussian.Scale.scale parameter (parent.edge.point 1 -
      parent.edge.point 0) := by
  apply Gaussian.Basic.ext <;>
    simp only [Integration.PreparedConstantModels.PreparedEdge.point,
      Geometry.ClearPath.ClearSegment.pointAt,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1

/-- Composing source-segment parameters agrees with affine interpolation of the corresponding points. -/
private theorem segment_affine (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish)
    (first last parameter : Rat.Fraction.Rational) :
    segment.pointAt ((1 - parameter) * first + parameter * last) =
      segment.pointAt first + Gaussian.Scale.scale parameter (segment.pointAt last - segment.pointAt first) := by
  apply Gaussian.Basic.ext <;>
    simp only [Geometry.ClearPath.ClearSegment.pointAt, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1

/-- Interpolating two unit-interval parameters with a unit-interval weight stays in that interval. -/
private theorem interpolate_inside {first last parameter : Rat.Fraction.Rational}
    (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    0 ≤ (1 - parameter) * first + parameter * last ∧ (1 - parameter) * first + parameter * last ≤ 1 := by
  have remaining := Rat.Fraction.Order.Arithmetic.sub_nonneg_direct inside.2
  refine ⟨add_nonneg (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct remaining firstInside.1)
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct inside.1 lastInside.1), ?_⟩
  exact (add_le_add (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct firstInside.2 remaining)
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lastInside.2 inside.1)).trans_eq (by ring1)

/-- Transport ordered source parameters through an actual root subedge with the same direction.

For a moving parent, compose the original parameters with the retained endpoint queries. A stationary parent uses one
retained source point for both endpoints. -/
theorem refine {parent child : CenteredEdge curve source} (original : SegmentSource segment parent)
    (relation : RootSubedge parent child) (direction : SameDirection parent child) : SegmentSource segment child := by
  obtain ⟨first, last, firstNonnegative, ordered, lastBound, firstEq, lastEq⟩ := original
  by_cases stationary : parent.edge.point 1 = parent.edge.point 0
  · have constant (parameter : Rat.Fraction.Rational) : parent.edge.point parameter = parent.edge.point 0 := by
      rw [parent_affine, stationary]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im,
          Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
          Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1
    exact ⟨first, first, firstNonnegative, le_rfl, ordered.trans lastBound,
      ((relation.location 0 (by decide)).point_eq.symm.trans (constant _)).trans firstEq,
      ((relation.location 1 (by decide)).point_eq.symm.trans (constant _)).trans firstEq⟩
  · let left := relation.location 0 (by decide)
    let right := relation.location 1 (by decide)
    have increasing : left.fraction ≤ right.fraction :=
      (RootContinuation.PreparedDirectedRootRefinements.RootSubedge.endpoint_order
        relation direction stationary).le
    have firstInside : 0 ≤ first ∧ first ≤ 1 := ⟨firstNonnegative, ordered.trans lastBound⟩
    have lastInside : 0 ≤ last ∧ last ≤ 1 := ⟨firstNonnegative.trans ordered, lastBound⟩
    have leftInside := interpolate_inside firstInside lastInside left.inside
    have rightInside := interpolate_inside firstInside lastInside right.inside
    have order : (1 - left.fraction) * first + left.fraction * last ≤
        (1 - right.fraction) * first + right.fraction * last := by
      apply Rat.Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
      have nonnegative := Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
        (Rat.Fraction.Order.Arithmetic.sub_nonneg_direct increasing) (Rat.Fraction.Order.Arithmetic.sub_nonneg_direct
          ordered)
      exact (by ring1 : _ = (right.fraction - left.fraction) * (last - first)).trans_ge nonnegative
    have query (parameter : Rat.Fraction.Rational) : parent.edge.point parameter = segment.pointAt ((1 - parameter) *
      first + parameter * last) := by
      rw [parent_affine, firstEq, lastEq, segment_affine]
    exact ⟨_, _, leftInside.1, order, rightInside.2,
      left.point_eq.symm.trans (query _), right.point_eq.symm.trans (query _)⟩

/-- Recasting the differential preserves the parent's original ordered source parameters. -/
theorem recast {parent : CenteredEdge curve source} (original : SegmentSource segment parent) (target :
  Hyperelliptic.Differentials.Basic.Differential genus) :
    SegmentSource segment (recastCenteredEdge target parent) := original

end SegmentSource

/-- Membership in a retained root-subedge block supplies an actual parent-to-child root relation. -/
private theorem rootBlock_member {parent child : CenteredEdge curve source} {children : List (CenteredEdge curve
  source)}
    (roots : RootSubedgeBlock parent children) (member : child ∈ children) : Nonempty (RootSubedge parent child) := by
  induction roots with
  | nil => exact (List.not_mem_nil member).elim
  | cons head tail ih =>
      rcases Membership.mem_cons.mp member with rfl | member
      · exact ⟨head⟩
      · exact ih member

/-- Every child of a directed refinement retains ordered parameters on the original segment.

The root relation and direction evidence are read from the same retained parent block, and each child inherits that
parent's existing source certificate. -/
theorem DirectedRefinement.segment_sources {parents children : List (CenteredEdge curve source)}
    (refinement : DirectedRefinement parents children) (original : ∀ parent ∈ parents, SegmentSource segment parent) :
    ∀ child ∈ children, SegmentSource segment child := by
  induction refinement with
  | nil => intro child member; exact (List.not_mem_nil member).elim
  | @cons parent parents block children chain roots direction tail ih =>
      intro child member
      rcases Membership.mem_append.mp member with member | member
      · obtain ⟨relation⟩ := rootBlock_member roots member
        exact (original parent List.mem_cons_self).refine relation (direction child member)
      · exact ih (fun parent member => original parent (List.mem_cons_of_mem _ member)) child member

end Purelib.Riemann.Paths.PreparedSegmentSources

end
