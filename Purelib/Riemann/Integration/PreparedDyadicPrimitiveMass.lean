module
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Algebra.NatCast
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Integration.Path.Dyadic.DyadicAreaRefinement
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
public import Purelib.Riemann.Integration.PreparedDyadicPrimitiveResampling
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Readings.PreparedDyadicPrimitiveArea
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! The source covers bound the mass of every scheduled primitive path
independently of the retained polynomial index and subdivision depth. -/
namespace Purelib.Riemann.Integration.PreparedDyadicPrimitiveMass

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.PreparedDyadicPrimitiveArea (dyadicPrimitivePath)
open Purelib.Riemann.Integration.PreparedDyadicPrimitiveResampling (PrimitiveSlopeBound)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements_length)
open Purelib.Integration.Path.Dyadic.DyadicAreaRefinement (dyadicIncrements_bounded)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {target : Coordinate}

open Purelib.Integration.Path.Dyadic in
/-- The shared-depth primitive path has original parent count times dyadic count many increments. -/
private theorem path_length (depth : Nat) : ∀ {parents : List (CenteredEdge curve source)}
    (requests : RequestedParents count target parents),
    (dyadicPrimitivePath depth requests).length = parents.length * 2 ^ depth
  | _, .nil => (Nat.zero_mul _).symm
  | _, .cons request tail => by
      rw [dyadicPrimitivePath, Purelib.Data.List.Append.length_append, DyadicPrimitivePaths.dyadicIncrements_length,
        path_length depth tail,
        List.length_cons, Nat.succ_mul, Nat.add_comm]

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path.Dyadic in
/-- The original primitive slope bound controls each retained dyadic increment by its quarter-radius. -/
private theorem path_bounded (depth : Nat) {slope : Coordinate} :
    ∀ {parents : List (CenteredEdge curve source)} (requests : RequestedParents count target parents),
    PrimitiveSlopeBound slope requests → ∀ value ∈ dyadicPrimitivePath depth requests,
      normSq value ≤ Geometric.Basic.quarterRadius slope depth
  | _, .nil, _, _, member => nomatch member
  | parent :: _, .cons request tail, bounded, value, member => by
      rcases Purelib.Data.List.Membership.mem_append.mp member with inHead | inTail
      · have slopeBounds : ∀ first last : Fraction.Rational, 0 ≤ first ∧ first ≤ 1 → 0 ≤ last ∧ last ≤ 1 →
            Data.Gaussian.Norm.Basic.normSq
              (request.request.model.primitive.value.eval (parent.edge.point last) -
                request.request.model.primitive.value.eval (parent.edge.point first)) ≤ slope * (last - first) ^ 2 := by
          intro first last firstInside lastInside
          have scalar := bounded.1 first last firstInside lastInside
          simpa only [-eq_self, -iff_self, Norm.Basic.normSq_eq_canonical] using scalar
        have scalar := DyadicAreaRefinement.dyadicIncrements_bounded
          (fun parameter => request.request.model.primitive.value.eval (parent.edge.point parameter)) slopeBounds depth
          ⟨le_rfl, by decide⟩ ⟨by decide, le_rfl⟩ (by decide) value inHead
        simpa only [-eq_self, -iff_self, Norm.Basic.normSq_eq_canonical, (show (1 : Purelib.Data.Rat.Fraction.Rational)
          - 0 = 1 by ring1), one_pow, Fraction.Field.mul_one_direct] using scalar
      · exact path_bounded depth tail bounded.2 value inTail

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The shared-depth primitive path's count-weighted squared-norm mass is bounded independently of depth.

The exact dyadic path length cancels the quarter-radius decay, leaving the square of the original parent count times its
retained primitive slope bound. -/
theorem dyadicPrimitivePath_mass {parents : List (CenteredEdge curve source)}
    (requests : RequestedParents count target parents) {slope : Coordinate}
    (bounded : PrimitiveSlopeBound slope requests) (depth : Nat) :
    ((dyadicPrimitivePath depth requests).length : Coordinate) *
      Norm.Sum.Basic.gaussianNormSqSum (dyadicPrimitivePath depth requests) ≤ (parents.length : Coordinate)^2 * slope :=
        by
  have mass := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Norm.Sum.Bounds.normSum_le (dyadicPrimitivePath depth requests) _
      (fun value member => (Norm.Basic.normSq_eq_canonical value).trans_le
        (path_bounded depth requests bounded value member)))
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le (dyadicPrimitivePath depth requests).length))
  apply mass.trans_eq
  rw [path_length, Purelib.Algebra.NatCast.mul]
  calc
    _ = (parents.length : Coordinate)^2 *
        (((2 ^ depth : Nat) : Coordinate) * (((2 ^ depth : Nat) : Coordinate) * Geometric.Basic.quarterRadius slope
          depth)) := by ring1
    _ = _ := congrArg (fun value => (parents.length : Coordinate)^2 * value)
      (Geometric.DyadicCount.dyadic_count_cancel slope depth)

end Purelib.Riemann.Integration.PreparedDyadicPrimitiveMass
