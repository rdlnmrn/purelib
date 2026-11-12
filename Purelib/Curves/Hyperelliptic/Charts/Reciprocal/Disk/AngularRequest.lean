module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Geometry.ClearPath

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedExteriorReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.ReciprocalDiskCoordinateOrientation
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Data.Rat.Fraction

open Purelib.Data.Gaussian

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Data.Rat

open Purelib.Integration.Energy

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Riemann.Normalization

@[expose] public section

/-!
# Finite angular margins before chart vertex acquisition

An oriented source parent has a positive inverse-arc area at each dyadic
step. The cached source norm ceiling supplies one lower margin for every
step. The other orientation remains available for ordinary area comparison.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Energy.AffineTriangle (crossEnergy)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {regular : RegularBounds.Data cap} {comparison :
    ArcSamples.Data regular cell}

set_option genInjectivity false in
/-- A positive angular margin retained before reciprocal chart vertex acquisition.

The original source orientation, norm ceiling and dyadic width determine the margin; the opposite orientation keeps a
positive fallback for general area comparison. -/
structure AngularRequest (comparison : ArcSamples.Data regular cell) (depth : Nat) (lower upper :
  Coordinate) where
  /-- The cached oriented cross energy of the original source parent endpoints. -/ angular :
    Coordinate
  /-- The cached angular factor equals the original source endpoint cross energy. -/ angular_eq : angular =
    crossEnergy (parent.edge.point 0) (parent.edge.point 1)
  /-- The cached common squared-norm ceiling on the original source boundary. -/ normUpper :
    Coordinate
  /-- The ceiling is twice the square of the original reciprocal collar radius. -/ normUpper_eq : normUpper = 2 *
    ReciprocalExteriorCollar.radius curve ^ 2
  /-- The retained source norm ceiling is strictly positive. -/ normPositive : 0 < normUpper
  /-- The cached source-parameter width of one dyadic step. -/ width : Coordinate
  /-- The step width is the original interval width divided by the exact dyadic count. -/ width_eq : width = (upper -
    lower) / ((2 ^ depth : Nat) : Coordinate)
  /-- The retained dyadic step width is strictly positive. -/ widthPositive : 0 < width
  /-- The cached positive reciprocal-arc angular margin. -/ margin : Coordinate
  /-- A positive original orientation uses the width-scaled angular factor divided by the squared norm ceiling;
    otherwise the margin is one. -/ margin_eq : margin = if 0 < angular then width * angular / normUpper ^ 2 else 1
  /-- The retained reciprocal-arc margin is strictly positive. -/ positive : 0 < margin

constructive_injectivity AngularRequest

namespace AngularRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.AngularRequest in
/-- Cache the original source angular factor, positive norm ceiling and dyadic width, then select their positive
reciprocal-arc margin. -/
def build (comparison : ArcSamples.Data regular cell) (depth : Nat)
    (lower upper : Coordinate) (ordered : lower < upper) :
      AngularRequest comparison depth lower upper := by
  let angular := crossEnergy (parent.edge.point 0) (parent.edge.point 1)
  let normUpper := 2 * ReciprocalExteriorCollar.radius curve ^ 2
  have normPositive : 0 < normUpper := Order.Arithmetic.mul_pos_direct (by decide)
    (ReciprocalExteriorCollar.radius_square_positive curve)
  let width := (upper - lower) / ((2 ^ depth : Nat) : Coordinate)
  have widthPositive : 0 < width := Order.Field.div_pos_direct
    (Order.Arithmetic.sub_pos_direct ordered)
    (Cast.Order.natCast_pos_direct (Nat.pow_pos (by decide)))
  let margin := if 0 < angular then width * angular / normUpper ^ 2 else 1
  have positive : 0 < margin := by
    dsimp only [margin]
    split
    · exact Order.Field.div_pos_direct (Order.Arithmetic.mul_pos_direct widthPositive ‹0 < angular›)
        (Order.Arithmetic.pow_pos_direct normPositive 2)
    · decide
  exact ⟨angular, rfl, normUpper, rfl, normPositive, width, rfl, widthPositive, margin, rfl, positive⟩

/-- The reversed inverse-endpoint cross energy is the original cross energy divided by both squared endpoint norms. -/
private theorem inverse_area (first last : Gaussian) :
    crossEnergy last⁻¹ first⁻¹ = crossEnergy first last /
      (Norm.Basic.normSq first * Norm.Basic.normSq last) := by
  simp only [crossEnergy, Basic.conj, Field.inv_eq,
    Field.inv, Basic.mul_im, Field.div_eq_mul_inv_direct,
    Field.inv_mul_direct]
  ring1

/-- The affine source parameter, rather than an endpoint-chord substitution, determines the original angular factor. -/
theorem source_area (first last : Coordinate) :
    crossEnergy (parent.edge.point first) (parent.edge.point last) =
      (last - first) * crossEnergy (parent.edge.point 0) (parent.edge.point 1) := by
  change crossEnergy (parent.edge.localSegment.pointAt first) (parent.edge.localSegment.pointAt last) =
    (last - first) * crossEnergy (parent.edge.localSegment.pointAt 0) (parent.edge.localSegment.pointAt
      1)
  simp only [crossEnergy, ClearSegment.pointAt, Basic.conj,
    Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im,
    Basic.mul_im, Scale.scale_re, Scale.scale_im,
      Field.div_eq_mul_inv_direct]
  ring1

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.AngularRequest in
/-- The retained positive angular margin bounds every original inverse-arc step with the specified dyadic width. -/
theorem lower {depth : Nat} {lower upper : Coordinate} (request :
  AngularRequest comparison depth lower upper)
    (oriented : 0 < crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    {first last : Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter)
    (width : ((2 ^ depth : Nat) : Coordinate) * (last - first) = upper - lower) :
    request.margin ≤ crossEnergy (parent.edge.point last)⁻¹ (parent.edge.point first)⁻¹ := by
  have firstBoundary := data.boundary.point ⟨edge.left.inside.1.trans firstInside.1, firstInside.2.trans
    edge.right.inside.2⟩
  have lastBoundary := data.boundary.point ⟨edge.left.inside.1.trans lastInside.1, lastInside.2.trans
    edge.right.inside.2⟩
  have firstPositive := Norm.Basic.normSq_pos (PreparedExteriorReciprocal.boundary_nonzero firstBoundary)
  have lastPositive := Norm.Basic.normSq_pos (PreparedExteriorReciprocal.boundary_nonzero lastBoundary)
  have denominatorPositive := Order.Arithmetic.mul_pos_direct firstPositive lastPositive
  have firstUpper : Norm.Basic.normSq (parent.edge.point first) ≤ request.normUpper := by
    rw [request.normUpper_eq]; exact (ReciprocalExteriorCollar.boundary_norm_bounds curve firstBoundary).2
  have lastUpper : Norm.Basic.normSq (parent.edge.point last) ≤ request.normUpper := by
    rw [request.normUpper_eq]; exact (ReciprocalExteriorCollar.boundary_norm_bounds curve lastBoundary).2
  have denominatorUpper := (Order.Arithmetic.mul_le_mul_direct firstUpper lastUpper lastPositive.le
    request.normPositive.le).trans_eq
    (show request.normUpper * request.normUpper = request.normUpper ^ 2 by ring1)
  have widthEq : request.width = last - first := by
    rw [request.width_eq]
    apply Fraction.Field.mul_right_cancel_of_ne
      (Cast.Order.natCast_pos_direct (Nat.pow_pos (by decide : 0 < 2)) (n := 2 ^ depth)).ne'
    rw [Field.div_mul_cancel_of_ne _ _
      (Cast.Order.natCast_pos_direct (Nat.pow_pos (by decide : 0 < 2)) (n := 2 ^ depth)).ne']
    exact width.symm.trans (by ring1)
  have angularPositive : 0 < request.angular := request.angular_eq.symm ▸ oriented
  rw [request.margin_eq, if_pos angularPositive,
    inverse_area,
    source_area, ← request.angular_eq, ←
    widthEq]
  exact Order.Field.div_le_div_of_nonneg_left_direct
    (Order.Arithmetic.mul_pos_direct request.widthPositive angularPositive).le denominatorPositive
      denominatorUpper

end AngularRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
