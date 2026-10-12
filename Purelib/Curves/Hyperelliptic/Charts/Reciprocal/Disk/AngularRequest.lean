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
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {comparison :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell}

set_option genInjectivity false in
/-- A positive angular margin retained before reciprocal chart vertex acquisition.

The original source orientation, norm ceiling and dyadic width determine the margin; the opposite orientation keeps a
positive fallback for general area comparison. -/
structure AngularRequest (comparison : ArcSamples.Data regular cell) (depth : Nat) (lower upper :
  InverseRootPolynomial.Coordinate) where
  /-- The cached oriented cross energy of the original source parent endpoints. -/ angular :
    InverseRootPolynomial.Coordinate
  /-- The cached angular factor equals the original source endpoint cross energy. -/ angular_eq : angular =
    AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1)
  /-- The cached common squared-norm ceiling on the original source boundary. -/ normUpper :
    InverseRootPolynomial.Coordinate
  /-- The ceiling is twice the square of the original reciprocal collar radius. -/ normUpper_eq : normUpper = 2 *
    ReciprocalExteriorCollar.radius curve ^ 2
  /-- The retained source norm ceiling is strictly positive. -/ normPositive : 0 < normUpper
  /-- The cached source-parameter width of one dyadic step. -/ width : InverseRootPolynomial.Coordinate
  /-- The step width is the original interval width divided by the exact dyadic count. -/ width_eq : width = (upper -
    lower) / ((2 ^ depth : Nat) : InverseRootPolynomial.Coordinate)
  /-- The retained dyadic step width is strictly positive. -/ widthPositive : 0 < width
  /-- The cached positive reciprocal-arc angular margin. -/ margin : InverseRootPolynomial.Coordinate
  /-- A positive original orientation uses the width-scaled angular factor divided by the squared norm ceiling;
    otherwise the margin is one. -/ margin_eq : margin = if 0 < angular then width * angular / normUpper ^ 2 else 1
  /-- The retained reciprocal-arc margin is strictly positive. -/ positive : 0 < margin

constructive_injectivity AngularRequest

namespace AngularRequest

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.AngularRequest in
/-- Cache the original source angular factor, positive norm ceiling and dyadic width, then select their positive
reciprocal-arc margin. -/
def build (comparison : ArcSamples.Data regular cell) (depth : Nat)
    (lower upper : InverseRootPolynomial.Coordinate) (ordered : lower < upper) :
      AngularRequest comparison depth lower upper := by
  let angular := AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1)
  let normUpper := 2 * ReciprocalExteriorCollar.radius curve ^ 2
  have normPositive : 0 < normUpper := Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (ReciprocalExteriorCollar.radius_square_positive curve)
  let width := (upper - lower) / ((2 ^ depth : Nat) : InverseRootPolynomial.Coordinate)
  have widthPositive : 0 < width := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Arithmetic.sub_pos_direct ordered)
    (Fraction.Cast.Order.natCast_pos_direct (Nat.pow_pos (by decide)))
  let margin := if 0 < angular then width * angular / normUpper ^ 2 else 1
  have positive : 0 < margin := by
    dsimp only [margin]
    split
    · exact Fraction.Order.Field.div_pos_direct (Fraction.Order.Arithmetic.mul_pos_direct widthPositive ‹0 < angular›)
        (Fraction.Order.Arithmetic.pow_pos_direct normPositive 2)
    · decide
  exact ⟨angular, rfl, normUpper, rfl, normPositive, width, rfl, widthPositive, margin, rfl, positive⟩

/-- The reversed inverse-endpoint cross energy is the original cross energy divided by both squared endpoint norms. -/
private theorem inverse_area (first last : InverseRootPolynomial.Gaussian) :
    AffineTriangle.crossEnergy last⁻¹ first⁻¹ = AffineTriangle.crossEnergy first last /
      (Data.Gaussian.Norm.Basic.normSq first * Data.Gaussian.Norm.Basic.normSq last) := by
  simp only [AffineTriangle.crossEnergy, Data.Gaussian.Basic.conj, Data.Gaussian.Field.inv_eq,
    Data.Gaussian.Field.inv, Data.Gaussian.Basic.mul_im, Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.inv_mul_direct]
  ring1

/-- The affine source parameter, rather than an endpoint-chord substitution, determines the original angular factor. -/
theorem source_area (first last : InverseRootPolynomial.Coordinate) :
    AffineTriangle.crossEnergy (parent.edge.point first) (parent.edge.point last) =
      (last - first) * AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1) := by
  change AffineTriangle.crossEnergy (parent.edge.localSegment.pointAt first) (parent.edge.localSegment.pointAt last) =
    (last - first) * AffineTriangle.crossEnergy (parent.edge.localSegment.pointAt 0) (parent.edge.localSegment.pointAt
      1)
  simp only [AffineTriangle.crossEnergy, ClearSegment.pointAt, Data.Gaussian.Basic.conj,
    Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
    Data.Gaussian.Basic.mul_im, Data.Gaussian.Scale.scale_re, Data.Gaussian.Scale.scale_im,
      Fraction.Field.div_eq_mul_inv_direct]
  ring1

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.AngularRequest in
/-- The retained positive angular margin bounds every original inverse-arc step with the specified dyadic width. -/
theorem lower {depth : Nat} {lower upper : InverseRootPolynomial.Coordinate} (request :
  AngularRequest comparison depth lower upper)
    (oriented : 0 < AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))
    {first last : InverseRootPolynomial.Coordinate} (firstInside : edge.left.parameter ≤ first ∧ first ≤
      edge.right.parameter)
    (lastInside : edge.left.parameter ≤ last ∧ last ≤ edge.right.parameter)
    (width : ((2 ^ depth : Nat) : InverseRootPolynomial.Coordinate) * (last - first) = upper - lower) :
    request.margin ≤ AffineTriangle.crossEnergy (parent.edge.point last)⁻¹ (parent.edge.point first)⁻¹ := by
  have firstBoundary := data.boundary.point ⟨edge.left.inside.1.trans firstInside.1, firstInside.2.trans
    edge.right.inside.2⟩
  have lastBoundary := data.boundary.point ⟨edge.left.inside.1.trans lastInside.1, lastInside.2.trans
    edge.right.inside.2⟩
  have firstPositive := Data.Gaussian.Norm.Basic.normSq_pos (PreparedExteriorReciprocal.boundary_nonzero firstBoundary)
  have lastPositive := Data.Gaussian.Norm.Basic.normSq_pos (PreparedExteriorReciprocal.boundary_nonzero lastBoundary)
  have denominatorPositive := Fraction.Order.Arithmetic.mul_pos_direct firstPositive lastPositive
  have firstUpper : Data.Gaussian.Norm.Basic.normSq (parent.edge.point first) ≤ request.normUpper := by
    rw [request.normUpper_eq]; exact (ReciprocalExteriorCollar.boundary_norm_bounds curve firstBoundary).2
  have lastUpper : Data.Gaussian.Norm.Basic.normSq (parent.edge.point last) ≤ request.normUpper := by
    rw [request.normUpper_eq]; exact (ReciprocalExteriorCollar.boundary_norm_bounds curve lastBoundary).2
  have denominatorUpper := (Fraction.Order.Arithmetic.mul_le_mul_direct firstUpper lastUpper lastPositive.le
    request.normPositive.le).trans_eq
    (show request.normUpper * request.normUpper = request.normUpper ^ 2 by ring1)
  have widthEq : request.width = last - first := by
    rw [request.width_eq]
    apply Fraction.Field.mul_right_cancel_of_ne
      (Fraction.Cast.Order.natCast_pos_direct (Nat.pow_pos (by decide : 0 < 2)) (n := 2 ^ depth)).ne'
    rw [Fraction.Field.div_mul_cancel_of_ne _ _
      (Fraction.Cast.Order.natCast_pos_direct (Nat.pow_pos (by decide : 0 < 2)) (n := 2 ^ depth)).ne']
    exact width.symm.trans (by ring1)
  have angularPositive : 0 < request.angular := request.angular_eq.symm ▸ oriented
  rw [request.margin_eq, if_pos angularPositive,
    inverse_area,
    source_area, ← request.angular_eq, ←
    widthEq]
  exact Fraction.Order.Field.div_le_div_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_pos_direct request.widthPositive angularPositive).le denominatorPositive
      denominatorUpper

end AngularRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
