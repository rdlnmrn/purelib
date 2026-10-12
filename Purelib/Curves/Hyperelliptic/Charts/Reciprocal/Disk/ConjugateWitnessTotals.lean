module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedWitnessSigns
import Purelib.Integration.Path.DyadicConjugateIncrementComparison
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedWitnessSigns

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses

open Purelib.Data.List

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! The conjugate polygon of retained parent totals uses one component-wide
root sign, independent of the two covers and their numerical depths. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateWitnessTotals
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank (Links)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Basic (conj)

/-- Negate both coordinates of the retained primitive point. -/
private def negate (point : Stokes.PrimitivePoint) : PrimitivePoint := ⟨-point.left, -point.right⟩

/-- Negating each original paired increment negates its complete total. -/
private theorem total_negate (points : List Stokes.PrimitivePoint) :
    PairedIncrementArea.total (points.map negate) =
      negate (PairedIncrementArea.total points) := by
  induction points with
  | nil => apply congrArg₂ PrimitivePoint.mk <;> exact (neg_zero).symm
  | cons head tail ih =>
      change (negate head).add
        (PairedIncrementArea.total (tail.map negate))
        =
        negate (head.add (PairedIncrementArea.total
          tail))
      rw [ih]
      apply congrArg₂ PrimitivePoint.mk <;> dsimp only
        [negate, PrimitivePoint.add] <;> ring1

/-- Negating both coordinates of every original paired increment preserves its complete area. -/
private theorem area_negate (points : List Stokes.PrimitivePoint) :
    PairedIncrementArea.area (points.map negate) =
      PairedIncrementArea.area points := by
  induction points with
  | nil => rfl
  | cons head tail ih =>
      rw [List.map_cons, PairedAreaBlocks.area_cons, PairedAreaBlocks.area_cons,
        total_negate, ih]
      simp only [Stokes.edgeArea, negate]
      ring1

variable {genus : Nat} {curve : HyperellipticCurve genus} {source target :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {index depth otherDepth : Nat}
    {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap source index box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap target index otherBox}

/-- The original pair of cap-polynomial endpoint increments with the first coordinate conjugated. -/
private def endpointPair (left right : InverseRootPolynomial.Polynomial) (parent :
  PreparedSubdivisionModelCore.CenteredEdge curve source) : PrimitivePoint :=
  ⟨conj (left.eval (parent.edge.point 1)⁻¹ - left.eval (parent.edge.point 0)⁻¹),
    right.eval (parent.edge.point 1)⁻¹ - right.eval (parent.edge.point 0)⁻¹⟩

/-- The actual paired regular path totals equal the original endpoint-pair list, independently of their retained covers
and depths. -/
private theorem paths_totals (left right : InverseRootPolynomial.Polynomial)
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} {covers :
      UniformReciprocalCover.ParentCovers parents}
    (bank : ParentJoins.SideBank regular covers) :
    ∀ {otherCovers : UniformReciprocalCover.ParentCovers (parents.map (PreparedEdgeRecasting.recastCenteredEdge
      target))}
      (otherBank : ParentJoins.SideBank regular otherCovers),
      List.zipWith (fun first last => (⟨conj (Data.Gaussian.Norm.Sum.Basic.gaussianSum first),
        Data.Gaussian.Norm.Sum.Basic.gaussianSum last⟩ : Stokes.PrimitivePoint))
        (SideBank.regularPrimitivePaths left depth bank)
        (SideBank.regularPrimitivePaths right otherDepth otherBank) =
      parents.map (endpointPair left right) := by
  induction bank with
  | nil => intro otherCovers otherBank; cases otherBank; rfl
  | cons head tail ih =>
      intro otherCovers otherBank
      cases otherBank with
      | cons otherHead otherTail =>
          change (⟨conj (Data.Gaussian.Norm.Sum.Basic.gaussianSum (Preparation.regularPrimitivePath head left
            depth)),
            Data.Gaussian.Norm.Sum.Basic.gaussianSum (Preparation.regularPrimitivePath otherHead right otherDepth)⟩
              : Stokes.PrimitivePoint) :: _ = _ :: _
          apply congrArg₂ List.cons ?_ (ih otherTail)
          simp only [Preparation.regularPrimitivePath,
            DyadicPrimitivePaths.dyadicIncrements_sum]
          rfl

/-- One common sign on the two original cap polynomials preserves the complete conjugate endpoint polygon area. -/
private theorem endpoint_signed (left right : InverseRootPolynomial.Polynomial) (flip : Bool) (parents : List
  (PreparedSubdivisionModelCore.CenteredEdge curve source)) :
    PairedIncrementArea.area (parents.map
      (endpointPair (if flip then -left else left)
      (if flip then -right else right))) =
      PairedIncrementArea.area (parents.map
        (endpointPair left right)) := by
  cases flip with
  | false => rfl
  | true =>
      have points : parents.map (endpointPair (-left)
        (-right)) = (parents.map (endpointPair left
        right)).map negate := by
        rw [Map.map_map]
        apply Map.map_congr_left
        intro parent _
        apply congrArg₂ PrimitivePoint.mk
        · change Data.Gaussian.Basic.conj ((-left).eval _ - (-left).eval _) =
            -Data.Gaussian.Basic.conj (left.eval _ - left.eval _)
          rw [DensePolynomial.eval_neg, DensePolynomial.eval_neg]
          have equal (a b : InverseRootPolynomial.Gaussian) : -a - -b = -(a - b) := by ring1
          rw [equal]
          rfl
        · change (-right).eval _ - (-right).eval _ = -(right.eval _ - right.eval _)
          rw [DensePolynomial.eval_neg, DensePolynomial.eval_neg]
          ring1
      exact (congrArg PairedIncrementArea.area points).trans
        (area_negate _)

/-- The actual root joins, together with recasting, remove one common sign from the full polygon of cached totals. No
equality of subdivisions is needed. -/
theorem RegularWitnesses.conjugate_total_polygon
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} {covers :
      UniformReciprocalCover.ParentCovers parents}
    {bank : ParentJoins.SideBank regular covers} {paths : List (List InverseRootPolynomial.Gaussian)}
    {otherCovers : UniformReciprocalCover.ParentCovers (parents.map (PreparedEdgeRecasting.recastCenteredEdge target))}
    {otherBank : ParentJoins.SideBank regular otherCovers} {otherPaths : List (List InverseRootPolynomial.Gaussian)}
    (first : RegularWitnesses sample depth bank paths) (last : RegularWitnesses otherSample otherDepth
      otherBank otherPaths)
    (links : SideBank.Links bank) (otherLinks : SideBank.Links otherBank) :
    PairedIncrementArea.area (List.zipWith
      (fun left right => (⟨conj (Data.Gaussian.Norm.Sum.Basic.gaussianSum left),
        Data.Gaussian.Norm.Sum.Basic.gaussianSum right⟩ : Stokes.PrimitivePoint)) paths otherPaths) =
      PairedIncrementArea.area (parents.map (fun parent =>
        (⟨conj (sample.primitive.value.eval (parent.edge.point 1)⁻¹ - sample.primitive.value.eval (parent.edge.point
          0)⁻¹),
          otherSample.primitive.value.eval (parent.edge.point 1)⁻¹ - otherSample.primitive.value.eval (parent.edge.point
            0)⁻¹⟩ :
            Stokes.PrimitivePoint))) := by
  let sign := RegularWitnesses.recastSign first last
  have pathsEq := RegularWitnesses.paired_paths_signed
    first last sign links otherLinks
  have totals := (congrArg₂ (List.zipWith
    (fun left right => (⟨conj (Data.Gaussian.Norm.Sum.Basic.gaussianSum left),
      Data.Gaussian.Norm.Sum.Basic.gaussianSum right⟩ : Stokes.PrimitivePoint))) pathsEq.1 pathsEq.2).trans
      (paths_totals _ _ bank otherBank)
  exact (congrArg PairedIncrementArea.area totals).trans
    (endpoint_signed _ _ sign.flip parents)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateWitnessTotals
