module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelOverlap

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSidePrimitive

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

@[expose] public section

/-! A common signed primitive pair is extracted from the actual retained
path witnesses. Recast parent roots discharge the comparison automatically. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedWitnessSigns
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Gaussian)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank (Links)

set_option genInjectivity false in
/-- Cache the common sheet bit, with both signed polynomial identities. -/
structure PairedPrimitiveSign (first last left right : InverseRootPolynomial.Polynomial) where
  /-- The actual common reciprocal sheet sign retained for both primitive polynomials. -/ flip : Bool
  /-- Both retained polynomials equal their original cap samples with that exact common sign. -/ signed : (first, last)
    = (if flip then -left else left, if flip then -right else right)

constructive_injectivity PairedPrimitiveSign

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source target :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {index depth otherDepth : Nat}
    {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap source index box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap target index otherBox}

/-- Independent numerical depths and reciprocal covers are allowed. The original parent list and its recast root names
fix the common sign. -/
def RegularWitnesses.recastSign
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} {covers :
      UniformReciprocalCover.ParentCovers parents}
    {bank : ParentJoins.SideBank regular covers} {paths : List (List InverseRootPolynomial.Gaussian)}
    (first : RegularWitnesses sample depth bank paths) :
    ∀ {otherCovers : UniformReciprocalCover.ParentCovers (parents.map (PreparedEdgeRecasting.recastCenteredEdge
      target))}
      {otherBank : ParentJoins.SideBank regular otherCovers} {otherPaths : List (List InverseRootPolynomial.Gaussian)}
      (last : RegularWitnesses otherSample otherDepth otherBank otherPaths),
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedWitnessSigns.PairedPrimitiveSign first.primitive last.primitive
        sample.primitive.value otherSample.primitive.value := by
  cases first with
  | nil =>
      intro otherCovers otherBank otherPaths last
      cases last
      exact ⟨false, rfl⟩
  | cons head tail =>
      intro otherCovers otherBank otherPaths last
      cases last with
      | cons otherHead otherTail =>
          exact ⟨head.first.alignment.first.flip,
            ReciprocalDiskArcOwners.recast_primitive_signed
              head.first otherHead.first head.ready⟩

/-- Consume the cached common sign on both complete retained paths. Each bank's own root joins identify its polynomial
along all original parents. -/
theorem RegularWitnesses.paired_paths_signed
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} {covers :
      UniformReciprocalCover.ParentCovers parents}
    {bank : ParentJoins.SideBank regular covers} {paths : List (List InverseRootPolynomial.Gaussian)}
    {otherParents : List (PreparedSubdivisionModelCore.CenteredEdge curve target)} {otherCovers :
      UniformReciprocalCover.ParentCovers otherParents}
    {otherBank : ParentJoins.SideBank regular otherCovers} {otherPaths : List (List InverseRootPolynomial.Gaussian)}
    (first : RegularWitnesses sample depth bank paths) (last : RegularWitnesses otherSample otherDepth
      otherBank otherPaths)
    (sign : Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedWitnessSigns.PairedPrimitiveSign first.primitive
      last.primitive sample.primitive.value otherSample.primitive.value)
    (links : SideBank.Links bank) (otherLinks : SideBank.Links otherBank) :
    paths = SideBank.regularPrimitivePaths
      (if sign.flip then -sample.primitive.value else sample.primitive.value) depth bank ∧
      otherPaths = SideBank.regularPrimitivePaths
        (if sign.flip then -otherSample.primitive.value else otherSample.primitive.value) otherDepth otherBank := by
  have firstEq := congrArg Prod.fst sign.signed
  have lastEq := congrArg Prod.snd sign.signed
  exact ⟨(first.paths_eq first.primitive (first.shared links)).trans
      (congrArg (fun value => SideBank.regularPrimitivePaths value depth bank) firstEq),
    (last.paths_eq last.primitive (last.shared otherLinks)).trans
      (congrArg (fun value => SideBank.regularPrimitivePaths value otherDepth otherBank) lastEq)⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedWitnessSigns
