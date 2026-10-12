module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedEndpoints
public import Purelib.Riemann.Topology.PreparedRecastRootChains
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SheetAlignment
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelOverlap

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSourceRootJoins

open Purelib.Riemann.Integration

open Purelib.Riemann.Topology.PreparedRecastRootChains

@[expose] public section

/-! Recasting the differential retains the actual source root at every
parameter. Its reciprocal channels therefore acquire a join automatically. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins.ReciprocalDiskArcOwners
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Polynomial)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRecastRootChains.PreparedDirectDyadicRefinements (recastPreparedEdge_rootName)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point Join)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
variable {genus count otherCount : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source
  target : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve source}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge target parent)}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {edge otherEdge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge} {otherCell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell otherData otherEdge}
  {model : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell} {otherModel :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel otherCell} {parameter :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}

/-- No caller root equivalence is required. Both local channels consume the same source root name retained by
differential recasting, even when their reciprocal covers and local inverse models differ. -/
def Join.ofRecast (first : ArcOwners.Point cap model parameter) (last : ArcOwners.Point cap otherModel parameter) :
  ArcOwners.Join first last := by
  have roots : Gaussian.Equivalence.NamedEquivalent
      (parent.edge.rootName parameter ⟨edge.left.inside.1.trans first.root.between.1, first.root.between.2.trans
        edge.right.inside.2⟩)
      ((PreparedEdgeRecasting.recastCenteredEdge target parent).edge.rootName parameter
        ⟨otherEdge.left.inside.1.trans last.root.between.1, last.root.between.2.trans otherEdge.right.inside.2⟩) := by
    change Gaussian.Equivalence.NamedEquivalent _ ((PreparedEdgeRecasting.recastPreparedEdge target
      parent.edge).rootName parameter _)
    rw [PreparedDirectDyadicRefinements.recastPreparedEdge_rootName]
    exact NamedEquivalent.refl _
  let joined := SourceJoin.build first.root last.root
    (parent.edge.point parameter) rfl rfl roots
  exact Join.ofRoots first last rfl (SourceJoin.rootEquivalent joined)

variable {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {index : Nat} {box
  otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap source index box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap target index otherBox}
  {first : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap model parameter} {last :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners.Point cap otherModel parameter} {firstValue lastValue
    : Purelib.Riemann.Normalization.InverseRootPolynomial.Polynomial}

/-- The actual retained endpoint primitives now share their sign without a caller-supplied join or a comparison of
independently chosen sheet bits. -/
theorem recast_primitive_signed
    (left : RegularEndpoints.RegularEndpoint regular sample first firstValue)
    (right : RegularEndpoints.RegularEndpoint regular otherSample last lastValue)
    (later : 2 ≤ index) :
    (firstValue, lastValue) =
      (if left.alignment.first.flip then -sample.primitive.value else sample.primitive.value,
       if left.alignment.first.flip then -otherSample.primitive.value else otherSample.primitive.value) :=
  RegularEndpoint.paired_primitive_signed left right
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins.ReciprocalDiskArcOwners.Join.ofRecast first last) later

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins.ReciprocalDiskArcOwners

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins.ReciprocalDiskParentComparison
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison (Preparation)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
variable {genus count otherCount : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source
  target : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {parent :
    Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve source}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge target parent)}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {otherData :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data otherPatch otherCount}
  {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {otherCover :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover otherData}

/-- The first retained endpoints are joined from their original source owner. No equality of the two reciprocal
preparation meshes is assumed. -/
def Preparation.recastFirstJoin (first : ParentComparison.Preparation regular cover) (last :
  ParentComparison.Preparation regular otherCover) :
    ArcOwners.Join first.boundary.first.point last.boundary.first.point :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins.ReciprocalDiskArcOwners.Join.ofRecast
    first.boundary.first.point last.boundary.first.point

/-- The same source-owner transport also joins the final retained endpoints. -/
def Preparation.recastLastJoin (first : ParentComparison.Preparation regular cover) (last : ParentComparison.Preparation
  regular otherCover) :
    ArcOwners.Join first.boundary.last.point last.boundary.last.point :=
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins.ReciprocalDiskArcOwners.Join.ofRecast
    first.boundary.last.point last.boundary.last.point

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins.ReciprocalDiskParentComparison
