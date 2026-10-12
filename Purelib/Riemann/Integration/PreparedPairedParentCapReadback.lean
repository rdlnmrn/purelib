module
import Purelib.Data.List.Map
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonCapOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedPairedReciprocalArc
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedUniformPaths

public section

/-! Synchronized parent meshes identify the requested unsigned cap path
with the literal inverse-segment arc, preserving its endpoint chord. -/
open
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

namespace Purelib.Riemann.Integration.PreparedPairedParentCapReadback.SideBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request (Entry Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest (sourceValues)

open Purelib.Curves in
open Purelib.Integration in
/-- Identify the bank's paired paths with dyadic inverse-polynomial paths on its ordered parents.

The identity retains the exact parent order and requested common depth. -/
theorem pairedUniformPaths_eq_parents {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Hyperelliptic.Differentials.Basic.Differential genus} {collar :
      Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
    {cap : Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {regular :
      Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
    {parents : List (CenteredEdge curve differential)} {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers) (left right : Polynomial) (depth :
      Nat) :
    bank.pairedUniformPaths left right depth = parents.map (fun parent =>
      Path.Dyadic.DyadicPairedPrimitivePaths.increments (fun parameter =>
        (⟨left.eval (parent.edge.point parameter)⁻¹, right.eval (parent.edge.point parameter)⁻¹⟩ : PrimitivePoint))
          depth 0 1) := by
  induction bank with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons _) ih

end Purelib.Riemann.Integration.PreparedPairedParentCapReadback.SideBank

namespace Purelib.Riemann.Integration.PreparedPairedParentCapReadback.Request
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request (Entry Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest (sourceValues)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {parents : List (CenteredEdge
    curve differential)}
  {target : Coordinate} {minimum stage fine : Nat} {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {request : Request regular other parents
    target minimum}

open Purelib.Curves in
open Purelib.Integration in
/-- The entry's source path uses its two certified source readings at the retained request depth. -/
theorem Entry.source_path (entry : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry request sample
  otherSample fine) :
    entry.pair.1 = Path.Dyadic.DyadicPairedPrimitivePaths.increments
      (Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.sourceValues entry.certified.source
        entry.certified.otherSource) (request.depth + fine) 0 1 := by
  change entry.certified.compared.firstPath = _
  rw [Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.AreaRequest.Certified.source_path
    entry.certified, entry.depth_eq]

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
/-- Read the evaluated cap paths as the side bank's ordered paired uniform paths.

The common depth is the retained request depth plus the supplied refinement level. -/
theorem Evaluation.cap_paths (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation
  request sample otherSample fine)
    {covers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers) :
    evaluated.pairs.map Prod.snd =
      bank.pairedUniformPaths sample.primitive.value otherSample.primitive.value (request.depth + fine) := by
  rw [Integration.PreparedPairedParentCapReadback.SideBank.pairedUniformPaths_eq_parents bank, evaluated.pairs_eq,
    Data.List.Map.map_map]
  have parentsEq := (congrArg (List.map Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Plan.parent)
    evaluated.plans_eq).trans request.parents_eq
  have paths := congrArg (List.map (fun parent => Path.Dyadic.DyadicPairedPrimitivePaths.increments
    (fun parameter => (⟨sample.primitive.value.eval (parent.edge.point parameter)⁻¹,
      otherSample.primitive.value.eval (parent.edge.point parameter)⁻¹⟩ : PrimitivePoint)) (request.depth + fine) 0 1))
        parentsEq
  unfold Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Entry.pair
    Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily.CommonRibbonRequest.capValues
  have compositionResult := paths
  simp only [Data.List.Map.map_map, -eq_self, -iff_self] at compositionResult ⊢
  dsimp only [Function.comp_def] at compositionResult ⊢
  exact compositionResult

end Purelib.Riemann.Integration.PreparedPairedParentCapReadback.Request

namespace Purelib.Riemann.Integration.PreparedPairedParentCapReadback.SurfaceOccurrence
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request (Evaluation)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {target : Rational} {minimum stage fine : Nat} {box otherBox :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
/-- Identify the evaluated cap area with its inverse arc area minus the endpoint chord.

The exact subdivision depth combines the occurrence mesh depth and paired request depth, preserving both polynomial
readings and endpoints. -/
theorem paired_cap_area_arc (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    {request : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other
      occurrence.compared.entered.cache.parents target minimum}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation request sample otherSample
      fine) :
    Path.PairedIncrementArea.area (evaluated.pairs.map Prod.snd).flatten =
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (fun point => ⟨sample.primitive.value.eval point, otherSample.primitive.value.eval point⟩)
        (occurrence.piece.mesh.depth + (request.depth + fine)) occurrence.start occurrence.finish -
      Polygon.Stokes.edgeArea
        ⟨sample.primitive.value.eval occurrence.start⁻¹, otherSample.primitive.value.eval occurrence.start⁻¹⟩
        ⟨sample.primitive.value.eval occurrence.finish⁻¹, otherSample.primitive.value.eval occurrence.finish⁻¹⟩ := by
  rw [Integration.PreparedPairedParentCapReadback.Request.Evaluation.cap_paths evaluated occurrence.cap.path.bank]
  exact Hyperelliptic.Charts.Reciprocal.PreparedPairedReciprocalArc.pairedUniformPaths_area_eq_arc
    occurrence.compared.entered.cache occurrence.cap.path.bank
    sample.primitive.value otherSample.primitive.value (request.depth + fine)

open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- The requested squared error between source area and the corrected cap arc area.

The correction retains the inverse endpoint chord and the evaluation's exact common subdivision depth. -/
@[expose] def PairedArcError (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    {request : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other
      occurrence.compared.entered.cache.parents target minimum}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation request sample otherSample
      fine) : Prop :=
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (evaluated.pairs.map Prod.fst).flatten -
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (fun point => ⟨sample.primitive.value.eval point, otherSample.primitive.value.eval point⟩)
        (occurrence.piece.mesh.depth + (request.depth + fine)) occurrence.start occurrence.finish -
      Polygon.Stokes.edgeArea
        ⟨sample.primitive.value.eval occurrence.start⁻¹, otherSample.primitive.value.eval occurrence.start⁻¹⟩
        ⟨sample.primitive.value.eval occurrence.finish⁻¹, otherSample.primitive.value.eval occurrence.finish⁻¹⟩)) <
          target

open Purelib.Curves in
/-- The evaluated source area satisfies the corrected cap arc error request.

Transport the retained paired area bound through the exact cap-path readback identity. -/
theorem paired_arc_error (occurrence :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
  regular domains differential)
    {request : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other
      occurrence.compared.entered.cache.parents target minimum}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation request sample otherSample
      fine) :
    PairedArcError occurrence evaluated := by
  have bound :=
    SurfaceOccurrence.paired_area_error
    occurrence evaluated
  unfold Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation.FullAreaError at bound
  rw [paired_cap_area_arc occurrence evaluated] at bound
  exact bound

end Purelib.Riemann.Integration.PreparedPairedParentCapReadback.SurfaceOccurrence
