module
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedPairedReciprocalArc
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.DyadicConjugateIncrementComparison
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedPairedParentCapReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConjugateParentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

public section

/-! The whole exterior occurrence compares with its literal conjugate cap
arc at the synchronized depth, retaining the endpoint chord. -/
namespace Purelib.Riemann.Integration.PreparedConjugateParentCapReadback
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
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst)
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

open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
open Purelib.Polynomial in
open Purelib.Riemann.Integration in
open Purelib.Topology.Polygon in
/-- The conjugated primitive cap-path area equals its retained reciprocal arc area minus the endpoint chord area.

The identity retains the original paired samples, actual cap bank and summed mesh/request/refinement depth, conjugating
only the first primitive component. -/
theorem conjugate_cap_area_arc (occurrence :
  Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence regular domains
  differential)
    {request : Charts.Reciprocal.Disk.PairedParentRequest.Request regular other
      occurrence.compared.entered.cache.parents target minimum}
    (evaluated : Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation request sample otherSample fine) :
    PairedIncrementArea.area ((evaluated.pairs.map Prod.snd).flatten.map ConjugateIncrementComparison.conjugateFirst) =
      Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (fun point => ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval point,
          otherSample.primitive.value.eval point⟩)
        (occurrence.piece.mesh.depth + (request.depth + fine)) occurrence.start occurrence.finish -
      Stokes.edgeArea
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.start⁻¹,
          otherSample.primitive.value.eval occurrence.start⁻¹⟩)
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.finish⁻¹,
          otherSample.primitive.value.eval occurrence.finish⁻¹⟩) := by
  rw [PreparedPairedParentCapReadback.Request.Evaluation.cap_paths evaluated occurrence.cap.path.bank,
    Charts.Reciprocal.PreparedPairedReciprocalArc.pairedUniformPaths_segment occurrence.compared.entered.cache
      occurrence.cap.path.bank,
    DyadicConjugateIncrementComparison.Bilinear.increments_conjugate, DyadicPairedPrimitivePaths.increments_area,
    Geometry.ClearPath.ClearSegment.pointAt_zero, Geometry.ClearPath.ClearSegment.pointAt_one]
  rfl

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Topology.Polygon in
/-- The original conjugated parent-area error against the retained reciprocal arc and chord.

Its squared Gaussian norm is compared with the request's exact target, using the same paired evaluation, ordered
endpoints and summed dyadic depth. -/
@[expose] def ConjugateArcError (occurrence :
  Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence regular domains
  differential)
    {request : Charts.Reciprocal.Disk.PairedParentRequest.Request regular other
      occurrence.compared.entered.cache.parents target minimum}
    (evaluated : Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation request sample otherSample fine) : Prop
      :=
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area ((evaluated.pairs.map Prod.fst).flatten.map
      ConjugateIncrementComparison.conjugateFirst) -
      (Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (fun point => ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval point,
          otherSample.primitive.value.eval point⟩)
        (occurrence.piece.mesh.depth + (request.depth + fine)) occurrence.start occurrence.finish -
      Stokes.edgeArea
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.start⁻¹,
          otherSample.primitive.value.eval occurrence.start⁻¹⟩)
        (ConjugateIncrementComparison.conjugateFirst ⟨sample.primitive.value.eval occurrence.finish⁻¹,
          otherSample.primitive.value.eval occurrence.finish⁻¹⟩))) < target

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.RootContinuation in
/-- The retained conjugated cap-area evaluation meets its requested error after the original stage floor.

The proof uses the exact cached parent chain and owner-root chain, then rewrites the paired primitive area to its
retained reciprocal arc readback. -/
theorem conjugate_arc_error (occurrence :
  Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence regular domains
  differential)
    {request : Charts.Reciprocal.Disk.PairedParentRequest.Request regular other
      occurrence.compared.entered.cache.parents target minimum}
    (evaluated : Charts.Reciprocal.Disk.PairedParentRequest.Request.Evaluation request sample otherSample fine)
    (later : request.index ≤ stage) :
    ConjugateArcError occurrence evaluated := by
  have bound := Charts.Reciprocal.Disk.ConjugateParentArea.Evaluation.full_conjugate_area_error evaluated later
    (by obtain ⟨chain⟩ := occurrence.compared.entered.cache.chain; exact ⟨chain.toDirectPathChain⟩)
    (PreparedCachedParentRoots.ParentCache.rootChain occurrence.compared.entered.cache)
  unfold Charts.Reciprocal.Disk.ConjugateParentArea.Evaluation.FullConjugateAreaError at bound
  rw [conjugate_cap_area_arc occurrence evaluated] at bound
  exact bound

end Purelib.Riemann.Integration.PreparedConjugateParentCapReadback
