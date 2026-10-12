module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Branches.NewtonRequestedCutComparison
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonBoundaryDepthRefinement

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalExteriorLapRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing
public import Purelib.Riemann.Normalization.NewtonOriginalDeterminantDecay
import Purelib.Riemann.Normalization.NewtonCanonicalDeterminantRequest
import Purelib.Riemann.Branches.NewtonRequestedCutBudget
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.RootContinuation.NewtonRequestedExteriorDepth
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedBoundary
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceCuts
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.FineAreaRequests
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Normalization.NewtonResplitDeterminantBound
import Purelib.Curves.Hyperelliptic.Meshes.Newton.TerminalExteriorBudget
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineAreaRequests
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

public section

/-! Acquire the actual numerical and annular readings that certify arbitrary
requested decay of the original corrected period-model determinant. -/
namespace Purelib.Riemann.Normalization.NewtonOriginalDeterminantRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.RootContinuation.NewtonRequestedBoundary (BoundaryPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedCutPairing (CutPairingRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearRequests (BilinearRequest)
open Purelib.Riemann.Normalization.NewtonCanonicalDeterminantRequest (CanonicalDeterminantRequest)
open Purelib.Riemann.Normalization.NewtonResplitDeterminantBound (ResplitExteriorPreparation)
open Purelib.Riemann.Normalization.NewtonOriginalDeterminantDecay (OriginalDeterminantComparison
  OriginalDeterminantDecay)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
  {preparation : NewtonPreparation base.bank.toBranchCellBank}
  {error radius : Rational} {first second : Fin genus} {minimum : Nat}

open Purelib.Data.Rat in
/-- The original Newton boundary request with determinant error divided by 1634. -/
@[expose] def OriginalRequestedBoundary (preparation : NewtonPreparation base.bank.toBranchCellBank)
    (first second : Fin genus) (error radius : Fraction.Rational) (minimum : Nat) :=
  BoundaryPreparation preparation first second (error / 1634) radius minimum

open Purelib.Riemann.RootContinuation in
/-- The exact identity between the retained refined boundary and the original exterior-depth refinement. -/
@[expose] def OriginalRefinementEq (boundary : OriginalRequestedBoundary preparation first second error radius minimum)
    (exterior : ResplitExteriorPreparation paired boundary)
    (refined : OriginalRequestedBoundary preparation first second error radius minimum) : Prop :=
  refined = NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth boundary exterior.source.depth

section
open Purelib.Curves.Hyperelliptic
/-- The original canonical determinant comparison at the retained refined boundary. -/
@[expose] def OriginalRequestedComparison (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (refined : OriginalRequestedBoundary preparation first second error radius minimum) :=
  CanonicalDeterminantRequest prepared refined (error / 1634) minimum

/-- The actual numerical cache indexed by the retained refined domains and threshold. -/
@[expose] def OriginalRequestedNumerics (refined : OriginalRequestedBoundary preparation first second error radius
  minimum)
    (threshold : Nat) := Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics refined.domains threshold

/-- The original cut readings indexed by their actual retained numerical cache. -/
@[expose] def OriginalRequestedReadings (refined : OriginalRequestedBoundary preparation first second error radius
  minimum)
    {threshold : Nat} (cache : OriginalRequestedNumerics refined threshold) :=
  Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings refined.paid.cut cache

end

open Purelib.Riemann.Branches in
/-- The original annular comparisons indexed by the retained cut readings. -/
@[expose] def OriginalRequestedAnnuli (refined : OriginalRequestedBoundary preparation first second error radius
  minimum)
    {threshold : Nat} {cache : OriginalRequestedNumerics refined threshold}
    (readings : OriginalRequestedReadings refined cache) :=
  NewtonRequestedCutComparison.CutAnnularReadings refined.comparison readings

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The original period determinant is below the requested error at every stage past the retained threshold. -/
@[expose] def OriginalDeterminantSmall (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (first
  second : Fin genus)
    (error : Fraction.Rational) (threshold : Nat) : Prop :=
  ∀ stage, threshold ≤ stage → Data.Gaussian.Norm.Basic.normSq
    (Meshes.PuncturedGrid.Paired.BilinearRequests.BilinearRequest.determinant prepared first second stage) < error

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- A complete original determinant request with retained geometric and numerical preparations.

The original boundary and exterior, exact refined identity, canonical comparison, cache, cut readings and annuli jointly
certify the later-stage determinant bound. -/
structure OriginalDeterminantRequest (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (preparation : NewtonPreparation base.bank.toBranchCellBank) (first second : Fin genus)
    (error radius : Fraction.Rational) (minimum : Nat) where
  /-- The original boundary prepared at the divided determinant error. -/ boundary : OriginalRequestedBoundary
    preparation first second error radius minimum
  /-- The retained original resplit-exterior preparation for that boundary. -/ exterior : ResplitExteriorPreparation
    paired boundary
  /-- The cached boundary at the original exterior's required depth. -/ refined : OriginalRequestedBoundary preparation
    first second error radius minimum
  /-- The refined cache is exactly the original exterior-depth refinement. -/ refined_eq : OriginalRefinementEq boundary
    exterior refined
  /-- The retained canonical determinant request for the exact refined boundary. -/ comparison :
    OriginalRequestedComparison prepared refined
  /-- The selected common determinant comparison threshold. -/ threshold : Nat
  /-- The threshold respects the original requested minimum. -/ minimum_le : minimum ≤ threshold
  /-- The actual original numerical cache at the retained threshold. -/ cache : OriginalRequestedNumerics refined
    threshold
  /-- The cut readings built from that exact retained numerical cache. -/ readings : OriginalRequestedReadings refined
    cache
  /-- The actual annular comparisons for those original readings. -/ annuli : OriginalRequestedAnnuli refined readings
  /-- Every later original period stage satisfies the requested determinant error. -/ accurate :
    OriginalDeterminantSmall prepared first second error threshold

constructive_injectivity OriginalDeterminantRequest

namespace OriginalDeterminantRequest

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Normalization in
open Purelib.Riemann.Periods in
open Purelib.Riemann.RootContinuation in
/-- Retain an original exterior preparation and construct its exact determinant request cache.

The exterior depth fixes the refined boundary; the selected threshold builds the actual standard-differential cache, cut
readings and annular comparisons, preserving the factor-1634 payment. -/
@[expose] def ofExterior (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (boundary : OriginalRequestedBoundary preparation first second error radius minimum)
    (exterior : ResplitExteriorPreparation paired boundary) :
    OriginalDeterminantRequest prepared preparation first second error radius minimum := by
  let refined := NewtonBoundaryDepthRefinement.BoundaryPreparation.atDepth boundary exterior.source.depth
  let request := NewtonOriginalDeterminantDecay.ResplitExteriorPreparation.originalDeterminantRequest exterior prepared
    minimum
  let cache := Vector.DependentVector.ofFn (fun differential =>
    Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank.build (PeriodMatrix.standardDifferential differential)
      request.2.val refined.domains)
  let readings := Meshes.PuncturedGrid.RequestedCutPairing.CutPairingRequest.Readings.build refined.paid.cut cache
  let annuli := NewtonRequestedCutComparison.CutAnnularReadings.build refined.comparison readings
  refine ⟨boundary, exterior, refined, rfl, request.1, request.2.val, request.2.property.1,
    cache, readings, annuli, ?_⟩
  intro stage later
  have accurate := request.2.property.2 request.2.val cache readings annuli le_rfl stage later
  have divisorPositive : (0 : Fraction.Rational) < 1634 := Fraction.Cast.Order.natCast_pos_direct (n := 1634) (by
    decide)
  exact accurate.trans_eq ((Fraction.Field.mul_comm _ _).trans (Fraction.Field.div_mul_cancel_of_ne _ _ (ne_of_gt
    divisorPositive)))

open Purelib.Curves.Hyperelliptic in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
open Purelib.Riemann.Normalization in
open Purelib.Riemann.Periods in
open Purelib.Riemann.RootContinuation in

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
/-- Prepare the original determinant request from positive error and radius targets.

The original Newton preparation and differential pair determine the divided boundary budget and exterior components,
then retain their exact refinement and numerical caches. -/
@[expose] def build (prepared : Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (preparation :
  NewtonPreparation base.bank.toBranchCellBank)
    (first second : Fin genus) (error radius : Fraction.Rational)
    (positive : 0 < error) (radiusPositive : 0 < radius) (minimum : Nat) :
    OriginalDeterminantRequest prepared preparation first second error radius minimum :=
  let divisorPositive : (0 : Fraction.Rational) < 1634 := Fraction.Cast.Order.natCast_pos_direct (n := 1634) (by decide)
  let boundary := BoundaryPreparation.build preparation first second (error / 1634) radius
    (Fraction.Order.Field.div_pos_direct positive divisorPositive) radiusPositive minimum
  let exterior := ResplitExteriorPreparation.build paired boundary
    (Meshes.Newton.OriginalExteriorLapRequest.build_exterior_components preparation first second (error / 1634) radius
      (Fraction.Order.Field.div_pos_direct positive divisorPositive) radiusPositive minimum)
  ofExterior prepared boundary exterior

end OriginalDeterminantRequest
end Purelib.Riemann.Normalization.NewtonOriginalDeterminantRequest
