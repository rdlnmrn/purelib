module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains

@[expose] public section

/-! Construct complete source runs from adjacent physical fragments. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest (BasisPreparedCommonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations
  (PrimitiveBank)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries (RowData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments (OwnedFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentBlocks (fragmentBlockError
  owned_fragments_area_bound)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnerRequest (ownedValue)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains (SourceChain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns (SourceRun)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.JoinedFragments (interleaveFragments)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : PreparedPatch parent}
  {sourceData : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Cover sourceData}
  {covers : BasisSourceCovers parent} {minimum
    floor index depth : Nat}
  {common : BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : Coordinate}
  {request : BasisPreparedCommonRequest
    regular common areaAllowance sourceTarget coefficientTarget floor}
  {box : Purelib.Geometry.Rational.Box}
  {polynomials : RegularBasisPolynomials cap
    index box}
  {originals :
    PrimitiveBank
    covers index}
  {cells : BasisSourceLocations.SampleBank
    covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr sumFin_mul_right sumFin_zero)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {acquired :
  BasisPreparedCommonRequest.Acquisition
  request polynomials originals cells coefficients depth}

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open Purelib.Integration.Path.ConjugateIncrementComparison (conjugateFirst conjugateFirst_error)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea (parameterStep)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks (maximum maximum_nonnegative
  le_maximum)

variable {faceIndex : Nat} {data :
  RowData occurrence faceIndex}

/-- The physical piece/junction order also determines the source chain. Only scalar endpoint equalities and the retained
parameter order are needed. -/
theorem interleave_source_chain {count : Nat}
    (pieces : Fin (count + 1) → OwnedFragments.OwnedFragment (originals := originals) (coefficients := coefficients)
      data)
    (junctions : Fin count → OwnedFragments.OwnedFragment (originals := originals) (coefficients := coefficients) data)
    (pieceOrdered : ∀ position, ∀ edge : Fin (pieces position).vertices,
      (pieces position).parameters edge.castSucc ≤ (pieces position).parameters edge.succ)
    (junctionOrdered : ∀ position, ∀ edge : Fin (junctions position).vertices,
      (junctions position).parameters edge.castSucc ≤ (junctions position).parameters edge.succ)
    (pieceLast : ∀ position : Fin count,
      (pieces position.castSucc).parameters (Fin.last (pieces position.castSucc).vertices) = (junctions
        position).parameters 0)
    (junctionLast : ∀ position : Fin count,
      (junctions position).parameters (Fin.last (junctions position).vertices) = (pieces position.succ).parameters 0) :
    SourceChains.SourceChain (JoinedFragments.interleaveFragments pieces junctions) ((pieces 0).parameters 0)
      ((pieces (Fin.last count)).parameters (Fin.last (pieces (Fin.last count)).vertices)) := by
  induction count with
  | zero => exact .cons (pieces 0) (pieceOrdered 0) (.nil _)
  | succ count ih =>
      have rest := ih (fun position => pieces position.succ) (fun position => junctions position.succ)
        (fun position => pieceOrdered position.succ) (fun position => junctionOrdered position.succ)
        (fun position => pieceLast position.succ) (fun position => junctionLast position.succ)
      have junctionTail : SourceChains.SourceChain
          (JoinedFragments.interleaveFragments (fun position => pieces position.succ) (fun position => junctions
            position.succ))
          ((junctions 0).parameters (Fin.last (junctions 0).vertices))
          ((pieces (Fin.last (count + 1))).parameters (Fin.last (pieces (Fin.last (count + 1))).vertices)) := by
        rw [junctionLast 0]
        exact rest
      have pieceTail : SourceChains.SourceChain
          (junctions 0 :: JoinedFragments.interleaveFragments (fun position => pieces position.succ) (fun position =>
            junctions position.succ))
          ((pieces 0).parameters (Fin.last (pieces 0).vertices))
          ((pieces (Fin.last (count + 1))).parameters (Fin.last (pieces (Fin.last (count + 1))).vertices)) := by
        have equal := pieceLast 0
        change (pieces 0).parameters (Fin.last (pieces 0).vertices) =
          (junctions 0).parameters 0 at equal
        rw [equal]
        exact .cons (junctions 0) (junctionOrdered 0) junctionTail
      exact .cons (pieces 0) (pieceOrdered 0) pieceTail

/-- Construct the complete run from its physical pieces and owner junctions. The source path and width are derived once
from their geometric adjacency. -/
def SourceRun.ofJoined {count : Nat}
    (pieces : Fin (count + 1) → OwnedFragments.OwnedFragment (originals := originals) (coefficients := coefficients)
      data)
    (junctions : Fin count → OwnedFragments.OwnedFragment (originals := originals) (coefficients := coefficients) data)
    (pieceOrdered : ∀ position, ∀ edge : Fin (pieces position).vertices,
      (pieces position).parameters edge.castSucc ≤ (pieces position).parameters edge.succ)
    (junctionOrdered : ∀ position, ∀ edge : Fin (junctions position).vertices,
      (junctions position).parameters edge.castSucc ≤ (junctions position).parameters edge.succ)
    (pieceLast : ∀ position : Fin count,
      (pieces position.castSucc).parameters (Fin.last (pieces position.castSucc).vertices) = (junctions
        position).parameters 0)
    (junctionLast : ∀ position : Fin count,
      (junctions position).parameters (Fin.last (junctions position).vertices) = (pieces position.succ).parameters 0)
    (first : (pieces 0).parameters 0 = 0)
    (last : (pieces (Fin.last count)).parameters (Fin.last (pieces (Fin.last count)).vertices) = 1) :
    SourceRuns.SourceRun acquired data := by
  have chain := interleave_source_chain pieces
    junctions pieceOrdered junctionOrdered pieceLast junctionLast
  rw [first, last] at chain
  exact SourceRun.ofChain (JoinedFragments.interleaveFragments pieces junctions) chain

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
