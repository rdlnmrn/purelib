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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves

open Purelib.Geometry

open Purelib

open Purelib.Polynomial

open Purelib.Riemann

@[expose] public section

/-! Assemble complete fragment lists in the retained physical interval order. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IntervalRuns

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {sourceData : UniformReciprocalModels.Data patch count} {cover :
    UniformReciprocalCover.Cover sourceData}
  {covers : Disk.Basis.SourceLocations.BasisSourceCovers parent} {minimum floor index
    depth : Nat}
  {common : Disk.Basis.CommonCover.BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : InverseRootPolynomial.Coordinate}
  {request : Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
    areaAllowance sourceTarget coefficientTarget floor}
  {box : Rational.Box}
  {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}
  {originals : Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Data.Rat.Fraction.Compatibility

variable {acquired :
  Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

variable {faceIndex : Nat} {data : FragmentQueries.RowData occurrence
  faceIndex}

namespace SourceRun
variable {intervals : List Rectangle.Partition.PreparedAxisPartitions.Interval}
  (piece : (interval : Rectangle.Partition.PreparedAxisPartitions.Interval) → interval ∈ intervals →
    OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data)
  (junction : (before after : Rectangle.Partition.PreparedAxisPartitions.Interval) → before ∈ intervals → after ∈
    intervals →
    OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data)

/-- Retain the one original junction to the next physical interval, or an empty list at the terminal interval. -/
public def leadingJunction (before : Rectangle.Partition.PreparedAxisPartitions.Interval) (member : before ∈ intervals)
  :
    {first last : InverseRootPolynomial.Coordinate} → Geometry.Grid.AxisWalks.IncreasingWalk intervals
      first last →
      List (OwnedFragments.OwnedFragment (originals := originals)
        (coefficients := coefficients) data)
  | _, _, .nil _ => []
  | _, _, .cons after present _ => [junction before after member present]

/-- Follow the retained physical interval walk, inserting exactly one owner
junction between adjacent pieces and none after the final piece. -/
def intervalFragments : {first last : InverseRootPolynomial.Coordinate} →
  Geometry.Grid.AxisWalks.IncreasingWalk intervals first last →
    List (OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data)
  | _, _, .nil _ => []
  | _, _, .cons interval member tail => piece interval member ::
      (SourceRun.leadingJunction junction interval
        member tail ++
        SourceRun.intervalFragments tail)

variable (parameter : InverseRootPolynomial.Coordinate → InverseRootPolynomial.Coordinate)
  (pieceFirst : ∀ interval member, (piece interval member).parameters 0 = parameter interval.lower)
  (pieceLast : ∀ interval member,
    (piece interval member).parameters (Fin.last (piece interval member).vertices) = parameter interval.upper)
  (pieceOrdered : ∀ interval member, ∀ edge : Fin (piece interval member).vertices,
    (piece interval member).parameters edge.castSucc ≤ (piece interval member).parameters edge.succ)
  (junctionFirst : ∀ before after bm am, after.lower = before.upper →
    (junction before after bm am).parameters 0 = parameter before.upper)
  (junctionLast : ∀ before after bm am, after.lower = before.upper →
    (junction before after bm am).parameters (Fin.last (junction before after bm am).vertices) = parameter after.lower)
  (junctionOrdered : ∀ before after bm am, after.lower = before.upper →
    ∀ edge : Fin (junction before after bm am).vertices,
      (junction before after bm am).parameters edge.castSucc ≤ (junction before after bm am).parameters edge.succ)

include pieceFirst pieceLast pieceOrdered junctionFirst junctionLast junctionOrdered

/-- Adjacency comes from the retained interval walk; no separate global
fragment-chain certificate is an input. -/
theorem intervalFragments_chain {first last : InverseRootPolynomial.Coordinate} (walk :
  Geometry.Grid.AxisWalks.IncreasingWalk intervals first last) :
    SourceChains.SourceChain
      (SourceRun.intervalFragments piece junction walk)
      (parameter first) (parameter last) := by
  induction walk with
  | nil point => exact .nil _
  | cons interval member tail ih =>
    change SourceChains.SourceChain (piece interval member ::
      (SourceRun.leadingJunction junction interval
        member tail ++ SourceRun.intervalFragments piece
        junction tail))
      (parameter interval.lower) _
    generalize middleEq : id interval.upper = middle at tail ih
    cases tail with
    | nil =>
      change SourceChains.SourceChain [piece interval member]
        (parameter interval.lower) _
      rw [← middleEq]
      change SourceChains.SourceChain [piece interval member]
        (parameter interval.lower) (parameter interval.upper)
      rw [← pieceFirst interval member, ← pieceLast interval member]
      exact .cons _ (pieceOrdered interval member) (.nil _)
    | cons next present rest =>
      change SourceChains.SourceChain (piece interval member ::
        junction interval next member present ::
        SourceRun.intervalFragments piece junction (.cons
          next present rest)) (parameter interval.lower) _
      rw [← pieceFirst interval member]
      apply SourceChains.SourceChain.cons _ (pieceOrdered interval
        member)
      rw [pieceLast interval member, ← junctionFirst interval next member present middleEq.symm]
      apply SourceChains.SourceChain.cons _ (junctionOrdered interval
        next member present middleEq.symm)
      rw [junctionLast interval next member present middleEq.symm]
      exact ih

/-- Build a complete cached run from the physical interval walk and local
piece/junction readbacks. The walk enforces order and includes every piece. -/
def ofIntervalWalk {first last : InverseRootPolynomial.Coordinate} (walk :
  Geometry.Grid.AxisWalks.IncreasingWalk intervals first last)
    (firstEq : parameter first = 0) (lastEq : parameter last = 1) :
      SourceRuns.SourceRun acquired data := by
  have chain := SourceRun.intervalFragments_chain piece
    junction parameter pieceFirst pieceLast pieceOrdered
    junctionFirst junctionLast junctionOrdered walk
  rw [firstEq, lastEq] at chain
  exact SourceChains.SourceRun.ofChain
    (SourceRun.intervalFragments piece junction walk)
    chain

end SourceRun
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IntervalRuns
