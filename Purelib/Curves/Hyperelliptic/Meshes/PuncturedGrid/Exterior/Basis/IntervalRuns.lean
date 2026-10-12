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

open Purelib.Curves

open Purelib.Geometry

open Purelib

open Purelib.Polynomial

open Purelib.Riemann

@[expose] public section

/-! Assemble complete fragment lists in the retained physical interval order. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IntervalRuns

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {count : Nat} {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {sourceData : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover sourceData}
  {covers : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent} {minimum floor index
    depth : Nat}
  {common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers minimum}
  {areaAllowance sourceTarget coefficientTarget : Normalization.InverseRootPolynomial.Coordinate}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common
    areaAllowance sourceTarget coefficientTarget floor}
  {box : Rational.Box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

open Purelib.Data.Rat.Fraction.Compatibility

variable {acquired :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.Acquisition request
  polynomials originals cells coefficients depth}

variable {faceIndex : Nat} {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData occurrence
  faceIndex}

namespace SourceRun
variable {intervals : List Rectangle.Partition.PreparedAxisPartitions.Interval}
  (piece : (interval : Rectangle.Partition.PreparedAxisPartitions.Interval) → interval ∈ intervals →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data)
  (junction : (before after : Rectangle.Partition.PreparedAxisPartitions.Interval) → before ∈ intervals → after ∈
    intervals →
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data)

/-- Retain the one original junction to the next physical interval, or an empty list at the terminal interval. -/
public def leadingJunction (before : Rectangle.Partition.PreparedAxisPartitions.Interval) (member : before ∈ intervals)
  :
    {first last : Normalization.InverseRootPolynomial.Coordinate} → Geometry.Grid.AxisWalks.IncreasingWalk intervals
      first last →
      List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
        (coefficients := coefficients) data)
  | _, _, .nil _ => []
  | _, _, .cons after present _ => [junction before after member present]

/-- Follow the retained physical interval walk, inserting exactly one owner
junction between adjacent pieces and none after the final piece. -/
def intervalFragments : {first last : Normalization.InverseRootPolynomial.Coordinate} →
  Geometry.Grid.AxisWalks.IncreasingWalk intervals first last →
    List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OwnedFragments.OwnedFragment (originals := originals)
      (coefficients := coefficients) data)
  | _, _, .nil _ => []
  | _, _, .cons interval member tail => piece interval member ::
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IntervalRuns.SourceRun.leadingJunction junction interval
        member tail ++
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IntervalRuns.SourceRun.intervalFragments tail)

variable (parameter : Normalization.InverseRootPolynomial.Coordinate → Normalization.InverseRootPolynomial.Coordinate)
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
theorem intervalFragments_chain {first last : Normalization.InverseRootPolynomial.Coordinate} (walk :
  Geometry.Grid.AxisWalks.IncreasingWalk intervals first last) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IntervalRuns.SourceRun.intervalFragments piece junction walk)
      (parameter first) (parameter last) := by
  induction walk with
  | nil point => exact .nil _
  | cons interval member tail ih =>
    change Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain (piece interval member ::
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IntervalRuns.SourceRun.leadingJunction junction interval
        member tail ++ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IntervalRuns.SourceRun.intervalFragments piece
        junction tail))
      (parameter interval.lower) _
    generalize middleEq : id interval.upper = middle at tail ih
    cases tail with
    | nil =>
      change Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain [piece interval member]
        (parameter interval.lower) _
      rw [← middleEq]
      change Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain [piece interval member]
        (parameter interval.lower) (parameter interval.upper)
      rw [← pieceFirst interval member, ← pieceLast interval member]
      exact .cons _ (pieceOrdered interval member) (.nil _)
    | cons next present rest =>
      change Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain (piece interval member ::
        junction interval next member present ::
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IntervalRuns.SourceRun.intervalFragments piece junction (.cons
          next present rest)) (parameter interval.lower) _
      rw [← pieceFirst interval member]
      apply Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain.cons _ (pieceOrdered interval
        member)
      rw [pieceLast interval member, ← junctionFirst interval next member present middleEq.symm]
      apply Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain.cons _ (junctionOrdered interval
        next member present middleEq.symm)
      rw [junctionLast interval next member present middleEq.symm]
      exact ih

/-- Build a complete cached run from the physical interval walk and local
piece/junction readbacks. The walk enforces order and includes every piece. -/
def ofIntervalWalk {first last : Normalization.InverseRootPolynomial.Coordinate} (walk :
  Geometry.Grid.AxisWalks.IncreasingWalk intervals first last)
    (firstEq : parameter first = 0) (lastEq : parameter last = 1) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns.SourceRun acquired data := by
  have chain := Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IntervalRuns.SourceRun.intervalFragments_chain piece
    junction parameter pieceFirst pieceLast pieceOrdered
    junctionFirst junctionLast junctionOrdered walk
  rw [firstEq, lastEq] at chain
  exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceRun.ofChain
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IntervalRuns.SourceRun.intervalFragments piece junction walk)
    chain

end SourceRun
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.IntervalRuns
