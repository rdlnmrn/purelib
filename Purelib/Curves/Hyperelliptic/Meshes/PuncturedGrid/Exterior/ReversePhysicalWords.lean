module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.SourceIntervals
import Purelib.Integration.Path.JoinedTrace
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedReverseFamily
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseParentHandoffs
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.JoinedFragmentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockPoints
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Polynomial.Rectangle.JoinedSampleBlocks
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockJunctions

public section

/-! Assemble exhaustive source words from the actual physical coverage. -/
section

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseChains
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedReverseOrder
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedFragmentFamily
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReverseParentHandoffs
open Purelib.Geometry.Rectangle
open Purelib.Geometry.Rectangle.Partition

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences (PairedSourcePlan)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  (ParentEvaluation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues (FirstData SecondData)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockParameters
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceBlockJunctions.SourceBlockParameters
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.IndexedSourceSplits (indexedEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.FragmentFamilies (JoinedFragmentFamily)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence)
open
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility
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
    regular domains differential} {target : Coordinate} {minimum
    stage fine index : Nat}
  {box otherBox : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : PairedSourcePlan occurrence
    other target minimum}

variable {evaluated :
  ParentEvaluation
  plan sample otherSample fine}
  {data : FirstData occurrence index}
    {otherData : SecondData occurrence
    other index}

open Purelib.Geometry.Rectangle.SourceIntervals (axisCoordinate)
variable {Vertex : Type} {count : Nat} {values : Vertex → Purelib.Topology.Polygon.Stokes.PrimitivePoint}
  {traces : Fin (count + 1) → Purelib.Integration.Path.JoinedTrace.VertexTrace Vertex}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReversePhysicalWords.JoinedFragmentFamily

/-- Physical coverage and cached parameter readbacks supply both complete parameter chains and exhaustive parent order
for the existing fragment family. -/
theorem indexedItems_reverse_physical_words
    (family : FragmentFamilies.JoinedFragmentFamily (evaluated := evaluated) (data := data) (otherData := otherData)
      values traces)
    {vertical : Bool}
    (physical : Fin (count + 1) → PreparedAxisPartitions.Interval)
    (blocks : (i : Fin (count + 1)) → SourceBlockParameters evaluated vertical false (physical i))
    (axis : vertical = occurrence.sourceVertical)
    (backward : occurrence.sourceForward = false)
    (pieceOwners : ∀ i, (family.pieces.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (blocks
      i).index)
    (junctionOwners : ∀ i, (family.junctions.get i).fragment.entry = IndexedSourceSplits.indexedEntry evaluated (blocks
      i.castSucc).index)
    (starts : ∀ i, JoinedFragmentFamily.pieceStart family i = (blocks i).firstParameter)
    (finishes : ∀ i, JoinedFragmentFamily.pieceFinish family i = (blocks i).lastParameter)
    (junctions : ∀ i vertex, (family.junctions.get i).fragment.parameters vertex = (blocks i.castSucc).lastParameter)
    (consecutive : ∀ i : Fin count, (physical i.succ).lower = (physical i.castSucc).upper)
    (start : (physical 0).lower = SourceIntervals.axisCoordinate vertical occurrence.finish)
    (finish : (physical (Fin.last count)).upper = SourceIntervals.axisCoordinate vertical occurrence.start) :
    let items := JoinedFragmentFamily.indexedItems family (fun i => (blocks i).index) pieceOwners junctionOwners
    IndexedOwnedFragment.ReverseWord items ∧ IndexedOwnedFragment.ReverseParentWord items := by
  cases axis
  have initial := SourceBlockParameters.reverse_at_physical_start (blocks 0) backward start
  have final := SourceBlockParameters.reverse_at_physical_finish (blocks (Fin.last count)) backward finish
  have steps (i : Fin count) := SourceBlockParameters.reverse_occurrence_parent_handoff (blocks i.castSucc)
    (blocks i.succ) backward (consecutive i)
  constructor
  · apply JoinedFragmentFamily.indexedItems_reverse_word family _ pieceOwners junctionOwners
      ((starts 0).trans initial.2) ((finishes (Fin.last count)).trans final.2)
    · intro i vertex
      exact (junctions i vertex).trans (finishes i.castSucc).symm
    · intro i same
      exact (finishes i.castSucc).trans
        (((blocks i.castSucc).same_parent_parameters (blocks i.succ) same.symm (consecutive i)).symm.trans
          (starts i.succ).symm)
    · intro i different
      rcases steps i with same | next
      · exact (different same.1.symm).elim
      · exact ⟨(finishes i.castSucc).trans next.2.1, (starts i.succ).trans next.2.2⟩
  · apply JoinedFragmentFamily.indexedItems_reverse_parent_word family _ pieceOwners junctionOwners initial.1 _ final.1
    intro i
    rcases steps i with same | next
    · exact Or.inl (congrArg Fin.val same.1)
    · exact Or.inr next.1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ReversePhysicalWords.JoinedFragmentFamily

end
