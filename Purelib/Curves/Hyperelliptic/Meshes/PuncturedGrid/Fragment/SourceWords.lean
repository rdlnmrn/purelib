module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.PreparedPathSources
import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.ParentGroups
public import Purelib.Riemann.Paths.PreparedTourSources
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedSwitchedRefinements

open Purelib.Riemann.Paths

open Purelib.Riemann.Readings

open Purelib.Riemann.Topology

@[expose] public section

/-!
# Original paths grouped in the actual rooted fragment words

The original path's segment boundaries are carried through the cached parent
and fragment groupings. Every segment has its exact endpoint coordinates,
actual entry and exit root names, and original source certificates for all
retained pieces. The four tour legs retain these same joins in traversal order.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords (LiftedFragment ParentCoordinates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RootedWords.LiftedFragment (RootedWord ParentGroups)
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Paths.PreparedSegmentSources (SegmentSource)
open Purelib.Riemann.Paths.PreparedPathSources (PathSources)
open Purelib.Riemann.Paths.PreparedTourSources (TourSources)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {source : Differential genus} {axes :
    PrimitiveAxes base.bank.grid}
  {domains : FaceDomainBank frames
    base.faces.regulars} {mesh : LiftedMesh vertices edges base.faces}
  {count : Nat} {target : Rational}

/-- Each original segment owns a connected group of the retained pieces. Empty and stationary groups keep their
root-equivalence evidence. -/
inductive PathSourceWords {ambient : Rational.Box} :
    {start finish : Data.Gaussian.Basic.Canonical} → Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish →
      Gaussian.Name.Basic.Named → Gaussian.Name.Basic.Named →
      List (RootedWords.LiftedFragment axes domains mesh source count target) → Prop
  /-- The stationary empty source path retains the actual endpoint root-name comparison. -/ | nil (point :
    Data.Gaussian.Basic.Canonical) {firstName lastName : Gaussian.Name.Basic.Named}
      (equivalent : Nonempty (Gaussian.Equivalence.NamedEquivalent firstName lastName)) :
      PathSourceWords (.nil point) firstName
        lastName []
  /-- Retain one original source segment's connected rooted fragment block and exact parent provenance before the
    remaining path. -/ | cons {start middle finish : Data.Gaussian.Basic.Canonical} {segment : ClearPath.ClearSegment
    curve.polynomial ambient start middle}
      {tail : Polynomial.Geometry.ClearPath curve.polynomial ambient middle finish} {firstName middleName lastName :
        Gaussian.Name.Basic.Named}
      {block pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
      (word : LiftedFragment.RootedWord block start firstName middle middleName)
      (original : ∀ piece ∈ block, PreparedSegmentSources.SegmentSource segment piece.parent)
      (remaining : PathSourceWords tail
        middleName lastName pieces) :
      PathSourceWords (.cons segment tail)
        firstName lastName (block ++ pieces)

namespace PathSourceWords

/-- Construct the source grouping from the exact retained parent and root spines. Every field is discharged from those
same data. -/
theorem ofParents {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish} {sheet : Fin 2}
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} (original :
      PreparedPathSources.PathSources sheet path parents)
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)} (groups :
      LiftedFragment.ParentGroups parents pieces)
    {firstName lastName : Gaussian.Name.Basic.Named} (roots : PreparedRefinementRootChains.RootChain parents firstName
      lastName) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.PathSourceWords path firstName lastName pieces := by
  induction original generalizing pieces firstName lastName with
  | nil point =>
      cases groups
      cases roots with
      | nil equivalent => exact .nil point ⟨equivalent⟩
  | @cons start middle finish segment tail block parents chain sources remaining ih =>
      obtain ⟨left, right, equal, firstPart, lastPart⟩ := groups.split block
      obtain ⟨middleName, ⟨firstRoots⟩, ⟨lastRoots⟩⟩ := roots.split block
      rw [equal]
      exact .cons
        (firstPart.rooted (ParentCoordinates.ofSwitched
          (SwitchedPathChain.ofDirectPathChain chain)) firstRoots)
        (firstPart.segment_sources sources) (ih lastPart lastRoots)

/-- Forget only the original segment grouping, preserving every actual coordinate and root junction of the concatenated
word. -/
theorem rooted {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish} {firstName lastName :
      Gaussian.Name.Basic.Named}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    (words : Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.PathSourceWords path firstName lastName
      pieces) : LiftedFragment.RootedWord pieces start firstName finish lastName := by
  induction words with
  | nil point equivalent => exact .nil rfl equivalent
  | cons word original remaining ih => exact word.append ih

end PathSourceWords

/-- The four exact source legs, with shared root names at every handoff. -/
inductive TourSourceWords (tour : PreparedBoundaryClosure.ClosedBoundaryDoublePath curve) (firstName lastName :
  Gaussian.Name.Basic.Named) :
    List (RootedWords.LiftedFragment axes domains mesh source count target) → Prop
  /-- Retain the four actual source-tour leg groupings and their shared endpoint root names in traversal order. -/ | mk
    {forward right backward left : List (RootedWords.LiftedFragment axes domains mesh source count target)}
      {afterForward afterRight afterBackward : Gaussian.Name.Basic.Named}
      (forwardWords : PathSourceWords
        tour.joined.data.connector firstName afterForward forward)
      (rightWords : PathSourceWords
        tour.joined.data.rightBoundaryPath afterForward afterRight right)
      (backwardWords : PathSourceWords (ClearPath.reverse
        tour.joined.data.connector) afterRight afterBackward backward)
      (leftWords : PathSourceWords
        tour.joined.data.leftBoundaryPath afterBackward lastName left) :
      TourSourceWords tour firstName lastName
        (((forward ++ right) ++ backward) ++ left)

namespace TourSourceWords

/-- Recover the original four tour-leg fragment groupings from the retained parent and root spines. -/
theorem ofParents {tour : PreparedBoundaryClosure.ClosedBoundaryDoublePath curve}
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve source)} (original :
      PreparedTourSources.TourSources tour parents)
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)} (groups :
      LiftedFragment.ParentGroups parents pieces)
    {firstName lastName : Gaussian.Name.Basic.Named} (roots : PreparedRefinementRootChains.RootChain parents firstName
      lastName) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.TourSourceWords tour firstName lastName pieces := by
  cases original with
  | @mk forward right backward left forwardSource rightSource backwardSource leftSource =>
      obtain ⟨firstThree, last, equal, firstThreePart, lastPart⟩ := groups.split ((forward ++ right) ++ backward)
      obtain ⟨firstTwo, third, firstThreeEq, firstTwoPart, thirdPart⟩ := firstThreePart.split (forward ++ right)
      obtain ⟨first, second, firstTwoEq, firstPart, secondPart⟩ := firstTwoPart.split forward
      obtain ⟨afterBackward, ⟨firstThreeRoots⟩, ⟨lastRoots⟩⟩ := roots.split ((forward ++ right) ++ backward)
      obtain ⟨afterRight, ⟨firstTwoRoots⟩, ⟨thirdRoots⟩⟩ := firstThreeRoots.split (forward ++ right)
      obtain ⟨afterForward, ⟨firstRoots⟩, ⟨secondRoots⟩⟩ := firstTwoRoots.split forward
      rw [equal, firstThreeEq, firstTwoEq]
      exact .mk (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.PathSourceWords.ofParents forwardSource
        firstPart firstRoots)
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.PathSourceWords.ofParents rightSource secondPart
          secondRoots)
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.PathSourceWords.ofParents backwardSource
          thirdPart thirdRoots)
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.PathSourceWords.ofParents leftSource lastPart
          lastRoots)

/-- Concatenate the four original source-leg words while retaining every coordinate and root junction. -/
theorem rooted {tour : PreparedBoundaryClosure.ClosedBoundaryDoublePath curve} {firstName lastName :
  Gaussian.Name.Basic.Named}
    {pieces : List (RootedWords.LiftedFragment axes domains mesh source count target)}
    (words : Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords.TourSourceWords tour firstName lastName
      pieces) :
    LiftedFragment.RootedWord pieces tour.joined.data.leftState.box.anchor firstName
      tour.joined.data.leftState.box.anchor lastName := by
  cases words with
  | mk forward right backward left =>
    exact ((forward.rooted.append right.rooted).append backward.rooted).append left.rooted

end TourSourceWords
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SourceWords
