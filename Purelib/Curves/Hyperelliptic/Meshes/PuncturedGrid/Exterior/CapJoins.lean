module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Topology.PreparedRefinementRootChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates

open Purelib

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Riemann.Integration

open Purelib.Riemann.Topology

@[expose] public section

/-!
# Root joins across the actual shared-surface exterior occurrences

Concatenate the retained reciprocal covers and cap banks. The exact ordered
parent-list equality transports the original period's geometric and root
chains, including its root return. No segment or owner is prepared again.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (ParentCovers)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

/-- Concatenate the actual retained cover or cap-bank spines without rebuilding their original parent data. -/
def append : {first last : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    UniformReciprocalCover.ParentCovers first → UniformReciprocalCover.ParentCovers last →
      UniformReciprocalCover.ParentCovers (first ++ last)
  | _, _, .nil, last => last
  | _, _, .cons patch data cover tail, last => .cons patch data cover
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers.append tail last)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

/-- Concatenate the actual retained cover or cap-bank spines without rebuilding their original parent data. -/
def append : {first last : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)} →
    {firstCovers : UniformReciprocalCover.ParentCovers first} → {lastCovers : UniformReciprocalCover.ParentCovers last}
      →
    ParentJoins.SideBank regular firstCovers → ParentJoins.SideBank regular lastCovers → ParentJoins.SideBank regular
      (firstCovers.append lastCovers)
  | _, _, _, _, .nil, last => last
  | _, _, _, _, .cons head tail, last => .cons head
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.append tail last)

set_option genInjectivity false in
/-- The paired bank transports as one object, preserving every cached cover and cap-owner endpoint through an equality
of parent lists. -/
structure Retained (regular : RegularBounds.Data cap) (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve
  differential)) where
  /-- The original reciprocal covers indexed by this exact retained parent list. -/ covers :
    UniformReciprocalCover.ParentCovers parents
  /-- The actual cap-preparation bank on these same retained covers. -/ bank : ParentJoins.SideBank regular covers

constructive_injectivity Retained

/-- Concatenate the actual retained cover or cap-bank spines without rebuilding their original parent data. -/
def Retained.append {first last : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (left : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Retained regular first) (right :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Retained regular last) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Retained regular (first ++ last) :=
  ⟨left.covers.append right.covers, left.bank.append right.bank⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms (ExteriorProgram)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins (SideBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence SurfacePreparation)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    base.faces.regulars}

/-- Concatenate the existing cap banks in the exact order of the original retained exterior surface occurrences. -/
def SurfaceOccurrence.capSpine (occurrences : List (ExteriorProgram.SurfaceOccurrence regular domains differential)) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Retained regular (occurrences.map (fun item =>
      item.compared.entered.cache.parents)).flatten :=
  match occurrences with
  | [] => ⟨.nil, .nil⟩
  | head :: tail => (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Retained.mk head.cap.path.covers
    head.cap.path.bank).append (capSpine tail)

namespace SurfacePreparation

variable {program : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted
  differential}

set_option genInjectivity false in
/-- Both the interior joins and the final join refer to the original period's parent list. The bank certificate ties
them to the supplied surface occurrences, rather than a second exterior preparation. -/
structure JoinedCap (prepared : ExteriorProgram.SurfacePreparation regular domains program) where
  /-- The retained concatenated original reciprocal-cover and cap-preparation bank. -/ spine :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Retained regular (prepared.occurrences.map (fun
    item => item.compared.entered.cache.parents)).flatten
  /-- The retained spine is exactly the original surface-occurrence concatenation. -/ spine_eq : spine =
    SurfaceOccurrence.capSpine
    prepared.occurrences
  /-- Operational root joins on the actual consecutive parents of the retained cap bank. -/ links : SideBank.Links
    spine.bank
  /-- The actual final-to-initial root join closing the original retained cap bank. -/ closing :
    ClosingJoins.ClosingJoin spine.bank

constructive_injectivity JoinedCap

/-- Transport the original period parent and root chains through their exact occurrence-list equality to construct the
retained interior and closing cap joins. -/
def JoinedCap.build (prepared : ExteriorProgram.SurfacePreparation regular domains program) :
  JoinedCap
  prepared := by
  let spine :=
    SurfaceOccurrence.capSpine
    prepared.occurrences
  have chain := program.cache.chain
  rw [← prepared.parents_eq] at chain
  have roots := program.period.initial.roots
  change PreparedRefinementRootChains.RootChain program.cache.parents _ _ at roots
  rw [← prepared.parents_eq] at roots
  let links := spine.bank.links
    (start := ⟨(Cuts.Ambient curve).anchor, 0⟩)
    (finish := ⟨(Cuts.Ambient curve).anchor, 0⟩) (by obtain ⟨chain⟩ := chain; exact ⟨chain.toDirectPathChain⟩) roots
  let closing := ClosingJoin.build spine.bank roots chain rfl
    (NamedEquivalent.refl _)
  exact ⟨spine, rfl, links, closing⟩

end SurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
