module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Integration.PreparedQueryNegation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Data.Rat

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements

open Purelib.Riemann.Integration.PreparedQueryNegation

open Purelib.Riemann.Integration.PreparedQueryNegation.PreparedFaceTracePrefixes

open Purelib.Riemann.Paths

open Purelib.Riemann.RootContinuation

@[expose] public section

/-!
# Opposite prepared coefficient queries inside an actual grid face

Both paths retain their own subdivisions and query parameters. Their source
owners are the two actual occurrences in the shared face frame. Membership
in the retained parent lists and containment provide the prefix certificates;
the caller supplies no root-sign, winding, or analytic comparison premise.
-/

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank (referenceAt)
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.QueryNegation

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedQueryNegation.PreparedFaceTracePrefixes (QueryNegation)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (traced_parent_reached)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {sheet : Fin 2} {firstAmbient secondAmbient : Box} {firstFinish secondFinish
    : Purelib.Data.Gaussian.Basic.Canonical}
  {firstPath : Polynomial.Geometry.ClearPath curve.polynomial firstAmbient face.cell.box.anchor
    firstFinish}
  {secondPath : Polynomial.Geometry.ClearPath curve.polynomial secondAmbient face.cell.box.anchor
    secondFinish}

/-- The comparison uses the original prepared parents, including nonzero interior query fractions and independent
subdivision depths. The endpoint frame may be the existing grid frame or a separately cached query frame. -/
def queryNegation (first : PreparedPathTrace.TracedPath firstPath (models.frame.owners sheet))
    (second : PreparedPathTrace.TracedPath secondPath (models.frame.owners (BranchCutLifts.otherSheet sheet)))
    (firstInside : firstPath.InBox face.cell.box) (secondInside : secondPath.InBox face.cell.box)
    (differential : Differentials.Basic.Differential genus) (leftSheet rightSheet : Fin 2)
    (leftParent rightParent : PreparedSubdivisionModelCore.CenteredEdge curve differential)
    (leftMember : leftParent ∈ (CenteredPathChain.ofPreparedPath curve differential leftSheet first.prepared).parents)
    (rightMember : rightParent ∈ (CenteredPathChain.ofPreparedPath curve differential rightSheet
      second.prepared).parents)
    (left right : Fraction.Rational) (leftInside : 0 ≤ left ∧ left ≤ 1) (rightInside : 0 ≤ right ∧ right ≤ 1)
    (point_eq : leftParent.edge.point left = rightParent.edge.point right)
    (frame : RootOwnerFrames.OwnerFrame (curve.polynomial.eval (leftParent.edge.point left))) :
    PreparedFaceTracePrefixes.QueryNegation leftParent rightParent left right leftInside rightInside point_eq frame :=
  ParentReached.queryNegation
    (PreparedFaceTracePrefixes.traced_parent_reached face.clearance differential leftSheet first firstInside leftParent
      leftMember)
    (PreparedFaceTracePrefixes.traced_parent_reached face.clearance differential rightSheet second secondInside
      rightParent rightMember)
    face.clearance
    (BranchCellBank.referenceAt bank _ (face.cell.anchor_mem face.member)).toLoop
    face.cell.box.contains_anchor
    left right leftInside rightInside point_eq frame

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.QueryNegation
