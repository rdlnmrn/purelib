module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PointContacts
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Riemann.Paths.PreparedPathPrimitiveCover

open Purelib.Riemann.Readings

public section

/-! Retained paired path entries tied to fixed shared face domains. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FixedDomainContacts

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests (ContactBudget)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
    RegularFace bank}
  {firstModels : FaceModels frames
    firstFace} {lastModels :
    FaceModels frames lastFace}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {owner :
    Owner (curve.polynomial.eval start)} {ambient :
    Purelib.Geometry.Rational.Box}
  {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish} {prepared :
    CoveredTracedPath path owner}
  {differential : Differential genus} {parentSheet : Fin 2}

set_option genInjectivity false in
/-- Two original path entries compared on their supplied fixed face domains.

Both entries consume the same retained covered path and parent cache, preserving actual root ownership and each face's
containment certificate. -/
structure FixedDomainContact (leftEntry : FaceModels.Entry firstModels start owner) (rightEntry : FaceModels.Entry
  lastModels start owner)
    (leftDomain : Periods.PeriodDomain firstModels leftEntry.sheet) (rightDomain : Periods.PeriodDomain lastModels
      rightEntry.sheet)
    (prepared : PreparedClearPathModels.CoveredTracedPath path owner) (leftInside : path.InBox firstFace.cell.box)
    (rightInside : path.InBox lastFace.cell.box) (differential : Differentials.Basic.Differential genus) (parentSheet :
      Fin 2) where
  /-- The shared original parent cache on this exact retained path and differential. -/ cache :
    PreparedClearPathModels.ParentCache prepared differential parentSheet
  /-- The actual entered path on the first retained face domain. -/ left : EnteredPaths.EnteredPath firstModels prepared
    differential parentSheet
  /-- The actual entered path on the second retained face domain. -/ right : EnteredPaths.EnteredPath lastModels
    prepared differential parentSheet
  /-- The first entry is exactly the supplied original entry and domain using the shared retained cache. -/ left_eq :
    left = EnteredPath.ofEntry leftEntry leftDomain prepared leftInside differential parentSheet cache
  /-- The second entry is exactly the supplied original entry and domain using that same retained cache. -/ right_eq :
    right = EnteredPath.ofEntry rightEntry rightDomain prepared rightInside differential parentSheet cache

constructive_injectivity FixedDomainContact

namespace FixedDomainContact

variable {leftEntry : Entry firstModels start
  owner} {rightEntry : Entry lastModels start
  owner}
  {leftDomain : PeriodDomain firstModels leftEntry.sheet}
    {rightDomain : PeriodDomain lastModels
    rightEntry.sheet}
  {leftInside : path.InBox firstFace.cell.box} {rightInside : path.InBox lastFace.cell.box}

/-- Retain both supplied face domains and entered paths while reusing the exact original covered-path parent cache. -/
@[expose] def build (leftEntry : FaceModels.Entry firstModels start owner) (rightEntry : FaceModels.Entry lastModels
  start owner)
    (leftDomain : Periods.PeriodDomain firstModels leftEntry.sheet) (rightDomain : Periods.PeriodDomain lastModels
      rightEntry.sheet)
    (prepared : PreparedClearPathModels.CoveredTracedPath path owner) (leftInside : path.InBox firstFace.cell.box)
    (rightInside : path.InBox lastFace.cell.box) (differential : Differentials.Basic.Differential genus) (parentSheet :
      Fin 2)
    (cache : PreparedClearPathModels.ParentCache prepared differential parentSheet) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.FixedDomainContacts.FixedDomainContact leftEntry rightEntry leftDomain
      rightDomain prepared leftInside rightInside differential parentSheet :=
  ⟨cache, EnteredPath.ofEntry leftEntry leftDomain prepared leftInside differential parentSheet cache,
    EnteredPath.ofEntry rightEntry rightDomain prepared rightInside differential parentSheet cache, rfl, rfl⟩

/-- The two actual retained endpoint-reading differences satisfy the original contact target on their supplied fixed
numerical domains. -/
theorem points_accurate
    (contact : Curves.Hyperelliptic.Meshes.PuncturedGrid.FixedDomainContacts.FixedDomainContact leftEntry rightEntry
      leftDomain rightDomain prepared leftInside rightInside differential parentSheet)
    {target : InverseRootPolynomial.Coordinate} (budget : ContactRequests.ContactBudget contact.left contact.right
      target)
    {index : Nat} (later : budget.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives leftDomain differential index) (rightData :
      PrimitiveData.DomainPrimitives rightDomain differential index)
    {leftCount rightCount : Nat} {leftPoints : Fin leftCount → Data.Gaussian.Basic.Canonical} {rightPoints : Fin
      rightCount → Data.Gaussian.Basic.Canonical}
    (leftReadings : RectangularPointReadings.PointReadings leftData.anchors leftData.offsets leftPoints)
    (rightReadings : RectangularPointReadings.PointReadings rightData.anchors rightData.offsets rightPoints)
    (leftStart leftFinish : Fin leftCount) (rightStart rightFinish : Fin rightCount)
    (leftStart_eq : leftPoints leftStart = start) (leftFinish_eq : leftPoints leftFinish = finish)
    (rightStart_eq : rightPoints rightStart = start) (rightFinish_eq : rightPoints rightFinish = finish) :
    Data.Gaussian.Norm.Basic.normSq ((leftReadings.values leftFinish - leftReadings.values leftStart) -
      (rightReadings.values rightFinish - rightReadings.values rightStart)) < target := by
  rcases contact with ⟨cache, left, right, leftEq, rightEq⟩
  cases leftEq
  cases rightEq
  exact budget.points_accurate later leftData rightData leftReadings rightReadings
    leftStart leftFinish rightStart rightFinish leftStart_eq leftFinish_eq rightStart_eq rightFinish_eq

end FixedDomainContact
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FixedDomainContacts
