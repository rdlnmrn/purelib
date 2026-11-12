module

public import Purelib.Riemann.Readings.UniformPreparedRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContinuedComparison.Entry
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Branches.PreparedPolynomialSheetReadings
import Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RegularFaceInverseModels
import Purelib.Riemann.Normalization.TransportedFaceInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames

/-! # Original parent primitive requests at interior face occurrences

The cached point sample remains the request's original continued-neighborhood
sample. Its actual parent fraction and retained patch give operational root
agreement. The retained face-entry transport then identifies this same root
with the original face polynomial, without a complete grid-edge premise.
-/

public section

namespace Purelib.Riemann.Readings.UniformPreparedRequests.LocalRequest

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.PreparedPolynomialSheetPropagation.InverseRootPolynomial
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.TransportedFaceInverseModels (TransportedCell)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {parent : CenteredEdge curve differential} {target : Rational} {point : Canonical}

/-- Identify the same cached point sample with the original parent's root channel at its actual fraction.

The request's exact neighborhood equation transports the supplied whole
sample to its own retained patch. The original patch point_equivalent_at
gives the named relation inside this erased existence proof. This is not
an extraction of a separately retained direct-query execution cache.
-/
theorem point_original (request : LocalRequest parent count target) (fraction : Rational)
    (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1) (pointEq : parent.edge.point fraction = point)
    (pointInside : request.neighborhood.box.Contains point)
    (sample : ContinuedNeighborhood.Point request.neighborhood point) :
    Nonempty (NamedEquivalent (parent.edge.rootName fraction fractionInside) sample.certificate.value.name) := by
  rcases request with ⟨patch, neighborhood, neighborhoodEq, _requested, _finishInside⟩
  subst neighborhood
  exact ⟨patch.point_equivalent_at count fraction fractionInside pointEq pointInside sample⟩

variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {bank : BranchCellBank curve branches higher}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : RegularFace bank}
variable {models : FaceModels frames face} {faceInside : face.cell.box.Contains point} {inner : Box}

/-- Align the original face polynomial with the actual parent query represented by this same retained request sample.

The actual fraction is related to point by its constructor coordinate law.
The interior-entry acquisition retains the sample's exact Owner. Both
operational relations are derived from those original cached objects.
-/
theorem face_aligned (request : LocalRequest parent count target) (fraction : Rational)
    (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1) (pointEq : parent.edge.point fraction = point)
    (pointInside : request.neighborhood.box.Contains point)
    (sample : ContinuedNeighborhood.Point request.neighborhood point)
    (acquired : Entry.Acquisition models faceInside sample.owner)
    (cell : TransportedCell models.bounds (models.frame.owners acquired.entry.sheet) inner)
    (inside : inner.Contains point) (index : Nat) :
    RootAligned ((Model.overlapRefine cell.model) index) point
      (parent.edge.rootName fraction fractionInside) := by
  obtain ⟨original⟩ := request.point_original fraction fractionInside pointEq pointInside sample
  intro otherCount patch patchInside otherSample roots otherIndex
  exact ContinuedComparison.acquired_aligned acquired cell differential inside index
    patch patchInside otherSample (original.symm.trans roots) otherIndex

/-- The actual original face and parent-request polynomial readings have the derived unflipped nearest sign.

Both retained polynomial refinement indices remain independent. The
comparison uses the SAME old request neighborhood, point sample and face
transport acquisition; no fixed old reading or request radius is changed.
-/
theorem face_nearest (request : LocalRequest parent count target) (fraction : Rational)
    (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1) (pointEq : parent.edge.point fraction = point)
    (pointInside : request.neighborhood.box.Contains point)
    (sample : ContinuedNeighborhood.Point request.neighborhood point)
    (acquired : Entry.Acquisition models faceInside sample.owner)
    (cell : TransportedCell models.bounds (models.frame.owners acquired.entry.sheet) inner)
    (inside : inner.Contains point) (leftIndex rightIndex : Nat) :
    normSq ((cell.model.refine (leftIndex + 2)).value.eval point -
      (request.neighborhood.base.refine rightIndex).value.eval point) ≤
    normSq ((cell.model.refine (leftIndex + 2)).value.eval point +
      (request.neighborhood.base.refine rightIndex).value.eval point) := by
  obtain ⟨original⟩ := request.point_original fraction fractionInside pointEq pointInside sample
  exact PreparedPolynomialSheetReadings.nearest_at_index
    (request.face_aligned fraction fractionInside pointEq pointInside sample acquired cell inside leftIndex)
    inside request.neighborhood pointInside sample
    original rightIndex

/-- The original Entry and retained request sample align the face polynomial with its actual parent query.

No grid-edge placement is needed. The original request patch derives its
point relation, and the actual Entry supplies signed reachability from the
same retained face-frame occurrence.
-/
theorem face_entry_aligned (request : LocalRequest parent count target) (fraction : Rational)
    (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1) (pointEq : parent.edge.point fraction = point)
    (pointInside : request.neighborhood.box.Contains point)
    (sample : ContinuedNeighborhood.Point request.neighborhood point)
    (entry : Entry models point sample.owner)
    (cell : TransportedCell models.bounds (models.frame.owners entry.sheet) inner)
    (inside : inner.Contains point) (index : Nat) :
    RootAligned ((Model.overlapRefine cell.model) index) point
      (parent.edge.rootName fraction fractionInside) := by
  obtain ⟨original⟩ := request.point_original fraction fractionInside pointEq pointInside sample
  intro otherCount patch patchInside otherSample roots otherIndex
  exact ContinuedComparison.entry_aligned entry cell differential inside index
    patch patchInside otherSample (original.symm.trans roots) otherIndex

/-- An actual Entry gives the unflipped comparison of the same face and original request polynomials. -/
theorem face_entry_nearest (request : LocalRequest parent count target) (fraction : Rational)
    (fractionInside : 0 ≤ fraction ∧ fraction ≤ 1) (pointEq : parent.edge.point fraction = point)
    (pointInside : request.neighborhood.box.Contains point)
    (sample : ContinuedNeighborhood.Point request.neighborhood point)
    (entry : Entry models point sample.owner)
    (cell : TransportedCell models.bounds (models.frame.owners entry.sheet) inner)
    (inside : inner.Contains point) (leftIndex rightIndex : Nat) :
    normSq ((cell.model.refine (leftIndex + 2)).value.eval point -
      (request.neighborhood.base.refine rightIndex).value.eval point) ≤
    normSq ((cell.model.refine (leftIndex + 2)).value.eval point +
      (request.neighborhood.base.refine rightIndex).value.eval point) := by
  obtain ⟨original⟩ := request.point_original fraction fractionInside pointEq pointInside sample
  exact PreparedPolynomialSheetReadings.nearest_at_index
    (request.face_entry_aligned fraction fractionInside pointEq pointInside sample entry cell inside leftIndex)
    inside request.neighborhood pointInside sample original rightIndex

end Purelib.Riemann.Readings.UniformPreparedRequests.LocalRequest

end
