module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SharedPointRequests
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
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
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Grid

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

@[expose] public section

/-! Cross-face contact bounds for arbitrary cached boundary points, using
one actual prepared path and its incoming sheet owner. -/
section
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)

namespace Purelib.Riemann.Integration.RectangularSharedPrimitives.SharedPrimitiveValues

/-- Repackage retained mesh readings without evaluating a primitive again. -/
def pointReadings {polynomial
  numerator : InverseRootPolynomial.Polynomial} {columns rows : Nat}
    {geometry : RectangularInverseModels.Geometry columns rows} {models : RectangularInverseModels.Bank polynomial
      geometry} {primitives : RectangularPrimitiveModels.Primitives models numerator}
    {anchors : RectangularPrimitiveGluing.PrimitiveAnchors primitives} {offsets : LinearAlgebra.Grid.Offsets
      anchors.edges}
    {triangles : List (RectangularOwnedTriangulation.ModelTriangle geometry)} {surface :
      RectangularOwnedTriangulation.OwnedTriangulation triangles}
    (readings : RectangularSharedPrimitives.SharedPrimitiveValues anchors offsets surface) :
    RectangularPointReadings.PointReadings anchors offsets surface.mesh.coordinate :=
  ⟨surface.owners, surface.point_eq, readings.values, readings.value_eq⟩

end Purelib.Riemann.Integration.RectangularSharedPrimitives.SharedPrimitiveValues

end

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests (ContactBudget)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget (Comparison)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment (FragmentAccuracy)
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
  (first : EnteredPath firstModels prepared
    differential parentSheet)
  (last : EnteredPath lastModels prepared
    differential parentSheet)

variable {first last} {target : Coordinate}

section

variable {budget : ContactBudget first last
  target} {index : Nat}
  {leftData : DomainPrimitives first.domain
    differential index} {rightData :
    DomainPrimitives last.domain differential
    index}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget.Comparison

/-- Sheet agreement comes from the common actual incoming owner retained by the two entries. Reversal of the second
face's boundary is explicit in the difference of the two forward increments. -/
theorem
  points_accurate
  (comparison : ContactBudget.Comparison budget leftData rightData)
    {leftCount rightCount : Nat} {leftPoints : Fin leftCount → Data.Gaussian.Basic.Canonical} {rightPoints : Fin
      rightCount → Data.Gaussian.Basic.Canonical}
    (leftReadings : RectangularPointReadings.PointReadings leftData.anchors leftData.offsets leftPoints)
    (rightReadings : RectangularPointReadings.PointReadings rightData.anchors rightData.offsets rightPoints)
    (leftStart leftFinish : Fin leftCount) (rightStart rightFinish : Fin rightCount)
    (leftStart_eq : leftPoints leftStart = start) (leftFinish_eq : leftPoints leftFinish = finish)
    (rightStart_eq : rightPoints rightStart = start) (rightFinish_eq : rightPoints rightFinish = finish) :
    Data.Gaussian.Norm.Basic.normSq ((leftReadings.values leftFinish - leftReadings.values leftStart) -
      (rightReadings.values rightFinish - rightReadings.values rightStart)) < target := by
  have left := SharedPointRequests.point_accurate first comparison.left leftData comparison.left_data leftReadings
    leftStart leftFinish leftStart_eq leftFinish_eq
  have right := SharedPointRequests.point_accurate last comparison.right rightData comparison.right_data rightReadings
    rightStart rightFinish rightStart_eq rightFinish_eq
  rw [← comparison.sum_eq] at right
  have equal : (leftReadings.values leftFinish - leftReadings.values leftStart) -
      (rightReadings.values rightFinish - rightReadings.values rightStart) =
      ((leftReadings.values leftFinish - leftReadings.values leftStart) - comparison.left.request.primitiveSum) -
        ((rightReadings.values rightFinish - rightReadings.values rightStart) - comparison.left.request.primitiveSum) :=
          by ring1
  rw [equal]
  apply (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
  have paid := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2)
    (Fraction.Order.Arithmetic.add_lt_add_direct left right)
  apply paid.trans_eq
  rw [budget.tolerance_eq, show 2 * (target / 4 + target / 4) = (target / 4) * 4 by ring1]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget.Comparison

end

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget

/-- The arbitrary point readings reuse the supplied primitive banks. The common prepared request is proof-local and
erased. -/
theorem points_accurate
  (budget : ContactRequests.ContactBudget first last target) {index : Nat} (later : budget.index ≤ index)
    (leftData : PrimitiveData.DomainPrimitives first.domain differential index) (rightData :
      PrimitiveData.DomainPrimitives last.domain differential index)
    {leftCount rightCount : Nat} {leftPoints : Fin leftCount → Data.Gaussian.Basic.Canonical} {rightPoints : Fin
      rightCount → Data.Gaussian.Basic.Canonical}
    (leftReadings : RectangularPointReadings.PointReadings leftData.anchors leftData.offsets leftPoints)
    (rightReadings : RectangularPointReadings.PointReadings rightData.anchors rightData.offsets rightPoints)
    (leftStart leftFinish : Fin leftCount) (rightStart rightFinish : Fin rightCount)
    (leftStart_eq : leftPoints leftStart = start) (leftFinish_eq : leftPoints leftFinish = finish)
    (rightStart_eq : rightPoints rightStart = start) (rightFinish_eq : rightPoints rightFinish = finish) :
    Data.Gaussian.Norm.Basic.normSq ((leftReadings.values leftFinish - leftReadings.values leftStart) -
      (rightReadings.values rightFinish - rightReadings.values rightStart)) < target :=
    Comparison.points_accurate
      (budget.compare later leftData rightData) leftReadings rightReadings leftStart leftFinish rightStart rightFinish
    leftStart_eq leftFinish_eq rightStart_eq rightFinish_eq

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.ContactRequests.ContactBudget

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PointContacts.FaceModels.ContactBudget

/-- Contact accuracy on two independently indexed fine meshes. Both retained readings refer to the supplied face
primitive caches. -/
theorem mesh_accurate (budget : ContactRequests.ContactBudget first last target) {index : Nat} (later : budget.index ≤
  index)
    (leftData : PrimitiveData.DomainPrimitives first.domain differential index) (rightData :
      PrimitiveData.DomainPrimitives last.domain differential index)
    {leftTriangles : List (RectangularOwnedTriangulation.ModelTriangle first.domain.geometry)}
    {rightTriangles : List (RectangularOwnedTriangulation.ModelTriangle last.domain.geometry)}
    {leftSurface : RectangularOwnedTriangulation.OwnedTriangulation leftTriangles}
    {rightSurface : RectangularOwnedTriangulation.OwnedTriangulation rightTriangles}
    (leftReadings : RectangularSharedPrimitives.SharedPrimitiveValues leftData.anchors leftData.offsets leftSurface)
    (rightReadings : RectangularSharedPrimitives.SharedPrimitiveValues rightData.anchors rightData.offsets rightSurface)
    (leftStart leftFinish : Fin leftSurface.mesh.vertices.length) (rightStart rightFinish : Fin
      rightSurface.mesh.vertices.length)
    (leftStart_eq : leftSurface.mesh.coordinate leftStart = start) (leftFinish_eq : leftSurface.mesh.coordinate
      leftFinish = finish)
    (rightStart_eq : rightSurface.mesh.coordinate rightStart = start) (rightFinish_eq : rightSurface.mesh.coordinate
      rightFinish = finish) :
    Data.Gaussian.Norm.Basic.normSq ((leftReadings.values leftFinish - leftReadings.values leftStart) -
      (rightReadings.values rightFinish - rightReadings.values rightStart)) < target :=
  ContactRequests.ContactBudget.points_accurate budget later leftData
    rightData
    leftReadings.pointReadings rightReadings.pointReadings
    leftStart leftFinish rightStart rightFinish leftStart_eq leftFinish_eq rightStart_eq rightFinish_eq

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PointContacts.FaceModels.ContactBudget

end
