module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Integration.RectangularPrimitiveOverlap
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Actual finite point readings on the same retained face primitives

One materialized dependent location vector drives one PointReadings build.
The supplied primitive polynomials, anchors, offsets and old corner bank
are unchanged. The same operations accept every retained numerator and odd
inverse power. Comparisons pay the actual differences of retained values.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry (Located)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Readings
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {face : RegularFace bank} {models : FaceModels frames face}
variable {sheet : Fin 2} {domain : PeriodDomain models sheet} {differential : Differential genus} {index : Nat}
variable {numerator : Polynomial} {pairs : Nat}

section Core

variable (data : DomainPrimitives domain differential index numerator pairs)
variable {count : Nat} (points : Fin count → Canonical) (inside : ∀ position, face.cell.box.Contains (points position))

/-- Retain each actual location once and the complete original PointReadings factory on those same locations.

The finite family retains every original occurrence. An equal coordinate
at another position neither removes a location nor identifies any Point
or root Owner. The original data's primitive constants remain parameters.
-/
abbrev PointBank :=
  Σ locations : {value : DependentVector (fun position => Located domain.geometry (points position)) //
    value = DependentVector.ofFn (fun position => PeriodDomain.locate domain (points position) (inside position))},
  {value : PointReadings data.anchors data.offsets points //
    value = PointReadings.build data.anchors data.offsets points
      (vectorOfFn fun position =>
        let located := locations.val.get position
        (⟨located.column, located.row, points position, located.inside⟩ : OwnedVertex domain.geometry))
      (fun position => by rewrite [vectorOfFn_apply]; rfl)}

/-- Materialize the finite locations and evaluate their actual aligned primitive readings once.

Only the domain's original locate and PointReadings builders execute.
No polynomial, anchor, offset, root, query, Point or Entry is acquired.
-/
def readPoints : data.PointBank points inside :=
  let locations := DependentVector.ofFn fun position => PeriodDomain.locate domain (points position) (inside position)
  let owners := vectorOfFn fun position =>
    let located := locations.get position
    (⟨located.column, located.row, points position, located.inside⟩ : OwnedVertex domain.geometry)
  let readings := PointReadings.build data.anchors data.offsets points owners
    (fun position => by rewrite [vectorOfFn_apply]; rfl)
  ⟨⟨locations, rfl⟩, ⟨readings, rfl⟩⟩

namespace PointBank

variable {data points inside} (observed : data.PointBank points inside)

/-- Read the same materialized original location vector without running point location again. -/
def locations : DependentVector (fun position => Located domain.geometry (points position)) := observed.1.val

/-- Read the whole cached numerical PointReadings, including its original owners and values. -/
def readings : PointReadings data.anchors data.offsets points := observed.2.val

/-- The location vector is the complete original finite factory at these literal point occurrences. -/
theorem locations_eq : observed.locations =
    DependentVector.ofFn (fun position => PeriodDomain.locate domain (points position) (inside position)) :=
  observed.1.property

/-- Each retained location is the original selected cell, including its actual boundary tie. -/
theorem location_eq (position : Fin count) :
    observed.locations.get position = PeriodDomain.locate domain (points position) (inside position) :=
  (congrArg (fun value => value.get position) observed.locations_eq).trans (DependentVector.ofFn_get _ position)

/-- The retained reading bank is the original factory on its SAME cached location vector. -/
theorem readings_eq : observed.readings = PointReadings.build data.anchors data.offsets points
    (vectorOfFn fun position =>
      let located := observed.locations.get position
      (⟨located.column, located.row, points position, located.inside⟩ : OwnedVertex domain.geometry))
    (fun position => by rewrite [vectorOfFn_apply]; rfl) := observed.2.property

/-- Every cached value is the aligned primitive at its actual once-selected domain cell. -/
theorem value_eq (position : Fin count) : observed.readings.values position =
    data.anchors.alignedValue data.offsets (observed.locations.get position).column
      (observed.locations.get position).row (points position) := by
  have owners := congrArg (fun value : PointReadings data.anchors data.offsets points => value.owners)
    observed.readings_eq
  have selected := congrArg (fun value => value position) owners
  change observed.readings.owners position =
    (vectorOfFn fun position =>
      let located := observed.locations.get position
      (⟨located.column, located.row, points position, located.inside⟩ :
        OwnedVertex domain.geometry)) position at selected
  rewrite [vectorOfFn_apply] at selected
  rewrite [observed.readings.value_eq position, selected]
  rfl

/-- Compute the actual oriented difference from another retained reading on the same primitive data. -/
def jump {otherCount : Nat} {otherPoints : Fin otherCount → Canonical}
    (other : PointReadings data.anchors data.offsets otherPoints) (position : Fin count)
    (otherPosition : Fin otherCount) : Canonical :=
  observed.readings.values position - other.values otherPosition

/-- The actual oriented increment changes by its two retained endpoint jumps, without zeroing either constant. -/
theorem increment_eq {otherCount : Nat} {otherPoints : Fin otherCount → Canonical}
    (other : PointReadings data.anchors data.offsets otherPoints) (first last : Fin count)
    (otherFirst otherLast : Fin otherCount) :
    observed.readings.values last - observed.readings.values first =
      (other.values otherLast - other.values otherFirst) +
        observed.jump other last otherLast - observed.jump other first otherFirst := by
  unfold jump
  ring1

end PointBank

end Core

section Accuracy

variable {bounds : PrimitiveOverlapBounds face.clearance numerator}
variable {target : Fraction.Rational} (request : GridPrimitiveAccuracy bounds domain.steps target pairs)
variable {data : DomainPrimitives domain differential request.index numerator pairs}
variable {count : Nat} {points : Fin count → Canonical} {inside : ∀ position, face.cell.box.Contains (points position)}
variable (observed : data.PointBank points inside)

namespace PointBank

/-- Original overlap payments bound one actual same-point jump between two retained reading banks.

Both banks use precisely the same primitive polynomials, anchors and
offsets. Coordinate equality supplies only analytic point incidence; no
root or Point comparison is inferred from it.
-/
theorem jump_le {otherCount : Nat} {otherPoints : Fin otherCount → Canonical}
    (other : PointReadings data.anchors data.offsets otherPoints) (position : Fin count)
    (otherPosition : Fin otherCount) (same : points position = otherPoints otherPosition) :
    Norm.Basic.normSq (observed.jump other position otherPosition) ≤ 4 * request.globalBound := by
  exact RectangularPointReadings.GridPrimitiveAccuracy.point_comparison_bound
    (bank := domain.patch.models) (transitions := (domain.patch.sheets.refine request.index).transitions)
    (gauge := (domain.patch.sheets.refine request.index).gauge) (primitives := data.primitives)
    (anchors := data.anchors) (offsets := data.offsets) request observed.readings other
    domain.patch.cell_refines position otherPosition same

/-- Two actual same-point endpoint jumps pay the complete oriented increment change.

The retained stage and global bound are those of the actual supplied
GridPrimitiveAccuracy. Independent primitive banks require their own
normalization or quantitative comparison and do not satisfy this type.
-/
theorem increment_le {otherCount : Nat} {otherPoints : Fin otherCount → Canonical}
    (other : PointReadings data.anchors data.offsets otherPoints) (first last : Fin count)
    (otherFirst otherLast : Fin otherCount) (firstEq : points first = otherPoints otherFirst)
    (lastEq : points last = otherPoints otherLast) :
    Norm.Basic.normSq ((observed.readings.values last - observed.readings.values first) -
      (other.values otherLast - other.values otherFirst)) ≤ 16 * request.globalBound := by
  exact RectangularPointReadings.GridPrimitiveAccuracy.increment_comparison_bound
    (bank := domain.patch.models) (transitions := (domain.patch.sheets.refine request.index).transitions)
    (gauge := (domain.patch.sheets.refine request.index).gauge) (primitives := data.primitives)
    (anchors := data.anchors) (offsets := data.offsets) request observed.readings other
    domain.patch.cell_refines first last otherFirst otherLast firstEq lastEq

end PointBank

end Accuracy

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives

end
