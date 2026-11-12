module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.Polynomial.Models
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings.Endpoints
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Polynomial
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Readings.RectangularPrimitiveBoundary

/-! # Ordinary polynomial models on retained endpoint views

The actual shared numerical index raises only its own genuine numerator
accuracy request. The retained two-slot view, primitive/anchor/offset bank,
source model and all physical/query owners remain unchanged.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.PolynomialModelComparison

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.CommonMeshes (FaceMeshBudgets FaceSharedMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (RegularPrimitiveFragment)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.SheetEntries.RegularPrimitiveFragment (SheetEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.BankReadings
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Rectangle.Accuracy
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds UniformRequest)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.UniformRequest (PolynomialModel)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Integration.RectangularSharedPrimitives.SharedPrimitiveValues (atPoint)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus count modelFloor : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {frames : RootFrames base.bank.grid} {source : Differential genus} {axes : PrimitiveAxes base.bank.grid}
variable {parent : CenteredEdge curve source} {domains : FaceDomainBank frames base.faces.regulars}
variable {target tolerance : Rational} {request : LocalRequest parent count target}
variable {cuts : List Rational} {partition : AxisPartition 0 1 cuts} {interval : Interval}
variable {fragment : RegularPrimitiveFragment axes parent partition interval}
variable (assigned : SheetEntry fragment domains request)
variable {differential : OddPowerDifferential curve.polynomial}
variable {sourceBounds : UniformBounds (request.patch.neighborhood count)}
variable {allowance : Rational} {positive : 0 < allowance}
variable {uniform : UniformRequest sourceBounds 0 (differential.numerator.scale differential.scale)
  modelFloor (allowance / 4)}
variable {first last : Canonical} {coordinate : Spatial.Coordinate first last}
variable (model : PolynomialModel (curve := curve) (differential := differential) uniform coordinate positive)
variable {points : List Canonical} {index : Nat}
variable {budgets : FaceMeshBudgets source points tolerance
  (numerator := differential.numerator.scale differential.scale) domains}
variable {numerics : FacePrimitiveBank source index
  (numerator := differential.numerator.scale differential.scale) domains}
variable {shared : FaceSharedMeshes (numerator := differential.numerator.scale differential.scale) budgets numerics}
variable {included : ∀ point ∈ assigned.split.points, point ∈ points}
variable (view : EndpointReadings.Cache assigned shared included)

/-- Raise only the genuine numerical accuracy to its SAME retained shared primitive stage.

The stored mesh-reading certificate supplies the sufficient-index proof.
This operation creates no primitive, mesh, observation, Point or query.
-/
@[expose] def endpointAccuracy : GridPrimitiveAccuracy (EndpointReadings.budget view).globalBounds
    assigned.domain.steps tolerance :=
  FragmentIndex.GridPrimitiveAccuracy.atIndex (EndpointReadings.budget view).accuracy index
    (EndpointReadings.meshValues view).later

/-- The scalar request's index is the actual already retained numerical primitive index. -/
theorem endpointAccuracy_index : (endpointAccuracy assigned view).index = index :=
  FragmentIndex.GridPrimitiveAccuracy.atIndex_index (EndpointReadings.budget view).accuracy index
    (EndpointReadings.meshValues view).later

/-- The existing ordinary model comparison on the actual supplied two-slot numerical caches.

The source model keeps its own independent stage, inverse and primitive
constant. The target is the genuine numerator bank at its stored numerical
index; it never borrows the old Differential-local fragment bound.
-/
abbrev EndpointCache := Cache assigned model (endpointAccuracy assigned view)
  (EndpointReadings.data view).primitives (EndpointReadings.budget view).mesh included
  (EndpointReadings.meshValues view).readings

/-- Execute one original full-numerator model comparison on the GIVEN endpoint-view caches.

Only the per-piece analytic comparisons are new. No source model, shared
primitive bank, lookup, Finish, query, root or geometric owner is rebuilt.
-/
def fromEndpoints (ordinary : differential.denominatorPairs = 0) :
    {value : EndpointCache assigned model view // value = build assigned model (endpointAccuracy assigned view)
      (EndpointReadings.data view).primitives (EndpointReadings.budget view).mesh included
      (EndpointReadings.meshValues view).readings ordinary} :=
  ⟨build assigned model (endpointAccuracy assigned view) (EndpointReadings.data view).primitives
    (EndpointReadings.budget view).mesh included (EndpointReadings.meshValues view).readings ordinary, rfl⟩

variable {assigned model view} (compared : EndpointCache assigned model view)

/-- The comparison value is the difference of the SAME retained literal finish and incoming slots.

Actual lookup membership and the existing ofShared factory give both slot
readbacks. This is a scalar cache identity, not a RootOwner identification.
-/
theorem endpoint_value_eq : compared.comparison.value =
    (EndpointReadings.reading view).values 1 - (EndpointReadings.reading view).values 0 := by
  have slots : (EndpointReadings.reading view).values 1 - (EndpointReadings.reading view).values 0 =
      atPoint (EndpointReadings.meshValues view).readings fragment.located.last -
        atPoint (EndpointReadings.meshValues view).readings fragment.located.first :=
    congrArg₂ (fun last first : Canonical => last - first)
      (EndpointReadings.value_eq_atPoint view (1 : Fin 2))
      (EndpointReadings.value_eq_atPoint view (0 : Fin 2))
  exact compared.comparison.value_eq.trans slots.symm

/-- The actual two-slot numerical increment pays the original comparison's exact retained piece allowance. -/
theorem endpoint_increment_le : normSq
    (((EndpointReadings.reading view).values 1 - (EndpointReadings.reading view).values 0) -
      (model.primitive.primitive.value.eval fragment.located.last -
        model.primitive.primitive.value.eval fragment.located.first)) ≤ compared.comparison.bound :=
  Eq.mp (congrArg (fun value : Canonical => normSq (value -
    (model.primitive.primitive.value.eval fragment.located.last -
      model.primitive.primitive.value.eval fragment.located.first)) ≤ compared.comparison.bound)
        (endpoint_value_eq compared)) (Cache.accurate compared)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.AnalyticComparison.PolynomialModelComparison
