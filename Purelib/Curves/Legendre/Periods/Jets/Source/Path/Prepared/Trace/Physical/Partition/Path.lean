module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Partition
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Endpoints.Partition.Path
import Purelib.Data.Vector.Dependent

/-! # One actual six-channel lifted refinement of the retained physical Segment

Each original parent contributes its same cached interval model lists and
genuine whole-path uniform certificates. The original CenteredPathChain
joins those actual refinements in original order. No source, Point, Query,
observation or physical owner is acquired by this geometric assembly.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets (UniformPathCertificates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Vector (DependentVector)
open PreparedParent
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner ((Paths.polynomial parameter).eval start)} {widthRequest : AccuracyRequest}
variable {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets originalPath stage} {accuracy : AccuracyRequest} {row : Row}
variable {retained : Acquisition.Segment (segment := segment) (within := within) (owner := sourceOwner) widthRequest}
variable {parents : Acquisition.Segment.Parents (curve := Fibre.frameCurve frame) basis sheet count retained}
variable {prepared : PreparedParents (frame := frame) (basis := basis) parents.coveredParents floor targets}
variable {allocation : targets.endpoint = 4 * accuracy.tolerance}
variable {observed : Primitive.Spine (row.expression parameter) accuracy retained.traced.trace.get}
variable {gridAmbient : Geometry.Rational.Box}
variable {grid : Polynomial.Geometry.Grid.ClearGrid (Fibre.frameCurve frame).polynomial gridAmbient}
variable {axes : PrimitiveAxes grid}

namespace Partition

variable {compared : Physical.Comparison (frame := frame) (basis := basis) (count := count) (floor := floor)
  (sheet := sheet) row retained parents prepared allocation observed}
variable {splits : PrimitiveSplits axes parents.covered.parents} {comparisonRequest requested : AccuracyRequest}
variable (executed : Partition compared splits comparisonRequest requested)

/-- Actual retained parent refinements indexed by their SAME original centered-parent occurrences. -/
@[expose] def ParentPaths :=
  DependentProduct parents.covered.parents (fun index => (executed.children index).Lifted)

/-- Read one identical retained parent path and all six original uniform certificate caches. -/
abbrev parent (paths : executed.ParentPaths) (index : Fin parents.covered.parents.length) :=
  DependentProduct.get parents.covered.parents paths index

/-- Transport only the whole original model-list index of an actual retained parent certificate. -/
private def parentCertificate (paths : executed.ParentPaths) (index : Fin parents.covered.parents.length)
    (channel : Fin 6) :
    UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      ((executed.children index).cells channel) (executed.parent paths index).path :=
  Eq.mp (congrArg (fun original =>
    UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
      (EndpointPoints.Partition.cells original channel) (executed.parent paths index).path)
    (executed.parent paths index).original_eq)
    ((executed.parent paths index).certificates.get channel)

/-- Construct the six original differential certificates on one cached concatenation of the actual parent paths. -/
def certifyAt (paths : executed.ParentPaths)
    (actual : LiftedPath 2 ⟨start, sheet⟩ ⟨finish, sheet⟩)
    (same : actual = Crop.parentPath parents.covered.chain
      (fun index => (executed.parent paths index).path)) :
    DependentVector (fun channel : Fin 6 =>
      UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (executed.cells channel) actual) :=
  DependentVector.ofFn (fun channel =>
    let raw := Crop.certifyParents channel parents.covered.chain
      (fun index => (executed.parent paths index).path)
      (fun index => (executed.children index).cells channel)
      (fun index => executed.parentCertificate paths index channel)
    let original := Eq.mpr (congrArg (fun cells =>
      UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        cells (Crop.parentPath parents.covered.chain (fun index => (executed.parent paths index).path)))
      (executed.cells_eq channel)) raw
    Eq.mpr (congrArg (fun path =>
      UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (executed.cells channel) path) same) original)

/-- The exact original Segment crop cache, retained parent refinements and six certificates on their actual path. -/
@[expose] def Lifted :=
  Σ original : {value : Partition compared splits comparisonRequest requested // value = executed},
  Σ paths : original.val.ParentPaths,
  Σ actual : {value : LiftedPath 2 ⟨start, sheet⟩ ⟨finish, sheet⟩ //
    value = Crop.parentPath parents.covered.chain (fun index => (original.val.parent paths index).path)},
    DependentVector (fun channel : Fin 6 =>
      UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (original.val.cells channel) actual.val)

/-- Build one retained geometric refinement per original parent and assemble their genuine common six-channel path. -/
def lift : executed.Lifted :=
  let original := executed
  let paths : original.ParentPaths := DependentProduct.ofFn parents.covered.parents
    (fun index => (original.children index).lift)
  let actual := Crop.parentPath parents.covered.chain (fun index => (original.parent paths index).path)
  let certificates := original.certifyAt paths actual rfl
  ⟨⟨original, rfl⟩, paths, ⟨actual, rfl⟩, certificates⟩

namespace Lifted

variable {executed} (lifted : executed.Lifted)

/-- Read the entire original acquired Segment crop cache, including its old comparison and actual splitting spine. -/
abbrev original := lifted.1.val

/-- Read the SAME retained ordered parent refinements and their whole original child caches. -/
abbrev paths := lifted.2.1

/-- Read the actual common ordered geometric path with its retained original sheet transports. -/
abbrev path := lifted.2.2.1.val

/-- Read all six genuine whole-path uniform certificates on that exact retained path. -/
abbrev certificates := lifted.2.2.2

/-- The full original acquired crop cache remains unchanged as runtime data. -/
theorem original_eq : lifted.original = executed := lifted.1.property

/-- The actual path is the original geometric-chain concatenation of the SAME cached parent refinements. -/
theorem path_eq : lifted.path = Crop.parentPath parents.covered.chain
    (fun index => (lifted.original.parent lifted.paths index).path) := lifted.2.2.1.property

end Lifted
end Partition

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical.Comparison

end
