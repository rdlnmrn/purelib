module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query.Rooted
public import Purelib.Curves.Legendre.Periods.Jets.Source.Row.Queries
public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Comparison.Reading
public import Purelib.Riemann.Paths.OwnerTracePath.Primitive
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Observations.Channels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Path.Primitive
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.OwnerTraceReadings

/-! # Actual fractional row comparisons on the same retained rooted query

The original source bundle's retained shared reading constructs one actual
row primitive value. The same RootedQuery's stored root attachment derives
agreement with its direct Query Owner. The new endpoint Vertex stays at
that exact Owner, and a finite operational comparison pays both actual
reading errors without selecting a new source model stage.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point (PrimitiveValue)
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
variable {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {fraction : Rational}
variable {inside : 0 ≤ fraction ∧ fraction ≤ 1} {accuracy : AccuracyRequest}
variable (prepared : PreparedParent patch count floor covered targets) (row : Row)
variable (queried : RootedQuery (frame := frame) prepared fraction inside)
variable (vertex : Primitive.Vertex (row.expression parameter)
  (parent.edge.point fraction) queried.direct.owner accuracy)
variable (request : AccuracyRequest)

/-- The same source-query row value and its actual comparison with the original direct-Owner endpoint Vertex. -/
@[expose] def EndpointComparison :=
  Σ source : Row.QueryValue row queried.observed.retained,
    PrimitiveValue.ReadingComparison source.value vertex.observation request

namespace EndpointComparison

/-- Derive both endpoint root and finite reading evidence from the same original rooted source-query answer.

The zero differential's retained root-name readback transports one stored
root comparison to the same shared source sample. It does not execute the
source observer or geometric comparison again. The actual row value uses
that same bundle's retained root and original model-power reading.
-/
def build : EndpointComparison prepared row queried vertex request :=
  let source := Row.QueryValue.build row queried.observed.retained
  have rootName := prepared.preparation.query.channel_root_name frame fraction inside.1 inside.2
    queried.observed queried.observed_eq 0
  let roots := NamedEquivalent.transport rfl rootName (queried.roots.get 0)
  let compared := source.value.compareAt vertex.original vertex.observation (prepared.queryPoint_eq fraction)
    roots.symm request
  ⟨source, compared⟩

variable {prepared row queried vertex request}
variable (compared : EndpointComparison prepared row queried vertex request)

/-- Read the retained row factor, original same-root denotation and actual source-model primitive value. -/
abbrev source := compared.1

/-- Read the original local reading, independent new Vertex reading and actual operational comparison cache. -/
abbrev readings := compared.2

/-- The finite endpoint ceiling uses both the actual source residual and the actual operational comparison payment. -/
abbrev bound := compared.readings.bound

/-- The same retained source table and actual fractional Vertex satisfy the internally computed endpoint payment. -/
theorem error_le : Norm.Basic.normSq
    ((row.spatial prepared.preparation.cell.request.models).eval
      (prepared.preparation.cell.models.coordinate.point fraction) - vertex.value) ≤ compared.bound :=
  compared.readings.source_error_le

end EndpointComparison

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop

end
