module

import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Request
import Purelib.Curves.Legendre.Periods.Jets.Source.Row
import Purelib.Riemann.Normalization.InverseModelPrimitiveResidual

/-! # Actual scalar and connection primitive rows on one original prepared source

The scalar construction retains the original prepared parent, its cubic
primitive table and both literal moving-vertex Owners. Its old observations
are selected once at the internally computed endpoint allocation. The same
original comparison factory pays their actual increment without a supplied
sample estimate. The readbacks distinguish cubic and inverse primitives,
including the scalar coefficient square and original residual index two.
-/

namespace TestPurelib.Curves.Legendre.PrimitiveRows

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Periods.Jets.Source
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Periods.Fibre.frameCurve frame) basis} {patch : PreparedPatch parent}
variable {count floor : Nat} {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}

/-- Construct both original old scalar observations and the actual retained comparison pair on one prepared parent. -/
private def scalarMoving (prepared : PreparedParent patch count floor covered targets) :
    Σ first : PreparedParent.SourceVertex Row.scalar parent (PreparedParents.Trace.localAccuracy targets),
      Σ last : PreparedParent.TargetVertex Row.scalar parent (PreparedParents.Trace.localAccuracy targets),
        PreparedParent.Comparisons Row.scalar prepared first last
          (PreparedParents.Trace.localAccuracy_allocation targets) :=
  let accuracy := PreparedParents.Trace.localAccuracy targets
  let first := Primitive.Vertex.build (Row.scalar.expression parameter) (PreparedParent.startPoint parent).coordinate
    parent.edge.cached.preparedOwner accuracy
    (Row.defined parameter (PreparedParent.startPoint parent).coordinate Row.scalar parent.edge.cached.preparedOwner)
  let targetOwner := PreparedSheetContinuation.transported parent.edge.segment parent.edge.within
    parent.edge.left parent.edge.owner parent.edge.request parent.edge.small
  let last := Primitive.Vertex.build (Row.scalar.expression parameter) (PreparedParent.finishPoint parent).coordinate
    targetOwner accuracy (Row.defined parameter (PreparedParent.finishPoint parent).coordinate Row.scalar targetOwner)
  let compared := PreparedParent.Comparisons.build Row.scalar prepared first last
    (PreparedParents.Trace.localAccuracy_allocation targets)
  ⟨first, ⟨last, compared⟩⟩

/-- The scalar producer's literal old observations pay the SAME retained original scalar cell integral. -/
example (prepared : PreparedParent patch count floor covered targets) :
    let observed := scalarMoving prepared
    Norm.Basic.normSq ((observed.2.1.value - observed.1.value) -
      prepared.preparation.models.scalar.integralSample) ≤
        8 * targets.endpoint + 4 * prepared.preparation.cell.primitives.bound :=
  PreparedParent.increment_le (scalarMoving prepared).2.2

/-- The scalar endpoint keeps the original divided coefficient's parameter-inverse square. -/
example (prepared : PreparedParent patch count floor covered targets) :
    (Row.scalar.denotation prepared.firstPlan.val).value.im =
      PicardFuchs.Polynomials.picardFuchsPrimitivePolynomial.eval (PreparedParent.startPoint parent).coordinate *
        prepared.firstPlan.val.requests.bounds.parameterInverse ^ 2 :=
  prepared.firstPlan.val.scalar.imaginary_readback prepared.firstPlan.val.requests.bounds

/-- The scalar selector consumes the actual stored original cube, rather than either connection inverse table. -/
example (prepared : PreparedParent patch count floor covered targets) :
    Row.scalar.spatial prepared.preparation.attached.source.models =
      PicardFuchs.Polynomials.picardFuchsPrimitivePolynomial *
        prepared.preparation.attached.source.models.powers.cube :=
  prepared.preparation.attached.source.models.scalarPrimitive_eq

/-- The second connection coordinate retains its distinct original numerator and original inverse-model cache. -/
example (prepared : PreparedParent patch count floor covered targets) :
    (Row.connection 1).spatial prepared.preparation.attached.source.models =
      PicardFuchs.Polynomials.secondPrimitivePolynomial parameter *
        prepared.preparation.attached.source.model.value :=
  prepared.preparation.attached.source.models.primitiveOne_eq

/-- The scalar discrepancy keeps its original cleared residual index two on the SAME source cache. -/
example (prepared : PreparedParent patch count floor covered targets) :
    InverseModelPrimitiveResidual.PrimitiveResidualBounds prepared.cache.root prepared.cache.residual
      prepared.cache.scalarPrimitive 2 := prepared.cache.scalarDelta

end TestPurelib.Curves.Legendre.PrimitiveRows
