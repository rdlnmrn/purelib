module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Telescope
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain
public import Purelib.Curves.Legendre.Periods.Jets.Source.Row.Path
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # The same paid affine source integrals on their original ordered source path

The supplied center/cover/preparation family builds the existing source
Path by reading its complete cached cells. The original cell construction
equations identify every selected model sample in order. The same actual
trace comparison then pays that path's relation integral with no new source,
observer, root or trace. Curved-chart integral correspondence is separate.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Subdivision)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath.OwnerPath
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage} {count floor : Nat} {sheet : Fin 2}
variable {ambient : Geometry.Rational.Box} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) ambient start finish} {within : segment.WithinAmbient}

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Sources

/-- Join the SAME retained source cells on their original center family's actual moving affine chain.

Only the existing ordered Path constructors are assembled. Every cell,
covering patch, endpoint request and preparation is the supplied original
cache; the full paid stationary/moving OwnerPath remains a separate owner.
-/
@[expose] def path {current : Endpoint}
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    {subdivision : Subdivision segment within current owner}
    (sources : Sources (frame := frame) (basis := basis) (targets := targets)
      (count := count) (floor := floor) (sheet := sheet) subdivision) :
    Path parameter (CenteredPathChain.ofCenteredSubdivision (Fibre.frameCurve frame) basis sheet
      subdivision sources.1).path :=
  PreparedParents.sources (frame := frame) (basis := basis) sources.2.1 sources.2.2
    (CenteredPathChain.ofCenteredSubdivision (Fibre.frameCurve frame) basis sheet subdivision sources.1)

end Sources

namespace Cache

/-- Every actual original trace integral is the sample of the SAME retained selected source cell, in original order. -/
theorem integrals_eq_cells (row : Row) : ∀ {current : Endpoint}
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (sources : Sources (frame := frame) (basis := basis) (targets := targets)
      (count := count) (floor := floor) (sheet := sheet) subdivision),
    integrals row (frame := frame) (basis := basis) subdivision sources =
      (row.cells sources.path).map (fun cell => cell.integralSample)
  | _, _, .stop _ _, sources => by
      cases sources with
      | mk centers rest =>
        cases rest with
        | mk covered prepared =>
          cases covered with
          | nil =>
            change [] = (row.cells (Path.nil _)).map (fun cell => cell.integralSample)
            rewrite [row.cells_nil]
            rfl
  | _, _, .next _ _ _ _ _ _ remaining, sources => by
      cases sources with
      | mk centers rest =>
        cases rest with
        | mk covered prepared =>
          cases covered with
          | cons _ _ covered =>
            change (row.cell prepared.1.preparation.models).integralSample :: _ =
              (row.cells (Path.cons prepared.1.preparation.cell
                (Sources.path (frame := frame) (basis := basis) (count := count) (floor := floor)
                  (sheet := sheet) (targets := targets)
                  ⟨centers.2, ⟨covered, prepared.2⟩⟩))).map (fun cell => cell.integralSample)
            rewrite [row.cells_cons]
            change (row.cell prepared.1.preparation.models).integralSample :: _ =
              (row.cell prepared.1.preparation.cell.models).integralSample :: _
            have sameHead : (row.cell prepared.1.preparation.models).integralSample =
                (row.cell prepared.1.preparation.cell.models).integralSample := by
              rewrite [prepared.1.preparation.cell_eq]
              rfl
            exact congrArg₂ List.cons sameHead
              (integrals_eq_cells row remaining ⟨centers.2, ⟨covered, prepared.2⟩⟩)
termination_by structural _ _ subdivision _ => subdivision

/-- The SAME ordered actual affine integral list sums to its retained original source Path's relation sample. -/
theorem integrals_sum_eq (row : Row) {current : Endpoint}
    {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
    (subdivision : Subdivision segment within current owner)
    (sources : Sources (frame := frame) (basis := basis) (targets := targets)
      (count := count) (floor := floor) (sheet := sheet) subdivision) :
    Norm.Sum.Basic.gaussianSum (integrals row (frame := frame) (basis := basis) subdivision sources) =
      (PathModel.mk (row.cells sources.path)).integralSample :=
  (congrArg Norm.Sum.Basic.gaussianSum
    (integrals_eq_cells row (frame := frame) (basis := basis) subdivision sources)).trans
      (PathModel.integralSample_eq_gaussianSum _).symm

end Cache

namespace Compared

variable {row : Row} {left right : Endpoint} {accuracy : AccuracyRequest}
variable {budget : PreparedTraceBudget segment left right}
variable {allocation : targets.endpoint = 4 * accuracy.tolerance} {current : Endpoint}
variable {owner : Owner ((Paths.polynomial parameter).eval (segment.pointAt current.parameter))}
variable {subdivision : Subdivision segment within current owner}
variable {originalSources : Sources (frame := frame) (basis := basis) (targets := targets)
  (count := count) (floor := floor) (sheet := sheet) subdivision}
variable {fits : budget.RequestsFit current subdivision.requests}
variable {originalObserved : Primitive.Spine (row.expression parameter) accuracy
  (PreparedSubdivisionTrace.PreparedTraceBudget.ownerPath budget subdivision fits)}
variable (retained : Compared row (frame := frame) (basis := basis)
  budget allocation subdivision originalSources fits originalObserved)

/-- The actual same-cache comparison's integral list is its original ordered source-cell sample list. -/
theorem integrals_eq_cells : retained.integrals =
    (row.cells retained.sources.path).map (fun cell => cell.integralSample) :=
  Cache.integrals_eq_cells row (frame := frame) (basis := basis) subdivision retained.sources

/-- The SAME literal trace comparison consumes its original ordered source Path relation integral. -/
theorem source_integral_error_le : Norm.Basic.normSq
    (retained.observed.last.value - retained.observed.first.value -
      (PathModel.mk (row.cells retained.sources.path)).integralSample) ≤
        (subdivision.requests.length : Rational) * ((subdivision.requests.length : Rational) *
          (26 * targets.endpoint)) := by
  have paid := retained.integral_error_le
  have sameIntegral : Norm.Sum.Basic.gaussianSum retained.integrals =
      (PathModel.mk (row.cells retained.sources.path)).integralSample :=
    Cache.integrals_sum_eq row (frame := frame) (basis := basis) subdivision retained.sources
  rewrite [sameIntegral] at paid
  exact paid

end Compared

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace

end
