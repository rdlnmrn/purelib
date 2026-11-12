module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Crop
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Chord
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Interior
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Transport
import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Crop
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings.Comparison

/-! # Actual interior query entries of one retained source crop

The original lower Point acquisition and its SAME stationary join reach
the cached lower direct Query. The retained same-View family then supplies
an actual prefix to the given later Query. Its stored root attachment
reaches that SAME query's source Point; no sheet or final comparison is
assumed from matching coordinates.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

universe u

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {originalPath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets originalPath stage} {row : Row} {accuracy : AccuracyRequest}
    {prepared : PreparedParent patch count floor covered targets} {lower upper : Rational}
    {lowerInside : 0 ≤ lower ∧ lower ≤ 1} {upperInside : 0 ≤ upper ∧ upper ≤ 1}
    {operation : PreparedTraceBudget.Trace.CropComparisons parent lower upper lowerInside upperInside}
    {cropped : Crop (frame := frame) (basis := basis) (row := row)
      prepared lower upper lowerInside upperInside operation}
    {comparisonRequest requested : AccuracyRequest}
    {observed : cropped.Observation (accuracy := accuracy) comparisonRequest}
    (points : observed.Points requested)
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {bank : BranchCellBank (Fibre.frameCurve frame) branches higher}
    {rootFrames : RootFrames bank.grid} {face : RegularFace bank} {oldModels : FaceModels rootFrames face}

/-- Derive an interior Entry through the original cached lower join and one actual same-View prefix.

The consumer receives the literal original path and its factory equation,
the actual source Point Entry, and the internally proved old-sheet index.
Both endpoint Queries and every Point remain retained inputs. The prefix
constructs two new Owner tails and one chord-variation table, retained in
that actual path. No Query, Point, join or source preparation is repeated.
-/
def withQueryEntry
    (prefixes : PreparedTraceBudget.Trace.CropFamily.Checked parent lower lowerInside)
    (firstInside : face.cell.box.Contains (parent.edge.point lower))
    (acquired : Entry.Acquisition oldModels firstInside points.samples.1.val.owner)
    {fraction : Rational} {inside : 0 ≤ fraction ∧ fraction ≤ 1}
    (queried : RootedQuery (frame := frame) prepared fraction inside) (later : lower ≤ fraction)
    (queryInside : face.cell.box.Contains (parent.edge.point fraction)) {Result : Type u}
    (consume :
      (path : OwnerPath (Paths.polynomial parameter) (parent.edge.point lower) cropped.endpoints.1.direct.owner
        (parent.edge.point fraction) queried.direct.owner) →
      path = prefixes.val fraction inside later cropped.endpoints.1.direct queried.direct →
      (entry : Entry oldModels (parent.edge.point fraction) queried.sample.owner) →
      entry.sheet = acquired.entry.sheet → Result) : Result :=
  let first := acquired.entry.followJoin points.joins.1.val
  let path := prefixes.val fraction inside later cropped.endpoints.1.direct queried.direct
  let reached := first.followQueryCrop parent.edge lower fraction lowerInside inside path
    (prefixes.property fraction inside later cropped.endpoints.1.direct queried.direct) firstInside queryInside
  let entry := reached.followEquivalent queried.sampleRoots
  have sheet : entry.sheet = acquired.entry.sheet :=
    (reached.followEquivalent_sheet queried.sampleRoots).trans
      ((first.followQueryCrop_sheet parent.edge lower fraction lowerInside inside path
        (prefixes.property fraction inside later cropped.endpoints.1.direct queried.direct)
        firstInside queryInside).trans (acquired.entry.followJoin_sheet points.joins.1.val))
  consume path rfl entry sheet

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

end
