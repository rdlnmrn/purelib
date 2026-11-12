module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.TraceEndpoints
public import Purelib.Riemann.Paths.PreparedSubdivisionTrace.Trace.Crop
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Integration.PreparedConstantModels.Query

/-! # Actual query crops on one retained paid segment's original parent occurrence

The same rootTrace endpoint reindexing and original centeredIndex locate
the exact child. Its whole parent equality transports only the interface;
no parent-word equality is used to reconstruct a physical trace.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

namespace Acquisition.Segment.Parents

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace.PreparedTraceBudget
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest}
variable {retained : Segment (segment := segment) (within := within) (owner := sourceOwner) request}
variable {sheet : Fin 2} {count : Nat}
variable (parents : Parents differential sheet count retained)

/-- Locate the same physical child once and retain its original endpoint comparisons together with a query crop.

The original full rootTrace and center family are the inputs. The selected
parent index changes only through the original whole parents_eq readback.
The old endpoint operations and new crop consume their own supplied
Queries; none is executed or selected during this lookup.
-/
def traceCropComparisons
    (actual : OwnerPath curve.polynomial start sourceOwner finish retained.traced.finishOwner)
    (actual_eq : actual = retained.traced.trace.get) (index : Fin parents.covered.parents.length)
    (lower upper : Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    (ordered : lower ≤ upper) :
    Trace.CropComparisons (parents.covered.parents[index.val]'index.isLt) lower upper lowerInside upperInside :=
  let selected := Trace.cropAt (retained.rootTrace actual actual_eq) parents.centers
    (parents.centeredIndex index) lower upper lowerInside upperInside ordered
  have same := getElem_congr parents.parents_eq
    (i := index.val) (j := (parents.centeredIndex index).val) rfl index.isLt
  Trace.CropComparisons.cast same.symm selected

/-- The same original rootTrace crop has exactly one ordered terminal vertex after its whole parent transport.

The selected comparison functions remain data in the original result.
This erased law consumes only the crop geometry and actual parents_eq.
-/
theorem traceCropComparisons_vertices
    (actual : OwnerPath curve.polynomial start sourceOwner finish retained.traced.finishOwner)
    (actual_eq : actual = retained.traced.trace.get) (index : Fin parents.covered.parents.length)
    (lower upper : Rational) (lowerInside : 0 ≤ lower ∧ lower ≤ 1) (upperInside : 0 ≤ upper ∧ upper ≤ 1)
    (ordered : lower ≤ upper)
    (source : PreparedEdge.Query
      (parents.covered.parents[index.val]'index.isLt).edge lower lowerInside)
    (target : PreparedEdge.Query
      (parents.covered.parents[index.val]'index.isLt).edge upper upperInside) :
    ((parents.traceCropComparisons actual actual_eq index lower upper lowerInside upperInside ordered).2
      source target).vertices = [(parents.covered.parents[index.val]'index.isLt).edge.point upper] := by
  unfold traceCropComparisons
  exact Trace.CropComparisons.cast_vertices
    (getElem_congr parents.parents_eq (i := index.val) (j := (parents.centeredIndex index).val) rfl index.isLt).symm
    (Trace.cropAt (retained.rootTrace actual actual_eq) parents.centers (parents.centeredIndex index)
      lower upper lowerInside upperInside ordered)
    (fun source target => Trace.cropAt_vertices
      (retained.rootTrace actual actual_eq) parents.centers (parents.centeredIndex index)
      lower upper lowerInside upperInside ordered source target) source target

end Acquisition.Segment.Parents

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

end
