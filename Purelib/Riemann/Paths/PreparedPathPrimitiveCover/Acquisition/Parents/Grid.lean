module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Classification
public import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPathWinding

/-! # Original canonical-grid fragments of an actual retained paid segment

The complete paid Segment and its stored Parents remain the owners. The
actual original centered edges are partitioned at the canonical grid's
retained axes, located once, and classified in that same face bank. Only
the two original segment endpoints require ambient containment. A retained
hole payload remains an unresolved geometric detour, without a signed or
integral attachment claim.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

namespace Acquisition.Segment.Parents

open Purelib
open Purelib.Polynomial.Geometry
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes PrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells (LocatedPrimitiveSplits)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge centeredEdges_point)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {basis : Differential genus}
variable {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest}
variable {sheet : Fin 2} {count : Nat}
variable {retained : Segment (segment := segment) (within := within) (owner := sourceOwner) request}

/-- Each actual retained paid child lies in every closed box containing the original segment endpoints. -/
theorem point_inside (parents : Parents basis sheet count retained) {box : Box}
    (first : box.Contains start) (last : box.Contains finish)
    (parent : CenteredEdge curve basis) (member : parent ∈ parents.covered.parents)
    (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    box.Contains (parent.edge.point fraction) := by
  rewrite [parents.parents_eq] at member
  rewrite [centeredEdges_point curve basis sheet retained.traced.prepared.subdivision parents.centers
    parent member fraction, ClearPath.ClearSegment.pointAt_eq_line]
  exact Geometry.Rational.Box.contains_line first last
    (PreparedSheetContinuation.parameterAt_inside parent.edge.left parent.edge.request
      parent.edge.ordered fraction inside)

/-- The actual stored parents' endpoints lie in the same box as the original paid segment endpoints. -/
theorem endpoints_inside (parents : Parents basis sheet count retained) {box : Box}
    (first : box.Contains start) (last : box.Contains finish) :
    ∀ parent ∈ parents.covered.parents, box.Contains (parent.edge.point 0) ∧ box.Contains (parent.edge.point 1) :=
  fun parent member =>
    ⟨point_inside parents first last parent member 0 ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩,
      point_inside parents first last parent member 1 ⟨of_decide_eq_true rfl, of_decide_eq_true rfl⟩⟩

variable {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree}
variable (base : FramedPuncturedGrid curve branches higher) (axes : PrimitiveAxes base.bank.grid)
variable (parents : Parents basis sheet count retained)
variable (first : (Cuts.Ambient curve).Contains start)
variable (last : (Cuts.Ambient curve).Contains finish)

/-- Exact original grid partitions, locations and classifications of the same complete stored paid parents.

The nearest SplitPrimitiveRequest also stores newly evaluated primitive
increments. This geometric cache only retains the original two splitting
spines and their original face-bank outcomes; it neither evaluates a
primitive nor replaces an existing source request or trace.
-/
@[expose] def GridFragments :=
  Σ splits : { cached : PrimitiveSplits axes parents.covered.parents //
      cached = PrimitiveSplits.build axes parents.covered.parents },
    Σ located : { cached : LocatedPrimitiveSplits axes splits.val //
        cached = LocatedPrimitiveSplits.build base.bank axes splits.val (endpoints_inside parents first last) },
      { classified : LocatedPrimitiveSplits.Classifications base.faces located.val //
        classified = LocatedPrimitiveSplits.classify base.faces located.val }

namespace GridFragments

/-- Partition, locate and classify the same actual paid parents once in the original canonical grid and face bank. -/
def build : GridFragments base axes parents first last :=
  let splits := PrimitiveSplits.build axes parents.covered.parents
  let located := LocatedPrimitiveSplits.build base.bank axes splits (endpoints_inside parents first last)
  let classified := LocatedPrimitiveSplits.classify base.faces located
  ⟨⟨splits, rfl⟩, ⟨located, rfl⟩, ⟨classified, rfl⟩⟩

variable (cached : GridFragments base axes parents first last)

/-- Read the same stored original grid-crossing partitions without another split. -/
@[expose] def splits : PrimitiveSplits axes parents.covered.parents := cached.1.val

/-- Read the same complete original cell-location spine on those retained partitions. -/
@[expose] def locations : LocatedPrimitiveSplits axes cached.splits := cached.2.1.val

/-- Read every original regular-face or branch-hole payload at its retained finite position. -/
@[expose] def classifications : LocatedPrimitiveSplits.Classifications base.faces cached.locations :=
  cached.2.2.val

/-- The stored partitions are the original factory on the identical actual paid parent list. -/
theorem splits_eq : cached.splits = PrimitiveSplits.build axes parents.covered.parents := cached.1.property

/-- The stored locations are the original factory on the same cached partitions and derived endpoint containment. -/
theorem locations_eq : cached.locations = LocatedPrimitiveSplits.build base.bank axes cached.splits
    (endpoints_inside parents first last) := cached.2.1.property

/-- The classification keeps the complete original lookup outcomes on the same retained location spine. -/
theorem classifications_eq : cached.classifications = LocatedPrimitiveSplits.classify base.faces cached.locations :=
  cached.2.2.property

end GridFragments

end Acquisition.Segment.Parents

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

end
