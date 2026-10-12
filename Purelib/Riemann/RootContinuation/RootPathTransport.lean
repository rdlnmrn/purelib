module
import Purelib.Data.Fin
import Purelib.Data.Nat.Order
import Purelib.Data.Int.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Segment
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
public import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Polynomial.Winding.Polygon.Stationary

public import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Retained two-sheet transports of actual clear paths

Both source rows retain their original integration preparation.  A checked
endpoint comparison identifies its actual finish owner with one owner in the
shared target frame.  The associated owner trace inserts only that proved
stationary comparison, not a labelled sheet switch.

Independently prepared reverse rows are inverse maps: their concatenations
have zero winding and hence return operationally.  The proof is erased;
reading the finite permutation does not rerun those concatenated traces.
-/

namespace Purelib.Riemann.RootContinuation.RootPathTransport

open scoped Purelib.Data.Nat
open Purelib.Data

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense

open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (NameSelection OwnerFrame OwnerSelection)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

namespace OwnerPath

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
/-- Join equivalent root owners at one fixed point by a stationary owner path.

The handoff retains both supplied owners and their name-equivalence witness.
Its single stationary link ends at the supplied last owner without tracing a new segment. -/
@[expose] def join (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (base :
  Basic.Canonical)
    (first last : Owner (polynomial.eval base)) (equivalent : Equivalence.NamedEquivalent (ownerName first) (ownerName
      last)) :
    OwnerPath polynomial base first base last :=
  .cons (OwnerLink.stationary polynomial base (OwnerJoin.acquire first last equivalent)) (.nil base last)

open Purelib.Approximation.Gaussian in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The stationary original owner join has zero raw winding. -/
theorem join_winding (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (base :
  Basic.Canonical)
    (first last : Owner (polynomial.eval base)) (equivalent : Equivalence.NamedEquivalent (ownerName first) (ownerName
      last)) :
    Winding.Polygon.Basic.chainRaw polynomial base (join polynomial base first last equivalent).vertices = 0 := by
  change (Path.Segment.segment polynomial base base).doubledWinding + 0 = 0
  rw [Winding.Polygon.Stationary.segment_self_doubledWinding polynomial base first.parameterNonzero,
    Int.Arithmetic.zero_add]

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
/-- Raw winding adds when original owner paths are concatenated at their shared owner. -/
theorem append_winding {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {start middle finish : Basic.Canonical}
    {first : Owner (polynomial.eval start)} {center : Owner (polynomial.eval middle)} {last : Owner (polynomial.eval
      finish)}
    (left : OwnerPath polynomial start first middle center) (right : OwnerPath polynomial middle center finish last) :
    Winding.Polygon.Basic.chainRaw polynomial start (left.append right).vertices =
      Winding.Polygon.Basic.chainRaw polynomial start left.vertices + Winding.Polygon.Basic.chainRaw polynomial middle
        right.vertices := by
  rw [OwnerTracePath.OwnerPath.append_vertices, Winding.Polygon.Basic.chainRaw_append, left.vertices_terminal]

end OwnerPath

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}

open Purelib.Approximation.Gaussian in
set_option genInjectivity false in
/-- A retained trace with a selected target name for its actual finish.

The finish-name function is applied to that exact trace, and the selection retains its original two-name family and
equivalence witness. -/
structure TracedSelection (Trace : Type) (finishName : Trace → Name.Basic.Named)
    (names : Fin 2 → Name.Basic.Named) where
  /-- The actual retained trace whose finish name is selected. -/ traced : Trace
  /-- The exact original target-name selection of this trace's finish. -/ selected : NameSelection names (finishName
    traced)

constructive_injectivity TracedSelection

open Purelib.Polynomial in
/-- One original framed root's traced path and exact target-frame selection. -/
abbrev TransportRow (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (first : OwnerFrame (polynomial.eval start)) (last : OwnerFrame (polynomial.eval finish)) (index : Fin 2) :=
  TracedSelection (TracedPath path (first.owners index)) (fun traced => ownerName traced.finishOwner)
    (fun target => ownerName (last.owners target))

namespace TransportRow

variable {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
  {first : OwnerFrame (polynomial.eval start)} {last : OwnerFrame (polynomial.eval finish)} {index : Fin 2}

/-- Read the selected target-frame index of the retained transport. -/
@[expose] def target (row : TransportRow path first last index) : Fin 2 := row.selected.index

open Purelib.Approximation.Gaussian in
/-- Read the original traced finish owner's equivalence to its selected target owner. -/
@[expose] def equivalent (row : TransportRow path first last index) :
    Equivalence.NamedEquivalent (ownerName row.traced.finishOwner) (ownerName (last.owners row.target)) :=
  row.selected.equivalent

/-- Select the original traced finish owner in the retained target frame. -/
@[expose] def ofTraced (last : OwnerFrame (polynomial.eval finish)) (traced : TracedPath path (first.owners index)) :
    TransportRow path first last index :=
  ⟨traced, last.select traced.finishOwner⟩

open Purelib.Polynomial in
/-- Trace a clear path from one retained source-frame owner and select its target-frame owner.

The resulting row stores that exact path trace and applies the target frame's
classification to its actual finish owner, preserving the selected equivalence witness. -/
@[expose] def build (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) (within : path.WithinAmbient)
    (first : OwnerFrame (polynomial.eval start)) (last : OwnerFrame (polynomial.eval finish)) (index : Fin 2) :
    TransportRow path first last index :=
  ofTraced last (TracedPath.build path within (first.owners index))

/-- Append a stationary target-owner join to the retained path trace.

The trace's actual finish owner is connected to its selected target owner
using the stored equivalence, while its initial owner and traced links remain. -/
@[expose] def joined (row : TransportRow path first last index) :
    OwnerPath polynomial start (first.owners index) finish (last.owners row.target) :=
  row.traced.trace.get.append (OwnerPath.join polynomial finish row.traced.finishOwner (last.owners row.target)
    row.equivalent)

open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- The joined owner trace preserves the original clear path's raw winding. -/
theorem joined_winding (row : TransportRow path first last index) :
    Winding.Polygon.Basic.chainRaw polynomial start row.joined.vertices = PreparedPathWinding.ClearPath.rawWinding path
      := by
  rw [joined, OwnerPath.append_winding, PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original
    row.traced, OwnerPath.join_winding, Int.add_zero]

end TransportRow

open Purelib.Polynomial in
set_option genInjectivity false in
/-- The two retained framed root transports along one original clear path.

The zero and one rows keep their respective original initial owners, actual path traces and target-frame selections. -/
structure PathTransport (path : Polynomial.Geometry.ClearPath polynomial ambient start finish)
    (first : OwnerFrame (polynomial.eval start)) (last : OwnerFrame (polynomial.eval finish)) where
  /-- The original clear-path transport from sheet zero. -/ zero : TransportRow path first last 0
  /-- The original clear-path transport from sheet one. -/ one : TransportRow path first last 1

constructive_injectivity PathTransport

namespace PathTransport

variable {path : Polynomial.Geometry.ClearPath polynomial ambient start finish}
  {first : OwnerFrame (polynomial.eval start)} {last : OwnerFrame (polynomial.eval finish)}

set_option backward.match.sparseCases false in
/-- Read the cached transport row at its retained two-sheet index.

The original zero or one coordinate selects the corresponding stored row.
The retained bound excludes every larger coordinate, so no transport is rebuilt. -/
@[expose] def row (transport : PathTransport path first last) : (index : Fin 2) → TransportRow path first last index
  | ⟨0, _⟩ => transport.zero
  | ⟨1, _⟩ => transport.one
  | ⟨value + 2, bound⟩ => False.elim (by omega0)

/-- Read the selected target sheet from the retained row at the original source index. -/
@[expose] def target (transport : PathTransport path first last) (index : Fin 2) : Fin 2 := (transport.row index).target

open Purelib.Polynomial in
/-- Build two-sheet root transport along a clear path between retained endpoint frames.

Each original source-frame owner receives its own stored trace and exact
target-frame selection. The two rows retain their distinct source indices. -/
@[expose] def build (path : Polynomial.Geometry.ClearPath polynomial ambient start finish) (within : path.WithinAmbient)
    (first : OwnerFrame (polynomial.eval start)) (last : OwnerFrame (polynomial.eval finish)) : PathTransport path first
      last :=
  ⟨TransportRow.build path within first last 0, TransportRow.build path within first last 1⟩

open Purelib.Approximation.Gaussian in
/-- Construct the empty-path transport retaining each frame owner.

The two stored empty traces finish at their respective original owners.
Their target selections retain the matching indices and reflexive name witnesses. -/
@[expose] def identity (frame : OwnerFrame (polynomial.eval start)) : PathTransport (.nil (ambient := ambient) start)
  frame frame :=
  ⟨⟨TracedPath.build (.nil start) (.nil start) (frame.owners 0), ⟨0, Equivalence.NamedEquivalent.refl _⟩⟩,
    ⟨TracedPath.build (.nil start) (.nil start) (frame.owners 1), ⟨1, Equivalence.NamedEquivalent.refl _⟩⟩⟩

/-- Identity transport preserves each original sheet index. -/
theorem identity_target (frame : OwnerFrame (polynomial.eval start)) (index : Fin 2) :
    (identity (ambient := ambient) frame).target index = index := by
  exact Fin.cases_induction rfl
    (fun next => Fin.cases_induction rfl (fun empty => Fin.elim0 empty) next) index

open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Zero combined winding makes the retained forward/backward transport return to its original sheet.

The proof uses the actual joined owner traces and a retained winding-one reference loop to distinguish the original
frame owners. -/
theorem roundTrip_index {backPath : Polynomial.Geometry.ClearPath polynomial ambient finish start}
    (reference : WindingOneLoop polynomial start)
    (forward : PathTransport path first last) (backward : PathTransport backPath last first)
    (cancel : PreparedPathWinding.ClearPath.rawWinding path + PreparedPathWinding.ClearPath.rawWinding backPath = 0)
      (index : Fin 2) :
    backward.target (forward.target index) = index := by
  let left := forward.row index
  let right := backward.row left.target
  let closed := left.joined.append right.joined
  have winding : Winding.Polygon.Basic.chainRaw polynomial start closed.vertices = 8 * (0 : Int) := by
    rw [OwnerPath.append_winding, left.joined_winding, right.joined_winding]
    exact cancel
  exact first.distinguish _ _ (OwnerLoopMonodromy.OwnerPath.rootEquivalent_of_even_with_reference reference closed 0
    winding)

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Construct the two-sheet bijection from retained forward/backward transport and zero combined winding.

Both endpoint reference loops certify the inverse laws for the exact target-selection functions already stored in the
transports. -/
@[expose] def bijection {backPath : Polynomial.Geometry.ClearPath polynomial ambient finish start}
    (firstReference : WindingOneLoop polynomial start) (lastReference : WindingOneLoop polynomial finish)
    (forward : PathTransport path first last) (backward : PathTransport backPath last first)
    (cancel : PreparedPathWinding.ClearPath.rawWinding path + PreparedPathWinding.ClearPath.rawWinding backPath = 0) :
    Data.Fin.Bijection 2 2 where
  forward := forward.target
  backward := backward.target
  backward_forward := forward.roundTrip_index firstReference backward cancel
  forward_backward := backward.roundTrip_index lastReference forward (by omega)

end PathTransport

end Purelib.Riemann.RootContinuation.RootPathTransport
