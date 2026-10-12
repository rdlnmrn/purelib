module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain

/-!
# A retained root frame at every common grid vertex

The canonical producer visits the finite Cartesian product of the two axes
once.  Edge queries look up stored owners by exact coordinates; they do not
run root isolation again.  Generated banks may provide different checked
owners and a different enumeration, subject to the same finite coverage law.
-/

namespace Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Data
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Data.List

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

namespace RootFrames

set_option genInjectivity false in
/-- One retained pair of actual root occurrences at its displayed point.

The displayed coordinate determines the exact polynomial value indexing the stored frame. Both root occurrences remain
owned by that retained base value. -/
public structure RootFrameEntry (polynomial : Geometry.ClearPath.GaussianPolynomial) where
  /-- The exact grid coordinate at which the root frame is retained. -/ point : Gaussian.Basic.Canonical
  /-- The retained pair of root occurrences over the polynomial value at this point. -/ frame :
    Riemann.RootContinuation.RootOwnerFrames.OwnerFrame (polynomial.eval point)

constructive_injectivity RootFrameEntry

end RootFrames

namespace RootFrames.RootFrameEntry

/-- Prepare a root frame at the intersection of two retained clear grid lines.

The original line clearance proves nonzeroness at that exact coordinate. -/
@[expose] public def ofLines (vertical : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (horizontal :
  Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) :
    SquareRoot.Grid.RootFrames.RootFrameEntry polynomial :=
  let segment : Geometry.ClearPath.ClearSegment polynomial ambient (Gaussian.Components.Basic.point vertical.coordinate
    horizontal.coordinate)
      (Gaussian.Components.Basic.point vertical.coordinate horizontal.coordinate) :=
    .horizontal vertical.coordinate vertical.coordinate horizontal.coordinate
      vertical.inside.1 vertical.inside.2 vertical.inside.1 vertical.inside.2 horizontal.clearance
  ⟨Gaussian.Components.Basic.point vertical.coordinate horizontal.coordinate,
    Riemann.RootContinuation.RootOwnerFrames.OwnerFrame.build segment.start_eval_ne_zero⟩

/-- Transport the stored root frame along equality of its displayed base coordinate. -/
@[expose] public def frameAt (entry : SquareRoot.Grid.RootFrames.RootFrameEntry polynomial) (base :
  Gaussian.Basic.Canonical) (equal : entry.point = base) :
    Riemann.RootContinuation.RootOwnerFrames.OwnerFrame (polynomial.eval base) := equal ▸ entry.frame

/-- Look up the actual stored frame at a displayed coordinate.

The first matching entry is returned after exact coordinate comparisons. The original finite bank, retained frames and
recursive tails are reused without root isolation or frame reconstruction. -/
@[expose] public def lookup (base : Gaussian.Basic.Canonical) : (entries : List
  (SquareRoot.Grid.RootFrames.RootFrameEntry polynomial)) →
    base ∈ entries.map SquareRoot.Grid.RootFrames.RootFrameEntry.point →
      Riemann.RootContinuation.RootOwnerFrames.OwnerFrame (polynomial.eval base)
  | [], member => (List.not_mem_nil member).elim
  | head :: tail, member =>
      if equal : base = head.point then head.frameAt base equal.symm
      else
        Purelib.RootIsolation.SquareRoot.Grid.RootFrames.RootFrameEntry.lookup base tail (by
          rcases Membership.mem_cons.mp member with same | remaining
          · exact (equal same).elim
          · exact remaining)

end RootFrames.RootFrameEntry

set_option genInjectivity false in
/-- A finite bank of retained root frames covering every original grid vertex.

The coverage witness indexes the actual stored entries, so queries reuse their owners. -/
public structure RootFrames (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) where
  /-- The retained finite list of actual root-frame entries. -/ entries : List
    (SquareRoot.Grid.RootFrames.RootFrameEntry polynomial)
  /-- Every original grid vertex occurs among the stored entry coordinates. -/ covers : ∀ base,
    Polynomial.Geometry.Grid.FromStates.ContainsVertex grid base →
    base ∈ entries.map SquareRoot.Grid.RootFrames.RootFrameEntry.point

constructive_injectivity RootFrames

namespace RootFrames

variable {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient}

/-- Materialize all endpoint frames once from the original grid lines.

The finite Cartesian traversal retains the original axis order and line-clearance certificates. Nonzeroness at each
displayed vertex follows from those exact lines, and the coverage proof indexes the stored frame bank. -/
@[expose] public def build (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) :
  RootFrames grid := by
  let entries := grid.vertical.flatMap fun vertical =>
    grid.horizontal.map fun horizontal => SquareRoot.Grid.RootFrames.RootFrameEntry.ofLines vertical horizontal
  refine ⟨entries, ?_⟩
  intro base member
  rcases Map.mem_map.mp member.1 with ⟨vertical, verticalMember, verticalEq⟩
  rcases Map.mem_map.mp member.2 with ⟨horizontal, horizontalMember, horizontalEq⟩
  apply Map.mem_map.mpr
  refine ⟨RootFrameEntry.ofLines vertical horizontal, ?_, ?_⟩
  · exact Flatten.mem_flatMap.mpr ⟨vertical, verticalMember,
      Map.mem_map.mpr ⟨horizontal, horizontalMember, rfl⟩⟩
  · exact Gaussian.Basic.ext verticalEq horizontalEq

/-- Look up the stored frame at a certified original grid vertex. -/
@[expose] public def frameAt (frames : RootFrames grid) (base : Gaussian.Basic.Canonical)
    (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid base) :
    Riemann.RootContinuation.RootOwnerFrames.OwnerFrame (polynomial.eval base) :=
  SquareRoot.Grid.RootFrames.RootFrameEntry.lookup base frames.entries (frames.covers base member)

end RootFrames

end Purelib.RootIsolation.SquareRoot.Grid
