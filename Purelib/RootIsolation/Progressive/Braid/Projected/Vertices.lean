module
import Purelib.Data.List.Map
import Purelib.RootIsolation.Progressive.Braid.Projected.Frame
public import Purelib.RootIsolation.Progressive.Braid.Projected.Path
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap

open Purelib.RootIsolation.Progressive.Braid.Projected.Frame (ProjectedFrame)
open Purelib.RootIsolation.Progressive.Braid.Projected.Path (ProjectedPath)

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# A finite braid theorem for certified rational polynomial loops

An admissible loop here is exactly the finite data required by the theorem:
rational coefficient tables in certified simple-root chambers, finite Rouché
overlaps between successive tables, rational projection-order root boxes, and
an atomic stationary/crossing certificate for every subdivision cell.  No
completed coefficient path or configuration space is part of the input.

The headline extraction is executable.  It returns the folded Artin word and
proves, in the endpoint projection coordinates, that the word permutation is
the persistent-root monodromy.  Concatenation is word multiplication;
operational refinement leaves the word unchanged; and a finite chain of
refinement and Artin moves preserves the braid class, endpoint transport, and
writhe.
-/

namespace Purelib.RootIsolation.Progressive.Braid.Projected.Vertices

/-- All finite chamber frames visited by a projected path, including both
endpoints. -/
def chamberFrames {strands : Nat} :
    {start finish : ProjectedFrame strands} →
      ProjectedPath start finish → List Progressive.Chamber.Frame.ChamberFrame
  | _, _, .nil frame => [frame.chamber]
  | _, _, .cons (start := start) _ remaining =>
      start.chamber :: chamberFrames remaining

/-- Exact monic Gaussian-rational coefficient polynomials at every displayed
subdivision vertex. -/
def coefficientVertices {strands : Nat}
    {start finish : ProjectedFrame strands}
    (path : ProjectedPath start finish) : List
      Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial :=
  (chamberFrames path).map Progressive.Chamber.Frame.ChamberFrame.polynomial

/-- The retained chamber-frame list has one more entry than the original projected path's step count. -/
@[simp] theorem chamberFrames_length {strands : Nat}
    {start finish : ProjectedFrame strands}
    (path : ProjectedPath start finish) :
    (chamberFrames path).length = path.stepCount + 1 := by
  induction path with
  | nil frame => rfl
  | cons step remaining inductionHypothesis =>
      simp only [chamberFrames,
        ProjectedPath.stepCount, -eq_self, -iff_self]
      exact congrArg Nat.succ inductionHypothesis

/-- The retained coefficient-vertex list has one more entry than the original projected path's step count. -/
@[simp] theorem coefficientVertices_length {strands :
  Nat}
    {start finish : ProjectedFrame strands}
    (path : ProjectedPath start finish) :
    (coefficientVertices path).length = path.stepCount + 1 := by
  rewrite [coefficientVertices]
  exact (Data.List.Map.length_map _ _).trans
    (chamberFrames_length path)

end Purelib.RootIsolation.Progressive.Braid.Projected.Vertices

end
