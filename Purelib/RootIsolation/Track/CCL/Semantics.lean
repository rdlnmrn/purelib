module
import Purelib.Approximation.Gaussian.Name.CCL.Semantics
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Committed
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Approximation.Name
import Purelib.RootIsolation.Track.Approximation.Process
import Purelib.RootIsolation.Track.Basic
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Basic

open Purelib.Data.CCL.Transducer (Machine)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

open Purelib

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Winding-one tracks as progressive arithmetic processes

Paper I supplies independently shrinking rational boxes without asserting a
completed root.  This module exposes each such finite track directly through
the CCL-2 squared-error process interface.  The possibility predicate is
the current box predicate itself; no point is selected from an intersection.
-/

namespace Purelib.RootIsolation.Track.CCL.Semantics

/-- The finite arithmetic cursor started from any displayed winding box is
exact for a rational point admitted by that box. -/
theorem toNamedAt_exact
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (state : State.WindingOne.Basic.WindingOneState p ambient)
    (count : Nat) :
    Machine.Semantics.Basic.ExactCursor
      (Approximation.Process.toProcess track) state
      (Machine.Advance.advance
        (Approximation.Name.toNamedAt track state).machine count) :=
  open Purelib.Approximation.Gaussian in Name.CCL.Semantics.Named.advance_exact
    (Approximation.Name.toNamedAt track state) count

/-- Pointwise box/cursor compatibility: every quantitative tail after a
finite bit request reconstructs a displayed rational point of the source
winding box through the unchanged raw parser. -/
theorem toNamedAt_candidate_exact
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (state : State.WindingOne.Basic.WindingOneState p ambient)
    (count : Nat)
    {tail : Gaussian.Basic.Canonical}
    (possible :
      CCL.Transducer.Mode.Semantics.SemanticMode.possible
        (Machine.Advance.advance
          (Approximation.Name.toNamedAt track state).machine count).mode tail) :
    ∃ value : Gaussian.Basic.Canonical,
      state.box.Contains value ∧
        (Geometry.Projective.Line.Matrix.act
          (CCL.Encoding.Parser.State.parse
            (Machine.committed
              (Machine.Advance.advance
                (Approximation.Name.toNamedAt track state).machine count))).matrix
          (CCL.Transducer.Mode.Semantics.SemanticMode.parserTail
            (Machine.Advance.advance
              (Approximation.Name.toNamedAt track state).machine count).mode tail)).Equivalent
                (Geometry.Projective.Line.Proj.affine value) := open Purelib.Approximation.Gaussian in by
  exact Name.CCL.Semantics.Named.advance_candidate_exact
    (Approximation.Name.toNamedAt track state) count possible

/-- Every finite advance of the initial track cursor remains exact for the original initial winding box. -/
theorem initial_exact
    {p : CoefficientPolynomial} {ambient : Box}
    (track : WindingOneTrack p ambient) (count : Nat) :
    Machine.Semantics.Basic.ExactCursor
      (Approximation.Process.toProcess track) track.initial
      (Machine.Advance.advance
        (Approximation.Name.initialNamed track).machine count) :=
  toNamedAt_exact track track.initial count

end Purelib.RootIsolation.Track.CCL.Semantics

end
