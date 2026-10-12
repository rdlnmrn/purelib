module
import Purelib.Approximation.Gaussian.Name.CCL.Grammar
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Grammar.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Track.Approximation.Name
import Purelib.RootIsolation.Track.Basic
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Basic

open Purelib.Data.CCL.Transducer (Machine)

open Purelib

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

namespace Purelib.RootIsolation.Track.CCL.Productivity

/-- Every finite bit request extends the original track cursor's emitted prefix and produces exactly the requested
number of bits. -/
theorem initial_productive {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient) (count : Nat) :
    (Track.Approximation.Name.initialNamed track).machine.emitted.IsPrefix
        (Machine.Advance.advance
          (Track.Approximation.Name.initialNamed track).machine count).emitted ∧
      (Machine.Advance.advance
          (Track.Approximation.Name.initialNamed track).machine count).emitted.length = count :=
  (Track.Approximation.Name.initialNamed track).productive count

/-- Advancing the initial retained track cursor preserves the machine grammar invariant. -/
theorem initial_grammar {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box}
    (track : Track.Basic.WindingOneTrack p ambient) (count : Nat) :
    Data.CCL.Transducer.Machine.Grammar.Invariant
      (Machine.Advance.advance
        (Track.Approximation.Name.initialNamed track).machine count) :=
  open Purelib.Approximation.Gaussian in Name.CCL.Grammar.Named.machine_advance_invariant
    (Track.Approximation.Name.initialNamed track) count
end Purelib.RootIsolation.Track.CCL.Productivity

end
