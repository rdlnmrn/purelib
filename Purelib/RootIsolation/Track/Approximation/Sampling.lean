module

public import Purelib.RootIsolation.Track.Approximation.Name
public import Purelib.Approximation.Gaussian.Process.Sampling
public import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Enclosure.Ball.Box

/-! # Actual sampled states of the original winding-track arithmetic process -/

public section

namespace Purelib.RootIsolation.Track.Approximation.Sampling

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Geometry.Rational
open Purelib.RootIsolation
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)

/-- The original box-process state selected by its canonical finite sampling trajectory. -/
@[expose] def stateAt {polynomial : CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack polynomial ambient) (index : Nat) :
    State.WindingOne.Basic.WindingOneState polynomial ambient :=
  Process.Sampling.stateAt (Approximation.Process.toProcess track) track.initial index

/-- Every original sampled state lies inside the same original initial winding box.

The zero stage is an actual refinement of the original start. Each successor
refines that same trajectory's preceding state and retains its nesting law.
-/
theorem refines_initial {polynomial : CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack polynomial ambient) (index : Nat) :
    (stateAt track index).box.Refines track.initial.box := by
  induction index with
  | zero => exact track.nested _ _ _
  | succ index previous => exact (track.nested _ _ _).trans previous

/-- The original sampled state's squared diagonal is below the same canonical geometric request. -/
theorem diagonal_lt {polynomial : CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack polynomial ambient) (index : Nat) :
    (stateAt track index).box.diagonalSq < Process.Sampling.refinementTarget index :=
  Process.Sampling.stateAt_accurate (Approximation.Process.toProcess track) track.initial index

/-- The original arithmetic name's sampled witness is the anchor of its actual sampled winding state. -/
theorem sample_eq_anchor {polynomial : CoefficientPolynomial} {ambient : Box}
    (track : Basic.WindingOneTrack polynomial ambient) (index : Nat) :
    (Name.Sampling.approximation (Approximation.Name.initialNamed track)).sample index =
      (stateAt track index).box.anchor := rfl

end Purelib.RootIsolation.Track.Approximation.Sampling

end
