module
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy of persistent root owners

This file turns the local owner identity supplied by progressive polynomial
root continuation into a pathwise construction.  A path is an inductive
finite chain of certified chamber overlaps.  Each overlap carries rational
boxes on which the two displayed polynomials are connected by an explicit
finite Rouché certificate, together with the two-sided owner matching proved
by those boxes.  Folding the matchings returns a finite bijection; for a
closed chain this is the monodromy permutation.

There is no completed coefficient path, root, loop, or root space here.  All
objects are finite coefficient tables, rational boxes, finite winding
certificates, and functions between displayed finite index types.
-/

namespace Purelib.RootIsolation.Track.Transport

/-- Reindex an entire executable shrinking track without changing its finite
refinement program. -/
def castWindingOneTrack
    {leftPolynomial rightPolynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {leftAmbient rightAmbient : Box}
    (polynomialSame : leftPolynomial = rightPolynomial)
    (ambientSame : leftAmbient = rightAmbient)
    (track : WindingOneTrack
      leftPolynomial leftAmbient) :
    WindingOneTrack rightPolynomial rightAmbient := by
  subst rightPolynomial
  subst rightAmbient
  exact track

/-- Polynomial and ambient reindexing preserve the track's exact initial box. -/
@[simp] theorem castWindingOneTrack_initial_box
    {leftPolynomial rightPolynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {leftAmbient rightAmbient : Box}
    (polynomialSame : leftPolynomial = rightPolynomial)
    (ambientSame : leftAmbient = rightAmbient)
    (track : WindingOneTrack
      leftPolynomial leftAmbient) :
    (castWindingOneTrack polynomialSame ambientSame track).initial.box =
      track.initial.box := by
  subst rightPolynomial
  subst rightAmbient
  rfl

end Purelib.RootIsolation.Track.Transport

end

public section

namespace Purelib.RootIsolation.Track.Basic.WindingOneTrack

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Rat.Fraction (Rational)

/-- Start the original refinement program at a supplied certified state of the same polynomial and ambient box.

Only the initial state changes. The original refine, nesting, strictness and
accuracy functions are retained unchanged, allowing the new track to keep its
source refinement procedure rather than running isolation again.
-/
@[expose] def atState
    {polynomial : CoefficientPolynomial}
    {ambient : Box} (track : WindingOneTrack polynomial ambient)
    (current : State.WindingOne.Basic.WindingOneState polynomial ambient) :
    WindingOneTrack polynomial ambient :=
  { track with initial := current }

/-- The new track retains the supplied original state literally as its initial state. -/
theorem atState_initial
    {polynomial : CoefficientPolynomial}
    {ambient : Box} (track : WindingOneTrack polynomial ambient)
    (current : State.WindingOne.Basic.WindingOneState polynomial ambient) :
    (track.atState current).initial = current := rfl

/-- Refinement after changing the initial state is the exact original refinement operation. -/
theorem atState_refine
    {polynomial : CoefficientPolynomial}
    {ambient : Box} (track : WindingOneTrack polynomial ambient)
    (initial current : State.WindingOne.Basic.WindingOneState polynomial ambient)
    (target : Rational) (positive : 0 < target) :
    (track.atState initial).refine current target positive = track.refine current target positive := rfl

end Purelib.RootIsolation.Track.Basic.WindingOneTrack

end
