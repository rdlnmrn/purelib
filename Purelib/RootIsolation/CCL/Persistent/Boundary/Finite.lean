module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
public import Purelib.Geometry.Projective.Hermitian.Formula.Box.Override
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.CCL.Persistent.State.Basic
public import Purelib.RootIsolation.CCL.Persistent.Terminal.Finite
import Purelib.RootIsolation.Track.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Geometry.Projective.Hermitian.Formula.Box (FormOverride)

public section

open Purelib.Data

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Finite equality ownership for CCL formula atoms

The parser's weak/strict convention decides every atom exactly at a zero of
its Hermitian form.  This module records that decision as finite data and
lets formula inspection reuse boundaries already proved identically zero.
Consequently a universal boundary is discharged once, and structural
reinspection either proves the complete formula stable or returns a
different unresolved atom.
-/

namespace Purelib.RootIsolation.CCL.Persistent.Boundary

set_option genInjectivity false in
/-- Resolving a finite nonnegative zero set either finds an exact polynomial
root or produces a same-prefix refinement on which that form is strictly
positive. -/
inductive Resolution
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) (atom : Geometry.Projective.Hermitian.Atom) where
  /-- An exact zero at one of the original retained boundary candidates. -/ | exact (root :
    State.Basic.ExactRootIn p current.numerical.box)
  /-- A same-word box refinement whose retained boundary values are strictly positive, with the exact form override. -/
    | positive (state : State p ambient)
      (boxRefines : state.numerical.box.Refines current.numerical.box)
      (word_eq : state.word = current.word)
      (stability : FormOverride
        state.numerical.box)
      (form_eq : stability.form = atom.form)

constructive_injectivity Resolution

/-- Exclude all displayed zeros using the winding track, then turn
nonnegativity plus nonvanishing into a reusable strict-positive form
override. -/
@[expose] def resolve
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : Track.Basic.WindingOneTrack p ambient) (current : State p
      ambient)
    (atom : Geometry.Projective.Hermitian.Atom) (points : List Gaussian.Basic.Canonical)
    (complete : ∀ value, atom.form.eval value = 0 → value ∈ points)
    (nonnegative : ∀ value, 0 ≤ atom.form.eval value) :
    Resolution current atom := by
  match CCL.Persistent.Terminal.Finite.resolvePoints degreePositive
      track current points with
  | .exact root => exact .exact root
  | .excluded state boxRefines word_eq outside =>
      let stability : FormOverride
          state.numerical.box :=
        FormOverride.positive atom.form
          (by
            intro value inside
            have nonzero : atom.form.eval value ≠ 0 := by
              intro evaluatesZero
              exact outside value (complete value evaluatesZero) inside
            rcases lt_trichotomy (atom.form.eval value) 0 with
                negative | equal | positive
            · exact (not_lt_of_ge (nonnegative value) negative).elim
            · exact (nonzero equal).elim
            · exact positive)
      exact .positive state boxRefines word_eq stability rfl

end Purelib.RootIsolation.CCL.Persistent.Boundary

end
