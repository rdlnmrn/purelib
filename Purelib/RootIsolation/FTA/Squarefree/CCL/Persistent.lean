module
public import Purelib.RootIsolation.FTA.Squarefree.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.RootIsolation.CCL.Persistent.Track.Basic
public import Purelib.RootIsolation.CCL.Persistent.Track.Request
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.CCL.Progressive.Cursor.Request
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Approximation.Process
import Purelib.RootIsolation.Track.Basic

open Purelib.Data.CCL.Transducer (Mode)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.FTA.Squarefree (AdapterResult)

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free box/CCL finite FTA interface

The winding calculation supplies the exact degree-many family and the total
shrinking box tracks.  Each finite accuracy request computes a nonzero
rational sample of its refined box, converts that sample to a canonical
Gaussian-integer fraction, and runs the terminating CCL encoder.  Thus the box
and projective records are carried together without extracting a quotient
representative or naming a completed root.
-/

namespace Purelib.RootIsolation.FTA.Squarefree.AdapterResult
section Result

/-- Persistent joint box/cylinder state for one degree-indexed higher root
site.  The state is intended to be fed back into every later request. -/
abbrev PersistentStateAt {p :
  CoefficientPolynomial} (result : AdapterResult p)
    (index : Fin p.natDegree) :=
  CCL.Persistent.Track.Basic.State (result.trackAt index)

/-- Begin the joint request history at the track's initial isolated box and
the empty raw prefix. -/
def persistentStateAt {p :
  CoefficientPolynomial} (result : AdapterResult p)
    (index : Fin p.natDegree) : result.PersistentStateAt index :=
  CCL.Persistent.Track.Basic.State.initial (result.trackAt index)

/-- Refine the preceding numerical box, append exactly `count` bits to the
same arithmetic cursor, and contract its quantitative cylinder below the
same displayed `epsilon^2`. -/
def persistentRequestAt
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree) (current : result.PersistentStateAt index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    result.PersistentStateAt index :=
  current.request epsilon positive count

/-- A joint request refines the retained previous numerical box and arithmetic cursor state. -/
theorem persistentRequestAt_refines
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree) (current : result.PersistentStateAt index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    CCL.Persistent.Track.Request.Refines
      (result.persistentRequestAt index current epsilon positive count)
      current :=
  current.request_refines epsilon positive count

/-- The requested retained numerical box has squared diagonal at most the original accuracy squared. -/
theorem persistentRequestAt_box_accurate
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree) (current : result.PersistentStateAt index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    (result.persistentRequestAt index current epsilon positive count).numerical.box.diagonalSq
      ≤ epsilon ^ 2 :=
  current.request_box_accurate epsilon positive count

/-- A persistent request appends exactly the supplied count to the original emitted word length. -/
theorem persistentRequestAt_word_length
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree) (current : result.PersistentStateAt index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat) :
    (result.persistentRequestAt index current epsilon positive count).cursor.machine.emitted.length =
      current.cursor.machine.emitted.length + count :=
  current.request_word_length epsilon positive count

/-- Any two admitted tails of the requested original cursor have squared chordal separation at most the requested
accuracy squared. -/
theorem persistentRequestAt_cylinder_accurate
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree) (current : result.PersistentStateAt index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat)
    {left right : Canonical}
    (leftPossible :
      Mode.Semantics.SemanticMode.possible
        (result.persistentRequestAt index current epsilon positive count).cursor.machine.mode
        left)
    (rightPossible :
      Mode.Semantics.SemanticMode.possible
        (result.persistentRequestAt index current epsilon positive count).cursor.machine.mode
        right) :
    Geometry.Projective.Chordal.Basic.chordalSq
        (Data.CCL.Progressive.Cursor.Image.Machine.image
          (result.persistentRequestAt index current epsilon positive count).cursor.machine
          left)
        (Data.CCL.Progressive.Cursor.Image.Machine.image
          (result.persistentRequestAt index current epsilon positive count).cursor.machine
          right) ≤ epsilon ^ 2 :=
  current.request_cylinder_accurate epsilon positive count
    leftPossible rightPossible

/-- Every admitted cylinder candidate remains owned by this degree-indexed
initial isolated region.  This is the finite compatibility assertion used to
identify the persistent cylinder with the same Paper-I site. -/
theorem persistentRequestAt_candidate_in_initial_box
    {p : CoefficientPolynomial} (result :
      AdapterResult p)
    (index : Fin p.natDegree) (current : result.PersistentStateAt index)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) (count : Nat)
    {tail : Canonical}
    (possible :
      Mode.Semantics.SemanticMode.possible
        (result.persistentRequestAt index current epsilon positive count).cursor.machine.mode
        tail) :
    ∃ value : Canonical,
      (result.trackAt index).initial.box.Contains value ∧
        (Data.CCL.Progressive.Cursor.Image.Machine.image
          (result.persistentRequestAt index current epsilon positive count).cursor.machine
          tail).Equivalent (Geometry.Projective.Line.Proj.affine value) :=
  (result.persistentRequestAt index current epsilon positive count).candidate_in_initial_box
    possible
end Result
end Purelib.RootIsolation.FTA.Squarefree.AdapterResult

end
