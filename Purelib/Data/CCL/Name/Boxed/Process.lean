module
import Purelib.Data.Rat.Fraction
import Purelib.Data.CCL.Name.Boxed.Basic
public import Purelib.Data.CCL.Name.Boxed.Refinement
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Finite boxed CCL names

This module formalizes the operational boxed-name interface independently of
arithmetic.  A certificate contains one ordinary finite raw word, one
rational box, and one displayed nonzero rational witness.  A progressive
name returns only further finite certificates.  It never forms a completed
bitstream, a completed complex value, or an intersection of all boxes.
-/

namespace Purelib.Data.CCL.Name.Boxed.Process

open Purelib.Data.CCL.Name in
open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Retain an executable family of boxed names with requested refinement and quantitative accuracy.

Each state owns its exact boxed certificate. A positive rational request returns another state refining that same
certificate, with squared diagonal at most the request squared; every state also refines the retained initial
certificate. -/
structure ProgressiveName where
  /-- The executable state carrier of this boxed-name family. -/ State : Type
  /-- The exact boxed-name certificate retained by each state. -/ certificate : State → Boxed.Basic.Certificate
  /-- The retained initial state of the boxed-name family. -/ initial : State
  /-- Produce a state for the supplied positive rational accuracy request. -/ request : (state : State) → (epsilon :
    Fraction.Rational) → 0 < epsilon → State
  /-- The requested state's exact certificate refines the supplied state's certificate. -/ request_refines : ∀ state
    epsilon positive,
    Boxed.Refinement.Refines (certificate (request state epsilon positive))
      (certificate state)
  /-- The requested certificate's squared diagonal is at most the positive request squared. -/ accurate : ∀ state
    epsilon positive,
    (certificate (request state epsilon positive)).box.diagonalSq ≤
      epsilon ^ 2
  /-- Every state's exact certificate refines the same retained initial certificate. -/ refinesInitial : ∀ state,
    Boxed.Refinement.Refines (certificate state) (certificate initial)

constructive_injectivity ProgressiveName

namespace ProgressiveName

open Purelib.Data.CCL.Name in
open Purelib.Data.Rat in
/-- Every requested boxed name refines the same retained initial certificate. -/
theorem request_refines_initial (name :
  ProgressiveName)
    (state : name.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Boxed.Refinement.Refines (name.certificate (name.request state epsilon positive))
      (name.certificate name.initial) :=
  (name.request_refines state epsilon positive).trans
    (name.refinesInitial state)

open Purelib.Data.CCL.Name in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A requested witness stays within the old certificate's squared diagonal of its retained witness. -/
theorem request_witness_distance_le (name :
  ProgressiveName)
    (state : name.State) (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    Data.Gaussian.Norm.Basic.normSq
        ((name.certificate (name.request state epsilon positive)).witness -
          (name.certificate state).witness) ≤
      (name.certificate state).box.diagonalSq :=
  (name.request_refines state epsilon positive).witness_distance_le

end ProgressiveName

end Purelib.Data.CCL.Name.Boxed.Process

end

public section
namespace Purelib.Data.CCL.Name.Boxed.Process

open Purelib.Data.CCL.Name
open Purelib.Data.Rat

end Purelib.Data.CCL.Name.Boxed.Process
end
