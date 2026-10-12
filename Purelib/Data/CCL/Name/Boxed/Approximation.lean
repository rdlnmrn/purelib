module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Box
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Data.CCL.Name.Boxed.Process
public import Purelib.Data.Rat.Bounds.AccuracyRadius
import Purelib.Data.CCL.Name.Boxed.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Boxed CCL names as arithmetic enclosure processes

This is the deliberate one-way bridge from an ordinary raw CCL word plus a
finite rational box sidecar to the generic arithmetic process.  The raw
encoder, parser, and boxed-name definitions do not import this module.
-/

namespace Purelib.Data.CCL.Name.Boxed.Approximation
namespace ProgressiveName

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Name in
open Purelib.Data.Rat in
/-- Use the exact states and certificates of a progressive boxed name as a Gaussian approximation process.

Balls enclose the retained boxes; possible values and witnesses remain those of the same certificates. Refinement
delegates to the original request operation with a positive radius request, preserving its witness, containment and
initial-center bound. -/
def toProcess (name : Boxed.Process.ProgressiveName) :
  Approximation.Gaussian.Process where
  State := name.State
  ball state :=
    Enclosure.Ball.ofBox
      (name.certificate state).box
  Possible state value := (name.certificate state).Possible value
  witness state :=
    ⟨(name.certificate state).witness,
      (name.certificate state).witness_nonzero,
      (name.certificate state).witness_represented⟩
  possible_inside := by
    intro state value possible
    exact Enclosure.Ball.contains_ofBox
      ((name.certificate state).possible_inside possible)
  refine state target positive :=
    name.request state (Bounds.AccuracyRadius.accuracyRadius target) (Bounds.AccuracyRadius.accuracyRadius_pos positive)
  refine_persists := by
    intro state target positive value possible
    exact (name.request_refines state (Bounds.AccuracyRadius.accuracyRadius target)
      (Bounds.AccuracyRadius.accuracyRadius_pos positive)).possible_persists possible
  accurate := by
    intro state target positive
    exact (name.accurate state (Bounds.AccuracyRadius.accuracyRadius target)
      (Bounds.AccuracyRadius.accuracyRadius_pos positive)).trans_lt
        (Bounds.AccuracyRadius.accuracyRadius_sq_lt positive)
  centerBound := (name.certificate name.initial).box.normSqBound
  centerBound_nonneg :=
    (name.certificate name.initial).box.normSqBound_nonneg
  center_bounded := by
    intro state
    exact (name.certificate name.initial).box.normSq_le_normSqBound
      ((name.refinesInitial state).box.contains
        (name.certificate state).box.contains_anchor)

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Name in
/-- The approximation ball is exactly the ball of the same retained boxed certificate. -/
@[simp] theorem toProcess_ball (name :
  Boxed.Process.ProgressiveName) (state : name.State) :
    (toProcess name).ball state =
      Approximation.Gaussian.Enclosure.Ball.ofBox
        (name.certificate state).box := rfl

open Purelib.Data.CCL.Name in
open Purelib.Data.Gaussian in
/-- Approximation possibility is exactly possibility in the same retained boxed certificate. -/
theorem toProcess_possible (name :
  Boxed.Process.ProgressiveName)
    (state : name.State) (value : Basic.Canonical) :
    (toProcess name).Possible state value ↔
      (name.certificate state).Possible value := by
  rfl

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Name in
/-- Pair the boxed-name approximation process with its exact original initial state. -/
def toNamed (name : Boxed.Process.ProgressiveName) :
  Name.Basic.Named :=
  { process := (toProcess name)
    state := name.initial }
end ProgressiveName

end Purelib.Data.CCL.Name.Boxed.Approximation

end
