module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Request
import Purelib.Data.CCL.Progressive.Cursor.Image
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.CCL.Request
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.CCL.Transducer.Mode.Semantics
import Purelib.Geometry.Projective.Chordal.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Calculus.Jet.Progressive.Quadratic (Program)
open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

/-!
# One certified finite program for progressive quadratic CCL calculus

The lower trace modules construct the arithmetic and analytic certificates.
This file packages those constructors into one indexed finite program.  The
index is the actual semantic `Trace`, so a program cannot pair unrelated value
and slope names: every node computes one common increment, base, output,
slope, remainder, and rational quadratic factor.

Partial nodes store their displayed lower-quadrance or disk evidence in the
constructor.  The total decision wrappers expose a precise missing
certificate.  Finally, the strengthened request contract combines the
quadratic law with persistent word extension, exact raw-parser semantics, and
the requested projective-cylinder diameter for every one of the five live CCL
channels.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic
namespace Calculation

open Purelib.Approximation.Gaussian.Name.Coherent.CCL.Cursor in
open Purelib.Geometry.Projective.Chordal in
open Purelib.Data in
/-- Persistent word, parser and projective-cylinder guarantees for one channel request.

The request uses a positive rational target and a finite bit count. Its emitted word extends the old word by exactly
that count, its cursor retains exact semantics, and any two permitted residual values have images within the target
chordal bound. -/
structure EntryRequestContract
    (entry : Basic.ChannelCursor)
    (target : Rational) (positive : 0 < target) (count : Nat) : Prop where
  /-- The original emitted word is a prefix of the requested word. -/ word_extends :
    entry.cursor.machine.emitted.IsPrefix
    (entry.request target positive count).cursor.machine.emitted
  /-- The requested emitted word gains exactly the specified number of bits. -/ word_length :
    (entry.request target positive count).cursor.machine.emitted.length =
      entry.cursor.machine.emitted.length + count
  /-- The requested machine retains exact semantics for the original process and root state. -/ exact :
    CCL.Transducer.Machine.Semantics.Basic.ExactCursor entry.channel.name.process entry.rootState
    (entry.request target positive count).cursor.machine
  /-- Images of any two permitted residual values have squared chordal distance at most the target. -/ cylinder : ∀
    {left right : Canonical},
    CCL.Transducer.Mode.Semantics.SemanticMode.possible
        (entry.request target positive count).cursor.machine.mode left →
      CCL.Transducer.Mode.Semantics.SemanticMode.possible
        (entry.request target positive count).cursor.machine.mode right →
      Basic.chordalSq
          (CCL.Progressive.Cursor.Image.Machine.image (entry.request target positive count).cursor.machine left)
          (CCL.Progressive.Cursor.Image.Machine.image (entry.request target positive count).cursor.machine right) ≤
        target

open Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic in
open Purelib.Data in
/-- The common quadratic request law and all five persistent channel guarantees.

The calculation's trace selects one refinement index. Every cursor entry initialized at that index satisfies the entry
request contract at the same positive target and bit count. -/
structure PersistentRequestContract
  {increment : Nat → Canonical}
    (calculation : Calculation increment) (current : Nat)
    (target : Rational) (positive : 0 < target) (count : Nat) : Prop where
  /-- The retained trace satisfies the common-index quadratic request contract. -/ quadratic :
    Trace.RequestContract
      calculation.trace current target positive count
  /-- Each cursor entry at the selected common index satisfies its persistent request contract. -/ entries : ∀ entry,
    entry ∈ (calculation.trace.cursorTableAt
      (calculation.trace.requestIndex current target)).entries →
      EntryRequestContract entry target positive count

open Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic in
open Purelib.Data in
/-- Every certified calculation satisfies its persistent finite request contract.

The trace supplies the common-index quadratic law, while each channel request extends its word and preserves parser
semantics and the projective-cylinder bound. -/
theorem
  persistent_bitstream_and_quadratic_law
    {increment : Nat → Canonical} (calculation : Calculation increment)
    (current : Nat) (target : Rational) (positive : 0 < target)
    (count : Nat) :
    PersistentRequestContract calculation current target positive count := by
  refine
    { quadratic := calculation.trace.bitstream_and_quadratic_law
        current target positive count
      entries := ?_ }
  intro entry member
  exact
    { word_extends := entry.request_word_extends target positive count
      word_length := entry.request_word_length target positive count
      exact := entry.request_exact target positive count
      cylinder := by
        intro left right leftPossible rightPossible
        exact entry.request_pair_chordalSq_le target positive count
          leftPossible rightPossible }
end Calculation

end Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic

end
