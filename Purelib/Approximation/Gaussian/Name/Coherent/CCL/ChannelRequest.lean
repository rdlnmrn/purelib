module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.CCL.Semantics
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Request
import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Init.Prelude
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

section

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Progressive CCL observations of quadratic jet certificates

This module connects the displayed quadratic-change certificates to the
productive CCL layer.  A `CertifiedCalculation` stores one finite rational
certificate, not five unrelated channels.  Its input increment, base value,
output value, slope, and remainder are then exposed as terminating coherent
CCL names.  One request returns certified enclosures and persistent raw CCL
prefixes for all five fields.

This is the exact-input specialization needed by the general progressive jet
construction.  Nothing here turns a non-rational result into a completed
value: the only exact channels introduced below are fields already present in
the supplied Gaussian-rational certificate.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.CCL

set_option genInjectivity false in
/-- One channel request, including both its semantic allowance and its actual persistent CCL cursor. -/
structure ChannelRequest (channel : CoherentNamed) (target : Fraction.Rational)
    (positive : 0 < target) (count : Nat) where
  /-- The retained refined output name used for both the enclosure and the finite bit request. -/ named :
    Gaussian.Name.Basic.Named
  /-- The retained name is exactly the original channel refined to its computed internal target. -/ named_eq : named =
    Refinement.refined channel.name
    (Request.channelTarget channel target) (Request.channelTarget_pos channel positive)
  /-- The ball at the retained output state has squared radius below the requested target. -/ radius_lt :
    (named.process.ball named.state).radiusSq < target
  /-- The original channel's semantic allowance at its refined state is below the requested target. -/ allowance_lt :
    channel.coherent.allowance
    (Refinement.refined channel.name
      (Request.channelTarget channel target)
      (Request.channelTarget_pos channel positive)).state < target
  /-- The finite bit request extends the retained name's initial emitted prefix. -/ prefix_preserved :
    named.machine.emitted.IsPrefix
    (Advance.advance
      named.machine count).emitted
  /-- The finite bit request emits exactly the requested number of bits. -/ emitted_length :
    (Advance.advance
      named.machine count).emitted.length = count
  /-- The resulting cursor has exact parser semantics relative to the retained name and state. -/ exact_cursor :
    Semantics.Basic.ExactCursor
    named.process named.state
    (Advance.advance named.machine count)

constructive_injectivity ChannelRequest

namespace ChannelRequest

/-- Execute one finite enclosure-and-prefix request against a coherent channel. -/
def requestChannel (channel : CoherentNamed) (target : Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    ChannelRequest channel target positive count := by
  let named := Refinement.refined channel.name
    (Request.channelTarget channel target) (Request.channelTarget_pos channel positive)
  exact
    { named := named
      named_eq := rfl
      radius_lt :=
        (Refinement.refined_error channel.name
          (Request.channelTarget channel target)
          (Request.channelTarget_pos channel positive)).trans
            (Request.channelTarget_lt_target channel positive)
      allowance_lt := channel.coherent.refine_accurate channel.name.state
        target positive (Request.channelTarget channel target)
        (Request.channelTarget_pos channel positive)
        (Request.channelTarget_lt_allowanceRequest channel positive)
      prefix_preserved := (named.productive count).1
      emitted_length := (named.productive count).2
      exact_cursor :=
        CCL.Semantics.Named.advance_exact
          named count }

end ChannelRequest

end Purelib.Approximation.Gaussian.Name.Coherent.CCL

end

end
