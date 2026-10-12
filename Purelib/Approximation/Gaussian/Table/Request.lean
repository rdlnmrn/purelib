module
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Refinement
public import Purelib.Approximation.Gaussian.Table.Basic
public import Purelib.Approximation.Rational.Request.Common
import Init.Prelude
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Process.Coherence.Basic (Coherent)
open Purelib.Approximation.Gaussian.Table.Basic (ChannelTable)

section

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Table.Basic
open Purelib.Data.Rat

public section

namespace Purelib.Approximation.Gaussian.Table.Request

/-!
# Joint finite requests for coherent CCL tables

Higher jets, local polynomial models, and finite-dimensional directional data
all consist of a displayed finite list of coherent CCL channels.  This module
computes one rational request shared by every list entry.  Membership in the
finite list is enough to recover strict enclosure and semantic-allowance
bounds, persistent prefix growth, and exact parser semantics for that entry.

The recursion is over the displayed list.  There is no unbounded coordinate
space, infimum, completed vector, or quantified family of all coefficients.
-/

/-- Fold a visible target through the finitely many semantic-coherence moduli. -/
@[expose] def requestTarget : List Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed →
  Purelib.Data.Rat.Fraction.Rational → Purelib.Data.Rat.Fraction.Rational
  | [], target => target
  | channel :: remaining, target =>
      Coherent.commonRequest
        (requestTarget remaining target)
        (channel.coherent.accuracyRequest target)

/-- The shared finite-table request is positive for every positive target. -/
theorem requestTarget_pos : ∀ (channels : List CoherentNamed)
    {target : Fraction.Rational}, 0 < target → 0 < requestTarget channels target
  | [], _target, positive => positive
  | channel :: remaining, _target, positive =>
      Coherent.commonRequest_pos
        (requestTarget_pos remaining positive)
        (channel.coherent.accuracyRequest_pos positive)

/-- The shared finite-table request is no larger than the original positive target. -/
theorem requestTarget_le_target : ∀ (channels : List CoherentNamed)
    {target : Fraction.Rational}, 0 < target → requestTarget channels target ≤
      target
  | [], _target, _positive => le_rfl
  | channel :: remaining, _target, positive =>
      (Coherent.commonRequest_lt_left
        (requestTarget_pos remaining positive)
        (channel.coherent.accuracyRequest_pos positive)).le.trans
          (requestTarget_le_target remaining positive)

/-- The shared request is strictly below the semantic accuracy request of every retained table member. -/
theorem requestTarget_lt_accuracy_of_mem :
    ∀ (channels : List CoherentNamed) {channel : CoherentNamed}
      (_member : channel ∈ channels) {target : Fraction.Rational}, 0 < target →
        requestTarget channels target <
          channel.coherent.accuracyRequest target
  | [], _channel, member, _target, _positive => by
      nomatch member
  | head :: remaining, channel, member, target, positive => by
      rcases Purelib.Data.List.Membership.mem_cons.mp member with equal | tailMember
      · subst head
        exact
          Coherent.commonRequest_lt_right
            (requestTarget_pos remaining positive)
            (channel.coherent.accuracyRequest_pos positive)
      · exact
          (Coherent.commonRequest_lt_left
            (requestTarget_pos remaining positive)
            (head.coherent.accuracyRequest_pos positive)).trans
              (requestTarget_lt_accuracy_of_mem remaining tailMember
                positive)

/-- Rebase one member at the request shared by its whole finite table. -/
@[expose] def sharedName (channels : List CoherentNamed) (channel : CoherentNamed)
    (target : Fraction.Rational) (positive : 0 < target) : Named :=
  Refinement.refined channel.name
    (requestTarget channels target)
      (requestTarget_pos channels positive)

/-- Refinement by the table's shared request makes the displayed channel enclosure radius smaller than the positive
target. -/
theorem sharedName_radius_lt (channels : List CoherentNamed)
    (channel : CoherentNamed) {target : Fraction.Rational} (positive : 0 < target) :
    ((sharedName channels channel target positive).process.ball
      (sharedName channels channel target positive).state).radiusSq < target :=
  (Refinement.refined_error channel.name
    (requestTarget channels target)
    (requestTarget_pos channels positive)).trans_le
      (requestTarget_le_target channels positive)

set_option genInjectivity false in
/-- One shared-table refinement and its evaluated enclosure, retained at the original request.

The channel order, original channel and positive target index the result. Its
name and ball equations identify the actual refinement and enclosure separately;
reading the two scalar fields never performs another refinement or evaluation. -/
structure PreparedEntry (channels : List CoherentNamed) (channel : CoherentNamed)
    (target : Fraction.Rational) (positive : 0 < target) where
  /-- The actual name returned by the shared positive request. -/ name : Named
  /-- The retained name is the refinement selected by the original shared table. -/ name_eq :
    name = sharedName channels channel target positive
  /-- The enclosure evaluated once at the retained name's selected state. -/ ball : Gaussian.Enclosure.Ball
  /-- The cached enclosure is the exact ball of the retained name. -/ ball_eq : ball = name.process.ball name.state
  /-- The evaluated enclosure meets the original strict squared-radius target. -/ accurate : ball.radiusSq < target

end Purelib.Approximation.Gaussian.Table.Request

open Purelib.Approximation.Gaussian.Table.Request (PreparedEntry)

section

variable {channels : List CoherentNamed} {channel : CoherentNamed}
    {target : Fraction.Rational} {positive : 0 < target}
    (prepared : PreparedEntry channels channel target positive)

namespace Purelib.Approximation.Gaussian.Table.Request.PreparedEntry

/-- Read the center directly from the retained enclosure. -/
@[expose] def center : Data.Gaussian.Basic.Canonical := prepared.ball.center

/-- Read the squared radius directly from the same retained enclosure. -/
@[expose] def radiusSq : Fraction.Rational := prepared.ball.radiusSq

/-- The cached enclosure is the ball selected by the original shared request. -/
theorem ball_readback : prepared.ball =
    (sharedName channels channel target positive).process.ball
      (sharedName channels channel target positive).state :=
  prepared.ball_eq.trans
    (congrArg (fun name : Named => name.process.ball name.state) prepared.name_eq)

/-- Both scalar reads project the same evaluated enclosure. -/
theorem readings_readback : (prepared.center, prepared.radiusSq) =
    (prepared.ball.center, prepared.ball.radiusSq) := rfl

/-- The retained squared radius is nonnegative. -/
theorem radiusSq_nonneg : 0 ≤ prepared.radiusSq := prepared.ball.radiusSq_nonneg

/-- The retained squared radius satisfies the original strict request. -/
theorem radiusSq_lt_target : prepared.radiusSq < target := prepared.accurate

end Purelib.Approximation.Gaussian.Table.Request.PreparedEntry

end

namespace Purelib.Approximation.Gaussian.Table.Request

/-- Refine one channel once and evaluate its selected enclosure once.

The shared target uses the original ordered channels. All subsequent center,
radius and accuracy reads consume the returned result instead of its producer. -/
@[expose] def prepareEntry (channels : List CoherentNamed) (channel : CoherentNamed)
    (target : Fraction.Rational) (positive : 0 < target) : PreparedEntry channels channel target positive :=
  let name := sharedName channels channel target positive
  let ball := name.process.ball name.state
  { name := name, name_eq := rfl, ball := ball, ball_eq := rfl
    accurate := sharedName_radius_lt channels channel positive }

/-- Refinement by the table's shared request makes every member's coherence allowance smaller than the positive target.
-/
theorem sharedName_allowance_lt (channels : List CoherentNamed)
    {channel : CoherentNamed} (member : channel ∈ channels)
    {target : Fraction.Rational} (positive : 0 < target) :
    channel.coherent.allowance
        (sharedName channels channel target positive).state < target :=
  channel.coherent.refine_accurate channel.name.state target positive
    (requestTarget channels target)
      (requestTarget_pos channels positive)
    (requestTarget_lt_accuracy_of_mem channels member positive)

end Purelib.Approximation.Gaussian.Table.Request

section

namespace Purelib.Approximation.Gaussian.Table.Basic.ChannelTable

/-- Compute the common positive-request budget for all channels in the retained finite table. -/
@[expose] def sharedTarget (table :
  ChannelTable) (target : Fraction.Rational) : Fraction.Rational :=
  Purelib.Approximation.Gaussian.Table.Request.requestTarget table.channels target

/-- The table's common request budget is positive when the target is positive. -/
theorem sharedTarget_pos (table :
  ChannelTable) {target : Fraction.Rational}
    (positive : 0 < target) : 0 < table.sharedTarget target :=
  Purelib.Approximation.Gaussian.Table.Request.requestTarget_pos table.channels positive

/-- The actual list of same-budget CCL names returned by one table request. -/
@[expose] def requestNames (table :
  ChannelTable) (target : Fraction.Rational)
    (positive : 0 < target) : List Named :=
  table.channels.map
    (fun channel => Purelib.Approximation.Gaussian.Table.Request.sharedName table.channels channel target positive)

/-- A shared table request preserves the number of channels. -/
@[simp] theorem requestNames_length (table :
  ChannelTable) (target : Fraction.Rational)
    (positive : 0 < target) :
    (table.requestNames target positive).length = table.length := by
  exact Purelib.Data.List.Map.length_map _ _

/-- Centres of all channels after the table's one shared request. -/
@[expose] def requestCenters (table :
  ChannelTable) (target : Fraction.Rational)
    (positive : 0 < target) : List Data.Gaussian.Basic.Canonical :=
  table.channels.map fun channel =>
    ((Purelib.Approximation.Gaussian.Table.Request.sharedName table.channels channel target positive).process.ball
      (Purelib.Approximation.Gaussian.Table.Request.sharedName table.channels channel target positive).state).center

end Purelib.Approximation.Gaussian.Table.Basic.ChannelTable

end

end

end
