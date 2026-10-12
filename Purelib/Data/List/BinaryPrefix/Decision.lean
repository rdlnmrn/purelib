module
public import Purelib.Data.List.BinaryPrefix.Basic

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.List.BinaryPrefix

open Purelib.Data.List.BinaryPrefix.Basic

open Purelib.Data.List.BinaryPrefix.Basic renaming SourceEncodingRawParserWordAlias -> Word

section
@[expose] public section

/-!
# Finite raw-prefix parser over constructive Gaussian fractions

The completed-block encoder is not enough for a persistent root name: a
request may stop inside a unary header or after only one or two sector bits.
This module records exactly that unfinished syntax, the finite decoder
product, and the finite list of already completed block constraints.  It is
the state needed by the box/CCL next-bit controller; no stream, completion,
or collection of compatible points is formed.
-/

namespace Purelib.Data.List.BinaryPrefix.Decision

/-- Test whether one displayed Boolean word is a prefix of another.

Direct recursion compares corresponding bits and accepts an exhausted first word. A
shorter second word or a mismatching bit rejects the test. -/
def isWordPrefix : Word → Word → Bool
  | [], _ => true
  | _ :: _, [] => false
  | false :: earlier, false :: later => isWordPrefix earlier later
  | true :: earlier, true :: later => isWordPrefix earlier later
  | false :: _, true :: _ => false
  | true :: _, false :: _ => false

/-- The executable Boolean-word prefix test is transitive on successful checks. -/
theorem isWordPrefix_trans {first second third : Word}
    (firstSecond : isWordPrefix first second = true)
    (secondThird : isWordPrefix second third = true) :
    isWordPrefix first third = true := by
  induction first generalizing second third with
  | nil => rfl
  | cons firstBit firstTail inductionHypothesis =>
      cases second with
      | nil =>
          cases firstBit <;> exact Bool.noConfusion firstSecond
      | cons secondBit secondTail =>
          cases third with
          | nil =>
              cases secondBit <;> exact Bool.noConfusion secondThird
          | cons thirdBit thirdTail =>
              cases firstBit <;> cases secondBit <;> cases thirdBit
              · exact inductionHypothesis firstSecond secondThird
              · exact Bool.noConfusion secondThird
              · exact Bool.noConfusion firstSecond
              · exact Bool.noConfusion firstSecond
              · exact Bool.noConfusion firstSecond
              · exact Bool.noConfusion firstSecond
              · exact Bool.noConfusion secondThird
              · exact inductionHypothesis firstSecond secondThird

end Purelib.Data.List.BinaryPrefix.Decision

end
