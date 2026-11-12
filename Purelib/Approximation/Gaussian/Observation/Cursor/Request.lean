module

public import Purelib.Computation.Query.History
public import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.List.Prefix

/-!
# Numerical cursor requests and their exact payments

A bit request extends the actual preceding word by its supplied count. An
enclosure request pays its original strictly positive squared allowance.
Payment certificates preserve the original rational reading and word,
while intrinsic code validity remains with each representation owner.
-/

public section

namespace Purelib.Approximation.Gaussian.Observation.Cursor

open Purelib.Computation.Query
open Purelib.Data
open Purelib.Data.Rat

set_option genInjectivity false in
/-- A numerical cursor request asks for additional prefix bits or a strictly positive squared-chordal allowance. -/
inductive Request where
  /-- Extend the exact already exposed word by this additional finite count. -/ | bits (count : Nat)
  /-- Refine the same retained chart to this positive squared-chordal target. -/ | enclosure
      (target : Fraction.Rational) (positive : 0 < target)

namespace Request

/-- Compare numerical request data while ignoring their proof certificates. -/
instance : DecidableEq Request := fun left right => by
  cases left with
  | bits left =>
      cases right with
      | enclosure _ _ => exact .isFalse (fun impossible => by nomatch impossible)
      | bits right =>
          exact if equal : left = right then .isTrue (equal ▸ rfl)
            else .isFalse (fun same => equal (by cases same; rfl))
  | enclosure left leftPositive =>
      cases right with
      | bits _ => exact .isFalse (fun impossible => by nomatch impossible)
      | enclosure right rightPositive =>
          exact if equal : left = right then .isTrue (by cases equal; rfl)
            else .isFalse (fun same => equal (by cases same; rfl))

end Request

namespace Request

universe u v w

set_option genInjectivity false in
/-- A request payment retains the common reading, original prefix and exact count or strict allowance.

The supplied projections read the same original preceding and next code owners.
The tagged request determines which numerical obligation must be paid.
-/
structure Payment {Code : Type u} {Point : Type v} (point : Code → Point)
    (word : Code → List Bool) (allowance : Code → Fraction.Rational)
    (earlier next : Code) (request : Request) : Prop where
  /-- The same rational reading survives this request. -/ pointEq : point next = point earlier
  /-- The exact previously exposed word persists. -/ wordPrefix : (word earlier).IsPrefix (word next)
  /-- An additional-bit request pays its original count. -/ length :
    ∀ count, request = .bits count → (word next).length = (word earlier).length + count
  /-- An enclosure request pays its original strictly positive squared target. -/ accurate :
    ∀ target positive, request = .enclosure target positive → allowance next < target

set_option genInjectivity false in
/-- A saved transition retains intrinsic next-code validity and its complete numerical payment.

The validity predicate belongs to the representation of the same cached next
code. Its common payment refers to the original preceding code and request.
-/
structure ValidStep {Code : Type u} {Point : Type v} (point : Code → Point)
    (word : Code → List Bool) (allowance : Code → Fraction.Rational) (valid : Code → Prop)
    (earlier : Code) (step : History.Step Request Code) : Prop extends
    Payment point word allowance earlier step.next step.request where
  /-- The exact retained next code has its intrinsic representation validity. -/ nextValid : valid step.next

set_option genInjectivity false in
/-- A prepared transition retains independent next-code checks and complete numerical payment before containment.

Only candidate containment is omitted. The retained prepared predicate and
payment certify the original next code and exact tagged request.
-/
structure PreparedStep {Code : Type u} {Point : Type v} (point : Code → Point)
    (word : Code → List Bool) (allowance : Code → Fraction.Rational) (prepared : Code → Prop)
    (earlier : Code) (step : History.Step Request Code) : Prop extends
    Payment point word allowance earlier step.next step.request where
  /-- The exact retained next code passed its independent checks. -/ next : prepared step.next

set_option genInjectivity false in
/-- A saved request identifies the exact next-code, reading, prefix, count or allowance condition that failed.

The original code-defect family remains representation-specific. Every payment
defect identifies and refutes the corresponding condition on the supplied codes.
-/
inductive StepInvalid {Code : Type u} {Point : Type v} (point : Code → Point)
    (word : Code → List Bool) (allowance : Code → Fraction.Rational) (invalid : Code → Type w)
    (earlier : Code) (step : History.Step Request Code) where
  /-- The original next code has this identified intrinsic defect. -/ | next (reason : invalid step.next)
  /-- The request changed its original rational reading. -/ | point (failed : point step.next ≠ point earlier)
  /-- The request lost part of the actual previously exposed word. -/ | wordPrefix
      (failed : ¬ (word earlier).IsPrefix (word step.next))
  /-- This bit request failed its original additional count. -/ | length (count : Nat)
      (requestEq : step.request = .bits count)
      (failed : (word step.next).length ≠ (word earlier).length + count)
  /-- This enclosure request failed its original strict positive target. -/ | accurate
      (target : Fraction.Rational) (positive : 0 < target) (requestEq : step.request = .enclosure target positive)
      (failed : ¬ allowance step.next < target)

namespace StepInvalid

/-- An identified request defect refutes preparation of this same retained transition. -/
theorem refutes {Code : Type u} {Point : Type v} {point : Code → Point}
    {word : Code → List Bool} {allowance : Code → Fraction.Rational}
    {prepared : Code → Prop} {invalid : Code → Type w}
    (refute : ∀ code, invalid code → ¬ prepared code)
    {earlier : Code} {step : History.Step Request Code}
    (reason : StepInvalid point word allowance invalid earlier step) :
    ¬ PreparedStep point word allowance prepared earlier step := by
  intro checked
  cases reason with
  | next reason => exact refute step.next reason checked.next
  | point failed => exact failed checked.pointEq
  | wordPrefix failed => exact failed checked.wordPrefix
  | length count requestEq failed => exact failed (checked.length count requestEq)
  | accurate target positive requestEq failed => exact failed (checked.accurate target positive requestEq)

end StepInvalid

/-- Check one original saved request after its intrinsic next-code check.

The order is intrinsic validity, common reading, preceding word, then tagged
request payment. Failure retains that same code, request and violated condition.
-/
def prepareStep {Code : Type u} {Point : Type v} [DecidableEq Point]
    (point : Code → Point) (word : Code → List Bool) (allowance : Code → Fraction.Rational)
    {prepared : Code → Prop} {invalid : Code → Type w}
    (prepareCode : (code : Code) → Except (invalid code) (PLift (prepared code)))
    (earlier : Code) (step : History.Step Request Code) :
    Except (StepInvalid point word allowance invalid earlier step)
      (PLift (PreparedStep point word allowance prepared earlier step)) :=
  match prepareCode step.next with
  | .error reason => .error (.next reason)
  | .ok next =>
      if pointEq : point step.next = point earlier then
        letI := List.Prefix.decidable (word earlier) (word step.next)
        if wordPrefix : (word earlier).IsPrefix (word step.next) then
          match requestEq : step.request with
          | .bits count =>
              if length : (word step.next).length = (word earlier).length + count then
                .ok ⟨{ next := next.down
                       pointEq := pointEq
                       wordPrefix := wordPrefix
                       length := by
                         intro requested same
                         cases requestEq.symm.trans same
                         exact length
                       accurate := by
                         intro _ _ impossible
                         nomatch requestEq.symm.trans impossible }⟩
              else .error (.length count requestEq length)
          | .enclosure target positive =>
              if accurate : allowance step.next < target then
                .ok ⟨{ next := next.down
                       pointEq := pointEq
                       wordPrefix := wordPrefix
                       length := by
                         intro _ impossible
                         nomatch requestEq.symm.trans impossible
                       accurate := by
                         intro requested requestedPositive same
                         cases requestEq.symm.trans same
                         exact accurate }⟩
              else .error (.accurate target positive requestEq accurate)
        else .error (.wordPrefix wordPrefix)
      else .error (.point pointEq)

end Request

end Purelib.Approximation.Gaussian.Observation.Cursor

end
