module

import Purelib.Data.List.Membership

/-!
# Retained finite-list membership decisions

These generic kernel checks compare complete membership decision records under
the same retained Boolean equality and lawfulness owners. Global and scoped
synthesis select the existing certificate, while explicitly supplied local
records retain precedence in both contexts.
-/

namespace Test.Data.List.Membership

open Purelib.Data.List.Membership (decidableMem)

/-- Infer a membership decision with the ordinary instance registration.

The target and finite list retain their original carrier, Boolean equality,
and lawfulness instances. No membership-specific scope or local decision
record is supplied during this synthesis. -/
def ordinaryDecision {Alpha : Type u} [BEq Alpha] [LawfulBEq Alpha]
    (target : Alpha) (values : List Alpha) : Decidable (target ∈ values) :=
  inferInstance

/-- Ordinary synthesis retains the complete existing membership decision record.

Kernel conversion compares the decision constructor and its proof field under
the same carrier, equality and lawfulness owners for every target and list. -/
theorem ordinary_record {Alpha : Type u} [BEq Alpha] [LawfulBEq Alpha]
    (target : Alpha) (values : List Alpha) :
    ordinaryDecision target values = decidableMem target values := rfl

/-- Infer membership while retaining an explicitly supplied local decision record.

The local record concerns this exact target and original list. Its installation
must take precedence over the ordinary global membership registration. -/
def ordinaryLocalDecision {Alpha : Type u} [BEq Alpha] [LawfulBEq Alpha]
    (target : Alpha) (values : List Alpha)
    (retained : Decidable (target ∈ values)) : Decidable (target ∈ values) :=
  letI := retained
  inferInstance

/-- Ordinary local synthesis returns the supplied complete decision record.

The arbitrary retained record remains the selected instance without rebuilding
its constructor or changing its certificate. -/
theorem ordinary_local_record {Alpha : Type u} [BEq Alpha] [LawfulBEq Alpha]
    (target : Alpha) (values : List Alpha)
    (retained : Decidable (target ∈ values)) :
    ordinaryLocalDecision target values retained = retained := rfl

section

open scoped Purelib.Data.List.Membership

/-- Infer a membership decision with its retained scope opened.

The same target, finite list, Boolean equality and lawfulness instances are
supplied. Opening the scope must retain the existing membership certificate. -/
def scopedDecision {Alpha : Type u} [BEq Alpha] [LawfulBEq Alpha]
    (target : Alpha) (values : List Alpha) : Decidable (target ∈ values) :=
  inferInstance

/-- Scoped synthesis retains the complete existing membership decision record.

Kernel conversion checks every decision constructor and retained proof field
under the original carrier, equality and lawfulness owners. -/
theorem scoped_record {Alpha : Type u} [BEq Alpha] [LawfulBEq Alpha]
    (target : Alpha) (values : List Alpha) :
    scopedDecision target values = decidableMem target values := rfl

/-- Infer membership with both its scope and an explicitly supplied local record.

The local record belongs to the same target and original list. Its installation
must take precedence even when both membership registrations are available. -/
def scopedLocalDecision {Alpha : Type u} [BEq Alpha] [LawfulBEq Alpha]
    (target : Alpha) (values : List Alpha)
    (retained : Decidable (target ∈ values)) : Decidable (target ∈ values) :=
  letI := retained
  inferInstance

/-- Scoped local synthesis returns the supplied complete decision record.

The arbitrary retained constructor and its certificate remain unchanged when
the membership scope is opened. -/
theorem scoped_local_record {Alpha : Type u} [BEq Alpha] [LawfulBEq Alpha]
    (target : Alpha) (values : List Alpha)
    (retained : Decidable (target ∈ values)) :
    scopedLocalDecision target values retained = retained := rfl

end

end Test.Data.List.Membership
