module
meta import Purelib.Elab.ConstructiveInjectivity
meta import Mathlib.Tactic.TypeStar

@[expose] public section
namespace Test.Elab.ConstructorContexts

set_option genInjectivity false in
/-- An owner with two original universe labels. -/
structure Mixed.{u, v} (α : Type u) (β : Type v) where
  /-- The first typed entry. -/ first : α
  /-- The second typed entry. -/ second : β

universe u
constructive_injectivity Mixed

set_option genInjectivity false in
/-- A pair used under an unrelated explicitly included proof. -/
structure Included where
  /-- The first entry. -/ first : Nat
  /-- The second entry. -/ second : Nat

section
variable (h : True)
include h
constructive_injectivity Included
omit h in
/-- An unrelated included proof does not become a constructor-certificate parameter. -/
theorem includedCertificate (first second otherFirst otherSecond : Nat) :
    Included.mk first second = Included.mk otherFirst otherSecond ↔
      first = otherFirst ∧ second = otherSecond :=
  Included.mk.injEq first second otherFirst otherSecond

/-- The original surrounding include remains available. -/
theorem surrounding : True := h
end

/-- A conditional proof domain with both truth branches. -/
def ProofDomain (b : Bool) : Prop := if b then True else False
/-- A conditional data domain with both data branches. -/
def DataDomain (b : Bool) : Type := if b then Nat else Unit

set_option genInjectivity false in
/-- Fields retain conditional proof and data domains at both Boolean inputs. -/
structure Conditional where
  /-- A proof in the true branch. -/ yesProof : ProofDomain true
  /-- A proof in the false branch. -/ noProof : ProofDomain false
  /-- Data in the true branch. -/ yesData : DataDomain true
  /-- Data in the false branch. -/ noData : DataDomain false
constructive_injectivity Conditional

set_option genInjectivity false in
/-- A constructor retaining an optional field annotation. -/
structure Optional where
  /-- The optional entry. -/ entry : Nat := 0
constructive_injectivity Optional

namespace Ambient
variable {K : Type*} [Inhabited K]
set_option genInjectivity false in
/-- An owner retains a universe introduced by an ambient Type* variable. -/
structure Holder (K : Type*) [Inhabited K] where
  /-- The typed scalar entry. -/ value : K
constructive_injectivity Holder
namespace Nested
variable {holder : Holder K}
set_option genInjectivity false in
/-- A nested owner retains the same ambient auto-generated universe. -/
structure Witness (holder : Holder K) where
  /-- The retained typed entry. -/ value : K
constructive_injectivity Witness
end Nested
end Ambient
/-- Conditional proof fields are omitted while both original conditional data domains are retained. -/
private theorem conditionalCertificate
    (yes otherYes : ProofDomain true) (no otherNo : ProofDomain false)
    (yesData otherYesData : DataDomain true) (noData otherNoData : DataDomain false) :
    Conditional.mk yes no yesData noData = Conditional.mk otherYes otherNo otherYesData otherNoData ↔
      yesData = otherYesData ∧ noData = otherNoData :=
  Conditional.mk.injEq yes no yesData noData otherYes otherNo otherYesData otherNoData

/-- Optional data fields keep their executable default after certificate generation. -/
private theorem optionalDefault : ({} : Optional).entry = 0 := rfl

end Test.Elab.ConstructorContexts
end
