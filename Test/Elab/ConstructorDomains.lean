module

meta import Purelib.Elab.ConstructiveInjectivity
import Test.Elab.ConstructorExposure

public section
namespace Test.Elab.ConstructorDomains

universe u

set_option genInjectivity false in
/-- A scalar field with an original optional lower bound. -/
structure Optional (minimum : Nat := 0) where
  /-- The retained scalar value. -/ value : Nat
  /-- The retained lower bound. -/ above : minimum ≤ value

constructive_injectivity Optional

set_option genInjectivity false in
/-- A scalar budget retaining its original automatic proof field. -/
structure AutoBudget where
  /-- The retained budget. -/ budget : Nat
  /-- The exact scalar budget. -/ exact : budget = 1 := by rfl

constructive_injectivity AutoBudget

set_option genInjectivity false in
/-- A higher-universe state action with a polymorphic callback result. -/
structure Polymorphic (State : Type u) where
  /-- The original polymorphic state restoration operation. -/ restore :
    {Result : Type} → State → (State → IO Result) → IO Result

constructive_injectivity Polymorphic

set_option genInjectivity false in
/-- A scalar field retaining its original local type expression. -/
structure LetField where
  /-- The original local type expression. -/ value : let carrier := Nat; carrier

set_option cleanup.letToHave false in
constructive_injectivity LetField

/-- Optional constructor parameters keep their original bound in both applications. -/
private theorem optionalCertificate (first second : Nat) (firstBound : 0 ≤ first) (secondBound : 0 ≤ second) :
    Optional.mk (minimum := 0) first firstBound = Optional.mk (minimum := 0) second secondBound ↔ first = second :=
  Optional.mk.injEq (minimum := 0) first firstBound second secondBound

/-- Automatic proof fields retain arbitrary original witnesses without a field relation. -/
private theorem automaticCertificate (firstProof secondProof : (1 : Nat) = 1) :
    AutoBudget.mk 1 firstProof = AutoBudget.mk 1 secondProof ↔ (1 : Nat) = 1 :=
  AutoBudget.mk.injEq 1 firstProof 1 secondProof

/-- Constructor defaults still build the same retained budget and original proof field. -/
private theorem automaticDefault : (AutoBudget.mk 1).budget = 1 := rfl

/-- The whole polymorphic callback is compared without specializing its result type. -/
private theorem callbackCertificate {State : Type u}
    (first second : {Result : Type} → State → (State → IO Result) → IO Result) :
    Polymorphic.mk (@first) = Polymorphic.mk (@second) ↔ (@first) = (@second) :=
  Polymorphic.mk.injEq (@first) (@second)

/-- Original local type expressions remain usable in complete constructor applications. -/
private theorem localDomainCertificate (first second : let carrier := Nat; carrier) :
    LetField.mk first = LetField.mk second ↔ first = second :=
  LetField.mk.injEq first second

/-- An ordinary client imports the public opaque certificates from an exposed owner. -/
private theorem importedPublicCertificate {α : Type u} (first second otherFirst otherSecond : α) :
    Test.Elab.ConstructorExposure.Pair.mk first second =
      Test.Elab.ConstructorExposure.Pair.mk otherFirst otherSecond ↔
      first = otherFirst ∧ second = otherSecond :=
  Test.Elab.ConstructorExposure.Pair.mk.injEq first second otherFirst otherSecond

end Test.Elab.ConstructorDomains
