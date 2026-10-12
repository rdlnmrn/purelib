module

public import Init
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

namespace NanodaDependencyFixture

private def hidden : Nat := 37
-- Keep this root body private so the exporter must recover its private dependency.
@[no_expose] def usesPrivate : Nat := hidden + 5
def naturalLiteral : Nat := 123456789
def stringLiteral : String := "nanoda graph fixture"

-- Excluded as a root, still required through its public consumer.
def helper.eq_def : Nat := 91
def usesExcluded : Nat := helper.eq_def

set_option genInjectivity false in
mutual
  inductive LeftTree where
    | leaf : LeftTree
    | branch : RightTree → LeftTree
  inductive RightTree where
    | branch : LeftTree → RightTree
end

constructive_injectivity LeftTree
constructive_injectivity RightTree

def tree : LeftTree := .branch (.branch .leaf)
def useRecursor (n : Nat) : Nat := Nat.rec 0 (fun _ acc => acc + 1) n
-- Exercises the exporter's indivisible quotient package without Quot.sound.
def quotientType : Sort 1 := Quot (fun a b : Nat => a = b)
def quotientValue : quotientType := Quot.mk _ 3

end NanodaDependencyFixture

end
