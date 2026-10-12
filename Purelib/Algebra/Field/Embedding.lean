module

-- The public embedding record retains this original parent in its negation law.
public import Purelib.Algebra.Group.Negation
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Explicit field embeddings

An original scalar map retains injectivity and preservation of the supplied
field operations. Its zero, inverse and division certificates compare the
same source and target operations through that retained map.
-/

namespace Purelib.Algebra.Field

set_option genInjectivity false in
/-- An injective map preserving the supplied explicit field operations.

The record retains the map, its injectivity, and preservation of zero, one, addition, negation, multiplication and total
inverse. -/
public structure Embedding (K L : Type*)
    [ExplicitField K] [DecidableEq K]
    [ExplicitField L] [DecidableEq L] where
  /-- The underlying scalar map between the two explicit fields. -/ toFun : K → L
  /-- Equal images imply equal source scalars. -/ injective : Function.Injective toFun
  /-- The map preserves zero. -/ map_zero : toFun 0 = 0
  /-- The map preserves one. -/ map_one : toFun 1 = 1
  /-- The map preserves addition. -/ map_add : ∀ left right, toFun (left + right) = toFun left + toFun right
  /-- The map preserves negation. -/ map_neg : ∀ source, toFun (-source) = -toFun source
  /-- The map preserves multiplication. -/ map_mul : ∀ left right, toFun (left * right) = toFun left * toFun right
  /-- The map preserves total inverse. -/ map_inv : ∀ source, toFun source⁻¹ = (toFun source)⁻¹

constructive_injectivity Embedding

variable {K L : Type*}
  [ExplicitField K] [DecidableEq K]
  [ExplicitField L] [DecidableEq L]

namespace Embedding

/-- An embedded scalar is zero exactly when the original scalar is zero.

Injectivity and preservation of zero give both directions. -/
public theorem map_zero_iff (embedding : Embedding K L) (source : K) :
    embedding.toFun source = 0 ↔ source = 0 := by
  constructor
  · intro imageZero
    apply embedding.injective
    exact imageZero.trans embedding.map_zero.symm
  · intro sourceZero
    cases sourceZero
    exact embedding.map_zero

/-- An explicit field embedding preserves total inversion.

The original retained inverse certificate compares the same source inverse
with the target inverse of its image, including the supplied value at zero. -/
public theorem apply_inv (embedding : Embedding K L) (source : K) :
    embedding.toFun source⁻¹ = (embedding.toFun source)⁻¹ :=
  embedding.map_inv source

/-- An explicit field embedding preserves division.

The identity follows from preservation of multiplication and total inverse, without a nonzero-denominator premise. -/
public theorem map_div (embedding : Embedding K L) (left right : K) :
    embedding.toFun (left / right) =
      embedding.toFun left / embedding.toFun right := by
  rw [ExplicitField.div_eq_mul_inv,
    ExplicitField.div_eq_mul_inv, embedding.map_mul, embedding.map_inv]

/-- An explicit field embedding preserves subtraction.

The original additive and negation certificates identify the difference
without imposing any new operation or order instance.
-/
public theorem map_sub (embedding : Embedding K L) (left right : K) :
    embedding.toFun (left - right) = embedding.toFun left - embedding.toFun right := by
  calc
    embedding.toFun (left - right) = embedding.toFun (left + -right) :=
      congrArg embedding.toFun (by ring1)
    _ = embedding.toFun left + embedding.toFun (-right) := embedding.map_add left (-right)
    _ = embedding.toFun left + -embedding.toFun right :=
      congrArg (fun value => embedding.toFun left + value) (embedding.map_neg right)
    _ = embedding.toFun left - embedding.toFun right := by ring1

end Embedding
end Purelib.Algebra.Field
