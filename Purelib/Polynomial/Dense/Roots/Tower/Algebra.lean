module

public import Purelib.Polynomial.Dense.Roots.Tower

/-!
# The final coefficient algebra of a retained root tower

The last retained stage supplies the actual scalar operations and equality
procedure. Original coefficients pass through the same successive scalar
embeddings. Each composed map retains injectivity and its original ring laws;
no field structure or quotient construction is introduced.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Tower

open Basic (DensePolynomial)
open Purelib.Algebra.Monogenic

universe u

/-- The original coefficient carrier at the final retained stage of a tower. -/
@[expose] def Scalar {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {polynomial : DensePolynomial K} (tower : Tower K ring equality polynomial) : Type u :=
  match tower with
  | .constant _ _ => K
  | .step _ _ remaining => Scalar remaining

/-- The actual executable ring dictionary of the final retained coefficient algebra. -/
@[expose, implicit_reducible] def scalarRing {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {polynomial : DensePolynomial K} (tower : Tower K ring equality polynomial) : CommRing tower.Scalar :=
  match tower with
  | .constant _ _ => ring
  | .step _ _ remaining => scalarRing remaining

/-- The final scalar operations are exactly those of the final retained original stage. -/
instance instCommRingScalar {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {polynomial : DensePolynomial K} (tower : Tower K ring equality polynomial) : CommRing tower.Scalar :=
  tower.scalarRing

/-- The final retained equality procedure compares the same original scalar payloads. -/
@[expose] def scalarDecidableEq {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {polynomial : DensePolynomial K} (tower : Tower K ring equality polynomial) : DecidableEq tower.Scalar :=
  match tower with
  | .constant _ _ => equality
  | .step _ _ remaining => scalarDecidableEq remaining

/-- The final scalar equality instance is the actual final-stage procedure. -/
instance instDecidableEqScalar {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {polynomial : DensePolynomial K} (tower : Tower K ring equality polynomial) : DecidableEq tower.Scalar :=
  tower.scalarDecidableEq

/-- Compose the same retained scalar embeddings into the final coefficient carrier.

The tail embedding is captured once before the original coefficient is
supplied. Each original cyclic scalar map is shared by the resulting closure.
-/
@[expose] def embed {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {polynomial : DensePolynomial K} (tower : Tower K ring equality polynomial) : K → tower.Scalar :=
  match tower with
  | .constant _ _ => id
  | .step adjunction _ remaining =>
      let tailEmbedding := embed remaining
      let scalarEmbedding := Cyclic.Element.scalar adjunction.table
      fun value => tailEmbedding (scalarEmbedding value)

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
variable {polynomial : DensePolynomial K}

/-- The retained composite embedding preserves original zero. -/
theorem embed_zero (tower : Tower K ring equality polynomial) : tower.embed 0 = 0 := by
  induction tower with
  | constant => rfl
  | step adjunction _ remaining previous =>
      change remaining.embed (Cyclic.Element.scalar adjunction.table 0) = 0
      rewrite [Cyclic.Element.scalar_zero]
      exact previous

/-- The retained composite embedding preserves original one. -/
theorem embed_one (tower : Tower K ring equality polynomial) : tower.embed 1 = 1 := by
  induction tower with
  | constant => rfl
  | step adjunction _ remaining previous =>
      change remaining.embed (Cyclic.Element.scalar adjunction.table 1) = 1
      rewrite [Cyclic.Element.scalar_one]
      exact previous

/-- The retained composite embedding preserves original addition. -/
theorem embed_add (tower : Tower K ring equality polynomial) (left right : K) :
    tower.embed (left + right) = tower.embed left + tower.embed right := by
  induction tower with
  | constant => rfl
  | step adjunction _ remaining previous =>
      change remaining.embed (Cyclic.Element.scalar adjunction.table (left + right)) = _
      rewrite [Cyclic.Element.scalar_add]
      exact previous _ _

/-- The retained composite embedding preserves original negation. -/
theorem embed_neg (tower : Tower K ring equality polynomial) (value : K) :
    tower.embed (-value) = -tower.embed value := by
  induction tower with
  | constant => rfl
  | step adjunction _ remaining previous =>
      change remaining.embed (Cyclic.Element.scalar adjunction.table (-value)) = _
      rewrite [Cyclic.Element.scalar_neg]
      exact previous _

/-- The retained composite embedding preserves original multiplication. -/
theorem embed_mul (tower : Tower K ring equality polynomial) (left right : K) :
    tower.embed (left * right) = tower.embed left * tower.embed right := by
  induction tower with
  | constant => rfl
  | step adjunction _ remaining previous =>
      change remaining.embed (Cyclic.Element.scalar adjunction.table (left * right)) = _
      rewrite [Cyclic.Element.scalar_mul]
      exact previous _ _

/-- Equal final embedded coefficients identify their same original source coefficients. -/
theorem embed_injective (tower : Tower K ring equality polynomial) : Function.Injective tower.embed := by
  induction tower with
  | constant => intro _ _ same; exact same
  | step adjunction _ remaining previous =>
      intro left right same
      change remaining.embed (Cyclic.Element.scalar adjunction.table left) =
        remaining.embed (Cyclic.Element.scalar adjunction.table right) at same
      exact Cyclic.Element.scalar_injective adjunction.table (previous same)

end Purelib.Polynomial.Dense.Roots.Tower

end
