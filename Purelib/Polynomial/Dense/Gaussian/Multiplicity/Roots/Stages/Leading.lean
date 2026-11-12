module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages
public import Purelib.Polynomial.Dense.Roots.Tower.Leading

/-!
# Original factor-leading ownership across retained stage towers

Each same original context supplies its retained mapped factor and original
factor tower. Its Gaussian leading coefficient owns every original stage
inverse. The existing whole-tower embedding transports the scalar-map laws
to the next original factor, without rebuilding a tower or coefficient map.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Polynomial.Dense.Roots (Tower)
open Purelib.Algebra.Monogenic

universe u

variable {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}

/-- Every same retained original factor tower owns its original Gaussian leading coefficient and inverse images.

The proof-only spine follows the original stage constructors. Its next
scalar map is exactly the original whole-tower embedding already used by
the next retained factor, rather than a separately constructed map.
-/
@[expose] def Leading {contexts : List (PositiveContext entries)}
    {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
    {function : Canonical → K} (stages : Stages contexts indices K ring equality function) : Prop :=
  match indices, stages with
  | [], .done => True
  | index :: _, .adjoin _ _ _ _ tower _ _ remaining =>
      Tower.Leading tower function (factor contexts index).leadingCoeff ∧ Leading remaining

namespace Leading

variable {indices : List (Fin contexts.length)} {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
variable {function : Canonical → K}

/-- Derive original factor-tower leading ownership from the same initial coefficient embedding laws.

The retained mapped-factor equality supplies the original leading
coefficient. Existing injective scalar embeddings transport that coefficient
and the same scalar laws through the original complete preceding tower.
-/
theorem ofScalar (stages : Stages contexts indices K ring equality function)
    (mapZero : function 0 = 0) (mapOne : function 1 = 1)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (injective : Function.Injective function) : Leading stages := by
  induction stages with
  | done => exact True.intro
  | @adjoin K ring equality function index indices mapped mappedEq normalized degree tower roots rootsEq
      remaining previous =>
      have leading : mapped.leadingCoeff = function (factor contexts index).leadingCoeff :=
        (congrArg DensePolynomial.leadingCoeff mappedEq).trans
          (Dense.Map.map_leadingCoeff function mapZero injective (factor contexts index))
      refine ⟨Tower.Leading.ofSource tower function (factor contexts index).leadingCoeff
        normalized leading mapZero mapOne mapMul, ?_⟩
      exact previous
        ((congrArg tower.embed mapZero).trans tower.embed_zero)
        ((congrArg tower.embed mapOne).trans tower.embed_one)
        (fun left right => (congrArg tower.embed (mapMul left right)).trans (tower.embed_mul _ _))
        (fun _ _ same => injective (tower.embed_injective same))

variable {index : Fin contexts.length} {mapped : DensePolynomial K}
variable {mappedEq : mapped = Dense.Map.map function (factor contexts index)}
variable {normalized : mapped.normalize = mapped} {degree : mapped.natDegree = (factor contexts index).natDegree}
variable {tower : Tower K ring equality mapped} {roots : List (Dense.Roots.Block tower.Scalar)}
variable {rootsEq : roots = tower.blocks}
variable {remaining : Stages contexts indices tower.Scalar inferInstance inferInstance
  (fun value => tower.embed (function value))}

/-- Read the same current original factor tower's Gaussian scalar-leading invariant. -/
theorem current (leading : Leading (.adjoin mapped mappedEq normalized degree tower roots rootsEq remaining)) :
    Tower.Leading tower function (factor contexts index).leadingCoeff := leading.1

/-- Read leading ownership for the same original remaining factor stages. -/
theorem next (leading : Leading (.adjoin mapped mappedEq normalized degree tower roots rootsEq remaining)) :
    Leading remaining := leading.2

end Leading

namespace Prepared

/-- The same automatic original positive-side stages supply their scalar-leading inverse readbacks. -/
theorem leading {source opposite : DensePolynomial Canonical}
    {input : Basis.Coprime.Side.PositiveSideInput source opposite} (prepared : Prepared input) :
    Leading prepared.stages :=
  Leading.ofScalar prepared.stages rfl rfl (fun _ _ => rfl) (fun _ _ same => same)

end Prepared

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages

end
