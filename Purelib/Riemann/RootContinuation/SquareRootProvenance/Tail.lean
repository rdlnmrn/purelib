module

public import Purelib.Riemann.RootContinuation.SquareRootProvenance
public import Purelib.Data.Gaussian.Norm.Power.Square
public import Purelib.Approximation.Gaussian.Geometric.Coherent.Tail
public import Purelib.Approximation.Gaussian.Geometric.Enclosure
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Approximation.Gaussian.Sequence.Name.Exact
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Actual bounded native tails from an original named square identity

One executable comparison pays a square residual before selecting the native
tail. The actual Gaussian parameter and residual imply a uniform quadrance
ceiling. The same channel, comparison floors, tail and enclosure are retained;
no finite reading is replaced by an exact root.
-/

public section

namespace Purelib.Riemann.RootContinuation.SquareRootProvenance

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation Enclosure)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (Comparison NamedEquivalent)

/-- The native residual request is one quarter of the original positive quadrance ceiling's square. -/
@[expose] def tailRequest (ceiling : Fraction.Rational) : Fraction.Rational := ceiling ^ 2 / 4

/-- Every positive quadrance ceiling supplies a positive original square-residual request. -/
theorem tailRequest_positive {ceiling : Fraction.Rational} (positive : 0 < ceiling) : 0 < tailRequest ceiling :=
  Fraction.Order.Field.div_pos_direct (Fraction.Order.Arithmetic.pow_pos_direct positive 2) (by decide +kernel)

/-- The actual square comparison, native tail and same-channel common enclosure retain their original factories. -/
@[expose] def Tail (channel : CoherentNamed) (parameter : Canonical) (square : SquareIdentity channel parameter)
    (floor : Nat) (ceiling : Fraction.Rational) (positive : 0 < ceiling) : Type _ :=
  (compared : { value : Comparison
      (Sequence.Arithmetic.Product.sampledProductApproximation channel.name channel.name)
      (Name.Sampling.approximation (Name.Basic.Named.exact parameter)) floor 0 (tailRequest ceiling) //
    value = (sampled_square square).compare floor 0 (tailRequest ceiling) (tailRequest_positive positive) }) ×
  (tail : { value : GeometricApproximation // value = nativeTail channel compared.val.leftIndex }) ×
  { value : Enclosure channel // value.source = tail.val ∧
    value.ball = { center := 0, radiusSq := ceiling, radiusSq_nonneg := positive.le } }

/-- A paid original square comparison bounds every later original native sample through its actual residual. -/
theorem native_normSq_le (channel : CoherentNamed) (parameter : Canonical)
    {floor : Nat} {ceiling : Fraction.Rational} (positive : 0 < ceiling)
    (parameterBound : Norm.Basic.normSq parameter ≤ tailRequest ceiling)
    (compared : Comparison
      (Sequence.Arithmetic.Product.sampledProductApproximation channel.name channel.name)
      (Name.Sampling.approximation (Name.Basic.Named.exact parameter)) floor 0 (tailRequest ceiling))
    {index : Nat} (later : compared.leftIndex ≤ index) :
    Norm.Basic.normSq ((Name.Sampling.approximation channel.name).sample index) ≤ ceiling := by
  have residual := compared.close (leftLater := index) (rightLater := compared.rightIndex)
    later (Nat.le_refl _)
  rewrite [Sequence.Arithmetic.Product.sampledProductApproximation_sample,
    Sequence.Name.Exact.exactNamedSample] at residual
  exact Norm.Power.root_normSq_le positive.le parameterBound residual.le

/-- Select one actual residual-paid native floor and enclose the SAME named channel from its exact coefficient bound.

The parameter inequality concerns only the displayed Gaussian coefficient.
The sample ceiling is derived from that inequality and the selected all-later
square residual; it is not an input bound on the channel's readings.
-/
def encloseAt (channel : CoherentNamed) (parameter : Canonical) (square : SquareIdentity channel parameter)
    (floor : Nat) (ceiling : Fraction.Rational) (positive : 0 < ceiling)
    (parameterBound : Norm.Basic.normSq parameter ≤ tailRequest ceiling) :
    Tail channel parameter square floor ceiling positive := by
  let compared := (sampled_square square).compare floor 0 (tailRequest ceiling) (tailRequest_positive positive)
  let tail := nativeTail channel compared.leftIndex
  let tailCache : { value : GeometricApproximation // value = nativeTail channel compared.leftIndex } := ⟨tail, rfl⟩
  have bound (index : Nat) : Norm.Basic.normSq (tail.sample index) ≤ ceiling := by
    have actual := native_normSq_le channel parameter positive parameterBound compared
      (index := compared.leftIndex + index) (Nat.le_add_right _ _)
    exact (congrArg Norm.Basic.normSq (nativeTail_sample channel compared.leftIndex index)).trans_le actual
  let enclosed : Enclosure channel :=
    { source := tail
      equivalent := nativeTail_agrees channel compared.leftIndex
      ball := { center := 0, radiusSq := ceiling, radiusSq_nonneg := positive.le }
      contains := fun index => by
        change Norm.Basic.normSq (tail.sample index - 0) ≤ ceiling
        rewrite [Basic.sub_zero]
        exact bound index }
  exact ⟨⟨compared, rfl⟩, tailCache, ⟨enclosed, rfl, rfl⟩⟩

/-- The coefficient-computed ceiling gives an actual bounded native tail for every original square identity. -/
def enclose (channel : CoherentNamed) (parameter : Canonical) (square : SquareIdentity channel parameter)
    (floor : Nat) : Tail channel parameter square floor (Norm.Power.rootNormCeiling parameter)
      (Norm.Power.rootNormCeiling_positive parameter) :=
  encloseAt channel parameter square floor (Norm.Power.rootNormCeiling parameter)
    (Norm.Power.rootNormCeiling_positive parameter) (Norm.Power.rootNormCeiling_parameter parameter)

namespace Tail

variable {channel : CoherentNamed} {parameter : Canonical} {square : SquareIdentity channel parameter}
    {floor : Nat} {ceiling : Fraction.Rational} {positive : 0 < ceiling}
    (actual : Tail channel parameter square floor ceiling positive)

/-- Read the SAME original channel enclosure stored after the actual square-comparison selection. -/
@[expose] def enclosure : Enclosure channel := actual.2.2.val

/-- The original minimum native floor is paid by the actual retained comparison. -/
theorem floor_le : floor ≤ actual.1.val.leftIndex := actual.1.val.left_ge

/-- The enclosure's source samples retain the actual original native floor without changing indices. -/
theorem source_sample (index : Nat) :
    actual.enclosure.source.sample index =
      (Name.Sampling.approximation channel.name).sample (actual.1.val.leftIndex + index) :=
  (congrArg (fun value : GeometricApproximation => value.sample index) actual.2.2.property.1).trans
    ((congrArg (fun value : GeometricApproximation => value.sample index) actual.2.1.property).trans
      (nativeTail_sample channel actual.1.val.leftIndex index))

end Tail

end Purelib.Riemann.RootContinuation.SquareRootProvenance

end
