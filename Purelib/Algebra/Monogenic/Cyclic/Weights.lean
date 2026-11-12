module

public import Purelib.Algebra.Monogenic.Weight
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached weights of an original cyclic generator and its retained powers

The same original matrix and cached power table supply the finite weight
calculations once. Subsequent readings consume the retained scalar vector
and total without evaluating the matrix-entry weight sums again.
-/

public section

namespace Purelib.Algebra.Monogenic.Cyclic

open Purelib.Algebra.Ring (Weight)
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Algebra.FiniteSum.Rational.Order
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.Data.Vector.Basic
open Purelib.Data.Rat.Fraction (Rational)

variable {K : Type*} [CommRing K] {dimension : Nat} {generator : SquareMatrix K dimension}

set_option genInjectivity false in
/-- Cached scalar weights of the original generator and its same original bounded power table.

The complete retained vector and its sum are executable data. The defining
equalities tie every entry to the original cyclic table and scalar weight;
no new matrix power computation is part of this preparation.
-/
structure Weights (cyclic : Cyclic generator) (parent : Weight K) where
  /-- The once-computed total of the original generator's entry weights. -/
  generatorWeight : Rational
  /-- The retained generator total has its original matrix specification. -/
  generatorWeight_eq : generatorWeight = SquareMatrix.Weight.total parent generator
  /-- The materialized weights of the same original retained matrix powers. -/
  powerWeights : Purelib.Data.Vector Rational dimension
  /-- Each stored scalar comes from its same original bounded power occurrence. -/
  powerWeights_eq : ∀ index, powerWeights index = SquareMatrix.Weight.total parent (cyclic.powers index)
  /-- The once-computed sum of the stored scalar power weights. -/
  powerTotal : Rational
  /-- The retained total sums the same materialized scalar table. -/
  powerTotal_eq : powerTotal = sumFin (fun index => powerWeights index)

constructive_injectivity Weights

namespace Weights

/-- Materialize original matrix weights once from the same retained generator and power table. -/
@[expose] def prepare (cyclic : Cyclic generator) (parent : Weight K) : Weights cyclic parent :=
  let powers := vectorOfFn (fun index => SquareMatrix.Weight.total parent (cyclic.powers index))
  { generatorWeight := SquareMatrix.Weight.total parent generator
    generatorWeight_eq := rfl
    powerWeights := powers
    powerWeights_eq := fun index => vectorOfFn_apply _ index
    powerTotal := sumFin (fun index => powers index)
    powerTotal_eq := rfl }

variable {cyclic : Cyclic generator} {parent : Weight K}

/-- The stored original generator total is nonnegative. -/
theorem generatorWeight_nonnegative (weights : Weights cyclic parent) : 0 ≤ weights.generatorWeight := by
  rewrite [weights.generatorWeight_eq]
  exact SquareMatrix.Weight.total_nonnegative parent generator

/-- Every stored original power weight is nonnegative. -/
theorem powerWeight_nonnegative (weights : Weights cyclic parent) (index : Fin dimension) :
    0 ≤ weights.powerWeights index := by
  rewrite [weights.powerWeights_eq index]
  exact SquareMatrix.Weight.total_nonnegative parent (cyclic.powers index)

/-- The sum of the same stored power weights is nonnegative. -/
theorem powerTotal_nonnegative (weights : Weights cyclic parent) : 0 ≤ weights.powerTotal := by
  rewrite [weights.powerTotal_eq]
  exact weight_sum_nonnegative _ weights.powerWeight_nonnegative

/-- The original algebra power's weight is its same retained scalar-table entry. -/
theorem root_power_weight (weights : Weights cyclic parent) (index : Fin dimension) :
    (Element.weight cyclic parent).value (Element.root cyclic ^ index.val) = weights.powerWeights index := by
  change SquareMatrix.Weight.total parent (Element.root cyclic ^ index.val).matrix = _
  rewrite [Element.pow_matrix, Element.root_matrix, ← cyclic.powers_eq index]
  exact (weights.powerWeights_eq index).symm

/-- The stored total uniformly bounds every same original bounded algebra power. -/
theorem root_power_weight_le (weights : Weights cyclic parent) (index : Fin dimension) :
    (Element.weight cyclic parent).value (Element.root cyclic ^ index.val) ≤ weights.powerTotal := by
  rewrite [weights.root_power_weight index, weights.powerTotal_eq]
  exact entry_le_sumFin _ weights.powerWeight_nonnegative index

end Weights

end Purelib.Algebra.Monogenic.Cyclic

end
