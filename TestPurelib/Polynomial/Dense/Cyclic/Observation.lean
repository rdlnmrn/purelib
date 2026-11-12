module

import Purelib.Algebra.Monogenic.Coordinates.Reading.Observation
import Purelib.Polynomial.Dense.Companion.Adjunction
import Purelib.Data.Gaussian.Field
import Purelib.System.IO

/-!
# Original cyclic observations from a retained generator matrix

The original quadratic adjunction retains its generator in its root. The
same observation uses that exact matrix cache and keeps the complete
generic-constructor value, including its nonmultiplicative child reading.
-/

namespace TestPurelib.Polynomial.Dense.Cyclic.Observation

open Purelib
open Polynomial.Dense.Basic (DensePolynomial)
open Polynomial.Dense (Companion)
open Algebra.Monogenic
open Algebra.Monogenic.Cyclic.Element.Reading (Parameters ColumnBound Observation)
open Algebra.Ring (GaussianReading)
open Data.Gaussian.Basic (Canonical)
open Data.Gaussian

/-- The original normalized quadratic has two distinct formal roots. -/
private def source : DensePolynomial Canonical := ⟨[1, 0, -1]⟩

/-- The original companion constructs and retains the same cyclic table and generator. -/
private def adjunction := Companion.adjoin (Companion.ofUnit source (by decide +kernel) 1 (by decide +kernel))

/-- The reading parameters belong to that same original cyclic table. -/
private def parameters := Parameters.prepare adjunction.table Norm.weight 1 1 (by decide) (by decide)

/-- The retained original root matrix equals the same table's original generator. -/
private theorem generator_eq : adjunction.root.matrix =
    LinearAlgebra.Matrix.Rectangular.transpose adjunction.companion.matrix :=
  (congrArg Cyclic.Element.matrix adjunction.root_eq).trans (Cyclic.Element.root_matrix adjunction.table)

/-- Every original column satisfies the displayed bound at the nonroot rational candidate. -/
private theorem columns : ColumnBound
    (LinearAlgebra.Matrix.Rectangular.transpose adjunction.companion.matrix) GaussianReading.identity (3 / 4) 1 := by
  unfold ColumnBound
  decide +kernel

/-- Construct the observation from the same retained root matrix without another transpose. -/
private def cached := Observation.prepareGenerator adjunction.root.matrix generator_eq parameters
  GaussianReading.identity rfl (3 / 4) (by decide +kernel) 1 (by decide) columns

/-- The cached-generator constructor preserves the complete original observation value. -/
private theorem agreement : cached = Observation.prepare parameters GaussianReading.identity rfl
    (3 / 4) (by decide +kernel) 1 (by decide) columns :=
  Observation.prepareGenerator_eq_prepare adjunction.root.matrix generator_eq parameters
    GaussianReading.identity rfl (3 / 4) (by decide +kernel) 1 (by decide) columns

/-- The scalar projections retain their original definitional reductions even for an arbitrary cache equality. -/
private theorem scalar_projections {K : Type*} [CommRing K] {dimension : Nat}
    {generator : LinearAlgebra.Matrix K dimension} {cyclic : Cyclic generator}
    {parent : Algebra.Ring.Weight K} {gain radius : Data.Rat.Fraction.Rational} {embed : Canonical → K}
    (matrix : LinearAlgebra.Matrix K dimension) (same : matrix = generator)
    (parameters : Parameters cyclic parent gain radius) (reading : GaussianReading parent embed)
    (gainEq : reading.gain = gain) (point : Canonical) (pointBound : Norm.Basic.normSq point ≤ radius)
    (residual : Data.Rat.Fraction.Rational) (nonnegative : 0 ≤ residual)
    (columns : ColumnBound generator reading point residual) :
    (Observation.prepareGenerator matrix same parameters reading gainEq point pointBound
      residual nonnegative columns).point = point ∧
      (Observation.prepareGenerator matrix same parameters reading gainEq point pointBound
        residual nonnegative columns).residual = residual := ⟨rfl, rfl⟩

/-- The same retained child reads the rational candidate and keeps its actual multiplication discrepancy. -/
private theorem computes : cached.point = 3 / 4 ∧ cached.residual = 1 ∧ cached.child.gain = 8 ∧
    cached.child.read adjunction.root = 3 / 4 ∧
      cached.child.read (adjunction.root * adjunction.root) -
        cached.child.read adjunction.root * cached.child.read adjunction.root = 7 / 16 := by decide +kernel

/-- Execute the cached original observation's actual numerical readbacks. -/
public def run : IO Unit := do
  unless cached.point == 3 / 4 && cached.residual == 1 && cached.child.gain == 8 &&
      cached.child.read adjunction.root == 3 / 4 &&
      cached.child.read (adjunction.root * adjunction.root) -
        cached.child.read adjunction.root * cached.child.read adjunction.root == 7 / 16 do
    throw (IO.userError "the retained generator changed its original observation or child reading")
  System.IO.println "Original retained generator: complete observation agreement, gain8, discrepancy7/16."

end TestPurelib.Polynomial.Dense.Cyclic.Observation
