module

public import Purelib.Algebra.Monogenic.Coordinates.Reading
public import Purelib.Algebra.Monogenic.Coordinates.Reading.Request
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained observations and their original cyclic readings

One bounded candidate and a certified original generator residual construct
one child reading. The observation retains that actual child and its complete
construction equation, so the next stage consumes the cached reading.
-/

public section

namespace Purelib.Algebra.Monogenic.Cyclic.Element.Reading

open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Algebra.FiniteSum.Fin
open Purelib.LinearAlgebra renaming Matrix → SquareMatrix
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

variable {K : Type*} [CommRing K] {dimension : Nat} {generator : SquareMatrix K dimension}
variable {cyclic : Cyclic generator} {parent : Weight K} {gain radius : Rational} {embed : Canonical → K}

/-- Every actual original generator column pays the retained candidate's squared residual bound. -/
@[expose] def ColumnBound (generator : SquareMatrix K dimension) (reading : GaussianReading parent embed)
    (point : Canonical) (residual : Rational) : Prop :=
  ∀ column : Fin dimension,
    Norm.Basic.normSq (sumFin (fun row => reading.read (generator row column) * point ^ row.val) -
      point * point ^ column.val) ≤ residual

set_option genInjectivity false in
/-- One original cyclic observation retains its candidate, residual and constructed child reading.

The parameter cache and actual parent reading remain indices. The complete
child equation preserves their original ownership without replaying the
finite evaluator or replacing the original coefficient algebra.
-/
structure Observation (parameters : Parameters cyclic parent gain radius)
    (reading : GaussianReading parent embed) (gain_eq : reading.gain = gain) where
  /-- The actual observed Gaussian candidate. -/
  point : Canonical
  /-- The candidate stays within the fixed pre-observation radius. -/
  pointBound : Norm.Basic.normSq point ≤ radius
  /-- The retained nonnegative bound for the actual original generator columns. -/
  residual : Rational
  /-- The same retained residual bound is nonnegative. -/
  residualNonnegative : 0 ≤ residual
  /-- Every original column satisfies the bound at this same candidate. -/
  columns : ColumnBound generator reading point residual
  /-- The once-constructed reading of the same original cyclic coefficient algebra. -/
  child : GaussianReading (Element.weight cyclic parent) (fun coefficient => scalar cyclic (embed coefficient))
  /-- The child is the exact original constructor on these retained observations. -/
  child_eq : child = parameters.toReading reading gain_eq point pointBound residual residualNonnegative columns

constructive_injectivity Observation

namespace Observation

/-- Construct the actual original child reading once and retain its original numerical inputs. -/
@[expose] def prepare (parameters : Parameters cyclic parent gain radius)
    (reading : GaussianReading parent embed) (gain_eq : reading.gain = gain)
    (point : Canonical) (pointBound : Norm.Basic.normSq point ≤ radius)
    (residual : Rational) (residualNonnegative : 0 ≤ residual)
    (columns : ColumnBound generator reading point residual) : Observation parameters reading gain_eq :=
  let child := parameters.toReading reading gain_eq point pointBound residual residualNonnegative columns
  { point, pointBound, residual, residualNonnegative, columns, child, child_eq := rfl }

/-- Construct the same original observation using an already retained equal generator matrix.

Equality transport preserves the original cyclic table, parameters, column
certificate and complete result. Only the supplied matrix cache is passed
to the original constructor; no table or parameter cache is reconstructed.
The point and residual keep their original definitional readbacks while the
same once-prepared child supplies the retained reading.
-/
@[expose] def prepareGenerator (cached : SquareMatrix K dimension) (cachedEq : cached = generator)
    (parameters : Parameters cyclic parent gain radius) (reading : GaussianReading parent embed)
    (gain_eq : reading.gain = gain) (point : Canonical) (pointBound : Norm.Basic.normSq point ≤ radius)
    (residual : Rational) (residualNonnegative : 0 ≤ residual)
    (columns : ColumnBound generator reading point residual) : Observation parameters reading gain_eq :=
  let prepared : Observation parameters reading gain_eq := by
    subst generator
    exact prepare parameters reading gain_eq point pointBound residual residualNonnegative columns
  have childEq : prepared.child =
      parameters.toReading reading gain_eq point pointBound residual residualNonnegative columns := by
    subst generator
    rfl
  { point, pointBound, residual, residualNonnegative, columns, child := prepared.child, child_eq := childEq }

/-- Generator-cache transport preserves the complete original observation value. -/
theorem prepareGenerator_eq_prepare (cached : SquareMatrix K dimension) (cachedEq : cached = generator)
    (parameters : Parameters cyclic parent gain radius) (reading : GaussianReading parent embed)
    (gain_eq : reading.gain = gain) (point : Canonical) (pointBound : Norm.Basic.normSq point ≤ radius)
    (residual : Rational) (residualNonnegative : 0 ≤ residual)
    (columns : ColumnBound generator reading point residual) :
    prepareGenerator cached cachedEq parameters reading gain_eq point pointBound residual residualNonnegative columns =
      prepare parameters reading gain_eq point pointBound residual residualNonnegative columns := by
  cases cachedEq
  rfl

variable {parameters : Parameters cyclic parent gain radius} {reading : GaussianReading parent embed}
variable {parentGainEq : reading.gain = gain}

/-- The retained child keeps the gain fixed by the same pre-observation parameter cache. -/
theorem gain_eq (observation : Observation parameters reading parentGainEq) :
    observation.child.gain = parameters.gain :=
  congrArg GaussianReading.gain observation.child_eq

/-- The retained child's actual error is linear in this same parent error and observed residual. -/
theorem error_eq (observation : Observation parameters reading parentGainEq) :
    observation.child.error =
      parameters.parentFactor * reading.error + parameters.sourceFactor * observation.residual :=
  congrArg GaussianReading.error observation.child_eq

/-- Each read consumes the retained original parent reading and candidate through the original evaluator. -/
theorem read_apply (observation : Observation parameters reading parentGainEq) (value : Element cyclic) :
    observation.child.read value = evaluate reading.read observation.point value :=
  congrArg (fun child => child.read value) observation.child_eq

/-- The retained child reads each original embedded parent coefficient exactly as its same parent. -/
theorem read_scalar (observation : Observation parameters reading parentGainEq) (value : K) :
    observation.child.read (scalar cyclic value) = reading.read value :=
  (observation.read_apply _).trans (evaluate_scalar reading.read reading.mapZero observation.point value)

/-- The actual original root reading has a source-fixed bound from the same retained gain and generator weight.

The child's certified gain applies to the original cyclic root itself. Its
matrix is the same original generator, so the weight is the already cached
generator total and no new matrix-weight scan is part of this readback.
-/
theorem root_normSq_le (observation : Observation parameters reading parentGainEq) :
    Norm.Basic.normSq (observation.child.read (Element.root cyclic)) ≤
      parameters.gain * parameters.weights.generatorWeight := by
  have bound := observation.child.gainBound (Element.root cyclic)
  have rootWeight : (Element.weight cyclic parent).value (Element.root cyclic) =
      parameters.weights.generatorWeight := by
    change SquareMatrix.Weight.total parent (Element.root cyclic).matrix = _
    rewrite [Element.root_matrix]
    exact parameters.weights.generatorWeight_eq.symm
  rewrite [observation.gain_eq, rootWeight] at bound
  exact bound

/-- Paying both original input obligations makes the cached child's actual error strictly sufficient. -/
theorem error_lt (observation : Observation parameters reading parentGainEq) {target : Rational}
    (request : Request parameters target) (parentBound : reading.error ≤ request.tolerance)
    (residualBound : observation.residual ≤ request.tolerance) : observation.child.error < target := by
  rewrite [observation.error_eq]
  exact request.error_lt reading.error observation.residual parentBound residualBound

end Observation

end Purelib.Algebra.Monogenic.Cyclic.Element.Reading

end
