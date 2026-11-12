module

import Purelib.Riemann.RootContinuation.CoherentRoot
public import Purelib.Riemann.RootContinuation.CoherentRoot.Refinement
public import Purelib.Approximation.Gaussian.Sequence.Preparation
public import Purelib.Approximation.Gaussian.Sequence.Selection.Separation
public import Purelib.Geometry.Rational.Box.Point
public import Purelib.RootIsolation.State.WindingOne.Exclusion
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Uniform
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Coefficient-derived separation of original root samples from rational points

A nonzero exact polynomial evaluation computes a positive refinement request.
The selected state is read from the original root certificate's actual cache.
Finite constant-dominance exclusion gives a positive coordinate gap, and the
original nested state chain carries that gap to every later original sample.
-/

public section

namespace Purelib.Riemann.RootContinuation.CoherentRoot

open Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial
open Purelib.RootIsolation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Geometry.Rational
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Norm.Basic (normSq normSq_pos)
open Purelib.Data.Rat

set_option genInjectivity false in
/-- A computed original root stage with a positive gap from a displayed polynomial nonroot.

The cached exact evaluation, positive request, selected index and actual
retained state stay linked to the original polynomial, point and approximation.
The gap controls the same original sample channel after the selected stage.
-/
structure PointSeparation {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (point : Gaussian) (start : Nat) where
  /-- The actual exact polynomial value computed at the displayed point. -/
  value : Gaussian
  /-- The cached evaluation uses the original polynomial and point. -/
  value_eq : polynomial.eval point = value
  /-- The supplied or checked exact value is nonzero. -/
  nonzero : value ≠ 0
  /-- The coefficient-computed squared radius request. -/
  targetSq : Coordinate
  /-- The request uses the same cached exact evaluation. -/
  targetSq_eq : targetSq =
    Uniform.uniformExclusionRadius polynomial ambient (normSq value) ^ 2
  /-- The retained original request is strictly positive. -/
  targetSq_positive : 0 < targetSq
  /-- The actual stage selected by the original approximation's refiner. -/
  index : Nat
  /-- The original refiner consumes the same retained request and start. -/
  index_eq : index = root.approximation.refineIndex start targetSq targetSq_positive
  /-- The selected stage follows the original request's starting stage. -/
  index_ge : start ≤ index
  /-- The actual state read from the original root's shared cache. -/
  current : WindingOneState polynomial ambient
  /-- The retained state is the original cache read at the same selected stage. -/
  current_eq : current = root.stateAt index
  /-- The actual retained state meets the original squared-radius request. -/
  diagonal_lt : current.box.diagonalSq < targetSq
  /-- The computed positive coordinate gap at the actual retained root state. -/
  separation : Box.SeparationCertificate current.box (Box.Point.pointBox point)

constructive_injectivity PointSeparation

namespace PointSeparation

/-- Separate an original root from a nonroot using its retained exact refinement payment.

The payment must use the coefficient-derived exclusion request and the original
refiner's sufficient upper stage. Its actual cached state supplies the coordinate
gap; no original state read or refinement producer is evaluated again.
-/
@[expose] def ofValueWithRefinement {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (point value : Gaussian)
    (valueEq : polynomial.eval point = value) (nonzero : value ≠ 0) (start : Nat)
    (paid : Refinement root start)
    (request : paid.targetSq = Uniform.uniformExclusionRadius polynomial ambient (normSq value) ^ 2)
    (maximum : paid.index = paid.maxIndex) : PointSeparation root point start := by
  have normPositive : 0 < normSq value := Purelib.Data.Gaussian.Norm.Basic.normSq_pos nonzero
  have diagonal := paid.diagonal_lt.trans_eq request
  have margin : Uniform.exclusionCoefficient polynomial ambient *
      paid.current.box.diagonalSq < normSq (polynomial.eval point) := by
    rewrite [valueEq]
    exact (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct diagonal.le
      (Uniform.exclusionCoefficient_pos polynomial ambient).le).trans_lt
        (Uniform.uniform_exclusion_margin polynomial ambient normPositive)
  have outside := State.WindingOne.Exclusion.not_contains_of_margin root.degreePositive paid.current point margin
  exact
    { value := value
      value_eq := valueEq
      nonzero := nonzero
      targetSq := paid.targetSq
      targetSq_eq := request
      targetSq_positive := paid.positive
      index := paid.index
      index_eq := maximum.trans paid.maxIndex_eq
      index_ge := paid.index_ge
      current := paid.current
      current_eq := paid.current_eq
      diagonal_lt := paid.diagonal_lt
      separation := Box.Point.separationCertificateOfNotContains paid.current.box point outside }

/-- Compute original-root point separation using an already retained exact polynomial value.

The original refiner computes its sufficient finite stage from coefficient
bounds. The original cache supplies that actual state once; winding exclusion
and finite coordinate comparison certify its positive point gap.
-/
@[expose] def ofValue {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (point value : Gaussian)
    (valueEq : polynomial.eval point = value) (nonzero : value ≠ 0) (start : Nat) :
    PointSeparation root point start := by
  let norm := normSq value
  have normPositive : 0 < norm := Purelib.Data.Gaussian.Norm.Basic.normSq_pos nonzero
  let radius := Uniform.uniformExclusionRadius polynomial ambient norm
  have radiusPositive : 0 < radius :=
    Uniform.uniformExclusionRadius_pos polynomial ambient normPositive
  let targetSq := radius ^ 2
  have targetPositive : 0 < targetSq := Order.Arithmetic.pow_pos_direct radiusPositive 2
  let index := root.approximation.refineIndex start targetSq targetPositive
  let current := root.stateAt index
  have diagonal : current.box.diagonalSq < targetSq := by
    have accurate : root.approximation.radiusSq index < targetSq :=
      root.approximation.refineIndex_accurate start targetSq targetPositive
    have radiusEq : root.approximation.radiusSq index = Geometric.Basic.quarterRadius (scale track) index := by
      rewrite [root.approximation_eq]
      rfl
    rewrite [radiusEq] at accurate
    have bound := state_diagonal_le track index
    have same : current = state track index := root.stateAt_eq index
    rewrite [← same] at bound
    exact bound.trans_lt accurate
  exact ofValueWithRefinement root point value valueEq nonzero start
    (Refinement.atState root start targetSq targetPositive index rfl index
      (root.approximation.refineIndex_ge start targetSq targetPositive) (Nat.le_refl index) current rfl diagonal)
    rfl rfl

/-- A retained exact request and maximum-stage payment preserve the complete original point separation.

The original value, target, stage, cached state and coordinate-gap certificate
all agree. This is equality of the whole retained result, not only its gap.
-/
theorem ofValueWithRefinement_eq {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (point value : Gaussian)
    (valueEq : polynomial.eval point = value) (nonzero : value ≠ 0) (start : Nat)
    (paid : Refinement root start)
    (request : paid.targetSq = Uniform.uniformExclusionRadius polynomial ambient (normSq value) ^ 2)
    (maximum : paid.index = paid.maxIndex) :
    ofValueWithRefinement root point value valueEq nonzero start paid request maximum =
      ofValue root point value valueEq nonzero start := by
  rcases paid with ⟨target, positive, index, maxIndex, maxEq, indexLe, indexGe, current, currentEq, diagonal⟩
  dsimp only [] at request maximum
  cases request
  cases maxEq
  cases maximum
  cases currentEq
  rfl

/-- Restore the complete original nonroot-point separation from its actual maximum-stage cache read.

The coefficient-derived request and original refiner choose the same sufficient
stage as the default constructor. The supplied reader is called once at that
stage; its actual state and any failure pass through unchanged.
-/
def ofValueWithStates {m : Type → Type} [Monad m] {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (point value : Gaussian)
    (valueEq : polynomial.eval point = value) (nonzero : value ≠ 0) (start : Nat)
    (states : (index : Nat) → m {current : WindingOneState polynomial ambient // current = root.stateAt index}) :
    m {certificate : PointSeparation root point start //
      certificate = ofValue root point value valueEq nonzero start} := do
  let norm := normSq value
  have normPositive : 0 < norm := normSq_pos nonzero
  let radius := Uniform.uniformExclusionRadius polynomial ambient norm
  have radiusPositive := Uniform.uniformExclusionRadius_pos polynomial ambient normPositive
  let target := radius ^ 2
  have positive := Order.Arithmetic.pow_pos_direct radiusPositive 2
  let index := root.approximation.refineIndex start target positive
  let current ← states index
  have accurate : current.val.box.diagonalSq < target := by
    rewrite [current.property]
    exact root.stateAt_refineIndex_diagonal_lt start target positive
  let paid := Refinement.atState root start target positive index rfl index
    (root.approximation.refineIndex_ge start target positive) (Nat.le_refl index)
    current.val current.property accurate
  return ⟨ofValueWithRefinement root point value valueEq nonzero start paid rfl rfl,
    ofValueWithRefinement_eq root point value valueEq nonzero start paid rfl rfl⟩

/-- Evaluate the original polynomial once and compute a positive gap from its displayed nonroot. -/
@[expose] def ofPoint {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} (root : CertifiedName track) (point : Gaussian)
    (nonroot : polynomial.eval point ≠ 0) (start : Nat) : PointSeparation root point start :=
  let value := polynomial.eval point
  ofValue root point value rfl nonroot start

/-- Every later original cached root sample retains the computed positive squared point-gap bound. -/
theorem samples_lower {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track} {point : Gaussian} {start : Nat}
    (certificate : PointSeparation root point start) {later : Nat} (order : certificate.index ≤ later) :
    certificate.separation.gap ^ 2 ≤ normSq (root.approximation.sample later - point) := by
  have refinement := state_refines_of_le track order
  rewrite [← root.stateAt_eq later, ← root.stateAt_eq certificate.index, ← certificate.current_eq] at refinement
  have inside := refinement.contains (root.stateAt later).box.contains_anchor
  rewrite [root.sample_stateAt later]
  exact certificate.separation.lower inside (Box.Point.pointBox_contains point)

/-- Retain the same original root-versus-point separation in an indexed original candidate family.

The original root program is identified by its exact readback, and every
reading of the other original program is the retained scalar point. The same
root start and squared gap supply the pair table without another producer.
-/
@[expose] def toPairBound {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track} {point : Gaussian} {start : Nat}
    (certificate : PointSeparation root point start)
    {count : Nat} (candidates : Fin count → Sequence.ApproximationData) (left right : Fin count)
    (left_eq : candidates left = root.approximation)
    (right_read : ∀ index, (candidates right).sample index = point) :
    Sequence.Selection.PairBound candidates left right :=
  { leftIndex := certificate.index
    rightIndex := 0
    gap := certificate.separation.gap ^ 2
    positive := Order.Arithmetic.pow_pos_direct certificate.separation.positive 2
    lower := by
      intro different leftLater rightLater leftOrder rightOrder
      rewrite [left_eq, right_read rightLater]
      exact certificate.samples_lower leftOrder }

/-- Prepare the original root-minus-point channel using the same computed gap and retained root stage. -/
@[expose] def prepareDifference {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient} {root : CertifiedName track} {point : Gaussian} {start : Nat}
    (certificate : PointSeparation root point start) :
    Division.Prepared
      (CoherentNamed.add root.value
        (CoherentNamed.Coherence.exact (-point))) := by
  rewrite [root.value_approximation]
  exact root.approximation.prepareDifference point certificate.index (certificate.separation.gap ^ 2)
    (Order.Arithmetic.pow_pos_direct certificate.separation.positive 2)
    (fun _ order => certificate.samples_lower order)

end PointSeparation

end Purelib.Riemann.RootContinuation.CoherentRoot

end
