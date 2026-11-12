module

public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Sampled.Matched
public import Purelib.Data.Gaussian.Norm.Radial
import Purelib.Polynomial.Dense.Roots.Tower.Reading.Realization.Roots
import Purelib.Data.Gaussian.Norm.Bounds

/-!
# Actual radial bounds for the same original sampled formal roots

The original indexed candidate supplies its norm bound, strict collar and
inside or outside sign. The same sampled reading pays the fixed radial cap,
and its original parameter total bounds the formal root reading. No label
or root count replaces either quantitative premise.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Tower.Reading.Sampled

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

universe u

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K]
variable {polynomial : DensePolynomial K} {tower : Tower K ring equality polynomial}
variable {parent : Weight K} {gain radius target tolerance : Rational}
variable {parameters : Parameters tower parent gain radius}
variable {budget : Budget parameters target tolerance} {embed : Canonical → K}
variable {reading : GaussianReading parent embed} {gain_eq : reading.gain = gain}
variable {nodes : List Canonical} {beta width : Rational}

/-- The same original indexed candidate-root displacement pays the fixed radial request.

Only the endpoints' order in squared distance is reversed. Both indexed
values and their retained bounds are the original correspondence's entries.
-/
theorem displacement (request : Norm.Radial.Request radius parameters.rootBoundTotal beta width)
    (sampled : Sampled budget reading gain_eq nodes (request.cap * beta)) (index : Fin tower.blocks.length) :
    Norm.Basic.normSq (nodes[index.val]'(sampled.matched.nodeBound index) -
      sampled.realization.finalReading.read (tower.blocks[index.val]'index.isLt).point) ≤ request.cap * beta := by
  rewrite [Norm.Bounds.normSq_sub_symm]
  exact sampled.matched.get index

/-- The original inside candidate and paid displacement put its actual formal-root reading below the fixed ceiling. -/
theorem inside (request : Norm.Radial.Request radius parameters.rootBoundTotal beta width)
    (sampled : Sampled budget reading gain_eq nodes (request.cap * beta)) (index : Fin tower.blocks.length)
    (candidateBounded : Norm.Basic.normSq (nodes[index.val]'(sampled.matched.nodeBound index)) ≤ radius)
    (collar : width ^ 2 < (Norm.Basic.normSq (nodes[index.val]'(sampled.matched.nodeBound index)) - 1) ^ 2)
    (inside : Norm.Basic.normSq (nodes[index.val]'(sampled.matched.nodeBound index)) < 1) :
    Norm.Basic.normSq (sampled.realization.finalReading.read (tower.blocks[index.val]'index.isLt).point) ≤
      request.ceiling :=
  request.inside _ _ candidateBounded (sampled.realization.root_normSq_le index) collar inside
    (sampled.displacement request index) (le_refl request.cap)

/-- The original outside candidate and paid displacement put its actual formal-root reading above the fixed floor. -/
theorem outside (request : Norm.Radial.Request radius parameters.rootBoundTotal beta width)
    (sampled : Sampled budget reading gain_eq nodes (request.cap * beta)) (index : Fin tower.blocks.length)
    (candidateBounded : Norm.Basic.normSq (nodes[index.val]'(sampled.matched.nodeBound index)) ≤ radius)
    (collar : width ^ 2 < (Norm.Basic.normSq (nodes[index.val]'(sampled.matched.nodeBound index)) - 1) ^ 2)
    (outside : 1 < Norm.Basic.normSq (nodes[index.val]'(sampled.matched.nodeBound index))) :
    request.floor ≤
      Norm.Basic.normSq (sampled.realization.finalReading.read (tower.blocks[index.val]'index.isLt).point) :=
  request.outside _ _ candidateBounded (sampled.realization.root_normSq_le index) collar outside
    (sampled.displacement request index) (le_refl request.cap)

end Purelib.Polynomial.Dense.Roots.Tower.Reading.Sampled

end
