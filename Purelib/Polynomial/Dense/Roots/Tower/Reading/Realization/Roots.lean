module

public import Purelib.Polynomial.Dense.Roots.Tower.Reading.Realization
public import Purelib.Polynomial.Dense.Roots.Tower.Factorization

/-!
# Bounds for the same original tower roots at the cached reading endpoint

The retained trace preserves each preceding root reading through every
later scalar embedding. Each actual cyclic observation pays its original
cached generator bound, and the same structural parameter total bounds
every root in the original complete ordered tower blocks.
-/

public section

namespace Purelib.Polynomial.Dense.Roots.Tower.Reading.Realization

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Algebra.Monogenic
open Purelib.Algebra.Ring (Weight GaussianReading)
open Purelib.Algebra.Monogenic.Cyclic.Element.Reading renaming
  Observation → CyclicObservation, Request → CyclicRequest
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)

universe u

variable {K : Type u} [ring : CommRing K] [equality : DecidableEq K] {polynomial : DensePolynomial K}
variable {adjunction : Companion.Adjunction polynomial}
variable {decreases : adjunction.division.quotient.natDegree + 1 = polynomial.natDegree}
variable {remaining : Tower (StageScalar adjunction) inferInstance inferInstance adjunction.division.quotient}
variable {parent : Weight K} {gain radius target tolerance : Rational}
variable {current : Cyclic.Element.Reading.Parameters adjunction.table parent gain radius}
variable {next : Parameters remaining (Cyclic.Element.weight adjunction.table parent) current.gain radius}
variable {embed : Canonical → K} {reading : GaussianReading parent embed} {gain_eq : reading.gain = gain}

/-- The cached final endpoint preserves the same original first root's actual child reading exactly. -/
theorem final_read_first_root (tail : Budget next target tolerance) (request : CyclicRequest current tolerance)
    (observation : CyclicObservation current reading gain_eq) (paid : observation.residual ≤ request.tolerance)
    (rest : Realization tail observation.child observation.gain_eq) :
    (Realization.step (decreases := decreases) tail request observation paid rest).finalReading.read
        (remaining.embed adjunction.root) = observation.child.read adjunction.root :=
  rest.final_read_embed adjunction.root

/-- The same first original root reading stays within the source-fixed total through every retained later stage. -/
theorem first_root_normSq_le (tail : Budget next target tolerance) (request : CyclicRequest current tolerance)
    (observation : CyclicObservation current reading gain_eq) (paid : observation.residual ≤ request.tolerance)
    (rest : Realization tail observation.child observation.gain_eq) :
    Norm.Basic.normSq ((Realization.step (decreases := decreases) tail request observation paid rest).finalReading.read
        (remaining.embed adjunction.root)) ≤
      (Parameters.step (decreases := decreases) current next).rootBoundTotal := by
  rewrite [final_read_first_root tail request observation paid rest, adjunction.root_eq]
  exact observation.root_normSq_le.trans (Parameters.rootBoundTotal_current_le current next)

variable {tower : Tower K ring equality polynomial} {parameters : Parameters tower parent gain radius}
variable {budget : Budget parameters target tolerance}

/-- Every same original complete tower block has an actual final root reading bounded by the cached parameter total.

Trace induction uses the same retained endpoint. The first root is preserved
by exact scalar readback through the tail; every original tail root uses its
same induction bound and the source-fixed tail-total inequality.
-/
theorem blocks_normSq_le (realization : Realization budget reading gain_eq) :
    ∀ block ∈ tower.blocks, Norm.Basic.normSq (realization.finalReading.read block.point) ≤
      parameters.rootBoundTotal := by
  cases realization with
  | mk endpoint trace =>
      induction trace with
      | constant =>
          intro block member
          cases member
      | step tail request observation paid rest previous =>
          intro block member
          cases member with
          | head => exact first_root_normSq_le tail request observation paid ⟨_, rest⟩
          | tail _ member =>
              exact (previous block member).trans (Parameters.rootBoundTotal_tail_le _ _)

/-- The original bounded root occurrence has the same source-fixed norm bound at the cached final endpoint. -/
theorem root_normSq_le (realization : Realization budget reading gain_eq) (index : Fin tower.blocks.length) :
    Norm.Basic.normSq (realization.finalReading.read (tower.blocks[index.val]'index.isLt).point) ≤
      parameters.rootBoundTotal :=
  realization.blocks_normSq_le _ (List.get_mem _ index)

end Purelib.Polynomial.Dense.Roots.Tower.Reading.Realization

end
