module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Program
public import Purelib.Integration.Partition.Interval.Chain
import Purelib.Data.List.Map
import Purelib.Integration.Path.Dyadic.DyadicTrace
public import Purelib.Integration.Path.Dyadic.DyadicSteps

/-!
# Exact chart partitions of original parallel-quarter layers

The original pieces keep their closed rational Bounds, prepared sources and
cell caches. Their endpoint views form the existing exact interval Chain.
Actual midpoint children and layerAt preserve every ordered seam and both
original outer endpoints; these claims do not apply to an arbitrary Layer.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Integration
open Purelib.Integration.Path.Dyadic
open Purelib.Approximation

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

namespace Piece

/-- Read the exact two endpoints of the original closed chart span as an oriented interval view. -/
@[expose] def chartInterval (piece : Piece data actual accuracy) : Partition.Interval :=
  ⟨piece.span.lower, piece.span.upper⟩

/-- Read the ordered endpoint views without changing any original piece or closed span. -/
@[expose] def chartIntervals (pieces : List (Piece data actual accuracy)) : List Partition.Interval :=
  pieces.map chartInterval

/-- The original two midpoint children form an exact chain across the same parent span. -/
theorem children_chain (piece : Piece data actual accuracy) (split : Split piece.cell piece.within) :
    Partition.Interval.Chain piece.span.lower piece.span.upper (chartIntervals (piece.children split)) := by
  change Partition.Interval.Chain piece.span.lower piece.span.upper
    [⟨piece.span.lower, Interval.Bisection.midpoint piece.span⟩,
      ⟨Interval.Bisection.midpoint piece.span, piece.span.upper⟩]
  exact .cons (.cons (.nil piece.span.upper))

end Piece

namespace Steps

/-- Splitting a retained exact parent chain preserves its original start, finish and ordered incidence.

Every displayed parent contributes its same two cached midpoint children.
Their common midpoint and the unchanged next-parent endpoint give the child chain.
-/
theorem children_chain : {parents : List (Piece data actual accuracy)} →
    (steps : Steps parents) → {start finish : Fraction.Rational} →
    Partition.Interval.Chain start finish (Piece.chartIntervals parents) →
    Partition.Interval.Chain start finish (Piece.chartIntervals steps.children)
  | _, .nil, _, _, chain => chain
  | parent :: _, .cons split tail, _, _, chain => by
      cases chain with
      | cons remaining =>
          have combined := (parent.children_chain split).append (tail.children_chain remaining)
          change Partition.Interval.Chain _ _
            ((Piece.children parent split ++ tail.children).map Piece.chartInterval)
          rewrite [Data.List.Map.map_append]
          exact combined

end Steps

namespace Layer

variable {initial : Piece data actual accuracy} {depth : Nat}

/-- The next original cached layer preserves any established endpoint chain of its retained parents. -/
theorem next_chain (layer : Layer initial depth) (steps : Steps layer.pieces)
    {start finish : Fraction.Rational}
    (chain : Partition.Interval.Chain start finish (Piece.chartIntervals layer.pieces)) :
    Partition.Interval.Chain start finish (Piece.chartIntervals (layer.next steps).pieces) :=
  steps.children_chain chain

/-- An original retained interval Chain gives the same cached layer's first chart endpoint. -/
theorem start_eq (layer : Layer initial depth) {start finish : Fraction.Rational}
    (chain : Partition.Interval.Chain start finish (Piece.chartIntervals layer.pieces))
    (bound : 0 < layer.pieces.length) : (layer.pieces[0]'bound).span.lower = start := by
  have mappedBound : 0 < (Piece.chartIntervals layer.pieces).length := by
    rewrite [Piece.chartIntervals, Data.List.Map.length_map]
    exact bound
  have endpoint := Partition.Interval.Chain.start_eq chain mappedBound
  dsimp only [Piece.chartIntervals] at endpoint
  rewrite [Data.List.Map.getElem_map Piece.chartInterval _ 0 bound mappedBound] at endpoint
  exact endpoint

/-- An original retained interval Chain gives each exact neighboring endpoint of the same cached layer. -/
theorem seam (layer : Layer initial depth) {start finish : Fraction.Rational}
    (chain : Partition.Interval.Chain start finish (Piece.chartIntervals layer.pieces)) (index : Nat)
    (bound : index < layer.pieces.length) (nextBound : index + 1 < layer.pieces.length) :
    (layer.pieces[index]'bound).span.upper = (layer.pieces[index + 1]'nextBound).span.lower := by
  have mappedBound : index < (Piece.chartIntervals layer.pieces).length := by
    rewrite [Piece.chartIntervals, Data.List.Map.length_map]
    exact bound
  have mappedNext : index + 1 < (Piece.chartIntervals layer.pieces).length := by
    rewrite [Piece.chartIntervals, Data.List.Map.length_map]
    exact nextBound
  have endpoint := Partition.Interval.Chain.adjacent chain index mappedBound mappedNext
  dsimp only [Piece.chartIntervals] at endpoint
  rewrite [Data.List.Map.getElem_map Piece.chartInterval _ index bound mappedBound,
    Data.List.Map.getElem_map Piece.chartInterval _ (index + 1) nextBound mappedNext] at endpoint
  exact endpoint

/-- An original retained interval Chain gives the final chart endpoint of the identical cached layer. -/
theorem finish_eq (layer : Layer initial depth) {start finish : Fraction.Rational}
    (chain : Partition.Interval.Chain start finish (Piece.chartIntervals layer.pieces)) (index : Nat)
    (bound : index < layer.pieces.length) (last : index + 1 = layer.pieces.length) :
    (layer.pieces[index]'bound).span.upper = finish := by
  have mappedBound : index < (Piece.chartIntervals layer.pieces).length := by
    rewrite [Piece.chartIntervals, Data.List.Map.length_map]
    exact bound
  have mappedLast : index + 1 = (Piece.chartIntervals layer.pieces).length := by
    rewrite [Piece.chartIntervals, Data.List.Map.length_map]
    exact last
  have endpoint := Partition.Interval.Chain.finish_eq chain index mappedBound mappedLast
  dsimp only [Piece.chartIntervals] at endpoint
  rewrite [Data.List.Map.getElem_map Piece.chartInterval _ index bound mappedBound] at endpoint
  exact endpoint

end Layer

namespace Piece

/-- Every constructed dyadic layer forms an exact ordered chart chain across the original closed span.

The proof follows the same original layerAt recursion and already completed
Steps.build children. The Layer record, its actual pieces and their caches stay unchanged.
-/
theorem layerAt_chain (initial : Piece data actual accuracy) : (depth : Nat) →
    Partition.Interval.Chain initial.span.lower initial.span.upper
      (chartIntervals (initial.layerAt depth).pieces)
  | 0 => .cons (.nil initial.span.upper)
  | depth + 1 =>
      (initial.layerAt depth).next_chain (Steps.build (initial.layerAt depth).pieces)
        (layerAt_chain initial depth)

/-- The first actual piece of the constructed layer starts at the original source chart endpoint. -/
theorem layerAt_start (initial : Piece data actual accuracy) (depth : Nat)
    (bound : 0 < (initial.layerAt depth).pieces.length) :
    ((initial.layerAt depth).pieces[0]'bound).span.lower = initial.span.lower := by
  exact (initial.layerAt depth).start_eq (initial.layerAt_chain depth) bound

/-- Consecutive actual pieces of the constructed layer share their exact original closed-span endpoint. -/
theorem layerAt_seam (initial : Piece data actual accuracy) (depth index : Nat)
    (bound : index < (initial.layerAt depth).pieces.length)
    (nextBound : index + 1 < (initial.layerAt depth).pieces.length) :
    ((initial.layerAt depth).pieces[index]'bound).span.upper =
      ((initial.layerAt depth).pieces[index + 1]'nextBound).span.lower := by
  exact (initial.layerAt depth).seam (initial.layerAt_chain depth) index bound nextBound

/-- The final actual piece of the constructed layer finishes at the original finish chart endpoint. -/
theorem layerAt_finish (initial : Piece data actual accuracy) (depth index : Nat)
    (bound : index < (initial.layerAt depth).pieces.length)
    (last : index + 1 = (initial.layerAt depth).pieces.length) :
    ((initial.layerAt depth).pieces[index]'bound).span.upper = initial.span.upper := by
  exact (initial.layerAt depth).finish_eq (initial.layerAt_chain depth) index bound last

/-- Neighboring constructed source times differ by the exact width of the first original span. -/
theorem layerAt_step_width (initial : Piece data actual accuracy) (depth index : Nat)
    (bound : index < (initial.layerAt depth).pieces.length)
    (nextBound : index + 1 < (initial.layerAt depth).pieces.length) :
    ((initial.layerAt depth).pieces[index + 1]'nextBound).span.lower -
        ((initial.layerAt depth).pieces[index]'bound).span.lower =
      ((initial.layerAt depth).pieces[index]'bound).span.width := by
  rewrite [← initial.layerAt_seam depth index bound nextBound]
  rfl

/-- Each actual factory piece has exactly its original two dyadic vertices at the same bounded ordinal.

The whole original layerAt factory supplies the ordered upper times and
endpoint chain. The original start/seam readbacks recover lower endpoints;
no Piece, Reading, scalar model or chart owner is reconstructed.
-/
theorem layerAt_endpoints (initial : Piece data actual accuracy) (depth : Nat) :
    let layer := initial.layerAt depth
    let times := DyadicTrace.tail depth initial.span.lower initial.span.upper
    let same : layer.pieces.length = times.length :=
      layer.count.trans (DyadicSteps.tail_length depth initial.span.lower initial.span.upper).symm
    ∀ edge : Fin times.length,
      DyadicTrace.indexed initial.span.lower times edge.castSucc =
          (layer.pieces[edge.val]'(same.symm ▸ edge.isLt)).span.lower ∧
        DyadicTrace.indexed initial.span.lower times edge.succ =
          (layer.pieces[edge.val]'(same.symm ▸ edge.isLt)).span.upper := by
  dsimp only
  let layer := initial.layerAt depth
  let times := DyadicTrace.tail depth initial.span.lower initial.span.upper
  have same : layer.pieces.length = times.length :=
    layer.count.trans (DyadicSteps.tail_length depth initial.span.lower initial.span.upper).symm
  have upper (edge : Fin times.length) :
      times[edge.val]'edge.isLt = (layer.pieces[edge.val]'(same.symm ▸ edge.isLt)).span.upper := by
    have pieceBound : edge.val < layer.pieces.length := same.symm ▸ edge.isLt
    have mappedBound : edge.val < (layer.pieces.map (fun piece => piece.span.upper)).length := by
      rewrite [Data.List.Map.length_map]
      exact pieceBound
    have retained : times[edge.val]'edge.isLt =
        (layer.pieces.map (fun piece => piece.span.upper))[edge.val]'mappedBound :=
      getElem_congr (initial.layerAt_uppers depth).symm rfl edge.isLt
    exact retained.trans (Data.List.Map.getElem_map (fun piece => piece.span.upper)
      layer.pieces edge.val pieceBound mappedBound)
  intro edge
  constructor
  · cases edge with
    | mk index bound =>
        cases index with
        | zero =>
            change initial.span.lower = _
            exact (initial.layerAt_start depth (same.symm ▸ bound)).symm
        | succ index =>
            have previous : index < times.length := (Nat.lt_succ_self index).trans bound
            have firstBound : index < layer.pieces.length := same.symm ▸ previous
            have nextBound : index + 1 < layer.pieces.length := same.symm ▸ bound
            change times[index]'previous = _
            exact (upper ⟨index, previous⟩).trans
              (initial.layerAt_seam depth index firstBound nextBound)
  · change times[edge.val]'edge.isLt = _
    exact upper edge

end Piece

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

end
