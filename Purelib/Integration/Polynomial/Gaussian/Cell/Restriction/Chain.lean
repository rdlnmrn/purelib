module

public import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
public import Purelib.Integration.Partition.Interval.Chain.Indexed
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.Ring

/-! # Reassembly of the same retained polynomial restriction cells

Every child consumes its existing Cached restriction. Exact interval-chain
incidence reassembles their original integral samples without constructing a
new restriction table, selecting a partition, or changing an allowance.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Restriction

open Purelib
open Purelib.Algebra
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Partition (Interval)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian
open Purelib.Polynomial.Ascending.Gaussian.Restriction (Cached)

/-- Exact polynomial integrals along the original finite interval chain telescope to its outer endpoints. -/
theorem polynomial_sum {count : Nat} (polynomial : CoefficientPolynomial)
    (intervals : Fin count → Interval) {start finish : Rational}
    (chain : Interval.Chain start finish (List.ofFn intervals)) :
    FiniteSum.Fin.sumFin (fun index => Integral.definiteIntegral polynomial
      (Cast.Path.ofCoordinate (intervals index).start) (Cast.Path.ofCoordinate (intervals index).finish)) =
      Integral.definiteIntegral polynomial (Cast.Path.ofCoordinate start) (Cast.Path.ofCoordinate finish) := by
  induction count generalizing start with
  | zero =>
      rewrite [List.ofFn_zero] at chain
      cases chain
      change (0 : Canonical) = _
      unfold Integral.definiteIntegral
      ring1
  | succ count previous =>
      rewrite [OfFn.Basic.ofFn_succ] at chain
      have first_eq : (intervals 0).start = start := chain.start_eq (Nat.zero_lt_succ _)
      rewrite [FiniteSum.Fin.sumFin_succ,
        previous (fun index => intervals index.succ) chain.tail, first_eq]
      exact (Integral.definiteIntegral_concat polynomial (Cast.Path.ofCoordinate start)
        (Cast.Path.ofCoordinate (intervals 0).finish) (Cast.Path.ofCoordinate finish)).symm

/-- The same cached restriction cells reassemble the original polynomial integral over the retained outer interval.

The family is a projection from already retained caches; this operation
executes no canonical restriction factory. Every original child integral
and its allowance remain unchanged.
-/
theorem integralSample_sum {count : Nat} (cell : CellModel) (intervals : Fin count → Interval)
    (cached : (index : Fin count) → Cached cell.polynomial
      (Cast.Path.ofCoordinate (intervals index).start) (Cast.Path.ofCoordinate (intervals index).finish))
    {start finish : Rational} (chain : Interval.Chain start finish (List.ofFn intervals)) :
    FiniteSum.Fin.sumFin (fun index => (model cell (cached index)).integralSample) =
      cell.displacement * Integral.definiteIntegral cell.polynomial
        (Cast.Path.ofCoordinate start) (Cast.Path.ofCoordinate finish) := by
  calc
    _ = FiniteSum.Fin.sumFin (fun index => cell.displacement * Integral.definiteIntegral cell.polynomial
        (Cast.Path.ofCoordinate (intervals index).start) (Cast.Path.ofCoordinate (intervals index).finish)) :=
      FiniteSum.Fin.sumFin_congr (fun index => integralSample_eq cell (cached index))
    _ = _ := by
      rewrite [FiniteSum.Fin.sumFin_mul_left, polynomial_sum cell.polynomial intervals chain]
      rfl

/-- A retained zero-to-one restriction chain recovers the SAME original cell's actual integral sample. -/
theorem integralSample_sum_unit {count : Nat} (cell : CellModel) (intervals : Fin count → Interval)
    (cached : (index : Fin count) → Cached cell.polynomial
      (Cast.Path.ofCoordinate (intervals index).start) (Cast.Path.ofCoordinate (intervals index).finish))
    (chain : Interval.Chain 0 1 (List.ofFn intervals)) :
    FiniteSum.Fin.sumFin (fun index => (model cell (cached index)).integralSample) = cell.integralSample :=
  integralSample_sum cell intervals cached chain

/-- The exact child displacement quadrance is its squared oriented width times the SAME original parent quadrance. -/
theorem displacement_normSq (cell : CellModel) {first last : Rational}
    (cached : Cached cell.polynomial (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last)) :
    Norm.Basic.normSq (model cell cached).displacement =
      (last - first) ^ 2 * Norm.Basic.normSq cell.displacement := by
  rewrite [displacement_eq, Norm.Basic.normSq_mul]
  have coordinate_eq : Cast.Path.ofCoordinate last - Cast.Path.ofCoordinate first =
      Cast.CoordinateTaylor.ofCoordinate (last - first) := by
    rewrite [Cast.ofCoordinate_sub]
    rfl
  rewrite [coordinate_eq, Norm.Basic.normSq_eq_canonical, Cast.ofCoordinate_normSq]
  rfl

end Purelib.Integration.Polynomial.Gaussian.Cell.Restriction

end
