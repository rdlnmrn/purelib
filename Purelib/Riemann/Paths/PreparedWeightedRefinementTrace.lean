module
import Purelib.Data.List.Map
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Paths.PathArea
public import Purelib.Riemann.Readings.PreparedWeightedRefinementArea

import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaMassComparison
import Purelib.Riemann.Integration.PreparedWeightedSourceMass
import Purelib.Tactic.Ring
import Purelib.Riemann.Paths.PreparedNestedDyadicPaths
public import Purelib.Riemann.Integration.PreparedDyadicPrimitiveResampling

public section

/-! Full weighted traces retain their initial ribbon and each ancestor's
primitive. Dyadic readbacks concern the literal row paths, not only totals. -/
namespace Purelib.Riemann.Paths.PreparedWeightedRefinementTrace

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Paths.PreparedNestedDyadicPaths (DyadicPaths)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.PreparedWeightedRefinementArea (WeightedRefinement)
open Purelib.Riemann.Readings.PreparedWeightedRefinementArea.WeightedRefinement (errorBudget weightedPairs)
open Purelib.Riemann.Integration.PreparedDyadicPrimitiveResampling (PrimitiveSlopeBound)
open Purelib.Riemann.Readings.PreparedRefinementPrimitiveArea (refinementAreaPairs_right)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum normSq_gaussianSum_le)
open Purelib.Integration.Path.IncrementArea (pathArea traceArea)
open Purelib.Integration.Path.BoundaryRibbon (area)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}
  {parents children : List (CenteredEdge curve source)} {target : Coordinate}
  {requests : (row : Fin genus) → RequestedParents count target
    (parents.map (recastCenteredEdge (standardDifferential row)))}
  {refinement : RootSubedgeRefinement parents children}

open Purelib.Data in

open Purelib.Algebra in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Bound the total error of a weighted refinement by its retained row budgets.

A common nonnegative movement ceiling for the actual children gives the coefficient squared norm times genus times the
sum of the original row error budgets. -/
theorem total_error (bank : WeightedRefinement requests refinement)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) {distance : Coordinate}
    (nonnegative : 0 ≤ distance) (movements : ∀ child ∈ children, child.edge.pointMovement ≤ distance) :
    normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum ((bank.weightedPairs coefficients).map Prod.fst) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((bank.weightedPairs coefficients).map Prod.snd)) ≤
        coefficientNormSq coefficients * ((genus : Coordinate) * FiniteSum.Fin.sumFin (errorBudget requests children
          distance)) := by
  rw [← Gaussian.Norm.Sum.Basic.gaussianSum_map_sub (bank.weightedPairs coefficients) Prod.fst Prod.snd]
  have bound := Gaussian.Norm.Sum.Basic.normSq_gaussianSum_le ((bank.weightedPairs coefficients).map (fun pair => pair.1
    - pair.2))
  rw [Purelib.Data.List.Map.length_map] at bound
  exact bound.trans (bank.weighted_error_mass coefficients nonnegative movements)

section
open Purelib.Data
/-- The sum of squared Gaussian norms is nonnegative. -/
private theorem normSum_nonnegative : ∀ values : List Gaussian, 0 ≤ Gaussian.Norm.Sum.Basic.gaussianNormSqSum values
  | [] => le_rfl
  | value :: values => add_nonneg (Gaussian.Basic.Canonical.normSq_nonneg value) (normSum_nonnegative values)

/-- Reversing every paired difference preserves the sum of squared errors. -/
private theorem reverse_errors (pairs : List (Gaussian × Gaussian)) :
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum (pairs.map (fun pair => pair.2 - pair.1)) =
      Gaussian.Norm.Sum.Basic.gaussianNormSqSum (pairs.map (fun pair => pair.1 - pair.2)) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      change normSq (pair.2 - pair.1) + Gaussian.Norm.Sum.Basic.gaussianNormSqSum _ = normSq (pair.1 - pair.2) +
        Gaussian.Norm.Sum.Basic.gaussianNormSqSum _
      rw [show pair.2 - pair.1 = -(pair.1 - pair.2) by ring1, Gaussian.Basic.Canonical.normSq_neg, ih]

end

open Purelib.Integration in
open Purelib.Data in
/-- Bound the complete path-area discrepancy using count-weighted error and source masses.

For nonnegative mass ceilings the squared area discrepancy is at most 32 times the error ceiling times the sum of the
two ceilings. -/
private theorem source_area_of_mass (pairs : List (Gaussian × Gaussian)) {error source : Coordinate}
    (errorNonnegative : 0 ≤ error) (sourceNonnegative : 0 ≤ source)
    (errors : (pairs.length : Coordinate) * Gaussian.Norm.Sum.Basic.gaussianNormSqSum (pairs.map (fun pair => pair.1 -
      pair.2)) ≤ error)
    (sources : (pairs.length : Coordinate) * Gaussian.Norm.Sum.Basic.gaussianNormSqSum (pairs.map Prod.fst) ≤ source) :
    normSq (Path.IncrementArea.pathArea (pairs.map Prod.fst) - Path.IncrementArea.pathArea (pairs.map Prod.snd)) ≤ 32 *
      error * (source + error) := by
  have swappedErrors : ((pairs.map Prod.swap).length : Coordinate) *
      Gaussian.Norm.Sum.Basic.gaussianNormSqSum ((pairs.map Prod.swap).map (fun pair => pair.1 - pair.2)) ≤ error := by
    rw [Purelib.Data.List.Map.length_map, Purelib.Data.List.Map.map_map]
    change (pairs.length : Coordinate) * Gaussian.Norm.Sum.Basic.gaussianNormSqSum (pairs.map (fun pair => pair.2 -
      pair.1)) ≤ error
    rw [reverse_errors]
    exact errors
  have swappedSources : ((pairs.map Prod.swap).length : Coordinate) *
      Gaussian.Norm.Sum.Basic.gaussianNormSqSum ((pairs.map Prod.swap).map Prod.snd) ≤ source := by
    rw [Purelib.Data.List.Map.length_map, Purelib.Data.List.Map.map_map]
    exact sources
  have bound := Path.IncrementAreaMassComparison.pathArea_difference_of_mass_bounds (pairs.map Prod.swap)
    errorNonnegative sourceNonnegative swappedErrors swappedSources
  rw [Purelib.Data.List.Map.map_map, Purelib.Data.List.Map.map_map] at bound
  simp only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] at bound
  change normSq (Path.IncrementArea.pathArea (pairs.map Prod.snd) - Path.IncrementArea.pathArea (pairs.map Prod.fst)) ≤
    _ at bound
  rw [show Path.IncrementArea.pathArea (pairs.map Prod.fst) - Path.IncrementArea.pathArea (pairs.map Prod.snd) =
    -(Path.IncrementArea.pathArea (pairs.map Prod.snd) - Path.IncrementArea.pathArea (pairs.map Prod.fst)) by ring1,
      Gaussian.Basic.Canonical.normSq_neg]
  exact bound

open Purelib.Algebra in
open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
open Purelib.LinearAlgebra in
/-- Compare the weighted primitive and sample areas using a fixed source ceiling.

The retained dyadic paths and original row slope bounds determine the source mass before acquisition; the result is
homogeneous of degree four in the coefficients. -/
theorem area_bound (bank : WeightedRefinement requests refinement) {depth : Nat}
    (paths : DyadicPaths depth refinement)
    (slopes : Fin genus → Coordinate) (bounded : ∀ row, PrimitiveSlopeBound (slopes row) (requests row))
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) {distance : Coordinate}
    (nonnegative : 0 ≤ distance) (movements : ∀ child ∈ children, child.edge.pointMovement ≤ distance) :
    let error := (genus : Coordinate) * FiniteSum.Fin.sumFin (errorBudget requests children distance)
    let sourceBound := (parents.length : Coordinate)^2 * (genus : Coordinate) * FiniteSum.Fin.sumFin slopes
    normSq (Path.IncrementArea.pathArea ((bank.weightedPairs coefficients).map Prod.fst) -
      Path.IncrementArea.pathArea ((bank.weightedPairs coefficients).map Prod.snd)) ≤
        32 * error * (sourceBound + error) * coefficientNormSq coefficients ^ 2 := by
  have errors := Readings.PreparedWeightedRefinementArea.WeightedRefinement.weighted_error_mass bank coefficients
    nonnegative movements
  have sources := Integration.PreparedWeightedSourceMass.source_mass bank paths slopes bounded coefficients
  have countNonnegative := Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le (bank.weightedPairs
    coefficients).length)
  have errorNonnegative := (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct countNonnegative (normSum_nonnegative
    _)).trans errors
  have sourceNonnegative := (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct countNonnegative (normSum_nonnegative
    _)).trans sources
  exact (source_area_of_mass _ errorNonnegative sourceNonnegative errors sources).trans_eq (by ring1)

open Purelib.Integration in
open Purelib.Data in
/-- Combine area and total-error bounds with a retained starting-value bound.

The starting ribbon is paid against the actual total discrepancy, yielding the complete trace bound with the same
coefficient homogeneity. -/
private theorem trace_of_bounds (left right : List Gaussian) (start : Gaussian)
    {error sample coefficient originBound : Coordinate}
    (areaBound : normSq (Path.IncrementArea.pathArea left - Path.IncrementArea.pathArea right) ≤ 32 * error * (sample +
      error) * coefficient ^ 2)
    (totalBound : normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum left - Data.Gaussian.Norm.Sum.Basic.gaussianSum
      right) ≤ coefficient * error)
    (origin : normSq start ≤ originBound * coefficient) :
    normSq (Path.IncrementArea.traceArea start left - Path.IncrementArea.traceArea start right) ≤
      (64 * error * (sample + error) + 8 * originBound * error) * coefficient ^ 2 := by
  have product := Rat.Fraction.Order.Arithmetic.mul_le_mul_direct origin totalBound
    (Gaussian.Basic.Canonical.normSq_nonneg _) ((Gaussian.Basic.Canonical.normSq_nonneg start).trans origin)
  have scaled := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by
      decide : (0 : Coordinate) ≤ 4)
  have ribbonBase := Path.BoundaryRibbon.area_bound start
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum left - Data.Gaussian.Norm.Sum.Basic.gaussianSum right)
  simp only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] at ribbonBase
  have ribbon := ribbonBase.trans
    ((show 4 * normSq start * normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum left -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum right) =
      4 * (normSq start * normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum left -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum right)) by ring1).trans_le scaled)
  have difference (left right : Gaussian) : Path.BoundaryRibbon.area start left - Path.BoundaryRibbon.area start right =
    Path.BoundaryRibbon.area start (left - right) := by
    apply Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, Path.BoundaryRibbon.area, Data.Gaussian.Basic.conj,
      Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1
  rw [Path.IncrementArea.traceArea_eq, Path.IncrementArea.traceArea_eq,
    show ∀ a b c d : Gaussian, a + b - (c + d) = (a - c) + (b - d) from fun _ _ _ _ => by ring1,
    difference]
  have triangle := Gaussian.Norm.Bounds.normSq_add_le_two
    (Path.IncrementArea.pathArea left - Path.IncrementArea.pathArea right)
    (Path.BoundaryRibbon.area start (Data.Gaussian.Norm.Sum.Basic.gaussianSum left -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum right))
  simp only [-eq_self, -iff_self, Gaussian.Norm.Basic.normSq_eq_canonical] at triangle
  exact triangle.trans
    ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Rat.Fraction.Order.Arithmetic.add_le_add_direct
      areaBound ribbon) (by decide : (0 : Coordinate) ≤ 2)).trans_eq (by ring1))

open Purelib.Algebra in
open Purelib.Integration in
open Purelib.LinearAlgebra in
/-- Bound complete weighted traces including the starting-value ribbon.

The original dyadic child paths, row slopes and homogeneous starting-value ceiling pay both the centered area and the
actual total model error. -/
theorem trace_bound (bank : WeightedRefinement requests refinement) {depth : Nat}
    (paths : DyadicPaths depth refinement)
    (slopes : Fin genus → Coordinate) (bounded : ∀ row, PrimitiveSlopeBound (slopes row) (requests row))
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (start : Gaussian) {distance originBound :
      Coordinate}
    (nonnegative : 0 ≤ distance) (movements : ∀ child ∈ children, child.edge.pointMovement ≤ distance)
    (origin : normSq start ≤ originBound * coefficientNormSq coefficients) :
    let error := (genus : Coordinate) * FiniteSum.Fin.sumFin (errorBudget requests children distance)
    let sample := (parents.length : Coordinate)^2 * (genus : Coordinate) * FiniteSum.Fin.sumFin slopes
    normSq (Path.IncrementArea.traceArea start ((bank.weightedPairs coefficients).map Prod.fst) -
      Path.IncrementArea.traceArea start ((bank.weightedPairs coefficients).map Prod.snd)) ≤
        (64 * error * (sample + error) + 8 * originBound * error) * coefficientNormSq coefficients ^ 2 := by
  exact trace_of_bounds _ _ start (area_bound bank paths slopes bounded coefficients nonnegative movements)
    (total_error bank coefficients nonnegative movements) origin

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
/-- Every weighted sample row reads back to the original recast child model sequence. -/
theorem sample_row (bank : WeightedRefinement requests refinement) (row : Fin genus) :
    List.ofFn (fun column => (bank.read column row).2) =
      Paths.PathArea.increments (Polynomial.Gaussian.Path.Basic.PathModel.mk
        ((children.map (recastCenteredEdge (standardDifferential row))).map CenteredEdge.model)) := by
  calc
    _ = (List.ofFn (fun column => bank.read column row)).map Prod.snd := List.OfFn.Basic.map_ofFn.symm
    _ = (bank.pairs row).map Prod.snd := congrArg (List.map Prod.snd) (bank.row_readback row)
    _ = _ := by rw [bank.pairs_eq, refinementAreaPairs_right]

end Purelib.Riemann.Paths.PreparedWeightedRefinementTrace
