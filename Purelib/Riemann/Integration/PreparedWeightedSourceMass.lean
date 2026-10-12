module
import Purelib.Data.List.Map
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Integration.Path.WeightedIncrementMass
public import Purelib.Riemann.Readings.PreparedWeightedRefinementArea
import Purelib.Riemann.Paths.PreparedRecastDyadicPaths
import Purelib.Riemann.Integration.PreparedDyadicPrimitiveMass
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Readings.PreparedDyadicPrimitiveArea
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Paths.PreparedNestedDyadicPaths
public import Purelib.Riemann.Integration.PreparedDyadicPrimitiveResampling
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! A source-cover ceiling for the actual weighted refinement. Unlike a
new request's sample density, these slopes can be fixed before acquisition. -/
namespace Purelib.Riemann.Integration.PreparedWeightedSourceMass

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Paths.PreparedNestedDyadicPaths (DyadicPaths)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.PreparedWeightedRefinementArea (WeightedRefinement)
open Purelib.Riemann.Readings.PreparedWeightedRefinementArea.WeightedRefinement (weightedPairs)
open Purelib.Riemann.Readings.PreparedDyadicPrimitiveArea (dyadicPrimitivePath refinementAreaPairs_dyadic)
open Purelib.Riemann.Integration.PreparedDyadicPrimitiveResampling (PrimitiveSlopeBound)
open Purelib.Riemann.Integration.PreparedDyadicPrimitiveMass (dyadicPrimitivePath_mass)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_mul_left)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parents children : List (CenteredEdge curve source)} {target : Coordinate}
  {requests : (row : Fin genus) → RequestedParents count target
    (parents.map (recastCenteredEdge (standardDifferential row)))}
  {refinement : RootSubedgeRefinement parents children}

open Purelib.Data.List in
open Purelib.Riemann.Paths in
/-- Reading first components of the cached pair row gives the original dyadic primitive path. -/
theorem source_row (bank : WeightedRefinement requests refinement) {depth : Nat}
    (paths : DyadicPaths depth refinement) (row : Fin genus) :
    List.ofFn (fun column => (bank.read column row).1) = dyadicPrimitivePath depth (requests row) := by
  calc
    _ = (List.ofFn (fun column => bank.read column row)).map Prod.fst := OfFn.Basic.map_ofFn.symm
    _ = (bank.pairs row).map Prod.fst := congrArg (List.map Prod.fst) (bank.row_readback row)
    _ = _ := by
      rw [bank.pairs_eq]
      exact refinementAreaPairs_dyadic (requests row) _
        (PreparedRecastDyadicPaths.DyadicPaths.recast paths (standardDifferential row))

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Path in
open Purelib.LinearAlgebra.Gaussian in
/-- Bound the original coefficient-weighted source mass by its retained primitive slopes.

The bound keeps the exact parent count squared, genus factor and coefficient norm, using each cached row's original
dyadic path identity. -/
theorem source_mass (bank : WeightedRefinement requests refinement) {depth : Nat}
    (paths : DyadicPaths depth refinement)
    (slopes : Fin genus → Coordinate) (bounded : ∀ row, PrimitiveSlopeBound (slopes row) (requests row))
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    ((bank.weightedPairs coefficients).length : Coordinate) *
      Norm.Sum.Basic.gaussianNormSqSum ((bank.weightedPairs coefficients).map Prod.fst) ≤
        coefficientNormSq coefficients * ((parents.length : Coordinate)^2 * (genus : Coordinate) * FiniteSum.Fin.sumFin
          slopes) := by
  have rows (row : Fin genus) : (children.length : Coordinate) *
      Norm.Sum.Basic.gaussianNormSqSum (List.ofFn (fun column => (bank.read column row).1)) ≤
        (parents.length : Coordinate)^2 * slopes row := by
    have mass := dyadicPrimitivePath_mass (requests row) (bounded row) depth
    rw [← source_row bank paths row, OfFn.Basic.length_ofFn, Purelib.Data.List.Map.length_map] at mass
    exact mass
  have mass := WeightedIncrementMass.weighted_increment_mass
    (List.ofFn (fun column : Fin children.length => column)) (fun column row => (bank.read column row).1)
    coefficients (fun row => (parents.length : Coordinate)^2 * slopes row) (by
      intro row
      rw [OfFn.Basic.length_ofFn, OfFn.Basic.map_ofFn]
      exact rows row)
  have path : (bank.weightedPairs coefficients).map Prod.fst =
      (List.ofFn (fun column : Fin children.length => column)).map
        (fun column => FiniteSum.Fin.sumFin (fun row => coefficients row * (bank.read column row).1)) :=
          Purelib.Data.List.Map.map_map ..
  rw [path]
  unfold weightedPairs
  rw [Purelib.Data.List.Map.length_map]
  exact mass.trans_eq (by rw [FiniteSum.Fin.sumFin_mul_left]; ring1)

end Purelib.Riemann.Integration.PreparedWeightedSourceMass
