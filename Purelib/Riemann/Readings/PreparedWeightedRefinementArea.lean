module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.List.OfFn.Basic

public import Purelib.Riemann.Readings.PreparedRefinementPrimitiveArea
public import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Integration.Path.WeightedIncrementMass
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Tactic.Ring

public section

/-! Weighted comparison on the actual common refinement. Each differential
retains its own primitive, while all rows share the original child order. -/
namespace Purelib.Riemann.Readings.PreparedWeightedRefinementArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.PreparedRefinementPrimitiveArea (refinementAreaPairs refinementAreaPairs_length
  refinement_error_mass_bound)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (remainderMaximum coefficientMaximum)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data (Vector)
open _root_.Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementMass)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}
  {parents children : List (CenteredEdge curve source)} {target : Coordinate}

open Purelib.Data in
open Purelib.Riemann.Topology in
set_option genInjectivity false in
/-- Cached primitive/integral pair rows for one exact original root-subedge refinement.

Each standard differential row retains its original request family and exact recast refinement identity; columns share
the same original child list. -/
structure WeightedRefinement
    (requests : (row : Fin genus) → RequestedParents count target
      (parents.map (recastCenteredEdge (standardDifferential row))))
    (refinement : RootSubedgeRefinement parents children) where
  /-- The cached original primitive/integral pair lists, one per standard differential. -/ pairs : Data.Vector
    (List (Gaussian × Gaussian)) genus
  /-- Each cached row is exactly the original request family's recast refinement pairs. -/ pairs_eq : ∀ row, pairs row =
    refinementAreaPairs (requests row)
    (PreparedRecastRootChains.PreparedRefinementRootEndpoints.RootSubedgeRefinement.recast (standardDifferential row)
      refinement)

constructive_injectivity WeightedRefinement

namespace WeightedRefinement

variable {requests : (row : Fin genus) → RequestedParents count target
    (parents.map (recastCenteredEdge (standardDifferential row)))}
  {refinement : RootSubedgeRefinement parents children}

open Purelib.Data in
open Purelib.Riemann.Topology in
/-- Cache the original refinement-pair rows with exact dependent-vector readback identities. -/
@[expose] def build (requests : (row : Fin genus) → RequestedParents count target
    (parents.map (recastCenteredEdge (standardDifferential row))))
    (refinement : RootSubedgeRefinement parents children) : WeightedRefinement requests refinement where
  pairs := Vector.Basic.vectorOfFn (fun row => refinementAreaPairs (requests row)
    (PreparedRecastRootChains.PreparedRefinementRootEndpoints.RootSubedgeRefinement.recast (standardDifferential row)
    refinement))
  pairs_eq := fun row => Vector.Basic.vectorOfFn_apply _ row

/-- Each cached original row has exactly the retained child count. -/
theorem length_eq (bank : WeightedRefinement requests refinement) (row : Fin genus) :
    (bank.pairs row).length = children.length := by
  rw [bank.pairs_eq, refinementAreaPairs_length, Purelib.Data.List.Map.length_map]

/-- Read the exact cached row/child pair using the original length proof. -/
@[expose] def read (bank : WeightedRefinement requests refinement) (column : Fin children.length) (row : Fin genus) :
    Gaussian × Gaussian := (bank.pairs row)[column.val]'((bank.length_eq row).symm ▸ column.isLt)

open Purelib.Data.List in
/-- Reconstructing a retained list through bounded finite indices returns that exact list. -/
private theorem ofFn_readback (values : List (Gaussian × Gaussian)) (size : Nat) (length_eq : values.length = size) :
    List.ofFn (fun column : Fin size => values[column.val]'(length_eq.symm ▸ column.isLt)) = values := by
  subst size
  exact OfFn.Basic.ofFn_getElem values

/-- Enumerating the original bounded columns reads back the exact cached pair row. -/
theorem row_readback (bank : WeightedRefinement requests refinement) (row : Fin genus) :
    List.ofFn (fun column => bank.read column row) = bank.pairs row :=
  ofFn_readback _ _ (bank.length_eq row)

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The original row error budget from request maxima, recast movement mass and aggregate allowance. -/
@[expose] def errorBudget (requests : (row : Fin genus) → RequestedParents count target
    (parents.map (recastCenteredEdge (standardDifferential row))))
    (children : List (CenteredEdge curve source)) (distance : Coordinate) (row : Fin genus) : Coordinate :=
  (remainderMaximum (requests row) * distance + coefficientMaximum (requests row)) *
    movementMass (children.map (recastCenteredEdge (standardDifferential row))) +
      (5 / 2) * (Basic.PathModel.mk ((children.map (recastCenteredEdge (standardDifferential row))).map
        CenteredEdge.model)).aggregateAllowance

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Riemann.Topology in
/-- The retained row's count-weighted squared error is bounded by its exact original error budget. -/
theorem error_mass (bank : WeightedRefinement requests refinement) {distance : Coordinate}
    (nonnegative : 0 ≤ distance) (movements : ∀ child ∈ children, child.edge.pointMovement ≤ distance)
    (row : Fin genus) :
    (children.length : Coordinate) * Norm.Sum.Basic.gaussianNormSqSum ((bank.pairs row).map (fun pair => pair.1 -
      pair.2)) ≤
      errorBudget requests children distance row := by
  have moved : ∀ child ∈ children.map (recastCenteredEdge (standardDifferential row)),
      child.edge.pointMovement ≤ distance := by
    intro child member
    obtain ⟨original, inChildren, rfl⟩ := Map.mem_map.mp member
    exact movements original inChildren
  have bound := refinement_error_mass_bound (requests row)
    (PreparedRecastRootChains.PreparedRefinementRootEndpoints.RootSubedgeRefinement.recast (standardDifferential row)
      refinement) nonnegative moved
  rw [Purelib.Data.List.Map.length_map, ← bank.pairs_eq row] at bound
  exact bound

open Purelib.Data.List in
/-- Transforming enumerated original columns equals transforming the exact cached row. -/
private theorem column_map (bank : WeightedRefinement requests refinement) (row : Fin genus)
    (transform : Gaussian × Gaussian → Gaussian) :
    (List.ofFn (fun column : Fin children.length => column)).map (fun column => transform (bank.read column row)) =
      (bank.pairs row).map transform := by
  calc
    _ = (List.ofFn (fun column => bank.read column row)).map transform := by
      rw [OfFn.Basic.map_ofFn, OfFn.Basic.map_ofFn]
      rfl
    _ = _ := congrArg (List.map transform) (bank.row_readback row)

open Purelib.Algebra in
open Purelib.LinearAlgebra.Gaussian in
/-- Combine the original cached pair rows by the supplied Gaussian coefficients at each retained child index. -/
@[expose] def weightedPairs (bank : WeightedRefinement requests refinement)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : List (Gaussian × Gaussian) :=
  (List.ofFn (fun column : Fin children.length => column)).map (fun column =>
    (FiniteSum.Fin.sumFin (fun row => coefficients row * (bank.read column row).1),
     FiniteSum.Fin.sumFin (fun row => coefficients row * (bank.read column row).2)))

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Integration.Path in
open Purelib.LinearAlgebra.Gaussian in
/-- Bound the original weighted pair errors using coefficient norm and the summed row budgets.

The exact child count and cached row readbacks feed the finite weighted-mass estimate; the genus factor and original
coefficient vector are retained. -/
theorem weighted_error_mass (bank : WeightedRefinement requests refinement)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) {distance : Coordinate}
    (nonnegative : 0 ≤ distance) (movements : ∀ child ∈ children, child.edge.pointMovement ≤ distance) :
    ((bank.weightedPairs coefficients).length : Coordinate) *
      Norm.Sum.Basic.gaussianNormSqSum ((bank.weightedPairs coefficients).map (fun pair => pair.1 - pair.2)) ≤
        coefficientNormSq coefficients * ((genus : Coordinate) * FiniteSum.Fin.sumFin (errorBudget requests children
          distance)) := by
  have difference : (bank.weightedPairs coefficients).map (fun pair => pair.1 - pair.2) =
      (List.ofFn (fun column : Fin children.length => column)).map (fun column =>
        FiniteSum.Fin.sumFin (fun row => coefficients row * ((bank.read column row).1 - (bank.read column row).2))) :=
          by
    unfold weightedPairs
    rw [Purelib.Data.List.Map.map_map]
    apply Map.map_congr_left
    intro column _
    change FiniteSum.Fin.sumFin _ - FiniteSum.Fin.sumFin _ = _
    rw [← FiniteSum.Fin.sumFin_sub]
    exact FiniteSum.Fin.sumFin_congr (fun row => by ring1)
  rw [difference]
  unfold weightedPairs
  rw [Purelib.Data.List.Map.length_map]
  apply WeightedIncrementMass.weighted_increment_mass
  intro row
  rw [OfFn.Basic.length_ofFn, bank.column_map row (fun pair => pair.1 - pair.2)]
  exact bank.error_mass nonnegative movements row

end WeightedRefinement
end Purelib.Riemann.Readings.PreparedWeightedRefinementArea
