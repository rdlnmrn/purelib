module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
public import Purelib.Riemann.Paths.PreparedPrimitivePathArea
import Purelib.Integration.Path.Dyadic.DyadicAreaRefinement
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Tactic.Ring

public section

/-! Cached synchronized polynomial/integral pairs retain the actual prepared
children. Per-row errors and slopes carry the common dyadic scale. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Integration.Path.Dyadic

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths.PreparedPrimitivePathArea

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations
  (PrimitiveBank)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest (BasisPreparedCommonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest
  (Acquisition)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {covers :
    BasisSourceCovers parent}
  {index : Nat} {box : Purelib.Geometry.Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin_zero sumFin_mul_right)

open Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples (DyadicSample)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements_sub_constant pathArea_dyadicIncrements)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)

variable {cover : Cover data} {target :
  Coordinate} {floor : Nat}

variable {minimum : Nat} {common :
  BasisCommonCover cover covers minimum}

open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledLocalRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests (CoupledLocalPlan)

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_eq_mul_pow)
open _root_.Purelib.Data (Vector)
open _root_.Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

namespace BasisPreparedCommonRequest.Acquisition

variable {areaAllowance sourceTarget coefficientTarget : Coordinate}
  {request : BasisPreparedCommonRequest
    regular common areaAllowance sourceTarget coefficientTarget floor}
  {polynomials : RegularBasisPolynomials cap
    index box} {originals :
    PrimitiveBank
    covers index}
  {cells : BasisSourceLocations.SampleBank
    covers index} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {depth : Nat}

/-- The primitive-increment and child-integral pairs for one retained prepared row.

The local request supplies both values for the same prepared children.
This readback retains its exact row and synchronized sample indices. -/
@[expose] def rowPairs (acquired : BasisPreparedCommonRequest.Acquisition request polynomials originals cells
  coefficients depth) (row : Fin genus) :
    List (InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian) := LocalRequest.areaPairs
      (acquired.prepared.get row).localRequest

set_option genInjectivity false in
/-- Cached synchronized primitive/integral pairs for every original basis row.

The cache retains the actual prepared children at the shared dyadic depth. -/
structure ChildPairs (acquired : BasisPreparedCommonRequest.Acquisition request polynomials originals cells coefficients
  depth) where
  /-- The cached list of actual child pairs for each retained basis row. -/ values : Data.Vector (List
    (InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian)) genus
  /-- Each row cache reads its actual prepared primitive/integral pairs. -/ values_eq : ∀ row, values row =
    rowPairs
    acquired row

constructive_injectivity ChildPairs

/-- Cache every retained row's actual prepared child pairs once.

Each row reads the supplied local request's prepared children. The vector
caches those exact pairs and retains its dependent readback equality. -/
@[expose] def childPairs (acquired : BasisPreparedCommonRequest.Acquisition request polynomials originals cells
  coefficients depth) :
  ChildPairs
  acquired :=
  ⟨vectorOfFn
    (rowPairs
    acquired), Data.Vector.Basic.vectorOfFn_apply _⟩

namespace ChildPairs

variable {acquired :
  Acquisition
  request polynomials originals cells coefficients depth}

/-- Every retained row contains exactly the dyadic number of children at the common depth.

The row cache reads the actual local request pairs. Its retained child-count
and common-depth equations identify the exact finite list length. -/
theorem count_eq (pairs :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired) (row : Fin genus) :
    (pairs.values row).length = 2 ^ (common.depth + acquired.extraDepth) := by
  rw [pairs.values_eq]
  unfold
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.rowPairs
    LocalRequest.areaPairs
  rw [Map.length_map, (acquired.prepared.get row).localRequest.request.block.childCount, acquired.depths_eq]

/-- The first coordinates of each retained row are the original primitive's synchronized dyadic increments.

Mapping the first projection preserves the synchronized source increments.
The same cached row and common depth supply their original path equation. -/
theorem source_path (pairs :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired) (row : Fin genus) :
    (pairs.values row).map Prod.fst = DyadicPrimitivePaths.dyadicIncrements
      (fun parameter => (originals.get row).primitive.value.eval (parent.edge.point parameter))
      (common.depth + acquired.extraDepth) 0 1 := by
  rw [pairs.values_eq]
  unfold
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.rowPairs
    LocalRequest.areaPairs
  rw [Map.map_map]
  exact acquired.synchronized_primitive_path row

/-- The quarter-radius bound is monotone in its initial scale at a fixed depth.

The retained geometric factor is nonnegative at every finite depth.
Multiplication transports the supplied initial-scale inequality. -/
private theorem quarter_mono {first last : InverseRootPolynomial.Coordinate} (small : first ≤ last) (depth : Nat) :
    Geometric.Basic.quarterRadius first depth ≤ Geometric.Basic.quarterRadius last depth := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct small (Fraction.Order.Arithmetic.pow_nonneg_direct
    (by decide) depth)

/-- Each actual child pair satisfies the retained source-tolerance error at the common dyadic scale.

The actual local request error and retained source tolerance are compared
at the same common dyadic depth and selected child pair. -/
theorem errors (pairs :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired) (row : Fin genus) (pair : InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian) (member : pair ∈
  pairs.values row) :
    Data.Gaussian.Norm.Basic.normSq (pair.1 - pair.2) ≤ Geometric.Basic.quarterRadius request.sourceTolerance
      (common.depth + acquired.extraDepth) := by
  rw [pairs.values_eq] at member
  have bounded := LocalRequest.areaPairs_errors
    (acquired.prepared.get row).localRequest pair member
  rw [acquired.depths_eq] at bounded
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at bounded
  exact bounded.trans
    (quarter_mono
    ((LocalRequest.areaComparisonError_lt
      (acquired.prepared.get row).localRequest request.tolerance_positive).le) _)

/-- Each actual primitive child increment obeys its original source-slope bound at the common dyadic scale.

The retained primitive increment certificate bounds that exact first
coordinate at the synchronized common depth. -/
theorem source_bound (pairs :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired) (row : Fin genus) (pair : InverseRootPolynomial.Gaussian × InverseRootPolynomial.Gaussian) (member : pair ∈
  pairs.values row) :
    Data.Gaussian.Norm.Basic.normSq pair.1 ≤ Geometric.Basic.quarterRadius (covers.get row).data.sourceSlope
      (common.depth + acquired.extraDepth) := by
  have present : pair.1 ∈ (pairs.values row).map Prod.fst := Map.mem_map.mpr ⟨pair, member, rfl⟩
  rw [pairs.source_path] at present
  have bound := DyadicAreaRefinement.dyadicIncrements_bounded
    (fun parameter => (originals.get row).primitive.value.eval (parent.edge.point parameter))
    (fun _ _ firstInside lastInside => (originals.get row).increment_bound firstInside lastInside)
    (common.depth + acquired.extraDepth) (first := 0) (last := 1) ⟨le_rfl, by decide⟩ ⟨by decide, le_rfl⟩ (by decide)
      pair.1 present
  exact bound.trans_eq (by ring1)

/-- Read a retained child pair with its supplied finite index bound.

The row-count equation transports the original column bound to the cached
list length. The lookup consumes that same cache and certificate. -/
@[expose] def read (pairs :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired) (row : Fin genus) (column : Fin (2 ^ (common.depth + acquired.extraDepth))) :
    InverseRootPolynomial.Gaussian × Gaussian :=
  (pairs.values row)[column.val]'((pairs.count_eq row).symm ▸ column.isLt)

/-- Reading a child pair with its retained finite bound returns an actual entry in that row.

The row-count equation supplies the same cached-list bound used by read.
The original indexed occurrence certificate then identifies the retained pair. -/
theorem read_mem (pairs :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
  acquired) (row : Fin genus) (column : Fin (2 ^ (common.depth + acquired.extraDepth))) :
    pairs.read row column ∈ pairs.values row := List.getElem_mem ((pairs.count_eq row).symm ▸ column.isLt)

end ChildPairs
end BasisPreparedCommonRequest.Acquisition
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
