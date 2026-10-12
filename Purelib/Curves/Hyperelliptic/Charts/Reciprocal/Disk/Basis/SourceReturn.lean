module
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedRestoration
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationBudget
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonBankEndpointReturn
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Pay the source-path total and its initial ribbon using actual sheet return. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceReturn

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {allowance coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor : Nat}
  {index minimum readingIndex : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

variable {stage energyFloor radialDepth : Nat} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
  genus}

namespace Samples

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility

open
  CommonPreparedRestoration.BasisCommonParentRequest.Plan.Acquisition.Sample.PreparedComparison
  (restoredTotalBound restored_after_area_bound restored_after_total_bounds)

namespace SourceRestoration

/-- The combined squared-error factor for restored/source discrepancies and the actual endpoint return. -/
@[expose] def totalScale (count : Nat) : Coordinate :=
  2 * ((4 * allowance)^2 + 2 * ((count : Normalization.InverseRootPolynomial.Coordinate)^2 *
    SourceRestorationBudget.BasisCommonParentRequest.Plan.Acquisition.Sample.PreparedComparison.uniformSourceTotalError
    allowance +
    (count : Normalization.InverseRootPolynomial.Coordinate)^2 * (4 * allowance)^2))

variable {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {anchors : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} {sources :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents}
  {bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
    allowance coefficientTarget coverFloor floor}
  {plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans capSample polynomials minimum anchors
    sources bank} {inputs : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.NumericalBank index anchors
    sources}
  {readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings anchors sources bank plans inputs
    stage}
  {prepared : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.FanPreparations energyFloor anchors sources
    bank plans inputs readings}

open Purelib.Data.Rat
/-- The retained source-path total is small after the original sheet returns.

The same parent samples, restoration comparisons, paid joins and closing junction control the bound, scaled by the
squared coefficient norm. -/
theorem source_total_bound
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared)
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples)
    (joins : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junctions anchors
      sources bank) (closing :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.ClosingJunction anchors
      sources bank)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (later : joins.stage anchors sources bank ≤ stage) (closingLater : closing.stage anchors sources bank ≤ stage) :
    let previous := (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection.Samples.firstValues anchors
      sources bank plans inputs readings prepared samples).1
    let items := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs
      anchors sources bank plans inputs readings prepared samples comparisons previous
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (items.map Prod.snd).flatten) ≤
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceReturn.Samples.SourceRestoration.totalScale (allowance :=
        allowance) parents.length * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  dsimp only
  have sourceError :=
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.total_error samples
    comparisons joins branch later
  dsimp only at sourceError
  rw [Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.left] at sourceError
  have chartError := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.restored_total_error
    samples comparisons joins branch later
  dsimp only at chartError
  let connection := (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection.Samples.family samples joins
    branch later).connect
  have chartTotal := connection.summary.total_eq.symm.trans connection.total_eq
  have returned := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonBankEndpointReturn.Samples.returned_endpoint_bound
    branch anchors sources bank plans inputs readings prepared samples closing closingLater
  dsimp only at returned
  rw [← chartTotal] at returned
  have errors := (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct sourceError
      chartError) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))
  have combined := (Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct returned
      errors) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))
  unfold Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceReturn.Samples.SourceRestoration.totalScale
  convert combined using 1 <;> first | rfl | (apply congrArg Data.Gaussian.Norm.Basic.normSq; ring1) | ring1

/-- Bound the initial-value ribbon of the literal retained source path after sheet return.

The original first-value bound and source-total estimate combine with the same restoration data and late join
thresholds. -/
theorem source_ribbon_bound
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared)
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples)
    (joins : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junctions anchors
      sources bank) (closing :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonClosingJoins.BasisCommonParentBank.ClosingJunction anchors
      sources bank)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (later : joins.stage anchors sources bank ≤ stage) (closingLater : closing.stage anchors sources bank ≤ stage) :
    let previous := (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection.Samples.firstValues anchors
      sources bank plans inputs readings prepared samples).1
    let items := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs
      anchors sources bank plans inputs readings prepared samples comparisons previous
    Data.Gaussian.Norm.Basic.normSq (Path.BoundaryRibbon.area previous (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (items.map Prod.snd).flatten)) ≤
      4 * (2 + 8 * basis.coefficient) *
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceReturn.Samples.SourceRestoration.totalScale (allowance :=
        allowance) parents.length *
        (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  dsimp only
  have first := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.firstValue_bound branch
    anchors sources bank plans inputs readings prepared samples comparisons
  have total := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceReturn.Samples.SourceRestoration.source_total_bound
    samples comparisons joins closing branch later closingLater
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct first total (Gaussian.Norm.Basic.normSq_nonneg _)
    ((Gaussian.Norm.Basic.normSq_nonneg _).trans first)
  exact (Path.BoundaryRibbon.area_bound _ _).trans
    ((show 4 * Data.Gaussian.Norm.Basic.normSq _ * Data.Gaussian.Norm.Basic.normSq _ = 4 *
      (Data.Gaussian.Norm.Basic.normSq _ * Data.Gaussian.Norm.Basic.normSq _) by ring1).trans_le
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)).trans_eq (by ring1)))

end SourceRestoration
end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceReturn
