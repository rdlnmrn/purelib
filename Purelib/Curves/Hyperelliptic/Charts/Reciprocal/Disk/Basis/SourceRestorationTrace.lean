module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Decide
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
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
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs
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

/-! Complete restored/source trace comparison on the retained parent bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace

open SourceRestorationBudget.BasisCommonParentRequest.Plan.Acquisition.Sample
open CommonPreparedRestoration.BasisCommonParentRequest.Plan.Acquisition

open Purelib.Data.Rat

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

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration
  (pairs totalBound bounded length)
open
  SourceRestorationBudget.BasisCommonParentRequest.Plan.Acquisition.Sample.PreparedComparison
  (uniformSourceAreaError uniformSourceTotalError)

/-- The complete original restored/source area-error factor from block count, source slope and retained increment
bounds. -/
@[expose] def areaScale (count : Nat) (slope : Normalization.InverseRootPolynomial.Coordinate) : Coordinate :=
  2 * ((count : Normalization.InverseRootPolynomial.Coordinate)^2 *
    PreparedComparison.uniformSourceAreaError
    allowance slope +
    16 * (count : Normalization.InverseRootPolynomial.Coordinate)^4 *
      PreparedComparison.uniformSourceTotalError
      allowance * Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.totalBound
      (basis := basis) (allowance := allowance) slope)

/-- The original restored/source trace-error factor including its initial-value ribbon contribution. -/
@[expose] def traceScale (count : Nat) (slope : Normalization.InverseRootPolynomial.Coordinate) : Coordinate :=
  2 * (Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.areaScale (basis :=
    basis) (allowance := allowance) count slope +
    4 * (2 + 8 * basis.coefficient) * (count : Normalization.InverseRootPolynomial.Coordinate)^2 *
      PreparedComparison.uniformSourceTotalError
      allowance)

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

open Purelib.Algebra in
open Purelib.Data.Rat in
/-- The complete original restored and source polygons satisfy their coefficient-weighted area comparison after all
retained joins are paid. -/
theorem area_bound
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared)
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples)
    (joins : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junctions anchors
      sources bank) (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (later : joins.stage anchors sources bank ≤ stage) :
    let previous := (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection.Samples.firstValues anchors
      sources bank plans inputs readings prepared samples).1
    let items := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs
      anchors sources bank plans inputs readings prepared samples comparisons previous
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea (items.map Prod.fst).flatten -
      Path.IncrementArea.pathArea (items.map Prod.snd).flatten) ≤
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.areaScale (basis :=
        basis) (allowance := allowance) parents.length
        (WeightedResampling.BasisCommonParentBank.Samples.weightedSourceSlopeMaximum
        anchors sources) *
        (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  dsimp only
  have bounds := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.bounded
    samples comparisons joins branch later
  have normNonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _ (fun row => Gaussian.Basic.Canonical.normSq_nonneg
      (coefficients row)))
  have errorNonnegative : 0 ≤
    PreparedComparison.uniformSourceTotalError
    allowance :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
      Normalization.InverseRootPolynomial.Coordinate) ≤ 2050) (Fraction.Order.Arithmetic.sq_nonneg_direct allowance)
  have totalNonnegative : 0 ≤
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.totalBound (basis :=
    basis) (allowance := allowance)
    (WeightedResampling.BasisCommonParentBank.Samples.weightedSourceSlopeMaximum
    anchors sources) :=

      (WeightedResampling.BasisCommonParentBank.Samples.weightedSourceSlopeMaximum_nonnegative
      anchors sources).trans (Fraction.Order.Basic.le_max_right _ _)
  have estimate := Path.IncrementAreaComparison.blocks_area_difference_bound
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs anchors sources
      bank plans inputs readings prepared samples comparisons
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection.Samples.firstValues anchors sources bank plans
        inputs readings prepared samples).1)
    (Fraction.Order.Arithmetic.mul_nonneg_direct errorNonnegative normNonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct totalNonnegative normNonnegative)
    (fun pair member => (bounds pair member).1) (fun pair member => (bounds pair member).2.1)
    (fun pair member => (bounds pair member).2.2.1) (fun pair member => (bounds pair member).2.2.2)
  rw [Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.length] at estimate
  exact estimate.trans_eq (by
    unfold Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.areaScale
    ring1)

/-- The sum of the original block increment differences equals the difference of the flattened path totals. -/
private theorem paired_total_sum (items : List (List Normalization.InverseRootPolynomial.Gaussian × List
  Normalization.InverseRootPolynomial.Gaussian)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (items.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.2)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (items.map Prod.fst).flatten - Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (items.map Prod.snd).flatten := by
  induction items with
  | nil => change (0 : Normalization.InverseRootPolynomial.Gaussian) = 0 - 0; ring1
  | cons pair tail ih =>
      simp only [-eq_self, -iff_self, List.map_cons, List.flatten_cons, Path.IncrementArea.sum_append,
        Data.Gaussian.Norm.Sum.Basic.gaussianSum, ih]
      ring1

/-- The original restored/source increment discrepancy is bounded by the squared retained parent count and common
per-block allowance. -/
theorem total_error
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared)
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples)
    (joins : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junctions anchors
      sources bank) (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (later : joins.stage anchors sources bank ≤ stage) :
    let previous := (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection.Samples.firstValues anchors
      sources bank plans inputs readings prepared samples).1
    let items := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs
      anchors sources bank plans inputs readings prepared samples comparisons previous
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (items.map Prod.fst).flatten -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (items.map Prod.snd).flatten) ≤
      (parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 *
        PreparedComparison.uniformSourceTotalError
        allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by
  dsimp only
  have bounds := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.bounded
    samples comparisons joins branch later
  let items := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs anchors
    sources bank plans inputs readings prepared samples comparisons
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection.Samples.firstValues anchors sources bank plans
      inputs readings prepared samples).1
  have estimate := Gaussian.Norm.Sum.Bounds.normSq_sum_le
    (items.map (fun pair => Data.Gaussian.Norm.Sum.Basic.gaussianSum pair.1 - Data.Gaussian.Norm.Sum.Basic.gaussianSum
      pair.2))
      (PreparedComparison.uniformSourceTotalError
      allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) (by
      intro value member
      obtain ⟨pair, inPairs, equal⟩ := Data.List.Map.mem_map.mp member
      rw [← equal]
      exact (bounds pair inPairs).2.1)
  rw [Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.paired_total_sum,
    List.Map.length_map] at estimate
  dsimp only [-eq_self, -iff_self, items] at estimate
  rw [Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.length] at estimate
  exact estimate.trans_eq (by ring1)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration in
open Purelib.Data.Rat in
/-- Transport complete restored traces to their literal cached source paths,
including the initial-value ribbon against the accumulated endpoint error. -/
theorem trace_bound
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared)
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples)
    (joins : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins.BasisCommonParentBank.Junctions anchors
      sources bank) (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (later : joins.stage anchors sources bank ≤ stage) :
    let previous := (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection.Samples.firstValues anchors
      sources bank plans inputs readings prepared samples).1
    let items := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs
      anchors sources bank plans inputs readings prepared samples comparisons previous
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.traceArea previous (items.map Prod.fst).flatten -
      Path.IncrementArea.traceArea previous (items.map Prod.snd).flatten) ≤
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.traceScale (basis :=
        basis) (allowance := allowance) parents.length
        (WeightedResampling.BasisCommonParentBank.Samples.weightedSourceSlopeMaximum
        anchors sources) *
        (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  dsimp only
  let previous := (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentConnection.Samples.firstValues anchors sources
    bank plans inputs readings prepared samples).1
  let items := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationPairs.Samples.SourceRestoration.pairs anchors
    sources bank plans inputs readings prepared samples comparisons previous
  let left := (items.map Prod.fst).flatten
  let right := (items.map Prod.snd).flatten
  have first := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedConcatenation.Samples.firstValue_bound branch
    anchors sources bank plans inputs readings prepared samples comparisons
  have total := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.total_error
    samples comparisons joins branch later
  have area := Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.area_bound
    samples comparisons joins branch later
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct first total (Gaussian.Norm.Basic.normSq_nonneg _)
    ((Gaussian.Norm.Basic.normSq_nonneg _).trans first)
  have ribbon : Data.Gaussian.Norm.Basic.normSq (Path.BoundaryRibbon.area previous
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum left - Data.Gaussian.Norm.Sum.Basic.gaussianSum right)) ≤
      4 * (2 + 8 * basis.coefficient) * (parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 *
        PreparedComparison.uniformSourceTotalError
        allowance * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
    calc
      _ ≤ 4 * Data.Gaussian.Norm.Basic.normSq previous * Data.Gaussian.Norm.Basic.normSq
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum left - Data.Gaussian.Norm.Sum.Basic.gaussianSum right) :=
        Path.BoundaryRibbon.area_bound _ _
      _ = 4 * (Data.Gaussian.Norm.Basic.normSq previous * Data.Gaussian.Norm.Basic.normSq
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum left - Data.Gaussian.Norm.Sum.Basic.gaussianSum right)) := by
        ring1
      _ ≤ 4 * ((2 + 8 * basis.coefficient) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients *
          ((parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 *
            PreparedComparison.uniformSourceTotalError
            allowance * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by
            decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4)
      _ = _ := by ring1
  have identity : Path.IncrementArea.traceArea previous left - Path.IncrementArea.traceArea previous right =
      (Path.IncrementArea.pathArea left - Path.IncrementArea.pathArea right) + Path.BoundaryRibbon.area previous
        (Data.Gaussian.Norm.Sum.Basic.gaussianSum left - Data.Gaussian.Norm.Sum.Basic.gaussianSum right) := by
    rw [Path.IncrementArea.traceArea_eq, Path.IncrementArea.traceArea_eq]
    apply Gaussian.Basic.ext <;> simp only [-eq_self, -iff_self, Path.BoundaryRibbon.area, Data.Gaussian.Basic.conj,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re,
      Gaussian.Basic.mul_im] <;> ring1
  change Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.traceArea previous left - Path.IncrementArea.traceArea
    previous right) ≤ _
  rw [identity]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct area
      ribbon) (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq
      (by
        unfold Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace.Samples.SourceRestoration.traceScale
        ring1))

end SourceRestoration
end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRestorationTrace
