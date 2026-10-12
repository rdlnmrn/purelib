module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
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
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.FiniteSum.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisCommonInterval

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.Integration.Path.Dyadic

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Complete homogeneous area comparison on each retained common interval.
Every dyadic depth is covered, with the open endpoint correction paid. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveArea

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
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval
  (PrimitiveSample PrimitiveRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers (primitiveSlope
  primitiveSlope_nonnegative)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {covers :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {index : Nat} {box : Purelib.Geometry.Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin_zero sumFin_mul_right)

open Purelib.Integration.Path.BoundaryRibbon (area area_bound)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea dyadicDifference)

namespace BasisCommonInterval.PrimitiveSample

variable {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {interval :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The original coefficient-weighted source primitive anchored at the retained common interval's left endpoint. -/
@[expose] def sourcePath (sample : BasisCommonInterval.PrimitiveSample interval regular polynomials) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (parameter : InverseRootPolynomial.Coordinate) : Gaussian :=
  sample.sourceValue coefficients parameter - sample.sourceValue coefficients interval.edge.left.parameter

/-- The original coefficient-weighted pullback primitive anchored at that same retained left endpoint. -/
@[expose] def pullbackPath (sample : BasisCommonInterval.PrimitiveSample interval regular polynomials) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (parameter : InverseRootPolynomial.Coordinate) : Gaussian :=
  sample.pullbackValue coefficients parameter - sample.pullbackValue coefficients interval.edge.left.parameter

/-- The anchored original source path vanishes at the retained left endpoint. -/
theorem sourcePath_left (sample : BasisCommonInterval.PrimitiveSample interval regular polynomials) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveArea.BasisCommonInterval.PrimitiveSample.sourcePath
      sample coefficients interval.edge.left.parameter = 0 := Data.Gaussian.Basic.sub_self _

/-- The anchored original pullback path vanishes at the retained left endpoint. -/
theorem pullbackPath_left (sample : BasisCommonInterval.PrimitiveSample interval regular polynomials) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus) :

      pullbackPath
      sample coefficients interval.edge.left.parameter = 0 := Data.Gaussian.Basic.sub_self _

/-- The squared norm sum of the actual finite coefficient vector is nonnegative. -/
private theorem coefficient_nonnegative (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) : 0 ≤
  PreparedObservationCoercivity.coefficientNormSq coefficients :=
  FiniteSum.Fin.sumFin_zero.symm.trans_le (Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
    InverseRootPolynomial.Coordinate)) _
    (fun row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))

/-- The original source-minus-pullback path drift satisfies the homogeneous retained tolerance bound between any two
interval points. -/
theorem path_drift (sample : BasisCommonInterval.PrimitiveSample interval regular polynomials)
    (request : BasisCommonInterval.PrimitiveRequest interval regular target floor) (later : request.index ≤ index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) {first last : InverseRootPolynomial.Coordinate}
    (firstInside : interval.edge.left.parameter ≤ first ∧ first ≤ interval.edge.right.parameter)
    (lastInside : interval.edge.left.parameter ≤ last ∧ last ≤ interval.edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq
      ((sourcePath
      sample coefficients last -
      pullbackPath
      sample coefficients last) -

        (sourcePath
        sample coefficients first -
        pullbackPath
        sample coefficients first)) ≤
      (target * PreparedObservationCoercivity.coefficientNormSq coefficients) * (last - first)^2 := by
  have equal :
    (sourcePath
    sample coefficients last -
    pullbackPath
    sample coefficients last) -

        (sourcePath
        sample coefficients first -
        pullbackPath
        sample coefficients first) =
      (sample.sourceValue coefficients last - sample.sourceValue coefficients first) -
      (sample.pullbackValue coefficients last - sample.pullbackValue coefficients first) := by
    dsimp only
      [sourcePath,
      pullbackPath]
    ring1
  rw [equal]
  exact (sample.accurate request later coefficients firstInside lastInside).trans_eq (by ring1)

/-- Every actual pullback path increment has the homogeneous retained cover-slope bound. -/
theorem path_increment (sample : BasisCommonInterval.PrimitiveSample interval regular polynomials)
    (request : BasisCommonInterval.PrimitiveRequest interval regular target floor) (later : request.index ≤ index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) {first last : InverseRootPolynomial.Coordinate}
    (firstInside : interval.edge.left.parameter ≤ first ∧ first ≤ interval.edge.right.parameter)
    (lastInside : interval.edge.left.parameter ≤ last ∧ last ≤ interval.edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq
      (pullbackPath
      sample coefficients last -
      pullbackPath
      sample coefficients first) ≤
      (2 * (BasisSourceCovers.primitiveSlope covers + target) * PreparedObservationCoercivity.coefficientNormSq
        coefficients) * (last - first)^2 := by
  have equal :
    pullbackPath
    sample coefficients last -
    pullbackPath
    sample coefficients first =
      sample.pullbackValue coefficients last - sample.pullbackValue coefficients first := by
    dsimp only
      [pullbackPath]
    ring1
  rw [equal]
  exact (PrimitiveSample.pullback_increment_bound sample request later coefficients firstInside lastInside).trans_eq (by
    ring1)

/-- The anchored source and pullback values have the original homogeneous tolerance bound throughout the retained
interval. -/
theorem path_point_error (sample : BasisCommonInterval.PrimitiveSample interval regular polynomials)
    (request : BasisCommonInterval.PrimitiveRequest interval regular target floor) (later : request.index ≤ index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) {parameter : InverseRootPolynomial.Coordinate}
    (inside : interval.edge.left.parameter ≤ parameter ∧ parameter ≤ interval.edge.right.parameter) :
    Data.Gaussian.Norm.Basic.normSq
      (sourcePath
      sample coefficients parameter -
      pullbackPath
      sample coefficients parameter) ≤
      target * PreparedObservationCoercivity.coefficientNormSq coefficients * (interval.edge.right.parameter -
        interval.edge.left.parameter)^2 := by
  have bound :=
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveArea.BasisCommonInterval.PrimitiveSample.path_drift
    sample request later coefficients ⟨le_rfl, interval.ordered⟩ inside
  rw
    [sourcePath_left
    sample,
    pullbackPath_left
    sample, Data.Gaussian.Basic.sub_self, Data.Gaussian.Basic.sub_zero] at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct (Purelib.Data.Rat.Fraction.Order.Arithmetic.sub_nonneg_direct inside.1)
      (Fraction.Order.Arithmetic.sub_le_sub_right_direct inside.2 _) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct request.positive.le
      (coefficient_nonnegative
      coefficients)))

/-- Every dyadic ribbon on the original common interval satisfies the retained homogeneous fourth-power width bound. -/
theorem ribbon_bound (sample : BasisCommonInterval.PrimitiveSample interval regular polynomials)
    (request : BasisCommonInterval.PrimitiveRequest interval regular target floor) (later : request.index ≤ index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBoundaryRibbon.dyadicDifference
      (sourcePath
      sample coefficients)
      (pullbackPath
      sample coefficients) depth
      interval.edge.left.parameter interval.edge.right.parameter) ≤
      8 * target * (8 * BasisSourceCovers.primitiveSlope covers + 9 * target) *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 * (interval.edge.right.parameter -
          interval.edge.left.parameter)^4 := by
  have bound := DyadicBoundaryRibbon.dyadicDifference_bound
    (sourcePath
    sample coefficients)
    (pullbackPath
    sample coefficients)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct request.positive.le
      (coefficient_nonnegative
      coefficients)) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    (fun _ inside =>
      path_point_error
      sample request later coefficients inside)
    (fun _ _ firstInside lastInside =>
      path_increment
      sample request later coefficients firstInside lastInside)
    (fun _ _ firstInside lastInside =>
      path_drift
      sample request later coefficients firstInside lastInside)
    depth ⟨le_rfl, interval.ordered⟩ ⟨interval.ordered, le_rfl⟩ interval.ordered
  exact bound.trans_eq (by ring1)

/-- The full anchored area error, including its endpoint term, is uniform in spatial depth and homogeneous for arbitrary
Gaussian coefficients. -/
theorem area_error (sample : BasisCommonInterval.PrimitiveSample interval regular polynomials)
    (request : BasisCommonInterval.PrimitiveRequest interval regular target floor) (later : request.index ≤ index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (depth : Nat) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBoundaryRibbon.dyadicArea
      (sourcePath
      sample coefficients) depth interval.edge.left.parameter interval.edge.right.parameter -
      DyadicBoundaryRibbon.dyadicArea
        (pullbackPath
        sample coefficients) depth interval.edge.left.parameter interval.edge.right.parameter) ≤
      target * (144 * BasisSourceCovers.primitiveSlope covers + 160 * target) *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 * (interval.edge.right.parameter -
          interval.edge.left.parameter)^4 := by
  let endpoint := BoundaryRibbon.area
    (pullbackPath
    sample coefficients interval.edge.right.parameter)

      (sourcePath
      sample coefficients interval.edge.right.parameter -
      pullbackPath
      sample coefficients interval.edge.right.parameter)
  have rightBound :=
    path_increment
    sample request later coefficients ⟨le_rfl, interval.ordered⟩ ⟨interval.ordered, le_rfl⟩
  rw
    [pullbackPath_left
    sample, Data.Gaussian.Basic.sub_zero] at rightBound
  have endpointBound : Data.Gaussian.Norm.Basic.normSq endpoint ≤
      8 * (BasisSourceCovers.primitiveSlope covers + target) * target * (PreparedObservationCoercivity.coefficientNormSq
        coefficients)^2 *
        (interval.edge.right.parameter - interval.edge.left.parameter)^4 := by
    have product := Fraction.Order.Arithmetic.mul_le_mul_direct rightBound

        (path_point_error
        sample request later coefficients ⟨interval.ordered, le_rfl⟩) (Data.Gaussian.Norm.Basic.normSq_nonneg _)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
          (BasisSourceCovers.primitiveSlope_nonnegative covers) request.positive.le))

          (coefficient_nonnegative
          coefficients)) (Fraction.Order.Arithmetic.sq_nonneg_direct _))
    have bound := (BoundaryRibbon.area_bound
      (pullbackPath
      sample coefficients interval.edge.right.parameter)

        (sourcePath
        sample coefficients interval.edge.right.parameter -
        pullbackPath
        sample coefficients interval.edge.right.parameter)).trans
      ((show 4 * Data.Gaussian.Norm.Basic.normSq
        (pullbackPath
        sample coefficients interval.edge.right.parameter) *
        Data.Gaussian.Norm.Basic.normSq
          (sourcePath
          sample coefficients interval.edge.right.parameter -
          pullbackPath
          sample coefficients interval.edge.right.parameter) =
        4 * (Data.Gaussian.Norm.Basic.normSq
          (pullbackPath
          sample coefficients interval.edge.right.parameter) *
          Data.Gaussian.Norm.Basic.normSq
            (sourcePath
            sample coefficients interval.edge.right.parameter -
            pullbackPath
            sample coefficients interval.edge.right.parameter)) by ring1).trans_le
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide)))
    exact bound.trans_eq (by ring1)
  have identity : DyadicBoundaryRibbon.dyadicArea
    (sourcePath
    sample coefficients) depth interval.edge.left.parameter interval.edge.right.parameter -
      DyadicBoundaryRibbon.dyadicArea
        (pullbackPath
        sample coefficients) depth interval.edge.left.parameter interval.edge.right.parameter =
      DyadicBoundaryRibbon.dyadicDifference
        (sourcePath
        sample coefficients)
        (pullbackPath
        sample coefficients) depth
        interval.edge.left.parameter interval.edge.right.parameter + endpoint := by
    rw [DyadicBoundaryRibbon.dyadicDifference,
      sourcePath_left
      sample,
      pullbackPath_left
      sample]
    dsimp only [endpoint, BoundaryRibbon.area]
    ring1
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      (ribbon_bound
      sample request later coefficients depth) endpointBound)
      (by decide)).trans_eq (by ring1))

end BasisCommonInterval.PrimitiveSample
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveArea
