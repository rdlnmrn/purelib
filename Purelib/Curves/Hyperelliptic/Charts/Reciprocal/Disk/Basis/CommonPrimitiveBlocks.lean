module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveArea
public import Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples
import Init.Prelude
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
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveArea.BasisCommonInterval

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisCommonInterval

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Integration.Path.Dyadic

open Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! Literal sampled blocks carry the original/pullback area and total bounds
needed for the complete parent polygon comparison. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks

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

open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements_sub_constant pathArea_dyadicIncrements)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)

namespace BasisCommonInterval.PrimitiveSample

variable {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {interval :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonInterval cover covers}
  {polynomials : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap
    index box}

set_option genInjectivity false in
/-- The actual dyadic source and pullback sample blocks on one retained common interval.

Both complete increment paths and executable summaries remain cached with their full area difference. -/
structure Block (sample : BasisCommonInterval.PrimitiveSample interval regular polynomials) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (depth : Nat) where
  /-- The actual original source sample at every retained dyadic vertex. -/ source :
    DyadicPrimitivePathSamples.DyadicSample (sample.sourceValue coefficients) depth interval.edge.left.parameter
    interval.edge.right.parameter
  /-- The actual original pullback sample at those same dyadic vertices. -/ pullback :
    DyadicPrimitivePathSamples.DyadicSample (sample.pullbackValue coefficients) depth interval.edge.left.parameter
    interval.edge.right.parameter
  /-- The cached difference of the two complete original sample areas. -/ difference : InverseRootPolynomial.Gaussian
  /-- The area difference cache equals the source summary area minus the pullback summary area. -/ difference_eq :
    difference = source.summary.area - pullback.summary.area

constructive_injectivity Block

/-- Sample the actual functions once per dyadic vertex and retain their full increment paths, totals and areas. No
endpoint closure is assumed. -/
@[expose] def block (sample : BasisCommonInterval.PrimitiveSample interval regular polynomials) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (depth : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval.PrimitiveSample.Block
      sample coefficients depth :=
  let source := DyadicSample.build (sample.sourceValue coefficients) depth interval.edge.left.parameter
    interval.edge.right.parameter
  let pullback := DyadicSample.build (sample.pullbackValue coefficients) depth interval.edge.left.parameter
    interval.edge.right.parameter
  ⟨source, pullback, source.summary.area - pullback.summary.area, rfl⟩

namespace Block

variable {sample :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisCommonInterval.PrimitiveSample
  interval regular polynomials} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {depth : Nat} {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval.PrimitiveSample
  in
/-- The cached source block area equals its original anchored dyadic path area. -/
theorem source_area (block :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval.PrimitiveSample.Block
  sample coefficients depth) :
    block.source.summary.area = DyadicBoundaryRibbon.dyadicArea (PrimitiveSample.sourcePath sample coefficients) depth
      interval.edge.left.parameter interval.edge.right.parameter := by
  rw [block.source.summary.area_eq, block.source.increments_eq,
    ← DyadicPrimitivePaths.dyadicIncrements_sub_constant (sample.sourceValue coefficients) (sample.sourceValue
      coefficients interval.edge.left.parameter)]
  exact DyadicPrimitivePaths.pathArea_dyadicIncrements (PrimitiveSample.sourcePath sample coefficients) depth _ _
    (PrimitiveSample.sourcePath_left sample coefficients)

/-- The cached pullback block area equals its original anchored dyadic path area. -/
theorem pullback_area (block :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval.PrimitiveSample.Block
  sample coefficients depth) :
    block.pullback.summary.area = DyadicBoundaryRibbon.dyadicArea (PrimitiveSample.pullbackPath sample coefficients)
      depth interval.edge.left.parameter interval.edge.right.parameter := by
  rw [block.pullback.summary.area_eq, block.pullback.increments_eq,
    ← DyadicPrimitivePaths.dyadicIncrements_sub_constant (sample.pullbackValue coefficients) (sample.pullbackValue
      coefficients interval.edge.left.parameter)]
  exact DyadicPrimitivePaths.pathArea_dyadicIncrements (PrimitiveSample.pullbackPath sample coefficients) depth _ _
    (PrimitiveSample.pullbackPath_left sample coefficients)

/-- The actual cached block area difference satisfies the homogeneous original tolerance and fourth-power interval-width
bound. -/
theorem area_error (block :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval.PrimitiveSample.Block
  sample coefficients depth)
    (request : BasisCommonInterval.PrimitiveRequest interval regular target floor) (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq block.difference ≤ target * (144 * BasisSourceCovers.primitiveSlope covers
      + 160 * target) *
      (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 * (interval.edge.right.parameter -
        interval.edge.left.parameter)^4 := by
  rw [block.difference_eq, block.source_area, block.pullback_area]
  exact PrimitiveSample.area_error sample request later coefficients depth

/-- The difference of the two original cached block totals satisfies the retained homogeneous increment bound. -/
theorem total_error (block :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval.PrimitiveSample.Block
  sample coefficients depth)
    (request : BasisCommonInterval.PrimitiveRequest interval regular target floor) (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (block.source.summary.total - block.pullback.summary.total) ≤
      target * (interval.edge.right.parameter - interval.edge.left.parameter)^2 *
        PreparedObservationCoercivity.coefficientNormSq coefficients := by
  rw [block.source.total, block.pullback.total]
  exact sample.accurate request later coefficients ⟨le_rfl, interval.ordered⟩ ⟨interval.ordered, le_rfl⟩

/-- The actual cached source block total has the original cover-slope bound. -/
theorem source_total_bound (block :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval.PrimitiveSample.Block
  sample coefficients depth) :
    Data.Gaussian.Norm.Basic.normSq block.source.summary.total ≤ BasisSourceCovers.primitiveSlope covers *
      (interval.edge.right.parameter - interval.edge.left.parameter)^2 * PreparedObservationCoercivity.coefficientNormSq
        coefficients := by
  rw [block.source.total]
  exact PrimitiveSample.source_increment_bound sample coefficients interval.edge.left.inside interval.edge.right.inside

/-- The actual cached pullback block total has the retained enlarged cover-slope bound. -/
theorem pullback_total_bound (block :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks.BasisCommonInterval.PrimitiveSample.Block
  sample coefficients depth)
    (request : BasisCommonInterval.PrimitiveRequest interval regular target floor) (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq block.pullback.summary.total ≤ 2 * (BasisSourceCovers.primitiveSlope covers
      + target) *
      (interval.edge.right.parameter - interval.edge.left.parameter)^2 * PreparedObservationCoercivity.coefficientNormSq
        coefficients := by
  rw [block.pullback.total]
  exact PrimitiveSample.pullback_increment_bound sample request later coefficients ⟨le_rfl, interval.ordered⟩
    ⟨interval.ordered, le_rfl⟩

end Block
end BasisCommonInterval.PrimitiveSample
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBlocks
