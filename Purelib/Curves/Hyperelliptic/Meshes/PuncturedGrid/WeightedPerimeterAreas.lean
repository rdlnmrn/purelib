module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
public import Purelib.Riemann.Integration.RectangularPerimeterLengths
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Integration.Path

open Purelib.Riemann.Integration

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Riemann.Integration.RectangularPerimeterLengths

@[expose] public section

/-! Full area estimates on the actual normalized perimeter bank. Exact
length caches eliminate caller-supplied geometric weights; every owner
junction remains in the trace and receives its allocated error tolerance. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering (CenteredPerimeters)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (faceValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideCenteredRemainder (sideCenteredArea)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {target : Rational} {i j : Fin genus} {stage : Nat} {cache :
    Numerics domains stage}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed target}

open Purelib.Integration.Path.NoisyPathArea (LengthErrorBudget)

namespace CenteredPerimeters

/-- Geometric lengths for the same retained traces and both sheet occurrences. -/
def Lengths (samples : RequestedHoleCentering.CenteredPerimeters request cache i j) :=
  Data.Vector.DependentVector (fun position : Fin base.faces.regulars.length =>
    Data.Vector.DependentVector (fun sheet : Fin 2 =>
      RectangularPerimeterLengths.Lengths ((samples.traces.get position).get sheet)))

namespace Lengths

/-- Cache the exact geometric trace lengths for every original face and sheet. -/
def build (samples : RequestedHoleCentering.CenteredPerimeters request cache i j) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples :=
  DependentVector.ofFn fun position => DependentVector.ofFn fun sheet =>
    RectangularPerimeterLengths.Lengths.build ((samples.traces.get position).get sheet)

end Lengths

/-- The actual bottom centered perimeter area satisfies the geometric weighted bound on its retained trace.

The estimate consumes the exact cached lengths, supplied pointwise magnitude and increment-density bounds, and the
length-error budget for every original owner junction. -/
theorem bottom_weighted_area_bound (samples : RequestedHoleCentering.CenteredPerimeters request cache i j)
    (lengths : Lengths samples)
      (position : Fin base.faces.regulars.length) (sheet : Fin 2)
    {allowance magnitude density : Fraction.Rational}
    (budget : NoisyPathArea.LengthErrorBudget (((samples.traces.get position).get sheet).bottom.vertices.rest.length)
      allowance)
    (magnitudeNonnegative : 0 ≤ magnitude) (densityNonnegative : 0 ≤ density)
    (bounded : ∀ vertex, PrimitivePoint.Bounded (((samples.samples.get position).get sheet).bottom.centered vertex)
      magnitude)
    (increments : ∀ edge : Fin (((samples.traces.get position).get sheet).bottom.vertices.rest.length),
      PrimitivePoint.Bounded ((((samples.traces.get position).get sheet).bottom.leftValue (FacePerimeters.faceValues
        cache.normalize i j position sheet)
          (((samples.traces.get position).get sheet).bottom.vertices.indexed edge.succ)).sub
        (((samples.traces.get position).get sheet).bottom.leftValue (FacePerimeters.faceValues cache.normalize i j
          position sheet)
          (((samples.traces.get position).get sheet).bottom.vertices.indexed edge.castSucc)))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (((samples.traces.get position).get sheet).bottom.point (((samples.traces.get position).get
            sheet).bottom.vertices.indexed edge.succ) -
            ((samples.traces.get position).get sheet).bottom.point (((samples.traces.get position).get
              sheet).bottom.vertices.indexed edge.castSucc)))) :
    Data.Gaussian.Norm.Basic.normSq (SideCenteredRemainder.sideCenteredArea ((samples.samples.get position).get
      sheet) .bottom) ≤
      4 * magnitude * (4 * density + 3) *
        ((base.faces.regulars[position.val]'position.isLt).cell.box.xUpper -
          (base.faces.regulars[position.val]'position.isLt).cell.box.xLower + allowance)^2 :=
  Centered.bottom_geometric_area_bound ((samples.samples.get position).get sheet)
    ((lengths.get position).get sheet) budget magnitudeNonnegative densityNonnegative bounded increments

/-- The actual top centered perimeter area satisfies the geometric weighted bound on its retained trace.

The estimate consumes the exact cached lengths, supplied pointwise magnitude and increment-density bounds, and the
length-error budget for every original owner junction. -/
theorem top_weighted_area_bound (samples : RequestedHoleCentering.CenteredPerimeters request cache i j)
    (lengths : Lengths samples)
      (position : Fin base.faces.regulars.length) (sheet : Fin 2)
    {allowance magnitude density : Fraction.Rational}
    (budget : NoisyPathArea.LengthErrorBudget (((samples.traces.get position).get sheet).top.vertices.rest.length)
      allowance)
    (magnitudeNonnegative : 0 ≤ magnitude) (densityNonnegative : 0 ≤ density)
    (bounded : ∀ vertex, PrimitivePoint.Bounded (((samples.samples.get position).get sheet).top.centered vertex)
      magnitude)
    (increments : ∀ edge : Fin (((samples.traces.get position).get sheet).top.vertices.rest.length),
      PrimitivePoint.Bounded ((((samples.traces.get position).get sheet).top.leftValue (FacePerimeters.faceValues
        cache.normalize i j position sheet)
          (((samples.traces.get position).get sheet).top.vertices.indexed edge.succ)).sub
        (((samples.traces.get position).get sheet).top.leftValue (FacePerimeters.faceValues cache.normalize i j position
          sheet)
          (((samples.traces.get position).get sheet).top.vertices.indexed edge.castSucc)))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (((samples.traces.get position).get sheet).top.point (((samples.traces.get position).get
            sheet).top.vertices.indexed edge.succ) -
            ((samples.traces.get position).get sheet).top.point (((samples.traces.get position).get
              sheet).top.vertices.indexed edge.castSucc)))) :
    Data.Gaussian.Norm.Basic.normSq (SideCenteredRemainder.sideCenteredArea ((samples.samples.get position).get
      sheet) .top) ≤
      4 * magnitude * (4 * density + 3) *
        ((base.faces.regulars[position.val]'position.isLt).cell.box.xUpper -
          (base.faces.regulars[position.val]'position.isLt).cell.box.xLower + allowance)^2 :=
  Centered.top_geometric_area_bound ((samples.samples.get position).get sheet)
    ((lengths.get position).get sheet) budget magnitudeNonnegative densityNonnegative bounded increments

/-- The actual left centered perimeter area satisfies the geometric weighted bound on its retained trace.

The estimate consumes the exact cached lengths, supplied pointwise magnitude and increment-density bounds, and the
length-error budget for every original owner junction. -/
theorem left_weighted_area_bound (samples : RequestedHoleCentering.CenteredPerimeters request cache i j)
    (lengths : Lengths samples)
      (position : Fin base.faces.regulars.length) (sheet : Fin 2)
    {allowance magnitude density : Fraction.Rational}
    (budget : NoisyPathArea.LengthErrorBudget (((samples.traces.get position).get sheet).left.vertices.rest.length)
      allowance)
    (magnitudeNonnegative : 0 ≤ magnitude) (densityNonnegative : 0 ≤ density)
    (bounded : ∀ vertex, PrimitivePoint.Bounded (((samples.samples.get position).get sheet).left.centered vertex)
      magnitude)
    (increments : ∀ edge : Fin (((samples.traces.get position).get sheet).left.vertices.rest.length),
      PrimitivePoint.Bounded ((((samples.traces.get position).get sheet).left.leftValue (FacePerimeters.faceValues
        cache.normalize i j position sheet)
          (((samples.traces.get position).get sheet).left.vertices.indexed edge.succ)).sub
        (((samples.traces.get position).get sheet).left.leftValue (FacePerimeters.faceValues cache.normalize i j
          position sheet)
          (((samples.traces.get position).get sheet).left.vertices.indexed edge.castSucc)))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (((samples.traces.get position).get sheet).left.point (((samples.traces.get position).get
            sheet).left.vertices.indexed edge.succ) -
            ((samples.traces.get position).get sheet).left.point (((samples.traces.get position).get
              sheet).left.vertices.indexed edge.castSucc)))) :
    Data.Gaussian.Norm.Basic.normSq (SideCenteredRemainder.sideCenteredArea ((samples.samples.get position).get
      sheet) .left) ≤
      4 * magnitude * (4 * density + 3) *
        ((base.faces.regulars[position.val]'position.isLt).cell.box.yUpper -
          (base.faces.regulars[position.val]'position.isLt).cell.box.yLower + allowance)^2 :=
  Centered.left_geometric_area_bound ((samples.samples.get position).get sheet)
    ((lengths.get position).get sheet) budget magnitudeNonnegative densityNonnegative bounded increments

/-- The actual right centered perimeter area satisfies the geometric weighted bound on its retained trace.

The estimate consumes the exact cached lengths, supplied pointwise magnitude and increment-density bounds, and the
length-error budget for every original owner junction. -/
theorem right_weighted_area_bound (samples : RequestedHoleCentering.CenteredPerimeters request cache i j)
    (lengths : Lengths samples)
      (position : Fin base.faces.regulars.length) (sheet : Fin 2)
    {allowance magnitude density : Fraction.Rational}
    (budget : NoisyPathArea.LengthErrorBudget (((samples.traces.get position).get sheet).right.vertices.rest.length)
      allowance)
    (magnitudeNonnegative : 0 ≤ magnitude) (densityNonnegative : 0 ≤ density)
    (bounded : ∀ vertex, PrimitivePoint.Bounded (((samples.samples.get position).get sheet).right.centered vertex)
      magnitude)
    (increments : ∀ edge : Fin (((samples.traces.get position).get sheet).right.vertices.rest.length),
      PrimitivePoint.Bounded ((((samples.traces.get position).get sheet).right.leftValue (FacePerimeters.faceValues
        cache.normalize i j position sheet)
          (((samples.traces.get position).get sheet).right.vertices.indexed edge.succ)).sub
        (((samples.traces.get position).get sheet).right.leftValue (FacePerimeters.faceValues cache.normalize i j
          position sheet)
          (((samples.traces.get position).get sheet).right.vertices.indexed edge.castSucc)))
        (3 * budget.tolerance + 4 * density * Data.Gaussian.Norm.Basic.normSq
          (((samples.traces.get position).get sheet).right.point (((samples.traces.get position).get
            sheet).right.vertices.indexed edge.succ) -
            ((samples.traces.get position).get sheet).right.point (((samples.traces.get position).get
              sheet).right.vertices.indexed edge.castSucc)))) :
    Data.Gaussian.Norm.Basic.normSq (SideCenteredRemainder.sideCenteredArea ((samples.samples.get position).get
      sheet) .right) ≤
      4 * magnitude * (4 * density + 3) *
        ((base.faces.regulars[position.val]'position.isLt).cell.box.yUpper -
          (base.faces.regulars[position.val]'position.isLt).cell.box.yLower + allowance)^2 :=
  Centered.right_geometric_area_bound ((samples.samples.get position).get sheet)
    ((lengths.get position).get sheet) budget magnitudeNonnegative densityNonnegative bounded increments

end CenteredPerimeters
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas
