module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedPairedRadialRibbon
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

public section

/-! Paid paired radial cancellation on every internal common-cover junction. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
open Purelib.Riemann.Normalization
open Purelib.Riemann.RootContinuation.RootRadialGeometry
open Purelib.Topology.Polygon
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank (ChartRequest junctionLeft junctionRight)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections (junction_le_readingFloor)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus count otherCount depth floor index : Nat} {curve : HyperellipticCurve
  genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent}
  {otherPatch : PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Data patch count} {otherData :
    Data otherPatch otherCount}
  {cover : Cover data} {otherCover :
    Cover otherData}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    CommonCover cover otherCover}
  {target : Coordinate} {request :
    ChartRequest regular common depth target floor}
  (evaluated : Evaluation request
    index)

/-- Evaluate both original retained cap primitive polynomials at the supplied common root coordinate. -/
@[expose] def radialValues (point : InverseRootPolynomial.Gaussian) : PrimitivePoint :=
  ⟨evaluated.samples.firstCap.primitive.value.eval point, evaluated.samples.otherCap.primitive.value.eval point⟩

/-- Read the paired radial area at the actual retained interval vertex and supplied radial depth. -/
@[expose] def radialPotential (radialDepth : Nat) (i : Fin common.intervals.length)
    (vertex : Fin ((request.plans.get i).geometry.tail.length + 1)) : Gaussian :=
  Bilinear.radialArea (radialValues evaluated)
    radialDepth (Evaluation.chartCoordinate evaluated i vertex)

/-- The actual adjacent radial-potential difference with its original paired endpoint wedge subtracted. -/
@[expose] def junctionRadialError (radialDepth : Nat) (i : Fin (common.intervals.length - 1)) : Gaussian :=
  radialPotential evaluated radialDepth
    (CommonChartBank.junctionRight common i) 0 -
    radialPotential evaluated radialDepth
      (CommonChartBank.junctionLeft common i)
      (Fin.last (request.plans.get (CommonChartBank.junctionLeft common i)).geometry.tail.length) -
    Stokes.edgeArea (Evaluation.lastChartPoint evaluated (CommonChartBank.junctionLeft common i))
      (Evaluation.firstChartPoint evaluated (CommonChartBank.junctionRight common i))

/-- Every actual internal common-cover radial junction satisfies its original paid allowance in the branch chart. -/
theorem junction_radial_accurate (branch : HyperellipticReciprocal.originOrder curve = 1)
    (radialDepth : Nat) (i : Fin (common.intervals.length - 1)) :
    Data.Gaussian.Norm.Basic.normSq
      (junctionRadialError evaluated
      radialDepth i) < request.allowance / 16 := by
  let left := evaluated.entries.get (CommonChartBank.junctionLeft common i)
  let right := evaluated.entries.get (CommonChartBank.junctionRight common i)
  let lastVertex := Fin.last (request.plans.get (CommonChartBank.junctionLeft common i)).geometry.tail.length
  have bound := (request.junctions.get i).radial_accurate
    (left.evaluated.chart.retained.area.evaluated.readings.get lastVertex)
    (right.evaluated.chart.retained.area.evaluated.readings.get 0) branch
    (Evaluation.chart_square_inside evaluated branch (CommonChartBank.junctionLeft common i) lastVertex)
    (Evaluation.chart_square_inside evaluated branch (CommonChartBank.junctionRight common i) 0)
    ((CommonChartConnections.junction_le_readingFloor i).trans left.readingLater)
    ((CommonChartConnections.junction_le_readingFloor i).trans right.readingLater) radialDepth
  unfold CommonChartRadialJunctions.junctionRadialError
  rw [show Evaluation.lastChartPoint evaluated (CommonChartBank.junctionLeft common i) =
      (radialValues evaluated)
        (Evaluation.chartCoordinate evaluated (CommonChartBank.junctionLeft common i) lastVertex) from
        Evaluation.chartPoint_readback evaluated branch (CommonChartBank.junctionLeft common i) lastVertex,
    show Evaluation.firstChartPoint evaluated (CommonChartBank.junctionRight common i) =
      (radialValues evaluated)
        (Evaluation.chartCoordinate evaluated (CommonChartBank.junctionRight common i) 0) from
        Evaluation.chartPoint_readback evaluated branch (CommonChartBank.junctionRight common i) 0]
  exact bound

set_option genInjectivity false in
/-- Numerical radial values and the actual endpoint wedge are computed once; their readbacks tie this certificate to the
original bank's chart paths. -/
structure RadialJunction (radialDepth : Nat) (i : Fin (common.intervals.length - 1)) where
  /-- The cached radial potential at the original left interval's terminal chart coordinate. -/ firstPotential :
    InverseRootPolynomial.Gaussian
  /-- The first potential cache is exactly the retained terminal radial reading. -/ first_eq : firstPotential =
    radialPotential evaluated radialDepth
    (CommonChartBank.junctionLeft common i)
    (Fin.last (request.plans.get (CommonChartBank.junctionLeft common i)).geometry.tail.length)
  /-- The cached radial potential at the original right interval's initial chart coordinate. -/ lastPotential :
    InverseRootPolynomial.Gaussian
  /-- The last potential cache is exactly the retained initial radial reading. -/ last_eq : lastPotential =
    radialPotential evaluated radialDepth
    (CommonChartBank.junctionRight common i) 0
  /-- The cached actual paired wedge between the original adjacent chart endpoints. -/ connector :
    InverseRootPolynomial.Gaussian
  /-- The connector cache equals the wedge of those exact retained paired chart points. -/ connector_eq : connector =
    Stokes.edgeArea (Evaluation.lastChartPoint evaluated (CommonChartBank.junctionLeft common i))
    (Evaluation.firstChartPoint evaluated (CommonChartBank.junctionRight common i))
  /-- The cached radial-potential discrepancy after subtracting the actual endpoint wedge. -/ difference :
    InverseRootPolynomial.Gaussian
  /-- The discrepancy cache is exactly the retained last-minus-first potential minus connector. -/ difference_eq :
    difference = lastPotential - firstPotential - connector
  /-- The actual cached radial discrepancy is below one sixteenth of the original bank allowance. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq difference < request.allowance / 16

constructive_injectivity RadialJunction

/-- Cache both actual radial endpoint potentials and their original paired wedge once, retaining the paid junction
certificate. -/
@[expose] def radialJunction (branch : HyperellipticReciprocal.originOrder curve = 1)
    (radialDepth : Nat) (i : Fin (common.intervals.length - 1)) :
      RadialJunction evaluated radialDepth i :=
  let first := radialPotential evaluated
    radialDepth (CommonChartBank.junctionLeft common i)
    (Fin.last (request.plans.get (CommonChartBank.junctionLeft common i)).geometry.tail.length)
  let last := radialPotential evaluated
    radialDepth (CommonChartBank.junctionRight common i) 0
  let connector := Stokes.edgeArea (Evaluation.lastChartPoint evaluated (CommonChartBank.junctionLeft common i))
    (Evaluation.firstChartPoint evaluated (CommonChartBank.junctionRight common i))
  ⟨first, rfl, last, rfl, connector, rfl, last - first - connector, rfl,
    junction_radial_accurate evaluated branch
      radialDepth i⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions
