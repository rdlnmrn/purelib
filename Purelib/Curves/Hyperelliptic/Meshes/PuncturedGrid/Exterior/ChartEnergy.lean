module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ParentOrientation
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-!
# Complete odd energy for the actual closed exterior program

The program supplies every parent's orientation. Energy consumes the same
acquired chart path and source comparison, including the second lap. The
endpoint correction to the closed polygon remains explicit for sewing.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartEnergy

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {totalTarget areaTarget target :
    Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}
  {entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapComparison.Entry regular lifted differential totalTarget
    areaTarget minimum}
  {charts : Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts.ChartRequest entry.request target}
  {index : Nat} {box : Rational.Box} {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartPlan entry charts sample} {depth readingIndex :
    Nat}

/-- Prepare energy on the actual acquired chart using the original exterior program's parent orientations and positive
energy target. -/
def energy (evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartPlan.Evaluation plan depth
  readingIndex)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (energyTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < energyTarget) (energyFloor : Nat) :
    Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.RequestedEnergy evaluated.chart energyTarget energyFloor :=
  Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.Evaluation.energy evaluated.chart
    branch entry.prepared.program.parents_oriented energyTarget positive energyFloor

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartEnergy in
/-- This is the actual closed polygon's area. The area of its closing
increment vanishes; the trace-origin term still belongs to the open path
and is retained along with the explicit parent boundary potentials. -/
theorem energy_polygon_close (evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartClosure.ChartPlan.Evaluation
  plan depth readingIndex)
    {energyTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor : Nat}
    (energy : Hyperelliptic.Charts.Reciprocal.Disk.ConnectedEnergy.RequestedEnergy evaluated.chart energyTarget
      energyFloor) :
    Data.Gaussian.Norm.Basic.normSq (energy.connected.energy - (-evaluated.polygon.area -
      Path.BoundaryRibbon.area evaluated.chart.original.firstValue evaluated.chart.connected.summary.total +
        energy.connected.boundary)) <
        256 * (4 * target + ((((totalTarget / 4) / 4) / 4) / 4) / 4) := by
  rw [evaluated.area_eq]
  exact energy.boundary_close

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartEnergy
