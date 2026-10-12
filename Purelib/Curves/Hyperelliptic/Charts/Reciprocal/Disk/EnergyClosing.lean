module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyBoundaryJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

@[expose] public section

/-!
# The retained root-return request controls the closing energy potential

The last endpoint is selected from the same cached parent energy bank.
The original closing join compares it with the retained first root reading
at the common fan depth, including its primitive endpoint correction.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyClosing

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count} {cover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}
  {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget target energyTarget joining :
    Normalization.InverseRootPolynomial.Coordinate}
  {minimum index depth readingIndex energyFloor energyDepth joinFloor : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- The actual closing energy-potential difference is bounded by eighty times the chart target plus twice the retained
root-return allowance.

The estimate uses the same cached parent energy endpoints and closing join at a sufficiently late shared reading stage.
-/
theorem closing_bound (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1)
    (targetNonnegative : 0 ≤ target) (joinNonnegative : 0 ≤ joining) (joinSmall : joining ≤ 1)
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents}
    {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers} {requests :
      Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.SideRequests.SideBank.Evaluations sample depth readingIndex
      requests) (charts : Hyperelliptic.Charts.Reciprocal.Disk.SideChartRequests.ChartReplacements target evaluated)
    (energies : Hyperelliptic.Charts.Reciprocal.Disk.SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth
      evaluated charts) {joined : Hyperelliptic.Charts.Reciprocal.Disk.ClosingJoins.ClosingJoin prepared}
    (closing : Hyperelliptic.Charts.Reciprocal.Disk.ClosingRequests.ClosingRequest joining joinFloor prepared joined)
      (later : closing.maximum ≤ readingIndex) :
    Data.Gaussian.Norm.Basic.normSq
      (Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.firstPotential evaluated
      charts energies -
      Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.lastPotential evaluated charts
      energies (Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.firstPotential
      evaluated charts energies) -
      Path.BoundaryRibbon.area (Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.lastValue evaluated
        (Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.firstValue evaluated))
        (Hyperelliptic.Charts.Reciprocal.Disk.SideConnections.Evaluations.firstValue evaluated)) ≤ 80 * target + 2 *
          joining := by
  have bound := (Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.endBank branch
    evaluated charts energies).closing_bound branch targetNonnegative joinNonnegative joinSmall closing later
  rw [Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.endBank_firstPotential
    evaluated charts energies branch,
    Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.endBank_firstValue evaluated
    charts energies branch,
    Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.endBank_lastPotential evaluated
    charts energies branch,
    Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements.EnergyData.endBank_lastValue evaluated
    charts energies branch] at bound
  exact bound

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyClosing
