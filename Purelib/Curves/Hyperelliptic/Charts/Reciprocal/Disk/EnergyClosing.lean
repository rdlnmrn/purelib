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

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyEndReadback.ChartReplacements

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

variable {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : UniformReciprocalModels.Data patch count} {cover :
    UniformReciprocalCover.Cover data}
  {sourceTarget reciprocalTarget coefficientTarget totalTarget areaTarget target energyTarget joining :
    Normalization.InverseRootPolynomial.Coordinate}
  {minimum index depth readingIndex energyFloor energyDepth joinFloor : Nat} {box : Rational.Box}
  {sample : Cap.Primitives.Sample cap differential index box}

/-- The actual closing energy-potential difference is bounded by eighty times the chart target plus twice the retained
root-return allowance.

The estimate uses the same cached parent energy endpoints and closing join at a sufficiently late shared reading stage.
-/
theorem closing_bound (branch : HyperellipticReciprocal.originOrder curve = 1)
    (targetNonnegative : 0 ≤ target) (joinNonnegative : 0 ≤ joining) (joinSmall : joining ≤ 1)
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)} {covers :
      UniformReciprocalCover.ParentCovers parents}
    {prepared : ParentJoins.SideBank regular covers} {requests :
      SideRequests.SideBank.Requests sourceTarget reciprocalTarget
      coefficientTarget totalTarget areaTarget minimum prepared}
    (evaluated : SideRequests.SideBank.Evaluations sample depth readingIndex
      requests) (charts : SideChartRequests.ChartReplacements target evaluated)
    (energies : SideEnergyRequests.EnergyData energyTarget energyFloor energyDepth
      evaluated charts) {joined : ClosingJoins.ClosingJoin prepared}
    (closing : ClosingRequests.ClosingRequest joining joinFloor prepared joined)
      (later : closing.maximum ≤ readingIndex) :
    Gaussian.Norm.Basic.normSq
      (EnergyData.firstPotential evaluated
      charts energies -
      EnergyData.lastPotential evaluated charts
      energies (EnergyData.firstPotential
      evaluated charts energies) -
      Path.BoundaryRibbon.area (SideConnections.Evaluations.lastValue evaluated
        (SideConnections.Evaluations.firstValue evaluated))
        (SideConnections.Evaluations.firstValue evaluated)) ≤ 80 * target + 2 *
          joining := by
  have bound := (EnergyData.endBank branch
    evaluated charts energies).closing_bound branch targetNonnegative joinNonnegative joinSmall closing later
  rw [EnergyData.endBank_firstPotential
    evaluated charts energies branch,
    EnergyData.endBank_firstValue evaluated
    charts energies branch,
    EnergyData.endBank_lastPotential evaluated
    charts energies branch,
    EnergyData.endBank_lastValue evaluated
    charts energies branch] at bound
  exact bound

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyClosing
