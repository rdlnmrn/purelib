module
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartEnergy
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartSchedule
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartTraces
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectorBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonEnergySamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonRibbons
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnector
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartBudget
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartPath
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.IntervalChartRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PathValues
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartBasisRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisRequest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.RootRadialGeometry
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonChartReadings.BasisCommonChartRequests

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonConnectedPaths.BasisCommonChartRequests.Plans

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Exact endpoint and trace readbacks for the physically joined common path. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback

variable {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {cover : UniformReciprocalCover.Cover data} {covers :
    SourceLocations.BasisSourceCovers parent}
  {regular : RegularBounds.Data cap} {bounds :
    ReciprocalPaddedInverse.UniformBounds regular.padded}
  {depth floor sourceFloor : Nat} {target sourceTarget : Normalization.InverseRootPolynomial.Coordinate}
  {index minimum stage : Nat} {box : Rational.Box}
  {capSample : Cap.Primitives.Sample cap differential index box}
  {polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {anchorBank : UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges}
  {bank : SourceLocations.BasisSourceLocations.SampleBank covers index}
  {basis : ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {joinTarget : Normalization.InverseRootPolynomial.Coordinate} {joinFloor : Nat}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Basic.Canonical

variable {energyTarget : Normalization.InverseRootPolynomial.Coordinate} {energyFloor energyDepth : Nat}

variable {originals :
  CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank covers index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Readings

/-- The first original chart endpoint value, or zero for an empty common interval list. -/
@[expose] def firstChartValue (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} →
      Plans.Readings anchorBank
      bank stage requests plans → Normalization.InverseRootPolynomial.Gaussian
  | _, .nil, _, _ => 0
  | _, .cons _ _, _, readings => polynomials.value coefficients readings.1.evaluated.first.root.coordinate

/-- The last original chart endpoint value, traversing the retained interval readings and returning zero for an empty
list. -/
@[expose] def lastChartValue (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    {intervals : List (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} →
      Plans.Readings anchorBank
      bank stage requests plans → Normalization.InverseRootPolynomial.Gaussian
  | _, .nil, _, _ => 0
  | _, .cons _ .nil, _, readings => polynomials.value coefficients readings.1.evaluated.last.root.coordinate
  | _, .cons _ (.cons next remaining), _, readings =>
    Readings.lastChartValue coefficients
    (.cons next remaining) readings.2

end Readings

namespace EnergySamples

/-- The first retained energy potential, or zero for an empty interval list. -/
@[expose] def firstPotential : {intervals : List
  (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Plans.Readings anchorBank
      bank stage requests plans} →
    {energies : CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings} →
    CommonEnergySamples.EnergySamples coefficients requests plans readings
      energies → Normalization.InverseRootPolynomial.Gaussian
  | _, .nil, _, _, _, _ => 0
  | _, .cons _ _, _, _, _, samples => samples.1.firstPotential

/-- The last retained energy potential on the original common interval traversal. -/
@[expose] def lastPotential : {intervals : List
  (CommonCover.BasisCommonInterval cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → {readings :
      Plans.Readings anchorBank
      bank stage requests plans} →
    {energies : CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings} →
    CommonEnergySamples.EnergySamples coefficients requests plans readings
      energies → Normalization.InverseRootPolynomial.Gaussian
  | _, .nil, _, _, _, _ => 0
  | _, .cons _ .nil, _, _, _, samples => samples.1.lastPotential
  | _, .cons _ (.cons next remaining), _, _, _, samples =>
    EnergySamples.lastPotential (.cons
    next remaining) samples.2

end EnergySamples

namespace Traces

variable {arcAllowance : Normalization.InverseRootPolynomial.Coordinate}

/-- Adding an endpoint increment to its starting value gives the terminal value. -/
private theorem endpoint_add (first last : Normalization.InverseRootPolynomial.Gaussian) : first + (last - first) = last
  := by ring1

/-- An incoming connector followed by the original head and tail paths splits their trace area at the retained
endpoints. -/
private theorem trace_step (start incoming first last : Normalization.InverseRootPolynomial.Gaussian) (head tail : List
  Normalization.InverseRootPolynomial.Gaussian)
    (begins : start + incoming = first) (total : Gaussian.Norm.Sum.Basic.gaussianSum head = last - first) :
    Path.IncrementArea.traceArea start (incoming :: (head ++ tail)) = Path.BoundaryRibbon.area start first +
      (Path.IncrementArea.traceArea first head + Path.IncrementArea.traceArea last tail) := by
  rw [Path.IncrementArea.traceArea, begins, Path.IncrementArea.traceArea_append, total,
    endpoint_add]

/-- The signed head and tail corrections telescope with the original connector potential difference. -/
private theorem splice_corrections (a b c d e f g h i j : Normalization.InverseRootPolynomial.Gaussian)
    (tail : e + f = -g + h - d + i) :
    ((-a + c - b) + e) + ((d - c - i) + f) = -(j + (a + g)) + h - b + j := by
  calc
    _ = -a + c - b + (e + f) + d - c - i := by ring1
    _ = _ := by rw [tail]; ring1

/-- The complete joined original path has total increment equal to its last chart value minus the supplied start.

The incoming increment must reach the first retained chart endpoint, and the original interval list is nonempty. -/
theorem joined_total : {intervals : List (CommonCover.BasisCommonInterval
  cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → (readings :
      Plans.Readings anchorBank
      bank stage requests plans) →
    (paths : CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings) →
    (energies : CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings) →
    (samples : CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies) →
    (traces : CommonChartTraces.Traces arcAllowance requests plans readings
      paths energies samples) →
    (connectors : CommonConnectorBank.Connectors coefficients energyDepth
      joinTarget requests plans readings) →
    intervals ≠ [] → (start incoming : Normalization.InverseRootPolynomial.Gaussian) →
    start + incoming = Readings.firstChartValue
      coefficients requests readings →
    Gaussian.Norm.Sum.Basic.gaussianSum
      (((Paths.joinedBlocks
      incoming paths connectors).map (fun block => block.1 :: block.2)).flatten) =
      Readings.lastChartValue coefficients requests
        readings - start
  | _, .nil, _, _, _, _, _, _, _, nonempty, _, _, _ => by cases nonempty rfl
  | _, .cons _ .nil, _, readings, paths, energies, samples, traces, _, _, start, incoming, begins => by
      have total := traces.1.summary.total_eq.symm.trans traces.1.total_eq
      change start + incoming = polynomials.value coefficients readings.1.evaluated.first.root.coordinate at begins
      rw
        [Paths.joinedBlocks]
      simp only [-eq_self, -iff_self, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        Data.List.Append.append_nil]
      change incoming + Gaussian.Norm.Sum.Basic.gaussianSum (paths.1.paired.pairs.map Prod.snd) = _
      rw [total, ← begins]
      change _ = polynomials.value coefficients readings.1.evaluated.last.root.coordinate - start
      ring1
  | _, .cons _ (.cons next remaining), _, readings, paths, energies, samples, traces, connectors, _, start, incoming,
    begins =>
    by
      have total := traces.1.summary.total_eq.symm.trans traces.1.total_eq
      have nextBegins : polynomials.value coefficients readings.1.evaluated.last.root.coordinate +
        connectors.1.increment =
          Readings.firstChartValue coefficients (.cons
            next remaining) readings.2 := by
        rw [connectors.1.increment_eq, connectors.1.first_eq, connectors.1.last_eq]
        change _ = polynomials.value coefficients readings.2.1.evaluated.first.root.coordinate
        ring1
      have tail := Traces.joined_total
        (.cons next remaining) readings.2 paths.2 energies.2 samples.2 traces.2 connectors.2
        (by intro impossible; cases impossible) _ _ nextBegins
      change start + incoming = polynomials.value coefficients readings.1.evaluated.first.root.coordinate at begins
      rw
        [Paths.joinedBlocks]
      simp only [-eq_self, -iff_self, List.map_cons, List.flatten_cons, List.cons_append]
      change incoming + Gaussian.Norm.Sum.Basic.gaussianSum ((paths.1.paired.pairs.map Prod.snd) ++ _) = _
      rw [Path.IncrementArea.sum_append, total, tail, ← begins]
      change _ = Readings.lastChartValue coefficients
        (.cons next remaining) readings.2 - start
      ring1

/-- The original corrected chart areas and signed ribbons equal the trace area and terminal potential difference of the
joined path.

All original connector increments, endpoint potentials and the initial ribbon correction remain in the exact readback.
-/
theorem joined_trace : {intervals : List (CommonCover.BasisCommonInterval
  cover covers)} →
    (requests : CommonChartSchedule.BasisCommonChartRequests regular depth
      target sourceTarget floor sourceFloor intervals) →
    {plans : CommonChartSchedule.BasisCommonChartRequests.Plans capSample
      polynomials minimum requests} → (readings :
      Plans.Readings anchorBank
      bank stage requests plans) →
    (paths : CommonChartPaths.BasisCommonChartRequests.Plans.Paths originals
      coefficients requests plans readings) →
    (energies : CommonChartEnergy.Energies energyTarget energyFloor
      energyDepth requests plans readings) →
    (samples : CommonEnergySamples.EnergySamples coefficients requests plans
      readings energies) →
    (traces : CommonChartTraces.Traces arcAllowance requests plans readings
      paths energies samples) →
    (connectors : CommonConnectorBank.Connectors coefficients energyDepth
      joinTarget requests plans readings) →
    intervals ≠ [] → (start incoming : Normalization.InverseRootPolynomial.Gaussian) →
    start + incoming = Readings.firstChartValue
      coefficients requests readings →
    Gaussian.Norm.Sum.Basic.gaussianSum traces.correctedAreas + Gaussian.Norm.Sum.Basic.gaussianSum
      (CommonRibbons.Connectors.ribbonValues requests energies samples
      connectors) =
      -Path.IncrementArea.traceArea start
        (((Paths.joinedBlocks
        incoming paths connectors).map (fun block => block.1 :: block.2)).flatten) +
      EnergySamples.lastPotential requests samples -
        EnergySamples.firstPotential requests samples +
        Path.BoundaryRibbon.area start
        (Readings.firstChartValue coefficients requests
        readings)
  | _, .nil, _, _, _, _, _, _, _, nonempty, _, _, _ => by cases nonempty rfl
  | _, .cons _ .nil, _, readings, paths, energies, samples, traces, _, _, start, incoming, begins => by
      have total := traces.1.summary.total_eq.symm.trans traces.1.total_eq
      change start + incoming = polynomials.value coefficients readings.1.evaluated.first.root.coordinate at begins
      rw
        [Paths.joinedBlocks]
      simp only [-eq_self, -iff_self, List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil,
        Data.List.Append.append_nil]
      change (traces.1.corrected + 0) + 0 =
        -Path.IncrementArea.traceArea start (incoming :: paths.1.paired.pairs.map Prod.snd) + samples.1.lastPotential -
          samples.1.firstPotential +
        Path.BoundaryRibbon.area start (polynomials.value coefficients readings.1.evaluated.first.root.coordinate)
      rw [Path.IncrementArea.traceArea, begins, ← traces.1.trace_eq, traces.1.corrected_eq]
      ring1
  | _, .cons _ (.cons next remaining), _, readings, paths, energies, samples, traces, connectors, _, start, incoming,
    begins =>
    by
      have total := traces.1.summary.total_eq.symm.trans traces.1.total_eq
      have nextBegins : polynomials.value coefficients readings.1.evaluated.last.root.coordinate +
        connectors.1.increment =
          Readings.firstChartValue coefficients (.cons
            next remaining) readings.2 := by
        rw [connectors.1.increment_eq, connectors.1.first_eq, connectors.1.last_eq]
        change _ = polynomials.value coefficients readings.2.1.evaluated.first.root.coordinate
        ring1
      have tail := Traces.joined_trace
        (.cons next remaining) readings.2 paths.2 energies.2 samples.2 traces.2 connectors.2
        (by intro impossible; cases impossible) _ _ nextBegins
      change start + incoming = polynomials.value coefficients readings.1.evaluated.first.root.coordinate at begins
      rw
        [Paths.joinedBlocks]
      simp only [-eq_self, -iff_self, List.map_cons, List.flatten_cons, List.cons_append]
      change (traces.1.corrected + Gaussian.Norm.Sum.Basic.gaussianSum traces.2.correctedAreas) +
        ((samples.2.1.firstPotential - samples.1.lastPotential - Path.BoundaryRibbon.area connectors.1.firstValue
          connectors.1.lastValue) +
          Gaussian.Norm.Sum.Basic.gaussianSum
            (CommonRibbons.Connectors.ribbonValues (.cons next remaining)
            energies.2 samples.2 connectors.2)) =
        -Path.IncrementArea.traceArea start (incoming :: ((paths.1.paired.pairs.map Prod.snd) ++ _)) +
        EnergySamples.lastPotential (.cons next
          remaining) samples.2 - samples.1.firstPotential +
        Path.BoundaryRibbon.area start (polynomials.value coefficients readings.1.evaluated.first.root.coordinate)
      rw [trace_step start incoming _ _ _ _ begins
        total,
        ← traces.1.trace_eq, traces.1.corrected_eq]
      have rearrange := tail
      change Gaussian.Norm.Sum.Basic.gaussianSum traces.2.correctedAreas + Gaussian.Norm.Sum.Basic.gaussianSum
        (CommonRibbons.Connectors.ribbonValues (.cons next remaining)
        energies.2 samples.2 connectors.2) =
        -Path.IncrementArea.traceArea _ _ +
          EnergySamples.lastPotential (.cons next
          remaining) samples.2 - samples.2.1.firstPotential +
        Path.BoundaryRibbon.area (polynomials.value coefficients readings.1.evaluated.last.root.coordinate)
          (polynomials.value coefficients readings.2.1.evaluated.first.root.coordinate) at rearrange
      have connectorArea : Path.BoundaryRibbon.area connectors.1.firstValue connectors.1.lastValue =
          Path.BoundaryRibbon.area (polynomials.value coefficients readings.1.evaluated.last.root.coordinate)
            (polynomials.value coefficients readings.2.1.evaluated.first.root.coordinate) :=
        congrArg₂ Path.BoundaryRibbon.area connectors.1.first_eq connectors.1.last_eq
      rw [← connectorArea] at rearrange
      exact splice_corrections _ _ _ _ _ _ _ _ _ _
        rearrange

end Traces
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonTraceReadback
