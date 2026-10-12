module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Arithmetic.Add
import Purelib.Approximation.Gaussian.Coherent.FiniteSum
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Geometric.Coherent.Comparison
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Sum.Congruence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Periods.Pairing
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Path.Cancellation
import Purelib.Integration.Program.Comparison
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Program.Gaussian.Name
public import Purelib.Riemann.BilinearRelations.Certificate
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Topology.Cells
import Purelib.Topology.BranchedCover.Double.Attachment

public import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Vector.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-!
# Prepared finite Stokes reduction

This module connects the prepared cycle geometry to the first bilinear
relation.  For a pair of standard differentials it materializes every local
zero-wedge chart on every displayed A- and B-cycle at one finite refinement.
A boundary-reduction certificate identifies the canonical primitive boundary
constructed in `FiniteBilinear` with that explicit finite wedge sum.  Since
each summand is already operationally zero, primitive closure and the Stokes
certificate are then derived.
-/

namespace Purelib.Riemann.Topology.PreparedStokes

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Periods.PeriodMatrix
open Purelib.LinearAlgebra.Gaussian.QuadraticForm

open Purelib.Data.Rat in
/-- The rational coordinate carrier of finite face and comparison budgets. -/
abbrev Coordinate := Fraction.Rational
/-- A coherent named Gaussian quantity with its retained approximation program. -/
abbrev CoherentNamed := Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
/-- Operational equivalence of the two retained Gaussian names. -/
abbrev NamedEquivalent := Purelib.Approximation.Gaussian.Equivalence.NamedEquivalent
/-- The finite Gaussian integral refinement program with explicit error and sample bounds. -/
abbrev RefinementProgram :=
  Purelib.Integration.Program.Gaussian.Basic.RefinementProgram
open Purelib.Curves.Hyperelliptic in
/-- A retained local wedge chart for the exact curve and ordered differential pair. -/
abbrev WedgeChart {genus : Nat} (curve : Basic.HyperellipticCurve genus)
    (leftDifferential rightDifferential : Differentials.Basic.Differential genus) :=
  Purelib.Riemann.Integration.PreparedSubdivisionModelCore.WedgeChart curve leftDifferential
    rightDifferential

/-- The rational parameter zero lies in the closed unit interval. -/
private theorem zeroInside :
    (0 : Coordinate) <= 0 ∧ (0 : Coordinate) <= 1 := by decide

/-- The rational parameter zero lies in the closed unit interval. -/
theorem zeroInsidePublic :
    (0 : Coordinate) <= 0 ∧ (0 : Coordinate) <= 1 := by decide

open Purelib.Curves.Hyperelliptic in
/-- Read the retained wedge coefficient at the initial chart parameter. -/
def chartContribution {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {leftDifferential rightDifferential : Differentials.Basic.Differential genus}
    (chart : WedgeChart curve leftDifferential rightDifferential) :
    CoherentNamed :=
  chart.coefficient 0 zeroInsidePublic

section
open Purelib.Approximation.Gaussian
open Purelib.Curves.Hyperelliptic
/-- The retained chart contribution is equivalent to the exact zero name. -/
def chartContribution_zero {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {leftDifferential rightDifferential : Differentials.Basic.Differential genus}
    (chart : WedgeChart curve leftDifferential rightDifferential) :
    NamedEquivalent (chartContribution chart).name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name :=
  chart.zero 0 zeroInsidePublic

/-- Sum the ordered chart contributions as coherent Gaussian names. -/
def wedgeSum {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {leftDifferential rightDifferential : Differentials.Basic.Differential genus} :
    List (WedgeChart curve leftDifferential rightDifferential) -> CoherentNamed
  | [] => Name.Coherent.CoherentNamed.Coherence.exact 0
  | chart :: remaining =>
      Name.Coherent.CoherentNamed.add (chartContribution chart)
        (wedgeSum remaining)

/-- A finite sum of the retained zero wedge contributions is equivalent to exact zero. -/
def wedgeSum_zero {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {leftDifferential rightDifferential : Differentials.Basic.Differential genus} :
    (charts : List
      (WedgeChart curve leftDifferential rightDifferential)) ->
      NamedEquivalent (wedgeSum charts).name
        (Name.Coherent.CoherentNamed.Coherence.exact 0).name
  | [] => Equivalence.NamedEquivalent.refl _
  | chart :: remaining => by
      let zero := Name.Coherent.CoherentNamed.Coherence.exact 0
      have replaceBoth : NamedEquivalent
          (Name.Coherent.CoherentNamed.add
            (chartContribution chart) (wedgeSum remaining)).name
          (Name.Coherent.CoherentNamed.add zero zero).name :=
        Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
          (chartContribution chart) zero (wedgeSum remaining) zero
          (chartContribution_zero chart) (wedgeSum_zero remaining)
      exact Equivalence.NamedEquivalent.trans replaceBoth
        (Arithmetic.Add.coherentAdd_zero_right zero)

end

section
open Purelib.Curves.Hyperelliptic
open Purelib.Riemann.Topology
/-- Collect A then B wedge charts in original finite cycle order at the requested stage. -/
def surfaceCharts {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve)
    (row column : Fin genus) (refinement : Nat) :
    List (WedgeChart curve (standardDifferential row)
      (standardDifferential column)) :=
  (List.ofFn fun cycle : Fin genus =>
    PreparedCycleModels.PreparedCycleData.wedgeCharts
        (standardDifferential row) (standardDifferential column)
        ((geometry.aCycle cycle).data refinement) ++
      PreparedCycleModels.PreparedCycleData.wedgeCharts
        (standardDifferential row) (standardDifferential column)
        ((geometry.bCycle cycle).data refinement)).flatten

/-- The coherent sum of the retained surface charts for the ordered differential pair. -/
def surfaceWedgeSum {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve)
    (row column : Fin genus) (refinement : Nat) : CoherentNamed :=
  wedgeSum (surfaceCharts geometry row column refinement)

end

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Topology in
/-- The retained surface wedge sum is equivalent to the exact zero name. -/
def surfaceWedgeSum_zero {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve)
    (row column : Fin genus) (refinement : Nat) :
    NamedEquivalent (surfaceWedgeSum geometry row column refinement).name
    (Name.Coherent.CoherentNamed.Coherence.exact 0).name :=
  wedgeSum_zero (surfaceCharts geometry row column refinement)

/-! ## Edge pairs indexed by the actual hyperelliptic cell surface -/

open Purelib in
open Purelib.Integration.Path in
/-- Sum the paired boundary-program readings over both sheets and original base indices. -/
def cellularBoundarySum {baseCount : Nat}
    (pairs : Fin baseCount ->
      Topology.BranchedCover.Double.Attachment.Sheet ->
        Cancellation.ProgramBoundaryPair) : CoherentNamed :=
  sumNamed fun base =>
    Cancellation.boundarySum fun sheet =>
      (pairs base sheet).toBoundaryPair

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Integration.Path in
/-- The finite paired cellular boundary sum is equivalent to exact zero. -/
def cellularBoundarySum_zero {baseCount : Nat}
    (pairs : Fin baseCount ->
      Topology.BranchedCover.Double.Attachment.Sheet ->
        Cancellation.ProgramBoundaryPair) :
    NamedEquivalent (cellularBoundarySum pairs).name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name :=
  Coherent.FiniteSum.sumNamed_zero
    (fun base =>
      Cancellation.boundarySum fun sheet =>
        (pairs base sheet).toBoundaryPair)
    (fun base =>
      Cancellation.boundarySum_zero fun sheet =>
        (pairs base sheet).toBoundaryPair)

set_option genInjectivity false in
open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Path in
/-- Paired boundary programs indexed by the curve's odd or even cell decomposition.

The degree identity selects the original finite base count, and every base index retains separate readings on both
sheets. -/
inductive CellularEdgePairs {genus : Nat}
    (curve : Basic.HyperellipticCurve genus) : Type 1
  /-- Paired boundary programs for the retained odd-degree cell decomposition. -/ | odd
      (degree_eq : curve.polynomial.natDegree = 2 * genus + 1)
      (pairs : Fin (Topology.Cells.oddBaseCount genus) ->
        Topology.BranchedCover.Double.Attachment.Sheet ->
          Cancellation.ProgramBoundaryPair)
  /-- Paired boundary programs for the retained even-degree cell decomposition. -/ | even
      (degree_eq : curve.polynomial.natDegree = 2 * genus + 2)
      (pairs : Fin (Topology.Cells.evenBaseCount genus) ->
        Topology.BranchedCover.Double.Attachment.Sheet ->
          Cancellation.ProgramBoundaryPair)

constructive_injectivity CellularEdgePairs

namespace CellularEdgePairs

open Purelib.Curves.Hyperelliptic in
/-- The number of retained cellular boundary pairs across both sheets. -/
def pairCount {genus : Nat} {curve : Basic.HyperellipticCurve genus} :
    CellularEdgePairs curve -> Nat
  | .odd _ _ => Topology.Cells.oddBaseCount genus * 2
  | .even _ _ => Topology.Cells.evenBaseCount genus * 2

section
open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Integration.Path
/-- The odd-degree paired boundary count equals the original odd cell complex's edge count. -/
theorem odd_pairCount {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (degree_eq : curve.polynomial.natDegree = 2 * genus + 1)
    (pairs : Fin (Topology.Cells.oddBaseCount genus) ->
      Topology.BranchedCover.Double.Attachment.Sheet ->
        Cancellation.ProgramBoundaryPair) :
    (CellularEdgePairs.odd degree_eq pairs).pairCount =
      (Topology.Cells.oddCellComplex genus).edges.length := by
  rw [Topology.Cells.oddCellComplex_edgeCount]
  rfl

/-- The even-degree paired boundary count equals the original even cell complex's edge count. -/
theorem even_pairCount {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (degree_eq : curve.polynomial.natDegree = 2 * genus + 2)
    (pairs : Fin (Topology.Cells.evenBaseCount genus) ->
      Topology.BranchedCover.Double.Attachment.Sheet ->
        Cancellation.ProgramBoundaryPair) :
    (CellularEdgePairs.even degree_eq pairs).pairCount =
      (Topology.Cells.evenCellComplex genus).edges.length := by
  rw [Topology.Cells.evenCellComplex_edgeCount]
  rfl

end

open Purelib.Curves.Hyperelliptic in
/-- Read the coherent paired boundary sum for the retained degree case. -/
def boundarySum {genus : Nat} {curve : Basic.HyperellipticCurve genus} :
    CellularEdgePairs curve -> CoherentNamed
  | .odd _ pairs => cellularBoundarySum pairs
  | .even _ pairs => cellularBoundarySum pairs

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
/-- The retained odd or even cellular boundary sum is equivalent to exact zero. -/
def boundarySum_zero {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    (pairs : CellularEdgePairs curve) :
    NamedEquivalent pairs.boundarySum.name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name := by
  cases pairs with
  | odd degree_eq pairs => exact cellularBoundarySum_zero pairs
  | even degree_eq pairs => exact cellularBoundarySum_zero pairs

end CellularEdgePairs

set_option genInjectivity false in
open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Path in
open Purelib.Riemann.Topology in
/-- A retained comparison of each period primitive with paired boundaries and surface wedges.

The record keeps the original differential-pair stage, finite edge-pair family and operational comparison to their exact
sum. -/
structure BoundaryReduction {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      PreparedCycleModels.PeriodSchedules curve geometry) where
  /-- The retained surface refinement stage for the original differential pair. -/ refinement : Fin genus -> Fin genus
    -> Nat
  /-- The retained finite number of edge pairs for each original differential pair. -/ edgePairCount : Fin genus -> Fin
    genus -> Nat
  /-- The original indexed family of paired boundary programs. -/ edgePairs : forall row column : Fin genus,
    Fin (edgePairCount row column) ->
      Cancellation.ProgramBoundaryPair
  /-- The original accumulated primitive is equivalent to the retained paired-boundary and surface-wedge sum. -/
    boundary_eq_surface : forall row column : Fin genus,
    NamedEquivalent
      (Periods.Pairing.periodPairingPrimitiveFinish
        schedules.toPeriodData row column).name
      (Name.Coherent.CoherentNamed.add
        (Cancellation.boundarySum fun index =>
          (edgePairs row column index).toBoundaryPair)
        (surfaceWedgeSum geometry row column
          (refinement row column))).name

constructive_injectivity BoundaryReduction

namespace BoundaryReduction

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Path in
open Purelib.Riemann.Topology in
/-- Close the original period primitives using the retained reduction certificates. -/
def toStokesClosure {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : BoundaryReduction schedules) :
    Periods.Pairing.StokesClosure
      schedules.toPeriodData where
  closed := by
    intro row column
    let paired := Cancellation.boundarySum fun index =>
      (reduction.edgePairs row column index).toBoundaryPair
    let wedges := surfaceWedgeSum geometry row column
      (reduction.refinement row column)
    let zero := Name.Coherent.CoherentNamed.Coherence.exact 0
    have pairedZero : NamedEquivalent paired.name zero.name := by
      simpa only [paired, zero] using
        Cancellation.boundarySum_zero fun index =>
          (reduction.edgePairs row column index).toBoundaryPair
    have wedgesZero : NamedEquivalent wedges.name zero.name := by
      simpa only [wedges, zero] using
        surfaceWedgeSum_zero geometry row column
          (reduction.refinement row column)
    have totalZero : NamedEquivalent
        (Name.Coherent.CoherentNamed.add paired wedges).name
        zero.name :=
      Equivalence.NamedEquivalent.trans
        (Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
          paired zero wedges zero pairedZero wedgesZero)
        (Arithmetic.Add.coherentAdd_zero_right zero)
    exact Equivalence.NamedEquivalent.trans
      (by
          simpa only [paired, wedges]
            using reduction.boundary_eq_surface row column)
      totalZero

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Topology in
/-- Read the Stokes certificate from the closure of the original retained period data. -/
def toStokesCertificate {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : BoundaryReduction schedules) :
    Riemann.BilinearRelations.Certificate.StokesCertificate schedules.toPeriodData :=
  reduction.toStokesClosure.toStokesCertificate

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Path in
open Purelib.Riemann.Topology in
/-- Construct the genus-one boundary reduction with no edge pairs and the original zero wedge sum. -/
def genusOne {curve : Basic.HyperellipticCurve 1}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      PreparedCycleModels.PeriodSchedules curve geometry) :
    BoundaryReduction schedules where
  refinement := fun _row _column => 0
  edgePairCount := fun _row _column => 0
  edgePairs := fun _row _column index => Fin.elim0 index
  boundary_eq_surface := by
    intro row column
    let wedges := surfaceWedgeSum geometry row column 0
    let zero := Name.Coherent.CoherentNamed.Coherence.exact 0
    have finishZero : NamedEquivalent
        (Periods.Pairing.periodPairingPrimitiveFinish
          schedules.toPeriodData row column).name zero.name := by
      simpa only [zero] using
        (Periods.Pairing.StokesClosure.genusOne
          schedules.toPeriodData).closed row column
    have wedgesZero : NamedEquivalent wedges.name zero.name := by
      simpa only [wedges, zero] using
        surfaceWedgeSum_zero geometry row column 0
    have totalToWedges : NamedEquivalent
        (Name.Coherent.CoherentNamed.add
          (Cancellation.boundarySum
            (fun index : Fin 0 =>
              (Fin.elim0 index :
                Cancellation.ProgramBoundaryPair).toBoundaryPair))
          wedges).name
        wedges.name := by
      change NamedEquivalent
        (Name.Coherent.CoherentNamed.add
          (Name.Coherent.CoherentNamed.Coherence.exact 0) wedges).name
        wedges.name
      simpa only [Name.Coherent.CoherentNamed.add,
        Name.Coherent.CoherentNamed.Coherence.exact] using
        Arithmetic.Add.coherentAdd_zero_left wedges
    have totalZero :=
      Equivalence.NamedEquivalent.trans totalToWedges wedgesZero
    exact Equivalence.NamedEquivalent.trans finishZero
      (Equivalence.NamedEquivalent.symm totalZero)

end BoundaryReduction

/-! ## Degree-shaped prepared surface reduction -/

set_option genInjectivity false in
open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Topology in
/-- A boundary reduction retaining the curve's original cellular edge-pair indexing.

Each ordered differential pair keeps its chosen stage and odd or even cellular family, together with the exact
primitive-to-boundary comparison. -/
structure CellularBoundaryReduction {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      PreparedCycleModels.PeriodSchedules curve geometry) where
  /-- The retained surface refinement stage for the original differential pair. -/ refinement : Fin genus -> Fin genus
    -> Nat
  /-- The original indexed family of paired boundary programs. -/ edgePairs : forall _row _column : Fin genus,
    CellularEdgePairs curve
  /-- The original accumulated primitive is equivalent to the retained paired-boundary and surface-wedge sum. -/
    boundary_eq_surface : forall row column : Fin genus,
    NamedEquivalent
      (Periods.Pairing.periodPairingPrimitiveFinish
        schedules.toPeriodData row column).name
      (Name.Coherent.CoherentNamed.add
        (edgePairs row column).boundarySum
        (surfaceWedgeSum geometry row column
          (refinement row column))).name

constructive_injectivity CellularBoundaryReduction

namespace CellularBoundaryReduction

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Topology in
/-- Close the original period primitives using the retained reduction certificates. -/
def toStokesClosure {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : CellularBoundaryReduction schedules) :
    Periods.Pairing.StokesClosure
      schedules.toPeriodData where
  closed := by
    intro row column
    let paired := (reduction.edgePairs row column).boundarySum
    let wedges := surfaceWedgeSum geometry row column
      (reduction.refinement row column)
    let zero := Name.Coherent.CoherentNamed.Coherence.exact 0
    have pairedZero : NamedEquivalent paired.name zero.name := by
      simpa only [paired, zero] using
        (reduction.edgePairs row column).boundarySum_zero
    have wedgesZero : NamedEquivalent wedges.name zero.name := by
      simpa only [wedges, zero] using
        surfaceWedgeSum_zero geometry row column
          (reduction.refinement row column)
    have totalZero : NamedEquivalent
        (Name.Coherent.CoherentNamed.add paired wedges).name
        zero.name :=
      Equivalence.NamedEquivalent.trans
        (Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
          paired zero wedges zero pairedZero wedgesZero)
        (Arithmetic.Add.coherentAdd_zero_right zero)
    exact Equivalence.NamedEquivalent.trans
      (by
          simpa only [paired, wedges]
            using reduction.boundary_eq_surface row column)
      totalZero

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Topology in
/-- Read the Stokes certificate from the closure of the original retained period data. -/
def toStokesCertificate {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : CellularBoundaryReduction schedules) :
    Riemann.BilinearRelations.Certificate.StokesCertificate schedules.toPeriodData :=
  reduction.toStokesClosure.toStokesCertificate

end CellularBoundaryReduction

/-! ## Local two-dimensional triangulated Stokes input -/

set_option genInjectivity false in
open Purelib.Approximation.Gaussian in
/-- Two retained geometric Gaussian streams providing the paired primitive coordinates.

Both streams are sampled at the same original natural-number stage to form each primitive point. -/
structure PrimitiveStream where
  /-- The retained left primitive-coordinate stream. -/ left : Geometric.GeometricApproximation
  /-- The retained right primitive-coordinate stream. -/ right : Geometric.GeometricApproximation

constructive_injectivity PrimitiveStream

namespace PrimitiveStream

open Purelib.Topology.Polygon in
/-- Read the two retained primitive streams at the same stage. -/
def sample (stream : PrimitiveStream) (index : Nat) :
    Stokes.PrimitivePoint :=
  ⟨stream.left.sample index, stream.right.sample index⟩

/-- The sampled primitive's left coordinate is the retained left stream sample. -/
@[simp] theorem sample_left (stream : PrimitiveStream) (index : Nat) :
    (stream.sample index).left = stream.left.sample index := rfl

/-- The sampled primitive's right coordinate is the retained right stream sample. -/
@[simp] theorem sample_right (stream : PrimitiveStream) (index : Nat) :
    (stream.sample index).right = stream.right.sample index := rfl

end PrimitiveStream

open Purelib.Data.Gaussian in
/-- The inverse of two in the canonical Gaussian rational field. -/
def gaussianHalf : Basic.Canonical :=
  Data.Gaussian.Field.inv 2

open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
/-- Half the oriented wedge area of the triangle's three retained primitive points. -/
def triangleIntegral {vertexCount : Nat}
    (points : Fin vertexCount ->
      Stokes.PrimitivePoint)
    (triangle :
      Stokes.OrientedTriangle vertexCount) :
    Basic.Canonical :=
  gaussianHalf *
    Stokes.triangleWedgeArea
      (points triangle.first) (points triangle.second) (points triangle.third)

open Purelib.Data.Gaussian in
/-- Multiplying a doubled Gaussian quantity by the retained half recovers it exactly. -/
theorem gaussianHalf_mul_two
    (value : Basic.Canonical) :
    gaussianHalf * (2 * value) = value := by
  unfold gaussianHalf
  rw [← Basic.mul_assoc]
  rw [Field.inv_mul 2 (by decide)]
  exact Basic.one_mul value

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Topology.Polygon in
/-- A wedge-area squared-norm budget gives one quarter of that budget for the triangle integral. -/
theorem normSq_triangleIntegral_le {vertexCount : Nat}
    (points : Fin vertexCount -> Stokes.PrimitivePoint)
    (triangle : Stokes.OrientedTriangle vertexCount)
    {budget : Coordinate}
    (bounded : Data.Gaussian.Norm.Basic.normSq
      (Stokes.triangleWedgeArea
        (points triangle.first) (points triangle.second) (points triangle.third)) ≤ budget) :
    Data.Gaussian.Norm.Basic.normSq (triangleIntegral points triangle) ≤
      budget * ((1 : Coordinate) / 4) := by
  have halfSquare : Data.Gaussian.Norm.Basic.normSq
      (Data.Gaussian.Field.inv (2 : Basic.Canonical)) = (1 : Coordinate) / 4 := by
    rw [Field.normSq_inv (2 : Basic.Canonical) (by decide +kernel)]
    rw [show Data.Gaussian.Norm.Basic.normSq (2 : Basic.Canonical) = 4 by decide +kernel]
    exact (Fraction.Field.one_mul ((4 : Coordinate)⁻¹)).symm
  unfold triangleIntegral gaussianHalf
  rw [Norm.Basic.normSq_mul, halfSquare]
  exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
    (Fraction.Order.Field.div_nonneg_direct (by decide : (0 : Coordinate) ≤ 1)
      (by decide : (0 : Coordinate) ≤ 4))).trans_eq
    (Fraction.Field.mul_comm _ _)

set_option genInjectivity false in
open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
/-- A fixed finite triangulation certifying decay of one period-pairing residual.

The original boundary area matches the sampled period matrices at every stage; each retained face has a nonnegative
scale and a geometric bound on its triangle integral. -/
structure LocalFaceCertificate {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) where
  /-- The finite number of vertices in the retained triangulation. -/ vertexCount : Nat
  /-- The finite number of oriented faces in the retained triangulation. -/ faceCount : Nat
  /-- The original oriented faces and boundary with their exact cancellation certificate. -/ triangulation :
    Stokes.Triangulation vertexCount faceCount
  /-- The original double-cover face label retained for each triangle. -/ faceLabel : Fin faceCount ->
    Topology.BranchedCover.Double.Attachment.Face
  /-- The original paired primitive data at each retained vertex. -/ primitive : Fin vertexCount -> PrimitiveStream
  /-- The retained boundary area equals the symplectic area of the original sampled period matrices. -/ boundary_matches
    : forall index : Nat,
    Stokes.edgeListArea
        (fun vertex => (primitive vertex).sample index)
        triangulation.boundary =
      Stokes.symplecticBoundaryArea
        (sampledMatrix data.aMatrix index)
        (sampledMatrix data.bMatrix index) row column
  /-- The retained geometric squared-norm scale for each original face. -/ faceScale : Fin faceCount -> Coordinate
  /-- Each retained face scale is nonnegative. -/ faceScale_nonnegative : forall face, 0 <= faceScale face
  /-- Each exact triangle integral satisfies its retained squared-norm bound. -/ face_close : forall face : Fin
    faceCount, forall index : Nat,
    Data.Gaussian.Norm.Basic.normSq
        (triangleIntegral
          (fun vertex => (primitive vertex).sample index)
          (triangulation.faces face)) <=
      Geometric.Basic.quarterRadius (faceScale face) index

constructive_injectivity LocalFaceCertificate

namespace LocalFaceCertificate

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Topology.Polygon in
/-- The finite sum of the retained oriented triangle integrals equals the synchronized residual sample. -/
theorem triangleIntegralSum_eq_residualSample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {row column : Fin genus}
    (certificate : LocalFaceCertificate data row column) (index : Nat) :
    FiniteSum.Fin.sumFin (fun face =>
        triangleIntegral
          (fun vertex => (certificate.primitive vertex).sample index)
          (certificate.triangulation.faces face)) =
      (Periods.Pairing.synchronizedPeriodPairingResidual
        data row column).sample index := by
  let points := fun vertex => (certificate.primitive vertex).sample index
  calc
    FiniteSum.Fin.sumFin (fun face =>
        triangleIntegral points (certificate.triangulation.faces face)) =
        gaussianHalf *
          Stokes.triangleWedgeSum points
            certificate.triangulation.faces := by
      unfold triangleIntegral
      exact FiniteSum.Fin.sumFin_mul_left gaussianHalf _
    _ = gaussianHalf *
          Stokes.edgeListArea points
            certificate.triangulation.boundary := by
      rw [certificate.triangulation.wedgeSum_eq_boundaryArea points]
    _ = gaussianHalf *
          Stokes.symplecticBoundaryArea
            (sampledMatrix data.aMatrix index)
            (sampledMatrix data.bMatrix index) row column := by
      rw [certificate.boundary_matches index]
    _ = gaussianHalf *
          (2 * Stokes.symplecticPairing
            (sampledMatrix data.aMatrix index)
            (sampledMatrix data.bMatrix index) row column) := by
      rw [Stokes.symplecticBoundaryArea_eq_two_mul_pairing]
    _ = Stokes.symplecticPairing
          (sampledMatrix data.aMatrix index)
          (sampledMatrix data.bMatrix index) row column :=
      gaussianHalf_mul_two _
    _ = (Periods.Pairing.synchronizedPeriodPairingResidual
          data row column).sample index := by
      rw [Periods.Pairing.synchronizedPeriodPairingResidual_sample]

open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Periods in
/-- The retained face certificate gives a geometric squared-norm bound on the synchronized residual sample. -/
theorem residualSample_close_zero {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {row column : Fin genus}
    (certificate : LocalFaceCertificate data row column) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        ((Periods.Pairing.synchronizedPeriodPairingResidual
          data row column).sample index) <=
      Geometric.Basic.quarterRadius
        (PeriodMatrix.sumBound certificate.faceScale) index := by
  rw [← certificate.triangleIntegralSum_eq_residualSample index]
  calc
    Data.Gaussian.Norm.Basic.normSq
        (FiniteSum.Fin.sumFin fun face =>
          triangleIntegral
            (fun vertex => (certificate.primitive vertex).sample index)
            (certificate.triangulation.faces face)) <=
        PeriodMatrix.sumBound (fun face =>
          Geometric.Basic.quarterRadius
            (certificate.faceScale face) index) :=
      PeriodMatrix.normSq_sumFin_le_sumBound _ _
        (fun face => certificate.face_close face index)
    _ = Geometric.Basic.quarterRadius
          (PeriodMatrix.sumBound certificate.faceScale) index :=
      PeriodMatrix.sumBound_quarterRadius
        certificate.faceScale index

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Periods in
/-- The original period-pairing residual name is equivalent to the exact zero name.

The retained geometric sample estimates compare the original residual program with the exact zero program and preserve
the original name conversions. -/
def residual_zero {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {row column : Fin genus}
    (certificate : LocalFaceCertificate data row column) :
    NamedEquivalent
      (Periods.Pairing.periodPairingResidual
        data row column).name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name := by
  let source :=
    Periods.Pairing.synchronizedPeriodPairingResidual
      data row column
  let zeroSource :=
    Geometric.GeometricApproximation.exact
      (0 : Basic.Canonical)
  let sourceProgram :=
    Integration.Program.Comparison.geometricRefinementProgram source
  let zeroProgram :=
    Integration.Program.Comparison.geometricRefinementProgram zeroSource
  have scaleNonnegative :
      0 <= PeriodMatrix.sumBound certificate.faceScale :=
    PeriodMatrix.sumBound_nonneg certificate.faceScale
      certificate.faceScale_nonnegative
  have programsEquivalent : NamedEquivalent sourceProgram.output.name
      zeroProgram.output.name := by
    apply Integration.Program.Comparison.refinementProgram_output_equivalent_of_samples_close
      sourceProgram zeroProgram
      (PeriodMatrix.sumBound certificate.faceScale)
      scaleNonnegative
    intro index
    rw [Integration.Program.Comparison.geometricRefinementProgram_integralSample,
      Integration.Program.Comparison.geometricRefinementProgram_integralSample]
    change Data.Gaussian.Norm.Basic.normSq
        (source.sample index - 0) <= _
    rw [Basic.sub_zero]
    simpa only [source] using certificate.residualSample_close_zero index
  exact Equivalence.NamedEquivalent.trans
    (Periods.Pairing.periodPairingResidual_equivalent_synchronized
      data row column)
    (Equivalence.NamedEquivalent.trans
      (Integration.Program.Comparison.geometricNamed_equivalent_geometricRefinementProgram
        source)
      (Equivalence.NamedEquivalent.trans programsEquivalent
        (Equivalence.NamedEquivalent.trans
          (Equivalence.NamedEquivalent.symm
            (Integration.Program.Comparison.geometricNamed_equivalent_geometricRefinementProgram
              zeroSource))
          (by
              simpa only [zeroSource]
                using Geometric.Coherent.Comparison.geometricZero_equivalent_exact))))

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
/-- Close the original accumulated period primitive through its retained zero residual comparison. -/
def closePrimitive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {data : PeriodData curve} {row column : Fin genus}
    (certificate : LocalFaceCertificate data row column) :
    NamedEquivalent
      (Periods.Pairing.periodPairingPrimitiveFinish
        data row column).name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name :=
  Equivalence.NamedEquivalent.trans
    (Periods.Pairing.periodPairingPrimitiveFinish_equivalent_residual
      data row column)
    certificate.residual_zero

end LocalFaceCertificate

/-! ## Refining two-dimensional cut-surface meshes -/

set_option genInjectivity false in
open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
/-- A finite triangulated face sample indexed by the exact period stage and differential pair.

The original boundary matches that stage's sampled symplectic area; every retained triangle has its own nonnegative
squared-norm budget. -/
structure RefiningFaceSample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) (index : Nat) where
  /-- The finite number of vertices in the retained triangulation. -/ vertexCount : Nat
  /-- The finite number of oriented faces in the retained triangulation. -/ faceCount : Nat
  /-- The original oriented faces and boundary with their exact cancellation certificate. -/ triangulation :
    Stokes.Triangulation vertexCount faceCount
  /-- The original double-cover face label retained for each triangle. -/ faceLabel : Fin faceCount ->
    Topology.BranchedCover.Double.Attachment.Face
  /-- The original paired primitive data at each retained vertex. -/ primitive : Fin vertexCount ->
    Stokes.PrimitivePoint
  /-- The retained boundary area equals the symplectic area of the original sampled period matrices. -/ boundary_matches
    :
    Stokes.edgeListArea primitive
        triangulation.boundary =
      Stokes.symplecticBoundaryArea
        (sampledMatrix data.aMatrix index)
        (sampledMatrix data.bMatrix index) row column
  /-- The retained squared-norm budget for each face at this exact sample stage. -/ faceBudget : Fin faceCount ->
    Coordinate
  /-- Each retained face budget is nonnegative. -/ faceBudget_nonnegative : forall face, 0 <= faceBudget face
  /-- Each exact triangle integral satisfies its retained squared-norm bound. -/ face_close : forall face : Fin
    faceCount,
    Data.Gaussian.Norm.Basic.normSq
        (triangleIntegral primitive (triangulation.faces face)) <=
      faceBudget face

constructive_injectivity RefiningFaceSample

namespace RefiningFaceSample

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Topology.Polygon in
/-- Construct a face sample from retained wedge-area bounds on the same triangulation.

Each triangle integral budget is exactly four times the supplied wedge budget times one quarter, preserving the existing
numerical payment and boundary identity. -/
def ofWedge {genus : Nat} {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus} {index : Nat}
    (vertexCount faceCount : Nat)
    (triangulation : Stokes.Triangulation vertexCount faceCount)
    (faceLabel : Fin faceCount -> Topology.BranchedCover.Double.Attachment.Face)
    (primitive : Fin vertexCount -> Stokes.PrimitivePoint)
    (boundary_matches :
      Stokes.edgeListArea primitive triangulation.boundary =
        Stokes.symplecticBoundaryArea
          (sampledMatrix data.aMatrix index) (sampledMatrix data.bMatrix index) row column)
    (wedgeBudget : Fin faceCount -> Coordinate)
    (wedgeBudget_nonnegative : forall face, 0 <= wedgeBudget face)
    (wedge_close : forall face : Fin faceCount,
      Data.Gaussian.Norm.Basic.normSq
        (Stokes.triangleWedgeArea
          (primitive (triangulation.faces face).first)
          (primitive (triangulation.faces face).second)
          (primitive (triangulation.faces face).third)) <= 4 * wedgeBudget face) :
    RefiningFaceSample data row column index where
  vertexCount := vertexCount
  faceCount := faceCount
  triangulation := triangulation
  faceLabel := faceLabel
  primitive := primitive
  boundary_matches := boundary_matches
  faceBudget := fun face => (4 * wedgeBudget face) * ((1 : Coordinate) / 4)
  faceBudget_nonnegative := fun face => Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Coordinate) ≤ 4)
      (wedgeBudget_nonnegative face))
    (Fraction.Order.Field.div_nonneg_direct (by decide : (0 : Coordinate) ≤ 1)
      (by decide : (0 : Coordinate) ≤ 4))
  face_close := fun face =>
    normSq_triangleIntegral_le primitive (triangulation.faces face) (wedge_close face)

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Topology.Polygon in
/-- The finite sum of the retained oriented triangle integrals equals the synchronized residual sample. -/
theorem triangleIntegralSum_eq_residualSample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus} {index : Nat}
    (sample : RefiningFaceSample data row column index) :
    FiniteSum.Fin.sumFin (fun face =>
        triangleIntegral sample.primitive
          (sample.triangulation.faces face)) =
      (Periods.Pairing.synchronizedPeriodPairingResidual
        data row column).sample index := by
  calc
    FiniteSum.Fin.sumFin (fun face =>
        triangleIntegral sample.primitive
          (sample.triangulation.faces face)) =
        gaussianHalf *
          Stokes.triangleWedgeSum sample.primitive
            sample.triangulation.faces := by
      unfold triangleIntegral
      exact FiniteSum.Fin.sumFin_mul_left gaussianHalf _
    _ = gaussianHalf *
          Stokes.edgeListArea sample.primitive
            sample.triangulation.boundary := by
      rw [sample.triangulation.wedgeSum_eq_boundaryArea sample.primitive]
    _ = gaussianHalf *
          Stokes.symplecticBoundaryArea
            (sampledMatrix data.aMatrix index)
            (sampledMatrix data.bMatrix index) row column := by
      rw [sample.boundary_matches]
    _ = gaussianHalf *
          (2 * Stokes.symplecticPairing
            (sampledMatrix data.aMatrix index)
            (sampledMatrix data.bMatrix index) row column) := by
      rw [Stokes.symplecticBoundaryArea_eq_two_mul_pairing]
    _ = Stokes.symplecticPairing
          (sampledMatrix data.aMatrix index)
          (sampledMatrix data.bMatrix index) row column :=
      gaussianHalf_mul_two _
    _ = (Periods.Pairing.synchronizedPeriodPairingResidual
          data row column).sample index := by
      rw [Periods.Pairing.synchronizedPeriodPairingResidual_sample]

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Periods in
/-- The synchronized residual's squared norm is bounded by the retained finite face-budget sum bound. -/
theorem residualSample_le_sumBudget {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus} {index : Nat}
    (sample : RefiningFaceSample data row column index) :
    Data.Gaussian.Norm.Basic.normSq
        ((Periods.Pairing.synchronizedPeriodPairingResidual
          data row column).sample index) <=
      PeriodMatrix.sumBound sample.faceBudget := by
  rw [<- sample.triangleIntegralSum_eq_residualSample]
  exact PeriodMatrix.normSq_sumFin_le_sumBound _ _
    sample.face_close

end RefiningFaceSample

set_option genInjectivity false in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
/-- Stage-dependent finite face samples with one geometric bound on their total budgets.

Each stage retains its own triangulation and primitive points; their exact summed budgets meet the original shared
nonnegative scale. -/
structure RefiningLocalFaceCertificate {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) where
  /-- The retained triangulated face sample at each original natural-number stage. -/ sample : forall index : Nat,
    RefiningFaceSample data row column index
  /-- The shared rational scale controlling the retained finite sample bounds. -/ scale : Coordinate
  /-- The retained global scale is nonnegative. -/ scale_nonnegative : 0 <= scale
  /-- The exact face-budget sum bound meets the retained geometric radius at every stage. -/ summedBudget_close : forall
    index : Nat,
    PeriodMatrix.sumBound (sample index).faceBudget <=
      Geometric.Basic.quarterRadius scale index

constructive_injectivity RefiningLocalFaceCertificate

namespace RefiningLocalFaceCertificate

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
/-- Package the retained face samples and their supplied geometric summed-budget payment. -/
def ofSamples {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (sample : forall index : Nat, RefiningFaceSample data row column index)
    (scale : Coordinate) (nonnegative : 0 <= scale)
    (summedBudget_close : forall index : Nat,
      PeriodMatrix.sumBound (sample index).faceBudget <=
        Geometric.Basic.quarterRadius scale index) :
    RefiningLocalFaceCertificate data row column where
  sample := sample
  scale := scale
  scale_nonnegative := nonnegative
  summedBudget_close := summedBudget_close

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- The retained face certificate gives a geometric squared-norm bound on the synchronized residual sample. -/
theorem residualSample_close_zero {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (certificate : RefiningLocalFaceCertificate data row column)
    (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        ((Periods.Pairing.synchronizedPeriodPairingResidual
          data row column).sample index) <=
      Geometric.Basic.quarterRadius certificate.scale index :=
  (certificate.sample index).residualSample_le_sumBudget.trans
    (certificate.summedBudget_close index)

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- The original period-pairing residual name is equivalent to the exact zero name.

The retained geometric sample estimates compare the original residual program with the exact zero program and preserve
the original name conversions. -/
def residual_zero {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (certificate : RefiningLocalFaceCertificate data row column) :
    NamedEquivalent
      (Periods.Pairing.periodPairingResidual
        data row column).name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name := by
  let source :=
    Periods.Pairing.synchronizedPeriodPairingResidual
      data row column
  let zeroSource :=
    Geometric.GeometricApproximation.exact
      (0 : Basic.Canonical)
  let sourceProgram :=
    Integration.Program.Comparison.geometricRefinementProgram source
  let zeroProgram :=
    Integration.Program.Comparison.geometricRefinementProgram zeroSource
  have programsEquivalent : NamedEquivalent sourceProgram.output.name
      zeroProgram.output.name := by
    apply Integration.Program.Comparison.refinementProgram_output_equivalent_of_samples_close
      sourceProgram zeroProgram certificate.scale certificate.scale_nonnegative
    intro index
    rw [Integration.Program.Comparison.geometricRefinementProgram_integralSample,
      Integration.Program.Comparison.geometricRefinementProgram_integralSample]
    change Data.Gaussian.Norm.Basic.normSq
        (source.sample index - 0) <= _
    rw [Basic.sub_zero]
    simpa only [source] using certificate.residualSample_close_zero index
  exact Equivalence.NamedEquivalent.trans
    (Periods.Pairing.periodPairingResidual_equivalent_synchronized
      data row column)
    (Equivalence.NamedEquivalent.trans
      (Integration.Program.Comparison.geometricNamed_equivalent_geometricRefinementProgram
        source)
      (Equivalence.NamedEquivalent.trans programsEquivalent
        (Equivalence.NamedEquivalent.trans
          (Equivalence.NamedEquivalent.symm
            (Integration.Program.Comparison.geometricNamed_equivalent_geometricRefinementProgram
              zeroSource))
          (by
              simpa only [zeroSource]
                using Geometric.Coherent.Comparison.geometricZero_equivalent_exact))))

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
/-- Close the original accumulated period primitive through its retained zero residual comparison. -/
def closePrimitive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (certificate : RefiningLocalFaceCertificate data row column) :
    NamedEquivalent
      (Periods.Pairing.periodPairingPrimitiveFinish
        data row column).name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name :=
  Equivalence.NamedEquivalent.trans
    (Periods.Pairing.periodPairingPrimitiveFinish_equivalent_residual
      data row column)
    certificate.residual_zero

end RefiningLocalFaceCertificate

set_option genInjectivity false in
open Purelib.Curves.Hyperelliptic in
/-- A refining local-face certificate for every strictly ordered differential pair.

The original row and column indices remain attached to each certificate; diagonal and reversed pairs are supplied by the
Stokes closure laws. -/
structure UpperRefiningLocalFaceReduction {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (data : PeriodData curve) where
  /-- The retained face certificate for the original strictly ordered differential pair. -/ certificate : forall row
    column : Fin genus,
    row.val < column.val -> RefiningLocalFaceCertificate data row column

constructive_injectivity UpperRefiningLocalFaceReduction

namespace UpperRefiningLocalFaceReduction

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Periods in
/-- Construct strict-upper face reductions from the supplied pair-indexed samples and shared geometric budget.

Each original pair keeps its own stagewise triangulation while using the exact common scale and summed-budget bound. -/
def ofSamples {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    (sample : forall (row column : Fin genus) (index : Nat),
      RefiningFaceSample data row column index)
    (scale : Coordinate) (nonnegative : 0 <= scale)
    (summedBudget_close : forall (row column : Fin genus) (index : Nat),
      PeriodMatrix.sumBound (sample row column index).faceBudget <=
        Geometric.Basic.quarterRadius scale index) :
    UpperRefiningLocalFaceReduction data where
  certificate := fun row column _ =>
    RefiningLocalFaceCertificate.ofSamples (fun index => sample row column index)
      scale nonnegative (fun index => summedBudget_close row column index)

open Purelib.Curves.Hyperelliptic
/-- Close each strict-upper primitive using its retained pair-specific certificate. -/
def toUpperTriangularStokesClosure {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    (reduction : UpperRefiningLocalFaceReduction data) :
    Periods.Pairing.UpperTriangularStokesClosure data where
  closed_of_lt := by
    intro row column less
    exact (reduction.certificate row column less).closePrimitive

/-- Close the original period primitives using the retained reduction certificates. -/
def toStokesClosure {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    (reduction : UpperRefiningLocalFaceReduction data) :
    Periods.Pairing.StokesClosure data :=
  reduction.toUpperTriangularStokesClosure.toStokesClosure

/-- Use the supplied certificate for the sole strict-upper pair in genus two. -/
def genusTwo {curve : Basic.HyperellipticCurve 2} (data : PeriodData curve)
    (certificate : RefiningLocalFaceCertificate data 0 1) :
    UpperRefiningLocalFaceReduction data where
  certificate := by
    intro row column less
    have rowZero : row = (0 : Fin 2) := by
      apply Fin.ext
      change row.val = 0
      exact Nat.eq_zero_of_le_zero
        (Nat.le_of_lt_succ
          (Nat.lt_of_lt_of_le less (Nat.le_of_lt_succ column.isLt)))
    have columnOne : column = (1 : Fin 2) := by
      apply Fin.ext
      change column.val = 1
      exact Nat.le_antisymm (Nat.le_of_lt_succ column.isLt)
        (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le row.val)) less)
    subst row
    subst column
    exact certificate

end UpperRefiningLocalFaceReduction

/-! ## Canonical handlewise decomposition

The arbitrary triangulation interface above is the geometric interface used
for an actual refining cut-surface mesh.  Separately, the standard
symplectic boundary has a useful exact algebraic decomposition: each handle
commutator `0, a, a+b, b` splits along the diagonal `0 -- (a+b)`.  Its two
triangle values need not tend to zero individually; in general they do not.
The certificate below therefore asks only for a shrinking bound on the sum
over the complete finite handle bank.  It exposes the exact terms whose
cancellation is being certified without falsely presenting a fixed handle
polygon as a refining local surface mesh. -/

section
open Purelib.Data.Gaussian
open Purelib.Topology.Polygon
/-- Half the wedge area of the first oriented triangle in the retained handle parallelogram. -/
def firstHandleTriangleIntegral
    (a b : Stokes.PrimitivePoint) :
    Basic.Canonical :=
  gaussianHalf *
    Stokes.triangleWedgeArea
      Stokes.PrimitivePoint.zero a (a.add b)

/-- Half the wedge area of the second oriented triangle in the retained handle parallelogram. -/
def secondHandleTriangleIntegral
    (a b : Stokes.PrimitivePoint) :
    Basic.Canonical :=
  gaussianHalf *
    Stokes.triangleWedgeArea
      Stokes.PrimitivePoint.zero (a.add b) b

end

open Purelib.Topology.Polygon in
/-- The two retained handle triangle integrals sum to the signed symplectic minor. -/
theorem handleTriangleIntegral_add
    (a b : Stokes.PrimitivePoint) :
    firstHandleTriangleIntegral a b + secondHandleTriangleIntegral a b =
      a.left * b.right - b.left * a.right := by
  have firstWedge :
      Stokes.triangleWedgeArea
          Stokes.PrimitivePoint.zero a (a.add b) =
        a.left * b.right - b.left * a.right := by
    unfold Stokes.triangleWedgeArea
      Stokes.PrimitivePoint.zero
      Stokes.PrimitivePoint.add
    ring1
  have secondWedge :
      Stokes.triangleWedgeArea
          Stokes.PrimitivePoint.zero (a.add b) b =
        a.left * b.right - b.left * a.right := by
    unfold Stokes.triangleWedgeArea
      Stokes.PrimitivePoint.zero
      Stokes.PrimitivePoint.add
    ring1
  rw [firstHandleTriangleIntegral, secondHandleTriangleIntegral,
    firstWedge, secondWedge]
  calc
    gaussianHalf * (a.left * b.right - b.left * a.right) +
          gaussianHalf * (a.left * b.right - b.left * a.right) =
        gaussianHalf *
          (2 * (a.left * b.right - b.left * a.right)) := by ring1
    _ = a.left * b.right - b.left * a.right :=
      gaussianHalf_mul_two _

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
/-- Select one of the two original handle triangle integrals at the retained sample stage. -/
def handleTriangleIntegral {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (data : PeriodData curve)
    (row column cycle : Fin genus) (face : Fin 2) (index : Nat) :
    Basic.Canonical :=
  let a := Stokes.aIncrement
    (sampledMatrix data.aMatrix index) row column cycle
  let b := Stokes.bIncrement
    (sampledMatrix data.bMatrix index) row column cycle
  if face = 0 then firstHandleTriangleIntegral a b
  else secondHandleTriangleIntegral a b

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- The two-face sum for a retained cycle equals its signed period-matrix minor. -/
theorem handleTriangleSum_eq_pairingTerm {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (data : PeriodData curve)
    (row column cycle : Fin genus) (index : Nat) :
    FiniteSum.Fin.sumFin (fun face : Fin 2 =>
        handleTriangleIntegral data row column cycle face index) =
      sampledMatrix data.aMatrix index row cycle *
          sampledMatrix data.bMatrix index column cycle -
        sampledMatrix data.bMatrix index row cycle *
          sampledMatrix data.aMatrix index column cycle := by
  rw [FiniteSum.Fin.sumFin_succ]
  change handleTriangleIntegral data row column cycle 0 index +
      FiniteSum.Fin.sumFin (fun face : Fin 1 =>
        handleTriangleIntegral data row column cycle face.succ index) = _
  rw [FiniteSum.Fin.sumFin_succ]
  change handleTriangleIntegral data row column cycle 0 index +
      (handleTriangleIntegral data row column cycle 1 index + 0) = _
  rw [Basic.add_zero]
  unfold handleTriangleIntegral
  rw [if_pos (show (0 : Fin 2) = 0 from rfl),
    if_neg (show (1 : Fin 2) ≠ 0 by decide)]
  exact handleTriangleIntegral_add _ _

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic in
open Purelib.Topology.Polygon in
/-- Summing both faces over the original cycles gives the synchronized residual sample. -/
theorem handleTriangleSum_eq_residualSample {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (data : PeriodData curve)
    (row column : Fin genus) (index : Nat) :
    FiniteSum.Fin.sumFin (fun cycle =>
        FiniteSum.Fin.sumFin (fun face : Fin 2 =>
          handleTriangleIntegral data row column cycle face index)) =
      (Periods.Pairing.synchronizedPeriodPairingResidual
        data row column).sample index := by
  rw [Periods.Pairing.synchronizedPeriodPairingResidual_sample]
  unfold Stokes.symplecticPairing
  exact FiniteSum.Fin.sumFin_congr
    (fun cycle => handleTriangleSum_eq_pairingTerm
      data row column cycle index)

set_option genInjectivity false in
open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- A geometric squared-norm bound on the retained total handle-triangle sum.

The original differential pair and period data determine every sample, with one explicit nonnegative scale for the full
finite sum. -/
structure HandleFaceCertificate {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) where
  /-- The shared rational scale controlling the retained finite sample bounds. -/ scale : Coordinate
  /-- The retained global scale is nonnegative. -/ scale_nonnegative : 0 <= scale
  /-- The exact finite handle-triangle sum satisfies the retained geometric squared-norm bound. -/ total_close : forall
    index : Nat,
    Data.Gaussian.Norm.Basic.normSq
        (FiniteSum.Fin.sumFin fun cycle =>
          FiniteSum.Fin.sumFin fun face : Fin 2 =>
            handleTriangleIntegral data row column cycle face index) <=
      Geometric.Basic.quarterRadius scale index

constructive_injectivity HandleFaceCertificate

namespace HandleFaceCertificate

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- The retained face certificate gives a geometric squared-norm bound on the synchronized residual sample. -/
theorem residualSample_close_zero {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (certificate : HandleFaceCertificate data row column) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        ((Periods.Pairing.synchronizedPeriodPairingResidual
          data row column).sample index) <=
      Geometric.Basic.quarterRadius certificate.scale index := by
  rw [<- handleTriangleSum_eq_residualSample data row column index]
  exact certificate.total_close index

open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Combine retained per-cycle triangle bounds with the supplied genus-squared payment.

The finite Gaussian sum estimate preserves both count factors, and the supplied inequality pays them into the original
global scale. -/
def ofCycleBound {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (scale perCycle : Coordinate) (nonnegative : 0 <= scale)
    (count_paid : (genus : Coordinate) * ((genus : Coordinate) * perCycle) <= scale)
    (cycleClose : forall (cycle : Fin genus) (index : Nat),
      Data.Gaussian.Norm.Basic.normSq
          (FiniteSum.Fin.sumFin fun face : Fin 2 =>
            handleTriangleIntegral data row column cycle face index) <=
        Geometric.Basic.quarterRadius perCycle index) :
    HandleFaceCertificate data row column where
  scale := scale
  scale_nonnegative := nonnegative
  total_close := by
    intro index
    have bound := Norm.Sum.Indexed.normSq_sumFin_le
      (fun cycle : Fin genus =>
        FiniteSum.Fin.sumFin fun face : Fin 2 =>
          handleTriangleIntegral data row column cycle face index)
      (Geometric.Basic.quarterRadius perCycle index)
      (fun cycle => cycleClose cycle index)
    refine bound.trans ?_
    have powerNonnegative : 0 <= (1 / 4 : Coordinate) ^ index :=
      Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) index
    calc
      ((genus : Coordinate))^2 * Geometric.Basic.quarterRadius perCycle index
          = ((genus : Coordinate) * ((genus : Coordinate) * perCycle)) * ((1 / 4 : Coordinate) ^ index) := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1
      _ <= scale * ((1 / 4 : Coordinate) ^ index) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct count_paid powerNonnegative
      _ = Geometric.Basic.quarterRadius scale index := by
        rw [Geometric.Basic.quarterRadius_eq_mul_pow]

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- Construct the handle certificate from retained signed period-minor bounds and the same genus-squared payment. -/
def ofCycleMinor {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (scale perCycle : Coordinate) (nonnegative : 0 <= scale)
    (count_paid : (genus : Coordinate) * ((genus : Coordinate) * perCycle) <= scale)
    (minorClose : forall (cycle : Fin genus) (index : Nat),
      Data.Gaussian.Norm.Basic.normSq
          (sampledMatrix data.aMatrix index row cycle * sampledMatrix data.bMatrix index column cycle -
            sampledMatrix data.bMatrix index row cycle * sampledMatrix data.aMatrix index column cycle) <=
        Geometric.Basic.quarterRadius perCycle index) :
    HandleFaceCertificate data row column :=
  ofCycleBound scale perCycle nonnegative count_paid (fun cycle index => by
    rw [handleTriangleSum_eq_pairingTerm]
    exact minorClose cycle index)

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- The original period-pairing residual name is equivalent to the exact zero name.

The retained geometric sample estimates compare the original residual program with the exact zero program and preserve
the original name conversions. -/
def residual_zero {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (certificate : HandleFaceCertificate data row column) :
    NamedEquivalent
      (Periods.Pairing.periodPairingResidual
        data row column).name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name := by
  let source :=
    Periods.Pairing.synchronizedPeriodPairingResidual
      data row column
  let zeroSource :=
    Geometric.GeometricApproximation.exact
      (0 : Basic.Canonical)
  let sourceProgram :=
    Integration.Program.Comparison.geometricRefinementProgram source
  let zeroProgram :=
    Integration.Program.Comparison.geometricRefinementProgram zeroSource
  have programsEquivalent : NamedEquivalent sourceProgram.output.name
      zeroProgram.output.name := by
    apply Integration.Program.Comparison.refinementProgram_output_equivalent_of_samples_close
      sourceProgram zeroProgram certificate.scale
        certificate.scale_nonnegative
    intro index
    rw [Integration.Program.Comparison.geometricRefinementProgram_integralSample,
      Integration.Program.Comparison.geometricRefinementProgram_integralSample]
    change Data.Gaussian.Norm.Basic.normSq
        (source.sample index - 0) <= _
    rw [Basic.sub_zero]
    simpa only [source] using certificate.residualSample_close_zero index
  exact Equivalence.NamedEquivalent.trans
    (Periods.Pairing.periodPairingResidual_equivalent_synchronized
      data row column)
    (Equivalence.NamedEquivalent.trans
      (Integration.Program.Comparison.geometricNamed_equivalent_geometricRefinementProgram
        source)
      (Equivalence.NamedEquivalent.trans programsEquivalent
        (Equivalence.NamedEquivalent.trans
          (Equivalence.NamedEquivalent.symm
            (Integration.Program.Comparison.geometricNamed_equivalent_geometricRefinementProgram
              zeroSource))
          (by
              simpa only [zeroSource]
                using Geometric.Coherent.Comparison.geometricZero_equivalent_exact))))

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
/-- Close the original accumulated period primitive through its retained zero residual comparison. -/
def closePrimitive {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    {row column : Fin genus}
    (certificate : HandleFaceCertificate data row column) :
    NamedEquivalent
      (Periods.Pairing.periodPairingPrimitiveFinish
        data row column).name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name :=
  Equivalence.NamedEquivalent.trans
    (Periods.Pairing.periodPairingPrimitiveFinish_equivalent_residual
      data row column)
    certificate.residual_zero

end HandleFaceCertificate

set_option genInjectivity false in
open Purelib.Curves.Hyperelliptic in
/-- A retained handle-face certificate for every strictly ordered differential pair.

The original period data and pair indices determine the finite handle samples used to close the upper-triangular
primitives. -/
structure UpperHandleFaceReduction {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (data : PeriodData curve) where
  /-- The retained face certificate for the original strictly ordered differential pair. -/ certificate : forall row
    column : Fin genus,
    row.val < column.val -> HandleFaceCertificate data row column

constructive_injectivity UpperHandleFaceReduction

namespace UpperHandleFaceReduction

section
open Purelib.Curves.Hyperelliptic
/-- Close each strict-upper primitive using its retained pair-specific certificate. -/
def toUpperTriangularStokesClosure {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    (reduction : UpperHandleFaceReduction data) :
    Periods.Pairing.UpperTriangularStokesClosure data where
  closed_of_lt := by
    intro row column less
    exact (reduction.certificate row column less).closePrimitive

/-- Close the original period primitives using the retained reduction certificates. -/
def toStokesClosure {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    (reduction : UpperHandleFaceReduction data) :
    Periods.Pairing.StokesClosure data :=
  reduction.toUpperTriangularStokesClosure.toStokesClosure

/-- Use the supplied certificate for the sole strict-upper pair in genus two. -/
def genusTwo {curve : Basic.HyperellipticCurve 2} (data : PeriodData curve)
    (certificate : HandleFaceCertificate data 0 1) :
    UpperHandleFaceReduction data where
  certificate := by
    intro row column less
    have rowZero : row = (0 : Fin 2) := by
      apply Fin.ext
      change row.val = 0
      exact Nat.eq_zero_of_le_zero
        (Nat.le_of_lt_succ
          (Nat.lt_of_lt_of_le less (Nat.le_of_lt_succ column.isLt)))
    have columnOne : column = (1 : Fin 2) := by
      apply Fin.ext
      change column.val = 1
      exact Nat.le_antisymm (Nat.le_of_lt_succ column.isLt)
        (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le row.val)) less)
    subst row
    subst column
    exact certificate

end

open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- Construct strict-upper handle certificates from the supplied per-cycle triangle bounds and count payment. -/
def ofCycleBounds {genus : Nat} {curve : Basic.HyperellipticCurve genus} (data : PeriodData curve)
    (scale perCycle : Coordinate) (nonnegative : 0 <= scale)
    (count_paid : (genus : Coordinate) * ((genus : Coordinate) * perCycle) <= scale)
    (cycleClose : forall (row column : Fin genus)
      (cycle : Fin genus) (index : Nat),
      Data.Gaussian.Norm.Basic.normSq
          (FiniteSum.Fin.sumFin fun face : Fin 2 =>
            handleTriangleIntegral data row column cycle face index) <=
        Geometric.Basic.quarterRadius perCycle index) :
    UpperHandleFaceReduction data where
  certificate := fun row column _ =>
    HandleFaceCertificate.ofCycleBound scale perCycle nonnegative count_paid
      (fun cycle index => cycleClose row column cycle index)

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- Construct strict-upper handle certificates from the supplied signed-minor bounds and count payment. -/
def ofCycleMinors {genus : Nat} {curve : Basic.HyperellipticCurve genus} (data : PeriodData curve)
    (scale perCycle : Coordinate) (nonnegative : 0 <= scale)
    (count_paid : (genus : Coordinate) * ((genus : Coordinate) * perCycle) <= scale)
    (minorClose : forall (row column : Fin genus) (cycle : Fin genus) (index : Nat),
      Data.Gaussian.Norm.Basic.normSq
          (sampledMatrix data.aMatrix index row cycle * sampledMatrix data.bMatrix index column cycle -
            sampledMatrix data.bMatrix index row cycle * sampledMatrix data.aMatrix index column cycle) <=
        Geometric.Basic.quarterRadius perCycle index) :
    UpperHandleFaceReduction data where
  certificate := fun row column _ =>
    HandleFaceCertificate.ofCycleMinor scale perCycle nonnegative count_paid
      (fun cycle index => minorClose row column cycle index)

end UpperHandleFaceReduction

set_option genInjectivity false in
open Purelib.Curves.Hyperelliptic in
/-- A fixed local-face certificate for every strictly ordered differential pair.

Each original pair keeps its finite triangulation, primitive streams and geometric face estimates. -/
structure UpperLocalFaceReduction {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} (data : PeriodData curve) where
  /-- The retained face certificate for the original strictly ordered differential pair. -/ certificate : forall row
    column : Fin genus,
    row.val < column.val -> LocalFaceCertificate data row column

constructive_injectivity UpperLocalFaceReduction

namespace UpperLocalFaceReduction

open Purelib.Curves.Hyperelliptic
/-- Close each strict-upper primitive using its retained pair-specific certificate. -/
def toUpperTriangularStokesClosure {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    (reduction : UpperLocalFaceReduction data) :
    Periods.Pairing.UpperTriangularStokesClosure data where
  closed_of_lt := by
    intro row column less
    exact (reduction.certificate row column less).closePrimitive

/-- Close the original period primitives using the retained reduction certificates. -/
def toStokesClosure {genus : Nat}
    {curve : Basic.HyperellipticCurve genus} {data : PeriodData curve}
    (reduction : UpperLocalFaceReduction data) :
    Periods.Pairing.StokesClosure data :=
  reduction.toUpperTriangularStokesClosure.toStokesClosure

/-- Use the supplied certificate for the sole strict-upper pair in genus two. -/
def genusTwo {curve : Basic.HyperellipticCurve 2} (data : PeriodData curve)
    (certificate : LocalFaceCertificate data 0 1) :
    UpperLocalFaceReduction data where
  certificate := by
    intro row column less
    have rowZero : row = (0 : Fin 2) := by
      apply Fin.ext
      change row.val = 0
      exact Nat.eq_zero_of_le_zero
        (Nat.le_of_lt_succ
          (Nat.lt_of_lt_of_le less (Nat.le_of_lt_succ column.isLt)))
    have columnOne : column = (1 : Fin 2) := by
      apply Fin.ext
      change column.val = 1
      exact Nat.le_antisymm (Nat.le_of_lt_succ column.isLt)
        (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le row.val)) less)
    subst row
    subst column
    exact certificate

end UpperLocalFaceReduction

/-! ## Exact finite-program surface comparison -/

open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Integration.Program in
open Purelib.Riemann.Topology in
/-- The exact refinement program of the retained cellular boundary and surface-wedge sum. -/
def cellularBoundaryProgram {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve)
    (pairs : CellularEdgePairs curve) (row column : Fin genus)
    (refinement : Nat) : RefinementProgram :=
  Gaussian.Basic.RefinementProgram.ofCoherentNamed
    (Name.Coherent.CoherentNamed.add pairs.boundarySum
      (surfaceWedgeSum geometry row column refinement))

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Topology in
/-- Close a period primitive from a retained geometric sample comparison with its cellular boundary program.

The original comparison scale pays the difference between the two executable programs; cancellation of the retained
boundary pairs and wedge charts supplies exact zero. -/
def closePrimitive_of_cellularProgramComparison {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    (geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve)
    (schedules :
      PreparedCycleModels.PeriodSchedules curve geometry)
    (row column : Fin genus) (refinement : Nat)
    (pairs : CellularEdgePairs curve) (bridgeScale : Coordinate)
    (bridgeScale_nonnegative : 0 <= bridgeScale)
    (sample_close : forall index : Nat,
      Data.Gaussian.Norm.Basic.normSq
          (((Periods.Pairing.periodPairingCycleSumProgram
            schedules.toPeriodData row column).model index).integralSample -
          ((cellularBoundaryProgram geometry pairs row column refinement).model
            index).integralSample) <=
        Geometric.Basic.quarterRadius bridgeScale index) :
    NamedEquivalent
      (Periods.Pairing.periodPairingPrimitiveFinish
        schedules.toPeriodData row column).name
      (Name.Coherent.CoherentNamed.Coherence.exact 0).name := by
  let paired := pairs.boundarySum
  let wedges := surfaceWedgeSum geometry row column refinement
  let total := Name.Coherent.CoherentNamed.add paired wedges
  let boundaryProgram := cellularBoundaryProgram geometry pairs row column
    refinement
  let zero := Name.Coherent.CoherentNamed.Coherence.exact 0
  have programsEquivalent : NamedEquivalent
      (Periods.Pairing.periodPairingCycleSumProgram
        schedules.toPeriodData row column).output.name
      boundaryProgram.output.name := by
    apply Integration.Program.Comparison.refinementProgram_output_equivalent_of_samples_close
      _ _ bridgeScale bridgeScale_nonnegative
    intro index
    simpa only [boundaryProgram] using sample_close index
  have boundaryProgramEquivalent : NamedEquivalent total.name
      boundaryProgram.output.name := by
    simpa only [total, boundaryProgram, cellularBoundaryProgram, paired,
      wedges] using
      Integration.Program.Comparison.ofCoherentNamed_output_equivalent total
  have pairedZero : NamedEquivalent paired.name zero.name := by
    simpa only [paired, zero] using pairs.boundarySum_zero
  have wedgesZero : NamedEquivalent wedges.name zero.name := by
    simpa only [wedges, zero] using
      surfaceWedgeSum_zero geometry row column refinement
  have totalZero : NamedEquivalent total.name zero.name :=
    Equivalence.NamedEquivalent.trans
      (Name.Coherent.Arithmetic.Sum.Congruence.coherentAdd_respects
        paired zero wedges zero pairedZero wedgesZero)
      (Arithmetic.Add.coherentAdd_zero_right zero)
  exact Equivalence.NamedEquivalent.trans
    (Periods.Pairing.periodPairingPrimitiveFinish_equivalent_program
      schedules.toPeriodData row column)
    (Equivalence.NamedEquivalent.trans programsEquivalent
      (Equivalence.NamedEquivalent.trans
        (Equivalence.NamedEquivalent.symm
          boundaryProgramEquivalent)
        totalZero))

set_option genInjectivity false in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Topology in
/-- Geometric sample comparisons between original period and cellular boundary programs.

Each differential pair retains its stage, cellular edge pairs and nonnegative comparison scale, with bounds on the exact
program samples. -/
structure CellularProgramBoundaryReduction {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      PreparedCycleModels.PeriodSchedules curve geometry) where
  /-- The retained surface refinement stage for the original differential pair. -/ refinement : Fin genus -> Fin genus
    -> Nat
  /-- The original indexed family of paired boundary programs. -/ edgePairs : forall _row _column : Fin genus,
    CellularEdgePairs curve
  /-- The retained rational scale for comparing the original period and boundary programs. -/ bridgeScale : Fin genus ->
    Fin genus -> Coordinate
  /-- The retained program-comparison scale is nonnegative. -/ bridgeScale_nonnegative : forall row column,
    0 <= bridgeScale row column
  /-- The exact difference of the retained program samples meets its original geometric bound. -/ sample_close : forall
    row column : Fin genus, forall index : Nat,
    Data.Gaussian.Norm.Basic.normSq
        (((Periods.Pairing.periodPairingCycleSumProgram
          schedules.toPeriodData row column).model index).integralSample -
        ((cellularBoundaryProgram geometry (edgePairs row column) row column
          (refinement row column)).model index).integralSample) <=
      Geometric.Basic.quarterRadius (bridgeScale row column) index

constructive_injectivity CellularProgramBoundaryReduction

namespace CellularProgramBoundaryReduction

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Topology in
/-- Construct a cellular program reduction with zero comparison scale from exact sample identities. -/
def ofSamplesEq {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      PreparedCycleModels.PeriodSchedules curve geometry}
    (refinement : Fin genus -> Fin genus -> Nat)
    (edgePairs : forall _row _column : Fin genus, CellularEdgePairs curve)
    (sample_eq : forall row column : Fin genus, forall index : Nat,
      ((Periods.Pairing.periodPairingCycleSumProgram
        schedules.toPeriodData row column).model index).integralSample =
      ((cellularBoundaryProgram geometry (edgePairs row column) row column
        (refinement row column)).model index).integralSample) :
    CellularProgramBoundaryReduction schedules where
  refinement := refinement
  edgePairs := edgePairs
  bridgeScale := fun _ _ => 0
  bridgeScale_nonnegative := fun _ _ => by decide
  sample_close := by
    intro row column index
    rw [sample_eq row column index,
      Basic.sub_self,
      Norm.Basic.normSq_zero]
    exact Geometric.Basic.quarterRadius_nonneg (by decide) index

open Purelib in
open Purelib.Approximation.Gaussian in
open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Topology in
/-- Transport the retained program sample comparisons to the corresponding named boundary reduction. -/
def toCellularBoundaryReduction {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : CellularProgramBoundaryReduction schedules) :
    CellularBoundaryReduction schedules where
  refinement := reduction.refinement
  edgePairs := reduction.edgePairs
  boundary_eq_surface := by
    intro row column
    let total := Name.Coherent.CoherentNamed.add
      (reduction.edgePairs row column).boundarySum
      (surfaceWedgeSum geometry row column
        (reduction.refinement row column))
    let boundaryProgram := cellularBoundaryProgram geometry
      (reduction.edgePairs row column) row column
        (reduction.refinement row column)
    have programsEquivalent : NamedEquivalent
        (Periods.Pairing.periodPairingCycleSumProgram
          schedules.toPeriodData row column).output.name
        boundaryProgram.output.name := by
      apply Integration.Program.Comparison.refinementProgram_output_equivalent_of_samples_close
        _ _ (reduction.bridgeScale row column)
          (reduction.bridgeScale_nonnegative row column)
      intro index
      simpa only [boundaryProgram] using reduction.sample_close row column index
    have boundaryProgramEquivalent : NamedEquivalent total.name
        boundaryProgram.output.name := by
      simpa only [total, boundaryProgram, cellularBoundaryProgram] using
        Integration.Program.Comparison.ofCoherentNamed_output_equivalent total
    exact Equivalence.NamedEquivalent.trans
      (Periods.Pairing.periodPairingPrimitiveFinish_equivalent_program
        schedules.toPeriodData row column)
      (Equivalence.NamedEquivalent.trans programsEquivalent
        (Equivalence.NamedEquivalent.symm
          boundaryProgramEquivalent))

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Topology in
/-- Close the original period primitives using the retained reduction certificates. -/
def toStokesClosure {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : CellularProgramBoundaryReduction schedules) :
    Periods.Pairing.StokesClosure
      schedules.toPeriodData :=
  reduction.toCellularBoundaryReduction.toStokesClosure

end CellularProgramBoundaryReduction

/-! ## Independent upper-triangular surface comparisons -/

set_option genInjectivity false in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Topology in
/-- Cellular program sample comparisons for strictly ordered differential pairs.

All stages, edge-pair families and scales retain the original strict-order witness and exact period programs. -/
structure UpperCellularProgramBoundaryReduction {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      PreparedCycleModels.PeriodSchedules curve geometry) where
  /-- The retained surface refinement stage for the original differential pair. -/ refinement : forall row column : Fin
    genus, row.val < column.val -> Nat
  /-- The original indexed family of paired boundary programs. -/ edgePairs : forall row column : Fin genus,
    (less : row.val < column.val) -> CellularEdgePairs curve
  /-- The retained rational scale for comparing the original period and boundary programs. -/ bridgeScale : forall row
    column : Fin genus,
    row.val < column.val -> Coordinate
  /-- The retained program-comparison scale is nonnegative. -/ bridgeScale_nonnegative : forall row column : Fin genus,
    (less : row.val < column.val) -> 0 <= bridgeScale row column less
  /-- The exact difference of the retained program samples meets its original geometric bound. -/ sample_close : forall
    row column : Fin genus,
    (less : row.val < column.val) -> forall index : Nat,
    Data.Gaussian.Norm.Basic.normSq
        (((Periods.Pairing.periodPairingCycleSumProgram
          schedules.toPeriodData row column).model index).integralSample -
        ((cellularBoundaryProgram geometry (edgePairs row column less)
          row column (refinement row column less)).model index).integralSample) <=
      Geometric.Basic.quarterRadius
        (bridgeScale row column less) index

constructive_injectivity UpperCellularProgramBoundaryReduction

namespace UpperCellularProgramBoundaryReduction

section
open Purelib.Curves.Hyperelliptic
open Purelib.Riemann.Topology
/-- Close each strict-upper primitive using its retained pair-specific certificate. -/
def toUpperTriangularStokesClosure {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : UpperCellularProgramBoundaryReduction schedules) :
    Periods.Pairing.UpperTriangularStokesClosure
      schedules.toPeriodData where
  closed_of_lt := by
    intro row column less
    exact closePrimitive_of_cellularProgramComparison geometry schedules
      row column (reduction.refinement row column less)
      (reduction.edgePairs row column less)
      (reduction.bridgeScale row column less)
      (reduction.bridgeScale_nonnegative row column less)
      (reduction.sample_close row column less)

/-- Close the original period primitives using the retained reduction certificates. -/
def toStokesClosure {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    {schedules :
      PreparedCycleModels.PeriodSchedules curve geometry}
    (reduction : UpperCellularProgramBoundaryReduction schedules) :
    Periods.Pairing.StokesClosure schedules.toPeriodData :=
  reduction.toUpperTriangularStokesClosure.toStokesClosure

end

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Riemann.Topology in
/-- Use the supplied certificate for the sole strict-upper pair in genus two. -/
def genusTwo {curve : Basic.HyperellipticCurve 2}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      PreparedCycleModels.PeriodSchedules curve geometry)
    (refinement : Nat) (pairs : CellularEdgePairs curve)
    (bridgeScale : Coordinate) (bridgeScale_nonnegative : 0 <= bridgeScale)
    (sample_close : forall index : Nat,
      Data.Gaussian.Norm.Basic.normSq
          (((Periods.Pairing.periodPairingCycleSumProgram
            schedules.toPeriodData 0 1).model index).integralSample -
          ((cellularBoundaryProgram geometry pairs 0 1 refinement).model
            index).integralSample) <=
        Geometric.Basic.quarterRadius bridgeScale index) :
    UpperCellularProgramBoundaryReduction schedules where
  refinement := by
    intro row column less
    exact refinement
  edgePairs := by
    intro row column less
    exact pairs
  bridgeScale := by
    intro row column less
    exact bridgeScale
  bridgeScale_nonnegative := by
    intro row column less
    exact bridgeScale_nonnegative
  sample_close := by
    intro row column less index
    have rowZero : row = (0 : Fin 2) := by
      apply Fin.ext
      change row.val = 0
      exact Nat.eq_zero_of_le_zero
        (Nat.le_of_lt_succ
          (Nat.lt_of_lt_of_le less (Nat.le_of_lt_succ column.isLt)))
    have columnOne : column = (1 : Fin 2) := by
      apply Fin.ext
      change column.val = 1
      exact Nat.le_antisymm (Nat.le_of_lt_succ column.isLt)
        (Nat.le_trans (Nat.succ_le_succ (Nat.zero_le row.val)) less)
    subst row
    subst column
    exact sample_close index

end UpperCellularProgramBoundaryReduction

open Purelib.Curves.Hyperelliptic
open Purelib.Riemann.Topology
/-- The same named boundary reduction on the original compatible period schedules. -/
abbrev CompatibleBoundaryReduction {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      PreparedCycleModels.CompatiblePeriodSchedules curve
        geometry) :=
  BoundaryReduction schedules.toPeriodSchedules

/-- The same cellular boundary reduction on the original compatible period schedules. -/
abbrev CompatibleCellularBoundaryReduction {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      PreparedCycleModels.CompatiblePeriodSchedules curve
        geometry) :=
  CellularBoundaryReduction schedules.toPeriodSchedules

/-- The same program-sample boundary reduction on the original compatible period schedules. -/
abbrev CompatibleCellularProgramBoundaryReduction {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      PreparedCycleModels.CompatiblePeriodSchedules curve
        geometry) :=
  CellularProgramBoundaryReduction schedules.toPeriodSchedules

/-- The same strict-upper program-sample reduction on the original compatible period schedules. -/
abbrev CompatibleUpperCellularProgramBoundaryReduction {genus : Nat}
    {curve : Basic.HyperellipticCurve genus}
    {geometry :
      PreparedCycleModels.SymplecticCycleSchedule curve}
    (schedules :
      PreparedCycleModels.CompatiblePeriodSchedules curve
        geometry) :=
  UpperCellularProgramBoundaryReduction schedules.toPeriodSchedules

end Purelib.Riemann.Topology.PreparedStokes
