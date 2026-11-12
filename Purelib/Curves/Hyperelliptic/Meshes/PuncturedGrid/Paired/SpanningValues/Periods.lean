module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningValues
public import Purelib.Riemann.Periods.WeightedPeriodNames
public import Purelib.Data.Vector.Split
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.WeightedPeriods
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction

/-! # Actual period combinations on retained spanning coordinates

The two original integer coefficient vectors determine the actual A/full-B
arithmetic combination. Existing weighted-period coefficients pay their
true magnitudes, including zero weights; no standard-coordinate, cycle,
root or frame identity follows from this numerical combination.
-/

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank ClosedCoordinates)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows (BasisCoordinates)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_split sumFin_add)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Periods
open Purelib.Riemann.Periods.PeriodMatrix (geometricNamed)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree}
    {base : FramedPuncturedGrid curve branches higher} {lifted : LiftedPuncturedGrid base}
    {bank : BasedBranchBank lifted} {sheet : Fin 2} {ordered : BasedBranchBank.Ordered bank sheet}
    {paired : OrderedBranchPairs.Ordered.Paired ordered} {prepared : Prepared paired}
    {cut : CutBank prepared} {word : List (OrientedEdge lifted.vertices.count)}
    {row : ClosedCoordinates word cut.integral}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

variable (prepared : Prepared paired)

/-- The original A and whole corrected-B cochain readings occupy their retained finite coefficient blocks. -/
@[expose] def periodCochains (value : OrientedEdge lifted.vertices.count → Canonical) :
    Data.Vector Canonical (genus + genus) :=
  Data.Vector.Split.join (Nat.le_add_right genus genus)
    (vectorOfFn fun index => wordValue value (prepared.aWord index))
    (Eq.mp (congrArg (Data.Vector Canonical) (Nat.add_sub_cancel_left genus genus).symm)
      (vectorOfFn fun index => wordValue value (prepared.bWord index)))

/-- First-block scalar lookup reads the actual A word at its original row. -/
theorem periodCochains_first (value : OrientedEdge lifted.vertices.count → Canonical) (index : Fin genus) :
    prepared.periodCochains value (Fin.castAdd genus index) = wordValue value (prepared.aWord index) :=
  (Data.Vector.Split.join_apply_take (Nat.le_add_right genus genus)
    (vectorOfFn fun index => wordValue value (prepared.aWord index))
    (Eq.mp (congrArg (Data.Vector Canonical) (Nat.add_sub_cancel_left genus genus).symm)
      (vectorOfFn fun index => wordValue value (prepared.bWord index))) index).trans (vectorOfFn_apply _ _)

/-- Second-block lookup preserves the original full corrected-B row through its whole vector-dimension transport. -/
theorem periodCochains_last (value : OrientedEdge lifted.vertices.count → Canonical) (index : Fin genus) :
    prepared.periodCochains value (Fin.natAdd genus index) = wordValue value (prepared.bWord index) :=
  ((Data.Vector.Split.join_apply_drop (Nat.le_add_right genus genus)
    (vectorOfFn fun index => wordValue value (prepared.aWord index))
    (Eq.mp (congrArg (Data.Vector Canonical) (Nat.add_sub_cancel_left genus genus).symm)
      (vectorOfFn fun index => wordValue value (prepared.bWord index)))
    (Fin.cast (Nat.add_sub_cancel_left genus genus).symm index)).trans
      (Data.Vector.Basic.get_eq_mp (Nat.add_sub_cancel_left genus genus).symm
        (vectorOfFn fun index => wordValue value (prepared.bWord index)) index)).trans (vectorOfFn_apply _ _)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates

variable (coordinates : BasisCoordinates cut row)

/-- Join the original signed A and full-B coefficient vectors in their literal retained block order. -/
@[expose] def periodWeights : Data.Vector Int (genus + genus) :=
  Data.Vector.Split.join (Nat.le_add_right genus genus) coordinates.a
    (Eq.mp (congrArg (Data.Vector Int) (Nat.add_sub_cancel_left genus genus).symm) coordinates.b)

/-- Every first-block joined weight is the original signed A coefficient at that same bounded index. -/
theorem periodWeights_first (index : Fin genus) :
    coordinates.periodWeights (Fin.castAdd genus index) = coordinates.a index :=
  Data.Vector.Split.join_apply_take (Nat.le_add_right genus genus) coordinates.a
    (Eq.mp (congrArg (Data.Vector Int) (Nat.add_sub_cancel_left genus genus).symm) coordinates.b) index

/-- Every second-block weight is the original signed full-B coefficient under its complete dimension transport. -/
theorem periodWeights_last (index : Fin genus) :
    coordinates.periodWeights (Fin.natAdd genus index) = coordinates.b index :=
  (Data.Vector.Split.join_apply_drop (Nat.le_add_right genus genus) coordinates.a
    (Eq.mp (congrArg (Data.Vector Int) (Nat.add_sub_cancel_left genus genus).symm) coordinates.b)
    (Fin.cast (Nat.add_sub_cancel_left genus genus).symm index)).trans
      (Data.Vector.Basic.get_eq_mp (Nat.add_sub_cancel_left genus genus).symm coordinates.b index)

/-- Cache the actual integer coefficient conversions, squared norms and finite mass using the original producer. -/
def periodCoefficients : {value : WeightedPeriods.Coefficients coordinates.periodWeights //
    value = WeightedPeriods.Coefficients.build coordinates.periodWeights} :=
  ⟨WeightedPeriods.Coefficients.build coordinates.periodWeights, rfl⟩

/-- The original weighted operation is exactly the existing spanning-coordinate periodValue on those same words.

The two whole original coefficient vectors, finite block readbacks and
original sum split supply the identity at every genus, including zero.
This is a scalar cochain law, not an identification of independent source
cycles, root owners or frames.
-/
theorem combine_periodValue (coefficients : WeightedPeriods.Coefficients coordinates.periodWeights)
    (value : OrientedEdge lifted.vertices.count → Canonical) :
    coefficients.combine (prepared.periodCochains value) = coordinates.periodValue value := by
  calc
    _ = sumFin (fun index : Fin (genus + genus) =>
        (coordinates.periodWeights index : Canonical) * prepared.periodCochains value index) :=
      coefficients.combine_eq _
    _ = sumFin (fun index : Fin genus =>
        (coordinates.periodWeights (Fin.castAdd genus index) : Canonical) *
          prepared.periodCochains value (Fin.castAdd genus index)) +
        sumFin (fun index : Fin genus =>
          (coordinates.periodWeights (Fin.natAdd genus index) : Canonical) *
            prepared.periodCochains value (Fin.natAdd genus index)) := sumFin_split _
    _ = sumFin (fun index : Fin genus => ((coordinates.a index : Int) : Canonical) *
          wordValue value (prepared.aWord index)) +
        sumFin (fun index : Fin genus => ((coordinates.b index : Int) : Canonical) *
          wordValue value (prepared.bWord index)) := by
      apply congrArg₂ (fun first last : Canonical => first + last)
      · apply sumFin_congr
        intro index
        rewrite [coordinates.periodWeights_first index, prepared.periodCochains_first value index]
        rfl
      · apply sumFin_congr
        intro index
        rewrite [coordinates.periodWeights_last index, prepared.periodCochains_last value index]
        rfl
    _ = coordinates.periodValue value := (sumFin_add _ _).symm

variable (coefficients : WeightedPeriods.Coefficients coordinates.periodWeights)
    (programmes : Data.Vector RefinementProgram (genus + genus))

/-- Read the actual weighted approximation from the GIVEN original A/full-B programme sample streams. -/
@[expose] def periodApproximation : WeightedPeriods.GeometricApproximation :=
  coefficients.approximation (programmes.map WeightedPeriodNames.programApproximation)

/-- The weighted stream reads the exact original programme model samples at the same actual stages. -/
theorem periodApproximation_sample (stage : Nat) :
    (coordinates.periodApproximation coefficients programmes).sample stage = coefficients.combine
      (fun index => ((programmes index).model stage).integralSample) := by
  change coefficients.combine (fun index =>
    ((programmes.map WeightedPeriodNames.programApproximation) index).sample stage) = _
  unfold WeightedPeriods.Coefficients.combine
  apply sumFin_congr
  intro index
  change coefficients.values index *
      ((programmes.map WeightedPeriodNames.programApproximation) index).sample stage =
    coefficients.values index * ((programmes index).model stage).integralSample
  rewrite [Data.Vector.Basic.map_apply]
  rfl

/-- Use original finite arithmetic on the GIVEN programme output names and retained signed coefficient cache. -/
def periodName : CoherentNamed :=
  WeightedPeriodNames.Coefficients.named coefficients (fun index => (programmes index).output)

/-- The actual arithmetic name is operationally equivalent to the weighted original sample stream.

Both components are the given programmes' own output names and model
samples. No name is manufactured from a finite cochain observation.
-/
def periodName_equivalent : NamedEquivalent (coordinates.periodName coefficients programmes).name
    (geometricNamed (coordinates.periodApproximation coefficients programmes)).name := by
  unfold periodName periodApproximation
  apply WeightedPeriodNames.Coefficients.named_equivalent
  intro index
  rewrite [Data.Vector.Basic.map_apply]
  exact WeightedPeriodNames.programApproximation_output (programmes index)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.SpanningRows.BasisCoordinates

end
