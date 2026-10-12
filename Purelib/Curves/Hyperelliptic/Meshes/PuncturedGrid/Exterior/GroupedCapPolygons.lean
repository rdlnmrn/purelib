module
import Purelib.Data.List.Map
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedAreaBlocks
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentClosure

public section

/-! Reassemble retained component samples without cross-component area loss. -/
section

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

open Purelib.Data.List

open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)

open _root_.Purelib.Data.Gaussian.Basic (conj)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons

/-- Pair the two original Gaussian increment lists with conjugation in the first coordinate. -/
@[expose] def paired (first last : List Normalization.InverseRootPolynomial.Gaussian) : List PrimitivePoint :=
  List.zipWith (fun left right => ⟨conj left, right⟩) first last

/-- Pairing commutes with append when the two original leading blocks have equal lengths. -/
private theorem paired_append (first last rest otherRest : List Normalization.InverseRootPolynomial.Gaussian) (same :
  first.length = last.length) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons.paired (first ++ rest) (last ++ otherRest) =
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons.paired first last ++
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons.paired rest otherRest := by
  induction first generalizing last with
  | nil => cases last with
    | nil => rfl
    | cons _ _ => cases same
  | cons head tail ih => cases last with
    | nil => cases same
    | cons other others => exact congrArg (List.cons _) (ih others (Nat.succ.inj same))

/-- The total of equal-length paired increment lists is the pair of their original Gaussian sums, conjugating the first.
-/
private theorem paired_total (first last : List Normalization.InverseRootPolynomial.Gaussian) (same : first.length =
  last.length) :
    Path.PairedIncrementArea.total (Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons.paired first last) =
      ⟨conj (Data.Gaussian.Norm.Sum.Basic.gaussianSum first), Data.Gaussian.Norm.Sum.Basic.gaussianSum last⟩ := by
  induction first generalizing last with
  | nil => cases last with
    | nil => rfl
    | cons _ _ => cases same
  | cons head tail ih => cases last with
    | nil => cases same
    | cons other others =>
        change (⟨conj head, other⟩ : Topology.Polygon.Stokes.PrimitivePoint).add (Path.PairedIncrementArea.total
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons.paired tail others)) = _
        rw [ih others (Nat.succ.inj same)]
        exact congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk (Gaussian.Basic.conj_add head
          (Data.Gaussian.Norm.Sum.Basic.gaussianSum tail)).symm rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {index depth readingIndex floor : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
    {localTarget localArea : Normalization.InverseRootPolynomial.Coordinate}
  {otherDepth otherReadingIndex otherFloor : Nat} {otherBox : Rational.Box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}
  {otherShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other index domains}
    {otherTarget otherArea : Normalization.InverseRootPolynomial.Coordinate}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons

/-- The sum of the original occurrence totals equals the sum of their ordered flattened cap paths. -/
private theorem sum_totals
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular) sample shared depth readingIndex localTarget localArea floor)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value => value.evaluated.right.total)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map (fun value => value.evaluated.capPath)).flatten := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      change head.evaluated.right.total + Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.map (fun value =>
        value.evaluated.right.total)) = _
      rw [head.evaluated.right.total_eq, ih, List.map_cons, List.flatten_cons, Path.IncrementArea.sum_append]

/-- A retained sampled component has exactly the original program's indexed-edge count. -/
private theorem group_length
    (group : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular) sample
      shared depth readingIndex localTarget localArea floor) :
    group.values.length = group.component.program.indexed.length := by
  have entries := congrArg List.length group.occurrences_eq
  have indices := congrArg List.length group.component.prepared.occurrences_eq
  simp only [Map.length_map, -eq_self, -iff_self] at entries indices
  exact entries.trans indices

/-- A retained same-sheet component pair reads its original paired inverse-edge polygon in even degree. -/
private theorem group_pair
    (first : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular) sample
      shared depth readingIndex localTarget localArea floor)
    (last : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular)
      otherSample otherShared otherDepth otherReadingIndex otherTarget otherArea otherFloor)
    (sheet : Fin 2)
    (firstProgram : first.component.program =
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted differential sheet)
    (lastProgram : last.component.program =
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted other sheet)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    Path.PairedIncrementArea.area (Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons.paired
      (first.values.map (fun value => value.evaluated.right.total))
      (last.values.map (fun value => value.evaluated.right.total))) =
      Path.PairedIncrementArea.area ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build
        lifted differential sheet).indexed.map (fun edge =>
        (⟨conj (sample.primitive.value.eval (lifted.vertices.coordinate edge.finish)⁻¹ -
          sample.primitive.value.eval (lifted.vertices.coordinate edge.start)⁻¹),
          otherSample.primitive.value.eval (lifted.vertices.coordinate edge.finish)⁻¹ -
          otherSample.primitive.value.eval (lifted.vertices.coordinate edge.start)⁻¹⟩ :
            Topology.Polygon.Stokes.PrimitivePoint))) := by
  rcases first with ⟨⟨firstProgram', firstPrepared⟩, firstValues, firstEq, firstCap, firstSurface⟩
  rcases last with ⟨⟨lastProgram', lastPrepared⟩, lastValues, lastEq, lastCap, lastSurface⟩
  dsimp only at firstProgram lastProgram
  subst firstProgram'
  subst lastProgram'
  exact firstPrepared.conjugate_occurrence_polygon lastPrepared firstValues lastValues firstEq lastEq degree

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent

/-- Exact regrouping on the supplied sample partition. Each head component
has zero paired total, so its cross term vanishes while its full area remains. -/
theorem paired_groups_area
    (sheets : List (Fin 2))
    (first : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular)
      sample shared depth readingIndex localTarget localArea floor))
    (last : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent (regular := regular)
      otherSample otherShared otherDepth otherReadingIndex otherTarget otherArea otherFloor))
    (firstPrograms : first.map (fun group => group.component.program) = sheets.map
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted differential))
    (lastPrograms : last.map (fun group => group.component.program) = sheets.map
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted other))
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    Path.PairedIncrementArea.area (Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons.paired (((first.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent.values).flatten).map (fun value =>
      value.evaluated.right.total))
      (((last.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent.values).flatten).map
        (fun value => value.evaluated.right.total))) =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (sheets.map (fun sheet =>
      Path.PairedIncrementArea.area ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build
        lifted differential sheet).indexed.map (fun edge =>
        (⟨conj (sample.primitive.value.eval (lifted.vertices.coordinate edge.finish)⁻¹ -
          sample.primitive.value.eval (lifted.vertices.coordinate edge.start)⁻¹),
          otherSample.primitive.value.eval (lifted.vertices.coordinate edge.finish)⁻¹ -
          otherSample.primitive.value.eval (lifted.vertices.coordinate edge.start)⁻¹⟩ :
            Topology.Polygon.Stokes.PrimitivePoint))))) := by
  induction sheets generalizing first last with
  | nil =>
      have firstNil : first = [] := List.map_eq_nil_iff.mp firstPrograms
      have lastNil : last = [] := List.map_eq_nil_iff.mp lastPrograms
      subst first
      subst last
      rfl
  | cons sheet sheets ih =>
      cases first with
      | nil => cases firstPrograms
      | cons head tail => cases last with
        | nil => cases lastPrograms
        | cons otherHead otherTail =>
            have firstParts := List.cons.inj firstPrograms
            have lastParts := List.cons.inj lastPrograms
            dsimp only at firstParts lastParts
            have same : head.values.length = otherHead.values.length := by
              rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons.group_length head,
                Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons.group_length otherHead, firstParts.1,
                lastParts.1]
              rfl
            have counts : (head.values.map (fun value => value.evaluated.right.total)).length =
                (otherHead.values.map (fun value => value.evaluated.right.total)).length := by
              simpa only [Map.length_map, -eq_self, -iff_self] using same
            have leftZero := (Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons.sum_totals
              head.values).trans (head.cap.total_eq.symm.trans (head.total_zero degree))
            have rightZero := (Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons.sum_totals
              otherHead.values).trans (otherHead.cap.total_eq.symm.trans (otherHead.total_zero degree))
            have closed := Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons.paired_total _ _ counts
            rw [leftZero, rightZero] at closed
            simp only [List.map_cons, List.flatten_cons, Map.map_append, -eq_self, -iff_self]
            rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons.paired_append _ _ _ _ counts,
              Path.PairedAreaBlocks.area_append, closed,
              Hyperelliptic.Meshes.PuncturedGrid.Exterior.GroupedCapPolygons.group_pair head otherHead sheet
                firstParts.1 lastParts.1 degree,
              ih tail otherTail firstParts.2 lastParts.2]
            change _ + _ + Topology.Polygon.Stokes.edgeArea ⟨conj 0, 0⟩ _ = _ + _
            have zero (point : Topology.Polygon.Stokes.PrimitivePoint) : Topology.Polygon.Stokes.edgeArea ⟨conj 0, 0⟩
              point = 0 := by
              change 0 * point.right - point.left * 0 = 0
              rw [zero_mul, mul_zero, sub_self]
            rw [zero, add_zero]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSamples.SampledComponent

end
