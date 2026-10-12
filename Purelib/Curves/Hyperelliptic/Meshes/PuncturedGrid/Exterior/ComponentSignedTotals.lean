module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedWitnessSigns
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularWitnesses
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.DifferentialParents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentClosure
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RegularWitnesses

open Purelib.Curves

open Purelib.Geometry

open Purelib.Riemann

@[expose] public section

/-! Occurrence totals retain the single root sign of their whole component. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSignedTotals.RegularWitnesses

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {index depth : Nat} {box :
    Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- A shared primitive witness on appended original parent banks restricts to the same primitive on each retained bank.
-/
theorem withPrimitive_append (value : Normalization.InverseRootPolynomial.Polynomial)
    {first last : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    {firstCovers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers first} {lastCovers :
      Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers last}
    {firstBank : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular firstCovers} {lastBank :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular lastCovers}
    {firstPaths lastPaths : List (List Normalization.InverseRootPolynomial.Gaussian)}
    (left : Charts.Reciprocal.Disk.RegularWitnesses sample depth firstBank
      firstPaths) (right : Charts.Reciprocal.Disk.RegularWitnesses sample depth
      lastBank lastPaths)
    (shared : (left.append right).WithPrimitive value) : left.WithPrimitive value ∧ right.WithPrimitive value := by
  induction left with
  | nil => exact ⟨True.intro, shared⟩
  | cons head tail ih =>
      obtain ⟨leftShared, rightShared⟩ := ih shared.2
      exact ⟨⟨shared.1, leftShared⟩, rightShared⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSignedTotals.RegularWitnesses

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence SurfacePreparation)

open Purelib.Riemann.Normalization

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

/-- Keep each occurrence's total readback while concatenating its parent
witnesses. A shared primitive then specializes all totals without reevaluation. -/
theorem
  SurfaceRequests.AllSurfacePreparation.SampledEntry.regular_total_witnesses
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular) sample shared depth readingIndex localTarget localArea floor))
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    ∃ paths, ∃ witnesses : Charts.Reciprocal.Disk.RegularWitnesses sample depth

        (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.capSpine
        (values.map (fun value => value.entry.occurrence))).bank paths,
      ∀ primitive, witnesses.WithPrimitive primitive →
        values.map (fun value => value.evaluated.right.total) = values.map (fun value =>
          primitive.eval value.entry.occurrence.finish⁻¹ - primitive.eval value.entry.occurrence.start⁻¹) := open
            Purelib.Data in by
  induction values with
  | nil => exact ⟨[], .nil, fun _ _ => rfl⟩
  | cons head tail ih =>
      obtain ⟨firstPaths, firstEq, ⟨firstWitnesses⟩⟩ := head.evaluated.regular_witnesses degree
      obtain ⟨lastPaths, lastWitnesses, lastTotals⟩ := ih
      refine ⟨firstPaths ++ lastPaths, firstWitnesses.append lastWitnesses, ?_⟩
      intro primitive sharedPrimitive
      obtain ⟨headShared, tailShared⟩ :=
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSignedTotals.RegularWitnesses.withPrimitive_append
        primitive firstWitnesses lastWitnesses sharedPrimitive
      obtain ⟨chain⟩ := head.entry.occurrence.compared.entered.cache.chain
      have headTotal := head.evaluated.right.total_eq.trans ((congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
        firstEq).trans
        ((congrArg (fun paths => Data.Gaussian.Norm.Sum.Basic.gaussianSum paths.flatten) (firstWitnesses.paths_eq
          primitive headShared)).trans
          (head.entry.occurrence.cap.path.bank.regularPrimitivePaths_sum primitive depth chain.toDirectPathChain)))
      exact congrArg₂ List.cons headTotal (lastTotals primitive tailShared)

/-- Exact differential recasting of the original parent lists gives the shared primitive sign of the two retained
witnesses. -/
private def ComponentSignedTotals.ExteriorProgram.sign_of_parent_eq
    {otherDepth : Nat} {otherBox : Rational.Box}
    {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}
    {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    {otherParents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve other)}
    (same : parents.map (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other) = otherParents)
    {covers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents} {bank :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular covers}
    {otherCovers : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers otherParents} {otherBank :
      Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank regular otherCovers}
    {paths otherPaths : List (List Normalization.InverseRootPolynomial.Gaussian)}
    (first : Charts.Reciprocal.Disk.RegularWitnesses sample depth bank paths)
    (last : Charts.Reciprocal.Disk.RegularWitnesses otherSample otherDepth
      otherBank otherPaths) :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedWitnessSigns.PairedPrimitiveSign first.primitive
      last.primitive sample.primitive.value otherSample.primitive.value := by
  cases same
  exact Hyperelliptic.Charts.Reciprocal.Disk.PairedWitnessSigns.RegularWitnesses.recastSign first last

/-- Every retained occurrence total in both independently evaluated component
lists uses the same sheet bit, even across occurrence boundaries. -/
theorem
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.paired_occurrence_totals
    {sheet : Fin 2}
    (first :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
      regular domains (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted
      differential sheet))
    (last :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
      regular domains (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted other
      sheet))
    {otherDepth otherReadingIndex otherFloor : Nat} {otherBox : Rational.Box}
    {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}
    {otherShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other index domains}
      {otherTarget otherArea : Normalization.InverseRootPolynomial.Coordinate}
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular) sample shared depth readingIndex localTarget localArea floor))
    (otherValues : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular)
      otherSample otherShared otherDepth otherReadingIndex otherTarget otherArea otherFloor))
    (occurrences : values.map (fun value => value.entry.occurrence) = first.occurrences)
    (otherOccurrences : otherValues.map (fun value => value.entry.occurrence) = last.occurrences)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    ∃ flip : Bool,
      values.map (fun value => value.evaluated.right.total) = values.map (fun value =>
        (if flip then -sample.primitive.value else sample.primitive.value).eval value.entry.occurrence.finish⁻¹ -
        (if flip then -sample.primitive.value else sample.primitive.value).eval value.entry.occurrence.start⁻¹) ∧
      otherValues.map (fun value => value.evaluated.right.total) = otherValues.map (fun value =>
        (if flip then -otherSample.primitive.value else otherSample.primitive.value).eval
          value.entry.occurrence.finish⁻¹ -
        (if flip then -otherSample.primitive.value else otherSample.primitive.value).eval
          value.entry.occurrence.start⁻¹) := by
  obtain ⟨paths, witnesses, totals⟩ :=
    SurfaceRequests.AllSurfacePreparation.SampledEntry.regular_total_witnesses
    values degree
  obtain ⟨otherPaths, otherWitnesses, otherTotals⟩ :=
    SurfaceRequests.AllSurfacePreparation.SampledEntry.regular_total_witnesses
    otherValues degree
  have parents := first.build_parents_recast last
  rw [← occurrences, ← otherOccurrences] at parents
  let sign := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSignedTotals.ExteriorProgram.sign_of_parent_eq
    parents witnesses otherWitnesses
  have firstLinks : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Links
    (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.capSpine
    (values.map (fun value => value.entry.occurrence))).bank := by
    rw [occurrences]
    exact
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.JoinedCap.build
      first).links
  have lastLinks : Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.SideBank.Links
    (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence.capSpine
    (otherValues.map (fun value => value.entry.occurrence))).bank := by
    rw [otherOccurrences]
    exact
      (SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation.JoinedCap.build
      last).links
  have firstTotal := totals witnesses.primitive (witnesses.shared firstLinks)
  have lastTotal := otherTotals otherWitnesses.primitive (otherWitnesses.shared lastLinks)
  have firstSigned := congrArg Prod.fst sign.signed
  have lastSigned := congrArg Prod.snd sign.signed
  change witnesses.primitive = _ at firstSigned
  change otherWitnesses.primitive = _ at lastSigned
  rw [firstSigned] at firstTotal
  rw [lastSigned] at lastTotal
  exact ⟨sign.flip, firstTotal, lastTotal⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior
