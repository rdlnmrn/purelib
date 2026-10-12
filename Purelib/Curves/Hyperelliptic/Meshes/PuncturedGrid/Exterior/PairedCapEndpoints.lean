module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedWitnessSigns
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentClosure
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.RegularWitnesses

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann

@[expose] public section

/-! Read both retained cap totals as endpoint differences with one common
sheet sign. The second differential uses the original occurrence's parents. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapEndpoints

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {target otherTarget areaTarget otherAreaTarget : Fraction.Rational} {minimum otherMinimum stage depth otherDepth
    readingIndex otherReadingIndex : Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}

/-- Both retained cap totals are endpoint differences with one common sheet sign.

For even polynomial degree, the original root chains identify the same sign despite different cap depths and reading
floors; neither retained path is evaluated again. -/
theorem paired_cap_totals
    (prepared :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
      regular domains differential)
    (occurrence :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
      regular domains differential) (member : occurrence ∈ prepared.occurrences)
    {firstRequest : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest
      occurrence.cap target areaTarget minimum}
    {lastRequest : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest
      (occurrence.pairedCap prepared member other)
      otherTarget otherAreaTarget otherMinimum}
    (first : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation
      firstRequest sample depth readingIndex)
    (last : Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest.Evaluation
      lastRequest otherSample otherDepth otherReadingIndex)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    ∃ flip : Bool,
      first.right.total =
        (if flip then -sample.primitive.value else sample.primitive.value).eval occurrence.finish⁻¹ -
        (if flip then -sample.primitive.value else sample.primitive.value).eval occurrence.start⁻¹ ∧
      last.right.total =
        (if flip then -otherSample.primitive.value else otherSample.primitive.value).eval occurrence.finish⁻¹ -
        (if flip then -otherSample.primitive.value else otherSample.primitive.value).eval occurrence.start⁻¹ := open
          Purelib.Data in by
  obtain ⟨firstPaths, firstEq, ⟨firstWitnesses⟩⟩ := first.regular_witnesses degree
  obtain ⟨lastPaths, lastEq, ⟨lastWitnesses⟩⟩ := last.regular_witnesses degree
  let sign := Hyperelliptic.Charts.Reciprocal.Disk.PairedWitnessSigns.RegularWitnesses.recastSign firstWitnesses
    lastWitnesses
  have paths := Hyperelliptic.Charts.Reciprocal.Disk.PairedWitnessSigns.RegularWitnesses.paired_paths_signed
    firstWitnesses lastWitnesses sign occurrence.cap.path.links
    (occurrence.pairedCap prepared member other).path.links
  obtain ⟨firstChain⟩ := occurrence.compared.entered.cache.chain
  obtain ⟨lastChain⟩ := (occurrence.recastComparison other).entered.cache.chain
  refine ⟨sign.flip, ?_, ?_⟩
  · exact first.right.total_eq.trans ((congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum firstEq).trans
      ((congrArg (fun paths => Data.Gaussian.Norm.Sum.Basic.gaussianSum paths.flatten) paths.1).trans
        (occurrence.cap.path.bank.regularPrimitivePaths_sum _ _ firstChain.toDirectPathChain)))
  · exact last.right.total_eq.trans ((congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum lastEq).trans
      ((congrArg (fun paths => Data.Gaussian.Norm.Sum.Basic.gaussianSum paths.flatten) paths.2).trans
        ((occurrence.pairedCap prepared member other).path.bank.regularPrimitivePaths_sum _ _
          lastChain.toDirectPathChain)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapEndpoints
