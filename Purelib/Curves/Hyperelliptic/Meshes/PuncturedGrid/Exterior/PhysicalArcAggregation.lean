module
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.ReciprocalCapBilinearBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalSourceRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceGeometry
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateArcFamily

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

open Purelib.Data.Gaussian.Norm.Sum

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Periods

public section

/-! Aggregate physical occurrence samples with their actual signs and chords. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfaceOccurrence AllSurfacePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation (CapAttachment)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Riemann.Normalization
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential other :
    Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub)
open Purelib.Data.Gaussian.Norm.Basic (normSq_neg)

/-- Convert the ascending physical side sample to the occurrence orientation, then restore the chord retained by the
literal cap-arc comparison. -/
@[expose] def physicalArcValue (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    {stage : Nat} {box otherBox : Rational.Box}
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox) (physical : Data.Gaussian.Basic.Canonical) : Gaussian :=
  (if SurfaceOccurrence.sourceForward occurrence then physical else -physical) +
    PairedArcRequest.conjugateChordValue occurrence sample otherSample

/-- The two physical-side theorems differ only by this explicitly retained sign. -/
@[expose] def physicalArcError (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    {stage : Nat} {box otherBox : Rational.Box}
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox) (depth : Nat) (physical : Data.Gaussian.Basic.Canonical)
      : Gaussian :=
  let centered := PairedArcRequest.conjugateArcValue occurrence sample otherSample depth -
    PairedArcRequest.conjugateChordValue occurrence sample otherSample
  if SurfaceOccurrence.sourceForward occurrence then physical - centered else physical + centered

/-- Restoring the retained occurrence sign and chord preserves the squared physical-to-arc error. -/
theorem physicalArcValue_error (occurrence : ExteriorProgram.SurfaceOccurrence regular domains differential)
    {stage : Nat} {box otherBox : Rational.Box}
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox) (depth : Nat) (physical : Data.Gaussian.Basic.Canonical)
      :
    Data.Gaussian.Norm.Basic.normSq
      (physicalArcValue occurrence sample
      otherSample physical -
      PairedArcRequest.conjugateArcValue occurrence sample otherSample depth) =
    Data.Gaussian.Norm.Basic.normSq
      (physicalArcError occurrence sample
      otherSample depth physical) := by
  cases direction : SurfaceOccurrence.sourceForward occurrence with
  | true =>
    simp only [physicalArcValue,
      physicalArcError]
    rw [direction]
    rewrite [if_pos (Eq.refl true), if_pos (Eq.refl true)]
    apply congrArg Data.Gaussian.Norm.Basic.normSq
    ring1
  | false =>
    simp only [physicalArcValue,
      physicalArcError]
    rw [direction]
    rewrite [if_neg (show ¬false = true from by decide), if_neg (show ¬false = true from by decide)]
    have scalar (a b c : Data.Gaussian.Basic.Canonical) : -a + b - c = -(a + (c - b)) := by ring1
    rw [scalar, Data.Gaussian.Norm.Basic.normSq_neg]

namespace PhysicalSourceRequest
variable {prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential} {target : Rational} {minimum floor : Nat}
  {stage depth : Nat} {box otherBox : Purelib.Geometry.Rational.Box}

/-- Sum the actual occurrence-level physical comparisons at the common arc depth. The finite family budget pays both
factors of its retained count. -/
theorem physical_arc_error (request : PhysicalSourceRequest prepared other target minimum floor)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox)
    (physical : Fin prepared.occurrences.length → Data.Gaussian.Basic.Canonical)
    (accurate : ∀ i, Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation.physicalArcError
      (prepared.occurrences[i.val]'i.isLt)
      sample otherSample depth (physical i)) < request.allowance) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun i =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation.physicalArcValue
      (prepared.occurrences[i.val]'i.isLt) sample otherSample (physical i)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.occurrences.map (fun occurrence =>
        PairedArcRequest.conjugateArcValue occurrence sample otherSample depth))) < target := by
  have bound := Indexed.normSq_sumFin_le
    (fun i : Fin prepared.occurrences.length =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation.physicalArcValue
        (prepared.occurrences[i.val]'i.isLt) sample otherSample (physical i) -
        PairedArcRequest.conjugateArcValue (prepared.occurrences[i.val]'i.isLt) sample otherSample depth)
    request.allowance (fun i =>
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation.physicalArcValue_error _ sample
      otherSample depth (physical i)).trans_le (accurate i).le)
  have readback := Data.Gaussian.Norm.Sum.Indexed.sumFin_eq_gaussianSum
    (fun i : Fin prepared.occurrences.length => PairedArcRequest.conjugateArcValue
      (prepared.occurrences[i.val]'i.isLt) sample otherSample depth)
  have mapped := Data.List.OfFn.Basic.map_ofFn
    (function := fun i : Fin prepared.occurrences.length => prepared.occurrences[i.val]'i.isLt)
    (transform := fun occurrence => PairedArcRequest.conjugateArcValue occurrence sample otherSample depth)
  change (List.ofFn (fun i : Fin prepared.occurrences.length => prepared.occurrences[i.val]'i.isLt)).map
    (fun occurrence => PairedArcRequest.conjugateArcValue occurrence sample otherSample depth) =
    List.ofFn (fun i : Fin prepared.occurrences.length => PairedArcRequest.conjugateArcValue
      (prepared.occurrences[i.val]'i.isLt) sample otherSample depth) at mapped
  rw [← mapped, Data.List.OfFn.Basic.ofFn_getElem] at readback
  rw [FiniteSum.Fin.sumFin_sub, readback] at bound
  exact bound.trans_lt ((show (prepared.occurrences.length : Fraction.Rational)^2 * request.allowance =
    (prepared.occurrences.length : Fraction.Rational) * ((prepared.occurrences.length : Fraction.Rational) *
      request.allowance) by ring1).trans_lt request.paid)

/-- The aggregated physical family compares with the cap attachment's actual boundary words, using the same pair of
reciprocal primitive samples. -/
theorem physical_attachment_arc_error (request : PhysicalSourceRequest prepared other target
  minimum floor)
    (attached : AllSurfacePreparation.CapAttachment prepared)
    (sample : Primitives.Sample cap differential stage box)
    (otherSample : Primitives.Sample cap other stage otherBox)
    (physical : Fin prepared.occurrences.length → Data.Gaussian.Basic.Canonical)
    (accurate : ∀ i, Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation.physicalArcError
      (prepared.occurrences[i.val]'i.isLt)
      sample otherSample depth (physical i)) < request.allowance) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun i =>
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation.physicalArcValue
      (prepared.occurrences[i.val]'i.isLt) sample otherSample (physical i)) -
      CellBoundary.sumValues (fun word => CellBoundary.sumValues (fun edge => Bilinear.arcArea
        (fun point => ConjugateIncrementComparison.conjugateFirst
          (ReciprocalCapBilinearBounds.pairedValue sample otherSample point)) depth
        (lifted.vertices.coordinate edge.start) (lifted.vertices.coordinate edge.finish)) word) attached.words) < target
          := by
  have bound :=
    physical_arc_error
    request sample otherSample physical accurate
  rw [PairedArcRequest.conjugate_attachment_arcs attached sample otherSample depth] at bound
  exact bound

end PhysicalSourceRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PhysicalArcAggregation
