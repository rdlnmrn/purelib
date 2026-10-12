module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Integration

open Purelib.Riemann

open Purelib

public section

/-!
# Two-differential identity for the actual corrected A/B words

Finite polarization extracts the determinant pairing from the established
conjugate/value area identity. All physical and regular-face terms survive
in the polarized residual. No smallness or vanishing assertion is made here.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Gaussian.Basic.Canonical

namespace BilinearPolarization

/-- The Gaussian imaginary unit with real part zero and imaginary part one. -/
@[expose] def imaginary : Gaussian := ⟨0, 1⟩

/-- The four finite scalar readings select the complex-bilinear cross term. -/
@[expose] def extract (value : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical) : Gaussian :=
  (⟨1 / 4, 0⟩ : Gaussian.Basic.Canonical) *
    (value 1 - value (-1) - Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary *
      (value Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary - value
      (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)))

/-- Combine the conjugate of the first original edge valuation with a Gaussian multiple of the second. -/
@[expose] def mix {vertices : Nat} (first second : Topology.Polygon.Stokes.OrientedEdge vertices →
  Gaussian.Basic.Canonical) (coefficient : Gaussian.Basic.Canonical)
    (edge : Topology.Polygon.Stokes.OrientedEdge vertices) : Gaussian := Gaussian.Basic.conj (first edge) +
      coefficient * second edge

/-- The mixed valuation reverses sign when both original edge valuations are antisymmetric. -/
theorem mix_reverse {vertices : Nat} (first second : Topology.Polygon.Stokes.OrientedEdge vertices →
  Gaussian.Basic.Canonical)
    (firstAnti : ∀ edge, first edge.reverse = -first edge)
    (secondAnti : ∀ edge, second edge.reverse = -second edge) (coefficient : Gaussian.Basic.Canonical) (edge :
      Topology.Polygon.Stokes.OrientedEdge vertices) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient
      edge.reverse = -Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
      coefficient edge := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
  rw [firstAnti, secondAnti]
  apply Gaussian.Basic.ext <;> simp only [Gaussian.Basic.conj, Gaussian.Basic.neg_re, Gaussian.Basic.neg_im,
    Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- Reading the mixed valuation along the original word equals the conjugated first total plus the scaled second total.
-/
theorem word_mix {vertices : Nat} (first second : Topology.Polygon.Stokes.OrientedEdge vertices →
  Gaussian.Basic.Canonical) (coefficient : Gaussian.Basic.Canonical)
    (word : List (Topology.Polygon.Stokes.OrientedEdge vertices)) :
    Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
      word = Gaussian.Basic.conj (Topology.Surface.Sewing.SewingRetraction.wordValue first word) + coefficient
      * Topology.Surface.Sewing.SewingRetraction.wordValue second word := by
  induction word with
  | nil =>
    change (0 : Gaussian.Basic.Canonical) = Gaussian.Basic.conj 0 + coefficient * 0; rw
      [Gaussian.Basic.conj_zero, Gaussian.Basic.mul_zero, Gaussian.Basic.add_zero]
  | cons edge rest ih =>
      change (Gaussian.Basic.conj (first edge) + coefficient * second edge) +
        Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
        rest = _
      rw [ih, Topology.Surface.Sewing.SewingRetraction.wordValue, Topology.Surface.Sewing.SewingRetraction.wordValue,
        Gaussian.Basic.conj_add]
      ring1

/-- The four retained scalar area readings extract exactly the original complex-bilinear determinant. -/
theorem extract_area (aFirst bFirst aSecond bSecond : Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Path.BoundaryRibbon.area (Gaussian.Basic.conj aFirst + coefficient * aSecond)
      (Gaussian.Basic.conj bFirst + coefficient * bSecond)) =
      aFirst * bSecond - bFirst * aSecond := by
  let value := fun coefficient => Path.BoundaryRibbon.area (Gaussian.Basic.conj aFirst + coefficient * aSecond)
    (Gaussian.Basic.conj bFirst + coefficient * bSecond)
  have cross : value 1 - value (-1) -
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary * (value
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary - value
    (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)) =
      (⟨4, 0⟩ : Gaussian.Basic.Canonical) * (aFirst * bSecond - bFirst * aSecond) := by
    apply Gaussian.Basic.ext <;>
      simp only [value, Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary,
        Path.BoundaryRibbon.area, Gaussian.Basic.conj, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
        Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
        Gaussian.Basic.neg_re, Gaussian.Basic.neg_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1
  change (⟨1 / 4, 0⟩ : Gaussian.Basic.Canonical) * _ = _
  rw [cross, ← _root_.mul_assoc, show (⟨1 / 4, 0⟩ : Gaussian.Basic.Canonical) * ⟨4, 0⟩ = 1 by decide, _root_.one_mul]

/-- Pointwise equal original scalar readings have equal finite polarization extractions. -/
theorem extract_congr {first second : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical} (same : ∀ coefficient, first
  coefficient = second coefficient) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract first =
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract second := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
  rw [same 1, same (-1), same Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary,
    same (-Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary)]

/-- Finite polarization commutes with the original finite indexed sum. -/
theorem extract_sum {count : Nat} (values : Gaussian.Basic.Canonical → Fin count → Gaussian.Basic.Canonical) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      FiniteSum.Fin.sumFin (values coefficient)) = FiniteSum.Fin.sumFin (fun index =>
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient => values
      coefficient index)) := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
  rw [FiniteSum.Fin.sumFin_mul_left, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_mul_left,
    FiniteSum.Fin.sumFin_sub]

end BilinearPolarization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered}

/-- The full right-hand side after moving only the finite exterior area.
Internal excursions, the reference hole, terminal data and signed faces are
still explicit. This is not a zero-residual certificate. -/
@[expose] def surfaceResidual (_prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  paired.rows.internalArea value + paired.ending.internalArea value +
    Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue value paired.rows.word)
      (-Topology.Surface.Sewing.SewingRetraction.wordValue value (paired.reference.hole.liftedBoundary lifted.vertices
      lifted.edges)) +
    paired.ending.exteriorArea value (Topology.Surface.Sewing.SewingRetraction.wordValue value paired.rows.word) +
    Topology.Mesh.RetracingWords.AreaTerm.total value ordered.prepared.compiled.areaTerms -
    lifted.edges.chainArea lifted.vertices value base.bank.exterior sheet

/-- The original corrected A/B pairing equals the complete retained surface residual. -/
theorem pairing_eq_surfaceResidual (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) : prepared.pairing value =
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared value := by
  have formula := prepared.area_formula value anti
  unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual
  rw [← formula]
  ring1

/-- The complete surface residual is the actual corrected A/B word area: the
retained interior, hole, exterior and face terms cancel against the fixed
exterior chain area. This is the simplification that makes the first relation
the polarization of the actual A/B determinant. -/
theorem surfaceResidual_eq_correctedArea (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared
  paired)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared value =
      paired.rows.correctedArea value :=
  (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.pairing_eq_surfaceResidual prepared value anti).symm.trans
    (prepared.pairing_eq value)

/-- Polarize the complete original physical and signed-face surface residual in the two supplied differential
valuations. -/
@[expose] def bilinearResidual (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
  (first second : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient))

/-- Exact two-differential determinant identity for the corrected walks,
with their complete polarized physical and face residual. -/
theorem bilinear_formula (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (first
  second : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (firstAnti : ∀ edge, first edge.reverse = -first edge)
    (secondAnti : ∀ edge, second edge.reverse = -second edge) :
    FiniteSum.Fin.sumFin (fun index : Fin genus =>
      Topology.Surface.Sewing.SewingRetraction.wordValue first (prepared.aWord index) *
        Topology.Surface.Sewing.SewingRetraction.wordValue second (prepared.bWord index) -
      Topology.Surface.Sewing.SewingRetraction.wordValue first (prepared.bWord index) *
        Topology.Surface.Sewing.SewingRetraction.wordValue second (prepared.aWord index)) =
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared first second := by
  have polarized := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun
    coefficient =>
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.pairing_eq_surfaceResidual prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix_reverse first second
        firstAnti secondAnti coefficient))
  change Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
    FiniteSum.Fin.sumFin (fun index : Fin genus =>
    Path.BoundaryRibbon.area (Topology.Surface.Sewing.SewingRetraction.wordValue
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
      (prepared.aWord index))
      (Topology.Surface.Sewing.SewingRetraction.wordValue
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
        (prepared.bWord index)))) =
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared first second at polarized
  rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_sum] at polarized
  apply Eq.trans _ polarized
  apply FiniteSum.Fin.sumFin_congr
  intro index
  symm
  calc
    _ = Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        Path.BoundaryRibbon.area (Gaussian.Basic.conj (Topology.Surface.Sewing.SewingRetraction.wordValue first
          (prepared.aWord index)) + coefficient * Topology.Surface.Sewing.SewingRetraction.wordValue second
          (prepared.aWord index))
          (Gaussian.Basic.conj (Topology.Surface.Sewing.SewingRetraction.wordValue first (prepared.bWord
            index)) + coefficient * Topology.Surface.Sewing.SewingRetraction.wordValue second (prepared.bWord index)))
            :=
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun coefficient =>
        by
        rw [Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix,
          Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix])
    _ = _ := Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_area _ _ _ _

/-- The first-bilinear residual is the polarization of the actual corrected A/B
word area, with no surface residual left in the way. -/
theorem bilinearResidual_eq_extract_correctedArea (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (first second : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (firstAnti : ∀ edge, first edge.reverse = -first edge)
    (secondAnti : ∀ edge, second edge.reverse = -second edge) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared first second =
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
        paired.rows.correctedArea (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix
          first second coefficient)) := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual
  exact Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun coefficient
    =>
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual_eq_correctedArea prepared _
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix_reverse first second
        firstAnti secondAnti coefficient))

/-- The first-bilinear residual is antisymmetric in its two differential
directions: swapping them negates it. This is the exact symplectic skewness of
the word pairing, proved from its explicit sum form. -/
theorem bilinearResidual_swap (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (first second : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (firstAnti : ∀ edge, first edge.reverse = -first edge)
    (secondAnti : ∀ edge, second edge.reverse = -second edge) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared first second =
      -Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared second first := by
  rw [← Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinear_formula prepared first second firstAnti
    secondAnti,
    ← Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinear_formula prepared second first secondAnti
      firstAnti]
  rw [← FiniteSum.Fin.sumFin_neg]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  ring1

/-- The diagonal first-bilinear residual vanishes: a direction paired with
itself has zero symplectic product. This is the exact diagonal cancellation
consumed by the genus-one and genus-two first-relation reductions. -/
theorem bilinearResidual_self_zero (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared value value = 0 := by
  have skew : Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared value value =
      -Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared value value :=
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual_swap prepared value value anti anti
  have doubled : Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared value value +
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared value value = 0 := by
    nth_rewrite 1 [skew]
    rw [neg_add_cancel]
  have factor : Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared value value * (2 :
    Gaussian.Basic.Canonical) =
      (0 : Gaussian.Basic.Canonical) * 2 := by
    have mul2 : Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared value value * (2 :
      Gaussian.Basic.Canonical) =
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared value value +
          Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.bilinearResidual prepared value value := by
      ring1
    rw [mul2, doubled, Gaussian.Basic.zero_mul]
  exact Gaussian.Field.mul_right_cancel_of_ne
    (by decide : (2 : Gaussian.Basic.Canonical) ≠ 0) factor

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib
open Purelib.Data

/-- Polarization extraction commutes with the pointwise difference of two readings.

The four original coefficient evaluations use the same extraction factors.
Scalar subtraction distributes over their retained Gaussian combination. -/
public theorem BilinearPolarization.extract_sub (first second : Data.Gaussian.Basic.Canonical →
  Data.Gaussian.Basic.Canonical) :
    BilinearPolarization.extract (fun coefficient => first coefficient - second coefficient) =
      BilinearPolarization.extract first - BilinearPolarization.extract second := by
  unfold BilinearPolarization.extract
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
