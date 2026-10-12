module
import Purelib.Algebra.FiniteSum.Gaussian
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh

public import Purelib.Riemann.Periods.PairedPeriodPairingBridge
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueWordLinearity
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Topology.Surface.Sewing.SewingConnected
import Mathlib.Data.Nat.Init
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Vector.Dependent
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Mathlib.Algebra.Group.Defs
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings (EdgeMagnitude)

/-!
# Conjugate-linearity of the chord and residual parts

Given the per-generator support certificate, the chord periods, the chord
part and the retained residual part of a mixed value vector are the
conjugate-linear combinations of the two sides. This is the linearity
consumed by the polarization of the ordered pairing.
-/

public section
namespace Purelib.Topology.Surface.Chord.ValueChordLinearity

open Purelib
open Algebra
open Algebra.FiniteSum.Rational
open Curves
open Curves.Hyperelliptic.Meshes.PuncturedGrid
open Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid
open Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
open Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired
open Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
open Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
open Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
open Data
open Data.Gaussian.Norm.Sum
open Data.Rat
open Integration.Path
open Riemann.Periods
open Topology.Surface.Boundary.BoundaryCoordinates
open Topology.Surface.Cut.BoundaryPairs.SewingForest
open Topology.Surface.Cut.IntegralPairing
open Topology.Surface.Sewing
open Topology.Surface.Sewing.VertexSewing
open Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueWordLinearity
open Topology.Polygon.Stokes
open _root_.Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open _root_.Purelib.Data.Gaussian.Basic (Canonical conj_add conj_mul conj_zero)
open _root_.Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
  (Ordered)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (ClosedCoordinates CutBank)
open _root_.Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open _root_.Purelib.Riemann.Periods.PairedPeriodPairingBridge (generatorValues chordValues chordPart residualPart)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open _root_.Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open _root_.Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue faceValue)
open _root_.Purelib.Algebra.FiniteSum.Fin
  (sumFin sumFin_congr sumFin_add sumFin_succ sumFin_mul_left sumFin_sub sumFin_neg)
open _root_.Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open _root_.Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open _root_.Purelib.Data.Rat.Fraction.Order.Arithmetic (add_le_add_direct mul_le_mul_of_nonneg_left_direct)
open _root_.Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve} {bank : LiftedPuncturedGrid.BasedBranchBank owner.lifted} {sheet : Fin 2}
  {ordered : BasedBranchBank.Ordered bank sheet} {paired : Ordered.Paired ordered} {prepared : PeriodPrograms.Prepared
    paired}

section
open _root_.Purelib.Data.Gaussian.Basic (conj)

/-- An integer combination of a conjugate-linear combination splits into the two conjugate-linear parts. -/
theorem combine_mixValues {count : Nat} (coefficients : Fin count → Int)
    {first second : Fin count → Gaussian.Basic.Canonical} (coefficient : Gaussian.Basic.Canonical) :
    WordCoordinates.combine coefficients (fun index => Data.Gaussian.Basic.conj (first index) + coefficient * second
      index) =
      Data.Gaussian.Basic.conj (WordCoordinates.combine coefficients first) +
        coefficient * WordCoordinates.combine coefficients second := by
  unfold WordCoordinates.combine
  have expand : ∀ index, (coefficients index : Gaussian.Basic.Canonical) *
      (Data.Gaussian.Basic.conj (first index) + coefficient * second index) =
      (coefficients index : Gaussian.Basic.Canonical) * Data.Gaussian.Basic.conj (first index) +
        (coefficients index : Gaussian.Basic.Canonical) * coefficient * second index := by
    intro index
    ring1
  have firstPart : FiniteSum.Fin.sumFin (fun index => (coefficients index : Gaussian.Basic.Canonical) *
    Data.Gaussian.Basic.conj (first index)) =
      Data.Gaussian.Basic.conj (FiniteSum.Fin.sumFin (fun index => (coefficients index : Gaussian.Basic.Canonical) *
        first index)) := by
    rw [Algebra.FiniteSum.Gaussian.conj_sumFin]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    rw [Gaussian.Basic.conj_mul, Data.Gaussian.Cast.conj_intCast]
  have secondPart : FiniteSum.Fin.sumFin (fun index => (coefficients index : Gaussian.Basic.Canonical) * coefficient *
    second index) =
      coefficient * FiniteSum.Fin.sumFin (fun index => (coefficients index : Gaussian.Basic.Canonical) * second index)
        := by
    rw [← FiniteSum.Fin.sumFin_mul_left]
    apply FiniteSum.Fin.sumFin_congr
    intro index
    ring1
  rw [FiniteSum.Fin.sumFin_congr expand, FiniteSum.Fin.sumFin_add, firstPart, secondPart]

/-- The support obligation for one retained cut generator. -/
@[expose] def generatorSupported (index : Fin owner.lifted.cutBoundaryWord.alphabet.count) : Prop :=
  (OrientedEdge.map owner.lifted.cutPolygon.patch.cut.vertexLabels (owner.lifted.cutBoundaryWord.alphabet.generators
    index)) ∈
      triangleEdgeOccurrences owner.lifted.mesh.triangulation.faces ∨
    ((OrientedEdge.map owner.lifted.cutPolygon.patch.cut.vertexLabels (owner.lifted.cutBoundaryWord.alphabet.generators
      index))).reverse ∈
      triangleEdgeOccurrences owner.lifted.mesh.triangulation.faces

/-- Every retained cut generator is supported: its projection is an actual occurrence of the lifted mesh. -/
theorem generatorSupported_all (index : Fin owner.lifted.cutBoundaryWord.alphabet.count) :
    generatorSupported (owner := owner) index := by
  unfold generatorSupported
  refine Or.inl ?_
  have member := owner.lifted.cutBoundaryWord.alphabet.generator_projected_mem index
  rw [owner.lifted.cutPolygon.patch.cut.boundary_eq] at member
  exact SinglePolygon.boundary_member owner.lifted.cutPolygon member

/-- Integer combination respects pointwise equality, without function extensionality. -/
theorem combine_congr_pointwise {count : Nat} (coefficients : Fin count → Int)
    {first last : Fin count → Gaussian.Basic.Canonical} (equal : ∀ index, first index = last index) :
    WordCoordinates.combine coefficients first = WordCoordinates.combine coefficients last := by
  unfold WordCoordinates.combine
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [equal index]

/-- The generator values of a mixed value vector are the conjugate-linear combination of the two sides, given the
retained generator support. -/
theorem generatorValues_mixValues
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical)
    (index : Fin owner.lifted.cutBoundaryWord.alphabet.count) :
    generatorValues (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues coefficient))
            index =
      Data.Gaussian.Basic.conj (generatorValues (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
        index) +
        coefficient * generatorValues (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) index := by
  unfold generatorValues
  exact EdgeMagnitude.edgeValuation_mixValues coefficient
      (generatorSupported_all index)

/-- The chord periods of a mixed value vector are the conjugate-linear combination of the two sides. -/
theorem chordValues_mixValues
    (integral : Cut.IntegralPairing.CutBoundaryWord owner.lifted.cutBoundaryWord)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical)
    (index : Fin owner.lifted.cutBoundaryWord.alphabet.count) :
    chordValues integral (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues coefficient))
            index =
      Data.Gaussian.Basic.conj (chordValues integral (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        leftValues) index) +
        coefficient * chordValues integral (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) index := by
  unfold chordValues
  rw [combine_congr_pointwise _
    (fun column => generatorValues_mixValues coefficient column)]
  rw [combine_mixValues]

/-- The conjugate-only special case of the integer-combination linearity. -/
theorem combine_conj {count : Nat} (coefficients : Fin count → Int)
    (values : Fin count → Gaussian.Basic.Canonical) :
    WordCoordinates.combine coefficients (fun index => Data.Gaussian.Basic.conj (values index)) =
      Data.Gaussian.Basic.conj (WordCoordinates.combine coefficients values) := by
  unfold WordCoordinates.combine
  rw [Algebra.FiniteSum.Gaussian.conj_sumFin]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [Gaussian.Basic.conj_mul, Data.Gaussian.Cast.conj_intCast]

/-- The chord part of one coordinate row is conjugate-linear in the value. -/
theorem chordPart_mixValues {word : List (OrientedEdge owner.lifted.vertices.count)}
    {integral : Cut.IntegralPairing.CutBoundaryWord owner.lifted.cutBoundaryWord}
    (cut : PeriodCoordinates.ClosedCoordinates word integral)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical) :
    chordPart cut (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues coefficient))
            =
      Data.Gaussian.Basic.conj (chordPart cut (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)) +
        coefficient * chordPart cut (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) := by
  unfold chordPart
  rw [combine_congr_pointwise
    (first := fun index => WordCoordinates.combine (integral.paired index)
      (fun column => CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues coefficient)
        (OrientedEdge.map owner.lifted.cutPolygon.patch.cut.vertexLabels
          (owner.lifted.cutBoundaryWord.alphabet.generators column))))
    (last := fun index =>
      Data.Gaussian.Basic.conj (WordCoordinates.combine (integral.paired index)
        (fun column => CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues
          (OrientedEdge.map owner.lifted.cutPolygon.patch.cut.vertexLabels
            (owner.lifted.cutBoundaryWord.alphabet.generators column)))) +
      coefficient * WordCoordinates.combine (integral.paired index)
        (fun column => CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues
          (OrientedEdge.map owner.lifted.cutPolygon.patch.cut.vertexLabels
            (owner.lifted.cutBoundaryWord.alphabet.generators column))))
    _ (fun index => by
      rw [combine_congr_pointwise _
        (fun column => EdgeMagnitude.edgeValuation_mixValues
            coefficient (generatorSupported_all column))]
      rw [combine_mixValues])]
  rw [combine_mixValues]

/-- The retained residual part of one coordinate row is conjugate-linear in the value. -/
theorem residualPart_mixValues {word : List (OrientedEdge owner.lifted.vertices.count)}
    {integral : Cut.IntegralPairing.CutBoundaryWord owner.lifted.cutBoundaryWord}
    (cut : PeriodCoordinates.ClosedCoordinates word integral)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical) :
    residualPart cut (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues coefficient))
            =
      Data.Gaussian.Basic.conj (residualPart cut (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)) +
        coefficient * residualPart cut (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) := by
  unfold residualPart
  rw [combine_congr_pointwise _
    (fun column => EdgeMagnitude.edgeValuation_mixValues coefficient
        (generatorSupported_all column))]
  rw [combine_mixValues, faceValue_mixValues, Gaussian.Basic.conj_add]
  ring1

/-- The retained word value of one coordinate row is conjugate-linear in the value. -/
theorem coordinate_value_mixValues {word : List (OrientedEdge owner.lifted.vertices.count)}
    {integral : Cut.IntegralPairing.CutBoundaryWord owner.lifted.cutBoundaryWord}
    (cut : PeriodCoordinates.ClosedCoordinates word integral)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical) :
    SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues coefficient))
            word =
      Data.Gaussian.Basic.conj (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        leftValues) word) +
        coefficient * SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) word
          := by
  rw [PairedPeriodPairingBridge.coordinate_value_eq_chord_add cut _
      (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh _ edge),
    chordPart_mixValues cut coefficient,
    residualPart_mixValues cut coefficient,
    PairedPeriodPairingBridge.coordinate_value_eq_chord_add cut (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      leftValues)
      (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh _ edge),
    PairedPeriodPairingBridge.coordinate_value_eq_chord_add cut (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
      rightValues)
      (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh _ edge),
    Gaussian.Basic.conj_add]
  ring1

/-- The A word value of a mixed value vector is conjugate-linear. -/
theorem aWord_value_mixValues (cut : PeriodCoordinates.CutBank prepared) (index : Fin genus)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical) :
    SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues coefficient))
            (prepared.aWord index) =
      Data.Gaussian.Basic.conj (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        leftValues) (prepared.aWord index)) +
        coefficient * SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
          (prepared.aWord index) :=
  coordinate_value_mixValues (cut.rows.get index).a coefficient

/-- The B word value of a mixed value vector is conjugate-linear. -/
theorem bWord_value_mixValues (cut : PeriodCoordinates.CutBank prepared) (index : Fin genus)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical) :
    SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues coefficient))
            (prepared.bWord index) =
      Data.Gaussian.Basic.conj (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        leftValues) (prepared.bWord index)) +
        coefficient * SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
          (prepared.bWord index) :=
  coordinate_value_mixValues (cut.rows.get index).b coefficient

/-- Word values agree on pointwise-equal edge functions. -/
theorem wordValue_congr_pointwise {word : List (OrientedEdge owner.lifted.vertices.count)}
    {first second : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical}
    (agree : ∀ edge, first edge = second edge) :
    SewingRetraction.wordValue first word = SewingRetraction.wordValue second word := by
  induction word with
  | nil => rfl
  | cons edge rest inductionHypothesis =>
      rw [SewingRetraction.wordValue, SewingRetraction.wordValue, agree edge, inductionHypothesis]

/-- The extracted polarization of one mixed row is the cross determinant of the two word values. -/
theorem row_extract_eq (cut : PeriodCoordinates.CutBank prepared) (index : Fin genus)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    BilinearPolarization.extract (fun coefficient : Gaussian.Basic.Canonical =>
        BoundaryRibbon.area
          (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
            (EdgeMagnitude.mixValues leftValues rightValues
                coefficient)) (prepared.aWord index))
          (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
            (EdgeMagnitude.mixValues leftValues rightValues
                coefficient)) (prepared.bWord index))) =
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) (prepared.aWord index)
        *
        SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) (prepared.bWord
          index) -
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) (prepared.aWord
        index) *
        SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) (prepared.bWord
          index) := by
  rw [BilinearPolarization.extract_congr (fun coefficient => by
    rw [aWord_value_mixValues cut index coefficient,
      bWord_value_mixValues cut index coefficient])]
  rw [BilinearPolarization.extract_area
    (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) (prepared.aWord index))
    (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) (prepared.bWord index))
    (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) (prepared.aWord
      index))
    (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) (prepared.bWord
      index))]
  ring1

/-- The area pairing of the two conjugate-linear mixed words expands as the conjugate of the left pairing, the right
pairing, and a coefficient-weighted cross determinant. -/
theorem area_mixWords (aFirst aSecond bFirst bSecond coefficient : Gaussian.Basic.Canonical) :
    BoundaryRibbon.area (Data.Gaussian.Basic.conj aFirst + coefficient * aSecond)
        (Data.Gaussian.Basic.conj bFirst + coefficient * bSecond) =
      Data.Gaussian.Basic.conj (BoundaryRibbon.area aFirst bFirst) +
        (Data.Gaussian.Basic.conj coefficient * coefficient) * BoundaryRibbon.area aSecond bSecond +
        (coefficient * (aFirst * bSecond - aSecond * bFirst) -
          Data.Gaussian.Basic.conj coefficient * Data.Gaussian.Basic.conj (aFirst * bSecond - aSecond * bFirst))
            := by
  simp only [BoundaryRibbon.area, Gaussian.Basic.conj_add, Gaussian.Basic.conj_mul,
    Gaussian.Basic.conj_conj, EdgeMagnitude.conj_sub]
  ring1

/-- The cross determinant of the two ordered word readings: the row-wise `A_left * B_right - A_right * B_left` sum. -/
@[expose] def crossWedge (prepared : PeriodPrograms.Prepared paired)
    (leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3) : Gaussian :=
  FiniteSum.Fin.sumFin (fun index : Fin genus =>
    SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) (prepared.aWord index) *
        SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) (prepared.bWord
          index) -
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) (prepared.aWord
        index) *
        SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) (prepared.bWord
          index))

/-- The mixed surface residual expands as the conjugate left residual, the right residual scaled by the coefficient
norm, and the cross determinant. -/
theorem surfaceResidual_mixValues (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical) :
    (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues coefficient))
            =
      Data.Gaussian.Basic.conj ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation
        owner.lifted.mesh leftValues)) +
        (Data.Gaussian.Basic.conj coefficient * coefficient) *
          (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
            +
        (coefficient * crossWedge prepared leftValues rightValues -
          Data.Gaussian.Basic.conj coefficient * Data.Gaussian.Basic.conj (crossWedge prepared leftValues
            rightValues)) := by
  rw [← (BilinearIdentity.pairing_eq_surfaceResidual prepared) _
      (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh _ edge),
    ← (BilinearIdentity.pairing_eq_surfaceResidual prepared) _
      (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh _ edge),
    ← (BilinearIdentity.pairing_eq_surfaceResidual prepared) _
      (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh _ edge),
    Prepared.pairing, Prepared.pairing, Prepared.pairing]
  unfold crossWedge
  have expand : ∀ index : Fin genus,
      BoundaryRibbon.area
          (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
            (EdgeMagnitude.mixValues leftValues rightValues
                coefficient)) (prepared.aWord index))
          (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
            (EdgeMagnitude.mixValues leftValues rightValues
                coefficient)) (prepared.bWord index)) =
        Data.Gaussian.Basic.conj (BoundaryRibbon.area
            (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) (prepared.aWord
              index))
            (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) (prepared.bWord
              index))) +
          (Data.Gaussian.Basic.conj coefficient * coefficient) *
            BoundaryRibbon.area
              (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
                (prepared.aWord index))
              (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
                (prepared.bWord index)) +
          (coefficient *
              (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
                (prepared.aWord index) *
                  SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
                    (prepared.bWord index) -
                SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
                  (prepared.aWord index) *
                  SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
                    (prepared.bWord index)) -
            Data.Gaussian.Basic.conj coefficient *
              Data.Gaussian.Basic.conj
                (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
                  (prepared.aWord index) *
                    SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
                      (prepared.bWord index) -
                  SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
                    (prepared.aWord index) *
                    SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
                      (prepared.bWord index))) := by
    intro index
    rw [aWord_value_mixValues cut index coefficient,
      bWord_value_mixValues cut index coefficient,
      area_mixWords]
  rw [FiniteSum.Fin.sumFin_congr expand]
  conv_lhs =>
    rw [FiniteSum.Fin.sumFin_add]
    rw [FiniteSum.Fin.sumFin_add]
    rw [FiniteSum.Fin.sumFin_sub]
    rw [FiniteSum.Fin.sumFin_mul_left]
    rw [FiniteSum.Fin.sumFin_mul_left]
    rw [FiniteSum.Fin.sumFin_mul_left]
    rw [← Algebra.FiniteSum.Gaussian.conj_sumFin]
    rw [← Algebra.FiniteSum.Gaussian.conj_sumFin]

/-- The cross determinant of a reading with itself vanishes. -/
theorem crossWedge_self_eq_zero (prepared : PeriodPrograms.Prepared paired)
    (values : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3) :
    crossWedge prepared values values = 0 := by
  unfold crossWedge
  trans FiniteSum.Fin.sumFin (fun _ : Fin genus => (0 : Gaussian.Basic.Canonical))
  · apply FiniteSum.Fin.sumFin_congr
    intro index
    ring1
  · exact FiniteSum.Fin.sumFin_zero

/-- On equal readings the mixed residual is the conjugate left residual plus its coefficient-scaled self. -/
theorem surfaceResidual_mixValues_self (cut : PeriodCoordinates.CutBank prepared)
    {values : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical) :
    (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues values values coefficient)) =
      Data.Gaussian.Basic.conj ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation
        owner.lifted.mesh values)) +
        (Data.Gaussian.Basic.conj coefficient * coefficient) *
          (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh values) := by
  rw [surfaceResidual_mixValues cut coefficient, crossWedge_self_eq_zero,
    Gaussian.Basic.conj_zero]
  ring1

/-- The ordered determinant of the two readings is exactly the cross determinant of the two ordered word readings. -/
theorem bilinearResidual_edgeValuation_eq_crossWedge
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    (BilinearIdentity.bilinearResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
        (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) =
      crossWedge prepared leftValues rightValues := by
  rw [← BilinearIdentity.bilinear_formula prepared (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
    (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
    (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh leftValues edge)
    (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh rightValues edge)]
  unfold crossWedge
  apply FiniteSum.Fin.sumFin_congr
  intro index
  ring1

/-- The chord-cycle combination of the two readings, the period part of the ordered determinant. -/
@[expose] def chordWedge (cut : PeriodCoordinates.CutBank prepared)
    (first second : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin (fun index : Fin genus =>
    chordPart (cut.rows.get index).a first * chordPart (cut.rows.get index).b second -
      chordPart (cut.rows.get index).a second * chordPart (cut.rows.get index).b first)

/-- The chord-left, residual-right cross term of the ordered determinant. -/
@[expose] def chordResidualWedge (cut : PeriodCoordinates.CutBank prepared)
    (first second : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin (fun index : Fin genus =>
    chordPart (cut.rows.get index).a first * residualPart (cut.rows.get index).b second -
      chordPart (cut.rows.get index).a second * residualPart (cut.rows.get index).b first)

/-- The residual-left, chord-right cross term of the ordered determinant. -/
@[expose] def residualChordWedge (cut : PeriodCoordinates.CutBank prepared)
    (first second : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin (fun index : Fin genus =>
    residualPart (cut.rows.get index).a first * chordPart (cut.rows.get index).b second -
      residualPart (cut.rows.get index).a second * chordPart (cut.rows.get index).b first)

/-- The residual-residual term of the ordered determinant. -/
@[expose] def residualWedge (cut : PeriodCoordinates.CutBank prepared)
    (first second : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin (fun index : Fin genus =>
    residualPart (cut.rows.get index).a first * residualPart (cut.rows.get index).b second -
      residualPart (cut.rows.get index).a second * residualPart (cut.rows.get index).b first)

/-- Substituting the value-level split into the ordered determinant exhibits the chord-cycle period part and the three
retained physical/face terms. -/
theorem crossWedge_eq_chord_add (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    crossWedge prepared leftValues rightValues =
      chordWedge cut (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
          (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) +
        chordResidualWedge cut (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
          (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) +
        residualChordWedge cut (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
          (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) +
        residualWedge cut (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
          (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) := by
  unfold crossWedge chordWedge chordResidualWedge residualChordWedge residualWedge
  have expand : ∀ index : Fin genus,
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) (prepared.aWord index)
        *
          SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) (prepared.bWord
            index) -
        SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) (prepared.aWord
          index) *
          SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) (prepared.bWord
            index) =
      (chordPart (cut.rows.get index).a (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) *
            chordPart (cut.rows.get index).b (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) -
          chordPart (cut.rows.get index).a (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) *
            chordPart (cut.rows.get index).b (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)) +
        (chordPart (cut.rows.get index).a (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) *
              residualPart (cut.rows.get index).b (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) -
            chordPart (cut.rows.get index).a (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) *
              residualPart (cut.rows.get index).b (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)) +
          (residualPart (cut.rows.get index).a (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) *
                chordPart (cut.rows.get index).b (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) -
              residualPart (cut.rows.get index).a (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) *
                chordPart (cut.rows.get index).b (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)) +
            (residualPart (cut.rows.get index).a (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) *
                  residualPart (cut.rows.get index).b (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
                    -
                residualPart (cut.rows.get index).a (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) *
                  residualPart (cut.rows.get index).b (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues))
                    := by
    intro index
    rw [PairedPeriodPairingBridge.coordinate_value_eq_chord_add (cut.rows.get index).a _
        (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh leftValues edge),
      PairedPeriodPairingBridge.coordinate_value_eq_chord_add (cut.rows.get index).b _
        (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh rightValues edge),
      PairedPeriodPairingBridge.coordinate_value_eq_chord_add (cut.rows.get index).a _
        (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh rightValues edge),
      PairedPeriodPairingBridge.coordinate_value_eq_chord_add (cut.rows.get index).b _
        (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh leftValues edge)]
    ring1
  rw [FiniteSum.Fin.sumFin_congr expand]
  conv_lhs =>
    rw [FiniteSum.Fin.sumFin_add]
    rw [FiniteSum.Fin.sumFin_add]
    rw [FiniteSum.Fin.sumFin_add]

end

-- This calculation uses the original canonical conjugation operation.
section
open Data.Gaussian.Basic.Canonical

/-- The extracted polarization of the mixed surface residual is exactly the cross determinant of the two readings. -/
theorem extract_surfaceResidual_mixValues (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    BilinearPolarization.extract (fun coefficient : Gaussian.Basic.Canonical =>
        (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
          (EdgeMagnitude.mixValues leftValues rightValues
              coefficient))) =
      crossWedge prepared leftValues rightValues := by
  rw [BilinearPolarization.extract_congr (fun coefficient =>
    surfaceResidual_mixValues cut coefficient)]
  let value := fun coefficient : Gaussian.Basic.Canonical =>
    conj ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues))
      +
      (conj coefficient * coefficient) *
        (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) +
      (coefficient * crossWedge prepared leftValues rightValues -
        conj coefficient * conj (crossWedge prepared leftValues rightValues))
  change BilinearPolarization.extract value = crossWedge prepared leftValues rightValues
  have cross : value 1 - value (-1) - BilinearPolarization.imaginary *
      (value BilinearPolarization.imaginary - value (-BilinearPolarization.imaginary)) =
      (⟨4, 0⟩ : Gaussian.Basic.Canonical) * crossWedge prepared leftValues rightValues := by
    apply Gaussian.Basic.ext <;>
      simp only [value, conj, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re,
        Gaussian.Basic.sub_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.neg_re,
        Gaussian.Basic.neg_im,
        Gaussian.Basic.one_re, Gaussian.Basic.one_im, BilinearPolarization.imaginary] <;> ring1
  unfold BilinearPolarization.extract
  rw [cross, ← _root_.mul_assoc,
    show (⟨1 / 4, 0⟩ : Gaussian.Basic.Canonical) * ⟨4, 0⟩ = 1 by decide, _root_.one_mul]

end

section
open _root_.Purelib.Data.Gaussian.Basic (conj)

/-- The edge-function mix of the two edge valuations has the same surface residual as the mixed value vector. This
unifies the polarization API on edge functions with the value-parameterized aggregate API. -/
theorem surfaceResidual_mix_eq (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical) :
    (BilinearIdentity.surfaceResidual prepared) (BilinearPolarization.mix
        (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
        (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) coefficient) =
      (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues coefficient))
            := by
  rw [← (BilinearIdentity.pairing_eq_surfaceResidual prepared) _
      (BilinearPolarization.mix_reverse _ _
        (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh leftValues edge)
        (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh rightValues edge) coefficient),
    ← (BilinearIdentity.pairing_eq_surfaceResidual prepared) _
      (fun edge => CanonicalEdgeValues.edgeValuation_reverse owner.lifted.mesh _ edge),
    Prepared.pairing, Prepared.pairing]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [BilinearPolarization.word_mix, BilinearPolarization.word_mix,
    coordinate_value_mixValues (cut.rows.get index).a coefficient,
    coordinate_value_mixValues (cut.rows.get index).b coefficient]

/-- The chord part is the spanning combination of the chord-cycle periods. -/
theorem chordPart_eq_combine_chordValues
    {word : List (OrientedEdge owner.lifted.vertices.count)}
    {integral : Cut.IntegralPairing.CutBoundaryWord owner.lifted.cutBoundaryWord}
    (cut : PeriodCoordinates.ClosedCoordinates word integral)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) :
    chordPart cut value =
      WordCoordinates.combine cut.span.coefficients (chordValues integral value) :=
  rfl

/-- The chord-cycle wedge is a determinant in the chord-cycle periods, the object the period layer controls. -/
theorem chordWedge_eq_period_determinant (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    chordWedge cut (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
        (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) =
      FiniteSum.Fin.sumFin (fun index : Fin genus =>
        WordCoordinates.combine (cut.rows.get index).a.span.coefficients
            (chordValues cut.integral (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)) *
          WordCoordinates.combine (cut.rows.get index).b.span.coefficients
            (chordValues cut.integral (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)) -
        WordCoordinates.combine (cut.rows.get index).a.span.coefficients
            (chordValues cut.integral (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)) *
          WordCoordinates.combine (cut.rows.get index).b.span.coefficients
            (chordValues cut.integral (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues))) := by
  unfold chordWedge
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [chordPart_eq_combine_chordValues (cut.rows.get index).a,
    chordPart_eq_combine_chordValues (cut.rows.get index).b,
    chordPart_eq_combine_chordValues (cut.rows.get index).a,
    chordPart_eq_combine_chordValues (cut.rows.get index).b]

/-- The cross determinant is alternating in the two readings. -/
theorem crossWedge_swap (prepared : PeriodPrograms.Prepared paired)
    (leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3) :
    crossWedge prepared rightValues leftValues = -crossWedge prepared leftValues rightValues := by
  unfold crossWedge
  trans FiniteSum.Fin.sumFin (fun index : Fin genus =>
      -(SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) (prepared.aWord
        index) *
          SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) (prepared.bWord
            index) -
        SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) (prepared.aWord
          index) *
          SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) (prepared.bWord
            index)))
  · apply FiniteSum.Fin.sumFin_congr
    intro index
    ring1
  · exact FiniteSum.Fin.sumFin_neg _

/-- The chord-cycle wedge is alternating. -/
theorem chordWedge_swap (cut : PeriodCoordinates.CutBank prepared)
    (first second : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) :
    chordWedge cut second first = -chordWedge cut first second := by
  unfold chordWedge
  trans FiniteSum.Fin.sumFin (fun index : Fin genus =>
      -(chordPart (cut.rows.get index).a first * chordPart (cut.rows.get index).b second -
        chordPart (cut.rows.get index).a second * chordPart (cut.rows.get index).b first))
  · apply FiniteSum.Fin.sumFin_congr
    intro index
    ring1
  · exact FiniteSum.Fin.sumFin_neg _

/-- The chord/residual wedge is alternating. -/
theorem chordResidualWedge_swap (cut : PeriodCoordinates.CutBank prepared)
    (first second : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) :
    chordResidualWedge cut second first = -chordResidualWedge cut first second := by
  unfold chordResidualWedge
  trans FiniteSum.Fin.sumFin (fun index : Fin genus =>
      -(chordPart (cut.rows.get index).a first * residualPart (cut.rows.get index).b second -
        chordPart (cut.rows.get index).a second * residualPart (cut.rows.get index).b first))
  · apply FiniteSum.Fin.sumFin_congr
    intro index
    ring1
  · exact FiniteSum.Fin.sumFin_neg _

/-- The residual/chord wedge is alternating. -/
theorem residualChordWedge_swap (cut : PeriodCoordinates.CutBank prepared)
    (first second : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) :
    residualChordWedge cut second first = -residualChordWedge cut first second := by
  unfold residualChordWedge
  trans FiniteSum.Fin.sumFin (fun index : Fin genus =>
      -(residualPart (cut.rows.get index).a first * chordPart (cut.rows.get index).b second -
        residualPart (cut.rows.get index).a second * chordPart (cut.rows.get index).b first))
  · apply FiniteSum.Fin.sumFin_congr
    intro index
    ring1
  · exact FiniteSum.Fin.sumFin_neg _

/-- The residual wedge is alternating. -/
theorem residualWedge_swap (cut : PeriodCoordinates.CutBank prepared)
    (first second : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) :
    residualWedge cut second first = -residualWedge cut first second := by
  unfold residualWedge
  trans FiniteSum.Fin.sumFin (fun index : Fin genus =>
      -(residualPart (cut.rows.get index).a first * residualPart (cut.rows.get index).b second -
        residualPart (cut.rows.get index).a second * residualPart (cut.rows.get index).b first))
  · apply FiniteSum.Fin.sumFin_congr
    intro index
    ring1
  · exact FiniteSum.Fin.sumFin_neg _

/-- The mixed residual formula in the edge-function representation, the form the four-direction gate consumes. -/
theorem surfaceResidual_mix_eq_formula (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical) :
    (BilinearIdentity.surfaceResidual prepared) (BilinearPolarization.mix
        (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues)
        (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) coefficient) =
      conj ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        leftValues)) +
        (conj coefficient * coefficient) *
          (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues)
            +
        (coefficient * crossWedge prepared leftValues rightValues -
          conj coefficient * conj (crossWedge prepared leftValues rightValues)) := by
  rw [surfaceResidual_mix_eq cut coefficient, surfaceResidual_mixValues cut coefficient]

/-- The chord-cycle wedge vanishes on a single reading. -/
theorem chordWedge_self_eq_zero (cut : PeriodCoordinates.CutBank prepared)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) :
    chordWedge cut value value = 0 := by
  unfold chordWedge
  trans FiniteSum.Fin.sumFin (fun _ : Fin genus => (0 : Gaussian.Basic.Canonical))
  · apply FiniteSum.Fin.sumFin_congr
    intro index
    ring1
  · exact FiniteSum.Fin.sumFin_zero

/-- The chord/residual wedge vanishes on a single reading. -/
theorem chordResidualWedge_self_eq_zero (cut : PeriodCoordinates.CutBank prepared)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) :
    chordResidualWedge cut value value = 0 := by
  unfold chordResidualWedge
  trans FiniteSum.Fin.sumFin (fun _ : Fin genus => (0 : Gaussian.Basic.Canonical))
  · apply FiniteSum.Fin.sumFin_congr
    intro index
    ring1
  · exact FiniteSum.Fin.sumFin_zero

/-- The residual/chord wedge vanishes on a single reading. -/
theorem residualChordWedge_self_eq_zero (cut : PeriodCoordinates.CutBank prepared)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) :
    residualChordWedge cut value value = 0 := by
  unfold residualChordWedge
  trans FiniteSum.Fin.sumFin (fun _ : Fin genus => (0 : Gaussian.Basic.Canonical))
  · apply FiniteSum.Fin.sumFin_congr
    intro index
    ring1
  · exact FiniteSum.Fin.sumFin_zero

/-- The residual wedge vanishes on a single reading. -/
theorem residualWedge_self_eq_zero (cut : PeriodCoordinates.CutBank prepared)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) :
    residualWedge cut value value = 0 := by
  unfold residualWedge
  trans FiniteSum.Fin.sumFin (fun _ : Fin genus => (0 : Gaussian.Basic.Canonical))
  · apply FiniteSum.Fin.sumFin_congr
    intro index
    ring1
  · exact FiniteSum.Fin.sumFin_zero

/-- On equal readings the edge-function mixed residual is the conjugate residual plus its coefficient-normed self. -/
theorem surfaceResidual_mix_eq_formula_self (cut : PeriodCoordinates.CutBank prepared)
    {values : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} (coefficient :
      Gaussian.Basic.Canonical) :
    (BilinearIdentity.surfaceResidual prepared) (BilinearPolarization.mix
        (CanonicalEdgeValues.edgeValuation owner.lifted.mesh values)
        (CanonicalEdgeValues.edgeValuation owner.lifted.mesh values) coefficient) =
      conj ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh values)) +
        (conj coefficient * coefficient) *
          (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh values) := by
  rw [surfaceResidual_mix_eq cut coefficient, surfaceResidual_mixValues_self cut coefficient]

/-- Gaussian conjugation fixes one. -/
private theorem conj_one : conj (1 : Gaussian.Basic.Canonical) = 1 := by decide

/-- Gaussian conjugation fixes negative one. -/
private theorem conj_neg_one : conj (-1 : Gaussian.Basic.Canonical) = -1 := by decide

/-- Conjugation negates the retained imaginary unit. -/
private theorem conj_imaginary :
    conj (BilinearPolarization.imaginary : Gaussian.Basic.Canonical) = -BilinearPolarization.imaginary := by
  decide

/-- Conjugation sends the negative imaginary unit to the imaginary unit. -/
private theorem conj_neg_imaginary :
    conj (-BilinearPolarization.imaginary : Gaussian.Basic.Canonical) = BilinearPolarization.imaginary := by
  decide

/-- The conjugate imaginary unit multiplied by the imaginary unit equals one. -/
private theorem conj_imaginary_mul :
    (-BilinearPolarization.imaginary : Gaussian.Basic.Canonical) * BilinearPolarization.imaginary = 1 := by
  decide

/-- The imaginary unit multiplied by its negative equals one. -/
private theorem conj_neg_imaginary_mul :
    (BilinearPolarization.imaginary : Gaussian.Basic.Canonical) * (-BilinearPolarization.imaginary) = 1 := by
  decide

/-- The mixed residual at the four polarization directions, displayed in terms of the conjugate left residual and the
determinant `Cross`. -/
theorem surfaceResidual_mixValues_one (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues 1)) =
      conj ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        leftValues)) +
        (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) +
        (crossWedge prepared leftValues rightValues -
          conj (crossWedge prepared leftValues rightValues)) := by
  rw [surfaceResidual_mixValues cut 1, conj_one]
  ring1

/-- Expand the mixed surface residual in the negative real polarization direction.

Its cross contribution is the negative of the determinant minus its conjugate, while both diagonal residuals retain
coefficient one. -/
theorem surfaceResidual_mixValues_negOne (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues (-1))) =
      conj ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        leftValues)) +
        (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) -
        (crossWedge prepared leftValues rightValues -
          conj (crossWedge prepared leftValues rightValues)) := by
  rw [surfaceResidual_mixValues cut (-1), conj_neg_one]
  ring1

/-- Expand the mixed surface residual in the positive imaginary polarization direction.

The cross contribution is the imaginary unit times the determinant plus its conjugate. -/
theorem surfaceResidual_mixValues_im (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues
            BilinearPolarization.imaginary)) =
      conj ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        leftValues)) +
        (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) +
        (BilinearPolarization.imaginary * crossWedge prepared leftValues rightValues +
          BilinearPolarization.imaginary * conj (crossWedge prepared leftValues rightValues)) := by
  rw [surfaceResidual_mixValues cut BilinearPolarization.imaginary, conj_imaginary,
    conj_imaginary_mul]
  ring1

/-- Expand the mixed surface residual in the negative imaginary polarization direction.

The cross contribution negates the positive imaginary contribution while retaining the same diagonal residuals. -/
theorem surfaceResidual_mixValues_negIm (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues
            (-BilinearPolarization.imaginary))) =
      conj ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        leftValues)) +
        (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) -
        (BilinearPolarization.imaginary * crossWedge prepared leftValues rightValues +
          BilinearPolarization.imaginary * conj (crossWedge prepared leftValues rightValues)) := by
  rw [surfaceResidual_mixValues cut (-BilinearPolarization.imaginary), conj_neg_imaginary,
    conj_neg_imaginary_mul]
  ring1

/-- The `c = 1` and `c = -1` mixed residuals average to the conjugate left residual plus the right residual. -/
theorem surfaceResidual_mixValues_one_add_negOne (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues 1)) +
      (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues (-1))) =
      2 * (conj ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        leftValues)) +
        (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues))
          := by
  rw [surfaceResidual_mixValues_one cut, surfaceResidual_mixValues_negOne cut]
  ring1

/-- Their difference is twice the antisymmetric part of the determinant. -/
theorem surfaceResidual_mixValues_one_sub_negOne (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues 1)) -
      (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues (-1))) =
      2 * (crossWedge prepared leftValues rightValues -
        conj (crossWedge prepared leftValues rightValues)) := by
  rw [surfaceResidual_mixValues_one cut, surfaceResidual_mixValues_negOne cut]
  ring1

/-- The `c = i` and `c = -i` mixed residuals average to the same diagonal. -/
theorem surfaceResidual_mixValues_im_add_negIm (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues
            BilinearPolarization.imaginary)) +
      (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues
            (-BilinearPolarization.imaginary))) =
      2 * (conj ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        leftValues)) +
        (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues))
          := by
  rw [surfaceResidual_mixValues_im cut, surfaceResidual_mixValues_negIm cut]
  ring1

/-- Their difference is twice the symmetric part of the determinant. -/
theorem surfaceResidual_mixValues_im_sub_negIm (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues
            BilinearPolarization.imaginary)) -
      (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues
            (-BilinearPolarization.imaginary))) =
      2 * (BilinearPolarization.imaginary * crossWedge prepared leftValues rightValues +
        BilinearPolarization.imaginary * conj (crossWedge prepared leftValues rightValues)) := by
  rw [surfaceResidual_mixValues_im cut, surfaceResidual_mixValues_negIm cut]
  ring1

/-- The four mixed residuals isolate four times the cross determinant, the explicit polarization identity consumed by
the physical-boundary gate. -/
theorem surfaceResidual_mixValues_extract_combination (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues 1)) -
      (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues (-1)))) -
      BilinearPolarization.imaginary *
        ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
          (EdgeMagnitude.mixValues leftValues rightValues
              BilinearPolarization.imaginary)) -
        (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
          (EdgeMagnitude.mixValues leftValues rightValues
              (-BilinearPolarization.imaginary)))) =
      4 * crossWedge prepared leftValues rightValues := by
  have polar := extract_surfaceResidual_mixValues cut
    (leftValues := leftValues) (rightValues := rightValues)
  unfold BilinearPolarization.extract at polar
  have scaled := congrArg (fun value : Gaussian.Basic.Canonical => (⟨4, 0⟩ : Gaussian.Basic.Canonical) * value) polar
  rw [← _root_.mul_assoc,
    show (⟨4, 0⟩ : Gaussian.Basic.Canonical) * (⟨1 / 4, 0⟩ : Gaussian.Basic.Canonical) = 1 by decide,
    _root_.one_mul] at scaled
  exact scaled

/-- The parallelogram law for the mixed residual: the two opposite-sum pairs agree. The four directional values
therefore have only three degrees of freedom, matching `(left residual, right residual, determinant)`. -/
theorem surfaceResidual_mixValues_parallelogram (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues 1)) +
      (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues (-1))) =
      (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues
            BilinearPolarization.imaginary)) +
      (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues
            (-BilinearPolarization.imaginary))) := by
  rw [surfaceResidual_mixValues_one_add_negOne cut, surfaceResidual_mixValues_im_add_negIm cut]

/-- The square of the retained Gaussian imaginary unit is negative one. -/
private theorem imaginary_mul :
    (BilinearPolarization.imaginary : Gaussian.Basic.Canonical) * BilinearPolarization.imaginary = -1 := by
  decide

/-- Multiplying a sum of two imaginary multiples by the imaginary unit negates their sum. -/
private theorem imaginary_mul_add (first last : Gaussian.Basic.Canonical) :
    BilinearPolarization.imaginary *
        (BilinearPolarization.imaginary * first + BilinearPolarization.imaginary * last) =
      -(first + last) := by
  rw [← _root_.mul_add, ← _root_.mul_assoc, imaginary_mul]
  ring1

/-- The conjugate polarization combination recovers the conjugate determinant, the companion of
`surfaceResidual_mixValues_extract_combination`. -/
theorem surfaceResidual_mixValues_extract_combination_conj (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3} :
    ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues 1)) -
      (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues (-1)))) +
      BilinearPolarization.imaginary *
        ((BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
          (EdgeMagnitude.mixValues leftValues rightValues
              BilinearPolarization.imaginary)) -
        (BilinearIdentity.surfaceResidual prepared) (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
          (EdgeMagnitude.mixValues leftValues rightValues
              (-BilinearPolarization.imaginary)))) =
      -4 * conj (crossWedge prepared leftValues rightValues) := by
  rw [surfaceResidual_mixValues_one_sub_negOne cut, surfaceResidual_mixValues_im_sub_negIm cut]
  have rearrange : BilinearPolarization.imaginary *
        (2 * (BilinearPolarization.imaginary * crossWedge prepared leftValues rightValues +
          BilinearPolarization.imaginary * conj (crossWedge prepared leftValues rightValues))) =
      2 * (BilinearPolarization.imaginary *
        (BilinearPolarization.imaginary * crossWedge prepared leftValues rightValues +
          BilinearPolarization.imaginary * conj (crossWedge prepared leftValues rightValues))) := by
    ring1
  rw [rearrange, imaginary_mul_add]
  ring1

/-- The base A/B pairing is bounded by the retained word-value magnitudes, one factor of the mesh-edge count per row. -/
theorem pairing_normSq_le (prepared : PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) {bound : Fraction.Rational}
    (nonnegative : 0 ≤ bound)
    (aBound : ∀ index : Fin genus, normSq (SewingRetraction.wordValue value (prepared.aWord index)) ≤ bound)
    (bBound : ∀ index : Fin genus, normSq (SewingRetraction.wordValue value (prepared.bWord index)) ≤ bound) :
    normSq (prepared.pairing value) ≤ (genus : Fraction.Rational) ^ 2 * (4 * bound ^ 2) := by
  rw [Prepared.pairing]
  apply Indexed.normSq_sumFin_le
  intro index
  have leftScale : 4 * normSq (SewingRetraction.wordValue value (prepared.aWord index)) ≤ 4 * bound :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (aBound index) (by decide)
  calc
    normSq (BoundaryRibbon.area (SewingRetraction.wordValue value (prepared.aWord index))
        (SewingRetraction.wordValue value (prepared.bWord index)))
      ≤ 4 * normSq (SewingRetraction.wordValue value (prepared.aWord index)) *
          normSq (SewingRetraction.wordValue value (prepared.bWord index)) :=
        BoundaryRibbon.area_bound _ _
    _ ≤ (4 * bound) * bound :=
      Fraction.Order.Arithmetic.mul_le_mul_direct leftScale (bBound index)
        (Gaussian.Norm.Basic.normSq_nonneg _)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) nonnegative)
    _ = 4 * bound ^ 2 := by ring1

/-- The mixed A word value is bounded by the two readings' A word magnitudes. -/
theorem aWord_mixValues_magnitude (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical) {leftMagnitude rightMagnitude : Fraction.Rational}
    (leftBound : ∀ index : Fin genus, normSq (SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) (prepared.aWord index)) ≤ leftMagnitude)
    (rightBound : ∀ index : Fin genus, normSq (SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) (prepared.aWord index)) ≤ rightMagnitude) :
    ∀ index : Fin genus, normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues coefficient))
            (prepared.aWord index)) ≤
      2 * (leftMagnitude + normSq coefficient * rightMagnitude) := by
  intro index
  rw [aWord_value_mixValues cut index coefficient]
  exact (EdgeMagnitude.normSq_conj_add_mul _ _ coefficient).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (leftBound index)
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (rightBound index)
          (Gaussian.Norm.Basic.normSq_nonneg coefficient)))
      (by decide : (0 : Fraction.Rational) ≤ 2))

/-- The mixed B word value is bounded by the two readings' B word magnitudes. -/
theorem bWord_mixValues_magnitude (cut : PeriodCoordinates.CutBank prepared)
    {leftValues rightValues : Fin owner.lifted.mesh.triangles.length → PrimitiveSewing.PrimitiveValues 3}
    (coefficient : Gaussian.Basic.Canonical) {leftMagnitude rightMagnitude : Fraction.Rational}
    (leftBound : ∀ index : Fin genus, normSq (SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation owner.lifted.mesh leftValues) (prepared.bWord index)) ≤ leftMagnitude)
    (rightBound : ∀ index : Fin genus, normSq (SewingRetraction.wordValue
      (CanonicalEdgeValues.edgeValuation owner.lifted.mesh rightValues) (prepared.bWord index)) ≤ rightMagnitude) :
    ∀ index : Fin genus, normSq (SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation owner.lifted.mesh
        (EdgeMagnitude.mixValues leftValues rightValues coefficient))
            (prepared.bWord index)) ≤
      2 * (leftMagnitude + normSq coefficient * rightMagnitude) := by
  intro index
  rw [bWord_value_mixValues cut index coefficient]
  exact (EdgeMagnitude.normSq_conj_add_mul _ _ coefficient).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct (leftBound index)
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (rightBound index)
          (Gaussian.Norm.Basic.normSq_nonneg coefficient)))
      (by decide : (0 : Fraction.Rational) ≤ 2))

/-- Sharper pairing bound: linear in the index count and retaining every row's squared area norm. -/
theorem pairing_normSq_le_sum (prepared : PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) :
    normSq (prepared.pairing value) ≤ (genus : Fraction.Rational) * FiniteSum.Fin.sumFin (fun index : Fin genus =>
      normSq (BoundaryRibbon.area (SewingRetraction.wordValue value (prepared.aWord index))
        (SewingRetraction.wordValue value (prepared.bWord index)))) := by
  rw [Prepared.pairing]
  exact Indexed.normSq_sumFin_le_sum _

/-- The displayed row-sum pairing bound: `genus` times the sum of the row areas' squared-norm bounds. This retains every
row, so it is never worse than the maximum-based bound and is strictly sharper when rows differ. -/
@[expose] def pairingRowBound (prepared : PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) : Fraction.Rational :=
  (genus : Fraction.Rational) * FiniteSum.Fin.sumFin (fun index : Fin genus =>
    4 * normSq (SewingRetraction.wordValue value (prepared.aWord index)) *
      normSq (SewingRetraction.wordValue value (prepared.bWord index)))

/-- Sharper pairing bound in terms of the A/B word-value norms: the row areas are bounded by `4 * |A|^2 * |B|^2` and the
rows are summed, so small rows are not paid at the maximum. -/
theorem pairing_normSq_le_wordNorms (prepared : PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) :
    normSq (prepared.pairing value) ≤ pairingRowBound prepared value := by
  refine (pairing_normSq_le_sum prepared value).trans ?_
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
  · apply Order.IndexedBudget.sumFin_le
    intro index
    exact BoundaryRibbon.area_bound _ _
  · exact Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus)

/-- Strict form of the row-sum pairing bound, with one unit of slack. -/
theorem pairing_lt_rowBound (prepared : PeriodPrograms.Prepared paired)
    (value : OrientedEdge owner.lifted.vertices.count → Gaussian.Basic.Canonical) :
    normSq (prepared.pairing value) < pairingRowBound prepared value + 1 :=
  (pairing_normSq_le_wordNorms prepared value).trans_lt (by
    have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
      (by decide : (0 : Fraction.Rational) < 1) (pairingRowBound prepared value)
    simpa only [add_zero] using shifted)

end

end Purelib.Topology.Surface.Chord.ValueChordLinearity
