module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Energy.Polygon

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Sewing.CutIntersection
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Topology.Surface.Cut.CoordinatePairing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank)

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)

open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue faceValue)

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

open _root_.Purelib.Data.Gaussian.Basic (conj)

open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing (SpanningCoordinates)

open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (ClosedCoordinates)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero)

@[expose] public section

/-!
# The ordered A/B pairing as a cut-coordinate wedge contraction

`ClosedCoordinates.value_eq` writes each corrected A/B word as an integer
combination of the retained cut generators plus a signed face correction.
Composing that with the area-level Stokes identification
(`area_combine_eq_contract`) turns each row's Gaussian area pairing into the
integer wedge contraction of the two coordinate vectors against the energy
primitives, plus explicit face cross terms. This is the finite bridge that
carries the ordered A/B pairing to the cut crossing/period layers.
-/

namespace Purelib.Riemann.Periods.PairedPeriodPairingBridge

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

open Purelib.Topology in
open Purelib.Data in
/-- Read the valuation on the actual cut generators after their retained vertex relabeling. -/
def generatorValues (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    Fin lifted.cutBoundaryWord.alphabet.count → Gaussian :=
  fun index => value (Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
    (lifted.cutBoundaryWord.alphabet.generators index))

open Purelib.Curves in
/-- Compute the antisymmetric integer wedge of one retained A/B coordinate row pair. -/
def coordinateWedge (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index : Fin
  genus) :
    Fin lifted.cutBoundaryWord.alphabet.count → Fin lifted.cutBoundaryWord.alphabet.count → Int :=
  fun row column =>
    (cut.rows.get index).a.coordinates.totals row * (cut.rows.get index).b.coordinates.totals column -
    (cut.rows.get index).b.coordinates.totals row * (cut.rows.get index).a.coordinates.totals column

open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- Split one corrected A/B area into its integer coordinate-wedge contraction and three face cross terms.

The valuation is antisymmetric and both retained coordinate rows include their signed face corrections. The contraction
uses the energy primitive of the same generator values. -/
theorem row_pairing_eq_contract (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared)
  (index : Fin genus)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    Path.BoundaryRibbon.area (Surface.Sewing.SewingRetraction.wordValue value (prepared.aWord index))
        (Surface.Sewing.SewingRetraction.wordValue value (prepared.bWord index)) =
      Surface.Word.Pairing.contract (fun row column =>
          (cut.rows.get index).a.coordinates.totals row * (cut.rows.get index).b.coordinates.totals column -
          (cut.rows.get index).b.coordinates.totals row * (cut.rows.get index).a.coordinates.totals column)
        (fun column => Energy.Polygon.energyPrimitivePoint (generatorValues value column)) +
      Path.BoundaryRibbon.area
        (Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (cut.rows.get index).a.coordinates.totals
          (generatorValues value))
        (Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
          index).b.route.correction) +
      Path.BoundaryRibbon.area
        (Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
          index).a.route.correction)
        (Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (cut.rows.get index).b.coordinates.totals
          (generatorValues value)) +
      Path.BoundaryRibbon.area
        (Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
          index).a.route.correction)
        (Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
          index).b.route.correction) := by
  unfold generatorValues
  rw [(cut.rows.get index).a.value_eq value anti, (cut.rows.get index).b.value_eq value anti]
  simp only [Path.IncrementArea.area_add_left, Path.IncrementArea.area_add_right]
  rw [Surface.Cut.CoordinatePairing.area_combine_eq_contract]
  ring1

end Purelib.Riemann.Periods.PairedPeriodPairingBridge

namespace Purelib.Riemann.Periods.PairedPeriodPairingBridge

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- The ordered surface residual is the finite sum of coordinate-wedge contractions and retained face terms.

Apply the row identity to the actual prepared A/B words under the same antisymmetric edge valuation. -/
theorem surfaceResidual_eq_contract_sum (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank
  prepared)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared value) =
      FiniteSum.Fin.sumFin (fun index : Fin genus =>
        Surface.Word.Pairing.contract (coordinateWedge cut index)
          (fun column => Energy.Polygon.energyPrimitivePoint (generatorValues value column)) +
        Path.BoundaryRibbon.area
          (Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (cut.rows.get index).a.coordinates.totals
            (generatorValues value))
          (Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
            index).b.route.correction) +
        Path.BoundaryRibbon.area
          (Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
            index).a.route.correction)
          (Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (cut.rows.get index).b.coordinates.totals
            (generatorValues value)) +
        Path.BoundaryRibbon.area
          (Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
            index).a.route.correction)
          (Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
            index).b.route.correction)) := by
  rw [← (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.pairing_eq_surfaceResidual prepared value anti),
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared.pairing]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  exact row_pairing_eq_contract cut index value anti

end Purelib.Riemann.Periods.PairedPeriodPairingBridge

namespace Purelib.Riemann.Periods.PairedPeriodPairingBridge

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

open Purelib.Topology in
open Purelib.Data in
/-- Contract each retained integer crossing row with the exact cut-generator valuation. -/
def chordValues (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    Fin lifted.cutBoundaryWord.alphabet.count → Gaussian :=
  fun index => Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (integral.paired index) (generatorValues
    value)

section
open Purelib.Curves
open Purelib.Topology
open Purelib.Data
/-- Compute a coordinate row's spanning combination of the retained chord-cycle values. -/
def chordPart {word : List (OrientedEdge lifted.vertices.count)}
    {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
    (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates word integral)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine cut.span.coefficients
    (fun index => Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine (integral.paired index)
      (fun column => value (Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
        (lifted.cutBoundaryWord.alphabet.generators column))))

/-- Compute a coordinate row's retained physical-generator contribution plus its signed face correction. -/
def residualPart {word : List (OrientedEdge lifted.vertices.count)}
    {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
    (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates word integral)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine cut.span.physical
    (fun index => value (Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
      (lifted.cutBoundaryWord.alphabet.generators index))) +
    Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value cut.route.correction

/-- An antisymmetric word valuation splits into its spanning chord part and retained physical/face residual.

The word uses its exact cut-coordinate and spanning certificates. -/
theorem coordinate_value_eq_chord_add {word : List (OrientedEdge lifted.vertices.count)}
    {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
    (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates word integral)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    Surface.Sewing.SewingRetraction.wordValue value word = chordPart cut value + residualPart cut value := by
  rw [cut.value_eq value anti, cut.span.value_eq]
  unfold chordPart residualPart
  ring1

end

open Purelib.Curves
open Purelib.Integration
open Purelib.Topology
open Purelib.Data
/-- Split one A/B area into chord pairing and all three chord/residual cross terms.

Both word values use their retained spanning decompositions under the same antisymmetric valuation. -/
theorem row_pairing_eq_chord_add (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared)
  (index : Fin genus)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    Path.BoundaryRibbon.area (Surface.Sewing.SewingRetraction.wordValue value (prepared.aWord index))
        (Surface.Sewing.SewingRetraction.wordValue value (prepared.bWord index)) =
      Path.BoundaryRibbon.area (chordPart (cut.rows.get index).a value)
          (chordPart (cut.rows.get index).b value) +
      Path.BoundaryRibbon.area (chordPart (cut.rows.get index).a value)
          (residualPart (cut.rows.get index).b value) +
      Path.BoundaryRibbon.area (residualPart (cut.rows.get index).a value)
          (chordPart (cut.rows.get index).b value) +
      Path.BoundaryRibbon.area (residualPart (cut.rows.get index).a value)
          (residualPart (cut.rows.get index).b value) := by
  rw [coordinate_value_eq_chord_add (cut.rows.get index).a value anti,
    coordinate_value_eq_chord_add (cut.rows.get index).b value anti]
  simp only [Path.IncrementArea.area_add_left, Path.IncrementArea.area_add_right]
  ring1

/-- The chord area of one A/B row is its spanning-coefficient wedge contracted against chord energy primitives.

The chord values and coefficient rows use the same retained integral pairing. -/
theorem chord_pairing_eq_contract (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared)
  (index : Fin genus)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    Path.BoundaryRibbon.area (chordPart (cut.rows.get index).a value)
        (chordPart (cut.rows.get index).b value) =
      Surface.Word.Pairing.contract (fun row column =>
          (cut.rows.get index).a.span.coefficients row * (cut.rows.get index).b.span.coefficients column -
          (cut.rows.get index).b.span.coefficients row * (cut.rows.get index).a.span.coefficients column)
        (fun column => Energy.Polygon.energyPrimitivePoint
          (chordValues cut.integral value column)) := by
  unfold chordPart chordValues generatorValues
  rw [Surface.Cut.CoordinatePairing.area_combine_eq_contract]

end Purelib.Riemann.Periods.PairedPeriodPairingBridge

namespace Purelib.Riemann.Periods.PairedPeriodPairingBridge

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Integration in
open Purelib.Data in
/-- The ordered surface residual is the row sum of chord areas and all retained physical/face cross terms.

The same prepared words and antisymmetric edge valuation determine each row. -/
theorem surfaceResidual_eq_chord_sum (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank
  prepared)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.surfaceResidual prepared value) =
      FiniteSum.Fin.sumFin (fun index : Fin genus =>
        Path.BoundaryRibbon.area (chordPart (cut.rows.get index).a value)
            (chordPart (cut.rows.get index).b value) +
        Path.BoundaryRibbon.area (chordPart (cut.rows.get index).a value)
            (residualPart (cut.rows.get index).b value) +
        Path.BoundaryRibbon.area (residualPart (cut.rows.get index).a value)
            (chordPart (cut.rows.get index).b value) +
        Path.BoundaryRibbon.area (residualPart (cut.rows.get index).a value)
            (residualPart (cut.rows.get index).b value)) := by
  rw [← (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.pairing_eq_surfaceResidual prepared value anti),
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared.pairing]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  exact row_pairing_eq_chord_add cut index value anti

end Purelib.Riemann.Periods.PairedPeriodPairingBridge

namespace Purelib.Riemann.Periods.PairedPeriodPairingBridge

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Topology in
/-- Compute a retained coordinate row's spanning combination of the integer crossing rows. -/
def pairedPart {word : List (OrientedEdge lifted.vertices.count)}
    {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
    (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates word integral) : Fin
      lifted.cutBoundaryWord.alphabet.count → Int :=
  fun column => FiniteSum.Fin.sumFin (fun index => cut.span.coefficients index * integral.paired index column)

open Purelib.Curves in
/-- Split the coordinate wedge into paired, two mixed and physical wedge terms.

The exact spanning equations decompose each A/B coordinate into its crossing-supported and physical components. -/
theorem coordinateWedge_eq_paired_add (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank
  prepared) (index : Fin genus)
    (row column : Fin lifted.cutBoundaryWord.alphabet.count) :
    coordinateWedge cut index row column =
      (pairedPart (cut.rows.get index).a row * pairedPart (cut.rows.get index).b column -
        pairedPart (cut.rows.get index).b row * pairedPart (cut.rows.get index).a column) +
      (pairedPart (cut.rows.get index).a row * (cut.rows.get index).b.span.physical column -
        pairedPart (cut.rows.get index).b row * (cut.rows.get index).a.span.physical column) +
      ((cut.rows.get index).a.span.physical row * pairedPart (cut.rows.get index).b column -
        (cut.rows.get index).b.span.physical row * pairedPart (cut.rows.get index).a column) +
      ((cut.rows.get index).a.span.physical row * (cut.rows.get index).b.span.physical column -
        (cut.rows.get index).b.span.physical row * (cut.rows.get index).a.span.physical column) := by
  unfold coordinateWedge pairedPart
  rw [(cut.rows.get index).a.span.equation row, (cut.rows.get index).b.span.equation column,
    (cut.rows.get index).b.span.equation row, (cut.rows.get index).a.span.equation column]
  ring1

end Purelib.Riemann.Periods.PairedPeriodPairingBridge

namespace Purelib.Riemann.Periods.PairedPeriodPairingBridge

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

section
open Purelib.Curves
/-- Compute the antisymmetric wedge of the two paired coordinate components. -/
def pairedWedge (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index : Fin genus)
  :
    Fin lifted.cutBoundaryWord.alphabet.count → Fin lifted.cutBoundaryWord.alphabet.count → Int :=
  fun row column =>
    pairedPart (cut.rows.get index).a row * pairedPart (cut.rows.get index).b column -
    pairedPart (cut.rows.get index).b row * pairedPart (cut.rows.get index).a column

/-- Compute the antisymmetric wedge of the two physical coordinate components. -/
def physicalWedge (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index : Fin
  genus) :
    Fin lifted.cutBoundaryWord.alphabet.count → Fin lifted.cutBoundaryWord.alphabet.count → Int :=
  fun row column =>
    (cut.rows.get index).a.span.physical row * (cut.rows.get index).b.span.physical column -
    (cut.rows.get index).b.span.physical row * (cut.rows.get index).a.span.physical column

/-- Compute the A/B wedge with a paired row and physical column. -/
def mixedWedge (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index : Fin genus)
  :
    Fin lifted.cutBoundaryWord.alphabet.count → Fin lifted.cutBoundaryWord.alphabet.count → Int :=
  fun row column =>
    pairedPart (cut.rows.get index).a row * (cut.rows.get index).b.span.physical column -
    pairedPart (cut.rows.get index).b row * (cut.rows.get index).a.span.physical column

/-- Compute the A/B wedge with a physical row and paired column. -/
def mixedWedge' (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index : Fin genus)
  :
    Fin lifted.cutBoundaryWord.alphabet.count → Fin lifted.cutBoundaryWord.alphabet.count → Int :=
  fun row column =>
    (cut.rows.get index).a.span.physical row * pairedPart (cut.rows.get index).b column -
    (cut.rows.get index).b.span.physical row * pairedPart (cut.rows.get index).a column

end

open Purelib.Algebra in
open Purelib.Topology in
/-- Pointwise equal integer matrices have equal contractions against the same primitive values. -/
private theorem contract_congr_pointwise {count : Nat} {first last : Fin count → Fin count → Int}
    (values : Fin count → PrimitivePoint) (equal : ∀ row column, first row column = last row column) :
    Surface.Word.Pairing.contract first values = Surface.Word.Pairing.contract last values := by
  unfold Surface.Word.Pairing.contract
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply FiniteSum.Fin.sumFin_congr
  intro column
  rw [equal]

open Purelib.Topology in
/-- Contracting the sum of four integer matrices gives the sum of their contractions. -/
private theorem contract_add_four {count : Nat} (first second third fourth : Fin count → Fin count → Int)
    (values : Fin count → PrimitivePoint) :
    Surface.Word.Pairing.contract (fun row column => first row column + second row column +
        third row column + fourth row column) values =
      Surface.Word.Pairing.contract first values + Surface.Word.Pairing.contract second values +
        Surface.Word.Pairing.contract third values + Surface.Word.Pairing.contract fourth values := by
  rw [Surface.Word.Pairing.contract_add, Surface.Word.Pairing.contract_add, Surface.Word.Pairing.contract_add]

open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- Split a coordinate-wedge contraction into paired, both mixed and physical contractions.

Every term is evaluated against the same chord-cycle energy primitives; no physical or face component is silently
discarded. -/
theorem pairing_contract_eq_paired_add (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank
  prepared) (index : Fin genus)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) :
    Surface.Word.Pairing.contract (coordinateWedge cut index)
        (fun column => Energy.Polygon.energyPrimitivePoint
          (chordValues cut.integral value column)) =
      Surface.Word.Pairing.contract (pairedWedge cut index)
          (fun column => Energy.Polygon.energyPrimitivePoint
            (chordValues cut.integral value column)) +
      Surface.Word.Pairing.contract (mixedWedge cut index)
          (fun column => Energy.Polygon.energyPrimitivePoint
            (chordValues cut.integral value column)) +
      Surface.Word.Pairing.contract (mixedWedge' cut index)
          (fun column => Energy.Polygon.energyPrimitivePoint
            (chordValues cut.integral value column)) +
      Surface.Word.Pairing.contract (physicalWedge cut index)
          (fun column => Energy.Polygon.energyPrimitivePoint
            (chordValues cut.integral value column)) := by
  rw [contract_congr_pointwise (first := coordinateWedge cut index)
    (last := fun row column => pairedWedge cut index row column + mixedWedge cut index row column +
      mixedWedge' cut index row column + physicalWedge cut index row column) _ (fun row column => by
    unfold pairedWedge mixedWedge mixedWedge' physicalWedge
    exact coordinateWedge_eq_paired_add cut index row column)]
  exact contract_add_four _ _ _ _ _

end Purelib.Riemann.Periods.PairedPeriodPairingBridge

namespace Purelib.Riemann.Periods.PairedPeriodPairingBridge

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Topology in
/-- The paired coordinate component vanishes at a one-sided physical generator. -/
theorem pairedPart_eq_zero {word : List (OrientedEdge lifted.vertices.count)}
    {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
    (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates word integral)
    (column : Fin lifted.cutBoundaryWord.alphabet.count)
    (side : lifted.cutBoundaryWord.alphabet.oneSided column = true) :
    pairedPart cut column = 0 := by
  unfold pairedPart
  apply (FiniteSum.Fin.sumFin_congr ?_).trans FiniteSum.Fin.sumFin_zero
  intro index
  rw [integral.paired_eq, side, Bool.or_true, if_pos rfl]
  ring1

open Purelib.Curves
/-- The A-row physical component equals its total on one-sided generators and vanishes elsewhere. -/
theorem physicalPart_eq (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index :
  Fin genus)
    (column : Fin lifted.cutBoundaryWord.alphabet.count) :
    (cut.rows.get index).a.span.physical column =
      if lifted.cutBoundaryWord.alphabet.oneSided column then
        (cut.rows.get index).a.coordinates.totals column else 0 :=
  (cut.rows.get index).a.span.physical_eq column

/-- The paired wedge vanishes when both generator indices are one-sided. -/
theorem pairedWedge_eq_zero (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index
  : Fin genus)
    (row column : Fin lifted.cutBoundaryWord.alphabet.count)
    (rowSide : lifted.cutBoundaryWord.alphabet.oneSided row = true)
    (columnSide : lifted.cutBoundaryWord.alphabet.oneSided column = true) :
    pairedWedge cut index row column = 0 := by
  unfold pairedWedge
  rw [pairedPart_eq_zero (cut.rows.get index).a row rowSide,
    pairedPart_eq_zero (cut.rows.get index).b row rowSide,
    pairedPart_eq_zero (cut.rows.get index).a column columnSide,
    pairedPart_eq_zero (cut.rows.get index).b column columnSide]
  ring1

end Purelib.Riemann.Periods.PairedPeriodPairingBridge

namespace Purelib.Riemann.Periods.PairedPeriodPairingBridge

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

open Purelib.Curves in
open Purelib.Topology in
/-- At a paired generator the paired component equals the exact retained coordinate total. -/
theorem pairedPart_eq_totals {word : List (OrientedEdge lifted.vertices.count)}
    {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
    (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates word integral)
    (column : Fin lifted.cutBoundaryWord.alphabet.count)
    (side : lifted.cutBoundaryWord.alphabet.oneSided column = false) :
    pairedPart cut column = cut.coordinates.totals column := by
  have equation := cut.span.equation column
  have physical : cut.span.physical column = 0 := by
    rw [cut.span.physical_eq, side]
    rfl
  unfold pairedPart
  rw [equation, physical, add_zero]

open Purelib.Algebra in
open Purelib.Topology in
open Purelib.Data in
/-- All chord-cycle values vanish if the generator valuation vanishes on every paired column. -/
theorem chordValues_eq_zero_of_paired_zero
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
    (zero : ∀ column, lifted.cutBoundaryWord.alphabet.oneSided column = false →
      generatorValues value column = 0)
    (index : Fin lifted.cutBoundaryWord.alphabet.count) :
    chordValues integral value index = 0 := by
  unfold chordValues Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine
  apply (FiniteSum.Fin.sumFin_congr ?_).trans FiniteSum.Fin.sumFin_zero
  intro column
  by_cases side : lifted.cutBoundaryWord.alphabet.oneSided column
  · rw [integral.paired_eq, side, Bool.or_true, if_pos rfl]
    ring1
  · rw [zero column (Bool.eq_false_iff.mpr side)]
    ring1

end Purelib.Riemann.Periods.PairedPeriodPairingBridge

namespace Purelib.Riemann.Periods.PairedPeriodPairingBridge

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

open Purelib.Curves
/-- The A-row physical component vanishes on a paired generator. -/
theorem physical_eq_zero_of_paired (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared)
  (index : Fin genus)
    (column : Fin lifted.cutBoundaryWord.alphabet.count)
    (side : lifted.cutBoundaryWord.alphabet.oneSided column = false) :
    (cut.rows.get index).a.span.physical column = 0 := by
  rw [(cut.rows.get index).a.span.physical_eq, side]
  rfl

/-- The B-row physical component vanishes on a paired generator. -/
theorem physical_b_eq_zero_of_paired (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank
  prepared) (index : Fin genus)
    (column : Fin lifted.cutBoundaryWord.alphabet.count)
    (side : lifted.cutBoundaryWord.alphabet.oneSided column = false) :
    (cut.rows.get index).b.span.physical column = 0 := by
  rw [(cut.rows.get index).b.span.physical_eq, side]
  rfl

/-- The paired-row mixed wedge vanishes on a one-sided physical row. -/
theorem mixedWedge_eq_zero_of_row_oneSided (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank
  prepared) (index : Fin genus)
    (row column : Fin lifted.cutBoundaryWord.alphabet.count)
    (side : lifted.cutBoundaryWord.alphabet.oneSided row = true) :
    mixedWedge cut index row column = 0 := by
  unfold mixedWedge
  rw [pairedPart_eq_zero (cut.rows.get index).a row side,
    pairedPart_eq_zero (cut.rows.get index).b row side]
  ring1

/-- The paired-column mixed wedge vanishes on a one-sided physical column. -/
theorem mixedWedge'_eq_zero_of_column_oneSided (cut :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index : Fin genus)
    (row column : Fin lifted.cutBoundaryWord.alphabet.count)
    (side : lifted.cutBoundaryWord.alphabet.oneSided column = true) :
    mixedWedge' cut index row column = 0 := by
  unfold mixedWedge'
  rw [pairedPart_eq_zero (cut.rows.get index).b column side,
    pairedPart_eq_zero (cut.rows.get index).a column side]
  ring1

/-- The physical wedge vanishes on a paired row. -/
theorem physicalWedge_eq_zero_of_row_paired (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank
  prepared) (index : Fin genus)
    (row column : Fin lifted.cutBoundaryWord.alphabet.count)
    (side : lifted.cutBoundaryWord.alphabet.oneSided row = false) :
    physicalWedge cut index row column = 0 := by
  unfold physicalWedge
  rw [physical_eq_zero_of_paired cut index row side, physical_b_eq_zero_of_paired cut index row side]
  ring1

end Purelib.Riemann.Periods.PairedPeriodPairingBridge

namespace Purelib.Riemann.Periods.PairedPeriodPairingBridge

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

open Purelib.Algebra in
open Purelib.Topology in
open Purelib.Data in
/-- Agreement of generator valuations on paired columns preserves every chord-cycle value. -/
theorem chordValues_congr (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord
  lifted.cutBoundaryWord)
    {first second : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical}
    (agree : ∀ column, lifted.cutBoundaryWord.alphabet.oneSided column = false →
      generatorValues first column = generatorValues second column)
    (index : Fin lifted.cutBoundaryWord.alphabet.count) :
    chordValues integral first index = chordValues integral second index := by
  unfold chordValues Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine
  apply FiniteSum.Fin.sumFin_congr
  intro column
  by_cases side : lifted.cutBoundaryWord.alphabet.oneSided column
  · rw [integral.paired_eq, side, Bool.or_true, if_pos rfl]
    ring1
  · rw [agree column (Bool.eq_false_iff.mpr side)]

open Purelib.Algebra in
open Purelib.Topology in
/-- Pointwise equal primitive values have equal contractions against the same integer matrix. -/
private theorem contract_value_congr {count : Nat} (matrix : Fin count → Fin count → Int)
    {first second : Fin count → PrimitivePoint} (agree : ∀ index, first index = second index) :
    Surface.Word.Pairing.contract matrix first = Surface.Word.Pairing.contract matrix second := by
  unfold Surface.Word.Pairing.contract
  apply FiniteSum.Fin.sumFin_congr
  intro row
  apply FiniteSum.Fin.sumFin_congr
  intro column
  rw [agree row, agree column]

open Purelib.Curves in
open Purelib.Integration in
open Purelib.Topology in
open Purelib.Data in
/-- The paired-wedge contraction depends only on valuations at paired generators.

Pointwise agreement on those generators preserves the retained chord values and hence their energy primitive
contraction. -/
theorem paired_wedge_congr (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared)
    {first second : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical}
    (agree : ∀ column, lifted.cutBoundaryWord.alphabet.oneSided column = false →
      generatorValues first column = generatorValues second column)
    (index : Fin genus) :
    Surface.Word.Pairing.contract (pairedWedge cut index)
        (fun column => Energy.Polygon.energyPrimitivePoint
          (chordValues cut.integral first column)) =
      Surface.Word.Pairing.contract (pairedWedge cut index)
        (fun column => Energy.Polygon.energyPrimitivePoint
          (chordValues cut.integral second column)) :=
  contract_value_congr _ (fun column => congrArg
    Energy.Polygon.energyPrimitivePoint
    (chordValues_congr cut.integral agree column))

end Purelib.Riemann.Periods.PairedPeriodPairingBridge

namespace Purelib.Riemann.Periods.PairedPeriodPairingBridge

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_swap sumFin_mul_right
  sumFin_mul_left)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

open Purelib.Curves in
open Purelib.Topology in
/-- The paired coordinate component is the retained total minus its physical component. -/
private theorem pairedPart_sub_physical {word : List (OrientedEdge lifted.vertices.count)}
    {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
    (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates word integral) (column : Fin
      lifted.cutBoundaryWord.alphabet.count) :
    pairedPart cut column = cut.coordinates.totals column - cut.span.physical column := by
  unfold pairedPart
  rw [cut.span.equation column]
  ring1

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Topology in
/-- Contracting the A paired component with B spanning coefficients gives the retained intersection number. -/
theorem pairedPart_inner (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index :
  Fin genus) :
    FiniteSum.Fin.sumFin (fun row => pairedPart (cut.rows.get index).a row *
        (cut.rows.get index).b.span.coefficients row) =
      (Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (cut.rows.get
        index).a.span (cut.rows.get index).b.span) := by
  rw [Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection_left_readback]
  apply FiniteSum.Fin.sumFin_congr
  intro column
  rw [pairedPart_sub_physical]

end Purelib.Riemann.Periods.PairedPeriodPairingBridge

namespace Purelib.Riemann.Periods.PairedPeriodPairingBridge

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Topology in
/-- Contracting the B paired component with A spanning coefficients gives the negative retained intersection number. -/
theorem pairedPart_inner_swap (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared)
  (index : Fin genus) :
    FiniteSum.Fin.sumFin (fun row => pairedPart (cut.rows.get index).b row *
        (cut.rows.get index).a.span.coefficients row) =
      - (Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (cut.rows.get
        index).a.span (cut.rows.get index).b.span) := by
  have h : FiniteSum.Fin.sumFin (fun row => pairedPart (cut.rows.get index).b row *
      (cut.rows.get index).a.span.coefficients row) =
      (Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (cut.rows.get
        index).b.span (cut.rows.get index).a.span) := by
    rw [Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection_left_readback
      (cut.rows.get index).b.span
      (cut.rows.get index).a.span]
    apply FiniteSum.Fin.sumFin_congr
    intro row
    rw [pairedPart_sub_physical]
  rw [h]
  exact Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection_skew
    (cut.rows.get index).b.span (cut.rows.get index).a.span

end Purelib.Riemann.Periods.PairedPeriodPairingBridge

namespace Purelib.Riemann.Periods.PairedPeriodPairingBridge

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}

section
open Purelib.Curves
/-- The B-row physical component equals its total on one-sided generators and vanishes elsewhere. -/
theorem physicalPart_b_eq (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index :
  Fin genus)
    (column : Fin lifted.cutBoundaryWord.alphabet.count) :
    (cut.rows.get index).b.span.physical column =
      if lifted.cutBoundaryWord.alphabet.oneSided column then
        (cut.rows.get index).b.coordinates.totals column else 0 :=
  (cut.rows.get index).b.span.physical_eq column

open Purelib.Topology in
/-- At a paired generator the paired component equals its retained coordinate total. -/
theorem pairedPart_b_eq_totals {word : List (OrientedEdge lifted.vertices.count)}
    {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
    (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates word integral)
    (column : Fin lifted.cutBoundaryWord.alphabet.count)
    (side : lifted.cutBoundaryWord.alphabet.oneSided column = false) :
    pairedPart cut column = cut.coordinates.totals column :=
  pairedPart_eq_totals cut column side

/-- The full coordinate wedge changes sign when its generator indices are exchanged. -/
theorem coordinateWedge_swap (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index
  : Fin genus)
    (row column : Fin lifted.cutBoundaryWord.alphabet.count) :
    coordinateWedge cut index row column = -coordinateWedge cut index column row := by
  unfold coordinateWedge
  ring1

/-- The paired wedge changes sign when its generator indices are exchanged. -/
theorem pairedWedge_swap (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index :
  Fin genus)
    (row column : Fin lifted.cutBoundaryWord.alphabet.count) :
    pairedWedge cut index row column = -pairedWedge cut index column row := by
  unfold pairedWedge
  ring1

/-- The paired wedge vanishes on the diagonal. -/
theorem pairedWedge_diagonal (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index
  : Fin genus)
    (row : Fin lifted.cutBoundaryWord.alphabet.count) :
    pairedWedge cut index row row = 0 := by
  unfold pairedWedge
  ring1

/-- The physical wedge changes sign when its generator indices are exchanged. -/
theorem physicalWedge_swap (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index :
  Fin genus)
    (row column : Fin lifted.cutBoundaryWord.alphabet.count) :
    physicalWedge cut index row column = -physicalWedge cut index column row := by
  unfold physicalWedge
  ring1

/-- The physical wedge vanishes on the diagonal. -/
theorem physicalWedge_diagonal (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared)
  (index : Fin genus)
    (row : Fin lifted.cutBoundaryWord.alphabet.count) :
    physicalWedge cut index row row = 0 := by
  unfold physicalWedge
  ring1

/-- The physical-row mixed wedge is the negative transpose of the paired-row mixed wedge. -/
theorem mixedWedge'_swap (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared) (index :
  Fin genus)
    (row column : Fin lifted.cutBoundaryWord.alphabet.count) :
    mixedWedge' cut index column row = -mixedWedge cut index row column := by
  unfold mixedWedge mixedWedge'
  ring1

/-- The paired-row mixed wedge vanishes on a paired column. -/
theorem mixedWedge_eq_zero_of_column_paired (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank
  prepared) (index : Fin genus)
    (row column : Fin lifted.cutBoundaryWord.alphabet.count)
    (side : lifted.cutBoundaryWord.alphabet.oneSided column = false) :
    mixedWedge cut index row column = 0 := by
  unfold mixedWedge
  rw [physical_b_eq_zero_of_paired cut index column side,
    physical_eq_zero_of_paired cut index column side]
  ring1

/-- The paired-column mixed wedge vanishes on a paired row. -/
theorem mixedWedge'_eq_zero_of_row_paired (cut : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank
  prepared) (index : Fin genus)
    (row column : Fin lifted.cutBoundaryWord.alphabet.count)
    (side : lifted.cutBoundaryWord.alphabet.oneSided row = false) :
    mixedWedge' cut index row column = 0 := by
  unfold mixedWedge'
  rw [physical_eq_zero_of_paired cut index row side,
    physical_b_eq_zero_of_paired cut index row side]
  ring1

end

end Purelib.Riemann.Periods.PairedPeriodPairingBridge
