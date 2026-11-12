module

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Stems
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Data.Vector.Dependent.Subtype
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Reverse
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction

/-! # Actual classified annular words for retained A and full corrected B

Each old branch occurrence uses its GIVEN annulus and stem strip. The
original circuit classifications are based and appended in literal source
order, then the original compiler runs once on the actual incoming sheet.
Strip excursions and all regular correction words and ribbon terms remain
present. No integral payment, basis reduction or root-path equality follows
from the resulting retracing comparison alone.
-/

public section

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (ClearancePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Vector (DependentVector)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder (CellCircuits)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank
open Purelib.Topology.Mesh.RetracingWords (wordArea AreaTerm)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {original : LiftedPuncturedGrid base}
    {patches : List (ContinuedNeighborhood curve.polynomial count)}
    {prepared : ClearancePreparation base.bank.toBranchCellBank patches}
    (retained : ClearanceRefinement original prepared)
    (oldBank : BasedBranchBank original) (newBank : BasedBranchBank retained.fine)
    {annulusSheet stripSheet : Fin 2}
    (annuli : DependentVector (fun index : Data.Index branches =>
      {value : retained.Annulus index annulusSheet // value = retained.annulus index annulusSheet}))

/-- Materialize one actual stem strip per original branch index using its SAME retained annulus cache.

The original bank, fine bank and all annuli are fixed before this finite
construction. Repeated labels later reuse these actual caches, while the
word compiler still retains each repeated signed occurrence separately.
-/
def stemStrips (stripSheet : Fin 2) : DependentVector (fun index : Data.Index branches =>
    {value : retained.StemStrip oldBank newBank (annuli.get index).val stripSheet //
      value = retained.stemStrip oldBank newBank (annuli.get index).val stripSheet}) :=
  DependentVector.ofFnWithEq (fun index =>
    retained.stemStrip oldBank newBank (annuli.get index).val stripSheet)

variable (strips : DependentVector (fun index : Data.Index branches =>
    {value : retained.StemStrip oldBank newBank (annuli.get index).val stripSheet //
      value = retained.stemStrip oldBank newBank (annuli.get index).val stripSheet}))

/-- Concatenate the true strip-excursion conjugates of the GIVEN fresh branch generators, in original label order. -/
@[expose] def freshWord : List (Data.Index branches) →
    Walk retained.fineBase.bank.grid (Cuts.Ambient curve).anchor (Cuts.Ambient curve).anchor
  | [] => .nil _
  | index :: rest => ((strips.get index).val.excursion.based
      (newBank.rows.get index).reference.walk).append (freshWord rest)

/-- One original annulus classification, based at its SAME actual old stem, with both rooted comparisons. -/
private def generatorPartition (index : Data.Index branches) :
    (tree : CellCircuits retained.fineBase.bank.grid (Cuts.Ambient curve).anchor) ×
      {partition : CircuitPartition retained.fineBase.faces tree //
        RootEdgeBank.ChainComparison retained.fine.edges retained.fine.vertices
          (retained.included.resplit (oldBank.rows.get index).reference.walk
            (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) tree.product ∧
        RootEdgeBank.ChainComparison retained.fine.edges retained.fine.vertices partition.kept.product
          ((strips.get index).val.excursion.based (newBank.rows.get index).reference.walk)} := by
  let annular := (annuli.get index).val
  let strip := (strips.get index).val
  let tree := annular.ordered.ordered.tree.based strip.oldStem
  let partition := annular.ordered.partition.based strip.oldStem
  let first := BasedBranchTours.FramedBranchCellBank.baseMember base.bank
  let last := ClearGrid.Cell.anchor_mem _ (base.bank.toBranchCellBank.cell_mem index)
  let reference := fun point member => (LoopMonodromy.BranchCellBank.referenceAt
    retained.fineBase.bank.toBranchCellBank point member).toLoop
  have raw : (oldBank.rows.get index).reference.walk = (oldBank.rows.get index).stem.based annular.oldWalk :=
    (oldBank.rows.get index).reference_eq.trans
      (congrArg (fun loop => (oldBank.rows.get index).stem.based loop)
        ((oldBank.rows.get index).boundary_eq.trans annular.2.2.2.1.property.symm))
  have resplit := retained.included.resplit_based retained.fine.edges retained.fine.vertices reference
    (oldBank.rows.get index).stem annular.oldWalk first last
  have caches : (retained.included.resplit (oldBank.rows.get index).stem last).based
      (retained.included.resplit annular.oldWalk last) = strip.oldStem.based annular.outerWalk :=
    congrArg₂ (fun stem loop => stem.based loop) strip.oldStem_eq.symm annular.2.2.2.2.1.property.symm
  have boundaryToTree := annular.outer_comparison.trans
    (annular.ordered.ordered.comparison.symm.trans
      (RootEdgeBank.ChainComparison.of_eq annular.ordered.ordered.product_eq))
  have full := (RootEdgeBank.ChainComparison.of_eq
    (congrArg (fun walk => retained.included.resplit walk first) raw)).trans
      (resplit.trans ((RootEdgeBank.ChainComparison.of_eq caches).trans
        ((boundaryToTree.based strip.oldStem).trans
          (CellCircuits.based_product reference strip.oldStem annular.ordered.ordered.tree).symm)))
  have keptEq := congrArg CellCircuits.product
    (CircuitPartition.based_kept strip.oldStem annular.ordered.partition)
  have toInner := (RootEdgeBank.ChainComparison.of_eq
    (congrArg CellCircuits.product annular.ordered.kept_eq.symm)).trans annular.inner_comparison
  have kept := (RootEdgeBank.ChainComparison.of_eq keptEq).trans
    ((CellCircuits.based_product reference strip.oldStem annular.ordered.partition.kept).trans
      ((toInner.based strip.oldStem).trans strip.generator_comparison))
  exact ⟨tree, ⟨partition, full, kept⟩⟩

/-- A retained original classified tree and its true excursion replacement for one literal old label word.

The source comparison keeps the resplit original walk and all rooted edge
relations. The replacement stores its exact pointwise freshWord factory,
so downstream users read the actual retained walk rather than rerun it.
-/
@[expose] def Word (labels : List (Data.Index branches)) : Type _ :=
  (tree : CellCircuits retained.fineBase.bank.grid (Cuts.Ambient curve).anchor) ×
  (partition : {_value : CircuitPartition retained.fineBase.faces tree //
    RootEdgeBank.ChainComparison retained.fine.edges retained.fine.vertices
      (retained.included.resplit (oldBank.loopProduct labels)
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
      tree.product}) ×
  {replacement : Walk retained.fineBase.bank.grid (Cuts.Ambient curve).anchor (Cuts.Ambient curve).anchor //
    RootEdgeBank.ChainComparison retained.fine.edges retained.fine.vertices partition.val.kept.product replacement ∧
      replacement = retained.freshWord oldBank newBank annuli strips labels}

/-- Base and append the SAME original annular classifications in the literal old word order.

No root or face is reselected. The original head classification and both
comparisons are read once, then the actual tail is constructed once.
Empty and repeated words retain their genuine circuit roles.
-/
def word : (labels : List (Data.Index branches)) → retained.Word oldBank newBank annuli strips labels
  | [] => ⟨.nil _, ⟨.nil, RootEdgeBank.ChainComparison.refl (.nil _)⟩,
      ⟨.nil _, RootEdgeBank.ChainComparison.refl (.nil _), rfl⟩⟩
  | index :: rest =>
      let head := retained.generatorPartition oldBank newBank annuli strips index
      let tail := word rest
      let tree := CellCircuits.append head.1 tail.1
      let partition := CircuitPartition.append head.2.val tail.2.1.val
      let replacement := ((strips.get index).val.excursion.based
        (newBank.rows.get index).reference.walk).append tail.2.2.val
      have source := (RootEdgeBank.ChainComparison.of_eq
        (retained.included.resplit_append (oldBank.rows.get index).reference.walk (oldBank.loopProduct rest)
          (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)
          (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))).trans
        (head.2.property.1.append tail.2.1.property)
      have kept := head.2.property.2.append tail.2.2.property.1
      have factory := congrArg (fun walk => ((strips.get index).val.excursion.based
        (newBank.rows.get index).reference.walk).append walk) tail.2.2.property.2
      ⟨tree, ⟨partition, source⟩, ⟨replacement, kept, factory⟩⟩

namespace Word

variable {retained oldBank newBank annuli strips} {labels : List (Data.Index branches)}
    (value : retained.Word oldBank newBank annuli strips labels)

/-- The SAME whole actual circuit expression constructed for the literal old labels. -/
@[expose] def tree : CellCircuits retained.fineBase.bank.grid (Cuts.Ambient curve).anchor := value.1

/-- The SAME original based/append classification with each retained regular/hole location unchanged. -/
@[expose] def partition : CircuitPartition retained.fineBase.faces value.tree := value.2.1.val

/-- The actual cached excursion replacement of the original word. -/
@[expose] def replacement : Walk retained.fineBase.bank.grid
    (Cuts.Ambient curve).anchor (Cuts.Ambient curve).anchor := value.2.2.val

/-- The actual original resplit word compares to its SAME retained classified circuit product on every sheet. -/
theorem source : RootEdgeBank.ChainComparison retained.fine.edges retained.fine.vertices
    (retained.included.resplit (oldBank.loopProduct labels)
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))
    value.tree.product := value.2.1.property

/-- The SAME retained hole product compares to the actual cached excursion replacement on every sheet. -/
theorem kept : RootEdgeBank.ChainComparison retained.fine.edges retained.fine.vertices
    value.partition.kept.product value.replacement := value.2.2.property.1

/-- The full replacement is the original literal list of fresh-generator strip conjugates. -/
theorem replacement_eq : value.replacement = retained.freshWord oldBank newBank annuli strips labels :=
  value.2.2.property.2

end Word

/-- A SAME once-built word together with one original compilation on the actual incoming sheet. -/
@[expose] def Compilation (labels : List (Data.Index branches)) (sheet : Fin 2) : Type _ :=
  (value : {value : retained.Word oldBank newBank annuli strips labels //
    value = retained.word oldBank newBank annuli strips labels}) ×
  (compiled : {result : CircuitPartition.Compiled value.val.partition
      retained.fine.edges retained.fine.vertices sheet //
    result = value.val.partition.compile retained.fine.edges retained.fine.vertices sheet}) ×
  {locations : retained.CorrectionLocations compiled.val //
    locations = retained.correctionLocations compiled.val}

/-- Construct the actual original word once, then compile it once on its true requested incoming sheet. -/
def compileWord (labels : List (Data.Index branches)) (sheet : Fin 2) :
    retained.Compilation oldBank newBank annuli strips labels sheet :=
  let value := retained.word oldBank newBank annuli strips labels
  let compiled := value.partition.compile retained.fine.edges retained.fine.vertices sheet
  let locations := retained.correctionLocations compiled
  ⟨⟨value, rfl⟩, ⟨compiled, rfl⟩, ⟨locations, rfl⟩⟩

namespace Compilation

variable {retained oldBank newBank annuli strips} {labels : List (Data.Index branches)} {sheet : Fin 2}
    (value : retained.Compilation oldBank newBank annuli strips labels sheet)

/-- Read the SAME once-built complete original word and its rooted source/replacement comparisons. -/
@[expose] def word : retained.Word oldBank newBank annuli strips labels := value.1.val

/-- Read the SAME original compiler cache, including actual finish sheet, words, occurrences and ribbon terms. -/
@[expose] def compiled : CircuitPartition.Compiled value.word.partition
    retained.fine.edges retained.fine.vertices sheet := value.2.1.val

/-- The retained word is exactly the original single word construction on these cached inputs. -/
theorem word_eq : value.word = retained.word oldBank newBank annuli strips labels := value.1.property

/-- The retained compiler is exactly one original compilation of that SAME actual word. -/
theorem compiled_eq : value.compiled =
    value.word.partition.compile retained.fine.edges retained.fine.vertices sheet := value.2.1.property

/-- The SAME original-mesh locations of all globally compiled correction occurrences and true arrival sheets. -/
@[expose] def corrections : retained.CorrectionLocations value.compiled := value.2.2.val

/-- The whole correction cache is exactly one original finite lookup construction on this SAME compilation. -/
theorem corrections_eq : value.corrections = retained.correctionLocations value.compiled := value.2.2.property

/-- Each physical quadrilateral boundary is the SAME actual globally compiled signed correction word. -/
theorem correction_boundary (position : Fin value.compiled.regulars.length) :
    (value.corrections.correction (retained := retained) (compiled := value.compiled) position).lifted.quad.boundary =
      (value.compiled.regulars[position.val]'position.isLt).word :=
  value.corrections.correction_boundary (retained := retained) (compiled := value.compiled) position

/-- The resplit original source word reaches the actual compiled finish sheet without a return assumption. -/
theorem source_target : RootEdgeBank.target retained.fine.edges
    (retained.included.resplit (oldBank.loopProduct labels)
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) sheet =
    value.compiled.finish :=
  (value.word.source.targets sheet).trans value.compiled.target_eq

/-- The actual excursion replacement reaches the SAME computed finish sheet, preserving its open groupoid role. -/
theorem replacement_target : RootEdgeBank.target retained.fine.edges value.word.replacement sheet =
    value.compiled.finish :=
  (value.word.kept.targets sheet).symm.trans value.compiled.kept_target_eq

/-- The full old word value equals its true fresh excursion word plus every original regular correction occurrence. -/
theorem values (reading : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, reading edge.reverse = -reading edge) :
    retained.fine.edges.chainValue retained.fine.vertices reading
      (retained.included.resplit (oldBank.loopProduct labels)
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) sheet =
    retained.fine.edges.chainValue retained.fine.vertices reading value.word.replacement sheet +
      CellBoundary.sumValues (fun occurrence => wordValue reading occurrence.word) value.compiled.regulars := by
  have original := (value.word.source.values reading anti sheet).trans (value.compiled.values reading anti)
  have replacement := (congrArg (wordValue reading) value.compiled.word_eq).trans
    (value.word.kept.values reading anti sheet)
  exact original.trans (congrArg (fun amount => amount +
    CellBoundary.sumValues (fun occurrence => wordValue reading occurrence.word) value.compiled.regulars) replacement)

/-- The full old word area keeps all genuine annular face and connector cross terms from the SAME original compiler. -/
theorem areas (reading : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, reading edge.reverse = -reading edge) :
    retained.fine.edges.chainArea retained.fine.vertices reading
      (retained.included.resplit (oldBank.loopProduct labels)
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) sheet =
    retained.fine.edges.chainArea retained.fine.vertices reading value.word.replacement sheet +
      AreaTerm.total reading value.compiled.areaTerms := by
  have original := (value.word.source.areas reading anti sheet).trans (value.compiled.areas reading anti)
  have replacement := (congrArg (wordArea reading) value.compiled.word_eq).trans
    (value.word.kept.areas reading anti sheet)
  exact original.trans (congrArg (fun amount => amount + AreaTerm.total reading value.compiled.areaTerms) replacement)

/-- The SAME retained ordered correction word reads as the exact finite correction sum used in values. -/
theorem correction_values (reading : OrientedEdge retained.fine.vertices.count → Canonical) :
    wordValue reading value.compiled.regularWord =
      CellBoundary.sumValues (fun occurrence => wordValue reading occurrence.word) value.compiled.regulars :=
  value.compiled.regularWord_values reading

end Compilation

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement

end
