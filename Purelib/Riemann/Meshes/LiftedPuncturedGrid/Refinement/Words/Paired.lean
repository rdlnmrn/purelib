module

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement.Words
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.Anchor
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Data.Vector.Dependent.Subtype
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction

/-! # Actual old A and full corrected-B words on the same refined mesh

One finite annulus bank and one finite stem-strip bank precede the row fold.
Each original period remains GIVEN. Its complete rooted preparation is
transported jointly through the real common-coordinate and Owner readbacks,
then its derived literal labels feed one original circuit compilation.
The actual replacement includes every strip excursion; no fresh-basis,
period-integral or homology equality is asserted by these word identities.
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
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Vector (DependentVector)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.Topology.Mesh.RetracingWords (AreaTerm)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)

section Inputs

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {original : LiftedPuncturedGrid base}
    {patches : List (ContinuedNeighborhood curve.polynomial count)}
    {prepared : ClearancePreparation base.bank.toBranchCellBank patches}
    (retained : ClearanceRefinement original prepared)
    (oldBank : BasedBranchBank original) (newBank : BasedBranchBank retained.fine)
    {oldSheet annulusSheet stripSheet : Fin 2}
    {ordered : BasedBranchBank.Ordered oldBank oldSheet}
    {paired : OrderedBranchPairs.Ordered.Paired ordered}
    (periods : Paired.PeriodPrograms.Prepared paired)
    (annuli : DependentVector (fun index : Data.Index branches =>
      {value : retained.Annulus index annulusSheet // value = retained.annulus index annulusSheet}))
    (strips : DependentVector (fun index : Data.Index branches =>
      {value : retained.StemStrip oldBank newBank (annuli.get index).val stripSheet //
        value = retained.stemStrip oldBank newBank (annuli.get index).val stripSheet}))

/-- The fine ambient frame is the SAME complete original retained frame, by actual extension-prefix readback. -/
theorem ambient_frame : retained.fine.frames.frameAt _
    (retained.included.vertex (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) =
    original.frames.frameAt _ (BasedBranchTours.FramedBranchCellBank.baseMember base.bank) :=
  (congrArg (fun frames : RootFrames retained.fineBase.bank.grid => frames.frameAt _
    (retained.included.vertex (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))) retained.fine_frames).trans
      (retained.frameAt _ (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))

/-- The actual original source sheet starts from the SAME complete Owner in the fine ambient frame. -/
theorem ambient_owner (sheet : Fin 2) :
    (retained.fine.frames.frameAt _
      (retained.included.vertex (BasedBranchTours.FramedBranchCellBank.baseMember base.bank))).owners sheet =
    (original.frames.frameAt _ (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)).owners sheet :=
  congrArg (fun frame : OwnerFrame _ => frame.owners sheet) retained.ambient_frame

/-- Actual whole original A and corrected-B preparations beside their own complete rooted-word compiler results. -/
@[expose] def PairCompilation (index : Fin genus) : Type _ :=
  (_aClosed : {value : RootClosedWalk base.bank.grid (Cuts.Ambient curve).anchor
    ((original.frames.frameAt _ (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)).owners oldSheet) //
      value = periods.aAtAnchor index}) ×
  (_bClosed : {value : RootClosedWalk base.bank.grid (Cuts.Ambient curve).anchor
    ((original.frames.frameAt _ (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)).owners oldSheet) //
      value = periods.bAtAnchor index}) ×
  (_a : {value : retained.Compilation oldBank newBank annuli strips (paired.aLabels index) oldSheet //
    value = retained.compileWord oldBank newBank annuli strips (paired.aLabels index) oldSheet}) ×
  {b : retained.Compilation oldBank newBank annuli strips (paired.bLabels index) oldSheet //
    b = retained.compileWord oldBank newBank annuli strips (paired.bLabels index) oldSheet}

/-- Transport each GIVEN full preparation once and compile its internally derived original label word once.

Both compiler runs start on the actual original source sheet. The SAME
whole ambient frame/Owner is derived by386 extension readback. They reuse
the same annuli, strips, fresh generator bank and original whole period
family. There is no new Pair.prepare, RootClosedWalk producer or source.
-/
def compilePair (index : Fin genus) :
    retained.PairCompilation oldBank newBank periods annuli strips index :=
  let aClosed := periods.aAtAnchor index
  let bClosed := periods.bAtAnchor index
  let a := retained.compileWord oldBank newBank annuli strips (paired.aLabels index) oldSheet
  let b := retained.compileWord oldBank newBank annuli strips (paired.bLabels index) oldSheet
  ⟨⟨aClosed, rfl⟩, ⟨bClosed, rfl⟩, ⟨a, rfl⟩, ⟨b, rfl⟩⟩

namespace PairCompilation

variable {retained oldBank newBank periods annuli strips} {index : Fin genus}
    (value : retained.PairCompilation oldBank newBank periods annuli strips index)

/-- The SAME complete original A preparation, jointly transported to its actual common anchor. -/
@[expose] def aClosed : RootClosedWalk base.bank.grid (Cuts.Ambient curve).anchor
    ((original.frames.frameAt _ (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)).owners oldSheet) :=
  value.1.val

/-- The SAME complete original corrected-B preparation, including every earlier-A traversal. -/
@[expose] def bClosed : RootClosedWalk base.bank.grid (Cuts.Ambient curve).anchor
    ((original.frames.frameAt _ (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)).owners oldSheet) :=
  value.2.1.val

/-- The exact once-built A word, original compilation and actual global physical correction locations. -/
@[expose] def a : retained.Compilation oldBank newBank annuli strips (paired.aLabels index) oldSheet := value.2.2.1.val

/-- The exact full corrected-B word, original compilation and actual global physical correction locations. -/
@[expose] def b : retained.Compilation oldBank newBank annuli strips (paired.bLabels index) oldSheet := value.2.2.2.val

/-- The whole A closed cache is exactly the given preparation's original joint anchor transport. -/
theorem aClosed_eq : value.aClosed = periods.aAtAnchor index := value.1.property

/-- The whole corrected-B cache is exactly the given preparation's original joint anchor transport. -/
theorem bClosed_eq : value.bClosed = periods.bAtAnchor index := value.2.1.property

/-- Joint A transport retains the SAME complete original traced/covered/root-return value. -/
theorem aClosed_heq : HEq value.aClosed (periods.aWalk index).closed :=
  (heq_of_eq value.aClosed_eq).trans (periods.aAtAnchor_heq index)

/-- Joint corrected-B transport retains the SAME complete original traced/covered/root-return value. -/
theorem bClosed_heq : HEq value.bClosed (periods.bWalk index).closed :=
  (heq_of_eq value.bClosed_eq).trans (periods.bAtAnchor_heq index)

/-- The actual retained A closed walk is exactly the original two-label word consumed by its compilation. -/
theorem aClosed_walk : value.aClosed.walk = oldBank.loopProduct (paired.aLabels index) :=
  (congrArg (fun closed => closed.walk) value.aClosed_eq).trans (periods.aAtAnchor_walk index)

/-- The retained corrected B has its original B pair and literal earlier-A prefix used by its compilation. -/
theorem bClosed_walk : value.bClosed.walk = oldBank.loopProduct (paired.bLabels index) :=
  (congrArg (fun closed => closed.walk) value.bClosed_eq).trans (periods.bAtAnchor_walk index)

/-- The whole A result is exactly its actual original word/compiler/physical-location execution. -/
theorem a_eq : value.a = retained.compileWord oldBank newBank annuli strips (paired.aLabels index) oldSheet :=
  value.2.2.1.property

/-- The whole corrected-B result is exactly its actual original word/compiler/physical-location execution. -/
theorem b_eq : value.b = retained.compileWord oldBank newBank annuli strips (paired.bLabels index) oldSheet :=
  value.2.2.2.property

/-- The resplit A source word equals its fresh-generator excursions plus the actual globally located corrections. -/
theorem a_values (reading : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, reading edge.reverse = -reading edge) :
    retained.fine.edges.chainValue retained.fine.vertices reading
      (retained.included.resplit value.aClosed.walk
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet =
      retained.fine.edges.chainValue retained.fine.vertices reading value.a.word.replacement oldSheet +
        CellBoundary.sumValues (fun occurrence => wordValue reading occurrence.word) value.a.compiled.regulars :=
  (congrArg (fun walk => retained.fine.edges.chainValue retained.fine.vertices reading
    (retained.included.resplit walk
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet) value.aClosed_walk).trans
      (value.a.values reading anti)

/-- The resplit actual full corrected B retains its original reference and every earlier-A correction occurrence. -/
theorem b_values (reading : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, reading edge.reverse = -reading edge) :
    retained.fine.edges.chainValue retained.fine.vertices reading
      (retained.included.resplit value.bClosed.walk
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet =
      retained.fine.edges.chainValue retained.fine.vertices reading value.b.word.replacement oldSheet +
        CellBoundary.sumValues (fun occurrence => wordValue reading occurrence.word) value.b.compiled.regulars :=
  (congrArg (fun walk => retained.fine.edges.chainValue retained.fine.vertices reading
    (retained.included.resplit walk
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet) value.bClosed_walk).trans
      (value.b.values reading anti)

/-- The A area identity keeps the SAME global regular occurrences and every original compiler ribbon term. -/
theorem a_areas (reading : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, reading edge.reverse = -reading edge) :
    retained.fine.edges.chainArea retained.fine.vertices reading
      (retained.included.resplit value.aClosed.walk
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet =
      retained.fine.edges.chainArea retained.fine.vertices reading value.a.word.replacement oldSheet +
        AreaTerm.total reading value.a.compiled.areaTerms :=
  (congrArg (fun walk => retained.fine.edges.chainArea retained.fine.vertices reading
    (retained.included.resplit walk
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet) value.aClosed_walk).trans
      (value.a.areas reading anti)

/-- The full corrected-B area identity retains all earlier-A and reference interactions in the SAME compiler terms. -/
theorem b_areas (reading : OrientedEdge retained.fine.vertices.count → Canonical)
    (anti : ∀ edge, reading edge.reverse = -reading edge) :
    retained.fine.edges.chainArea retained.fine.vertices reading
      (retained.included.resplit value.bClosed.walk
        (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet =
      retained.fine.edges.chainArea retained.fine.vertices reading value.b.word.replacement oldSheet +
        AreaTerm.total reading value.b.compiled.areaTerms :=
  (congrArg (fun walk => retained.fine.edges.chainArea retained.fine.vertices reading
    (retained.included.resplit walk
      (BasedBranchTours.FramedBranchCellBank.baseMember base.bank)) oldSheet) value.bClosed_walk).trans
      (value.b.areas reading anti)

end PairCompilation

/-- One actual finite cache of annuli, stem strips and all original A/full corrected-B compilation rows. -/
@[expose] def PairedWords (annulusSheet stripSheet : Fin 2) : Type _ :=
  (annuli : DependentVector (fun index : Data.Index branches =>
    {value : retained.Annulus index annulusSheet // value = retained.annulus index annulusSheet})) ×
  (strips : DependentVector (fun index : Data.Index branches =>
    {value : retained.StemStrip oldBank newBank (annuli.get index).val stripSheet //
      value = retained.stemStrip oldBank newBank (annuli.get index).val stripSheet})) ×
  DependentVector (fun index : Fin genus =>
    {value : retained.PairCompilation oldBank newBank periods annuli strips index //
      value = retained.compilePair oldBank newBank periods annuli strips index})

/-- Build the finite shared annuli and strips once, then consume the GIVEN whole original paired family.

Each bounded row runs one A and one full corrected-B compiler. Independent
calls are independent finite executions, not a memoized family. The given
old/fine banks, root frames, source periods and canonical cut ownership stay
distinct; physical integral comparison and fresh-basis reduction are later
operations with their own geometric and numerical inputs.
-/
def compilePairs (annulusSheet stripSheet : Fin 2) :
    retained.PairedWords oldBank newBank periods annulusSheet stripSheet :=
  let annuli := retained.annuli annulusSheet
  let strips := retained.stemStrips oldBank newBank annuli stripSheet
  let rows := DependentVector.ofFnWithEq (fun index : Fin genus =>
    retained.compilePair oldBank newBank periods annuli strips index)
  ⟨annuli, strips, rows⟩

end Inputs

namespace PairedWords

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {original : LiftedPuncturedGrid base}
    {patches : List (ContinuedNeighborhood curve.polynomial count)}
    {prepared : ClearancePreparation base.bank.toBranchCellBank patches}
    {retained : ClearanceRefinement original prepared}
    {oldBank : BasedBranchBank original} {newBank : BasedBranchBank retained.fine}
    {oldSheet : Fin 2} {ordered : BasedBranchBank.Ordered oldBank oldSheet}
    {paired : OrderedBranchPairs.Ordered.Paired ordered} {periods : Paired.PeriodPrograms.Prepared paired}
    {annulusSheet stripSheet : Fin 2}
    (value : retained.PairedWords oldBank newBank periods annulusSheet stripSheet)

/-- Read the SAME finite original annulus cache, with each whole original construction factory. -/
@[expose] def annuli : DependentVector (fun index : Data.Index branches =>
    {value : retained.Annulus index annulusSheet // value = retained.annulus index annulusSheet}) := value.1

/-- Read the SAME finite strip cache consuming these exact retained annuli and both given generator banks. -/
@[expose] def strips : DependentVector (fun index : Data.Index branches =>
    {result : retained.StemStrip oldBank newBank (value.annuli.get index).val stripSheet //
      result = retained.stemStrip oldBank newBank (value.annuli.get index).val stripSheet}) := value.2.1

/-- Read the original bounded A/full corrected-B row with both whole original source preparations retained. -/
@[expose] def row (index : Fin genus) :
    retained.PairCompilation oldBank newBank periods value.annuli value.strips index :=
  (value.2.2.get index).val

/-- The row is exactly its single actual compilation run on the SAME original source and shared finite caches. -/
theorem row_eq (index : Fin genus) : value.row index =
    retained.compilePair oldBank newBank periods value.annuli value.strips index :=
  (value.2.2.get index).property

end PairedWords

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement

end
