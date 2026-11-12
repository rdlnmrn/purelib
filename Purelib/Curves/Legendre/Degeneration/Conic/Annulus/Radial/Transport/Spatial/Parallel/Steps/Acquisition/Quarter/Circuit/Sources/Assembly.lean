module

import Purelib.Curves.Legendre.Periods.Fibre
public import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
public import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
public import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Data.Nat.Order
import Purelib.Tactic.QuotientFreeOmega

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Closure.Source
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Observation.Source.Assembly
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Coordinates.Injective
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Seam
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic
import Purelib.Geometry.Gaussian.UnitCircle.Basic
import Purelib.Data.Fin
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization.Sources
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten.Occurrence
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Approximation.Gaussian.Equivalence

/-! # The original four-quarter source assembly and its literal global occurrences

The four existing paid-quarter source families supply all actual geometry,
patches and completed source preparations. Their original physical seam
laws only transport the assembled endpoint indices. The existing append
operation preserves every original quarter, Block, Segment and child in
order. No source preparation, query, paid path or signed seam is replayed.
The resulting base closure does not assert repeated-visit root agreement.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Steps.Acquisition.Quarter.Input

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Curves.Legendre.Periods
open Purelib.Geometry.Gaussian.UnitCircle.Basic (UnitVertex)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Geometry

section ActualInputs

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter} {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable {initial : Input.Realization firstInput sourceOwner agreement}
variable {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}
variable {execution : Execution.Cache initial secondInput thirdInput fourthInput}

variable {frame : Paths.Frame parameter} {basis : Differential 1}
variable {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Execution.Cache.Sources

variable (sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution)

/-- Assemble the four SAME retained quarter source families in the original oriented circuit order.

The complete local source products already exist. Original seam point laws
transport only their endpoint indices; existing append operations join the
same covers and prepared parents. No source, observation, query, paid quarter
or signed seam factory runs here.
-/
def assemble : Spine.Sources.Assembled (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (targets := sourceTargets)
    (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)
    (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter) :=
  let first := Realization.Sources.assemble execution.first sources.1
  let second := Realization.Sources.assemble execution.second.paid sources.2.1
  let third := Realization.Sources.assemble execution.third.paid sources.2.2.1
  let fourth := Realization.Sources.assemble execution.fourth.paid sources.2.2.2
  let firstSecond := Transport.Seam.point_eq (site := site) (parameter := parameter)
    (leftQuarter := .first) (rightQuarter := .second)
    execution.first.finish_time secondInput.source_time Waist.directions_join.1
  let secondThird := Transport.Seam.point_eq (site := site) (parameter := parameter)
    (leftQuarter := .second) (rightQuarter := .third)
    execution.second.paid.finish_time thirdInput.source_time Waist.directions_join.2.1
  let thirdFourth := Transport.Seam.point_eq (site := site) (parameter := parameter)
    (leftQuarter := .third) (rightQuarter := .fourth)
    execution.third.paid.finish_time fourthInput.source_time Waist.directions_join.2.2.1
  let fourthFirst := Transport.Seam.point_eq (site := site) (parameter := parameter)
    (leftQuarter := .fourth) (rightQuarter := .first)
    execution.fourth.paid.finish_time firstInput.source_time Waist.directions_join.2.2.2
  first.append ((second.castEndpoints firstSecond.symm rfl).append
    ((third.castEndpoints secondThird.symm rfl).append
      (fourth.castEndpoints thirdFourth.symm fourthFirst)))

/-- Read the four actual ordered parent words directly from their original stored Block/source families. -/
@[expose] def parentWords : List (List (CenteredEdge (Fibre.frameCurve frame) basis)) :=
  [ (Realization.Sources.parentWords execution.first sources.1).flatten,
    (Realization.Sources.parentWords execution.second.paid sources.2.1).flatten,
    (Realization.Sources.parentWords execution.third.paid sources.2.2.1).flatten,
    (Realization.Sources.parentWords execution.fourth.paid sources.2.2.2).flatten ]

/-- The global assembly preserves the exact four-quarter parent flattening, including all repeated occurrences. -/
theorem assemble_parents : (assemble sources).geometry.parents = (parentWords sources).flatten := by
  unfold assemble
  rewrite [Spine.Sources.Assembled.append_parents, Spine.Sources.Assembled.append_parents,
    Spine.Sources.Assembled.append_parents, Spine.Sources.Assembled.castEndpoints_parents,
    Spine.Sources.Assembled.castEndpoints_parents, Spine.Sources.Assembled.castEndpoints_parents,
    Realization.Sources.assemble_parents, Realization.Sources.assemble_parents,
    Realization.Sources.assemble_parents, Realization.Sources.assemble_parents]
  change _ = _ ++ (_ ++ (_ ++ (_ ++ [])))
  rewrite [Append.append_nil]
  rfl

/-- The original first-quarter endpoint coordinates differ on every admitted regular parallel ellipse. -/
private theorem firstEndpoints_ne :
    coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter ≠
      coordinate site parameter 2 .first (of_decide_eq_true rfl) execution.first.finishEndpoint.parameter := by
  intro equal
  have source := firstInput.source_time
  have finish := execution.first.finish_time
  rewrite [source, finish] at equal
  unfold coordinate at equal
  change (Radial.point site parameter 2 (Waist.direction .first 0) (of_decide_eq_true rfl)).base =
    (Radial.point site parameter 2 (Waist.direction .first 1) (of_decide_eq_true rfl)).base at equal
  have vertices := Radial.point_two_vertex_eq site parameter (Waist.direction .first 0)
    (Waist.direction .first 1) (of_decide_eq_true rfl) circuit.first.regular equal
  have values := congrArg UnitVertex.value vertices
  rewrite [Waist.direction_start_value, Waist.direction_value, Stereographic.unitQuarterPoint_one] at values
  have scalar : (1 : Data.Rat.Fraction.Rational) = 0 := congrArg Canonical.re values
  exact (of_decide_eq_true rfl : ¬ ((1 : Data.Rat.Fraction.Rational) = 0)) scalar

/-- The actual original first quarter contains a retained physical source parent. -/
theorem first_parents_ne_nil :
    (Realization.Sources.assemble execution.first sources.1).geometry.parents ≠ [] :=
  Spine.Sources.Assembled.parents_ne_nil_of_endpoints_ne
    (Realization.Sources.assemble execution.first sources.1) (firstEndpoints_ne (execution := execution))

/-- The SAME global assembled source geometry is nonempty before a new global allocation is selected. -/
theorem assemble_parents_ne_nil : (assemble sources).geometry.parents ≠ [] := by
  intro empty
  have nonempty := first_parents_ne_nil sources
  have words := (assemble_parents sources).symm.trans empty
  change (Realization.Sources.parentWords execution.first sources.1).flatten ++ _ = [] at words
  rewrite [← Realization.Sources.assemble_parents execution.first sources.1] at words
  generalize (Realization.Sources.assemble execution.first sources.1).geometry.parents =
    firstParents at nonempty words
  cases firstParents with
  | nil => exact nonempty rfl
  | cons head tail => cases words

/-- The actual global source words have precisely the original four oriented quarter positions. -/
theorem parentWords_length : (parentWords sources).length = 4 := rfl

/-- An original quarter assembly with its exact physical endpoints, using only existing dependent containers.

This is a read-only view of the same local covering/source family. Endpoint
indices and the complete original source product remain together; it is not
another root owner, acquisition, observation or geometric execution.
-/
@[expose] def QuarterSource :=
  Σ endpoints : Canonical × Canonical,
    Spine.Sources.Assembled (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
      (sheet := sheet) (targets := sourceTargets) endpoints.1 endpoints.2

/-- Read the selected original quarter source view in its actual first-to-fourth order.

Only existing source products and pure assembly operations are consumed.
The displayed Input.Realization.Sources.assemble operations join already prepared
containers and do not acquire patches, models, queries or observations.
-/
@[expose] def quarterSource : Fin 4 → QuarterSource (frame := frame) (basis := basis)
    (modelCount := modelCount) (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) :=
  Data.Fin.cases ⟨⟨_, _⟩, Realization.Sources.assemble execution.first sources.1⟩
    (Data.Fin.cases ⟨⟨_, _⟩, Realization.Sources.assemble execution.second.paid sources.2.1⟩
      (Data.Fin.cases ⟨⟨_, _⟩, Realization.Sources.assemble execution.third.paid sources.2.2.1⟩
        (fun _ : Fin 1 => ⟨⟨_, _⟩, Realization.Sources.assemble execution.fourth.paid sources.2.2.2⟩)))

/-- The selected quarter view retains exactly its own original quarter parent word. -/
theorem quarterSource_parents (quarter : Fin 4) :
    (quarterSource sources quarter).2.geometry.parents =
      (parentWords sources)[quarter.val]'(Eq.mpr
        (congrArg (fun length => quarter.val < length) (parentWords_length sources)) quarter.isLt) := by
  refine Data.Fin.cases_induction ?_ (fun second => ?_) quarter
  · exact Realization.Sources.assemble_parents execution.first sources.1
  · refine Data.Fin.cases_induction ?_ (fun third => ?_) second
    · exact Realization.Sources.assemble_parents execution.second.paid sources.2.1
    · refine Data.Fin.cases_induction ?_ (fun fourth => ?_) third
      · exact Realization.Sources.assemble_parents execution.third.paid sources.2.2.1
      · refine Data.Fin.cases_induction ?_ (fun empty => Fin.elim0 empty) fourth
        exact Realization.Sources.assemble_parents execution.fourth.paid sources.2.2.2

/-- Transfer the SAME assembled source index to the identical ordered quarter flattening. -/
@[expose] def flattenedIndex (index : Fin (assemble sources).geometry.parents.length) :
    Fin (parentWords sources).flatten.length :=
  ⟨index.val, Eq.mp (congrArg (fun parents => index.val < parents.length) (assemble_parents sources)) index.isLt⟩

/-- Execute the original finite locator once on this SAME actual global source position. -/
def locate (index : Fin (assemble sources).geometry.parents.length) :
    Flatten.Occurrence (parentWords sources) (flattenedIndex sources index) :=
  Flatten.locate (parentWords sources) (flattenedIndex sources index)

/-- The location is the exact original executable flatten lookup on the unchanged global occurrence. -/
theorem locate_eq (index : Fin (assemble sources).geometry.parents.length) :
    locate sources index = Flatten.locate (parentWords sources) (flattenedIndex sources index) := by
  unfold locate
  rfl

variable (index : Fin (assemble sources).geometry.parents.length)
variable (position : Flatten.Occurrence (parentWords sources) (flattenedIndex sources index))

/-- Read the literal first-to-fourth quarter occurrence from the SAME retained global location. -/
@[expose] def quarter : Fin 4 :=
  ⟨position.1.val, Eq.mp (congrArg (fun length => position.1.val < length) (parentWords_length sources))
    position.1.isLt⟩

/-- Read the complete original selected quarter geometry, cover and source family without another source acquisition. -/
@[expose] def selected := quarterSource sources (quarter sources index position)

/-- Read the selected quarter's actual local child, transporting only its exact original word bound. -/
@[expose] def child : Fin (selected sources index position).2.geometry.parents.length :=
  ⟨position.2.val.val, Eq.mpr (congrArg (fun parents => position.2.val.val < parents.length)
    (quarterSource_parents sources (quarter sources index position))) position.2.val.isLt⟩

/-- A global occurrence is the SAME actual selected original quarter parent, independent of repeated point values. -/
theorem parent_eq :
    (assemble sources).geometry.parents[index.val]'index.isLt =
      (selected sources index position).2.geometry.parents[(child sources index position).val]'
        (child sources index position).isLt := by
  have whole := getElem_congr (i := index.val) (j := index.val) (assemble_parents sources) rfl index.isLt
  have localParent := getElem_congr (i := (child sources index position).val)
    (j := (child sources index position).val)
    (quarterSource_parents sources (quarter sources index position)) rfl (child sources index position).isLt
  exact whole.trans (position.2.property.1.trans localParent.symm)

section SignedRoots

open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology

/-- Derive one closed signed root chain of these SAME actual four-quarter source parents.

Every quarter contributes its original source-chain cache. The three actual
Seam.name_eq receipts identify the literal next source names. The stored
returnEquivalent, whose factory law uses THIS closing receipt, pays the
fourth-to-first root comparison. Empty parent words retain their real signed
handoffs through RootChain.append; no geometric closure or key supplies a sign.
-/
def rootChain : RootChain (assemble sources).geometry.parents
    (ownerRootName sourceOwner.parameterNonzero sourceOwner)
    (ownerRootName sourceOwner.parameterNonzero sourceOwner) := by
  let first := Realization.Sources.rootChain execution.first sources.1
  let second := Realization.Sources.rootChain execution.second.paid sources.2.1
  let third := Realization.Sources.rootChain execution.third.paid sources.2.2.1
  let fourth := Realization.Sources.rootChain execution.fourth.paid sources.2.2.2
  let firstHandoff := PreparedBankRootChains.RootChain.castNames rfl execution.second.seam.name_eq.symm first
  let secondHandoff := PreparedBankRootChains.RootChain.castNames rfl execution.third.seam.name_eq.symm second
  let thirdHandoff := PreparedBankRootChains.RootChain.castNames rfl execution.fourth.seam.name_eq.symm third
  let returned := PreparedBankRootChains.RootChain.changeFinish fourth execution.returnEquivalent
  let joined := firstHandoff.append (secondHandoff.append (thirdHandoff.append returned))
  have parents : (assemble sources).geometry.parents =
      (Realization.Sources.assemble execution.first sources.1).geometry.parents ++
        ((Realization.Sources.assemble execution.second.paid sources.2.1).geometry.parents ++
          ((Realization.Sources.assemble execution.third.paid sources.2.2.1).geometry.parents ++
            (Realization.Sources.assemble execution.fourth.paid sources.2.2.2).geometry.parents)) := by
    unfold assemble
    rewrite [Spine.Sources.Assembled.append_parents, Spine.Sources.Assembled.append_parents,
      Spine.Sources.Assembled.append_parents, Spine.Sources.Assembled.castEndpoints_parents,
      Spine.Sources.Assembled.castEndpoints_parents, Spine.Sources.Assembled.castEndpoints_parents]
    rfl
  exact PreparedBankRootChains.RootChain.castChildren parents.symm joined

end SignedRoots

end Execution.Cache.Sources

end ActualInputs

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter}
variable {firstReading : ReadingAt circuit.first.actual UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginalOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {firstOriginal : Steps.Quarter circuit.first.actual circuit.first.regular
  UniformPrimitiveMesh.firstEndpoint firstReading firstOriginalOwner}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {agreement : InitialAgreement UniformPrimitiveMesh.firstEndpoint firstReading sourceOwner}
variable {initial : Quarter firstOriginal sourceOwner agreement}
variable {secondReading : ReadingAt circuit.second.actual UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginalOwner : OwnerAt site parameter .second (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable {secondOriginal : Steps.Quarter circuit.second.actual circuit.second.regular
  UniformPrimitiveMesh.firstEndpoint secondReading secondOriginalOwner}
variable {thirdReading : ReadingAt circuit.third.actual UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginalOwner : OwnerAt site parameter .third (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint}
variable {thirdOriginal : Steps.Quarter circuit.third.actual circuit.third.regular
  UniformPrimitiveMesh.firstEndpoint thirdReading thirdOriginalOwner}
variable {fourthReading : ReadingAt circuit.fourth.actual UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginalOwner : OwnerAt site parameter .fourth (of_decide_eq_true rfl)
  UniformPrimitiveMesh.firstEndpoint}
variable {fourthOriginal : Steps.Quarter circuit.fourth.actual circuit.fourth.regular
  UniformPrimitiveMesh.firstEndpoint fourthReading fourthOriginalOwner}
variable {execution : Execution initial secondOriginal thirdOriginal fourthOriginal}

variable {frame : Paths.Frame parameter} {basis : Differential 1}
variable {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}

namespace Execution.Sources

variable (sources : Execution.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution)

/-- The original old-input facade uses the SAME shared actual four-quarter source assembler. -/
@[expose] def assemble : Spine.Sources.Assembled (frame := frame) (basis := basis) (count := modelCount)
    (floor := floor) (sheet := sheet) (targets := sourceTargets)
    (coordinate site parameter 2 .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint.parameter)
    (coordinate site parameter 2 .first (of_decide_eq_true rfl) UniformPrimitiveMesh.firstEndpoint.parameter) :=
  Cache.Sources.assemble (execution := execution) sources

/-- The old-input assembly facade retains exactly the SAME complete shared actual four-quarter source cache. -/
theorem assemble_eq_shared : assemble sources = Cache.Sources.assemble (execution := execution) sources := by
  unfold assemble
  rfl

/-- The old-input words are the identical ordered parent lists of the shared actual source family. -/
@[expose] def parentWords : List (List (CenteredEdge (Fibre.frameCurve frame) basis)) :=
  Cache.Sources.parentWords (execution := execution) sources

/-- Shared assembly preserves the SAME complete old-input ordered parent flattening. -/
theorem assemble_parents : (assemble sources).geometry.parents = (parentWords sources).flatten :=
  Cache.Sources.assemble_parents (execution := execution) sources

/-- The actual original first quarter remains nonempty on its literal old source parents. -/
theorem first_parents_ne_nil : (Quarter.Sources.assemble execution.first sources.1).geometry.parents ≠ [] := by
  have nonempty := Cache.Sources.first_parents_ne_nil (execution := execution) sources
  have same := congrArg (fun retained => retained.geometry.parents)
    (Realization.Sources.assemble_ofSteps rfl execution.first sources.1)
  exact Eq.mp (congrArg (fun parents => parents ≠ []) same) nonempty

/-- The shared original old-input source assembly is nonempty before a new Stage request is selected. -/
theorem assemble_parents_ne_nil : (assemble sources).geometry.parents ≠ [] :=
  Cache.Sources.assemble_parents_ne_nil (execution := execution) sources

/-- The old-input facade retains the original four oriented source positions. -/
theorem parentWords_length : (parentWords sources).length = 4 :=
  Cache.Sources.parentWords_length (execution := execution) sources

/-- The old-input quarter occurrence view is the SAME existing whole assembled source parent. -/
@[expose] def QuarterSource :=
  Cache.Sources.QuarterSource (frame := frame) (basis := basis) (modelCount := modelCount) (floor := floor)
    (sheet := sheet) (sourceTargets := sourceTargets)

/-- Read the same actual complete quarter source view through the single shared original finite selector. -/
@[expose] def quarterSource : Fin 4 → QuarterSource (frame := frame) (basis := basis)
    (modelCount := modelCount) (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) :=
  Cache.Sources.quarterSource (execution := execution) sources

/-- The selected original old-input quarter retains its literal source parent word. -/
theorem quarterSource_parents (quarter : Fin 4) :
    (quarterSource sources quarter).2.geometry.parents =
      (parentWords sources)[quarter.val]'(Eq.mpr
        (congrArg (fun length => quarter.val < length) (parentWords_length sources)) quarter.isLt) :=
  Cache.Sources.quarterSource_parents (execution := execution) sources quarter

/-- Transfer the unchanged old-input global source coordinate to the SAME shared ordered flattening. -/
@[expose] def flattenedIndex (index : Fin (assemble sources).geometry.parents.length) :
    Fin (parentWords sources).flatten.length := Cache.Sources.flattenedIndex (execution := execution) sources index

/-- Execute the SAME original finite locator on the literal old-input source occurrence. -/
def locate (index : Fin (assemble sources).geometry.parents.length) :
    Flatten.Occurrence (parentWords sources) (flattenedIndex sources index) :=
  Cache.Sources.locate (execution := execution) sources index

/-- The retained old-input position is exactly the original executable flatten worker result. -/
theorem locate_eq (index : Fin (assemble sources).geometry.parents.length) :
    locate sources index = Flatten.locate (parentWords sources) (flattenedIndex sources index) :=
  Cache.Sources.locate_eq (execution := execution) sources index

variable (index : Fin (assemble sources).geometry.parents.length)
variable (position : Flatten.Occurrence (parentWords sources) (flattenedIndex sources index))

/-- Read the original first-to-fourth coordinate of the SAME retained old-input global position. -/
@[expose] def quarter : Fin 4 := Cache.Sources.quarter (execution := execution) sources index position

/-- Read the SAME complete actual selected old-input quarter source family, without a second source acquisition. -/
@[expose] def selected := Cache.Sources.selected (execution := execution) sources index position

/-- Read the identical local child coordinate from the original whole retained old-input location. -/
@[expose] def child : Fin (selected sources index position).2.geometry.parents.length :=
  Cache.Sources.child (execution := execution) sources index position

/-- The old-input global source is the literal selected original quarter parent, including repeated occurrences. -/
theorem parent_eq :
    (assemble sources).geometry.parents[index.val]'index.isLt =
      (selected sources index position).2.geometry.parents[(child sources index position).val]'
        (child sources index position).isLt := Cache.Sources.parent_eq (execution := execution) sources index position

end Execution.Sources

section ActualDetours

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter} {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable {initial : Input.Realization firstInput sourceOwner agreement}
variable {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}
variable {execution : Execution.Cache initial secondInput thirdInput fourthInput}

namespace Execution.Cache

/-- The four original paired-line banks on the SAME actual paid quarter realizations.

This is an ordinary product of the shared original bank view. Each factor
retains its actual branch and ordered endpoints, including repetitions.
One supplied coefficient eliminant and line provider index all four banks.
-/
abbrev Lines {degreeBound : Nat} (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) :=
  Input.Realization.Lines execution.first elimination clearances ×
    Input.Realization.Lines execution.second.paid elimination clearances ×
    Input.Realization.Lines execution.third.paid elimination clearances ×
    Input.Realization.Lines execution.fourth.paid elimination clearances

namespace Lines

variable {degreeBound : Nat}
variable {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
variable {clearances : AxisClearances elimination}

/-- Compute the four occurrence banks once from the same actual execution and supplied original eliminant. -/
def build (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) : Lines execution elimination clearances :=
  let first : Input.Realization.Lines execution.first elimination clearances :=
    Geometry.Lines.Bank.build elimination clearances circuit.first.regular circuit.first.actual.data.bound
      execution.first.endpointList
      (fun endpoint : Endpoint => coordinate site parameter 2 .first (of_decide_eq_true rfl) endpoint.parameter)
      (fun endpoint => coordinate_inside site parameter 2 .first (of_decide_eq_true rfl)
        circuit.first.actual.data.lower circuit.first.actual.data.upper circuit.first.actual.data.bound
        endpoint.parameter)
  let second : Input.Realization.Lines execution.second.paid elimination clearances :=
    Geometry.Lines.Bank.build elimination clearances circuit.second.regular circuit.second.actual.data.bound
      execution.second.paid.endpointList
      (fun endpoint : Endpoint => coordinate site parameter 2 .second (of_decide_eq_true rfl) endpoint.parameter)
      (fun endpoint => coordinate_inside site parameter 2 .second (of_decide_eq_true rfl)
        circuit.second.actual.data.lower circuit.second.actual.data.upper circuit.second.actual.data.bound
        endpoint.parameter)
  let third : Input.Realization.Lines execution.third.paid elimination clearances :=
    Geometry.Lines.Bank.build elimination clearances circuit.third.regular circuit.third.actual.data.bound
      execution.third.paid.endpointList
      (fun endpoint : Endpoint => coordinate site parameter 2 .third (of_decide_eq_true rfl) endpoint.parameter)
      (fun endpoint => coordinate_inside site parameter 2 .third (of_decide_eq_true rfl)
        circuit.third.actual.data.lower circuit.third.actual.data.upper circuit.third.actual.data.bound
        endpoint.parameter)
  let fourth : Input.Realization.Lines execution.fourth.paid elimination clearances :=
    Geometry.Lines.Bank.build elimination clearances circuit.fourth.regular circuit.fourth.actual.data.bound
      execution.fourth.paid.endpointList
      (fun endpoint : Endpoint => coordinate site parameter 2 .fourth (of_decide_eq_true rfl) endpoint.parameter)
      (fun endpoint => coordinate_inside site parameter 2 .fourth (of_decide_eq_true rfl)
        circuit.fourth.actual.data.lower circuit.fourth.actual.data.upper circuit.fourth.actual.data.bound
        endpoint.parameter)
  ⟨first, second, third, fourth⟩

/-- The four original occurrence products on the same final grid and unchanged paid execution.

Each component retains the corresponding input branch's actual head Walks;
ordered repetitions and old/fine branch ownership remain unchanged.
-/
abbrev DetourWalks (_lines : Lines execution elimination clearances)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :=
  Input.Realization.DetourWalks execution.first elimination grid ×
    Input.Realization.DetourWalks execution.second.paid elimination grid ×
      Input.Realization.DetourWalks execution.third.paid elimination grid ×
        Input.Realization.DetourWalks execution.fourth.paid elimination grid

/-- All four original occurrence banks lie on their same ordered final grid extension.

This exact proposition retains the four original grid extensions and each
actual endpoint occurrence. It imposes no clearance of a source line and
preserves repeated points and the original quarter order.
-/
@[expose] def OnExtended (lines : Lines execution elimination clearances)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) : Prop :=
  let firstPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular) lines.1
  let secondPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular) lines.2.1
  let thirdPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular) lines.2.2.1
  let fourthPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular) lines.2.2.2
  let firstGrid := Grid.Extension.extend base (firstPairs.map Prod.fst) (firstPairs.map Prod.snd)
  let secondGrid := Grid.Extension.extend firstGrid (secondPairs.map Prod.fst) (secondPairs.map Prod.snd)
  let thirdGrid := Grid.Extension.extend secondGrid (thirdPairs.map Prod.fst) (thirdPairs.map Prod.snd)
  let finalGrid := Grid.Extension.extend thirdGrid (fourthPairs.map Prod.fst) (fourthPairs.map Prod.snd)
  (∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular) lines.1,
      Grid.FromStates.ContainsVertex finalGrid point) ∧
  (∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular) lines.2.1,
      Grid.FromStates.ContainsVertex finalGrid point) ∧
  (∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular) lines.2.2.1,
      Grid.FromStates.ContainsVertex finalGrid point) ∧
  (∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular) lines.2.2.2,
      Grid.FromStates.ContainsVertex finalGrid point)

/-- Derive all four occurrence memberships through the original coordinate inclusions. -/
theorem onExtended (lines : Lines execution elimination clearances)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) : OnExtended lines base :=
  let firstPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular) lines.1
  let secondPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular) lines.2.1
  let thirdPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular) lines.2.2.1
  let fourthPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular) lines.2.2.2
  let firstGrid := Grid.Extension.extend base (firstPairs.map Prod.fst) (firstPairs.map Prod.snd)
  let secondGrid := Grid.Extension.extend firstGrid (secondPairs.map Prod.fst) (secondPairs.map Prod.snd)
  let thirdGrid := Grid.Extension.extend secondGrid (thirdPairs.map Prod.fst) (thirdPairs.map Prod.snd)
  let firstSecond := Grid.Extension.extend_inclusion firstGrid (secondPairs.map Prod.fst) (secondPairs.map Prod.snd)
  let secondThird := Grid.Extension.extend_inclusion secondGrid (thirdPairs.map Prod.fst) (thirdPairs.map Prod.snd)
  let thirdFourth := Grid.Extension.extend_inclusion thirdGrid (fourthPairs.map Prod.fst) (fourthPairs.map Prod.snd)
  ⟨    (fun point member => (firstSecond.trans (secondThird.trans thirdFourth)).vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular)
        lines.1 base point member)),
        (fun point member => (secondThird.trans thirdFourth).vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular)
        lines.2.1 firstGrid point member)),
        (fun point member => thirdFourth.vertex
      (Geometry.Lines.Bank.onExtended
        (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular)
        lines.2.2.1 secondGrid point member)),
        (Geometry.Lines.Bank.onExtended
      (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular)
      lines.2.2.2 thirdGrid)⟩

/-- Retain all original head Walks and the closed aggregate on ONE actual original clear-grid extension.

The four banks are read once to construct the nested original extensions.
Each actual paid quarter is split directly on that same final grid, with
membership derived through the original coordinate inclusions. The actual
seam coordinate laws close the walk without any root or cycle identification.
-/
def prepareDetour (lines : Lines execution elimination clearances)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    Σ grid : Grid.ClearGrid (Paths.polynomial parameter)
        (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)),
      DetourWalks lines grid ×
      {_walk : Grid.Walks.Walk grid
        (Geometry.move elimination circuit.first.regular
          (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))
        (Geometry.move elimination circuit.first.regular
          (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)) //
        Grid.FromStates.ContainsVertex grid
          (Geometry.move elimination circuit.first.regular
            (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))} :=
  let firstPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular) lines.1
  let secondPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular) lines.2.1
  let thirdPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular) lines.2.2.1
  let fourthPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular) lines.2.2.2
  let firstGrid := Grid.Extension.extend base (firstPairs.map Prod.fst) (firstPairs.map Prod.snd)
  let secondGrid := Grid.Extension.extend firstGrid (secondPairs.map Prod.fst) (secondPairs.map Prod.snd)
  let thirdGrid := Grid.Extension.extend secondGrid (thirdPairs.map Prod.fst) (thirdPairs.map Prod.snd)
  let finalGrid := Grid.Extension.extend thirdGrid (fourthPairs.map Prod.fst) (fourthPairs.map Prod.snd)
  let firstWalk := Input.Realization.prepareDetourOn execution.first elimination clearances lines.1 finalGrid
    ((lines.onExtended base).1)
  let secondWalk := Input.Realization.prepareDetourOn execution.second.paid elimination clearances lines.2.1 finalGrid
    ((lines.onExtended base).2.1)
  let thirdWalk := Input.Realization.prepareDetourOn execution.third.paid elimination clearances lines.2.2.1 finalGrid
    ((lines.onExtended base).2.2.1)
  let fourthWalk := Input.Realization.prepareDetourOn execution.fourth.paid elimination clearances lines.2.2.2 finalGrid
    ((lines.onExtended base).2.2.2)
  let firstSeam := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .first) (rightQuarter := .second)
      execution.first.finish_time secondInput.source_time Waist.directions_join.1)
  let secondSeam := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .second) (rightQuarter := .third)
      execution.second.paid.finish_time thirdInput.source_time Waist.directions_join.2.1)
  let thirdSeam := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .third) (rightQuarter := .fourth)
      execution.third.paid.finish_time fourthInput.source_time Waist.directions_join.2.2.1)
  let closing := congrArg (Geometry.move elimination circuit.first.regular)
    (Transport.Seam.point_eq (site := site) (parameter := parameter) (leftQuarter := .fourth) (rightQuarter := .first)
      execution.fourth.paid.finish_time firstInput.source_time Waist.directions_join.2.2.2)
  ⟨finalGrid, ⟨⟨firstWalk.1, secondWalk.1, thirdWalk.1, fourthWalk.1⟩,
    ⟨firstWalk.2.val.append ((secondWalk.2.val.castEndpoints firstSeam.symm rfl).append
      ((thirdWalk.2.val.castEndpoints secondSeam.symm rfl).append
        (fourthWalk.2.val.castEndpoints thirdSeam.symm closing))),
    Eq.mp (congrArg (Grid.FromStates.ContainsVertex finalGrid) closing) fourthWalk.2.property⟩⟩⟩

/-- Assemble the numeric four-quarter detour on ONE actual retained extension of the original clear grid.

The four banks are read once to construct the nested original extensions.
Each actual paid quarter is split directly on that same final grid, with
membership derived through the original coordinate inclusions. The actual
seam coordinate laws close the walk without any root or cycle identification.
-/
def detour (lines : Lines execution elimination clearances)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    Σ grid : Grid.ClearGrid (Paths.polynomial parameter)
        (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)),
      {_walk : Grid.Walks.Walk grid
        (Geometry.move elimination circuit.first.regular
          (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))
        (Geometry.move elimination circuit.first.regular
          (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)) //
        Grid.FromStates.ContainsVertex grid
          (Geometry.move elimination circuit.first.regular
            (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))} :=
  let retained := lines.prepareDetour base
  ⟨retained.1, retained.2.2⟩

end Lines

/-- Retain all four actual line banks and their constructed closed numeric walk on the same original grid extension.

The returned ordinary dependent pairs keep the literal bank and final grid
values. Source/sheet ownership and canonical period coordinates remain
separate from this exact finite numeric construction.
-/
def detour {degreeBound : Nat} (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    Σ _lines : Lines execution elimination clearances,
      Σ grid : Grid.ClearGrid (Paths.polynomial parameter)
          (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)),
        {_walk : Grid.Walks.Walk grid
          (Geometry.move elimination circuit.first.regular
            (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))
          (Geometry.move elimination circuit.first.regular
            (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)) //
          Grid.FromStates.ContainsVertex grid
            (Geometry.move elimination circuit.first.regular
              (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))} :=
  let lines := Lines.build execution elimination clearances
  ⟨lines, Lines.detour (execution := execution) (elimination := elimination)
    (clearances := clearances) lines base⟩

namespace Lines

variable {degreeBound : Nat}
variable {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
variable {clearances : AxisClearances elimination}

/-- The actual four-quarter detour grid retains every coordinate of its original base grid.

The four original extension inclusions compose in the same quarter order.
This is only a semantic readback of the retained numeric result; it does
not reconstruct any source owner or acquire another path.
-/
theorem detour_inclusion (lines : Lines execution elimination clearances)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :
    Grid.Extension.CoordinateInclusion base (lines.detour base).1 := by
  let firstPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular) lines.1
  let secondPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular) lines.2.1
  let thirdPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular) lines.2.2.1
  let fourthPairs := Geometry.Lines.Bank.pairs
    (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular) lines.2.2.2
  let firstGrid := Grid.Extension.extend base (firstPairs.map Prod.fst) (firstPairs.map Prod.snd)
  let secondGrid := Grid.Extension.extend firstGrid (secondPairs.map Prod.fst) (secondPairs.map Prod.snd)
  let thirdGrid := Grid.Extension.extend secondGrid (thirdPairs.map Prod.fst) (thirdPairs.map Prod.snd)
  exact (Grid.Extension.extend_inclusion base (firstPairs.map Prod.fst) (firstPairs.map Prod.snd)).trans
    ((Grid.Extension.extend_inclusion firstGrid (secondPairs.map Prod.fst) (secondPairs.map Prod.snd)).trans
      ((Grid.Extension.extend_inclusion secondGrid (thirdPairs.map Prod.fst) (thirdPairs.map Prod.snd)).trans
        (Grid.Extension.extend_inclusion thirdGrid (fourthPairs.map Prod.fst) (fourthPairs.map Prod.snd))))

open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)

/-- A winding-one reference at an actual cached detour vertex, derived from the same original branch bank.

The supplied grid is the literal retained output of the four-quarter
numeric detour. Its factory readback transports only coordinate inclusion.
The original bank supplies one real branch-cell loop; an actual connector
on that SAME cached grid rebases it without another root bank or budget.
-/
def referenceAt (lines : Lines execution elimination clearances)
    (frame : Paths.Frame parameter)
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : BranchCellBank (Fibre.frameCurve frame) branches higher)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (same : grid = (lines.detour bank.grid).1)
    (point : Canonical) (member : Grid.FromStates.ContainsVertex grid point) :
    WindingOneLoop (Paths.polynomial parameter) point :=
  let index : BranchIsolation.Data.Index branches := ⟨0, by
    have count := branches.count_eq
    have positive := BranchIsolation.degreePositive (Fibre.frameCurve frame)
    omega0⟩
  let cell := bank.cell index
  let anchorMember := Grid.ClearGrid.Cell.anchor_mem cell (bank.cell_mem index)
  let original := LoopMonodromy.BranchCellBank.referenceAt bank cell.box.anchor anchorMember
  let included : Grid.Extension.CoordinateInclusion bank.grid grid :=
    Eq.mpr (congrArg (Grid.Extension.CoordinateInclusion bank.grid) same) (lines.detour_inclusion bank.grid)
  let connector := LoopMonodromy.Grid.connect grid point cell.box.anchor member (included.vertex anchorMember)
  original.toLoop.rebase connector.path connector.withinAmbient

/-- The actual original moved-vertex reference retains the same original large-square ambient. -/
theorem referenceAt_ambient (lines : Lines execution elimination clearances)
    (frame : Paths.Frame parameter)
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : BranchCellBank (Fibre.frameCurve frame) branches higher)
    (grid : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter)))
    (same : grid = (lines.detour bank.grid).1)
    (point : Canonical) (member : Grid.FromStates.ContainsVertex grid point) :
    (referenceAt lines frame bank grid same point member).ambient =
      RootRadius.Box.largeSquareBox (Paths.polynomial parameter) := (rfl)

/-- The exact cached whole numeric detour factory on the original base grid.

The ordinary subtype retains the full dependent grid/walk value together
with its original producer equation. It creates no new nominal owner.
-/
abbrev DetourCache (lines : Lines execution elimination clearances)
    (base : Grid.ClearGrid (Paths.polynomial parameter)
      (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))) :=
  { value // value = lines.prepareDetour base }

namespace DetourCache

variable {lines : Lines execution elimination clearances}
variable {base : Grid.ClearGrid (Paths.polynomial parameter)
  (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))}

/-- The same four original occurrence banks remain members of the literal stored numeric grid. -/
theorem onGrid (cached : DetourCache lines base) :
    (∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := circuit.first.regular) lines.1,
      Grid.FromStates.ContainsVertex cached.val.1 point) ∧
    (∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := circuit.second.regular) lines.2.1,
      Grid.FromStates.ContainsVertex cached.val.1 point) ∧
    (∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := circuit.third.regular) lines.2.2.1,
      Grid.FromStates.ContainsVertex cached.val.1 point) ∧
    (∀ point ∈ Geometry.Lines.Bank.points
      (elimination := elimination) (clearances := clearances) (regular := circuit.fourth.regular) lines.2.2.2,
      Grid.FromStates.ContainsVertex cached.val.1 point) := by
  have same : cached.val.1 = (lines.prepareDetour base).1 := congrArg Sigma.fst cached.property
  have retained := lines.onExtended base
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro point member
    have present := retained.1 point member
    change Grid.FromStates.ContainsVertex (lines.prepareDetour base).1 point at present
    exact Eq.mpr (congrArg (fun grid => Grid.FromStates.ContainsVertex grid point) same) present
  · intro point member
    have present := retained.2.1 point member
    change Grid.FromStates.ContainsVertex (lines.prepareDetour base).1 point at present
    exact Eq.mpr (congrArg (fun grid => Grid.FromStates.ContainsVertex grid point) same) present
  · intro point member
    have present := retained.2.2.1 point member
    change Grid.FromStates.ContainsVertex (lines.prepareDetour base).1 point at present
    exact Eq.mpr (congrArg (fun grid => Grid.FromStates.ContainsVertex grid point) same) present
  · intro point member
    have present := retained.2.2.2 point member
    change Grid.FromStates.ContainsVertex (lines.prepareDetour base).1 point at present
    exact Eq.mpr (congrArg (fun grid => Grid.FromStates.ContainsVertex grid point) same) present

/-- Read the four literal stored head banks with their same original quarter-factory identities.

The returned products only retain existing bank pointers. Each erased
factory equation follows from the whole cached numeric producer; no Walk,
query, line bank or grid extension is recomputed by this projection.
-/
def components (cached : DetourCache lines base) :
    Input.Realization.DetourWalkCache elimination clearances cached.val.1
      execution.first lines.1 cached.onGrid.1 ×
    Input.Realization.DetourWalkCache elimination clearances cached.val.1
      execution.second.paid lines.2.1 cached.onGrid.2.1 ×
    Input.Realization.DetourWalkCache elimination clearances cached.val.1
      execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 ×
    Input.Realization.DetourWalkCache elimination clearances cached.val.1
      execution.fourth.paid lines.2.2.2 cached.onGrid.2.2.2 := by
  refine ⟨⟨cached.val.2.1.1, ?_⟩, ⟨cached.val.2.1.2.1, ?_⟩,
    ⟨cached.val.2.1.2.2.1, ?_⟩, ⟨cached.val.2.1.2.2.2, ?_⟩⟩
  all_goals
    cases cached with
    | mk value retained =>
      cases retained
      rfl

/-- Rebase the same stored moved-point loop at any actual vertex of the literal cached grid.

The original shared loop remains a single retained value. Each connector
is constructed on that same grid from its actual vertex witnesses; no
branch bank, isolation or old source preparation is recomputed.
-/
def pointReferences (cached : DetourCache lines base)
    (reference : WindingOneLoop (Paths.polynomial parameter)
      (Geometry.move elimination circuit.first.regular
        (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)))
    (same : reference.ambient = RootRadius.Box.largeSquareBox (Paths.polynomial parameter))
    (point : Canonical) (member : Grid.FromStates.ContainsVertex cached.val.1 point) :
    WindingOneLoop (Paths.polynomial parameter) point := by
  cases reference with
  | mk ambient path within winding =>
      cases same
      let connector := LoopMonodromy.Grid.connect cached.val.1 point
        (Geometry.move elimination circuit.first.regular
          (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))
        member cached.val.2.2.property
      exact (⟨_, path, within, winding⟩ : WindingOneLoop (Paths.polynomial parameter)
        (Geometry.move elimination circuit.first.regular
          (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))).rebase
        connector.path connector.withinAmbient

attribute [local irreducible] Realization.DetourSpine components

/-- The four actual signed quarter cofolds retain their literal preceding finishes and original seam comparisons.

Each head uses the stored numeric bank on the one cached grid. The existing
seam casts preserve its entire actual finish Owner and supply the next
optional start with the same retained relation to the old paid Owner. This
carrier contains no desired signed closure or canonical period relation.
-/
@[expose] def Signed
    (cached : DetourCache lines base)
    (reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point) :=
  let heads := cached.components
  Σ first : Realization.DetourSpine elimination clearances cached.val.1 reference
      firstInput sourceOwner agreement execution.first lines.1 cached.onGrid.1 heads.1 none,
  let secondStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.first lines.1 cached.onGrid.1 heads.1 none
      first secondInput Waist.directions_join.1 circuit.first_second execution.second.seam
  Σ second : Realization.DetourSpine elimination clearances cached.val.1 reference
      secondInput execution.second.seam.owner execution.second.seam.nextAgreement
      execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart),
  let thirdStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart)
      second thirdInput Waist.directions_join.2.1 circuit.second_third execution.third.seam
  Σ third : Realization.DetourSpine elimination clearances cached.val.1 reference
      thirdInput execution.third.seam.owner execution.third.seam.nextAgreement
      execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart),
  let fourthStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart)
      third fourthInput Waist.directions_join.2.2.1 circuit.third_fourth execution.fourth.seam
  Realization.DetourSpine elimination clearances cached.val.1 reference
      fourthInput execution.fourth.seam.owner execution.fourth.seam.nextAgreement
      execution.fourth.paid lines.2.2.2 cached.onGrid.2.2.2 heads.2.2.2 (some fourthStart)

/-- Prepare the four actual signed quarter cofolds once in their retained original circuit order. -/
def sign
    (cached : DetourCache lines base)
    (reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point) : Signed cached reference :=
  let heads := cached.components
  let first := Input.Realization.prepareDetour elimination clearances cached.val.1 reference
      execution.first lines.1 cached.onGrid.1 heads.1 none
  let secondStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.first lines.1 cached.onGrid.1 heads.1 none
      first secondInput Waist.directions_join.1 circuit.first_second execution.second.seam
  let second := Input.Realization.prepareDetour elimination clearances cached.val.1 reference
      execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart)
  let thirdStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart)
      second thirdInput Waist.directions_join.2.1 circuit.second_third execution.third.seam
  let third := Input.Realization.prepareDetour elimination clearances cached.val.1 reference
      execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart)
  let fourthStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart)
      third fourthInput Waist.directions_join.2.2.1 circuit.third_fourth execution.fourth.seam
  let fourth := Input.Realization.prepareDetour elimination clearances cached.val.1 reference
      execution.fourth.paid lines.2.2.2 cached.onGrid.2.2.2 heads.2.2.2 (some fourthStart)
  ⟨first, second, third, fourth⟩

namespace Signed

/-- Read the literal final Owner of the fourth retained signed cofold. -/
@[expose] def finishOwner
    (cached : DetourCache lines base)
    (reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (prepared : Signed cached reference) :
    OwnerAt site parameter .fourth (of_decide_eq_true rfl) execution.fourth.paid.finishEndpoint :=
  let heads := cached.components
  let first := prepared.1
  let secondStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.first lines.1 cached.onGrid.1 heads.1 none
      first secondInput Waist.directions_join.1 circuit.first_second execution.second.seam
  let second := prepared.2.1
  let thirdStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart)
      second thirdInput Waist.directions_join.2.1 circuit.second_third execution.third.seam
  let third := prepared.2.2.1
  let fourthStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart)
      third fourthInput Waist.directions_join.2.2.1 circuit.third_fourth execution.fourth.seam
  let fourth := prepared.2.2.2
  Realization.DetourSpine.finishOwner elimination clearances cached.val.1 reference
    fourthInput execution.fourth.seam.owner execution.fourth.seam.nextAgreement
    execution.fourth.paid lines.2.2.2 cached.onGrid.2.2.2 heads.2.2.2 (some fourthStart) fourth

/-- Derive the actual signed terminal-to-initial root comparison from the stored fourth comparison and old closing.

Both original and newly prepared Owners remain retained. This operation
only composes the actual endpoint relation already stored on the cofold
with the original circuit's paid return comparison; it does not assert a
primitive integral equality or a vanishing face residual.
-/
def equivalent
    (cached : DetourCache lines base)
    (reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (prepared : Signed cached reference) :
    NamedEquivalent (ownerName (finishOwner cached reference prepared)) (ownerName sourceOwner) := by
  let heads := cached.components
  let first := prepared.1
  let secondStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.first lines.1 cached.onGrid.1 heads.1 none
      first secondInput Waist.directions_join.1 circuit.first_second execution.second.seam
  let second := prepared.2.1
  let thirdStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart)
      second thirdInput Waist.directions_join.2.1 circuit.second_third execution.third.seam
  let third := prepared.2.2.1
  let fourthStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart)
      third fourthInput Waist.directions_join.2.2.1 circuit.third_fourth execution.fourth.seam
  let fourth := prepared.2.2.2
  have fourthEquivalent := Realization.DetourSpine.equivalent elimination clearances cached.val.1 reference
    fourthInput execution.fourth.seam.owner execution.fourth.seam.nextAgreement
    execution.fourth.paid lines.2.2.2 cached.onGrid.2.2.2 heads.2.2.2 (some fourthStart) fourth
  have returned := execution.returnEquivalent
  unfold ownerRootName at returned
  exact fourthEquivalent.trans returned

/-- Read the same actual signed terminal Owner at the identical original first-quarter base point. -/
@[expose] def returnOwner
    (cached : DetourCache lines base)
    (reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (prepared : Signed cached reference) :
    OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint :=
  Transport.Seam.castOwner (site := site) (parameter := parameter)
    (leftQuarter := .fourth) (rightQuarter := .first)
    execution.fourth.paid.finish_time firstInput.source_time Waist.directions_join.2.2.2
    (finishOwner cached reference prepared)

/-- The closed-base index transport preserves the entire actual signed terminal Owner. -/
theorem returnOwner_heq
    (cached : DetourCache lines base)
    (reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (prepared : Signed cached reference) :
    HEq (returnOwner cached reference prepared) (finishOwner cached reference prepared) :=
  Transport.Seam.castOwner_heq (site := site) (parameter := parameter)
    (leftQuarter := .fourth) (rightQuarter := .first)
    execution.fourth.paid.finish_time firstInput.source_time Waist.directions_join.2.2.2
    (finishOwner cached reference prepared)

/-- The actual closed-base returned Owner retains the same paid initial-root comparison. -/
def returnEquivalent
    (cached : DetourCache lines base)
    (reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (prepared : Signed cached reference) :
    NamedEquivalent (ownerName (returnOwner cached reference prepared)) (ownerName sourceOwner) := by
  have same := Transport.Seam.castOwner_name (site := site) (parameter := parameter)
    (leftQuarter := .fourth) (rightQuarter := .first)
    execution.fourth.paid.finish_time firstInput.source_time Waist.directions_join.2.2.2
    (finishOwner cached reference prepared)
  unfold ownerRootName at same
  exact NamedEquivalent.transport same.symm rfl (equivalent cached reference prepared)

/-- Compare the actual fourth-quarter return with the retained first entry through the original paid circuit closure.

The first spine keeps its original absent supplied start. The existing
closed-base root certificate pays its handoff from the actual fourth
finish, and the shared quarter operation derives connector cancellation.
Both saved middle-root selections remain inputs to that same comparison.
-/
def closingEntryEquivalent
    (cached : DetourCache lines base)
    (reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (prepared : Signed cached reference) := by
  let heads := cached.components
  let secondStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.first lines.1 cached.onGrid.1 heads.1 none prepared.1
    secondInput Waist.directions_join.1 circuit.first_second execution.second.seam
  let thirdStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart) prepared.2.1
    thirdInput Waist.directions_join.2.1 circuit.second_third execution.third.seam
  let fourthStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart) prepared.2.2.1
    fourthInput Waist.directions_join.2.2.1 circuit.third_fourth execution.fourth.seam
  let closingStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
    execution.fourth.paid lines.2.2.2 cached.onGrid.2.2.2 heads.2.2.2 (some fourthStart) prepared.2.2.2
    firstInput Waist.directions_join.2.2.2 circuit.fourth_first execution.closing
  have same : closingStart.1 = returnOwner cached reference prepared :=
    Realization.DetourSpine.nextStart_owner_eq elimination clearances cached.val.1 reference
      execution.fourth.paid lines.2.2.2 cached.onGrid.2.2.2 heads.2.2.2 (some fourthStart) prepared.2.2.2
      firstInput Waist.directions_join.2.2.2 circuit.fourth_first execution.closing
  have handoff := NamedEquivalent.transport (congrArg ownerName same).symm rfl
    (returnEquivalent cached reference prepared)
  exact Realization.DetourSpine.nextEntryEquivalent elimination clearances cached.val.1 reference
    execution.fourth.paid lines.2.2.2 cached.onGrid.2.2.2 heads.2.2.2 (some fourthStart) prepared.2.2.2
    firstInput Waist.directions_join.2.2.2 circuit.fourth_first execution.closing
    sourceOwner agreement execution.first lines.1 cached.onGrid.1 heads.1 none prepared.1 handoff

/-- Join the four actual signed traces through their retained seam index transports and exact physical closure.

Every original entry, retained grid Walk and return remains in its actual
signed order. The terminal Owner is transported only to the identical
base point; its relation to the initial Owner is separately retained by
returnEquivalent. No primitive jump or physical residual is discarded.
-/
def trace
    (cached : DetourCache lines base)
    (reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (prepared : Signed cached reference) :
    OwnerPath (Paths.polynomial parameter)
      (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter) sourceOwner
      (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter)
      (returnOwner cached reference prepared) := by
  let heads := cached.components
  let first := prepared.1
  let secondStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.first lines.1 cached.onGrid.1 heads.1 none
      first secondInput Waist.directions_join.1 circuit.first_second execution.second.seam
  let second := prepared.2.1
  let thirdStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart)
      second thirdInput Waist.directions_join.2.1 circuit.second_third execution.third.seam
  let third := prepared.2.2.1
  let fourthStart := Realization.DetourSpine.nextStart elimination clearances cached.val.1 reference
      execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart)
      third fourthInput Waist.directions_join.2.2.1 circuit.third_fourth execution.fourth.seam
  let fourth := prepared.2.2.2
  let firstTrace := Realization.DetourSpine.trace elimination clearances cached.val.1 reference
    firstInput sourceOwner agreement
    execution.first lines.1 cached.onGrid.1 heads.1 none first
  let secondTrace := Realization.DetourSpine.trace elimination clearances cached.val.1 reference
    secondInput execution.second.seam.owner execution.second.seam.nextAgreement
    execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1 (some secondStart) second
  let thirdTrace := Realization.DetourSpine.trace elimination clearances cached.val.1 reference
    thirdInput execution.third.seam.owner execution.third.seam.nextAgreement
    execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1 (some thirdStart) third
  let fourthTrace := Realization.DetourSpine.trace elimination clearances cached.val.1 reference
    fourthInput execution.fourth.seam.owner execution.fourth.seam.nextAgreement
    execution.fourth.paid lines.2.2.2 cached.onGrid.2.2.2 heads.2.2.2 (some fourthStart) fourth
  have firstsecond := Transport.Seam.point_eq (site := site) (parameter := parameter)
    (leftQuarter := .first) (rightQuarter := .second)
    execution.first.finish_time secondInput.source_time Waist.directions_join.1
  have secondOwner := Realization.DetourSpine.nextStart_owner_heq
    elimination clearances cached.val.1 reference execution.first lines.1 cached.onGrid.1 heads.1
    none first secondInput Waist.directions_join.1 circuit.first_second execution.second.seam
  let secondJoined := OwnerPath.castEndpoints firstsecond.symm rfl secondOwner HEq.rfl secondTrace
  have secondthird := Transport.Seam.point_eq (site := site) (parameter := parameter)
    (leftQuarter := .second) (rightQuarter := .third)
    execution.second.paid.finish_time thirdInput.source_time Waist.directions_join.2.1
  have thirdOwner := Realization.DetourSpine.nextStart_owner_heq
    elimination clearances cached.val.1 reference execution.second.paid lines.2.1 cached.onGrid.2.1 heads.2.1
    (some secondStart) second thirdInput Waist.directions_join.2.1 circuit.second_third execution.third.seam
  let thirdJoined := OwnerPath.castEndpoints secondthird.symm rfl thirdOwner HEq.rfl thirdTrace
  have thirdfourth := Transport.Seam.point_eq (site := site) (parameter := parameter)
    (leftQuarter := .third) (rightQuarter := .fourth)
    execution.third.paid.finish_time fourthInput.source_time Waist.directions_join.2.2.1
  have fourthOwner := Realization.DetourSpine.nextStart_owner_heq
    elimination clearances cached.val.1 reference execution.third.paid lines.2.2.1 cached.onGrid.2.2.1 heads.2.2.1
    (some thirdStart) third fourthInput Waist.directions_join.2.2.1 circuit.third_fourth execution.fourth.seam
  let fourthJoined := OwnerPath.castEndpoints thirdfourth.symm rfl fourthOwner HEq.rfl fourthTrace
  let joined := firstTrace.append (secondJoined.append (thirdJoined.append fourthJoined))
  have closing := Transport.Seam.point_eq (site := site) (parameter := parameter)
    (leftQuarter := .fourth) (rightQuarter := .first)
    execution.fourth.paid.finish_time firstInput.source_time Waist.directions_join.2.2.2
  exact OwnerPath.castEndpoints rfl closing HEq.rfl (returnOwner_heq cached reference prepared).symm joined

end Signed

end DetourCache

end Lines

/-- The whole original line/numeric/reference producer result retains its exact original dependent owners. -/
@[expose] def DetourReference {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : Hyperelliptic.Branches.BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : Hyperelliptic.Branches.BranchCellBank (Fibre.frameCurve frame) branches higher) :=
    Σ lines : { value : Lines execution elimination clearances //
        value = Lines.build execution elimination clearances },
      Σ _cached : Lines.DetourCache lines.val bank.grid,
        Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop (Paths.polynomial parameter)
          (Geometry.move elimination circuit.first.regular
            (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))

/-- Produce the actual four-quarter detour and its genuine moved-vertex reference from the same retained branch bank.

The original line producer and complete numeric detour run once and stay
in their certified caches. Their actual initial moved point obtains the
reference from the SAME bank. This constructs the signed Block reference
input; it does not assert closure of the new signed lift or any integral
or canonical homology identification.
-/
def detourWithReference {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : Hyperelliptic.Branches.BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : Hyperelliptic.Branches.BranchCellBank (Fibre.frameCurve frame) branches higher) :
    DetourReference execution elimination clearances frame bank :=
  let lines := Lines.build execution elimination clearances
  let cached := lines.prepareDetour bank.grid
  let reference := lines.referenceAt frame bank cached.1 rfl
    (Geometry.move elimination circuit.first.regular
      (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))
    cached.2.2.property
  ⟨⟨lines, rfl⟩, ⟨cached, rfl⟩, reference⟩

namespace DetourReference

/-- The retained original producer equation identifies the ambient of its same stored reference value. -/
theorem ambient_eq {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : Hyperelliptic.Branches.BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : Hyperelliptic.Branches.BranchCellBank (Fibre.frameCurve frame) branches higher)
    (retained : { value : DetourReference execution elimination clearances frame bank //
      value = execution.detourWithReference elimination clearances frame bank }) :
    retained.val.2.2.ambient = RootRadius.Box.largeSquareBox (Paths.polynomial parameter) := by
  have selected := congrArg (fun value : DetourReference execution elimination clearances frame bank =>
    value.2.2.ambient) retained.property
  refine selected.trans ?_
  unfold detourWithReference
  let lines := Lines.build execution elimination clearances
  let cached := lines.prepareDetour bank.grid
  exact Lines.referenceAt_ambient lines frame bank cached.1 rfl
    (Geometry.move elimination circuit.first.regular
      (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))
    cached.2.2.property

/-- Put the original framed branch labels on this SAME retained detour grid.

The old canonical frame and root family remain the inputs. Only the
original branch locator refines their already retained states; each new
selected cell is certified inside its old labelled cell. This produces
finite branch incidence, not a second canonical period programme or an
identification of the connector integrals.
-/
def framedBank {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : Hyperelliptic.Branches.BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : Hyperelliptic.Branches.FramedBranchCellBank (Fibre.frameCurve frame) branches higher)
    (retained : DetourReference execution elimination clearances frame bank.toBranchCellBank) :
    { target : Hyperelliptic.Branches.FramedBranchCellBank (Fibre.frameCurve frame) branches higher //
      target.grid = retained.2.1.val.1 ∧
      ∀ index, (target.cell index).box.Refines (bank.cell index).box } := by
  have same : retained.2.1.val.1 = (retained.1.val.detour bank.grid).1 :=
    congrArg Sigma.fst retained.2.1.property
  have included : Grid.Extension.CoordinateInclusion bank.grid retained.2.1.val.1 :=
    Eq.mpr (congrArg (Grid.Extension.CoordinateInclusion bank.grid) same)
      (retained.1.val.detour_inclusion bank.grid)
  let target := bank.onGrid retained.2.1.val.1 included
  have bankEq := bank.onGrid_toBranchCellBank retained.2.1.val.1 included
  have gridEq : target.grid = retained.2.1.val.1 :=
    (congrArg (fun value : Hyperelliptic.Branches.BranchCellBank
      (Fibre.frameCurve frame) branches higher => value.grid) bankEq).trans
      (bank.toBranchCellBank.onGrid_grid retained.2.1.val.1 included)
  refine ⟨target, gridEq, ?_⟩
  intro index
  exact Eq.mpr (congrArg (fun value : Hyperelliptic.Branches.BranchCellBank
      (Fibre.frameCurve frame) branches higher =>
      (value.cell index).box.Refines (bank.cell index).box) bankEq)
    (bank.toBranchCellBank.onGrid_cell_refines retained.2.1.val.1 included index)

end DetourReference

/-- Prepare the actual four signed quarters from one retained numeric/reference producer result.

The original line banks, richer numeric heads, closed Walk and branch-bank
reference are computed once. The signed cofold consumes those same head
banks and threads literal new finishes through the original retained seams.
No final root, integral or canonical programme identification is an input.
-/
def prepareSignedDetour {degreeBound : Nat}
    (execution : Execution.Cache initial secondInput thirdInput fourthInput)
    (elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound)
    (clearances : AxisClearances elimination) (frame : Paths.Frame parameter)
    {branches : Hyperelliptic.Branches.BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    (bank : Hyperelliptic.Branches.BranchCellBank (Fibre.frameCurve frame) branches higher) :
    Σ retained : { value : DetourReference execution elimination clearances frame bank //
        value = execution.detourWithReference elimination clearances frame bank },
      Lines.DetourCache.Signed retained.val.2.1
        (retained.val.2.1.pointReferences retained.val.2.2
          (DetourReference.ambient_eq execution elimination clearances frame bank retained)) :=
  let retained := execution.detourWithReference elimination clearances frame bank
  let references := retained.2.1.pointReferences retained.2.2
    (DetourReference.ambient_eq execution elimination clearances frame bank ⟨retained, rfl⟩)
  let prepared := retained.2.1.sign references
  ⟨⟨retained, rfl⟩, prepared⟩

namespace Lines.DetourCache.Signed

open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)

variable {degreeBound : Nat}
variable {elimination : AxisEliminationCertificate (Paths.polynomial parameter) degreeBound}
variable {clearances : AxisClearances elimination}
variable {lines : Lines execution elimination clearances}
variable {base : Grid.ClearGrid (Paths.polynomial parameter)
  (RootRadius.Box.largeSquareBox (Paths.polynomial parameter))}

attribute [local irreducible] Realization.DetourSpine components

/-- Read the literal first middle Owner from the complete four-quarter signed cofold.

The same stored first numeric head bank and actual first signed quarter
supply the Owner. Both original and fine first quarters are handled by
the existing shared readback; the other three quarters, seams, closing
comparison and complete numerical loop remain untouched.
-/
@[expose] def middleSource
    (cached : DetourCache lines base)
    (reference : ∀ point, Grid.FromStates.ContainsVertex cached.val.1 point →
      WindingOneLoop (Paths.polynomial parameter) point)
    (prepared : Signed cached reference) :
    Riemann.Topology.SquareRootContinuationChain.Owner ((Paths.polynomial parameter).eval
      (Geometry.move elimination circuit.first.regular
        (coordinate site parameter 2 .first (of_decide_eq_true rfl) firstInput.sourceEndpoint.parameter))) :=
  let heads := cached.components
  Realization.DetourSpine.middleSource elimination clearances cached.val.1 reference
    firstInput sourceOwner agreement execution.first lines.1 cached.onGrid.1 heads.1 none prepared.1

end Lines.DetourCache.Signed

end Execution.Cache

end ActualDetours

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
