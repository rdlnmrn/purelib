module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Riemann.Periods.NewtonConjugatePeriodReadback
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalPeriodComparison
import Purelib.Riemann.RootContinuation.NewtonHomogeneousConjugateReadback
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchAggregate

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBranchAggregate.PairedBranchRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateRegularAggregate.PairedRegularRequests

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Data.Rat

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

public section

/-! Cache the actual regular and branch requests behind the conjugate physical
comparison. Its certificate applies to the retained requests and shared sample. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization (extract mix)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedRegularAggregate (PairedRegularRequests)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate (PairedBranchRequests)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.PolarizedCorrections (PolarizedCorrectionRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.ExteriorTotal (resplitPhysicalExteriorCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPeriodArea (resplitPeriodArea)
open Purelib.Riemann.Periods.NewtonConjugatePeriodReadback (conjugateResplitPeriodArea extract_conjugate_resplit)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OrderedBranchPolygons (branchSheet)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm perTerm_positive)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    (prepared : Prepared paired)
  {preparation : NewtonPreparation
    base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {firstIndex secondIndex : Fin genus}

section ConjugatePhysicalRequest

/-- The retained resplit compiler for the original ordered branch partition and chosen sheet. -/
@[expose] def compiler (newSheet : Fin 2) :=
  CircuitPartition.compileResplit grid.shrunk.included current.edges current.vertices
    (fun point member => (BranchCellBank.referenceAt grid.punctured.bank.toBranchCellBank point member).toLoop)
    (FramedBranchCellBank.baseMember base.bank) ordered.prepared.partition newSheet

/-- The actual regular-region requests with their allocated share of the original conjugate error budget. -/
@[expose] def RegularRequests (newSheet : Fin 2)
    (first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential firstIndex))
    (second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) (floor : Nat) :=
  PairedRegularAggregate.PairedRegularRequests first second
    (Aggregate.perTerm (Aggregate.perTerm (error / 4) 2)
      (compiler (ordered :=
      ordered) (current := current) newSheet).regulars.length)
    floor (compiler (ordered :=
      ordered) (current := current) newSheet).regulars

/-- The actual branch-region requests on the retained excision entries and ordered branch sheets. -/
@[expose] def BranchRequests (newSheet : Fin 2) (excision : Excision.AllHoleExcision grid current)
    (first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential firstIndex))
    (second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) (floor : Nat) :=
  PairedBranchAggregate.PairedBranchRequests bank (OrderedBranchPolygons.branchSheet ordered newSheet) first second
    (Aggregate.perTerm (Aggregate.perTerm (error / 4) 2) excision.entries.length) floor excision.entries

/-- The complete conjugate physical comparison value.

It retains the original exterior area, corrected period area and physical exterior correction on the same edge
valuations. -/
@[expose] def physical (newSheet : Fin 2)
    (first second : Stokes.OrientedEdge current.vertices.count → Data.Gaussian.Basic.Canonical) : Gaussian :=
  BilinearPolarization.extract fun coefficient =>
    let value := BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj (first edge)) second
      coefficient
    current.edges.chainArea current.vertices value
      (grid.shrunk.included.resplit base.bank.exterior (FramedBranchCellBank.baseMember base.bank)) newSheet +
      OriginalPeriodArea.resplitPeriodArea prepared grid.shrunk.included current.edges current.vertices newSheet value -
      ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired) grid.shrunk.included current.edges
        current.vertices newSheet value

/-- The exterior term is retained separately from the corrected period pairing. -/
@[expose] def exterior (newSheet : Fin 2)
    (first second : Stokes.OrientedEdge current.vertices.count → Data.Gaussian.Basic.Canonical) : Gaussian :=
  BilinearPolarization.extract fun coefficient =>
    let value := BilinearPolarization.mix (fun edge => Data.Gaussian.Basic.conj (first edge)) second
      coefficient
    current.edges.chainArea current.vertices value
      (grid.shrunk.included.resplit base.bank.exterior (FramedBranchCellBank.baseMember base.bank)) newSheet -
      ExteriorTotal.resplitPhysicalExteriorCorrection (paired := paired) grid.shrunk.included current.edges
        current.vertices newSheet value

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest in
/-- The complete conjugate physical value splits into the original corrected period pairing and retained exterior term.
-/
theorem physical_split (newSheet : Fin 2)
    (first second : Stokes.OrientedEdge current.vertices.count → Data.Gaussian.Basic.Canonical) :
    physical prepared newSheet
      first second =
      NewtonConjugatePeriodReadback.conjugateResplitPeriodArea prepared grid.shrunk.included current.edges
        current.vertices newSheet first second +
        exterior (paired := paired) newSheet first second := by
  have linear (outer period correction : Data.Gaussian.Basic.Canonical → Data.Gaussian.Basic.Canonical) :
      BilinearPolarization.extract (fun coefficient => outer coefficient + period coefficient - correction coefficient)
        =
        BilinearPolarization.extract period + BilinearPolarization.extract (fun coefficient => outer coefficient -
          correction coefficient) := by
    unfold BilinearPolarization.extract
    ring1
  rw [← NewtonConjugatePeriodReadback.extract_conjugate_resplit prepared]
  exact linear _ _ _

/-- The certificate names the cached requests, rather than recomputing their geometric data when a later sample or
coefficient vector is supplied. -/
@[expose] def Accurate {newSheet : Fin 2} {excision : Excision.AllHoleExcision grid current}
    {first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential firstIndex)}
    {second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential secondIndex)}
    {error : Fraction.Rational} {floor : Nat}
    (regular : RegularRequests
      (ordered := ordered) newSheet first second error floor)
    (branch : BranchRequests
      (ordered := ordered) newSheet excision first second error floor) (index : Nat) : Prop :=
  ∀ stage (leftBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential firstIndex) stage domains)
    (rightBank : PrimitiveData.FacePrimitiveBank (PeriodMatrix.standardDifferential secondIndex) stage domains)
    (left : TrianglePrimitiveReadings.TriangleReadings leftBank current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings rightBank current.mesh)
    (leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values)
    (rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values)
    (pair : SewnConjugateSamples.ConjugatePair leftSurface rightSurface), index ≤ stage →
    let regularSamples := ConjugateSamples.build left right leftSurface rightSurface pair regular
    let branchSamples := ConjugateSamples.build left right leftSurface rightSurface pair branch
    let area := physical prepared
      newSheet (CanonicalEdgeValues.edgeValuation current.mesh left.values)
      (CanonicalEdgeValues.edgeValuation current.mesh right.values)
    Data.Gaussian.Norm.Basic.normSq (pair.boundaryArea - (regularSamples.corrections +
      branchSamples.corrections) - (area + area)) < error

set_option genInjectivity false in
/-- The cached requests and paid stage for one original conjugate physical comparison.

Regular and branch requests keep their original geometric owners, and the certificate applies to those exact retained
requests at every later shared sample. -/
structure PairRequest (newSheet : Fin 2) (excision : Excision.AllHoleExcision grid current)
    (first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential firstIndex))
    (second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) (floor : Nat) where
  /-- The cached original regular-region requests. -/ regular :
    RegularRequests (ordered :=
    ordered) newSheet first second error floor
  /-- The cached original branch-region requests on the retained excision entries. -/ branch :
    BranchRequests (ordered :=
    ordered) newSheet excision first second error floor
  /-- The retained terminal and connector correction request on the actual compiler. -/ corrections :
    PolarizedCorrections.PolarizedCorrectionRequest (paired := paired) grid.shrunk.included
    (compiler (ordered := ordered)
      (current := current) newSheet) first second (error / 16)
  /-- The cached common stage paying the retained regular, branch and correction requests. -/ index : Nat
  /-- The requested floor is at most the retained common stage. -/ floor_le : floor ≤ index
  /-- The actual cached requests satisfy their comparison at every later shared numerical stage. -/ accurate :
    Accurate prepared regular
    branch index

constructive_injectivity PairRequest

namespace PairRequest

/-- Prepare and retain the original regular, branch and correction requests with a common paid stage. -/
@[expose] def build (newSheet : Fin 2) (excision : Excision.AllHoleExcision grid current)
    (first : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential firstIndex))
    (second : MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential secondIndex))
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    PairRequest prepared newSheet
      excision first second error floor := by
  let compiled := compiler (ordered
    := ordered) (current := current) newSheet
  have partPositive := Aggregate.perTerm_positive (Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : Fraction.Rational) < 4)) 2
  let regular := PairedRegularRequests.build first second
    (Aggregate.perTerm (Aggregate.perTerm (error / 4) 2) compiled.regulars.length) (Aggregate.perTerm_positive
      partPositive _) floor compiled.regulars
  let branch := PairedBranchRequests.build bank (OrderedBranchPolygons.branchSheet ordered newSheet) first second
    (Aggregate.perTerm (Aggregate.perTerm (error / 4) 2) excision.entries.length) (Aggregate.perTerm_positive
      partPositive _) floor excision.entries
  let corrections := PolarizedCorrectionRequest.build (paired := paired) grid.shrunk.included compiled first second
    (error / 16) (Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 16)) floor
  let index := max (max regular.index branch.index) (corrections.index floor)
  have certified := ConjugatePhysicalPeriodComparison.conjugate_physical_period_accurate prepared newSheet excision
    first second error positive floor
  exact ⟨regular, branch, corrections, index, certified.1, certified.2⟩

variable {prepared} {newSheet : Fin 2} {excision :
  AllHoleExcision grid current}
  {first : FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential firstIndex)}
  {second : FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential secondIndex)}
  {error : Rational} {floor stage : Nat}
  {leftBank : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential firstIndex) stage domains}
  {rightBank : FacePrimitiveBank
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential secondIndex) stage domains}
  (left : TriangleReadings leftBank
    current.mesh) (right : TriangleReadings
    rightBank current.mesh)
  (leftSurface : CachedSample current.cutPolygon.patch left.values)
  (rightSurface : CachedSample current.cutPolygon.patch
    right.values)
  (pair : ConjugatePair leftSurface rightSurface)

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest in
set_option genInjectivity false in
/-- The actual regular and branch readbacks and cached scalars for a retained conjugate request.

Every cache is tied by an equality to the supplied shared readings and their original sewn-surface pair. -/
structure Sample (request :
  PairRequest prepared newSheet
  excision first second error floor) where
  /-- The actual conjugate samples of the retained regular-region requests. -/ regular :
    PairedRegularRequests.ConjugateSamples left right leftSurface rightSurface pair request.regular
  /-- The retained regular sample is exactly the readback of the cached regular requests. -/ regular_eq : regular =
    ConjugateSamples.build left right leftSurface rightSurface pair request.regular
  /-- The actual conjugate samples of the retained branch-region requests. -/ branch :
    PairedBranchRequests.ConjugateSamples left right leftSurface rightSurface pair request.branch
  /-- The retained branch sample is exactly the readback of the cached branch requests. -/ branch_eq : branch =
    ConjugateSamples.build left right leftSurface rightSurface pair request.branch
  /-- The cached sum of the actual regular and branch cut corrections. -/ correction : Data.Gaussian.Basic.Canonical
  /-- The correction cache is exactly the sum of the two retained correction readbacks. -/ correction_eq : correction =
    regular.corrections + branch.corrections
  /-- The cached original physical exterior contribution. -/ exterior : Data.Gaussian.Basic.Canonical
  /-- The exterior cache is exactly the original physical exterior term on these edge readings. -/ exterior_eq :
    exterior = ConjugatePhysicalRequest.exterior (paired :=
    paired) newSheet
    (CanonicalEdgeValues.edgeValuation current.mesh left.values) (CanonicalEdgeValues.edgeValuation current.mesh
      right.values)
  /-- The cached complete conjugate physical comparison value. -/ area : Data.Gaussian.Basic.Canonical
  /-- The area cache is exactly the original physical comparison on the retained edge readings. -/ area_eq : area =
    physical prepared newSheet
    (CanonicalEdgeValues.edgeValuation current.mesh left.values)
    (CanonicalEdgeValues.edgeValuation current.mesh right.values)

constructive_injectivity Sample

namespace Sample

open Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest in
/-- Acquire the retained regular and branch request samples once and cache their exact correction and physical values.
-/
@[expose] def build (request :
  PairRequest prepared newSheet
  excision first second error floor) :
    Sample left right
      leftSurface rightSurface pair request :=
  let regular := ConjugateSamples.build left right leftSurface rightSurface pair request.regular
  let branch := ConjugateSamples.build left right leftSurface rightSurface pair request.branch
  let firstValue := CanonicalEdgeValues.edgeValuation current.mesh left.values
  let secondValue := CanonicalEdgeValues.edgeValuation current.mesh right.values
  let exterior := ConjugatePhysicalRequest.exterior (paired
    := paired) newSheet firstValue secondValue
  ⟨regular, rfl, branch, rfl, regular.corrections + branch.corrections, rfl, exterior, rfl,
    NewtonConjugatePeriodReadback.conjugateResplitPeriodArea prepared grid.shrunk.included current.edges
      current.vertices newSheet firstValue secondValue + exterior,
    (physical_split prepared
      newSheet firstValue secondValue).symm⟩

end Sample

variable {left right leftSurface rightSurface pair}

namespace Sample

/-- The actual retained correction and physical caches satisfy the original request at every paid stage. -/
theorem accurate {request :
  PairRequest prepared newSheet
  excision first second error floor}
    (sample : Sample
      left right leftSurface rightSurface pair request) (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (pair.boundaryArea - sample.correction - (sample.area + sample.area)) <
      error := by
  rw [sample.correction_eq, sample.regular_eq, sample.branch_eq, sample.area_eq]
  exact request.accurate stage leftBank rightBank left right leftSurface rightSurface pair later

end Sample

end PairRequest
end ConjugatePhysicalRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalRequest
