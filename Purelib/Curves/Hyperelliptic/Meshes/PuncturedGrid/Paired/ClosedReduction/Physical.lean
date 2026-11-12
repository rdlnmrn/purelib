module
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Ordinary
import Purelib.Riemann.Readings.PreparedPrimitiveSamples.Numerator

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ClosedReduction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalLoopRequests
public import Purelib.Topology.Surface.Sewing.PhysicalCycleCoordinates.Comparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # Paid physical remainder of an actual corrected-basis reduction

The original closed-word reduction already retains its complete physical
loop row and its factory on the same lifted boundary. Its coefficient gain
selects the original loop request target before the shared cochain is sampled.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates.Reduction

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential (Ordinary)
open Purelib.Riemann.Readings
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Chain
open Purelib.Topology.Polygon.Stokes (OrientedEdge triangleEdgeOccurrences)
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles.PolygonStokes (BoundaryCycleDecomposition)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {lifted : LiftedPuncturedGrid base} {bank : BasedBranchBank lifted} {basisSheet : Fin 2}
    {ordered : BasedBranchBank.Ordered bank basisSheet} {paired : OrderedBranchPairs.Ordered.Paired ordered}
    {prepared : PeriodPrograms.Prepared paired} {basis : prepared.GeometricBasis}
    {word : List (OrientedEdge lifted.vertices.count)} {sourceSheet : Fin 2}
    {supported : CutPath.Supported (SewingConnected.SewnPatch.originalEdges lifted.cutPolygon.patch) word}
    {closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word
      (BasedBranchBank.anchor lifted sourceSheet) (BasedBranchBank.anchor lifted sourceSheet)}
    {boundary : BoundaryCycleDecomposition (triangleEdgeOccurrences lifted.mesh.triangulation.faces)}
    {factory : boundary = lifted.boundaryComponents}
    (retained : ClosedCoordinates.Reduction basis word sourceSheet supported closed boundary factory)

/-- Allocate and prepare the original exterior/hole requests using the actual physical row's finite coefficient gain.

Only request and paired-walk caches are constructed. The numerical bank and
triangle readings remain absent until a caller selects a sufficient common
stage, which may also pay its face and annular correction requests.
-/
def preparePhysicalLoops (domains : FaceDomainBank lifted.frames base.faces.regulars)
    (differential : Differential genus) (target : Rational) (positive : 0 < target) (minimum : Nat)
    (polynomial : Option (Ordinary curve.polynomial) := none) :
    PhysicalLoopRequests.Preparation lifted domains differential (retained.loops.loopTarget target)
      (retained.loops.loopTarget_positive positive) minimum polynomial :=
  PhysicalLoopRequests.prepare lifted domains differential (retained.loops.loopTarget target)
    (retained.loops.loopTarget_positive positive) minimum polynomial

/-- The same later shared canonical cochain pays the complete actual weighted exterior/hole contribution strictly.

The whole original boundary factory transports the actual cycle list. The
finite coefficient gain retains exterior parity, doubled-hole words and every
integer occurrence; no physical-paired-zero simplification is used.
-/
theorem physicalLoops_accurate (degree : curve.polynomial.natDegree = 2 * genus + 1)
    {domains : FaceDomainBank lifted.frames base.faces.regulars} {differential : Differential genus}
    {target : Rational} (positive : 0 < target) {minimum : Nat}
    (requests : PhysicalLoopRequests.Preparation lifted domains differential (retained.loops.loopTarget target)
      (retained.loops.loopTarget_positive positive) minimum)
    {stage : Nat} {shared : FacePrimitiveBank differential stage domains}
    (readings : TriangleReadings shared lifted.mesh) (later : requests.index ≤ stage) :
    normSq (gaussianSum (retained.loops.rows.map (fun entry => (entry.1 : Canonical) *
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) entry.2))) <
        target := by
  apply retained.loops.loop_requested_lt _ positive
  intro original member
  have same : boundary.cycles = lifted.boundaryLoops := congrArg
    (fun value : BoundaryCycleDecomposition (triangleEdgeOccurrences lifted.mesh.triangulation.faces) => value.cycles)
    factory
  have inLoops : original ∈ lifted.boundaryLoops :=
    Eq.mp (congrArg (fun words => original ∈ words) same) member
  exact requests.accurate degree readings later original inLoops

/-- The original full physical-vector reading is paid by the same actual weighted-loop requests and later cochain. -/
theorem physicalValue_accurate (degree : curve.polynomial.natDegree = 2 * genus + 1)
    {domains : FaceDomainBank lifted.frames base.faces.regulars} {differential : Differential genus}
    {target : Rational} (positive : 0 < target) {minimum : Nat}
    (requests : PhysicalLoopRequests.Preparation lifted domains differential (retained.loops.loopTarget target)
      (retained.loops.loopTarget_positive positive) minimum)
    {stage : Nat} {shared : FacePrimitiveBank differential stage domains}
    (readings : TriangleReadings shared lifted.mesh) (later : requests.index ≤ stage) :
    normSq (retained.coordinates.physicalValue
      (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)) < target := by
  have original := retained.physicalLoops_accurate degree positive requests readings later
  have same := PhysicalCycleCoordinates.Data.value_eq retained.loops
    (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
  change retained.coordinates.physicalValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) = _ at same
  exact Eq.mpr (congrArg (fun value : Canonical => normSq value < target) same) original

/-- Actual retained polynomial comparisons pay the full original weighted physical-loop contribution. -/
theorem physicalLoops_comparison_accurate (degree : curve.polynomial.natDegree = 2 * genus + 1)
    {polynomial : Option (Ordinary curve.polynomial)}
    {domains : FaceDomainBank lifted.frames base.faces.regulars} {differential : Differential genus}
    {target : Rational} (positive : 0 < target) {minimum : Nat}
    (requests : PhysicalLoopRequests.Preparation lifted domains differential (retained.loops.loopTarget target)
      (retained.loops.loopTarget_positive positive) minimum polynomial)
    {stage : Nat} {shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (readings : TriangleReadings shared lifted.mesh) (compared : requests.Comparison shared)
    (later : requests.index ≤ stage) :
    normSq (gaussianSum (retained.loops.rows.map (fun entry => (entry.1 : Canonical) *
      SewingRetraction.wordValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) entry.2))) <
        target := by
  apply retained.loops.loop_requested_lt _ positive
  intro original member
  have same : boundary.cycles = lifted.boundaryLoops := congrArg
    (fun value : BoundaryCycleDecomposition (triangleEdgeOccurrences lifted.mesh.triangulation.faces) => value.cycles)
    factory
  have inLoops : original ∈ lifted.boundaryLoops :=
    Eq.mp (congrArg (fun words => original ∈ words) same) member
  exact requests.comparison_accurate degree readings compared later original inLoops

/-- The SAME polynomial comparison caches pay the original full physical vector without discarding any loop row. -/
theorem physicalValue_comparison_accurate (degree : curve.polynomial.natDegree = 2 * genus + 1)
    {polynomial : Option (Ordinary curve.polynomial)}
    {domains : FaceDomainBank lifted.frames base.faces.regulars} {differential : Differential genus}
    {target : Rational} (positive : 0 < target) {minimum : Nat}
    (requests : PhysicalLoopRequests.Preparation lifted domains differential (retained.loops.loopTarget target)
      (retained.loops.loopTarget_positive positive) minimum polynomial)
    {stage : Nat} {shared : FacePrimitiveBank differential stage domains
      (numerator := PreparedPrimitiveSamples.numerator curve.polynomial differential polynomial)}
    (readings : TriangleReadings shared lifted.mesh) (compared : requests.Comparison shared)
    (later : requests.index ≤ stage) :
    normSq (retained.coordinates.physicalValue
      (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)) < target := by
  have original := retained.physicalLoops_comparison_accurate degree positive requests readings compared later
  have same := PhysicalCycleCoordinates.Data.value_eq retained.loops
    (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values)
  change retained.coordinates.physicalValue (CanonicalEdgeValues.edgeValuation lifted.mesh readings.values) = _ at same
  exact Eq.mpr (congrArg (fun value : Canonical => normSq value < target) same) original

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates.Reduction
