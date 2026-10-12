module
import Purelib.Data.List.Membership
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.ChartAreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.SourceChartComparison
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Integration.Path.PairedAreaComparison
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.MixedChartAreaRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh

@[expose] public section

namespace Purelib.Examples.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReadingRoutes

open Purelib.Data.Gaussian
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SourceChartAreaRequests (SourceChartAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings (MixedChartAreaRequest)

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib.Topology

open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

/-! A displayed three-edge face boundary is a shared small fixture. Its order
and orientation remain source data; no differential or chart is invented. -/
/-- The three ordered oriented edges 0→1, 1→2 and 2→0 of a supplied face. -/
def triangleSources {count : Nat} (face : Fin count) :
    List (Surface.Sewing.SewnPrimitiveContacts.SourceEdge count) :=
  [⟨face, 0, 1⟩, ⟨face, 1, 2⟩, ⟨face, 2, 0⟩]

section Single

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid}
  {edges : SquareRoot.Grid.RootEdgeBank frames} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges
    base.faces}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames base.faces.regulars}
    {differential : Differential genus}

/-- A paid source-to-chart request retains the supplied source area, exact residual and target bound. -/
example {fixed : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
  differential}
    {face : Fin mesh.triangles.length}
    {target : Fraction.Rational}
    (request : SourceChartAreaRequest fixed
      (triangleSources face) target)
    (sample : SourceChartAreaRequest.Sample
      (mesh := mesh) (domains := domains) (differential := differential))
    (source :
      SourceChartAreaRequest.SourceData sample
      (triangleSources face))
    (later : request.index ≤ sample.stage) :
    let retained := SourceChartAreaRequest.realize request
      sample source later
    retained.residual = source.summary.area - retained.chartArea ∧
      Norm.Basic.normSq retained.residual ≤ target := by
  let retained := SourceChartAreaRequest.realize request
    sample source later
  refine ⟨retained.residual_cached, ?_⟩
  rw [Norm.Basic.normSq_eq_canonical]
  exact retained.pay

end Single

section Mixed

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.Families
  (Domains MagnitudeBank Sources)

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {owner : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh curve}
    {domains : Domains owner}
    {leftDifferential rightDifferential : Differential genus}
    {leftFixed : MagnitudeBank owner domains leftDifferential}
    {rightFixed : MagnitudeBank owner domains rightDifferential}
    {coefficient : Gaussian.Basic.Canonical} {face : Fin owner.mesh.triangles.length} {target : Fraction.Rational}

/-! The same supplied source summary is used by realize and readback. A mixed
sample retains two differentials, two banks and two readings, with the actual
coefficient. It is not obtained by changing a single-reading coefficient. -/
/-- A paid mixed-reading request retains both supplied reading parents, their actual coefficient and the cached
source-area residual. -/
example (request : MixedChartAreaRequest (owner := owner)
    leftDifferential rightDifferential domains leftFixed rightFixed coefficient (triangleSources face) target)
    (sample : MixedChartAreaRequest.Sample (owner := owner)
      domains leftDifferential rightDifferential coefficient)
    (source : MixedChartAreaRequest.Observations sample
      (triangleSources face)) (later : request.index ≤ sample.stage) :
    let retained := MixedChartAreaRequest.realize request sample source
      later
    retained.residual = source.summary.area - retained.chartArea ∧
      Norm.Basic.normSq retained.residual ≤ target := by
  let retained := MixedChartAreaRequest.realize request sample source later
  refine ⟨retained.residual_cached, ?_⟩
  rw [Norm.Basic.normSq_eq_canonical]
  exact retained.pay

end Mixed

section Paired

open Hyperelliptic.Meshes.PuncturedGrid
open Hyperelliptic.Meshes.PuncturedGrid.Paired
open Hyperelliptic.Meshes.PuncturedGrid.Readings
open Purelib.Integration.Path
open Purelib.Polynomial.Geometry.Grid

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {owner : OwnedPuncturedMesh curve} {domains : SourceChartComparison.DomainFamily owner}
    {leftDifferential rightDifferential : Differential genus}
    (leftFixed : Readings.Families.MagnitudeBank owner domains leftDifferential)
    (rightFixed : Readings.Families.MagnitudeBank owner domains rightDifferential)
    {stage : Nat} {leftBank : SourceChartComparison.ReadingBank owner leftDifferential stage domains}
    {rightBank : SourceChartComparison.ReadingBank owner rightDifferential stage domains}
    (leftReadings : SourceChartComparison.BankReadings owner leftDifferential stage domains leftBank)
    (rightReadings : SourceChartComparison.BankReadings owner rightDifferential stage domains rightBank)

/-- Build a paid request, retain both reading banks and consume one ordered source cache in either paired view.

The source observation, signed occurrence list and original differential parents survive the chart construction; payment
uses the retained numerical comparison rather than acquiring another source summary. -/
theorem paired_chart_construction (view : PairedAreaComparison.View) (face : Fin owner.mesh.triangles.length)
    (nonloop : ∀ source ∈ triangleSources face, source.first ≠ source.last)
    (target : Fraction.Rational) (positive : 0 < target)
    (later : (ChartAreaRequests.PairedChartAreaRequest.build (mesh := owner.mesh)
      leftFixed rightFixed (triangleSources face) nonloop target positive).index ≤ stage) :
    let sample := SourceChartComparison.PairedReadings.ofReadings (owner := owner) leftReadings rightReadings
    let request := ChartAreaRequests.PairedChartAreaRequest.build (mesh := owner.mesh)
      leftFixed rightFixed (triangleSources face) nonloop target positive
    let source := PairedAreaComparison.Observation.realize
      (ChartAreaRequests.PairedChartAreaRequest.SourceEntries (mesh := owner.mesh) view
        sample.leftReadings.values sample.rightReadings.values (triangleSources face))
    let result := request.realizeSupplied (mesh := owner.mesh) (leftBank := sample.leftBank)
      (rightBank := sample.rightBank) view sample.leftReadings sample.rightReadings later source
    result.sourceParent = source ∧ result.sourceEdges = triangleSources face ∧
      result.leftBankParent = leftBank ∧ result.rightBankParent = rightBank ∧
      Norm.Basic.normSq result.residual ≤ target := by
  let sample := SourceChartComparison.PairedReadings.ofReadings (owner := owner) leftReadings rightReadings
  let request := ChartAreaRequests.PairedChartAreaRequest.build (mesh := owner.mesh)
    leftFixed rightFixed (triangleSources face) nonloop target positive
  let source := PairedAreaComparison.Observation.realize
    (ChartAreaRequests.PairedChartAreaRequest.SourceEntries (mesh := owner.mesh) view
      sample.leftReadings.values sample.rightReadings.values (triangleSources face))
  let result := request.realizeSupplied (mesh := owner.mesh) (leftBank := sample.leftBank)
    (rightBank := sample.rightBank) view sample.leftReadings sample.rightReadings later source
  exact ⟨result.sourceParent_eq, result.sourceEdges_eq, result.leftBankParent_eq,
    result.rightBankParent_eq, result.pay⟩

/-- Realize both opposite-sheet views from the original paired source selection and consume their paid residuals.

The two views retain the same source-occurrence selection and distinct left/right banks. Conjugation applies only to the
first differential; it does not identify that reading with a mixed Gaussian value. -/
example {start finish : Gaussian.Basic.Canonical} {walk : Walks.Walk owner.base.bank.grid start finish}
    (paired : WalkOccurrences.PairedWalk owner.mesh walk) (target : Fraction.Rational) (positive : 0 < target)
    (leftSheet rightSheet : Fin 2) (different : leftSheet ≠ rightSheet)
    (later : (BilinearAreaRequests.BilinearAreaRequest.build leftFixed rightFixed paired target positive).index ≤ stage)
    (selection : BilinearAreaRequests.BilinearAreaRequest.SelectedSources paired leftSheet rightSheet) :
    let sample := SourceChartComparison.PairedReadings.ofReadings (owner := owner) leftReadings rightReadings
    let request := BilinearAreaRequests.BilinearAreaRequest.build leftFixed rightFixed paired target positive
    let direct := request.realizePairedWithSources (mesh := owner.mesh) (leftBank := sample.leftBank)
      (rightBank := sample.rightBank) sample.leftReadings sample.rightReadings later leftSheet rightSheet different
        selection
    let conjugate := request.realizeConjugateWithSources (mesh := owner.mesh) (leftBank := sample.leftBank)
      (rightBank := sample.rightBank) sample.leftReadings sample.rightReadings later leftSheet rightSheet different
        selection
    Norm.Basic.normSq direct.residual ≤ target ∧
      Norm.Basic.normSq conjugate.residual ≤ target := by
  let sample := SourceChartComparison.PairedReadings.ofReadings (owner := owner) leftReadings rightReadings
  let request := BilinearAreaRequests.BilinearAreaRequest.build leftFixed rightFixed paired target positive
  let direct := request.realizePairedWithSources (mesh := owner.mesh) (leftBank := sample.leftBank)
    (rightBank := sample.rightBank) sample.leftReadings sample.rightReadings later leftSheet rightSheet different
      selection
  let conjugate := request.realizeConjugateWithSources (mesh := owner.mesh) (leftBank := sample.leftBank)
    (rightBank := sample.rightBank) sample.leftReadings sample.rightReadings later leftSheet rightSheet different
      selection
  exact ⟨direct.pay, conjugate.pay⟩

end Paired

end Purelib.Examples.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReadingRoutes
