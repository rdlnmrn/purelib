module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Basic

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugatePhysicalAggregate
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateRemaining
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnEnergyRequest

public section

/-! One annular request tail for every conjugate basis pair. The Newton
budget precedes the grid; all later samples use the same retained excision. -/
namespace Purelib.Riemann.RootContinuation.NewtonHomogeneousAnnularRequest

open Purelib

open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Topology.Surface.Sewing.SewnEnergyCombination (EnergySurfaces EnergyPairs)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest (EnergyPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples (ConjugateSample)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {target radius : Data.Rat.Fraction.Rational}
  {family : Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest
    preparation target radius}
  {lifted : LiftedPuncturedGrid family.single.grid.punctured}
  {excision : Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision family.single.grid lifted}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    family.single.grid.faces.regulars}
  (prepared :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
    excision)
  (sewing : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation lifted.cutPolygon domains)

namespace HomogeneousAnnularRequest

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples (ConjugateSample)

open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
/-- Every later conjugate sample has corrected annular quadrance below 82/4 times the retained target.

The quantification uses the same comparison, domain bank, numerical stage and sewn conjugate pair for all later samples.
-/
@[expose] def Accurate {first second : Fin genus} (comparison :
  Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison prepared
  first second domains) (index : Nat) : Prop :=
  ∀ stage (cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get first) lifted.mesh)
      (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get second)
      lifted.mesh)
    (leftSurface : Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values)
    (rightSurface : Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values)
    (pair : Surface.Sewing.SewnConjugateSamples.ConjugatePair leftSurface rightSurface)
    (sample : Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateSample left right leftSurface rightSurface
      pair comparison), index ≤ stage →
      Data.Gaussian.Norm.Basic.normSq (sample.area + sample.holes) < (82 / 4 : Rat.Fraction.Rational) * target

open Purelib.Curves in
set_option genInjectivity false in
/-- One retained conjugate basis comparison with a certified request tail.

Its index respects the supplied floor and establishes the annular accuracy claim for every later sample. -/
structure PairRequest (first second : Fin genus) (floor : Nat) where
  /-- The retained comparison for this ordered pair of basis indices. -/ comparison :
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison prepared
    first second domains
  /-- The acquired stage from which the comparison is accurate. -/ index : Nat
  /-- The acquired stage is at least the requested floor. -/ floor_le : floor ≤ index
  /-- All samples at or after the retained stage satisfy the corrected annular bound. -/ accurate : Accurate prepared
    comparison index

constructive_injectivity PairRequest

open Purelib.Curves in
/-- Acquire the annular request for one ordered basis pair from its retained sewing preparation. -/
@[expose] def PairRequest.build (first second : Fin genus) (floor : Nat) : PairRequest (domains := domains) prepared
  first second floor :=
  let comparison :=
    Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.build
    prepared first second domains
  let acquired := Hyperelliptic.Meshes.Newton.AllHoles.ConjugatePhysicalAggregate.conjugatePhysicalRequest comparison
    (sewing.pair first second) floor
  ⟨comparison, acquired.val, acquired.property.1, acquired.property.2⟩

open Purelib.Data in
/-- A dependent bank retaining a request for every ordered pair of basis indices. -/
@[expose] def Entries (floor : Nat) := Vector.DependentVector (fun first : Fin genus =>
  Vector.DependentVector (fun second : Fin genus => PairRequest (domains := domains) prepared first second floor))

/-- Every retained pair request starts no later than the supplied common index. -/
@[expose] def Entries.IndexBound {floor : Nat} (entries : Entries (domains := domains) prepared floor) (index : Nat) :
  Prop :=
  ∀ first second, ((entries.get first).get second).index ≤ index

set_option genInjectivity false in
/-- A complete bank of conjugate pair requests with one dominating stage.

The common index respects the original floor and every exact request in the retained dependent bank. -/
structure Request (floor : Nat) where
  /-- The retained dependent bank of all ordered basis-pair requests. -/ entries : Entries (domains := domains) prepared
    floor
  /-- The common natural stage dominating the retained request bank. -/ index : Nat
  /-- The common stage respects the original request floor. -/ floor_le : floor ≤ index
  /-- Every request in the retained bank starts no later than the common stage. -/ index_ge : entries.IndexBound
    prepared index

constructive_injectivity Request

open Purelib.Data in
/-- Acquire every basis-pair request once and retain their common maximum stage.

The maximum is also compared with the original floor, including an empty basis bank. -/
@[expose] def Request.build (floor : Nat) : Request (domains := domains) prepared floor := by
  let entries : Entries (domains := domains) prepared floor := Vector.DependentVector.ofFn fun first =>
    Vector.DependentVector.ofFn fun second =>
    PairRequest.build prepared sewing first second floor
  let maximum := entries.maximum fun _ row => row.maximum fun _ request => request.index
  refine ⟨entries, max floor maximum, Data.Nat.Order.le_max_left _ _, ?_⟩
  intro first second
  exact ((entries.get first).get_le_maximum (fun _ request => request.index) second).trans
    ((entries.get_le_maximum (fun _ row => row.maximum fun _ request => request.index) first).trans
      (Data.Nat.Order.le_max_right _ _))

variable {prepared sewing} {floor stage : Nat} {cache :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  (triangles : Data.Vector.DependentVector (fun basis : Fin genus =>
    Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get basis) lifted.mesh))
  (surfaces : Topology.Surface.Sewing.SewnEnergyCombination.EnergySurfaces lifted.cutPolygon.patch (fun basis =>
    (triangles.get basis).values))
  (pairs : Topology.Surface.Sewing.SewnEnergyCombination.EnergyPairs surfaces) (request : Request (domains := domains)
    prepared floor)

open Purelib.Curves
open Purelib.Data
/-- A dependent bank of conjugate samples indexed by the exact retained request comparisons. -/
@[expose] def Samples := Vector.DependentVector (fun first : Fin genus => Vector.DependentVector (fun second : Fin genus
  =>
  Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateSample (triangles.get first) (triangles.get second)
    (surfaces.get first) (surfaces.get second)
    ((pairs.get first).get second) ((request.entries.get first).get second).comparison))

/-- Build every conjugate sample from the retained triangles, sewn surfaces, pair certificates and comparison bank. -/
@[expose] def Samples.build : Samples triangles surfaces pairs request :=
  Vector.DependentVector.ofFn fun first => Vector.DependentVector.ofFn fun second =>
    Hyperelliptic.Meshes.Newton.AllHoles.ConjugateSamples.ConjugateSample.build (triangles.get first) (triangles.get
      second) (surfaces.get first) (surfaces.get second)
      ((pairs.get first).get second) ((request.entries.get first).get second).comparison

end HomogeneousAnnularRequest
end Purelib.Riemann.RootContinuation.NewtonHomogeneousAnnularRequest
