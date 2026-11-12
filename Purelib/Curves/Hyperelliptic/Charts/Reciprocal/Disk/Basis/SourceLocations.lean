module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RecastJoins
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitiveReadback
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Division
import Purelib.Approximation.Gaussian.Request.Basic
import Purelib.Approximation.Gaussian.Request.Division
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Request.Common
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Curves.Hyperelliptic.Sheets.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Rounding.Floor
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance

open Purelib.Data.Vector (DependentVector)

open Purelib.Curves

open Purelib

open Purelib.Geometry

open Purelib.Riemann

@[expose] public section

/-! Locate each basis source in its retained reciprocal cover and reuse its
sampled cell. Differential recasting supplies the actual root-owner joins. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Riemann.Normalization

open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)

variable {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {model : UniformReciprocalRootChannels.RootModel cell} {parameter :
    InverseRootPolynomial.Coordinate} {anchor : ArcOwners.Point cap
    model parameter}
  {regular : RegularBounds.Data cap}

set_option genInjectivity false in
/-- The existing source cover of one recast basis parent. -/
structure BasisSourceCover (parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential) (row :
  Fin genus) where
  /-- The retained primitive patch of the original parent recast to this standard differential. -/ patch :
    Branches.UniformPrimitiveSheetCompatibility.PreparedPatch (recastCenteredEdge
    (Periods.PeriodMatrix.standardDifferential row) parent)
  /-- The original source model count. -/ count : Nat
  /-- The retained reciprocal source model data. -/ data : UniformReciprocalModels.Data
    patch count
  /-- The actual reciprocal cover on that same original model data. -/ cover :
    UniformReciprocalCover.Cover data

constructive_injectivity BasisSourceCover

/-- The retained reciprocal source cover for each recast basis row of one original physical parent. -/
def BasisSourceCovers (parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential) :=
  DependentVector (BasisSourceCover parent)

/-- The basis rows retain covers of the same physical parent spine. -/
def BasisParentSourceCovers (parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential))
  :=
  DependentVector (fun row : Fin genus =>
    UniformReciprocalCover.ParentCovers
    (parents.map (recastCenteredEdge (Periods.PeriodMatrix.standardDifferential
      row))))

namespace BasisParentSourceCovers

variable {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}

/-- Extract the actual first parent covers, retaining every prepared patch,
uniform model and mesh from the original per-basis banks. -/
def head (covers : BasisParentSourceCovers (parent ::
  parents)) : BasisSourceCovers parent :=
  DependentVector.ofFn fun row =>
    match covers.get row with
    | .cons patch data cover _ => ⟨patch, genus, data, cover⟩

/-- Reuse each basis row's original remaining parent covers after dropping the same head parent. -/
def tail (covers : BasisParentSourceCovers (parent ::
  parents)) : BasisParentSourceCovers parents :=
  DependentVector.ofFn fun row =>
    match covers.get row with
    | .cons _ _ _ rest => rest

end BasisParentSourceCovers

set_option genInjectivity false in
/-- One basis source located in its original cover with the actual root model, anchor joining and cached comparison
bounds. -/
structure BasisSourceLocation (regular : RegularBounds.Data cap)
    (anchor : ArcOwners.Point cap model parameter) {row : Fin genus} (source :
      BasisSourceCover parent row) where
  /-- The actual retained cell containing the requested source parameter. -/ located :
    UniformReciprocalCover.Cells.Located source.data source.cover.mesh.edges parameter
  /-- The original root model prepared on that exact located cell. -/ model :
    UniformReciprocalRootChannels.RootModel located.cell
  /-- The retained source point on that model at the requested parameter. -/ point :
    ArcOwners.Point cap model parameter
  /-- The actual root-owner join from the original anchor to this source point. -/ joined :
    ArcOwners.Join anchor point
  /-- The cached source arc comparison on the located cell. -/ comparison :
    ArcSamples.Data regular located.cell
  /-- The cached endpoint comparison bounds on the same point. -/ bounds :
    EndpointComparison.Data regular point

constructive_injectivity BasisSourceLocation

namespace BasisSourceLocation

variable {row : Fin genus} {source :
  BasisSourceCover parent row}

/-- Locate the parameter in the original cover and retain its actual root model, recast-owner joining and comparison
caches. -/
def build (regular : RegularBounds.Data cap) (anchor :
  ArcOwners.Point cap model parameter)
    (source : BasisSourceCover parent row) :
      BasisSourceLocation regular anchor source :=
  let inside := ⟨edge.left.inside.1.trans anchor.root.between.1, anchor.root.between.2.trans edge.right.inside.2⟩
  let located := source.cover.locate parameter inside
  let model := UniformReciprocalRootChannels.RootModel.build located.cell
  let point := ArcOwners.Point.build cap model parameter located.between
  ⟨located, model, point, RecastJoins.ReciprocalDiskArcOwners.Join.ofRecast anchor
    point, ArcSamples.Data.build regular located.cell,
    EndpointComparison.Data.build regular point⟩

/-- Package cached ownership and bounds; no root or model is prepared again. -/
def owner (location : BasisSourceLocation regular anchor
  source) : SourceRequests.BasisSourceOwner regular anchor row :=
  ⟨recastCenteredEdge (Periods.PeriodMatrix.standardDifferential row) parent, source.patch, source.count, source.data,
    location.located.edge, location.located.cell, location.model, parameter, location.point, location.joined,
    location.comparison, location.bounds⟩

/-- Read the original sampled cell and reuse its inverse when forming the
cap pullback. The locator's membership certificate guarantees success. -/
def sample (location : BasisSourceLocation regular anchor
  source) {index : Nat} {box : Rational.Box}
    (cells : UniformReciprocalPrimitives.PrimitiveCells source.data index
      source.cover.mesh.edges)
    (polynomial : Cap.Primitives.Sample cap (Periods.PeriodMatrix.standardDifferential
      row) index box) :
    ArcSamples.Sample location.owner.comparison polynomial :=
  let retained := cells.readCell location.located.cell location.located.member
  ArcSamples.Sample.ofPrimitive location.comparison polynomial retained.primitive
    retained.cell_eq

end BasisSourceLocation

/-- The dependent vector of actual source locations in the original per-basis covers. -/
def BasisSourceLocations (regular : RegularBounds.Data cap) (anchor :
  ArcOwners.Point cap model parameter)
    (covers : BasisSourceCovers parent) :=
  DependentVector (fun row => BasisSourceLocation
    regular anchor (covers.get row))

namespace BasisSourceLocations

variable {covers : BasisSourceCovers parent}

/-- Locate each original basis source at the same anchor parameter while retaining its own source cover and model. -/
def build (regular : RegularBounds.Data cap) (anchor :
  ArcOwners.Point cap model parameter)
    (covers : BasisSourceCovers parent) :
      BasisSourceLocations regular anchor covers :=
  DependentVector.ofFn fun row =>
    BasisSourceLocation.build regular anchor (covers.get row)

/-- Package the already retained locations as the original per-row source owners. -/
def owners (locations : BasisSourceLocations regular anchor
  covers) : SourceRequests.BasisSourceOwners regular anchor :=
  DependentVector.ofFn fun row => (locations.get row).owner

/-- Reading one packaged source owner returns exactly that retained location's owner. -/
theorem owners_get (locations : BasisSourceLocations regular
  anchor covers) (row : Fin genus) :
    locations.owners.get row = (locations.get row).owner := DependentVector.ofFn_get _ row

/-- The numerical bank is shared across all located vertices of this parent. -/
def SampleBank (covers : BasisSourceCovers parent) (index :
  Nat) :=
  DependentVector (fun row => UniformReciprocalPrimitives.PrimitiveCells
    (covers.get row).data index (covers.get row).cover.mesh.edges)

/-- Read each original located cell from the shared sampled bank and retain its cap pullback sample without rebuilding
the cell. -/
def samples (locations : BasisSourceLocations regular anchor
  covers) {index : Nat} {box : Rational.Box}
    (bank : SampleBank covers index)
      (polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box) :
    SourceRequests.BasisSourceRequest.Samples locations.owners polynomials :=
      by
  refine DependentVector.ofFn ?_
  intro row
  rw [locations.owners_get]
  exact (locations.get row).sample (bank.get row) (polynomials.get row)

end BasisSourceLocations
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
