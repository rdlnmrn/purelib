module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.Grid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells.Comparison.Requested
import Purelib.Approximation.AccuracyRequest
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

/-! # Original-request primitive payments on one actual paid segment

The complete paid Parents, retained split/location/classification cache and
same-parent original request bank remain inputs. Geometry and numerical
folds are each materialized once on those exact ordered caches. A hole
outcome is retained as unresolved rather than paid by a zero discrepancy.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

namespace Acquisition.Segment.Parents.GridFragments

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFragmentCells (LocatedPrimitiveSplits)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPrimitiveSplits (PrimitiveAxes)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus count index : Nat} {curve : HyperellipticCurve genus} {basis : Differential genus}
variable {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest} {sheet : Fin 2}
variable {retained : Segment (segment := segment) (within := within) (owner := sourceOwner) request}
variable {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
variable {base : FramedPuncturedGrid curve branches higher} {axes : PrimitiveAxes base.bank.grid}
variable {parents : Parents basis sheet count retained}
variable {first : (Cuts.Ambient curve).Contains start} {last : (Cuts.Ambient curve).Contains finish}
variable {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {target : Rational}

/-- One whole regular/hole comparison factory on the identical original paid parents and cached grid split. -/
@[expose] def Comparisons (cached : GridFragments base axes parents first last)
    (domains : FaceDomainBank frames base.faces.regulars)
    (requests : RequestedParents count target parents.covered.parents) :=
  {value : LocatedPrimitiveSplits.Comparisons domains cached.locations requests cached.classifications //
    value = LocatedPrimitiveSplits.compare domains cached.locations requests cached.classifications}

/-- Consume the supplied whole requests and grid cache once, without another split, cell lookup or original request. -/
def compare (cached : GridFragments base axes parents first last)
    (domains : FaceDomainBank frames base.faces.regulars)
    (requests : RequestedParents count target parents.covered.parents) : Comparisons cached domains requests :=
  let compared := LocatedPrimitiveSplits.compare domains cached.locations requests cached.classifications
  ⟨compared, rfl⟩

/-- One whole finite numerical fold on the same retained regular/hole comparisons and original shared face caches. -/
@[expose] def Evaluation {cached : GridFragments base axes parents first last}
    {domains : FaceDomainBank frames base.faces.regulars}
    {requests : RequestedParents count target parents.covered.parents} (compared : Comparisons cached domains requests)
    {points : List Canonical} {tolerance : Rational}
    (budgets : CommonMeshes.FaceMeshBudgets basis points tolerance domains)
    (numerics : PrimitiveData.FacePrimitiveBank basis index domains) :=
  {value : LocatedPrimitiveSplits.Evaluation budgets numerics cached.locations requests cached.classifications
      compared.val //
    value = LocatedPrimitiveSplits.evaluate budgets numerics cached.locations requests cached.classifications
      compared.val}

/-- Materialize every actual regular-leaf payment once, preserving all original unresolved hole outcomes and order. -/
def evaluate {cached : GridFragments base axes parents first last}
    {domains : FaceDomainBank frames base.faces.regulars}
    {requests : RequestedParents count target parents.covered.parents} (compared : Comparisons cached domains requests)
    {points : List Canonical} {tolerance : Rational}
    (budgets : CommonMeshes.FaceMeshBudgets basis points tolerance domains)
    (numerics : PrimitiveData.FacePrimitiveBank basis index domains) : Evaluation compared budgets numerics :=
  let evaluated := LocatedPrimitiveSplits.evaluate budgets numerics cached.locations requests cached.classifications
    compared.val
  ⟨evaluated, rfl⟩

end Acquisition.Segment.Parents.GridFragments

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

end
