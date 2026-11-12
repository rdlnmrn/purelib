module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents
public import Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenterStates
import Purelib.Data.List.Membership

/-! # Actual retained paid centers at the identical acquired-subdivision index

The original Parents cache owns its selected centers above the stored trace.
The original whole traced_prepared_eq transports those SAME states to the
actual acquired preparation used by the factor Fold. Both whole caches stay
inputs; equality transport neither executes a factory nor selects a state.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

namespace Acquisition.Segment.Parents

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
  (CenterStates centeredEdges CenteredEdge)
open Purelib.Riemann.Paths.PreparedClearPathModels (CompleteSegment)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
variable {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {owner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest}
variable {sheet : Fin 2} {count : Nat}
variable {paid : Segment (segment := segment) (within := within) (owner := owner) request}
variable (parents : Parents differential sheet count paid)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

/-- The retained trace and acquired preparation have the identical complete original subdivision. -/
theorem acquiredSubdivision_eq :
    paid.traced.prepared.subdivision = paid.prepared.acquired.prepared.subdivision :=
  congrArg (fun complete : CompleteSegment segment within owner => complete.subdivision) paid.traced_prepared_eq

/-- Read the SAME actual center observations at their exact original acquired-subdivision index. -/
@[expose] def acquiredCenters : CenterStates curve differential sheet paid.prepared.acquired.prepared.subdivision :=
  CenterStates.castSubdivision (acquiredSubdivision_eq (paid := paid)) parents.centers

/-- The acquired-index view retains every original selected center observation, state and cache unchanged. -/
theorem acquiredCenters_heq : HEq parents.acquiredCenters parents.centers :=
  CenterStates.castSubdivision_heq (acquiredSubdivision_eq (paid := paid)) parents.centers

/-- The actual parents are the SAME acquired preparation's centered edges on its transported retained states. -/
theorem acquiredParents_eq : parents.covered.parents =
    centeredEdges curve differential sheet paid.prepared.acquired.prepared.subdivision parents.acquiredCenters :=
  parents.parents_eq.trans
    (CenterStates.castSubdivision_edges (acquiredSubdivision_eq (paid := paid)) parents.centers).symm

/-- Change only an actual parent occurrence's bound to the SAME original acquired centered-edge list. -/
@[expose] def acquiredIndex (index : Fin parents.covered.parents.length) :
    Fin (centeredEdges curve differential sheet paid.prepared.acquired.prepared.subdivision
      parents.acquiredCenters).length :=
  ⟨index.val, Eq.mp (congrArg (fun entries => index.val < entries.length) parents.acquiredParents_eq) index.isLt⟩

/-- The acquired-index transport preserves the literal original child occurrence exactly. -/
theorem acquiredIndex_val (index : Fin parents.covered.parents.length) :
    (parents.acquiredIndex index).val = index.val := rfl

/-- The original retained child and its acquired-index view are the SAME entire centered edge. -/
theorem acquiredParent_eq (index : Fin parents.covered.parents.length) :
    parents.covered.parents[index.val]'index.isLt =
      (centeredEdges curve differential sheet paid.prepared.acquired.prepared.subdivision parents.acquiredCenters)[
        (parents.acquiredIndex index).val]'(parents.acquiredIndex index).isLt :=
  getElem_congr parents.acquiredParents_eq rfl index.isLt

end Acquisition.Segment.Parents

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

end
