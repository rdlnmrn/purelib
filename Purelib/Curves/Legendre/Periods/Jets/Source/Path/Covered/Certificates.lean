module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Chain
import Purelib.Curves.Legendre.Periods.Jets.Source.Observations
public import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Uniform certificates for the six retained prepared-parent source lists

Each original source preparation already contains a paid six-channel Query.
The same original centered chain orders the source cells and their uniform
certificates. The constructor reads those stored queries, without selecting
another model, preparing another chart or requesting endpoint observations.
Each per-channel query answers through its own original bundled observation;
evaluation sharing across independent future queries is not asserted.

These certificates identify the actual differential integrands of the six
literal spatial cell lists. Progressive integral convergence and parameter
differentiation require additional finite estimates.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets (UniformPathCertificates)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)

variable {parameter : Canonical} (frame : Paths.Frame parameter) {basis : Differential 1} {count floor : Nat}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}

set_option genInjectivity false in
/-- Uniform integrand certificates for the six literal source lists on the identical original centered path.

The original prepared cells, model and request caches remain indices. Each
certificate answers all bounded rational queries with the same differential,
physical cell and selected sheet as its own retained source list. The six
channels share one geometric path; no parameter derivative is inferred.
-/
structure Certificates {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (covered : CoveredParents count parents) (prepared : PreparedParents covered floor targets)
    {start finish : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := start) (finish := finish)) : Type 2 where
  /-- The first value differential is certified on the exact retained first value-cell list. -/
  valueZero : UniformPathCertificates (Fibre.frameCurve frame) (Specification.valueSpecification parameter 0)
    (sources covered prepared chain).valueZero chain.path
  /-- The second value differential uses the original coordinate-weighted value-cell list. -/
  valueOne : UniformPathCertificates (Fibre.frameCurve frame) (Specification.valueSpecification parameter 1)
    (sources covered prepared chain).valueOne chain.path
  /-- The first parameter-differential integrand uses the same original physical source path. -/
  firstZero : UniformPathCertificates (Fibre.frameCurve frame) (Specification.firstDerivativeSpecification parameter 0)
    (sources covered prepared chain).firstZero chain.path
  /-- The weighted first parameter-differential integrand uses its own literal retained cell list. -/
  firstOne : UniformPathCertificates (Fibre.frameCurve frame) (Specification.firstDerivativeSpecification parameter 1)
    (sources covered prepared chain).firstOne chain.path
  /-- The first second-parameter-differential integrand is certified on its original source cells. -/
  secondZero : UniformPathCertificates (Fibre.frameCurve frame)
    (Specification.secondDerivativeSpecification parameter 0)
    (sources covered prepared chain).secondZero chain.path
  /-- The weighted second parameter-differential integrand retains the same lifted path and source owners. -/
  secondOne : UniformPathCertificates (Fibre.frameCurve frame)
    (Specification.secondDerivativeSpecification parameter 1)
    (sources covered prepared chain).secondOne chain.path

constructive_injectivity Certificates

namespace Certificates

variable {frame}

/-- Read the existing uniform certificate on the exact selected original source-cell list.

The finite index selects the original Specification.Table entry and its
literal source list. No observation callback or source owner is replaced.
-/
def channel {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count parents} {prepared : PreparedParents covered floor targets}
    {start finish : LiftedPoint 2} {chain : CenteredPathChain parents (start := start) (finish := finish)}
    (certificates : Certificates frame covered prepared chain) :
    (index : Fin 6) → UniformPathCertificates (Fibre.frameCurve frame) (Specification.Table.forms parameter index)
      ((sources covered prepared chain).cells index) chain.path :=
  Fin.cases certificates.valueZero (Fin.cases certificates.valueOne
    (Fin.cases certificates.firstZero (Fin.cases certificates.firstOne
      (Fin.cases certificates.secondZero (Fin.cases certificates.secondOne (fun index => Fin.elim0 index))))))

/-- Prepend the original prepared head to certificates on its unchanged covered tail.

The covering patch and centered chain retain the head's exact physical
endpoints. Each channel reads its own original bundled observation and
reuses the corresponding retained tail certificate.
-/
private def cons {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    (patch : PreparedPatch parent) (inside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (covered : CoveredParents count parents) (head : PreparedParent patch count floor inside targets)
    (remaining : PreparedParents covered floor targets) {finish : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := PreparedParent.finishPoint parent) (finish := finish))
    (tail : Certificates frame covered remaining chain) :
    Certificates frame (CoveredParents.cons patch inside covered) ⟨head, remaining⟩
      (CenteredPathChain.cons parent chain) :=
  let cell := head.preparation.cell
  let query := head.preparation.query
  { valueZero := .cons cell.models.valueZero.start_eq cell.models.valueZero.finish_eq
      (.uniform ⟨fun input lower upper => (query.observe frame input lower upper).valueZero⟩) tail.valueZero
    valueOne := .cons cell.models.valueOne.start_eq cell.models.valueOne.finish_eq
      (.uniform ⟨fun input lower upper => (query.observe frame input lower upper).valueOne⟩) tail.valueOne
    firstZero := .cons cell.models.firstZero.start_eq cell.models.firstZero.finish_eq
      (.uniform ⟨fun input lower upper => (query.observe frame input lower upper).firstZero⟩) tail.firstZero
    firstOne := .cons cell.models.firstOne.start_eq cell.models.firstOne.finish_eq
      (.uniform ⟨fun input lower upper => (query.observe frame input lower upper).firstOne⟩) tail.firstOne
    secondZero := .cons cell.models.secondZero.start_eq cell.models.secondZero.finish_eq
      (.uniform ⟨fun input lower upper => (query.observe frame input lower upper).secondZero⟩) tail.secondZero
    secondOne := .cons cell.models.secondOne.start_eq cell.models.secondOne.finish_eq
      (.uniform ⟨fun input lower upper => (query.observe frame input lower upper).secondOne⟩) tail.secondOne }

end Certificates

/-- Certify all six original source lists from their already paid queries in one traversal of the retained parent spine.

The constructor consumes each existing Preparation.query and the identical
stored tail. Its six uniform callbacks retain the original point-query
operation and read the corresponding channel of its actual observation
bundle. It constructs no source model or endpoint reading, and accepts no
integrand error or final period comparison as an extra input.
-/
def certify : {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} →
    (covered : CoveredParents count parents) → (prepared : PreparedParents covered floor targets) →
    {start finish : LiftedPoint 2} →
    (chain : CenteredPathChain parents (start := start) (finish := finish)) →
    Certificates frame covered prepared chain
  | [], .nil, _, _, _, .nil point =>
      ⟨.nil point, .nil point, .nil point, .nil point, .nil point, .nil point⟩
  | _ :: _, .cons patch inside covered, prepared, _, _, .cons _ chain =>
      Certificates.cons patch inside covered prepared.1 prepared.2 chain
        (certify covered prepared.2 chain)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
