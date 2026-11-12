module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
public import Purelib.Curves.Legendre.Periods.Jets.Source.Observations.Channels
public import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
public import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table

/-! # Actual source-query roots on their original affine prepared parent

One original six-channel bundle and one direct Query are executed and kept.
The shared sample-to-query comparison is constructed once. All six actual
observation roots are attached to that same direct Owner using their
original whole-factory readbacks, without another Point or source model.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformCellCertificate)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
variable {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
variable {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
variable {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {targets : CellEndpoints.Targets original stage}
variable (prepared : PreparedParent patch count floor covered targets)

/-- The actual six-channel bundle at one original parent fraction, with its unchanged request owners. -/
@[expose] def QueryObservations (fraction : Rational) :=
  CellModels.Observations frame (liftedCell parent) prepared.preparation.cell.models
    prepared.preparation.query.requests fraction

/-- One actual source-query bundle, one original direct Query and six retained signed root attachments.

The source bundle has its complete original observer equation. The direct
Query already retains its original whole Owner factory. Each dependent
vector entry relates these actual independent roots, rather than inferring
an Owner identity from a coordinate or a sheet label.
-/
@[expose] def RootedQuery (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :=
  Σ observed : {value : QueryObservations (frame := frame) prepared fraction //
    value = prepared.preparation.query.observe frame fraction inside.1 inside.2},
  Σ direct : PreparedEdge.Query parent.edge fraction inside,
    DependentVector (fun channel : Fin 6 =>
      NamedEquivalent (ownerName direct.owner) (observed.val.channel channel).algebraic.sheetValue.value.name)

namespace RootedQuery

/-- Execute the original source bundle and direct Query once, then derive every actual channel's root attachment.

The same retained source sample and direct Query pay one common geometric
comparison. Original channel readbacks transport it to all six actual
observation generators. No signed relation, new clearance, replacement
source or promoted old observation is supplied.
-/
def build (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    RootedQuery (frame := frame) prepared fraction inside :=
  let observed := prepared.preparation.query.observe frame fraction inside.1 inside.2
  let direct := PreparedEdge.Query.build parent.edge fraction inside
  let common := prepared.querySampleEquivalent fraction inside observed.retained.sample direct
  let roots := DependentVector.ofFn (fun channel : Fin 6 =>
    let actual := prepared.preparation.query.channel_root_name frame fraction inside.1 inside.2 observed rfl channel
    NamedEquivalent.transport direct.name_eq actual.symm common)
  ⟨⟨observed, rfl⟩, direct, roots⟩

variable {prepared} {fraction : Rational} {inside : 0 ≤ fraction ∧ fraction ≤ 1}
variable (queried : RootedQuery (frame := frame) prepared fraction inside)

/-- Read the retained complete original six-channel observation bundle without another query execution. -/
abbrev observed := queried.1.val

/-- Read the same actual original direct Query, including its complete Owner factory. -/
abbrev direct := queried.2.1

/-- Read the six stored operational root attachments without reconstructing the shared comparison. -/
abbrev roots := queried.2.2

/-- The retained six-channel bundle is the original source observer at this exact parent fraction. -/
theorem observed_eq : queried.observed = prepared.preparation.query.observe frame fraction inside.1 inside.2 :=
  queried.1.property

/-- Every actual retained channel lies at the original parent's exact affine physical point. -/
theorem point_eq (channel : Fin 6) :
    (queried.observed.channel channel).algebraic.point = parent.edge.point fraction :=
  (queried.observed.channel_point channel).trans (prepared.queryPoint_eq fraction)

/-- Read the SAME retained source Point at its original physical parent fraction.

Only the exact coordinate index changes. The Point's Owner, parameter
norm, seed refinement and root certificate remain the original query
bundle's supplied data; no Point or direct Query is acquired.
-/
def sample : ContinuedNeighborhood.Point prepared.preparation.cell.patch (parent.edge.point fraction) :=
  ContinuedNeighborhood.Point.castPoint (prepared.queryPoint_eq fraction).symm queried.observed.retained.sample

/-- Physical-point transport retains this SAME query's original certified root name. -/
theorem sample_name : queried.sample.certificate.value.name =
    queried.observed.retained.sample.certificate.value.name := by
  unfold sample
  exact ContinuedNeighborhood.Point.castPoint_name _ _

include inside in
/-- The retained source chart contains the exact physical coordinate of this SAME query. -/
theorem sample_inside : prepared.preparation.cell.patch.box.Contains (parent.edge.point fraction) :=
  Eq.mp (congrArg prepared.preparation.cell.patch.box.Contains (prepared.queryPoint_eq fraction))
    (prepared.preparation.cell.models.coordinate.point_inside
      prepared.preparation.cell.startInside prepared.preparation.cell.finishInside inside.1 inside.2)

/-- The stored channel attachment compares the actual direct Query Owner to the SAME retained source Point.

The value-zero channel supplies one existing attachment. Its original
whole-factory root readback removes only that channel's wrapper, then the
physical Point transport preserves the name. No comparison producer runs.
-/
def sampleRoots : NamedEquivalent (ownerName queried.direct.owner) queried.sample.certificate.value.name :=
  NamedEquivalent.transport rfl
    ((prepared.preparation.query.channel_root_name frame fraction inside.1 inside.2
      queried.observed queried.observed_eq 0).trans queried.sample_name.symm) (queried.roots.get 0)

end RootedQuery

/-- Productive source queries keep their actual six observations and geometric root attachments together. -/
@[expose] def RootedQueries :=
  (fraction : Rational) → (inside : 0 ≤ fraction ∧ fraction ≤ 1) →
    RootedQuery (frame := frame) prepared fraction inside

namespace RootedQueries

variable {prepared}

/-- Read uniform certificates from the retained rooted-query callbacks on the same six original spatial cells.

A channel query consumes one returned bundle and its actual observation.
Independent future channel queries remain separate executions; no sharing
across independent callback calls is asserted.
-/
def certificates (queries : RootedQueries (frame := frame) prepared) :
    DependentVector (fun channel : Fin 6 =>
      UniformCellCertificate (Fibre.frameCurve frame) (Specification.Table.forms parameter channel)
        (liftedCell parent) (prepared.preparation.cell.models.cell channel)) :=
  DependentVector.ofFn (fun channel =>
    ⟨fun fraction lower upper => (queries fraction ⟨lower, upper⟩).observed.channel channel⟩)

/-- Reading an actual certificate callback recovers the original rooted callback's same actual channel observation. -/
private theorem packaged_certificates_query (queries : RootedQueries (frame := frame) prepared)
    (channel : Fin 6) (fraction : Rational) (lower : 0 ≤ fraction) (upper : fraction ≤ 1) :
    ((certificates queries).get channel).query fraction lower upper =
      (queries fraction ⟨lower, upper⟩).observed.channel channel := by
  unfold certificates
  rewrite [DependentVector.ofFn_get]
  rfl

/-- The actual certificate query reads the same original channel from its retained rooted-query callback. -/
theorem certificates_query (queries : RootedQueries (frame := frame) prepared)
    (channel : Fin 6) (fraction : Rational) (lower : 0 ≤ fraction) (upper : fraction ≤ 1) :
    ((certificates queries).get channel).query fraction lower upper =
      (queries fraction ⟨lower, upper⟩).observed.channel channel :=
  packaged_certificates_query queries channel fraction lower upper

end RootedQueries

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
