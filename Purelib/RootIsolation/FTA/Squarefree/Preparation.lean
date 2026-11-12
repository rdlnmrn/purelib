module

public import Purelib.RootIsolation.FTA.Squarefree.Basic
public import Purelib.RootIsolation.FTA.Squarefree.Input
public import Purelib.Polynomial.Elimination.Axis.Preparation
-- Complete original-preparation equalities retain the original isolation procedure.
public import Purelib.RootIsolation.Exact.LargeSquare
-- The original ownership readback names the retained selector itself.
public import Purelib.RootIsolation.Exact.Ownership.Prepare
import Purelib.RootIsolation.Exact.Ownership.Cardinality
import Purelib.RootIsolation.Track.Newton.Build
import Purelib.Geometry.Rational.Box.Refinement
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Retained squarefree isolation with its own checked axis preparation -/

public section

namespace Purelib.RootIsolation.FTA.Squarefree

open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Polynomial.Elimination

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation

set_option genInjectivity false in
/-- The same original squarefree input with its retained alternate axis certificate and complete root family.

The actual axis preparation supplies the same certificate used for isolation,
ownership and localization. Its root family belongs to the original source
polynomial and coefficient square, with its own ordered tracks and support.
It is not identified with the canonical input's separate isolation procedure.
-/
structure Preparation {p : CoefficientPolynomial} (input : Input p) where
  /-- The retained checked preparations of this same original source's two axis systems. -/
  axis : Axis.Preparation.Prepared p
  /-- The actual axis certificate at those retained eliminants' computed degree. -/
  elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p axis.degree
  /-- This certificate belongs to these same retained original matrix preparations. -/
  elimination_eq : elimination = axis.certificate input.nonzero input.degreePositive
  /-- The complete root family with its actual ordered tracks and ownership function. -/
  boxes : BoxResult p
  /-- The retained isolation's exact original coefficient-square support. -/
  support : boxes.isolation.support = RootRadius.Box.largeSquareBox p

constructive_injectivity Preparation

namespace Preparation

/-- Attach ownership and maximality to one retained isolation using its same supplied axis preparation.

Both procedures consume the supplied certificate and original isolation.
The finite family cardinality proof uses that same retained output and support,
without replacing its nominal owner or constructing another family.
-/
def fromIsolation {p : CoefficientPolynomial} (input : Input p)
    (axis : Axis.Preparation.Prepared p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p axis.degree)
    (same : elimination = axis.certificate input.nonzero input.degreePositive)
    (isolation : Exact.Basic.Output p (RootRadius.Box.largeSquareBox p) p.natDegree)
    (support : isolation.support = RootRadius.Box.largeSquareBox p) : Preparation input :=
  let boxes : BoxResult p :=
    { eliminationDegree := axis.degree
      elimination := fun _ => elimination
      isolation := isolation
      ownership := fun track supported =>
        Exact.Ownership.Prepare.selectOutputOwner
          input.degreeAtLeastTwo input.squarefree elimination isolation track supported
      maximality := fun family pairwise =>
        Exact.Ownership.Cardinality.family_card_le_output_count input.degreeAtLeastTwo input.squarefree
          elimination isolation family (fun index => by
            rewrite [support]
            exact (family index).initial.refinesAmbient) pairwise }
  ⟨axis, elimination, same, boxes, support⟩

/-- Prepare the original input's own checked axes and isolate its roots once with that same retained certificate. -/
def ofInput {p : CoefficientPolynomial} (input : Input p) : Preparation input :=
  let axis := Axis.Preparation.prepare p input.nonzero
  let elimination := axis.certificate input.nonzero input.degreePositive
  let isolation := Exact.LargeSquare.isolateLargeSquare input.degreeAtLeastTwo input.squarefree elimination
  fromIsolation input axis elimination rfl isolation
    (Exact.LargeSquare.isolateLargeSquare_support input.degreeAtLeastTwo input.squarefree elimination)

/-- A retained isolation on the original prepared axes yields the complete original preparation.

The supplied axis and elimination equalities retain their actual owners.
Equality of the complete isolation preserves its ordered tracks, and the
original ownership and maximality callbacks close around that same value. -/
theorem fromIsolation_eq_ofInput {p : CoefficientPolynomial} (input : Input p)
    (axis : Axis.Preparation.Prepared p)
    (axisEq : axis = Axis.Preparation.prepare p input.nonzero)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p axis.degree)
    (same : elimination = axis.certificate input.nonzero input.degreePositive)
    (isolation : Exact.Basic.Output p (RootRadius.Box.largeSquareBox p) p.natDegree)
    (support : isolation.support = RootRadius.Box.largeSquareBox p)
    (isolationEq : isolation =
      Exact.LargeSquare.isolateLargeSquare input.degreeAtLeastTwo input.squarefree elimination) :
    fromIsolation input axis elimination same isolation support = ofInput input := by
  cases axisEq
  cases same
  cases isolationEq
  rfl

/-- Every track of an authenticated original preparation retains its complete original Newton constructor.

The original prepared elimination and the actual stored isolation remain
attached to the track. The origin includes its original initial state and
pointwise refinement operation, without constructing another isolation. -/
theorem track_origin {p : CoefficientPolynomial} {input : Input p}
    (preparation : Preparation input) (same : preparation = ofInput input)
    (track : Track.Basic.WindingOneTrack p (RootRadius.Box.largeSquareBox p))
    (member : track ∈ preparation.boxes.isolation.tracks) :
    Track.Newton.Build.Origin input.degreeAtLeastTwo input.squarefree preparation.elimination track := by
  cases same
  exact Exact.LargeSquare.isolateLargeSquare_tracks_origin input.degreeAtLeastTwo input.squarefree
    ((Axis.Preparation.prepare p input.nonzero).certificate input.nonzero input.degreePositive)
    none track member

/-- Authenticated original preparation retains its exact deterministic owner selector.

The actual elimination, isolation, source track and support witness are the
original selector's inputs. The equality concerns the whole owner selection,
including its ownership-radius refinement and retained state. -/
theorem ownership_eq {p : CoefficientPolynomial} {input : Input p}
    (preparation : Preparation input) (same : preparation = ofInput input)
    (track : Track.Basic.WindingOneTrack p (RootRadius.Box.largeSquareBox p))
    (supported : track.initial.box.Refines preparation.boxes.isolation.support) :
    preparation.boxes.ownership track supported =
      Exact.Ownership.Prepare.selectOutputOwner input.degreeAtLeastTwo input.squarefree
        preparation.elimination preparation.boxes.isolation track supported := by
  cases same
  rfl

end Preparation

end Purelib.RootIsolation.FTA.Squarefree

end
