module

public import Purelib.RootIsolation.Progressive.Power.Frame.Basic
public import Purelib.RootIsolation.Owner.Local.Preparation
public import Purelib.RootIsolation.Power.Isolation.Track
public import Purelib.RootIsolation.FTA.Squarefree.Prepare
import Purelib.RootIsolation.Track.Newton.Refinement
import Purelib.RootIsolation.Owner.Local.Transport
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Canonical power frames and owners from retained original isolation -/

public section

namespace Purelib.RootIsolation.Progressive.Power.Frame.Preparation

open Purelib
open Purelib.RootIsolation
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Nat.Positive (RootDegree)
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.Polynomial

set_option genInjectivity false in
/-- A cached complete frame equal to the original coefficient-selected power frame.

The cached frame retains its original reference table, complete ordered owner
family and chamber certificate. Its equality identifies all these fields,
including every original bounded owner occurrence.
-/
structure Prepared {parameter : Canonical} (nonzero : parameter ≠ 0)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value) where
  /-- The actual complete cached frame consumed by owner lookup and matching. -/
  frame : ChamberFrame
  /-- The cached frame is the complete original coefficient-selected frame. -/
  frame_eq : frame = Basic.chamberFrame nonzero degree degreeTwo
  /-- The actual saved original partition, including its ordered tracks and zero-winding remainder cells. -/
  isolation : Exact.Basic.Output (Power.Gaussian.rootPolynomial parameter degree)
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Power.Gaussian.rootPolynomial parameter degree))
    (Power.Gaussian.rootPolynomial parameter degree).natDegree
  /-- The cached complete partition is the original power input's deterministic isolation. -/
  isolation_eq : isolation = (Power.Isolation.isolationInput nonzero degree degreeTwo).isolation
  /-- The actual original squarefree input reused by isolation and later root refinements. -/
  input : FTA.Squarefree.Input (Power.Gaussian.rootPolynomial parameter degree)
  /-- The retained complete input is the original power-family input at the same parameter and degree. -/
  input_eq : input = Power.Isolation.isolationInput nonzero degree degreeTwo
  /-- The actual original bounded axis-elimination certificate paid during isolation. -/
  elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate
    (Power.Gaussian.rootPolynomial parameter degree) input.eliminationDegree
  /-- The retained elimination certificate is the same input's complete original constructor. -/
  elimination_eq : elimination = input.elimination

constructive_injectivity Prepared

/-- Attach original input, elimination, coefficient table and owners to the same saved complete isolation.

The retained input and bounded elimination have complete original readbacks.
Ownership and maximality consume the same isolation; later refinement clients
reuse the elimination already computed for its producer.
-/
@[expose] def fromCachedIsolation {parameter : Canonical} (nonzero : parameter ≠ 0)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (input : FTA.Squarefree.Input (Power.Gaussian.rootPolynomial parameter degree))
    (inputEq : input = Power.Isolation.isolationInput nonzero degree degreeTwo)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate
      (Power.Gaussian.rootPolynomial parameter degree) input.eliminationDegree)
    (eliminationEq : elimination = input.elimination)
    (isolation : Exact.Basic.Output (Power.Gaussian.rootPolynomial parameter degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Power.Gaussian.rootPolynomial parameter degree))
      (Power.Gaussian.rootPolynomial parameter degree).natDegree)
    (same : isolation = (Power.Isolation.isolationInput nonzero degree degreeTwo).isolation) :
    Prepared nonzero degree degreeTwo :=
  let result : FTA.Squarefree.AdapterResult (Power.Gaussian.rootPolynomial parameter degree) :=
    ⟨FTA.Squarefree.Build.BoxFTA.fromIsolation input isolation⟩
  have resultEq : result = Power.Isolation.isolationResult nonzero degree degreeTwo :=
    (congrArg FTA.Squarefree.AdapterResult.mk
      (FTA.Squarefree.Build.BoxFTA.fromIsolation_eq_prove input isolation
        (same.trans (congrArg FTA.Squarefree.Input.isolation inputEq.symm)))).trans
      (congrArg FTA.Squarefree.Build.Box.prove inputEq)
  { frame := Basic.fromResult nonzero degree degreeTwo result
    frame_eq := Basic.fromResult_eq_chamberFrame nonzero degree degreeTwo result resultEq
    isolation := isolation
    isolation_eq := same
    input := input
    input_eq := inputEq
    elimination := elimination
    elimination_eq := eliminationEq }

/-- Attach the original coefficient-selected frame and input cache to a saved complete isolation.

The original input and elimination are computed once by this constructor.
Clients that already paid them use `fromCachedIsolation` instead.
-/
@[expose] def fromIsolation {parameter : Canonical} (nonzero : parameter ≠ 0)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (isolation : Exact.Basic.Output (Power.Gaussian.rootPolynomial parameter degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Power.Gaussian.rootPolynomial parameter degree))
      (Power.Gaussian.rootPolynomial parameter degree).natDegree)
    (same : isolation = (Power.Isolation.isolationInput nonzero degree degreeTwo).isolation) :
    Prepared nonzero degree degreeTwo :=
  let input := Power.Isolation.isolationInput nonzero degree degreeTwo
  fromCachedIsolation nonzero degree degreeTwo input rfl input.elimination rfl isolation same

/-- Read one cached owner at its original frame index, preserving the complete original local owner.

The existing degree and polynomial casts transport the actual cached lookup
to the original frame occurrence. Equality supplies the complete owner
readback without running a canonical frame or owner producer.
-/
@[expose] def Prepared.owner {parameter : Canonical} {nonzero : parameter ≠ 0}
    {degree : RootDegree} {degreeTwo : 2 ≤ degree.value} (prepared : Prepared nonzero degree degreeTwo)
    (index : (Basic.chamberFrame nonzero degree degreeTwo).Index) :
    Owner.Local.Preparation.Prepared ((Basic.chamberFrame nonzero degree degreeTwo).owner index) :=
  let cachedIndex := Fin.cast (congrArg ChamberFrame.degree prepared.frame_eq.symm) index
  let cachedOwner := Owner.Local.Transport.castOwner
    (congrArg ChamberFrame.polynomial prepared.frame_eq) (prepared.frame.owner cachedIndex)
  { owner := cachedOwner
    owner_eq := by
      rcases prepared with ⟨frame, same, _, _, _, _, _, _⟩
      cases same
      rfl }

/-- Read the exact original globally supported track from the retained complete isolation partition.

The original degree index is transported by the same polynomial-degree
identity, then consumed by the cached partition's original track lookup.
The complete track readback preserves its initial state and refinement operation.
-/
@[expose] def Prepared.track {parameter : Canonical} {nonzero : parameter ≠ 0}
    {degree : RootDegree} {degreeTwo : 2 ≤ degree.value} (prepared : Prepared nonzero degree degreeTwo)
    (index : Fin degree.value) :
    { value : RootIsolation.Track.Basic.WindingOneTrack (Power.Gaussian.rootPolynomial parameter degree)
      (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox (Power.Gaussian.rootPolynomial parameter degree)) //
      value = Power.Isolation.Track.isolatedTrack nonzero degree degreeTwo index } :=
  let retained := prepared.isolation.trackAt
    (Fin.cast (Power.Gaussian.rootPolynomial_degree parameter degree).symm index)
  ⟨retained, by
    rcases prepared with ⟨frame, frameEq, isolation, same, _, _, _, _⟩
    cases same
    rfl⟩

/-- Refining with a frame's retained input and elimination gives the complete original power-family Newton result.

The original polynomial, ambient, current state and positive accuracy remain
fixed. Both exact cache equalities transport the entire result, including its
new box, boundary certificate and four ambient clearances.
-/
theorem Prepared.refine_eq {parameter : Canonical} {nonzero : parameter ≠ 0}
    {degree : RootDegree} {degreeTwo : 2 ≤ degree.value} (prepared : Prepared nonzero degree degreeTwo)
    {ambient : Geometry.Rational.Box}
    (current : State.WindingOne.Basic.WindingOneState (Power.Gaussian.rootPolynomial parameter degree) ambient)
    (epsilon : Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    RootIsolation.Track.Newton.Refinement.refineState prepared.input.degreeAtLeastTwo prepared.input.squarefree
      prepared.elimination current epsilon positive =
    RootIsolation.Track.Newton.Refinement.refineState
      (Power.Isolation.isolationInput nonzero degree degreeTwo).degreeAtLeastTwo
      (Power.Isolation.isolationInput nonzero degree degreeTwo).squarefree
      (Power.Isolation.isolationInput nonzero degree degreeTwo).elimination current epsilon positive :=
  (congrArg (fun elimination => RootIsolation.Track.Newton.Refinement.refineState
    prepared.input.degreeAtLeastTwo prepared.input.squarefree elimination current epsilon positive)
    prepared.elimination_eq).trans
    (congrArg (fun input : FTA.Squarefree.Input (Power.Gaussian.rootPolynomial parameter degree) =>
      RootIsolation.Track.Newton.Refinement.refineState input.degreeAtLeastTwo input.squarefree input.elimination
        current epsilon positive) prepared.input_eq)

end Purelib.RootIsolation.Progressive.Power.Frame.Preparation
