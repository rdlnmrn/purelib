module

import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Preparation
import Purelib.RootIsolation.Progressive.Power.Unit.Frame.Preparation
import Purelib.RootIsolation.Progressive.Power.Frame.Preparation
import Purelib.RootIsolation.Progressive.Power.Unit.Owner.Preparation
import Purelib.RootIsolation.Progressive.Power.Unit.Move.Frame.Preparation
import Purelib.RootIsolation.Owner.Local.Preparation
import Purelib.RootIsolation.Power.Unit.Source.Preparation
import Purelib.Riemann.RootContinuation.CoherentRoot.Reconditioning.Algebraic

/-! # Complete original-owner and numerical-cache readbacks -/

namespace TestPurelib.Riemann.RootOwnerPreparation

open Purelib
open Purelib.RootIsolation
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Nonzero (nonzero_of_normSq_eq_one)
open Purelib.RootIsolation.Progressive.Power
open Purelib.RootIsolation.Owner.Local.Preparation (Prepared)
open Purelib.Data.Nat.Positive (RootDegree)

example (frame : ChamberFrame) (index : frame.Index)
    (prepared : Prepared (frame.owner index)) :
    Root.ofPreparedOwner frame index prepared = Root.ofOwner frame index :=
  Root.ofPreparedOwner_eq frame index prepared

example (frame : ChamberFrame) (index : frame.Index) (root : CoherentRoot.Chamber.Root frame index)
    (start : Nat) (target : Data.Rat.Fraction.Rational) (positive : 0 < target) :
    CoherentRoot.Reconditioning.ofTargetFromAmbient root.track.initial.box root.initial_box
      root.certificate start target positive =
      CoherentRoot.Reconditioning.ofTarget root.certificate start target positive :=
  CoherentRoot.Reconditioning.ofTargetFromAmbient_eq root.track.initial.box root.initial_box
    root.certificate start target positive

example (frame : ChamberFrame) (index : frame.Index) (root : CoherentRoot.Chamber.Root frame index)
    (start : Nat) (prepared : CoherentRoot.Reconditioning root.certificate start) :
    prepared.algebraicFromAmbient root.track.initial.box root.initial_box frame.input =
      prepared.algebraic frame.input :=
  prepared.algebraicFromAmbient_eq root.track.initial.box root.initial_box frame.input

example (frame : ChamberFrame) (index : frame.Index) (root : Root frame index)
    (start : Nat) (target : Data.Rat.Fraction.Rational) (positive : 0 < target)
    (paid : CoherentRoot.Refinement root.certificate (start + 1))
    (same : paid = CoherentRoot.Refinement.ofTarget root.certificate (start + 1) target positive) :
    CoherentRoot.Reconditioning.ofRefinementFromAmbient root.track.initial.box root.initial_box
      root.certificate start target positive paid same =
      CoherentRoot.Reconditioning.ofTarget root.certificate start target positive :=
  CoherentRoot.Reconditioning.ofRefinementFromAmbient_eq root.track.initial.box root.initial_box
    root.certificate start target positive paid same

example (frame : ChamberFrame) (index : frame.Index) (root : Root frame index)
    (start : Nat) (target : Data.Rat.Fraction.Rational) (positive : 0 < target)
    (current : CoherentRoot.WindingOneState frame.polynomial (frame.owner index).box)
    (same : current = root.certificate.stateAt start) (accurate : current.box.diagonalSq < target) :
    CoherentRoot.Refinement.ofTargetFromState root.certificate start target positive current same accurate =
      CoherentRoot.Refinement.ofTarget root.certificate start target positive :=
  CoherentRoot.Refinement.ofTargetFromState_eq root.certificate start target positive current same accurate

example {start finish : ChamberFrame}
    (path : Progressive.Chamber.Path.Basic.ChamberPath start finish)
    (index : start.Index) (root : Root start index)
    (owners : CoherentRoot.Chamber.Trace.Owners path index) :
    CoherentRoot.Chamber.Trace.ofPreparedOwners root owners =
      CoherentRoot.Chamber.Trace.build path index root :=
  CoherentRoot.Chamber.Trace.ofPreparedOwners_eq root owners

example {parameter : Canonical} (nonzero : parameter ≠ 0) (unit : normSq parameter = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value) (index : Fin degree.value)
    (source : Power.Unit.Source.Preparation.Prepared nonzero unit degree degreeTwo index) :
    (Unit.Owner.Preparation.fromSource nonzero unit degree degreeTwo index source).owner.owner =
      Unit.Owner.unitRobustOwner nonzero unit degree degreeTwo index :=
  (Unit.Owner.Preparation.fromSource nonzero unit degree degreeTwo index source).owner.owner_eq

example {parameter : Canonical} (nonzero : parameter ≠ 0) (unit : normSq parameter = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (index : (Unit.Frame.robustChamberFrame nonzero unit degree degreeTwo).Index)
    (prepared : Unit.Owner.Preparation.Prepared nonzero unit degree degreeTwo
      (Fin.cast (Unit.Frame.robustChamberFrame_degree nonzero unit degree degreeTwo) index)) :
    (Unit.Frame.Preparation.fromOwner nonzero unit degree degreeTwo index prepared).owner =
      (Unit.Frame.robustChamberFrame nonzero unit degree degreeTwo).owner index :=
  (Unit.Frame.Preparation.fromOwner nonzero unit degree degreeTwo index prepared).owner_eq

example {source target : Canonical} (sourceUnit : normSq source = 1) (targetUnit : normSq target = 1)
    (degree : RootDegree) (degreeTwo : 2 ≤ degree.value)
    (small : Power.Unit.Move.Budget.UnitMoveSmall sourceUnit targetUnit degree degreeTwo)
    (index : (Unit.Frame.robustChamberFrame
      (nonzero_of_normSq_eq_one sourceUnit)
      sourceUnit degree degreeTwo).Index)
    (prepared : Prepared
      ((Unit.Frame.robustChamberFrame
        (nonzero_of_normSq_eq_one sourceUnit)
        sourceUnit degree degreeTwo).owner index)) :
    (Unit.Move.Frame.Preparation.fromSource
      sourceUnit targetUnit degree degreeTwo small index prepared).owner =
      (Unit.Move.Frame.unitTransportedFrame sourceUnit targetUnit degree degreeTwo small).owner
        (Fin.cast (Unit.Move.Frame.unitMoveCountEq sourceUnit targetUnit degree degreeTwo) index) :=
  (Unit.Move.Frame.Preparation.fromSource
    sourceUnit targetUnit degree degreeTwo small index prepared).owner_eq

example {parameter : Canonical} (nonzero : parameter ≠ 0) (degree : RootDegree)
    (degreeTwo : 2 ≤ degree.value) (prepared : Frame.Preparation.Prepared nonzero degree degreeTwo) :
    prepared.frame = Frame.Basic.chamberFrame nonzero degree degreeTwo := prepared.frame_eq

example {parameter : Canonical} (nonzero : parameter ≠ 0) (degree : RootDegree)
    (degreeTwo : 2 ≤ degree.value) (prepared : Frame.Preparation.Prepared nonzero degree degreeTwo) :
    prepared.isolation = (Power.Isolation.isolationInput nonzero degree degreeTwo).isolation :=
  prepared.isolation_eq

example {parameter : Canonical} (nonzero : parameter ≠ 0) (degree : RootDegree)
    (degreeTwo : 2 ≤ degree.value) (prepared : Frame.Preparation.Prepared nonzero degree degreeTwo)
    (index : (Frame.Basic.chamberFrame nonzero degree degreeTwo).Index) :
    Root.ofPreparedOwner _ index (prepared.owner index) =
      Root.ofOwner _ index :=
  Root.ofPreparedOwner_eq _ index (prepared.owner index)

example {parameter : Canonical} (nonzero : parameter ≠ 0) (degree : RootDegree)
    (degreeTwo : 2 ≤ degree.value) (prepared : Frame.Preparation.Prepared nonzero degree degreeTwo) :
    prepared.input = Power.Isolation.isolationInput nonzero degree degreeTwo := prepared.input_eq

example {parameter : Canonical} (nonzero : parameter ≠ 0) (degree : RootDegree)
    (degreeTwo : 2 ≤ degree.value) (prepared : Frame.Preparation.Prepared nonzero degree degreeTwo) :
    prepared.elimination = prepared.input.elimination := prepared.elimination_eq

example {parameter : Canonical} (nonzero : parameter ≠ 0) (degree : RootDegree)
    (degreeTwo : 2 ≤ degree.value) (prepared : Frame.Preparation.Prepared nonzero degree degreeTwo)
    {ambient : Purelib.Geometry.Rational.Box}
    (current : State.WindingOne.Basic.WindingOneState
      (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree) ambient)
    (epsilon : Purelib.Data.Rat.Fraction.Rational) (positive : 0 < epsilon) :
    Track.Newton.Refinement.refineState prepared.input.degreeAtLeastTwo prepared.input.squarefree
      prepared.elimination current epsilon positive =
    Track.Newton.Refinement.refineState
      (Power.Isolation.isolationInput nonzero degree degreeTwo).degreeAtLeastTwo
      (Power.Isolation.isolationInput nonzero degree degreeTwo).squarefree
      (Power.Isolation.isolationInput nonzero degree degreeTwo).elimination current epsilon positive :=
  prepared.refine_eq current epsilon positive

end TestPurelib.Riemann.RootOwnerPreparation
