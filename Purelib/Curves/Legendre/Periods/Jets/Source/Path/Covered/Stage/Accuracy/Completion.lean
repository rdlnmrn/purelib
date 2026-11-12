module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained.Transport
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

/-! # Completed families of the same actual sufficiently paid source request

The original Requested owner retains its canonical covered-stage factory.
One genuine completion extends through that exact stage family and retains
the whole selected Completed cache. New stages keep their own original
Targets, preparations, bank checks and numerical admissions.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

/-- Retain this same actual source request and genuine completion throughout its canonical stage family.

The original attempt_eq certificate supplies the factory evidence. No
all-stage success or new signed geometric comparison is assumed. Only
new stages execute their original preparation/check factories; the
selected member retains the entire supplied Completed object.
-/
public def completedFamily
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (request : Requested covered chain current floor rootStage accuracy)
    (completed : Completion request.attempt) : request.attempt.CompletedFamily :=
  let selected : Completed covered chain request.selected.stage floor rootStage := ⟨request.attempt, completed⟩
  Completed.family (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (index := request.selected.stage) (floor := floor) (rootStage := rootStage)
    covered chain selected request.attempt_eq

/-- The selected member is the same whole original completed request, including all retained geometric caches. -/
public theorem completedFamily_at
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (request : Requested covered chain current floor rootStage accuracy)
    (completed : Completion request.attempt) :
    (request.completedFamily completed request.selected.stage).val =
      (⟨request.attempt, completed⟩ : Completed covered chain request.selected.stage floor rootStage) := by
  unfold completedFamily
  exact Completed.family_at (parameter := parameter) (frame := frame) (basis := basis) (count := count)
    (parent := parent) (parents := parents) (index := request.selected.stage) (floor := floor) (rootStage := rootStage)
    covered chain ⟨request.attempt, completed⟩ request.attempt_eq

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested
