module

import Purelib.Approximation.Gaussian.Enclosure.Ball.Presentation
import Purelib.Data.Gaussian.Presentation
import Purelib.Geometry.Gaussian.UnitCircle.Presentation

open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Approximation.Gaussian.Enclosure.Ball.Data
open Purelib.Approximation.Gaussian.Enclosure.Ball.Presentation

example : (match check (⟨0, 0⟩ : BallData) with
    | .valid _ => true
    | .negativeRadius _ => false) = true := by decide

example : (match check (⟨0, 1⟩ : BallData) with
    | .valid _ => true
    | .negativeRadius _ => false) = true := by decide

example : (match check (⟨0, -1⟩ : BallData) with
    | .valid _ => false
    | .negativeRadius _ => true) = true := by decide

private def zeroBall : Display := ⟨⟨0, 0⟩, by decide⟩

private def unitBall : Display := ⟨⟨0, 1⟩, by decide⟩

example : (match compare zeroBall zeroBall with
    | .isTrue _ => true
    | .isFalse _ => false) = true := by decide

example : (match compare zeroBall unitBall with
    | .isTrue _ => false
    | .isFalse _ => true) = true := by decide

example (original : Ball) : read (quote original) = original := read_quote original

example (display : Display) : quote (read display) = display := quote_read display

example (left right : Display) : Same left right ↔ read left = read right :=
  same_iff_read_eq left right

example (original : Ball) (first second : 0 ≤ original.radiusSq) :
    (⟨original.center, original.radiusSq, first⟩ : Ball) =
      ⟨original.center, original.radiusSq, second⟩ := Ball.ext rfl rfl

namespace GaussianCoordinates

open Purelib.Data.Gaussian

private def first : Presentation.Display := ⟨(1, 0), trivial⟩

private def second : Presentation.Display := ⟨(1, 1), trivial⟩

private def third : Presentation.Display := ⟨(0, 0), trivial⟩

example : (match Presentation.recognize (1, 0) with
    | .isTrue _ => true
    | .isFalse _ => false) = true := by decide

example : (match Presentation.compare first first with
    | .isTrue _ => true
    | .isFalse _ => false) = true := by decide

example : (match Presentation.compare first second with
    | .isTrue _ => false
    | .isFalse _ => true) = true := by decide

example : (match Presentation.compare first third with
    | .isTrue _ => false
    | .isFalse _ => true) = true := by decide

example (original : Ball) :
    Presentation.read (Presentation.quote original.center) = original.center :=
  Presentation.read_quote original.center

example (original : Purelib.Geometry.Gaussian.UnitCircle.Basic.UnitVertex) :
    Presentation.read (Presentation.quote original.value) = original.value :=
  Presentation.read_quote original.value

example (display : Presentation.Display) :
    Presentation.quote (Presentation.read display) = display := Presentation.quote_read display

example (left right : Presentation.Display) :
    Presentation.Same left right ↔ Presentation.read left = Presentation.read right :=
  Presentation.same_iff_read_eq left right

end GaussianCoordinates
