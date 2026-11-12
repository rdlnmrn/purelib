module

import Purelib.Approximation.Gaussian.Observation.Prefix.Family
import Purelib.Approximation.Gaussian.Observation.Prefix.Observer.Source
import Purelib.Approximation.Gaussian.Observation.Prefix.Check
import TestPurelib.Approximation.Gaussian.Observation.Prefix
import Purelib.Data.Rat.Fraction.Cast

/-! # Distinct finite rational continuations preserve one complete adaptive numerical execution -/

namespace TestPurelib.Approximation.Gaussian.Observation.Prefix.Family

open Purelib
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Observation
open Purelib.Geometry.Rational
open Purelib.Data.CCL
open Purelib.Data.Rat

/-- An actual proper source region for separated numerical continuations. -/
private def box : Box := ⟨1 / 4, 1 / 2, 1 / 8, 1 / 4, by decide, by decide⟩

/-- Check all retained leaves, exact whole executions, distinct readings and later accuracy. -/
public def run : IO Unit := do
  let origin := Prefix.Source.Snapshot.ofEnclosure (Encoding.Prefix.Enclosure.ofBox box ⟨by decide, by decide⟩)
  let original := Prefix.Observer.Source.execute origin [.block Prefix.program] [] 100
  let recording := original.context.recording
  unless original.requestCount == original.state.path.length &&
      original.evaluationCount ≤ original.evaluationBound do
    throw (IO.userError "separated family lost its original source construction accounting")
  for depth in [0, 1, 2, 3] do
    let family := Prefix.Source.Recording.Family.build recording depth
    unless family.leaves.length == 2 ^ depth do
      throw (IO.userError "separated family lost its requested number of leaves")
    let mut readings : List Purelib.Data.Gaussian.Basic.Canonical := []
    let mut words : List (List Bool) := []
    for leaf in family.leaves do
      let point := leaf.admitted.realization.point
      let terminal := leaf.continuation.terminal
      unless !words.contains terminal.completion.word &&
          decide (terminal.completion.word = terminal.encoding.word) &&
          terminal.bound == terminal.encoding.word.length - leaf.admitted.endpoint.cursor.word.length do
        throw (IO.userError "separated leaf lost its cached canonical terminal word or computed bound")
      words := terminal.completion.word :: words
      for entry in recording.trace do
        unless decide (terminal.completion.word.take entry.reply.word.length = entry.reply.word) do
          throw (IO.userError "separated leaf terminal completion discarded an original exposed word")
      unless decide (recording.current.enclosure.box.Contains point) && !readings.contains point do
        throw (IO.userError "separated family duplicated a leaf or left its uniform box")
      readings := point :: readings
      match Prefix.Check.check leaf.admitted.history with
      | .valid _ => pure ()
      | _ => throw (IO.userError "retained rational leaf failed complete independent history checking")
      let replay := Prefix.Observer.execute [.block Prefix.program] [] 100 leaf.interpret
      unless Prefix.sameTrace replay.trace original.numerical.trace do
        throw (IO.userError "separated leaf changed the complete adaptive numerical trace")
      match replay.value, original.numerical.value with
      | .returned (.natural actual), .returned (.natural expected) =>
          unless actual == expected do throw (IO.userError "separated leaf changed the numerical result")
      | _, _ => throw (IO.userError "separated leaf changed the returned numerical kind")
      let target : Fraction.Rational := 1 / Fraction.Cast.fromInt 256
      let before := leaf.interpret ⟨[], .bits 5⟩
      let later := leaf.interpret ⟨[.bits 5], .enclosure target (by decide)⟩
      unless decide (later.word = before.word) && decide (later.ball.radiusSq < target) &&
          decide (later.ball.Contains point) do
        throw (IO.userError "separated leaf failed a later divergent prefix or accuracy request")
    let admissions := Prefix.Source.Recording.Family.admissions recording depth
    unless admissions.map (fun admitted => admitted.realization.point) == readings.reverse do
      throw (IO.userError "direct admissions differ from the complete family's ordered leaf points")
  IO.print "separated families: depths 0 through 3 preserve exact observers, distinct readings and later accuracy\n"

end TestPurelib.Approximation.Gaussian.Observation.Prefix.Family
