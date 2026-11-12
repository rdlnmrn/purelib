module

import Purelib.Data.CCL.Encoding.Prefix.Completion
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.List.BinaryPrefix.Decision
import Purelib.Geometry.Projective.Line.Gaussian

/-! # Exact saved raw prefixes finish through the original sector encoder and their cached decoder chart -/

namespace TestPurelib.Data.CCL.Encoding.Prefix.Completion

open Purelib
open Purelib.Data
open Purelib.Data.CCL
open Purelib.Data.Gaussian
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Geometry.Rational
open Purelib.Geometry.Projective

/-- Realize a nonzero sample in a proper box and finish its original cursor using the automatically computed bound. -/
private def check (point : Basic.Canonical) (inside : (Box.symmetric 2 (by decide)).Contains point)
    (nonzero : point ≠ 0) : IO Unit := do
  let enclosure := Encoding.Prefix.Enclosure.ofBox (Box.symmetric 2 (by decide)) ⟨by decide, by decide⟩
  let realization := enclosure.realizeSample ⟨point, inside, nonzero⟩
  let original := Encoding.Prefix.Cursor.ofRealization realization
  let finished := original.val.finishEncoding original.property realization.fraction
    realization.numeratorNonzero realization.fractionValue
  let completed := finished.completion
  unless List.BinaryPrefix.Decision.isWordPrefix original.val.word completed.word &&
      List.BinaryPrefix.Decision.isWordPrefix finished.request.next.word completed.word &&
      completed.word.length == finished.request.next.word.length + 1 &&
      decide (completed.encoding.word = [completed.first, completed.second, completed.bit]) &&
      decide (completed.word = finished.encoding.word) &&
      finished.bound == finished.encoding.word.length - original.val.word.length do
    throw (IO.userError "automatic canonical terminal completion lost its original prefix, encoder word or bound")
  unless decide (Line.Gaussian.Proj.affineReading
      (Line.Matrix.act completed.state.matrix Line.Proj.omega) = point) &&
      decide ((Line.Matrix.act completed.state.matrix Line.Proj.omega).q ≠ 0) do
    throw (IO.userError "automatic canonical completion lost its original affine input or projective denominator")
  match finished.request.next.nextBit finished.request.valid with
  | .terminal _ => pure ()
  | .advanced _ => throw (IO.userError "automatic canonical bound failed to reach its actual affine terminal")
  let exactBound := original.val.request original.property (finished.bound - 1)
  let detection := exactBound.next.request exactBound.valid 1
  unless exactBound.suffix.length == finished.bound - 1 &&
      decide (exactBound.next.word = finished.request.next.word) && detection.suffix.isEmpty do
    throw (IO.userError "computed canonical bound lost its exact affine suffix or stop-detection unit")

/-- Check every original sector representative, the radial equality boundary and nonterminal rational examples. -/
public def run : IO Unit := do
  for sector in [Sector.east, Sector.northEast, Sector.north, Sector.northWest,
      Sector.west, Sector.southWest, Sector.south, Sector.southEast] do
    have inside : (Box.symmetric 2 (by decide)).Contains sector.rep := by cases sector <;> decide
    have nonzero : sector.rep ≠ 0 := by cases sector <;> decide
    check sector.rep inside nonzero
  check (⟨3 / 2, 1 / 2⟩ : Basic.Canonical) ⟨by decide, by decide, by decide, by decide⟩ (by decide)
  check (⟨1 / 3, 1 / 2⟩ : Basic.Canonical) ⟨by decide, by decide, by decide, by decide⟩ (by decide)
  IO.print "canonical completion: saved prefixes, all sectors and rational tails finish through original encoder bits\n"

end TestPurelib.Data.CCL.Encoding.Prefix.Completion
