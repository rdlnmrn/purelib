module
import Purelib.Data.Int.Arithmetic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Bilinear.Integral
import Purelib.LinearAlgebra.Bilinear.Matrix.Basic
import Purelib.LinearAlgebra.Vector.Weighted

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.IntegralPairing
public import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.CutIntersection
import Purelib.LinearAlgebra.Bilinear.Matrix.Wedge
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! The paired part of a closed row, retaining its exact physical subtraction. -/

namespace Purelib.Topology.Surface.Cut.PairedRowReadback
public section
open Purelib
open Purelib.Algebra
open Purelib.LinearAlgebra.Bilinear
open Purelib.LinearAlgebra.Vector
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.IntegralPairing
open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord
open Purelib.Data.Int

open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing (SpanningCoordinates)

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_swap sumFin_mul_right)
open Purelib.LinearAlgebra.Vector.Weighted (weighted)
open Purelib.LinearAlgebra.Bilinear.Integral (pairing)

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}
  {word : BoundaryWord.CutBoundaryWord labels edges} {integral : IntegralPairing.CutBoundaryWord word}
  {row : Data.Vector Int word.alphabet.count}
  (span : IntegralPairing.SpanningCoordinates integral row)

/-- Subtract the retained physical row from the original integral row, leaving its paired-coordinate reading. -/
@[expose]
def pairedReadback (index : Fin word.alphabet.count) : Int := row index - span.physical index

open Purelib.Topology.Surface.Cut
/-- The paired readback vanishes at every one-sided generator coordinate. -/
theorem pairedReadback_physical (index : Fin word.alphabet.count)
    (physical : word.alphabet.oneSided index = true) : (pairedReadback span) index = 0 := by
  rw [pairedReadback, span.physical_eq, physical]
  exact sub_self _

/-- The paired readback equals the original row at every two-sided generator coordinate.

The supplied two-sided generator coordinate has zero physical contribution. Subtracting that exact zero retains the
original integral row entry. -/
theorem pairedReadback_paired (index : Fin word.alphabet.count)
    (paired : word.alphabet.oneSided index = false) : (pairedReadback span) index = row index := by
  rw [pairedReadback, span.physical_eq, paired]
  exact Arithmetic.sub_zero _

/-- The paired readback is exactly the retained linear combination of paired matrix rows. -/
theorem pairedReadback_eq_sum (index : Fin word.alphabet.count) :
    (pairedReadback span) index = FiniteSum.Fin.sumFin (fun position => span.coefficients position *
      integral.paired position index) := by
  have equal := span.equation index
  unfold pairedReadback
  omega

/-- Evaluating the paired readback agrees with the paired matrix contraction against the retained coefficients. -/
theorem weighted_pairedReadback (values : Data.Vector Int word.alphabet.count) :
    Weighted.weighted (pairedReadback span) values = Integral.pairing integral.paired
      span.coefficients values := by
  calc
    _ = FiniteSum.Fin.sumFin (fun column => FiniteSum.Fin.sumFin (fun index => span.coefficients index * integral.paired
      index column * values column)) := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [pairedReadback_eq_sum span]
      exact (FiniteSum.Fin.sumFin_mul_right _ _).symm
    _ = _ := (FiniteSum.Fin.sumFin_swap _).trans (FiniteSum.Fin.sumFin_congr (fun index => FiniteSum.Fin.sumFin_congr
      (fun column => by
      dsimp only [Integral.pairing, Matrix.Basic.bilinear]
      rw [Int.cast_id]
      ring1)))

end
end Purelib.Topology.Surface.Cut.PairedRowReadback
