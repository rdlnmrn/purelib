module
import Purelib.Geometry.Projective.Bihomographic.Basic
public import Purelib.Geometry.Projective.Bihomographic.Composition
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Matrix
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.Gaussian.Basic

open Purelib

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Bihomographic.Basic

open Purelib.Geometry.Projective.Line.Basic

open Purelib.LinearAlgebra.Coordinates2.Matrix

section
@[expose] public section

/-!
# Bihomographic semantics of progressive arithmetic

The enclosure implementation computes `+`, `-`, `*`, and `/` directly on
finite rational balls.  This module proves that its candidate predicates are
the affine instances of the paper's bihomographic initial matrices and that
all input/output decoder substitutions compose exactly.  Thus the direct
implementation and the matrix account are two certified views of the same
finite arithmetic step.
-/

namespace Purelib.Geometry.Projective.Bihomographic.Substitution

/-- Consuming one matrix from each input is exact, independent of the elementary operation represented by the eight
coefficients. -/
theorem map_precompose_both (state :
  Bihomographic.Basic.State) (left right : GaussianMatrix)
    (x y : Line.GaussianLine) :
    ((state.precomposeLeft left).precomposeRight right).map x y =
      state.map (Line.Matrix.act left x) (Line.Matrix.act right y) := by
  rw [State.map_precomposeRight, State.map_precomposeLeft]

/-- Input consumption followed by an output chart change is one exact projective identity. -/
theorem map_full_substitution (state :
  Bihomographic.Basic.State) (left right output : GaussianMatrix)
    (x y : Line.GaussianLine) :
    (((state.precomposeLeft left).precomposeRight right).postcompose output).map
        x y =
      Line.Matrix.act output
        (state.map (Line.Matrix.act left x) (Line.Matrix.act right y)) := by
  rw [State.map_postcompose, map_precompose_both]

/-- In particular, emitting an output decoder block uses its explicit adjugate while input blocks are precomposed in
their respective variables. -/
theorem map_after_emitted_block (state :
  Bihomographic.Basic.State) (left right block : GaussianMatrix)
    (x y : Line.GaussianLine) :
    (((state.precomposeLeft left).precomposeRight right).postcompose
        (BoundaryAdjugate.adjugate block)).map x y =
      Line.Matrix.act (BoundaryAdjugate.adjugate block)
        (state.map (Line.Matrix.act left x) (Line.Matrix.act right y)) :=
  map_full_substitution state left right
    (BoundaryAdjugate.adjugate block) x y

end Purelib.Geometry.Projective.Bihomographic.Substitution

end
