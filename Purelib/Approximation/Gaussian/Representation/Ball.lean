module
public import Purelib.Approximation.Gaussian.Representation.Basic

import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Refinement
import Purelib.Data.Gaussian.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Enclosure.Ball.Refinement

section
@[expose] public section

/-!
# Finite enclosure representations and direct translations

This module instantiates the generic protocol for rational balls, rational
boxes, boxed raw CCL prefixes, finite fast-Cauchy indices, and states of an
arbitrary progressive enclosure process.
-/

namespace Purelib.Approximation.Gaussian.Representation.Ball
open Purelib.Data.Gaussian.Basic.Canonical

namespace Ball
end Ball

/-- Closed Gaussian-rational balls, using their stored squared radius as the native precision gauge. -/
def ballRepresentation :
  Approximation.Gaussian.Representation where
  Observation := Ball
  Possible ball value := ball.Contains value
  witness ball := ball.center
  witness_possible ball := ball.contains_center
  Refines := Approximation.Gaussian.Enclosure.Ball.Refinement.Refines
  refines_refl := Approximation.Gaussian.Enclosure.Ball.Refinement.refines_refl
  refines_trans := Approximation.Gaussian.Enclosure.Ball.Refinement.refines_trans
  possible_persists refines possible := refines possible
  precisionSq ball := ball.radiusSq
  precisionSq_nonneg ball := ball.radiusSq_nonneg
  boundary := .closed
end Purelib.Approximation.Gaussian.Representation.Ball

end
