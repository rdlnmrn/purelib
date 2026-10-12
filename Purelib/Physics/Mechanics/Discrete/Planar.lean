module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Point.Addition
import Purelib.Geometry.Plane.Point.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field (ExplicitField)

section
@[expose] public section

/-!
# Discrete planar motion
-/

namespace Purelib.Physics.Mechanics.Discrete.Planar

variable {K : Type*} [ExplicitField K]

open Purelib.Geometry.Plane in
set_option genInjectivity false in
/-- A planar particle state with position and velocity over the same scalar type.

Both coordinates are retained as points; equality compares the two fields componentwise when scalar equality is
decidable. -/
@[ext] structure ParticleState (K : Type*) where
  /-- The current planar position. -/ position : Purelib.Geometry.Plane.Point K
  /-- The current planar velocity. -/ velocity : Purelib.Geometry.Plane.Point K
deriving DecidableEq

constructive_injectivity Purelib.Physics.Mechanics.Discrete.Planar.ParticleState

open Purelib.Geometry.Plane in
open Purelib.Physics.Mechanics.Discrete in
/-- Advance position by the retained velocity and velocity by the supplied acceleration.

Both updates use the input state, so the position increment uses the old velocity. The construction requires only the
explicit field operations. -/
def particleStep (acceleration : Purelib.Geometry.Plane.Point K)
    (state : Planar.ParticleState K) : Planar.ParticleState K :=
  ⟨Point.Addition.pointAdd state.position state.velocity,
    Point.Addition.pointAdd state.velocity acceleration⟩
end Purelib.Physics.Mechanics.Discrete.Planar

end
