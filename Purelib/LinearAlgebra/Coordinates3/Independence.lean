module

public import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Algebra.Field.ExplicitField

open Purelib.Algebra.Field

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

@[expose] public section

namespace Purelib.LinearAlgebra.Coordinates3.Vector

open Purelib.LinearAlgebra.Coordinates3

variable {K : Type*} [ExplicitField K]

/-- Displayed independence of two three-dimensional vectors. -/
def Independent (first second : Vector K) : Prop :=
  Vector3.cross first second ≠ Vector3.zero

end Purelib.LinearAlgebra.Coordinates3.Vector
