module
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.GaussianInt.Basic

public import Purelib.Data.GaussianInt.Embedding
import Mathlib.Order.Basic

@[expose] public section
namespace Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Integral

open Purelib.Data.GaussianInt (toGaussian)

open Purelib in
open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- Read the retained sector representative as an exact Gaussian integer. -/
def sectorInt : Sector → Data.GaussianInt
  | .east => ⟨1, 0⟩
  | .northEast => ⟨1, 1⟩
  | .north => ⟨0, 1⟩
  | .northWest => ⟨-1, 1⟩
  | .west => ⟨-1, 0⟩
  | .southWest => ⟨-1, -1⟩
  | .south => ⟨0, -1⟩
  | .southEast => ⟨1, -1⟩

open Purelib.Data.ComplexContinuedFraction.Encoding in
/-- Embedding the integral sector representative recovers the canonical Gaussian representative. -/
@[simp] theorem toGaussian_sectorInt (sector : Sector) :
    toGaussian (sectorInt sector) = sector.rep := by
  cases sector <;> rfl

end Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Integral
end
