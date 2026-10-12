module
public import Purelib.Data.Gaussian.Constants

public import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Norm.Basic

open Purelib.Data.Gaussian.Basic

@[expose] public section
namespace Purelib.Data.GaussianInt

/-- The displayed Gaussian integer one plus the imaginary unit. -/
def gammaInt : GaussianInt := ⟨1, 1⟩

/-- The natural squared norm of one plus the imaginary unit is two. -/
@[simp] theorem normNat_gammaInt : normNat gammaInt = 2 := rfl

/-- Embedding integral one plus the imaginary unit gives the canonical rational Gaussian
gamma. -/
@[simp] theorem toGaussian_gammaInt :
    toGaussian gammaInt = Canonical.gamma := rfl

end Purelib.Data.GaussianInt
end
