module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Process.Imaginary.Positive.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Signed

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Bounded signed acquisition for Legendre input ratios

Requested-precision inspection always yields one of three mathematical
outcomes. The positive branch feeds the existing guaranteed word evaluators;
negative and near-boundary branches preserve their candidate evidence and
the exact state needed for subsequent work. A negative branch is not a
claim that all fractional transformations are undefined.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate.Near

/-- Near-boundary evidence refutes a lower bound at this margin, not every positive lower bound. The source equality
makes the scope explicit. -/
theorem incompatible_lower {tau :
  Coherent.CoherentNamed} {state : Approximation.Gaussian.Acquisition.State tau} {delta : Fraction.Rational}
    (near : Certificate.Near tau state delta) (certificate : Positive.Basic.PositiveEnclosure tau)
    (source : certificate.state = state.retained.source)
    (large : delta ≤ certificate.lower) : False := by
  let witness := tau.name.process.witness state.retained.source
  have lower : certificate.lower ≤ witness.val.im := by
    apply certificate.inside_lower
    rw [source]
    exact tau.name.process.possible_inside witness.property
  exact (not_lt_of_ge (large.trans lower)) (near.bounds witness.property).2
end Purelib.Approximation.Gaussian.Acquisition.Signed.Certificate.Near

end
