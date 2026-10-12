module

public import Purelib.Data.Fin.Bijection.Cycle
public import Purelib.RootIsolation.Progressive.Chamber.Path.Transport
import Purelib.Data.Fin.Bijection.Iteration
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Nat.Divisibility.Witness
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Progressive.Chamber.Frame
import Purelib.RootIsolation.Progressive.Chamber.Path.Basic

open Purelib

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Progressive.Chamber.Cycle.Divisibility

open Purelib.Data.Gaussian

/-- Once every returning owner lift supplies the finite power-winding
identity, the computed monodromy is forced to be one full degree-cycle. -/
theorem monodromy_isSingleCycle_of_returnWinding
    {frame : Progressive.Chamber.Frame.ChamberFrame}
    (degree : Data.Nat.Positive.RootDegree)
    (degreeEq : frame.degree = degree.value)
    (loop : Progressive.Chamber.Path.Basic.ChamberPath frame frame)
    (returnWinding : ∀ (index : frame.Index) (circuits : Nat),
      0 < circuits →
      Data.Fin.Bijection.iterateForward
          loop.monodromy circuits index = index →
        Data.Nat.Divisibility.Witness.ReturnWindingCertificate degree circuits) :
    Data.Fin.Bijection.IsSingleCycle loop.monodromy := by
  apply
    Data.Fin.Bijection.isSingleCycle_of_noEarlyReturn
  intro index circuits circuitsPositive circuitsSmall returned
  have divides :=
    (returnWinding index circuits circuitsPositive returned).degree_dvd
  rcases divides with ⟨factor, factorization⟩
  have factorPositive : 0 < factor := by
    by_cases factorZero : factor = 0
    · subst factor
      have circuitsZero : circuits = 0 := by
        simpa only [Nat.mul_zero] using factorization
      exact ((Nat.ne_of_gt circuitsPositive) circuitsZero).elim
    · exact Nat.pos_of_ne_zero factorZero
  have degreeLeCircuits : degree.value ≤ circuits := by
    calc
      degree.value ≤ degree.value * factor :=
        Nat.le_mul_of_pos_right degree.value factorPositive
      _ = circuits := factorization.symm
  have circuitsBelowDegree : circuits < degree.value := by
    rw [← degreeEq]
    exact circuitsSmall
  exact (Nat.not_lt_of_ge degreeLeCircuits circuitsBelowDegree).elim
end Purelib.RootIsolation.Progressive.Chamber.Cycle.Divisibility

end
