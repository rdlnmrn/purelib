module

import Purelib.Polynomial.Dense.Gaussian.Roots.Candidates
import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.System.IO

/-! # Exact Gaussian-rational candidate enumeration with nonreal coefficients -/

namespace TestPurelib.Polynomial.GaussianRootCandidates

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Roots
open Purelib.Polynomial.Elimination.Axis

/-- The original polynomial with exact roots one plus i and two minus i. -/
private def polynomial : CoefficientPolynomial := ⟨[1, -3, ⟨3, 1⟩]⟩

/-- The original coefficient-produced coordinate eliminants for that same Gaussian polynomial. -/
private def certificate := Separated.separatedAxisEliminationCertificate polynomial
  (by decide +kernel) (by decide +kernel)

/-- The first exact nonreal root retains its original evaluation certificate. -/
private def first : Certificate.ExactRoot polynomial := ⟨⟨1, 1⟩, by decide +kernel⟩

/-- The second exact nonreal root retains its original evaluation certificate. -/
private def second : Certificate.ExactRoot polynomial := ⟨⟨2, -1⟩, by decide +kernel⟩

/-- The complete Gaussian candidate construction retains the first original nonreal root certificate. -/
example : first ∈ Candidates.exactRoots certificate := Candidates.root_mem_exactRoots certificate first

/-- The same original coordinate certificate also covers the second exact nonreal root. -/
example : second ∈ Candidates.exactRoots certificate := Candidates.root_mem_exactRoots certificate second

/-- The original coordinate polynomial supplies the zero-root edge case. -/
private def zeroPolynomial : CoefficientPolynomial := ⟨[1, 0]⟩

/-- The original coefficient construction supplies both coordinate eliminants for zero. -/
private def zeroCertificate := Separated.separatedAxisEliminationCertificate zeroPolynomial
  (by decide +kernel) (by decide +kernel)

/-- Execute exact nonreal roots, rejected crossed coordinates, retained finite bounds and the separately tested zero.

The two original coefficient-produced axis certificates are each retained
once. Candidate outputs are checked directly without a successful comparison
premise or root isolation. Duplicate successful occurrences remain permitted;
the candidate list does not represent source multiplicities.
-/
public def check : IO Unit := do
  let roots := Candidates.exactRoots certificate
  let points := roots.map Certificate.ExactRoot.point
  unless first.point ∈ points ∧ second.point ∈ points do
    throw (IO.userError "exact Gaussian enumeration lost an original nonreal coefficient root")
  unless points.all (fun point => decide (point = first.point ∨ point = second.point)) do
    throw (IO.userError "exact Gaussian enumeration retained a false crossed-coordinate candidate")
  unless roots.length ≤ Candidates.searchSize certificate do
    throw (IO.userError "exact Gaussian enumeration exceeded its original coordinate-search bound")
  for root in roots do
    unless polynomial.eval root.point = 0 do
      throw (IO.userError "an emitted exact root lost its original numerical evaluation")
  let zeroRoots := Candidates.exactRoots zeroCertificate
  unless zeroRoots.map Certificate.ExactRoot.point = [0] do
    throw (IO.userError "exact Gaussian enumeration lost the separately tested original zero root")
  Purelib.System.IO.println "exact Gaussian coordinate candidates: nonreal roots, rejection, bounds and zero PASS"

end TestPurelib.Polynomial.GaussianRootCandidates
