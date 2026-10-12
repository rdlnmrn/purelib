module
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.List.Map
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Basic
public import Purelib.RationalFunctions.ArgumentPrinciple.CCL.Name
public import Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Index
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Polynomial.Dense.Gaussian.Unit

open Purelib.Approximation.Gaussian

open Purelib

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
public section

/-!
# Productive CCL streams for every polynomial root site

This polynomial-facing facade specializes the finite rational-function
argument principle to `p / 1`.  A nonzero polynomial receives one displayed
site index for every exact root or higher-degree root-approximation track of
its squarefree multiplicity basis.  The attached natural multiplicity records
repeated factors without duplicating a geometric site.

Every site exposes a persistent finite-request CCL cursor.  A request appends
exactly the requested number of raw bits, preserves the preceding prefix, and
contracts its projective sidecar below the requested squared error.  Exact
rational sites, including zero, use an exact progressive name; higher sites
simultaneously refine their nested Paper-I winding box.  No completed root or
actual infinite stream is introduced.
-/

namespace Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Name
namespace NonzeroResult

/-- Productive arithmetic CCL name of one polynomial root site. -/
@[expose] def rootName
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) : Name.Basic.Named :=
  (ArgumentPrinciple.CCL.Basic.NonzeroResult.zeroArithmeticName result) index

/-- Displayed finite list of the productive names of all root sites. -/
@[expose] def rootNames {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
  Multiplicity.CCL.Polynomial.Basic.NonzeroResult p) :
    List Name.Basic.Named :=
  (Multiplicity.CCL.Polynomial.Index.NonzeroResult.rootIndices result).map
    (Multiplicity.CCL.Polynomial.Name.NonzeroResult.rootName result)

/-- The displayed list of root names has exactly one entry for each retained root-site index. -/
@[simp] theorem rootNames_length
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p) :
    (Multiplicity.CCL.Polynomial.Name.NonzeroResult.rootNames result).length =
      (Multiplicity.CCL.Polynomial.Index.NonzeroResult.rootIndices result).length := by
  simp only [Multiplicity.CCL.Polynomial.Name.NonzeroResult.rootNames, Purelib.Data.List.Map.length_map, -eq_self,
    -iff_self]
  rfl

/-- The productive name of every indexed root occurs in the displayed root
name list. -/
theorem rootName_mem
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) :
    (Multiplicity.CCL.Polynomial.Name.NonzeroResult.rootName result) index ∈
      (Multiplicity.CCL.Polynomial.Name.NonzeroResult.rootNames result) :=
  Data.List.Map.mem_map.mpr ⟨index, (Multiplicity.CCL.Polynomial.Index.NonzeroResult.mem_rootIndices result) index, rfl⟩

/-- Every root name returns exactly any requested finite number of raw bits. -/
theorem rootName_productive
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) (count : Nat) :
    ((Multiplicity.CCL.Polynomial.Name.NonzeroResult.rootName result) index).machine.emitted.IsPrefix
        (Data.CCL.Transducer.Machine.Advance.advance
          ((Multiplicity.CCL.Polynomial.Name.NonzeroResult.rootName result) index).machine count).emitted ∧
      (Data.CCL.Transducer.Machine.Advance.advance
        ((Multiplicity.CCL.Polynomial.Name.NonzeroResult.rootName result) index).machine count).emitted.length = count
          :=
  (ArgumentPrinciple.CCL.Basic.NonzeroResult.zeroArithmeticName_productive result) index count

/-- Every finite prefix of a root name has exact ordinary raw-parser semantics
for that same exact site or initial RAT box. -/
theorem rootName_exact
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} (result :
      Multiplicity.CCL.Polynomial.Basic.NonzeroResult p)
    (index : (Multiplicity.CCL.Polynomial.Index.NonzeroResult.RootIndex result)) (count : Nat) :
    let name := (Multiplicity.CCL.Polynomial.Name.NonzeroResult.rootName result) index
    Data.CCL.Transducer.Machine.Semantics.Basic.ExactCursor
      name.process name.state
      (Data.CCL.Transducer.Machine.Advance.advance name.machine count) :=
  (ArgumentPrinciple.CCL.Basic.NonzeroResult.zeroArithmeticName_exact result) index count
end NonzeroResult

end Purelib.RootIsolation.Multiplicity.CCL.Polynomial.Name

end
