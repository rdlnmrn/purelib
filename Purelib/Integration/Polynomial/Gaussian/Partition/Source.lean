module
import Purelib.Data.Gaussian.Basic
public import Purelib.Integration.Polynomial.Gaussian.Segment.Basic

section
@[expose] public section

/-!+# Generated, cached polynomial path partitions

The source is a finite ordered list of oriented polynomial segments.  A
partition restricts the polynomial as well as its geometry: the geometric
displacement supplies the Jacobian exactly once.  The constructors cache the
restricted polynomials, their samples and the assembled path model.  The
proof-facing integral is the existing Gaussian integration kernel's integral.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Partition.Source

open Purelib.Integration.Polynomial in
/-- An ordered list of original Gaussian polynomial segments. -/
abbrev PolynomialPath := List
  Gaussian.Segment.Basic.PolynomialSegment

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial in
/-- Sum the exact original polynomial-segment integral samples in retained source order. -/
def sourceSample :
  PolynomialPath → Basic.Canonical
  | [] => 0
  | source :: rest => source.integralSample + sourceSample rest
end Purelib.Integration.Polynomial.Gaussian.Partition.Source

end
