module

public import Purelib.Riemann.RootContinuation.RootPathTransport
public import Purelib.Riemann.Paths.PreparedPathTrace.Lineage
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.RootOwnerFrames

/-! # Exact trace coherence of the same actual transport row

The original row factory equation certifies its retained trace against the
same prepared/lineage factory. The row remains the supplied runtime value;
only proof evidence specializes its original build, without running it.
-/

public section

namespace Purelib.Riemann.RootContinuation.RootPathTransport.TransportRow

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
    {path : ClearPath polynomial ambient start finish}
    {first : OwnerFrame (polynomial.eval start)} {last : OwnerFrame (polynomial.eval finish)} {index : Fin 2}

/-- The given original build equation derives literal coherence of this SAME retained row's actual trace. -/
theorem traced_coherent (within : path.WithinAmbient) (row : TransportRow path first last index)
    (factory : row = TransportRow.build path within first last index) : row.traced.Coherent := by
  cases factory
  exact Paths.PreparedPathTrace.TracedPath.coherent_of_build within _ rfl

end Purelib.Riemann.RootContinuation.RootPathTransport.TransportRow

end
