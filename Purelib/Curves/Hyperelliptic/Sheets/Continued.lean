module

public import Purelib.Curves.Hyperelliptic.Sheets.Basic
public import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner

/-!
# Original continued-root sheet values

The retained continued point's root certificate supplies the original curve
equation and apartness. Its numerical root is reused directly with the label
of the supplied lifted sheet; no fresh root isolation is performed.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Sheets.Basic.AlgebraicSheetValue

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Polynomial.Approximation.Gaussian.Evaluation

/-- Retain the original continued point's root certificate under its supplied lifted-sheet label. -/
@[expose] def ofContinuedPoint {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus)
    {count : Nat} {patch : ContinuedNeighborhood curve.polynomial count} {point : Canonical}
    (sample : ContinuedNeighborhood.Point patch point) (sheet : Fin 2) : AlgebraicSheetValue curve point :=
  ⟨sample.certificate.value, sample.certificate.apart, sheet,
    sample.certificate.square.trans (Horner.polynomialEval_exact curve.polynomial point).symm⟩

end Purelib.Curves.Hyperelliptic.Sheets.Basic.AlgebraicSheetValue

end
