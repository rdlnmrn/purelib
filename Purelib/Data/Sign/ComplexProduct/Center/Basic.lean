module

public import Purelib.Data.Sign.ComplexProduct
import Purelib.Data.Sign.Basic

meta import Purelib.Elab.Deriving.Repr
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained formal factor-center coordinates

Four original factor-coordinate signs determine the conservative real and
imaginary product readings without selecting new scalar representatives.
-/

namespace Purelib.Data.Sign.ComplexProduct.Center.Basic

open _root_.Purelib.Data (Sign)

@[expose] public section

set_option genInjectivity false in
/-- Retain the four formal coordinate signs of two factor centers.

Each factor supplies a real and an imaginary sign. Product-center coordinates are
computed from these exact retained signs by the conservative complex-product choices. -/
structure ProductCenterSigns where
  /-- The retained real sign of the left factor center. -/ factorLeftReal : Sign
  /-- The retained imaginary sign of the left factor center. -/ factorLeftImag : Sign
  /-- The retained real sign of the right factor center. -/ factorRightReal : Sign
  /-- The retained imaginary sign of the right factor center. -/ factorRightImag : Sign
deriving DecidableEq

constructive_injectivity ProductCenterSigns

derive_exposed_repr ProductCenterSigns

end

end Purelib.Data.Sign.ComplexProduct.Center.Basic

namespace Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns

open _root_.Purelib.Data (Sign)
open Purelib.Data.Sign.ComplexProduct.Center.Basic (ProductCenterSigns)

/-- Compute the conservative real sign from the four retained factor-center signs.

The original AC and negated BD signs are combined by the original conservative
sum choice. Every input coordinate sign remains attached to its factor. -/
@[expose] public def productReal (centers : ProductCenterSigns) : Sign :=
  Sign.productRealChoice
    centers.factorLeftReal centers.factorLeftImag
    centers.factorRightReal centers.factorRightImag

/-- Compute the conservative imaginary sign from the retained factor-center signs.

The original AD and BC signs are combined by the same original conservative
sum choice, without selecting a scalar magnitude or new center coordinates. -/
@[expose] public def productImag (centers : ProductCenterSigns) : Sign :=
  Sign.productImagChoice
    centers.factorLeftReal centers.factorLeftImag
    centers.factorRightReal centers.factorRightImag

end Purelib.Data.Sign.ComplexProduct.Center.Basic.ProductCenterSigns
