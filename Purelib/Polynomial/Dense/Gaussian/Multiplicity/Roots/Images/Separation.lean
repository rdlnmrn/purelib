module

public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Images.Factorization
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Readings
public import Purelib.Polynomial.Dense.Derivative.Map
public import Purelib.Data.List.DependentProduct
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original squarefree-factor root separation caches

The original squarefree Bezout certificate gives one mapped right-cofactor
reading at each same retained root. Those readings invert the first jets of
the original factor. Every distinct pair then retains the original indexed
twice-excluded cofactor and its explicit difference inverse.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Images

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Roots (Block)
open Purelib.Polynomial.Dense.Roots
open Purelib.Polynomial.Recurrence.Mode
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic (PositiveContext)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Vector.Basic
open Purelib.Data.List

universe u

variable {K : Type u} [CommRing K] [DecidableEq K]

set_option genInjectivity false in
/-- A diagonal original root pair or its retained indexed explicit difference inverse. -/
inductive Pair (roots : List (Block K)) (leading : K) (inverses : Vec K roots.length)
    (first second : Fin roots.length) where
  /-- The same original bounded root occurrence has no requested difference inverse. -/
  | diagonal (equal : second = first)
  /-- Distinct original occurrences retain the same original twice-excluded cofactor cache. -/
  | separated (different : second ≠ first)
      (cache : Product.DifferenceInverse roots (roots.get first).point second (some ⟨first, different⟩)
        leading (inverses first))

constructive_injectivity Pair

namespace Pair

/-- Read the retained inverse scalar, with zero on the certified original diagonal. -/
@[expose] def inverse {roots : List (Block K)} {leading : K} {inverses : Vec K roots.length}
    {first second : Fin roots.length} (pair : Pair roots leading inverses first second) : K :=
  match pair with
  | .diagonal _ => 0
  | .separated _ cache => cache.inverse.val

omit [DecidableEq K] in
/-- Every distinct original pair reads the same certified difference unit. -/
theorem unit {roots : List (Block K)} {leading : K} {inverses : Vec K roots.length}
    {first second : Fin roots.length} (pair : Pair roots leading inverses first second) (different : second ≠ first) :
    ((roots.get first).point - (roots.get second).point) * pair.inverse = 1 := by
  cases pair with
  | diagonal equal => exact (different equal).elim
  | separated _ cache => exact cache.inverse.property

end Pair

/-- The original dependent product of actual caches at both original bounded root occurrences. -/
abbrev Pairs (roots : List (Block K)) (leading : K) (inverses : Vec K roots.length) :=
  DependentProduct roots fun first => DependentProduct roots fun second => Pair roots leading inverses first second

namespace Pairs

/-- Store the actual indexed cofactor once per distinct pair using the same retained first-jet inverse. -/
@[expose] def prepare (roots : List (Block K))
    (simple : ∀ index : Fin roots.length, (roots.get index).multiplicity = 1)
    (leading : K) (inverses : Vec K roots.length)
    (units : ∀ index : Fin roots.length,
      (leading * coefficientRow (Roots.product roots).coeffs (roots.get index).point 1 0) * inverses index = 1) :
    Pairs roots leading inverses :=
  DependentProduct.ofFn roots fun first =>
    DependentProduct.ofFn roots fun second =>
      if equal : second = first then .diagonal equal
      else .separated equal (Product.DifferenceInverse.ofFirstJetUnit roots simple first second equal leading
        (inverses first) (units first))

/-- Read the same stored root-pair cache without repeating a cofactor product. -/
@[expose] def get {roots : List (Block K)} {leading : K} {inverses : Vec K roots.length}
    (pairs : Pairs roots leading inverses) (first second : Fin roots.length) :
    Pair roots leading inverses first second :=
  DependentProduct.get roots (DependentProduct.get roots pairs first) second

end Pairs

variable {entries : List PositiveEntry} {contexts : List (PositiveContext entries)}
variable {indices : List (Fin contexts.length)} {K : Type u} {ring : CommRing K} {equality : DecidableEq K}
variable {function : Canonical → K}

set_option genInjectivity false in
/-- Actual original first-jet units and pairwise differences for one same cached final factor-root list. -/
structure FirstJets (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (position : Fin indices.length) where
  /-- The same original factor's leading scalar in the common final algebra. -/
  leading : stages.Scalar
  /-- The leading cache maps the same original factor coefficient. -/
  leading_eq : leading = coefficientMap stages (factor contexts (indices.get position)).leadingCoeff
  /-- The original squarefree certificate's once-mapped right cofactor and actual readings. -/
  readings : Coprime.Readings (contexts.get (indices.get position)).focus.part.squarefree
    (coefficientMap stages) (rootsAt stages images position)
    (fun index => ((rootsAt stages images position).get index).point)
  /-- Each reading inverts the same original scaled first-jet value. -/
  units : ∀ index : Fin (rootsAt stages images position).length,
    (leading * coefficientRow (Roots.product (rootsAt stages images position)).coeffs
      ((rootsAt stages images position).get index).point 1 0) * readings.inverses index = 1
  /-- Every distinct original pair retains its actual twice-excluded cofactor and inverse. -/
  pairs : Pairs (rootsAt stages images position) leading readings.inverses

constructive_injectivity FirstJets

namespace FirstJets

/-- Build actual derivative and difference-unit caches directly from the original squarefree context certificate.

The retained factor tower supplies root vanishing and literal coefficients.
The original squarefree Bezout right cofactor is mapped once and read once
per root. Each distinct pair then consumes that same root reading; no field
structure, derivative evaluation per pair, or supplied final separation is used.
-/
@[expose] def prepare (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (mapZero : function 0 = 0) (injective : Function.Injective function) (mapOne : function 1 = 1)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (mapNeg : ∀ value, function (-value) = -function value) (position : Fin indices.length) :
    FirstJets stages images position :=
  let roots := rootsAt stages images position
  let context := contexts.get (indices.get position)
  let embedding := coefficientMap stages
  let leading := embedding context.focus.part.polynomial.leadingCoeff
  let readings := Coprime.Readings.prepare context.focus.part.squarefree embedding
    (coefficientMap_zero stages mapZero) (coefficientMap_injective stages injective)
    (coefficientMap_one stages mapOne) (coefficientMap_add stages mapAdd) (coefficientMap_mul stages mapMul)
    roots (fun index => (roots.get index).point)
    (rootsAt_vanishes stages images mapZero injective mapOne mapAdd mapMul mapNeg position)
  have units : ∀ index : Fin roots.length,
      (leading * coefficientRow (Roots.product roots).coeffs (roots.get index).point 1 0) *
        readings.inverses index = 1 := by
    intro index
    have retained := readings.unit index
    have derivative := Derivative.Map.firstJet embedding (coefficientMap_zero stages mapZero)
      (coefficientMap_injective stages injective) (coefficientMap_add stages mapAdd)
      context.focus.part.polynomial (roots.get index).point
    change (Dense.Map.map embedding (Derivative.derivative context.focus.part.polynomial)).eval
      (roots.get index).point * readings.inverses index = 1 at retained
    rewrite [derivative] at retained
    have factorization := congrArg
      (fun polynomial : DensePolynomial stages.Scalar => coefficientRow polynomial.coeffs (roots.get index).point 1 0)
      (factorizationAt stages images mapZero injective mapOne mapAdd mapMul mapNeg position)
    rewrite [coefficientRow_normalize, coefficientRow_scale] at factorization
    rewrite [factorization] at retained
    exact retained
  let pairs := Pairs.prepare roots (rootsAt_simple stages images position) leading readings.inverses units
  { leading := leading, leading_eq := rfl, readings := readings, units := units, pairs := pairs }

end FirstJets

/-- The same original bounded roots of two factors index the actual once-computed cross-factor cofactors. -/
abbrev CrossPairs {L : Type*} [CommRing L] [DecidableEq L]
    (firstRoots secondRoots : List (Block L)) (leading : L) (inverses : Vec L firstRoots.length) :=
  DependentProduct firstRoots fun first => DependentProduct secondRoots fun second =>
    Product.DifferenceInverse secondRoots (firstRoots.get first).point second none leading (inverses first)

set_option genInjectivity false in
/-- One original context-pair certificate and all actual same-owner cross-factor difference caches. -/
structure Cross (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (first second : Fin indices.length) where
  /-- The same original Gaussian coprimality certificate for the two focused context factors. -/
  certificate : Coprime.Basic.CoprimeCertificate (factor contexts (indices.get first))
    (factor contexts (indices.get second))
  /-- The same original second factor's leading scalar in the common final algebra. -/
  leading : stages.Scalar
  /-- The retained leading scalar maps the original second factor's coefficient. -/
  leading_eq : leading = coefficientMap stages (factor contexts (indices.get second)).leadingCoeff
  /-- The original pair certificate's once-mapped cofactor and readings at the same first-factor roots. -/
  readings : Coprime.Readings certificate (coefficientMap stages) (rootsAt stages images first)
    (fun index => ((rootsAt stages images first).get index).point)
  /-- Every actual inverse reading inverts the same second-factor scaled simple-root product. -/
  units : ∀ index : Fin (rootsAt stages images first).length,
    (leading * (Roots.product (rootsAt stages images second)).eval
      ((rootsAt stages images first).get index).point) * readings.inverses index = 1
  /-- Every original root pair retains its actual once-computed one-exclusion cofactor and inverse. -/
  pairs : CrossPairs (rootsAt stages images first) (rootsAt stages images second) leading readings.inverses

constructive_injectivity Cross

namespace Cross

/-- Construct every cross-factor root-difference cache from one same original context-pair certificate.

The original Bezout right polynomial is mapped once and evaluated once at
each original first-factor root. Each original second-root occurrence then
reuses that same reading in its retained one-exclusion cofactor calculation.
-/
@[expose] def prepare (stages : Stages contexts indices K ring equality function) (images : Images stages)
    (mapZero : function 0 = 0) (injective : Function.Injective function) (mapOne : function 1 = 1)
    (mapAdd : ∀ left right, function (left + right) = function left + function right)
    (mapMul : ∀ left right, function (left * right) = function left * function right)
    (mapNeg : ∀ value, function (-value) = -function value) (first second : Fin indices.length)
    (certificate : Coprime.Basic.CoprimeCertificate (factor contexts (indices.get first))
      (factor contexts (indices.get second))) : Cross stages images first second :=
  let firstRoots := rootsAt stages images first
  let secondRoots := rootsAt stages images second
  let embedding := coefficientMap stages
  let leading := embedding (factor contexts (indices.get second)).leadingCoeff
  let readings := Coprime.Readings.prepare certificate embedding
    (coefficientMap_zero stages mapZero) (coefficientMap_injective stages injective)
    (coefficientMap_one stages mapOne) (coefficientMap_add stages mapAdd) (coefficientMap_mul stages mapMul)
    firstRoots (fun index => (firstRoots.get index).point)
    (rootsAt_vanishes stages images mapZero injective mapOne mapAdd mapMul mapNeg first)
  have units : ∀ index : Fin firstRoots.length,
      (leading * (Roots.product secondRoots).eval (firstRoots.get index).point) * readings.inverses index = 1 := by
    intro index
    have retained := readings.unit index
    have factorization := congrArg
      (fun polynomial : DensePolynomial stages.Scalar => polynomial.eval (firstRoots.get index).point)
      (factorizationAt stages images mapZero injective mapOne mapAdd mapMul mapNeg second)
    rewrite [DensePolynomial.eval_normalize, DensePolynomial.eval_scale] at factorization
    rewrite [factorization] at retained
    exact retained
  let pairs := DependentProduct.ofFn firstRoots fun firstRoot =>
    DependentProduct.ofFn secondRoots fun secondRoot =>
      Product.DifferenceInverse.ofEvalUnit secondRoots (rootsAt_simple stages images second)
        (firstRoots.get firstRoot).point secondRoot leading (readings.inverses firstRoot) (units firstRoot)
  { certificate := certificate, leading := leading, leading_eq := rfl, readings := readings,
    units := units, pairs := pairs }

/-- Read one same retained original cross-factor inverse cache without repeating any scalar product. -/
@[expose] def get {stages : Stages contexts indices K ring equality function} {images : Images stages}
    {first second : Fin indices.length} (cross : Cross stages images first second)
    (firstRoot : Fin (rootsAt stages images first).length) (secondRoot : Fin (rootsAt stages images second).length) :=
  DependentProduct.get (rootsAt stages images second)
    (DependentProduct.get (rootsAt stages images first) cross.pairs firstRoot) secondRoot

end Cross

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Roots.Stages.Images

end
