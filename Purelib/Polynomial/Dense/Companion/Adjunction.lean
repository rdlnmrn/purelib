module

public import Purelib.Polynomial.Dense.Companion.Algebra
public import Purelib.Polynomial.Dense.Division.Synthetic.Factorization
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Cached exact root adjunction and coefficient stripping

An original companion supplies its finite cyclic coefficient algebra and an
exact root. The root, mapped original coefficients, original synthetic
division and literal linear-factor product are each materialized once and
retained together with their exact readbacks. No field instance is assigned
to the resulting algebra.
-/

public section

namespace Purelib.Polynomial.Dense.Companion

open Basic (DensePolynomial)
open Purelib.Algebra.Monogenic
open Purelib.LinearAlgebra.Matrix
open Division

variable {K : Type*} [CommRing K] [DecidableEq K]
variable {polynomial : DensePolynomial K}

namespace Adjunction

/-- The original cyclic table type indexed by the same retained companion matrix. -/
abbrev Table (companion : Companion polynomial) := Cyclic (Rectangular.transpose companion.matrix)

/-- The exact original matrix algebra supplied by a retained companion's cyclic table. -/
abbrev Scalar (companion : Companion polynomial) (table : Table companion) := Cyclic.Element table

/-- The original dense coefficient representation over that same retained matrix algebra. -/
abbrev Coefficients (companion : Companion polynomial) (table : Table companion) :=
  DensePolynomial (Scalar companion table)

end Adjunction

set_option genInjectivity false in
/-- A cached exact root adjunction and one certified stripping step for the original polynomial.

All executable payloads retain their original owners. The same root and
mapped source feed the original synthetic division once; its actual quotient
supplies the cached product, which equals the original normalized source.
-/
structure Adjunction (polynomial : DensePolynomial K) where
  /-- The actual original coefficient companion. -/
  companion : Companion polynomial
  /-- The materialized successive-power cyclic table. -/
  table : Adjunction.Table companion
  /-- The table was computed from that same original companion. -/
  table_eq : table = companion.cyclic
  /-- The retained actual algebra generator. -/
  root : Adjunction.Scalar companion table
  /-- The retained generator is the root of this same original cyclic algebra. -/
  root_eq : root = Cyclic.Element.root table
  /-- The original source coefficient table mapped into this same retained algebra. -/
  source : Adjunction.Coefficients companion table
  /-- Every source coefficient uses the original scalar embedding. -/
  source_eq : source = Map.map (Cyclic.Element.scalar table) polynomial
  /-- The single retained original synthetic division at the retained exact root. -/
  division : Synthetic.Result source root
  /-- The division is the actual output of the original public constructor. -/
  division_eq : division = Synthetic.divide source root
  /-- The retained exact source root gives a zero original Horner remainder. -/
  remainder_zero : division.remainder = 0
  /-- The retained original coefficient product of the linear factor and actual quotient. -/
  product : Adjunction.Coefficients companion table
  /-- The product consumes the same cached root and quotient. -/
  product_eq : product = (⟨[1, -root]⟩ : Adjunction.Coefficients companion table) * division.quotient
  /-- The original mapped source has this literal coefficient factorization. -/
  factorization : source.normalize = product

constructive_injectivity Adjunction

/-- Materialize the original companion's exact root algebra and one original synthetic stripping step. -/
@[expose] def adjoin (companion : Companion polynomial) : Adjunction polynomial :=
  let table := companion.cyclic
  let root := Cyclic.Element.root table
  let source := Map.map (Cyclic.Element.scalar table) polynomial
  let division := Synthetic.divide source root
  let product := (⟨[1, -root]⟩ : Adjunction.Coefficients companion table) * division.quotient
  have vanishes : source.eval root = 0 := companion.root_relation
  { companion := companion
    table := table
    table_eq := rfl
    root := root
    root_eq := rfl
    source := source
    source_eq := rfl
    division := division
    division_eq := rfl
    remainder_zero := division.remainder_eval.trans vanishes
    product := product
    product_eq := rfl
    factorization := Synthetic.factorization_of_root source root vanishes }

namespace Adjunction

/-- The retained root is an exact root of the retained original coefficient table. -/
theorem root_vanishes (adjunction : Adjunction polynomial) : adjunction.source.eval adjunction.root = 0 :=
  adjunction.division.remainder_eval.symm.trans adjunction.remainder_zero

/-- Mapping into the retained root algebra preserves the original natural degree. -/
theorem source_degree (adjunction : Adjunction polynomial) : adjunction.source.natDegree = polynomial.natDegree := by
  rewrite [adjunction.source_eq]
  exact Map.map_natDegree (Cyclic.Element.scalar adjunction.table)
    (Cyclic.Element.scalar_zero adjunction.table)
    (fun _ _ same => Cyclic.Element.scalar_injective adjunction.table same) polynomial

/-- Mapping a normalized original source retains that same normalization. -/
theorem source_normalized (adjunction : Adjunction polynomial) (normalized : polynomial.normalize = polynomial) :
    adjunction.source.normalize = adjunction.source := by
  rewrite [adjunction.source_eq,
    ← Map.map_normalize (Cyclic.Element.scalar adjunction.table) (Cyclic.Element.scalar_zero adjunction.table)
      (fun _ _ same => Cyclic.Element.scalar_injective adjunction.table same)]
  exact congrArg (Map.map (Cyclic.Element.scalar adjunction.table)) normalized

/-- The mapped source retains the image of its original leading coefficient. -/
theorem source_leadingCoeff (adjunction : Adjunction polynomial) :
    adjunction.source.leadingCoeff = Cyclic.Element.scalar adjunction.table polynomial.leadingCoeff := by
  rewrite [adjunction.source_eq]
  exact Map.map_leadingCoeff (Cyclic.Element.scalar adjunction.table) (Cyclic.Element.scalar_zero adjunction.table)
    (fun _ _ same => Cyclic.Element.scalar_injective adjunction.table same) polynomial

/-- The retained mapped source has the same positive original natural degree. -/
theorem source_positive (adjunction : Adjunction polynomial) : 0 < adjunction.source.natDegree := by
  rewrite [adjunction.source_degree]
  exact adjunction.companion.positive

/-- Injectivity of the original scalar map preserves the nonzero original leading coefficient. -/
theorem source_leading_nonzero (adjunction : Adjunction polynomial) : adjunction.source.leadingCoeff ≠ 0 := by
  intro zero
  have equal : Cyclic.Element.scalar adjunction.table polynomial.leadingCoeff =
      Cyclic.Element.scalar adjunction.table 0 :=
    adjunction.source_leadingCoeff.symm.trans (zero.trans (Cyclic.Element.scalar_zero adjunction.table).symm)
  exact adjunction.companion.leading_nonzero (Cyclic.Element.scalar_injective adjunction.table equal)

/-- The same actual quotient is normalized when the original source is normalized. -/
theorem quotient_normalized (adjunction : Adjunction polynomial) (normalized : polynomial.normalize = polynomial) :
    adjunction.division.quotient.normalize = adjunction.division.quotient :=
  adjunction.division.quotient_normalized (adjunction.source_normalized normalized)
    adjunction.source_positive adjunction.source_leading_nonzero

/-- The actual stripping step lowers the original natural degree by exactly one. -/
theorem quotient_degree (adjunction : Adjunction polynomial) (normalized : polynomial.normalize = polynomial) :
    adjunction.division.quotient.natDegree + 1 = polynomial.natDegree :=
  (adjunction.division.quotient_degree (adjunction.source_normalized normalized)
    adjunction.source_positive adjunction.source_leading_nonzero).trans adjunction.source_degree

/-- The actual quotient retains the scalar image of the original leading coefficient. -/
theorem quotient_leadingCoeff (adjunction : Adjunction polynomial) (normalized : polynomial.normalize = polynomial) :
    adjunction.division.quotient.leadingCoeff = Cyclic.Element.scalar adjunction.table polynomial.leadingCoeff :=
  (adjunction.division.quotient_leadingCoeff (adjunction.source_normalized normalized)
    adjunction.source_positive adjunction.source_leading_nonzero).trans adjunction.source_leadingCoeff

/-- The same cached original leading inverse remains a leading inverse of the actual quotient. -/
theorem quotient_unit (adjunction : Adjunction polynomial) (normalized : polynomial.normalize = polynomial) :
    adjunction.division.quotient.leadingCoeff *
      Cyclic.Element.scalar adjunction.table adjunction.companion.leadingInverse = 1 := by
  rewrite [adjunction.quotient_leadingCoeff normalized, ← Cyclic.Element.scalar_mul,
    adjunction.companion.leading_unit, Cyclic.Element.scalar_one]
  rfl

end Adjunction

end Purelib.Polynomial.Dense.Companion

end
