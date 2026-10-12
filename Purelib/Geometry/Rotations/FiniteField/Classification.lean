module

public import Purelib.Geometry.Rotations.Cayley.FieldRealizations
import Purelib.Data.List.Filter
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Append
import Purelib.Data.Bool.Decide
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Nat.Multiplication
import Purelib.Data.Nat.Division
import Purelib.Geometry.Rotations.Reflection
import Purelib.Data.List.Nodup
import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
import Purelib.Geometry.Rotations.Cayley.Cap
public import Purelib.Algebra.Quaternion.Projective.UnitObstruction
public import Purelib.Algebra.Field.Finite.Odd.SquareClassRepresentatives
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Geometry.Rotations.Basic
import Purelib.Data.List.Bijection
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Finite.Odd.Presentation
import Purelib.Algebra.Field.Finite.Odd.SquareClasses
import Purelib.Algebra.Field.SquareClass.Basic
import Purelib.Algebra.Field.SumsOfSquares.Four
import Purelib.Algebra.Quadratic.Pair.Coordinates
import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.Algebra.Quaternion.Projective.SquareClass
import Purelib.Data.List.CountWhere
import Purelib.Data.List.FilterMap
import Purelib.Data.List.Map
public import Purelib.Geometry.Projective.Quaternion.Finite.Counts
import Purelib.Geometry.Projective.Quaternion.Finite.Enumeration
import Purelib.Geometry.Quadratic.Finite.NullDirections
import Purelib.Geometry.Rotations.Axis.Recovery
import Purelib.Geometry.Rotations.Cayley.Charts
import Purelib.Geometry.Rotations.Projective.Action
import Purelib.Geometry.Rotations.Projective.Correspondence
import Purelib.Geometry.Rotations.Projective.SquareClass
import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Geometry.Quadratic.Finite.Fibers
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

section
public section

/-!
# Certified rotation and projective occurrence counts

The displayed odd-field presentation retains its original finite scalar and
vector enumerations. Boolean filters and explicit bijections count canonical
projective representatives and the corresponding rotation strata.
-/

namespace Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

open Purelib
open Purelib.Algebra.Field
open Purelib.Algebra.Field.Finite.Odd
open Purelib.Algebra.Field.Finite.Odd.Presentation
open Purelib.Algebra.Field.Finite.Odd.SquareClasses
open Purelib.Algebra.Field.SquareClass.Basic
open Purelib.Algebra.Field.SumsOfSquares
open Purelib.Algebra.Field.SumsOfSquares.Four
open Purelib.Algebra.Quadratic.Pair
open Purelib.Algebra.Quaternion
open Purelib.Algebra.Quaternion.Projective.Basic
open Purelib.Algebra.Quaternion.Projective.SquareClass
open Purelib.Algebra.Quaternion.Projective.UnitObstruction.NonNullProportion
open Purelib.Data.List
open Purelib.Data.List.Bijection
open Purelib.Geometry
open Purelib.Geometry.Rotations
open Purelib.Geometry.Rotations.Axis
open Purelib.Geometry.Rotations.Basic
open Purelib.Geometry.Rotations.Cayley
open Purelib.Geometry.Rotations.Projective.Action
open Purelib.Geometry.Rotations.Projective.Correspondence
open Purelib.Geometry.Rotations.Projective.SquareClass
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3

open Purelib.Data.List

variable {K : Type*} [ExplicitField K]

section

variable (presentation : Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K)

/-- The corresponding computed rotation list. Its duplicate-freeness and completeness are inherited from the canonical
projective list and the inverse theorem, rather than checked by matrix equality. -/
@[expose] public def rotations : List (Rotations.Basic.Rotation K) :=
  presentation.nonNullProjectiveRepresentatives.map
    NonNullProportion.rotation

/-- Mapping a function injective on the actual list preserves duplicate-freeness. -/
private theorem nodup_map_of_injective_on
    {Alpha Beta : Type*} {values : List Alpha} (function : Alpha → Beta)
    (injectiveOn : ∀ left ∈ values, ∀ right ∈ values,
      function left = function right → left = right)
    (valuesNodup : values.Nodup) : (values.map function).Nodup := by
  induction values with
  | nil => exact List.Pairwise.nil
  | cons head tail inductionHypothesis =>
      rw [List.map_cons]
      apply List.pairwise_cons.mpr
      constructor
      · intro mapped mappedMember equal
        rcases Map.mem_map.mp mappedMember with
          ⟨source, sourceMember, sourceEqual⟩
        apply (List.pairwise_cons.mp valuesNodup).1 source sourceMember
        apply injectiveOn head List.mem_cons_self source
          (List.mem_cons_of_mem head sourceMember)
        exact equal.trans sourceEqual.symm
      · apply inductionHypothesis
        · intro left leftMember right rightMember equal
          exact injectiveOn left (List.mem_cons_of_mem head leftMember)
            right (List.mem_cons_of_mem head rightMember) equal
        · exact (List.pairwise_cons.mp valuesNodup).2

/-- Canonical non-null proportions representing the same rotation are equal. -/
private theorem rotation_injective_on_canonical
    {left right : Projective.Basic.NonNullProportion K}
    (leftMember : left ∈ presentation.nonNullProjectiveRepresentatives)
    (rightMember : right ∈ presentation.nonNullProjectiveRepresentatives)
    (equal : (NonNullProportion.rotation left) = (NonNullProportion.rotation right)) : left = right := by
  letI : DecidableEq K := presentation.eqDecidable
  have matrixEqual : (NonNullProportion.rotationMatrix left) = (NonNullProportion.rotationMatrix right) :=
    congrArg Rotation.matrix equal
  have equivalent := NonNullProportion.equivalent_of_rotationMatrix_eq
    left right presentation.twoNonzero matrixEqual
  have rawEqual := presentation.projective_eq_of_equivalent
    (presentation.raw_mem_of_nonNull_mem leftMember)
    (presentation.raw_mem_of_nonNull_mem rightMember) equivalent
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar rawEqual
  · exact congrArg Proportion.vector rawEqual

/-- The canonical rotation enumeration has no duplicates. -/
theorem rotations_nodup : presentation.rotations.Nodup := by
  unfold rotations
  apply nodup_map_of_injective_on
    NonNullProportion.rotation
  · intro left leftMember right rightMember equal
    exact presentation.rotation_injective_on_canonical leftMember rightMember
      equal
  · exact presentation.nonNullProjectiveRepresentatives_nodup

/-- Every stored rotation occurs in the explicit canonical projective list. The witness is the normalized executable
inverse from Theorem 58. -/
theorem rotations_complete (rotation : Rotations.Basic.Rotation K) :
    rotation ∈ presentation.rotations := by
  letI : DecidableEq K := presentation.eqDecidable
  let source := RotationProportion.ofRotation rotation presentation.twoNonzero
  let normalized := (presentation.canonicalize source).representative
  apply Map.mem_map.mpr
  refine ⟨normalized, presentation.canonicalize_mem source, ?_⟩
  apply (fun {K : Type _} [ExplicitField K] {left right :
    Purelib.Geometry.Rotations.Basic.Rotation K} (equal : left.matrix = right.matrix) =>
    (Purelib.Geometry.Rotations.Basic.Rotation.eq_of_matrix_eq (K := K) (left := left) (right := right) equal : left =
    right))
  change (NonNullProportion.rotationMatrix normalized) = rotation.matrix
  calc
    (NonNullProportion.rotationMatrix normalized) = (NonNullProportion.rotationMatrix source) :=
      (NonNullProportion.rotationMatrix_respects_equivalent
        (presentation.canonicalize source).equivalent).symm
    _ = rotation.matrix :=
      RotationProportion.ofRotation_rotationMatrix rotation
        presentation.twoNonzero

set_option genInjectivity false in
/-- A complete duplicate-free executable carrier of finite-field rotations. -/
structure RotationEnumeration where
  /-- The retained finite list of rotations. -/ values : List (Rotations.Basic.Rotation K)
  /-- The rotation list contains no duplicates. -/ nodup : values.Nodup
  /-- Every rotation belongs to the retained list. -/ complete : ∀ rotation : Rotations.Basic.Rotation K, rotation ∈
    values

constructive_injectivity RotationEnumeration

/-- The canonical four-chart rotation enumeration packaged with both finite carrier certificates. -/
@[expose] public def rotationEnumeration :
  RotationEnumeration (K := K) where
  values := presentation.rotations
  nodup := presentation.rotations_nodup
  complete := presentation.rotations_complete

/-- The matrices underlying the canonical rotation carrier. Keeping this list separately makes matrix-level finite
searches executable without recomputing the projective rotation map. -/
@[expose] public def rotationMatrices : List (Coordinates3.Matrix3 K) :=
  presentation.rotations.map Rotation.matrix

/-- The retained list of rotation matrices has no duplicates. -/
theorem rotationMatrices_nodup : presentation.rotationMatrices.Nodup := by
  unfold rotationMatrices
  apply nodup_map_of_injective_on Rotation.matrix
  · intro left _ right _ matrixEqual
    exact (fun {K : Type _} [ExplicitField K] {left right :
      Purelib.Geometry.Rotations.Basic.Rotation K} (equal : left.matrix = right.matrix) =>
      (Purelib.Geometry.Rotations.Basic.Rotation.eq_of_matrix_eq (K := K) (left := left) (right := right) equal : left =
      right)) matrixEqual
  · exact presentation.rotations_nodup

/-- Every displayed rotation matrix belongs to the matrix enumeration. -/
theorem rotationMatrices_complete (rotation : Rotations.Basic.Rotation K) :
    rotation.matrix ∈ presentation.rotationMatrices := by
  unfold rotationMatrices
  exact Map.mem_map.mpr
    ⟨rotation, presentation.rotations_complete rotation, rfl⟩

set_option genInjectivity false in
/-- Complete duplicate-free executable carrier of the matrices representing finite-field rotations. -/
structure RotationMatrixEnumeration where
  /-- The retained finite list of rotation matrices. -/ values : List (Coordinates3.Matrix3 K)
  /-- The matrix list contains no duplicates. -/ nodup : values.Nodup
  /-- Every rotation's matrix appears in the retained list. -/ realizes : ∀ rotation : Rotations.Basic.Rotation K,
    rotation.matrix ∈ values

constructive_injectivity RotationMatrixEnumeration

/-- Package the canonical matrix list with its uniqueness and completeness certificates. -/
@[expose] public def rotationMatrixEnumeration :
  RotationMatrixEnumeration (K := K) where
  values := presentation.rotationMatrices
  nodup := presentation.rotationMatrices_nodup
  realizes := presentation.rotationMatrices_complete

/-- Executable inverse from a finite-field rotation to its unique canonical four-chart projective representative. -/
@[expose] public def canonicalRotationRepresentative (rotation : Rotations.Basic.Rotation K) :
    Projective.Basic.NonNullProportion K := by
  letI : DecidableEq K := presentation.eqDecidable
  exact (presentation.canonicalize
    (RotationProportion.ofRotation rotation
      presentation.twoNonzero)).representative

/-- The recovered rotation representative belongs to the canonical projective carrier. -/
theorem canonicalRotationRepresentative_mem (rotation : Rotations.Basic.Rotation K) :
    presentation.canonicalRotationRepresentative rotation ∈
      presentation.nonNullProjectiveRepresentatives := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.canonicalize_mem
    (RotationProportion.ofRotation rotation presentation.twoNonzero)

/-- The recovered canonical proportion represents the original rotation. -/
theorem canonicalRotationRepresentative_rotation (rotation : Rotations.Basic.Rotation K) :
    (NonNullProportion.rotation (presentation.canonicalRotationRepresentative rotation)) =
      rotation := by
  letI : DecidableEq K := presentation.eqDecidable
  apply (fun {K : Type _} [ExplicitField K] {left right :
    Purelib.Geometry.Rotations.Basic.Rotation K} (equal : left.matrix = right.matrix) =>
    (Purelib.Geometry.Rotations.Basic.Rotation.eq_of_matrix_eq (K := K) (left := left) (right := right) equal : left =
    right))
  let source := RotationProportion.ofRotation rotation presentation.twoNonzero
  change (NonNullProportion.rotationMatrix (presentation.canonicalize source).representative) =
    rotation.matrix
  calc
    (NonNullProportion.rotationMatrix (presentation.canonicalize source).representative) =
        (NonNullProportion.rotationMatrix source) :=
      (NonNullProportion.rotationMatrix_respects_equivalent
        (presentation.canonicalize source).equivalent).symm
    _ = rotation.matrix :=
      RotationProportion.ofRotation_rotationMatrix rotation
        presentation.twoNonzero

/-- The projective rotation theorem as an explicit finite-list bijection on the canonical representatives used for
counting. -/
@[expose] public def projectiveRotationBijection : Bijection.ListBijection
    presentation.nonNullProjectiveRepresentatives presentation.rotations where
  forward := NonNullProportion.rotation
  backward := presentation.canonicalRotationRepresentative
  forward_mem := by
    intro proportion member
    unfold rotations
    exact Map.mem_map.mpr ⟨proportion, member, rfl⟩
  backward_mem := fun rotation _ =>
    presentation.canonicalRotationRepresentative_mem rotation
  backward_forward := by
    intro proportion member
    apply presentation.rotation_injective_on_canonical
      (presentation.canonicalRotationRepresentative_mem (NonNullProportion.rotation proportion))
      member
    exact presentation.canonicalRotationRepresentative_rotation
      (NonNullProportion.rotation proportion)
  forward_backward := by
    intro rotation _
    exact presentation.canonicalRotationRepresentative_rotation rotation

/-- The projective half-spread fiber, evaluated by the homogeneous closed formula `Q(v)/N(x,v)`. -/
@[expose] public def halfSpreadFiber (value : K) : List (Projective.Basic.NonNullProportion K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.nonNullProjectiveRepresentatives.filter fun proportion =>
    proportion.vector.quadrance / proportion.toProportion.norm = value

/-- The affine quadric `Q(v) = value`, retained in normalized projective coordinates so every point also caches the
non-null norm certificate needed by the rotation map. This is constructed independently of half spread by filtering the
displayed four-chart carrier. -/
@[expose] public def affineQuadricRawRepresentatives (value : K) : List (Projective.Basic.Proportion K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.projectiveRepresentatives.filter fun raw =>
    raw.scalar = 1 ∧ raw.vector.quadrance = value

/-- Certify the non-null members of the independently filtered affine quadric.

The representatives have scalar coordinate one and the prescribed vector quadrance. -/
@[expose] public def affineQuadricRepresentatives (value : K) :
    List (Projective.Basic.NonNullProportion K) :=
  (presentation.affineQuadricRawRepresentatives value).filterMap
    presentation.certifyNonNull

/-- Canonical projective axis representatives: the displayed projective plane at infinity, before removing its null
conic. -/
@[expose] public def projectiveAxisRawRepresentatives : List (Projective.Basic.Proportion K) := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.projectiveRepresentatives.filter fun raw =>
    raw.scalar = 0

/-- The non-null projective-axis quadric complement parametrizing half turns. The construction is independent of the
half-spread fiber predicate. -/
@[expose] public def projectiveNonNullAxisRepresentatives :
    List (Projective.Basic.NonNullProportion K) :=
  presentation.projectiveAxisRawRepresentatives.filterMap
    presentation.certifyNonNull

/-- Each filtered half-spread fiber has no duplicate representatives. -/
theorem halfSpreadFiber_nodup (value : K) :
    (presentation.halfSpreadFiber value).Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold halfSpreadFiber
  exact Filter.pairwise_filter _
    presentation.nonNullProjectiveRepresentatives_nodup

/-- The raw affine quadric filter has no duplicates. -/
theorem affineQuadricRawRepresentatives_nodup (value : K) :
    (presentation.affineQuadricRawRepresentatives value).Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold affineQuadricRawRepresentatives
  exact Filter.pairwise_filter _ presentation.projectiveRepresentatives_nodup

/-- Certifying the affine quadric retains duplicate-freeness. -/
theorem affineQuadricRepresentatives_nodup (value : K) :
    (presentation.affineQuadricRepresentatives value).Nodup := by
  unfold affineQuadricRepresentatives
  exact FiniteOddFieldPresentation.certifyNonNull_filterMap_nodup (presentation := presentation)
    (presentation.affineQuadricRawRepresentatives value)
    (presentation.affineQuadricRawRepresentatives_nodup value)

/-- The raw projective-axis filter has no duplicates. -/
theorem projectiveAxisRawRepresentatives_nodup :
    presentation.projectiveAxisRawRepresentatives.Nodup := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold projectiveAxisRawRepresentatives
  exact Filter.pairwise_filter _ presentation.projectiveRepresentatives_nodup

/-- The certified non-null projective axes have no duplicates. -/
theorem projectiveNonNullAxisRepresentatives_nodup :
    presentation.projectiveNonNullAxisRepresentatives.Nodup := by
  unfold projectiveNonNullAxisRepresentatives
  exact FiniteOddFieldPresentation.certifyNonNull_filterMap_nodup (presentation := presentation)
    presentation.projectiveAxisRawRepresentatives
    presentation.projectiveAxisRawRepresentatives_nodup

/-- Affine quadric membership means canonical membership, scalar one and the specified vector quadrance. -/
theorem mem_affineQuadricRepresentatives_iff
    (value : K) (proportion : Projective.Basic.NonNullProportion K) :
    proportion ∈ presentation.affineQuadricRepresentatives value ↔
      proportion ∈ presentation.nonNullProjectiveRepresentatives ∧
        proportion.scalar = 1 ∧
          proportion.vector.quadrance = value := by
  letI : DecidableEq K := presentation.eqDecidable
  constructor
  · intro member
    unfold affineQuadricRepresentatives at member
    rcases FilterMap.mem_filterMap.mp member with
      ⟨raw, rawMember, certified⟩
    have filtered := Filter.mem_filter.mp rawMember
    have rawEqual :=
      (FiniteOddFieldPresentation.certifyNonNull_eq_some_toProportion presentation) certified
    constructor
    · unfold FiniteOddFieldPresentation.nonNullProjectiveRepresentatives
      exact FilterMap.mem_filterMap.mpr
        ⟨raw, filtered.1, certified⟩
    · rw [rawEqual]
      exact of_decide_eq_true filtered.2
  · rintro ⟨projectiveMember, scalarOne, quadranceValue⟩
    unfold affineQuadricRepresentatives
    apply FilterMap.mem_filterMap.mpr
    refine ⟨proportion.toProportion, ?_,
      presentation.certifyNonNull_self proportion⟩
    apply Filter.mem_filter.mpr
    exact ⟨presentation.raw_mem_of_nonNull_mem projectiveMember,
      decide_eq_true ⟨scalarOne, quadranceValue⟩⟩

/-- Non-null projective-axis membership means canonical membership with scalar zero. -/
theorem mem_projectiveNonNullAxisRepresentatives_iff
    (proportion : Projective.Basic.NonNullProportion K) :
    proportion ∈ presentation.projectiveNonNullAxisRepresentatives ↔
      proportion ∈ presentation.nonNullProjectiveRepresentatives ∧
        proportion.scalar = 0 := by
  letI : DecidableEq K := presentation.eqDecidable
  constructor
  · intro member
    unfold projectiveNonNullAxisRepresentatives at member
    rcases FilterMap.mem_filterMap.mp member with
      ⟨raw, rawMember, certified⟩
    have filtered := Filter.mem_filter.mp rawMember
    have rawEqual :=
      (FiniteOddFieldPresentation.certifyNonNull_eq_some_toProportion presentation) certified
    constructor
    · unfold FiniteOddFieldPresentation.nonNullProjectiveRepresentatives
      exact FilterMap.mem_filterMap.mpr
        ⟨raw, filtered.1, certified⟩
    · rw [rawEqual]
      exact of_decide_eq_true filtered.2
  · rintro ⟨projectiveMember, scalarZero⟩
    unfold projectiveNonNullAxisRepresentatives
    apply FilterMap.mem_filterMap.mpr
    refine ⟨proportion.toProportion, ?_,
      presentation.certifyNonNull_self proportion⟩
    apply Filter.mem_filter.mpr
    exact ⟨presentation.raw_mem_of_nonNull_mem projectiveMember,
      decide_eq_true scalarZero⟩

/-- Canonical representatives whose four-square norm has square class one. This is the executable kernel list for the
map `chi`. -/
@[expose] public def quadranceClassKernel : List (Projective.Basic.NonNullProportion K) := by
  exact presentation.nonNullProjectiveRepresentatives.filter fun proportion =>
    (FiniteOddFieldPresentation.isSquare presentation) proportion.toProportion.norm

/-- The other quadrance-class fiber in the canonical projective carrier. -/
@[expose] public def quadranceClassNontrivialFiber : List (Projective.Basic.NonNullProportion K) :=
  presentation.nonNullProjectiveRepresentatives.filter fun proportion =>
    !(FiniteOddFieldPresentation.isSquare presentation) proportion.toProportion.norm

/-- On the canonical finite rotation carrier, the executable square-norm filter is exactly the unit-quaternion kernel
predicate. -/
theorem mem_quadranceClassKernel_iff_hasUnitRepresentative
    (proportion : Projective.Basic.NonNullProportion K) :
    proportion ∈ presentation.quadranceClassKernel ↔
      proportion ∈ presentation.nonNullProjectiveRepresentatives ∧
        (QuaternionObstruction.HasUnitRepresentative proportion) := by
  letI : DecidableEq K := presentation.eqDecidable
  constructor
  · intro member
    have filtered := Filter.mem_filter.mp member
    have squareMember : proportion.toProportion.norm ∈
        presentation.squareValues := by
      unfold FiniteOddFieldPresentation.isSquare at filtered
      exact of_decide_eq_true filtered.2
    let root := presentation.squareRoot proportion.toProportion.norm
    have rootSquare : root ^ 2 = proportion.toProportion.norm :=
      presentation.squareRoot_spec proportion.toProportion.norm squareMember
    have rootNonzero : root ≠ 0 := by
      intro rootZero
      apply proportion.normNonzero
      calc
        proportion.toProportion.norm = root ^ 2 := rootSquare.symm
        _ = 0 := by rw [rootZero]; ring1
    refine ⟨filtered.1, root⁻¹,
      ExplicitField.inv_ne_zero rootNonzero, ?_⟩
    rw [Proportion.norm_scale]
    have cancel := ExplicitField.mul_inv_cancel root rootNonzero
    calc
      root⁻¹ ^ 2 * proportion.toProportion.norm =
          root⁻¹ ^ 2 * root ^ 2 := by rw [rootSquare]
      _ = (root * root⁻¹) ^ 2 := by ring1
      _ = 1 := by rw [cancel]; ring1
  · rintro ⟨carrierMember, factor, factorNonzero, unitNorm⟩
    unfold quadranceClassKernel
    apply Filter.mem_filter.mpr
    constructor
    · exact carrierMember
    · unfold FiniteOddFieldPresentation.isSquare
      apply decide_eq_true
      apply (presentation.mem_squareValues_iff_hasSquareRoot _).2
      refine ⟨factor⁻¹, ?_⟩
      rw [Proportion.norm_scale] at unitNorm
      have cancel := ExplicitField.mul_inv_cancel factor factorNonzero
      calc
        factor⁻¹ ^ 2 = factor⁻¹ ^ 2 * 1 := by ring1
        _ = factor⁻¹ ^ 2 *
            (factor ^ 2 * proportion.toProportion.norm) := by rw [unitNorm]
        _ = (factor * factor⁻¹) ^ 2 *
            proportion.toProportion.norm := by ring1
        _ = proportion.toProportion.norm := by rw [cancel]; ring1

/-- Two squares representing a nonzero scalar supply a four-square representation with two cached zero coordinates. -/
@[expose] public def quadranceClassRepresentation
    (target : SquareClass.Basic.SquareClassRepresentative K) :
    Four.FourSquareRepresentation target.value := by
  let pair := presentation.twoSquareRepresentation target.value
  exact
    { scalar := pair.first
      t := pair.second
      r := 0
      s := 0
      equation := by
        rw [show pair.first ^ 2 + pair.second ^ 2 = target.value from
          pair.equation]
        ring1 }

/-- Executable finite-field preimage of an arbitrary square-class representative. -/
@[expose] public def quadranceClassPreimageProportion
    (target : SquareClass.Basic.SquareClassRepresentative K) : Projective.Basic.NonNullProportion K :=
  (presentation.quadranceClassRepresentation target).proportion target

/-- The computed preimage proportion has exactly the requested square-class representative norm. -/
theorem quadranceClassPreimageProportion_norm
    (target : SquareClass.Basic.SquareClassRepresentative K) :
    (presentation.quadranceClassPreimageProportion target).toProportion.norm =
      target.value := by
  exact FourSquareRepresentation.realizes_quadranceClass target
    (presentation.quadranceClassRepresentation target)

/-- Construct a rotation representing the requested nonzero square class.

Use the finite two-square representation to construct a non-null quaternion proportion and apply its rotation. -/
@[expose] public def quadranceClassPreimageRotation
    (target : SquareClass.Basic.SquareClassRepresentative K) : Rotations.Basic.Rotation K :=
  (NonNullProportion.rotation (presentation.quadranceClassPreimageProportion target))

/-- The finite-field quadrance-class map is onto, with a computed preimage for every displayed nonzero representative.
-/
theorem quadranceClassPreimage_realizes
    (target : SquareClass.Basic.SquareClassRepresentative K) :
    letI : DecidableEq K := presentation.eqDecidable
    (RotationQuadranceClass.ofRotation
      (presentation.quadranceClassPreimageRotation target)
      presentation.twoNonzero).Equivalent target := by
  letI : DecidableEq K := presentation.eqDecidable
  let source := presentation.quadranceClassPreimageProportion target
  let canonical := RotationProportion.ofRotation (NonNullProportion.rotation source)
    presentation.twoNonzero
  have matrixEqual : (NonNullProportion.rotationMatrix canonical) = (NonNullProportion.rotationMatrix source) := by
    calc
      (NonNullProportion.rotationMatrix canonical) = (NonNullProportion.rotation source).matrix :=
        RotationProportion.ofRotation_rotationMatrix (NonNullProportion.rotation source)
          presentation.twoNonzero
      _ = (NonNullProportion.rotationMatrix source) := rfl
  have equivalent := NonNullProportion.equivalent_of_rotationMatrix_eq
    canonical source presentation.twoNonzero matrixEqual
  have classEquivalent :=
    NonNullProportion.quadranceClass_respects_equivalent equivalent
  have sourceClassEqual : (NonNullProportion.quadranceClass source) = target := by
    apply SquareClassRepresentative.ext
    exact FourSquareRepresentation.realizes_quadranceClass target
      (presentation.quadranceClassRepresentation target)
  change (NonNullProportion.quadranceClass canonical).Equivalent target
  rw [← sourceClassEqual]
  exact classEquivalent

/-- A fixed non-null proportion whose norm represents the nontrivial square class. -/
@[expose] public def quadranceClassSwitcher : Projective.Basic.NonNullProportion K :=
  presentation.quadranceClassPreimageProportion
    presentation.nontrivialSquareClass

/-- The fixed fiber switcher has the chosen nonsquare norm. -/
theorem quadranceClassSwitcher_norm :
    presentation.quadranceClassSwitcher.toProportion.norm =
      (FiniteOddFieldPresentation.chosenNonsquare presentation).value := by
  exact presentation.quadranceClassPreimageProportion_norm
    presentation.nontrivialSquareClass

/-- Multiply by the fixed nonsquare-norm proportion and normalize back to the canonical four-chart carrier. -/
@[expose] public def switchQuadranceClassForward (source : Projective.Basic.NonNullProportion K) :
    Projective.Basic.NonNullProportion K :=
  (presentation.canonicalize
    (NonNullProportion.mul presentation.quadranceClassSwitcher source)).representative

/-- The inverse switch uses the displayed quaternion conjugate. -/
@[expose] public def switchQuadranceClassBackward (source : Projective.Basic.NonNullProportion K) :
    Projective.Basic.NonNullProportion K :=
  (presentation.canonicalize
    (NonNullProportion.mul
      (NonNullProportion.conjugate presentation.quadranceClassSwitcher)
      source)).representative

/-- Equivalent canonical non-null representatives are literally equal. -/
private theorem canonical_nonNull_eq_of_equivalent
    {left right : Projective.Basic.NonNullProportion K}
    (leftMember : left ∈ presentation.nonNullProjectiveRepresentatives)
    (rightMember : right ∈ presentation.nonNullProjectiveRepresentatives)
    (equivalent : left.Equivalent right) : left = right := by
  have rawEqual := presentation.projective_eq_of_equivalent
    (presentation.raw_mem_of_nonNull_mem leftMember)
    (presentation.raw_mem_of_nonNull_mem rightMember) equivalent
  apply NonNullProportion.ext (K := K)
  · exact congrArg Proportion.scalar rawEqual
  · exact congrArg Proportion.vector rawEqual

/-- Canonical normalization preserves the existence of a norm square root. -/
private theorem canonicalize_norm_hasSquareRoot
    (source : Projective.Basic.NonNullProportion K) (root : K)
    (rootSquare : root ^ 2 = source.toProportion.norm) :
    FiniteOddFieldPresentation.HasSquareRoot
      (presentation.canonicalize source).representative.toProportion.norm := by
  rcases (presentation.canonicalize source).equivalent with
    ⟨factor, _, representativeValue⟩
  refine ⟨factor * root, ?_⟩
  calc
    (factor * root) ^ 2 = factor ^ 2 * source.toProportion.norm := by
      rw [← rootSquare]
      ring1
    _ = (Proportion.scale factor source.toProportion).norm :=
      (Proportion.norm_scale factor source.toProportion).symm
    _ = (presentation.canonicalize source).representative.toProportion.norm :=
      congrArg Proportion.norm representativeValue.symm

/-- Canonical normalization preserves the absence of a norm square root. -/
private theorem canonicalize_norm_noRoot
    (source : Projective.Basic.NonNullProportion K)
    (sourceNoRoot : ∀ root : K, root ^ 2 ≠ source.toProportion.norm) :
    ∀ root : K,
      root ^ 2 ≠
        (presentation.canonicalize source).representative.toProportion.norm := by
  rcases (presentation.canonicalize source).equivalent with
    ⟨factor, factorNonzero, representativeValue⟩
  have factorSquareNonzero : factor ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      ExplicitField.mul_ne_zero factorNonzero factorNonzero
  have scaledNoRoot := FiniteOddFieldPresentation.square_mul_nonsquare_noRoot (factor ^ 2) factor
    source.toProportion.norm factorSquareNonzero rfl sourceNoRoot
  intro root rootSquare
  apply scaledNoRoot root
  calc
    root ^ 2 =
        (presentation.canonicalize source).representative.toProportion.norm :=
      rootSquare
    _ = (Proportion.scale factor source.toProportion).norm :=
      congrArg Proportion.norm representativeValue
    _ = factor ^ 2 * source.toProportion.norm :=
      Proportion.norm_scale factor source.toProportion

/-- Multiplication by the switcher sends the square-norm kernel to the nonsquare fiber. -/
theorem switchQuadranceClassForward_mem
    {source : Projective.Basic.NonNullProportion K}
    (member : source ∈ presentation.quadranceClassKernel) :
    presentation.switchQuadranceClassForward source ∈
      presentation.quadranceClassNontrivialFiber := by
  letI : DecidableEq K := presentation.eqDecidable
  have sourceSquareAccepted := (Filter.mem_filter.mp member).2
  unfold FiniteOddFieldPresentation.isSquare at sourceSquareAccepted
  have sourceSquareMember := of_decide_eq_true sourceSquareAccepted
  let sourceRoot := presentation.squareRoot source.toProportion.norm
  have sourceRootSquare : sourceRoot ^ 2 = source.toProportion.norm :=
    presentation.squareRoot_spec source.toProportion.norm sourceSquareMember
  let switcher := presentation.quadranceClassSwitcher
  let product := NonNullProportion.mul switcher source
  have productNoRoot : ∀ root : K,
      root ^ 2 ≠ product.toProportion.norm := by
    have baseNoRoot := FiniteOddFieldPresentation.square_mul_nonsquare_noRoot
      source.toProportion.norm sourceRoot
      (FiniteOddFieldPresentation.chosenNonsquare presentation).value source.normNonzero sourceRootSquare
      (FiniteOddFieldPresentation.chosenNonsquare presentation).noRoot
    intro root rootSquare
    apply baseNoRoot root
    calc
      root ^ 2 = product.toProportion.norm := rootSquare
      _ = switcher.toProportion.norm * source.toProportion.norm :=
        NonNullProportion.mul_norm switcher source
      _ = (FiniteOddFieldPresentation.chosenNonsquare presentation).value *
          source.toProportion.norm := by
        rw [presentation.quadranceClassSwitcher_norm]
      _ = source.toProportion.norm *
          (FiniteOddFieldPresentation.chosenNonsquare presentation).value := by ring1
  have resultNoRoot := presentation.canonicalize_norm_noRoot product
    productNoRoot
  unfold quadranceClassNontrivialFiber
  apply Filter.mem_filter.mpr
  constructor
  · exact presentation.canonicalize_mem product
  · apply Purelib.Data.Bool.Decide.not_true_iff _ |>.mpr
    unfold FiniteOddFieldPresentation.isSquare
    apply decide_eq_false
    intro squareMember
    exact resultNoRoot (presentation.squareRoot
      (presentation.canonicalize product).representative.toProportion.norm)
      (presentation.squareRoot_spec _ squareMember)

/-- Multiplication by the conjugate switcher sends the nonsquare fiber to the kernel. -/
theorem switchQuadranceClassBackward_mem
    {source : Projective.Basic.NonNullProportion K}
    (member : source ∈ presentation.quadranceClassNontrivialFiber) :
    presentation.switchQuadranceClassBackward source ∈
      presentation.quadranceClassKernel := by
  letI : DecidableEq K := presentation.eqDecidable
  have sourceRejected := (Filter.mem_filter.mp member).2
  have sourceSquareFalse := Purelib.Data.Bool.Decide.not_true_iff _ |>.mp sourceRejected
  unfold FiniteOddFieldPresentation.isSquare at sourceSquareFalse
  have sourceNotSquare := decide_eq_false_iff_not.mp sourceSquareFalse
  have sourceNoRoot : ∀ root : K,
      root ^ 2 ≠ source.toProportion.norm := by
    intro root rootSquare
    exact sourceNotSquare
      (rootSquare ▸ presentation.squareValuesComplete root)
  let switcher := presentation.quadranceClassSwitcher
  let conjugate := NonNullProportion.conjugate switcher
  let product := NonNullProportion.mul conjugate source
  have conjugateNorm : conjugate.toProportion.norm =
      (FiniteOddFieldPresentation.chosenNonsquare presentation).value := by
    calc
      conjugate.toProportion.norm = switcher.toProportion.norm :=
        Proportion.norm_conjugate switcher.toProportion
      _ = (FiniteOddFieldPresentation.chosenNonsquare presentation).value :=
        presentation.quadranceClassSwitcher_norm
  let witness := (FiniteOddFieldPresentation.nonsquareMulNonsquareSquareWitness presentation)
    (FiniteOddFieldPresentation.chosenNonsquare presentation).value source.toProportion.norm
    (FiniteOddFieldPresentation.chosenNonsquare presentation).noRoot sourceNoRoot
  have productRootSquare : witness.root ^ 2 = product.toProportion.norm := by
    calc
      witness.root ^ 2 = (FiniteOddFieldPresentation.chosenNonsquare presentation).value *
          source.toProportion.norm := witness.equation
      _ = conjugate.toProportion.norm * source.toProportion.norm := by
        rw [conjugateNorm]
      _ = product.toProportion.norm :=
        (NonNullProportion.mul_norm conjugate source).symm
  rcases presentation.canonicalize_norm_hasSquareRoot product witness.root
      productRootSquare with ⟨resultRoot, resultRootSquare⟩
  unfold quadranceClassKernel
  apply Filter.mem_filter.mpr
  constructor
  · exact presentation.canonicalize_mem product
  · unfold FiniteOddFieldPresentation.isSquare
    apply decide_eq_true
    exact (presentation.mem_squareValues_iff_hasSquareRoot _).2
      ⟨resultRoot, resultRootSquare⟩

/-- The backward switch undoes the forward switch on the kernel. -/
theorem switchQuadranceClassBackward_forward
    {source : Projective.Basic.NonNullProportion K}
    (member : source ∈ presentation.quadranceClassKernel) :
    presentation.switchQuadranceClassBackward
        (presentation.switchQuadranceClassForward source) = source := by
  let switcher := presentation.quadranceClassSwitcher
  let forwardProduct := NonNullProportion.mul switcher source
  let forwardRepresentative :=
    (presentation.canonicalize forwardProduct).representative
  let backwardProduct := NonNullProportion.mul
    (NonNullProportion.conjugate switcher) forwardRepresentative
  have replaceForward :
      (NonNullProportion.mul (NonNullProportion.conjugate switcher)
          forwardProduct).Equivalent backwardProduct := by
    exact NonNullProportion.mul_respects_equivalent
      (NonNullProportion.equivalent_refl _)
      (presentation.canonicalize forwardProduct).equivalent
  have cancel :
      (NonNullProportion.mul (NonNullProportion.conjugate switcher)
          forwardProduct).Equivalent source := by
    change (NonNullProportion.mul (NonNullProportion.conjugate switcher)
      (NonNullProportion.mul switcher source)).Equivalent source
    rw [← NonNullProportion.mul_assoc]
    have lifted := NonNullProportion.mul_respects_equivalent
      (NonNullProportion.conjugate_mul_equivalent_identity switcher)
      (NonNullProportion.equivalent_refl source)
    rw [NonNullProportion.identity_mul] at lifted
    exact lifted
  have backwardProductEquivalent : backwardProduct.Equivalent source :=
    NonNullProportion.equivalent_trans
      (NonNullProportion.equivalent_symm replaceForward) cancel
  unfold switchQuadranceClassBackward switchQuadranceClassForward
  apply presentation.canonical_nonNull_eq_of_equivalent
    (presentation.canonicalize_mem backwardProduct)
    (Filter.mem_filter.mp member).1
  exact NonNullProportion.equivalent_trans
    (NonNullProportion.equivalent_symm
      (presentation.canonicalize backwardProduct).equivalent)
    backwardProductEquivalent

/-- The forward switch undoes the backward switch on the nonsquare fiber. -/
theorem switchQuadranceClassForward_backward
    {source : Projective.Basic.NonNullProportion K}
    (member : source ∈ presentation.quadranceClassNontrivialFiber) :
    presentation.switchQuadranceClassForward
        (presentation.switchQuadranceClassBackward source) = source := by
  let switcher := presentation.quadranceClassSwitcher
  let backwardProduct := NonNullProportion.mul
    (NonNullProportion.conjugate switcher) source
  let backwardRepresentative :=
    (presentation.canonicalize backwardProduct).representative
  let forwardProduct :=
    NonNullProportion.mul switcher backwardRepresentative
  have replaceBackward :
      (NonNullProportion.mul switcher backwardProduct).Equivalent
        forwardProduct := by
    exact NonNullProportion.mul_respects_equivalent
      (NonNullProportion.equivalent_refl _)
      (presentation.canonicalize backwardProduct).equivalent
  have cancel :
      (NonNullProportion.mul switcher backwardProduct).Equivalent source := by
    change (NonNullProportion.mul switcher
      (NonNullProportion.mul (NonNullProportion.conjugate switcher)
        source)).Equivalent source
    rw [← NonNullProportion.mul_assoc]
    have lifted := NonNullProportion.mul_respects_equivalent
      (NonNullProportion.mul_conjugate_equivalent_identity switcher)
      (NonNullProportion.equivalent_refl source)
    rw [NonNullProportion.identity_mul] at lifted
    exact lifted
  have forwardProductEquivalent : forwardProduct.Equivalent source :=
    NonNullProportion.equivalent_trans
      (NonNullProportion.equivalent_symm replaceBackward) cancel
  unfold switchQuadranceClassForward switchQuadranceClassBackward
  apply presentation.canonical_nonNull_eq_of_equivalent
    (presentation.canonicalize_mem forwardProduct)
    (Filter.mem_filter.mp member).1
  exact NonNullProportion.equivalent_trans
    (NonNullProportion.equivalent_symm
      (presentation.canonicalize forwardProduct).equivalent)
    forwardProductEquivalent

/-- Multiplication by one fixed nonsquare-norm proportion exchanges the two quadrance-class fibers. -/
@[expose] public def quadranceClassFiberBijection : Bijection.ListBijection
    presentation.quadranceClassKernel
    presentation.quadranceClassNontrivialFiber where
  forward := presentation.switchQuadranceClassForward
  backward := presentation.switchQuadranceClassBackward
  forward_mem := fun _ member =>
    presentation.switchQuadranceClassForward_mem member
  backward_mem := fun _ member =>
    presentation.switchQuadranceClassBackward_mem member
  backward_forward := fun _ member =>
    presentation.switchQuadranceClassBackward_forward member
  forward_backward := fun _ member =>
    presentation.switchQuadranceClassForward_backward member

open Purelib.Data.List.Filter (pairwise_filter) in
/-- The two canonical quadrance-class fibers have equal finite lengths.

The retained forward and backward maps form the original finite bijection;
filtering the executable projective representative list preserves its nodup certificate. -/
theorem quadranceClassKernel_length_eq_nontrivialFiber_length :
    presentation.quadranceClassKernel.length =
      presentation.quadranceClassNontrivialFiber.length := by
  apply ListBijection.length_eq
    presentation.quadranceClassFiberBijection
  · exact pairwise_filter _ presentation.nonNullProjectiveRepresentatives_nodup
  · exact pairwise_filter _ presentation.nonNullProjectiveRepresentatives_nodup

/-- The canonical parabolic rotation attached to a displayed null anchor. -/
@[expose] public def parabolicRotation (presentation : Presentation.FiniteOddFieldPresentation K)
    (vector : Coordinates3.Vector K) (null : vector.quadrance = 0) :
    Rotations.Basic.Rotation K :=
  Cap.capRotation vector
    ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation) vector null)

/-- A cap rotation of a null vector has half spread zero. -/
theorem parabolicRotation_halfSpread (vector : Coordinates3.Vector K)
    (null : vector.quadrance = 0) :
    Spread.halfSpread (presentation.parabolicRotation vector null) = 0 := by
  unfold parabolicRotation
  rw [Spread.halfSpread_cap vector _ presentation.twoNonzero, null,
    ExplicitField.zero_div]

/-- A cap rotation of a null vector has characteristic value equal to the cube of X minus one. -/
theorem parabolicRotation_characteristic (vector : Coordinates3.Vector K)
    (null : vector.quadrance = 0) (X : K) :
    Matrix3.characteristicValue
        (presentation.parabolicRotation vector null).matrix X =
      (X - 1) ^ 3 := by
  unfold parabolicRotation Cap.capRotation
  rw [Cap.characteristicValue_cap vector _ X, null]
  have denominatorOne : Cap.capDenominator vector = 1 := by
    unfold Cap.capDenominator
    rw [null]
    ring1
  rw [denominatorOne]
  have oneInverse : (1 : K)⁻¹ = 1 := by
    have cancel := ExplicitField.mul_inv_cancel (1 : K)
      (FiniteOddFieldPresentation.one_ne_zero presentation)
    simpa only [_root_.one_mul] using cancel
  simp only [ExplicitField.div_eq_mul_inv, oneInverse]
  ring1

/-- A null cap rotation fixes its displayed anchor vector. -/
theorem parabolicRotation_fixedAnchor (vector : Coordinates3.Vector K)
    (null : vector.quadrance = 0) :
    Matrix3.rowMul vector
        (presentation.parabolicRotation vector null).matrix = vector := by
  change Matrix3.rowMul vector
      (Cap.cap vector
        ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation) vector null))
          =
    vector
  exact Cap.rowMul_self_cap vector
    ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation) vector null)

/-- A nonzero null anchor gives a nonidentity parabolic rotation. -/
theorem parabolicRotation_nonidentity (vector : Coordinates3.Vector K)
    (null : vector.quadrance = 0) (nonzero : vector ≠ Coordinates3.Vector.zero) :
    (presentation.parabolicRotation vector null).matrix ≠ Matrix3.identity := by
  intro identity
  apply nonzero
  apply Cap.cap_injective presentation.twoNonzero vector Coordinates3.Vector.zero
    ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation) vector null)
    ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation)
      Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero)
  calc
    Cap.cap vector
        ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation) vector null) =
      Matrix3.identity := identity
    _ = Cap.cap Coordinates3.Vector.zero
        ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation)
          Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) :=
      (((fun {K : Type _} [ExplicitField K] (presentation :
        Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) =>
        (Purelib.Geometry.Rotations.Cayley.FieldRealizations.cap_zero_eq_identity (K := K)
        (Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation
        Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) :
        Purelib.Geometry.Rotations.Cayley.Cap.cap (Coordinates3.Vector.zero :
        Coordinates3.Vector K)
        ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation)
        Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) =
        Purelib.LinearAlgebra.Coordinates3.Matrix3.identity)) presentation)).symm

/-- Equal parabolic cap rotations have equal null anchors. -/
theorem parabolicRotation_injective
    {left right : Coordinates3.Vector K} (leftNull : left.quadrance = 0)
    (rightNull : right.quadrance = 0)
    (equal : presentation.parabolicRotation left leftNull =
      presentation.parabolicRotation right rightNull) : left = right := by
  apply Cap.cap_injective presentation.twoNonzero left right
    ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation) left leftNull)
    ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation) right rightNull)
  exact congrArg Rotation.matrix equal

/-- The nonidentity parabolic rotations lying over one canonical projective null direction, parametrized by every
displayed nonzero scalar. -/
@[expose] public def parabolicRotationsOverDirection (direction : Coordinates3.Vector K)
    (directionMember : direction ∈
      presentation.nullDirectionRepresentatives) : List (Rotations.Basic.Rotation K) :=
  presentation.nonzeroScalars.map fun parameter =>
    presentation.parabolicRotation (Coordinates3.Vector.scale parameter direction) (by
      rw [Coordinates3.Vector.quadrance_scale,
        presentation.nullDirectionRepresentative_null directionMember]
      ring1)

/-- The rotations over a canonical null direction have no duplicates. -/
theorem parabolicRotationsOverDirection_nodup (direction : Coordinates3.Vector K)
    (directionMember : direction ∈
      presentation.nullDirectionRepresentatives) :
    (presentation.parabolicRotationsOverDirection direction
      directionMember).Nodup := by
  unfold parabolicRotationsOverDirection
  apply Data.List.Nodup.nodup_map_of_injective
  · intro left right equal
    apply presentation.nullDirection_scale_injective directionMember
    apply presentation.parabolicRotation_injective
      (leftNull := by
        rw [Coordinates3.Vector.quadrance_scale,
          presentation.nullDirectionRepresentative_null directionMember]
        ring1)
      (rightNull := by
        rw [Coordinates3.Vector.quadrance_scale,
          presentation.nullDirectionRepresentative_null directionMember]
        ring1)
    exact equal
  · exact presentation.nonzeroScalars_nodup

/-- A canonical null direction supports one parabolic rotation for each nonzero field element. -/
theorem parabolicRotationsOverDirection_length (direction : Coordinates3.Vector K)
    (directionMember : direction ∈
      presentation.nullDirectionRepresentatives) :
    (presentation.parabolicRotationsOverDirection direction
      directionMember).length = presentation.carrier.length - 1 := by
  unfold parabolicRotationsOverDirection
  rw [Map.length_map, presentation.nonzeroScalars_length]

/-- Each rotation in the direction fiber is nonidentity, has half spread zero and has the unipotent characteristic
polynomial. -/
theorem parabolicRotationsOverDirection_mem_properties
    (direction : Coordinates3.Vector K)
    (directionMember : direction ∈
      presentation.nullDirectionRepresentatives)
    {rotation : Rotations.Basic.Rotation K}
    (member : rotation ∈ presentation.parabolicRotationsOverDirection
      direction directionMember) :
    Spread.halfSpread rotation = 0 ∧
      rotation.matrix ≠ Matrix3.identity ∧
      ∀ X : K, Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3 := by
  unfold parabolicRotationsOverDirection at member
  rcases Map.mem_map.mp member with
    ⟨parameter, parameterMember, equal⟩
  have parameterNonzero :=
    (presentation.mem_nonzeroScalars_iff parameter).1 parameterMember |>.1
  have scaledNull : (Coordinates3.Vector.scale parameter direction).quadrance = 0 := by
    rw [Coordinates3.Vector.quadrance_scale,
      presentation.nullDirectionRepresentative_null directionMember]
    ring1
  have scaledNonzero : Coordinates3.Vector.scale parameter direction ≠ Coordinates3.Vector.zero := by
    intro scaledZero
    apply parameterNonzero
    apply presentation.nullDirection_scale_injective directionMember
    calc
      Coordinates3.Vector.scale parameter direction = Coordinates3.Vector.zero := scaledZero
      _ = Coordinates3.Vector.scale 0 direction := (Coordinates3.Vector.zero_scale direction).symm
  rw [← equal]
  exact
    ⟨presentation.parabolicRotation_halfSpread _ scaledNull,
      presentation.parabolicRotation_nonidentity _ scaledNull scaledNonzero,
      presentation.parabolicRotation_characteristic _ scaledNull⟩

/-- Every nonidentity half-spread-zero rotation has one and only one displayed nonzero null anchor. The existential
retains the null and nonzero certificates used to construct the cap. -/
theorem parabolicRotation_complete (rotation : Rotations.Basic.Rotation K)
    (spreadZero : Spread.halfSpread rotation = 0)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    ∃ vector : Coordinates3.Vector K, ∃ null : vector.quadrance = 0,
      vector ≠ Coordinates3.Vector.zero ∧
      vector ∈ presentation.nonzeroNullVectors ∧
        rotation = presentation.parabolicRotation vector null := by
  have notHalfTurn : Spread.halfSpread rotation ≠ 1 := by
    intro spreadOne
    apply FiniteOddFieldPresentation.one_ne_zero presentation
    calc
      (1 : K) = Spread.halfSpread rotation := spreadOne.symm
      _ = 0 := spreadZero
  let vector := Recovery.rotationAnchorVector rotation notHalfTurn
  have null : vector.quadrance = 0 := by
    have recoveredQuadrance := Recovery.quadrance_rotationAnchorVector rotation
      notHalfTurn presentation.twoNonzero
    rw [spreadZero] at recoveredQuadrance
    have oneSubtractZero : (1 : K) - 0 = 1 := by ring1
    rewrite [oneSubtractZero, ExplicitField.zero_div] at recoveredQuadrance
    exact recoveredQuadrance
  have nonzero : vector ≠ Coordinates3.Vector.zero := by
    intro vectorZero
    apply nonidentity
    have recovered := Recovery.cap_rotationAnchor rotation notHalfTurn
      presentation.twoNonzero
    have zeroCap := ((fun {K : Type _} [ExplicitField K] (presentation :
      Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) =>
      (Purelib.Geometry.Rotations.Cayley.FieldRealizations.cap_zero_eq_identity (K := K)
      (Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation
      Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) :
      Purelib.Geometry.Rotations.Cayley.Cap.cap (Coordinates3.Vector.zero :
      Coordinates3.Vector K)
      ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation)
      Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) =
      Purelib.LinearAlgebra.Coordinates3.Matrix3.identity)) presentation)
    calc
      rotation.matrix = Cap.cap vector
          (Recovery.rotationAnchorVector_capDefined rotation notHalfTurn
            presentation.twoNonzero) := recovered.symm
      _ = Cap.cap Coordinates3.Vector.zero
          ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation)
            Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) :=
        Purelib.Geometry.Rotations.Cayley.Cap.eq_of_vector_eq vectorZero
          _ _
      _ = Matrix3.identity := zeroCap
  have member : vector ∈ presentation.nonzeroNullVectors :=
    (presentation.mem_nonzeroNullVectors_iff vector).2
      ⟨presentation.vectors_complete vector, null, nonzero⟩
  refine ⟨vector, null, nonzero, member, ?_⟩
  apply (fun {K : Type _} [ExplicitField K] {left right :
    Purelib.Geometry.Rotations.Basic.Rotation K} (equal : left.matrix = right.matrix) =>
    (Purelib.Geometry.Rotations.Basic.Rotation.eq_of_matrix_eq (K := K) (left := left) (right := right) equal : left =
    right))
  exact (Recovery.cap_rotationAnchor rotation notHalfTurn presentation.twoNonzero).symm

/-- Characteristic-polynomial form of parabolic completeness. This is the literal converse requested by Problem 69:
every nonidentity rotation with characteristic polynomial `(X - 1)^3` is a cap of one displayed nonzero null anchor. -/
theorem parabolicRotation_complete_of_characteristic
    (rotation : Rotations.Basic.Rotation K)
    (characteristic : ∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    ∃ vector : Coordinates3.Vector K, ∃ null : vector.quadrance = 0,
      vector ≠ Coordinates3.Vector.zero ∧
      vector ∈ presentation.nonzeroNullVectors ∧
        rotation = presentation.parabolicRotation vector null :=
  presentation.parabolicRotation_complete rotation
    ((Spread.characteristicUnipotent_iff_halfSpread_eq_zero rotation
      presentation.twoNonzero).1 characteristic)
    nonidentity

set_option genInjectivity false in
/-- Executable canonical null-direction and nonzero parameter coordinates for one nonidentity parabolic rotation. -/
structure ParabolicDirectionCoordinates (rotation : Rotations.Basic.Rotation K) where
  /-- The retained canonical projective null direction. -/ direction : Coordinates3.Vector K
  /-- The direction belongs to the canonical null-direction list. -/ directionMember : direction ∈
    presentation.nullDirectionRepresentatives
  /-- The retained nonzero scalar along the direction. -/ parameter : K
  /-- The parameter belongs to the displayed nonzero scalar list. -/ parameterMember : parameter ∈
    presentation.nonzeroScalars
  /-- The scaled direction has zero quadrance. -/ scaledNull : (Coordinates3.Vector.scale parameter direction).quadrance
    = 0
  /-- The original rotation is the cap rotation of this exact scaled direction. -/ rotation_eq : rotation =
    presentation.parabolicRotation
    (Coordinates3.Vector.scale parameter direction) scaledNull

constructive_injectivity ParabolicDirectionCoordinates

/-- Recover the canonical projective null direction and its affine parameter directly from a nonidentity
half-spread-zero rotation. -/
@[expose] public def parabolicDirectionCoordinates (rotation : Rotations.Basic.Rotation K)
    (spreadZero : Spread.halfSpread rotation = 0)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    presentation.ParabolicDirectionCoordinates rotation := by
  have notHalfTurn : Spread.halfSpread rotation ≠ 1 := by
    intro spreadOne
    apply FiniteOddFieldPresentation.one_ne_zero presentation
    calc
      (1 : K) = Spread.halfSpread rotation := spreadOne.symm
      _ = 0 := spreadZero
  let anchorVector := Recovery.rotationAnchorVector rotation notHalfTurn
  have anchorNull : anchorVector.quadrance = 0 := by
    have recoveredQuadrance := Recovery.quadrance_rotationAnchorVector rotation
      notHalfTurn presentation.twoNonzero
    rw [spreadZero] at recoveredQuadrance
    have oneSubtractZero : (1 : K) - 0 = 1 := by ring1
    rewrite [oneSubtractZero, ExplicitField.zero_div] at recoveredQuadrance
    exact recoveredQuadrance
  have anchorNonzero : anchorVector ≠ Coordinates3.Vector.zero := by
    intro anchorZero
    apply nonidentity
    have recovered := Recovery.cap_rotationAnchor rotation notHalfTurn
      presentation.twoNonzero
    have zeroCap := ((fun {K : Type _} [ExplicitField K] (presentation :
      Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) =>
      (Purelib.Geometry.Rotations.Cayley.FieldRealizations.cap_zero_eq_identity (K := K)
      (Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation
      Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) :
      Purelib.Geometry.Rotations.Cayley.Cap.cap (Coordinates3.Vector.zero :
      Coordinates3.Vector K)
      ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation)
      Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) =
      Purelib.LinearAlgebra.Coordinates3.Matrix3.identity)) presentation)
    calc
      rotation.matrix = Cap.cap anchorVector
          (Recovery.rotationAnchorVector_capDefined rotation notHalfTurn
            presentation.twoNonzero) := recovered.symm
      _ = Cap.cap Coordinates3.Vector.zero
          ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation)
            Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) :=
        Purelib.Geometry.Rotations.Cayley.Cap.eq_of_vector_eq anchorZero
          _ _
      _ = Matrix3.identity := zeroCap
  let normalization := presentation.normalizeNullDirection anchorVector
    anchorNull anchorNonzero
  have directionNull : normalization.representative.quadrance = 0 :=
    presentation.nullDirectionRepresentative_null
      normalization.representativeMember
  have scaledNull :
      (Coordinates3.Vector.scale normalization.parameter
        normalization.representative).quadrance = 0 := by
    rw [Coordinates3.Vector.quadrance_scale, directionNull]
    ring1
  refine
    { direction := normalization.representative
      directionMember := normalization.representativeMember
      parameter := normalization.parameter
      parameterMember :=
        (presentation.mem_nonzeroScalars_iff normalization.parameter).2
          ⟨normalization.parameterNonzero,
            presentation.carrierComplete normalization.parameter⟩
      scaledNull := scaledNull
      rotation_eq := ?_ }
  apply (fun {K : Type _} [ExplicitField K] {left right :
    Purelib.Geometry.Rotations.Basic.Rotation K} (equal : left.matrix = right.matrix) =>
    (Purelib.Geometry.Rotations.Basic.Rotation.eq_of_matrix_eq (K := K) (left := left) (right := right) equal : left =
    right))
  let scaledDefined :=
    (Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation)
      (Coordinates3.Vector.scale normalization.parameter normalization.representative)
      scaledNull
  change rotation.matrix = Cap.cap
    (Coordinates3.Vector.scale normalization.parameter normalization.representative)
      scaledDefined
  have recovered := Recovery.cap_rotationAnchor rotation notHalfTurn
    presentation.twoNonzero
  calc
    rotation.matrix = Cap.cap anchorVector
        (Recovery.rotationAnchorVector_capDefined rotation notHalfTurn
          presentation.twoNonzero) := recovered.symm
    _ = Cap.cap (Coordinates3.Vector.scale normalization.parameter normalization.representative)
        scaledDefined :=
      Purelib.Geometry.Rotations.Cayley.Cap.eq_of_vector_eq
        normalization.source_eq_scale _ _

/-- Executable direction/parameter normal form obtained directly from the paper's characteristic-polynomial description
of a parabolic rotation. -/
@[expose] public def parabolicDirectionCoordinatesOfCharacteristic
    (rotation : Rotations.Basic.Rotation K)
    (characteristic : ∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3)
    (nonidentity : rotation.matrix ≠ Matrix3.identity) :
    presentation.ParabolicDirectionCoordinates rotation :=
  presentation.parabolicDirectionCoordinates rotation
    ((Spread.characteristicUnipotent_iff_halfSpread_eq_zero rotation
      presentation.twoNonzero).1 characteristic)
    nonidentity

/-- Any other canonical direction/parameter description of the same parabolic rotation agrees with the computed
coordinates. -/
theorem parabolicDirectionCoordinates_unique (rotation : Rotations.Basic.Rotation K)
    (spreadZero : Spread.halfSpread rotation = 0)
    (nonidentity : rotation.matrix ≠ Matrix3.identity)
    (direction : Coordinates3.Vector K)
    (directionMember : direction ∈
      presentation.nullDirectionRepresentatives)
    (parameter : K) (parameterNonzero : parameter ≠ 0)
    (scaledNull : (Coordinates3.Vector.scale parameter direction).quadrance = 0)
    (rotationEq : rotation = presentation.parabolicRotation
      (Coordinates3.Vector.scale parameter direction) scaledNull) :
    let coordinates := presentation.parabolicDirectionCoordinates rotation
      spreadZero nonidentity
    direction = coordinates.direction ∧ parameter = coordinates.parameter := by
  let coordinates := presentation.parabolicDirectionCoordinates rotation
    spreadZero nonidentity
  have coordinateParameterNonzero :=
    (presentation.mem_nonzeroScalars_iff coordinates.parameter).1
      coordinates.parameterMember |>.1
  have rotationEqual :
      presentation.parabolicRotation (Coordinates3.Vector.scale parameter direction)
          scaledNull =
        presentation.parabolicRotation
          (Coordinates3.Vector.scale coordinates.parameter coordinates.direction)
          coordinates.scaledNull :=
    rotationEq.symm.trans coordinates.rotation_eq
  have anchorEqual :
      Coordinates3.Vector.scale parameter direction =
        Coordinates3.Vector.scale coordinates.parameter coordinates.direction :=
    presentation.parabolicRotation_injective scaledNull
      coordinates.scaledNull rotationEqual
  let factor := coordinates.parameter⁻¹ * parameter
  have factorNonzero : factor ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.inv_ne_zero coordinateParameterNonzero)
      parameterNonzero
  have coordinateCancel := FiniteOddFieldPresentation.inverse_mul coordinates.parameter
    coordinateParameterNonzero
  have scaledDirections :
      coordinates.direction = Coordinates3.Vector.scale factor direction := by
    apply Coordinates3.Vector.ext
    · have coordinate := congrArg Coordinates3.Vector.t anchorEqual
      change parameter * direction.t =
        coordinates.parameter * coordinates.direction.t at coordinate
      change coordinates.direction.t =
        (coordinates.parameter⁻¹ * parameter) * direction.t
      calc
        coordinates.direction.t = 1 * coordinates.direction.t := by ring1
        _ = (coordinates.parameter⁻¹ * coordinates.parameter) *
            coordinates.direction.t := by rw [coordinateCancel]
        _ = coordinates.parameter⁻¹ *
            (coordinates.parameter * coordinates.direction.t) := by ring1
        _ = coordinates.parameter⁻¹ * (parameter * direction.t) := by
          rw [coordinate]
        _ = (coordinates.parameter⁻¹ * parameter) * direction.t := by ring1
    · have coordinate := congrArg Coordinates3.Vector.r anchorEqual
      change parameter * direction.r =
        coordinates.parameter * coordinates.direction.r at coordinate
      change coordinates.direction.r =
        (coordinates.parameter⁻¹ * parameter) * direction.r
      calc
        coordinates.direction.r = 1 * coordinates.direction.r := by ring1
        _ = (coordinates.parameter⁻¹ * coordinates.parameter) *
            coordinates.direction.r := by rw [coordinateCancel]
        _ = coordinates.parameter⁻¹ *
            (coordinates.parameter * coordinates.direction.r) := by ring1
        _ = coordinates.parameter⁻¹ * (parameter * direction.r) := by
          rw [coordinate]
        _ = (coordinates.parameter⁻¹ * parameter) * direction.r := by ring1
    · have coordinate := congrArg Coordinates3.Vector.s anchorEqual
      change parameter * direction.s =
        coordinates.parameter * coordinates.direction.s at coordinate
      change coordinates.direction.s =
        (coordinates.parameter⁻¹ * parameter) * direction.s
      calc
        coordinates.direction.s = 1 * coordinates.direction.s := by ring1
        _ = (coordinates.parameter⁻¹ * coordinates.parameter) *
            coordinates.direction.s := by rw [coordinateCancel]
        _ = coordinates.parameter⁻¹ *
            (coordinates.parameter * coordinates.direction.s) := by ring1
        _ = coordinates.parameter⁻¹ * (parameter * direction.s) := by
          rw [coordinate]
        _ = (coordinates.parameter⁻¹ * parameter) * direction.s := by ring1
  have directionEqual := presentation.nullDirectionRepresentative_eq_of_scaled
    directionMember coordinates.directionMember factorNonzero scaledDirections
  constructor
  · exact directionEqual
  · apply presentation.nullDirection_scale_injective
      coordinates.directionMember
    calc
      Coordinates3.Vector.scale parameter coordinates.direction =
          Coordinates3.Vector.scale parameter direction := by rw [directionEqual]
      _ = Coordinates3.Vector.scale coordinates.parameter coordinates.direction :=
        anchorEqual

set_option genInjectivity false in
/-- Executable four-way classification of one finite-field rotation. The endpoint cases retain the matrix, axis, or
canonical parabolic coordinates needed by downstream computations instead of storing only a proposition. -/
inductive RotationStratum (rotation : Rotations.Basic.Rotation K) where
  /-- The identity matrix, with its zero half-spread certificate. -/ | identity
      (spreadZero : Spread.halfSpread rotation = 0)
      (matrixIdentity : rotation.matrix = Matrix3.identity)
  /-- A nonidentity zero-half-spread rotation with executable null-direction coordinates. -/ | parabolic
      (spreadZero : Spread.halfSpread rotation = 0)
      (matrixNonidentity : rotation.matrix ≠ Matrix3.identity)
      (coordinates : presentation.ParabolicDirectionCoordinates rotation)
  /-- A half-spread-one rotation with a retained non-null axis and half-turn matrix equality. -/ | halfTurn
      (spreadOne : Spread.halfSpread rotation = 1)
      (axis : Coordinates3.Vector K)
      (axisNonNull : axis.quadrance ≠ 0)
      (matrix_eq : rotation.matrix = Reflection.halfTurn axis axisNonNull)
  /-- A rotation whose half spread differs from both endpoint values. -/ | semisimple
      (spreadNonzero : Spread.halfSpread rotation ≠ 0)
      (spreadNotOne : Spread.halfSpread rotation ≠ 1)

constructive_injectivity RotationStratum

/-- Classify a displayed rotation by the two finite half-spread tests and one matrix-identity test. -/
@[expose] public def classifyRotationStratum (rotation : Rotations.Basic.Rotation K) :
    presentation.RotationStratum rotation := by
  letI : DecidableEq K := presentation.eqDecidable
  by_cases spreadZero : Spread.halfSpread rotation = 0
  · by_cases matrixIdentity : rotation.matrix = Matrix3.identity
    · exact Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.RotationStratum.identity spreadZero
        matrixIdentity
    · exact Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.RotationStratum.parabolic spreadZero
        matrixIdentity
        (presentation.parabolicDirectionCoordinates rotation spreadZero
          matrixIdentity)
  · by_cases spreadOne : Spread.halfSpread rotation = 1
    · let axis := Recovery.halfTurnAxis rotation spreadOne presentation.twoNonzero
      let axisNonNull := Recovery.halfTurnAxis_nonNull rotation spreadOne
        presentation.twoNonzero
      exact Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.RotationStratum.halfTurn spreadOne axis
        axisNonNull
        (Recovery.rotation_eq_halfTurn_halfTurnAxis rotation spreadOne
          presentation.twoNonzero)
    · exact Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.RotationStratum.semisimple spreadZero
        spreadOne

/-- The square and nonsquare norm filters partition the canonical carrier by length. -/
theorem quadranceClassFibers_partition :
    presentation.quadranceClassKernel.length +
        presentation.quadranceClassNontrivialFiber.length =
      presentation.nonNullProjectiveRepresentatives.length := by
  exact CountWhere.listCountWhere_add_complement
    presentation.nonNullProjectiveRepresentatives
    (fun proportion => (FiniteOddFieldPresentation.isSquare presentation) proportion.toProportion.norm)

/-- Efficient executable count of the non-null canonical projective carrier. -/
@[expose] public def rotationCount : Nat := by
  exact presentation.projectiveCountWhere fun raw =>
    (presentation.certifyNonNull raw).isSome

/-- The efficient counter counts the proved duplicate-free complete rotation carrier, not a separate unchecked table. -/
theorem rotationCount_eq_rotationEnumeration_length :
    presentation.rotationCount =
      presentation.rotationEnumeration.values.length := by
  unfold rotationCount rotationEnumeration
    FiniteOddFieldPresentation.RotationEnumeration.values rotations
  rw [Map.length_map]
  calc
    presentation.projectiveCountWhere
          (fun raw => (presentation.certifyNonNull raw).isSome) =
        (presentation.projectiveRepresentatives.filter
          (fun raw => (presentation.certifyNonNull raw).isSome)).length :=
      presentation.projectiveCountWhere_eq_length_filter _
    _ = presentation.nonNullProjectiveRepresentatives.length := by
      unfold FiniteOddFieldPresentation.nonNullProjectiveRepresentatives
      exact (CountWhere.length_filterMap_eq_count_isSome
        presentation.projectiveRepresentatives
        presentation.certifyNonNull).symm

/-- Homogeneous Boolean test for a non-null projective point of prescribed half spread. -/
@[expose] public def halfSpreadAccepted (value : K) (raw : Projective.Basic.Proportion K) : Bool := by
  letI : DecidableEq K := presentation.eqDecidable
  exact decide (raw.norm ≠ 0) &&
    decide (raw.vector.quadrance = value * raw.norm)

/-- The scalar whose square class determines the sign of a non-endpoint half-spread fiber in Problem 69. -/
@[expose] public def halfSpreadDiscriminant (value : K) : K :=
  -value * (1 - value)

/-- On scalar-zero proportions, half-turn acceptance is exactly non-null norm acceptance. -/
private theorem halfSpreadAccepted_one_of_scalar_zero (raw : Projective.Basic.Proportion K)
    (scalarZero : raw.scalar = 0) :
    presentation.halfSpreadAccepted 1 raw =
      presentation.normNonzeroAccepted raw := by
  letI : DecidableEq K := presentation.eqDecidable
  have normQuadrance : raw.norm = raw.vector.quadrance := by
    unfold Proportion.norm
    rw [scalarZero]
    ring1
  unfold halfSpreadAccepted FiniteOddFieldPresentation.normNonzeroAccepted
  rw [normQuadrance]
  have equation : raw.vector.quadrance = (1 : K) * raw.vector.quadrance := by
    ring1
  rw [decide_eq_true equation, Bool.and_true]

/-- A proportion with nonzero scalar coordinate is rejected by the half-turn test. -/
private theorem halfSpreadAccepted_one_of_scalar_nonzero
    (raw : Projective.Basic.Proportion K) (scalarNonzero : raw.scalar ≠ 0) :
    presentation.halfSpreadAccepted 1 raw = false := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold halfSpreadAccepted
  apply Bool.eq_false_iff.mpr
  intro accepted
  have acceptedParts := Purelib.Data.Bool.Decide.and_true_iff _ _ |>.mp accepted
  have equation := of_decide_eq_true acceptedParts.2
  have normEquation : raw.norm = raw.vector.quadrance := by
    calc
      raw.norm = (1 : K) * raw.norm := by ring1
      _ = raw.vector.quadrance := equation.symm
  have scalarSquareZero : raw.scalar ^ 2 = 0 := by
    unfold Proportion.norm at normEquation
    calc
      raw.scalar ^ 2 =
          (raw.scalar ^ 2 + raw.vector.quadrance) -
            raw.vector.quadrance := by ring1
      _ = raw.vector.quadrance - raw.vector.quadrance :=
        congrArg (fun norm => norm - raw.vector.quadrance) normEquation
      _ = 0 := by ring1
  have scalarSquareNonzero : raw.scalar ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      ExplicitField.mul_ne_zero scalarNonzero scalarNonzero
  exact scalarSquareNonzero scalarSquareZero

/-- Efficient executable half-spread fiber count. -/
@[expose] public def halfSpreadFiberCount (value : K) : Nat :=
  presentation.projectiveCountWhere (presentation.halfSpreadAccepted value)

/-- The half-turn fiber is precisely the non-null projective plane at infinity, decomposed into its three
first-nonzero-coordinate charts. -/
theorem halfSpreadFiberCount_one_eq_infinityCounts :
    presentation.halfSpreadFiberCount 1 =
      presentation.infinityTNonNullCount +
        presentation.infinityRNonNullCount + 1 := by
  letI : DecidableEq K := presentation.eqDecidable
  have affineZero :
      presentation.vectorCountWhere (fun vector =>
        presentation.halfSpreadAccepted 1 ⟨1, vector⟩) = 0 := by
    apply (FiniteOddFieldPresentation.vectorCountWhere_eq_zero_of_reject presentation)
    intro vector _
    exact presentation.halfSpreadAccepted_one_of_scalar_nonzero
      ⟨1, vector⟩ (FiniteOddFieldPresentation.one_ne_zero presentation)
  have infinityTEqual :
      (presentation.carrier.map fun r =>
        presentation.infinityTSliceCountWhere r
          (presentation.halfSpreadAccepted 1)).foldr Nat.add 0 =
        presentation.infinityTNonNullCount := by
    unfold FiniteOddFieldPresentation.infinityTNonNullCount FiniteOddFieldPresentation.infinityTSliceCountWhere
      FiniteOddFieldPresentation.scalarPairs
    rw [CountWhere.listCountWhere_flatMap]
    apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
    apply Map.map_congr_left
    intro r _
    rw [CountWhere.listCountWhere_map, CountWhere.listCountWhere_map]
    apply CountWhere.listCountWhere_congr
    intro s _
    exact presentation.halfSpreadAccepted_one_of_scalar_zero
      ⟨0, ⟨1, r, s⟩⟩ rfl
  have infinityREqual :
      CountWhere.listCountWhere
          (presentation.carrier.map fun s =>
            (⟨0, ⟨0, 1, s⟩⟩ : Projective.Basic.Proportion K))
          (presentation.halfSpreadAccepted 1) =
        presentation.infinityRNonNullCount := by
    unfold FiniteOddFieldPresentation.infinityRNonNullCount
    rw [CountWhere.listCountWhere_map]
    apply CountWhere.listCountWhere_congr
    intro s _
    exact presentation.halfSpreadAccepted_one_of_scalar_zero
      ⟨0, ⟨0, 1, s⟩⟩ rfl
  have infinitySAccepted :
      presentation.halfSpreadAccepted 1 FiniteOddFieldPresentation.infinitySRepresentative = true := by
    rw [presentation.halfSpreadAccepted_one_of_scalar_zero
      FiniteOddFieldPresentation.infinitySRepresentative rfl]
    unfold FiniteOddFieldPresentation.normNonzeroAccepted
    have normEquation :
        Proportion.norm (FiniteOddFieldPresentation.infinitySRepresentative : Projective.Basic.Proportion K) = 1 := by
      unfold FiniteOddFieldPresentation.infinitySRepresentative Proportion.norm Coordinates3.Vector.quadrance
        Coordinates3.Vector.dot
      ring1
    rw [normEquation]
    apply decide_eq_true
    exact FiniteOddFieldPresentation.one_ne_zero presentation
  unfold halfSpreadFiberCount FiniteOddFieldPresentation.projectiveCountWhere
  rw [affineZero, infinityTEqual, infinityREqual, infinitySAccepted]
  rw [if_pos rfl]
  change 0 + presentation.infinityTNonNullCount +
      presentation.infinityRNonNullCount + 1 = _
  rw [Nat.zero_add]

/-- The projective half-turn fiber also has `q²` elements. The proof counts all three charts and handles the
split/nonsplit conic at infinity explicitly. -/
theorem halfSpreadFiberCount_one :
    presentation.halfSpreadFiberCount 1 =
      presentation.carrier.length * presentation.carrier.length := by
  have minusOneNonzero : (-1 : K) ≠ 0 := by
    intro minusOneZero
    apply FiniteOddFieldPresentation.one_ne_zero presentation
    calc
      (1 : K) = -(-1) := by ring1
      _ = 0 := by rw [minusOneZero]; ring1
  rw [presentation.halfSpreadFiberCount_one_eq_infinityCounts]
  cases presentation.classifyMinusOne with
  | square root rootSquare =>
      have tPartition :=
        presentation.infinityTNonNullCount_add_twoSquareCount_minus_one
      have rPartition :=
        presentation.infinityRNonNullCount_add_squareRootCount_minus_one
      rw [presentation.twoSquareCount_of_minus_one_square_of_ne_zero
          (-1) root rootSquare minusOneNonzero] at tPartition
      rw [presentation.squareRootCount_of_nonzero_square
          (-1) root minusOneNonzero rootSquare] at rPartition
      have rPlusOne : presentation.infinityRNonNullCount + 1 =
          presentation.carrier.length - 1 := by
        calc
          presentation.infinityRNonNullCount + 1 =
              ((presentation.infinityRNonNullCount + 1) + 1) - 1 :=
            (Purelib.Data.Nat.Subtraction.add_sub_cancel_right
              (presentation.infinityRNonNullCount + 1) 1).symm
          _ = (presentation.infinityRNonNullCount + 2) - 1 := by
            exact congrArg (fun count => count - 1)
              (Nat.add_assoc presentation.infinityRNonNullCount 1 1)
          _ = presentation.carrier.length - 1 :=
            congrArg (fun count => count - 1) rPartition
      calc
        presentation.infinityTNonNullCount +
            presentation.infinityRNonNullCount + 1 =
          presentation.infinityTNonNullCount +
            (presentation.infinityRNonNullCount + 1) :=
              Nat.add_assoc _ _ _
        _ = presentation.infinityTNonNullCount +
            (presentation.carrier.length - 1) :=
          congrArg (Nat.add presentation.infinityTNonNullCount) rPlusOne
        _ = presentation.carrier.length * presentation.carrier.length :=
          tPartition
  | nonsquare minusOneNoRoot =>
      have tPartition :=
        presentation.infinityTNonNullCount_add_twoSquareCount_minus_one
      have rPartition :=
        presentation.infinityRNonNullCount_add_squareRootCount_minus_one
      rw [presentation.twoSquareCount_of_minus_one_nonsquare_of_ne_zero
          (-1) minusOneNonzero minusOneNoRoot] at tPartition
      rw [presentation.squareRootCount_of_nonsquare
          (-1) minusOneNoRoot] at rPartition
      have rCount : presentation.infinityRNonNullCount =
          presentation.carrier.length := by
        calc
          presentation.infinityRNonNullCount =
              presentation.infinityRNonNullCount + 0 :=
            (Nat.add_zero _).symm
          _ = presentation.carrier.length := rPartition
      calc
        presentation.infinityTNonNullCount +
            presentation.infinityRNonNullCount + 1 =
          presentation.infinityTNonNullCount +
            (presentation.infinityRNonNullCount + 1) :=
              Nat.add_assoc _ _ _
        _ = presentation.infinityTNonNullCount +
            (presentation.carrier.length + 1) := by rw [rCount]
        _ = presentation.carrier.length * presentation.carrier.length :=
          tPartition

/-- The non-null projective rotation carrier is the affine non-null chart plus the three non-null charts at infinity. -/
theorem rotationCount_eq_affineNonNullCount_add_infinityCounts :
    presentation.rotationCount = presentation.affineNonNullCount +
      presentation.infinityTNonNullCount +
        presentation.infinityRNonNullCount + 1 := by
  letI : DecidableEq K := presentation.eqDecidable
  have predicateEqual := presentation.projectiveCountWhere_congr
    (fun raw => (presentation.certifyNonNull raw).isSome)
    presentation.normNonzeroAccepted
    (FiniteOddFieldPresentation.certifyNonNull_isSome_eq_normNonzeroAccepted presentation)
  have infinityTEqual :
      (presentation.carrier.map fun r =>
        presentation.infinityTSliceCountWhere r
          presentation.normNonzeroAccepted).foldr Nat.add 0 =
        presentation.infinityTNonNullCount := by
    unfold FiniteOddFieldPresentation.infinityTNonNullCount FiniteOddFieldPresentation.infinityTSliceCountWhere
      FiniteOddFieldPresentation.scalarPairs
    rw [CountWhere.listCountWhere_flatMap]
    apply congrArg (fun counts : List Nat => counts.foldr Nat.add 0)
    apply Map.map_congr_left
    intro r _
    rw [CountWhere.listCountWhere_map, CountWhere.listCountWhere_map]
  have infinityREqual :
      CountWhere.listCountWhere
          (presentation.carrier.map fun s =>
            (⟨0, ⟨0, 1, s⟩⟩ : Projective.Basic.Proportion K))
          presentation.normNonzeroAccepted =
        presentation.infinityRNonNullCount := by
    unfold FiniteOddFieldPresentation.infinityRNonNullCount
    rw [CountWhere.listCountWhere_map]
  have infinitySAccepted :
      presentation.normNonzeroAccepted FiniteOddFieldPresentation.infinitySRepresentative = true := by
    unfold FiniteOddFieldPresentation.normNonzeroAccepted
    have normEquation :
        Proportion.norm (FiniteOddFieldPresentation.infinitySRepresentative : Projective.Basic.Proportion K) = 1 := by
      unfold FiniteOddFieldPresentation.infinitySRepresentative Proportion.norm Coordinates3.Vector.quadrance
        Coordinates3.Vector.dot
      ring1
    rw [normEquation]
    exact decide_eq_true (FiniteOddFieldPresentation.one_ne_zero presentation)
  calc
    presentation.rotationCount =
        presentation.projectiveCountWhere
          presentation.normNonzeroAccepted := predicateEqual
    _ = presentation.affineNonNullCount +
        presentation.infinityTNonNullCount +
          presentation.infinityRNonNullCount + 1 := by
      unfold FiniteOddFieldPresentation.projectiveCountWhere FiniteOddFieldPresentation.affineNonNullCount
      rw [infinityTEqual, infinityREqual, infinitySAccepted, if_pos rfl]

/-- The kernel has half the total number of rotations. -/
@[expose] public def quadranceClassKernelCount : Nat := by
  exact presentation.projectiveCountWhere fun raw =>
    presentation.normNonzeroAccepted raw && (FiniteOddFieldPresentation.isSquare presentation) raw.norm

/-- The efficient kernel counter equals the actual certified kernel-list length. -/
theorem quadranceClassKernelCount_eq_length :
    presentation.quadranceClassKernelCount =
      presentation.quadranceClassKernel.length := by
  unfold FiniteOddFieldPresentation.quadranceClassKernelCount quadranceClassKernel
    FiniteOddFieldPresentation.nonNullProjectiveRepresentatives
  rw [presentation.projectiveCountWhere_eq_length_filter]
  exact (FiniteOddFieldPresentation.certifiedSquareFilter_length_eq_rawCount
    (presentation := presentation)
    presentation.projectiveRepresentatives).symm

/-- Twice the kernel-list length equals the full rotation count. -/
theorem quadranceClassKernel_twice_eq_rotationCount :
    presentation.quadranceClassKernel.length +
        presentation.quadranceClassKernel.length =
      presentation.rotationCount := by
  calc
    presentation.quadranceClassKernel.length +
        presentation.quadranceClassKernel.length =
      presentation.quadranceClassKernel.length +
        presentation.quadranceClassNontrivialFiber.length := by
          rw [presentation.quadranceClassKernel_length_eq_nontrivialFiber_length]
    _ = presentation.nonNullProjectiveRepresentatives.length :=
      presentation.quadranceClassFibers_partition
    _ = presentation.rotationEnumeration.values.length := by
      unfold rotationEnumeration FiniteOddFieldPresentation.RotationEnumeration.values
        rotations
      rw [Map.length_map]
    _ = presentation.rotationCount :=
      presentation.rotationCount_eq_rotationEnumeration_length.symm

/-- The complement of a scalar different from one is nonzero. -/
public theorem one_sub_ne_zero_of_ne_one_counting {value : K}
    (notOne : value ≠ 1) : 1 - value ≠ 0 := by
  intro differenceZero
  apply notOne
  calc
    value = 1 - (1 - value) := by ring1
    _ = 1 := by rw [differenceZero]; ring1

/-- Minus one is nonzero in the displayed odd finite field. -/
public theorem minus_one_ne_zero_counting
    (presentation : Presentation.FiniteOddFieldPresentation K) : (-1 : K) ≠ 0 := by
  intro minusOneZero
  apply FiniteOddFieldPresentation.one_ne_zero presentation
  calc
    (1 : K) = -(-1) := by ring1
    _ = 0 := by rw [minusOneZero]; ring1

/-- Solve a scalar multiplication equality by its nonzero denominator. -/
private theorem eq_div_of_mul_eq_counting {left right denominator : K}
    (denominatorNonzero : denominator ≠ 0)
    (product : left * denominator = right) :
    left = right / denominator := by
  have cancel := ExplicitField.mul_inv_cancel denominator
    denominatorNonzero
  rw [ExplicitField.div_eq_mul_inv]
  calc
    left = left * (denominator * denominator⁻¹) := by rw [cancel, mul_one]
    _ = (left * denominator) * denominator⁻¹ := by ring1
    _ = right * denominator⁻¹ := by rw [product]

/-- A non-null raw proportion is accepted at exactly one displayed half-spread value; a null one is never accepted. -/
private theorem halfSpreadAccepted_count_over_carrier
    (raw : Projective.Basic.Proportion K) :
    CountWhere.listCountWhere presentation.carrier (fun value =>
        presentation.halfSpreadAccepted value raw) =
      if presentation.normNonzeroAccepted raw then 1 else 0 := by
  letI : DecidableEq K := presentation.eqDecidable
  cases presentation.eqDecidable raw.norm 0 with
  | isTrue normZero =>
      have normRejected : presentation.normNonzeroAccepted raw = false := by
        unfold FiniteOddFieldPresentation.normNonzeroAccepted
        exact decide_eq_false (fun normNonzero => normNonzero normZero)
      have allRejected : ∀ value ∈ presentation.carrier,
          presentation.halfSpreadAccepted value raw = false := by
        intro value _
        unfold halfSpreadAccepted
        rw [decide_eq_false (fun normNonzero => normNonzero normZero),
          Bool.false_and]
      rw [CountWhere.listCountWhere_eq_zero_of_reject presentation.carrier
        (fun value => presentation.halfSpreadAccepted value raw) allRejected,
        normRejected]
      rfl
  | isFalse normNonzero =>
      let target := raw.vector.quadrance / raw.norm
      have normAccepted : presentation.normNonzeroAccepted raw = true := by
        unfold FiniteOddFieldPresentation.normNonzeroAccepted
        exact decide_eq_true normNonzero
      have predicateEqual : ∀ value ∈ presentation.carrier,
          presentation.halfSpreadAccepted value raw =
            decide (value = target) := by
        intro value _
        unfold halfSpreadAccepted
        rw [decide_eq_true normNonzero, Bool.true_and]
        apply Purelib.Data.Bool.Decide.eq_of_true_iff
        constructor
        · intro accepted
          apply decide_eq_true
          exact eq_div_of_mul_eq_counting normNonzero
            (of_decide_eq_true accepted).symm
        · intro accepted
          apply decide_eq_true
          have multiplied := congrArg (fun scalar => scalar * raw.norm)
            (of_decide_eq_true accepted)
          change value * raw.norm = target * raw.norm at multiplied
          unfold target at multiplied
          rw [ExplicitField.div_mul_cancel raw.vector.quadrance
            normNonzero] at multiplied
          exact multiplied.symm
      have countEqual := CountWhere.listCountWhere_congr presentation.carrier
        (fun value => presentation.halfSpreadAccepted value raw)
        (fun value => decide (value = target)) predicateEqual
      rw [countEqual,
        CountWhere.listCountWhere_eq_one_of_eq_target presentation.eqDecidable
          presentation.carrier presentation.carrierNodup target
          (presentation.carrierComplete target),
        normAccepted]
      rw [if_pos rfl]

/-- The displayed half-spread fibers form a genuine partition of the rotation carrier. Their finite sum therefore agrees
with the independently counted group order. -/
theorem halfSpreadFiberCounts_sum :
    (presentation.carrier.map presentation.halfSpreadFiberCount).foldr
        Nat.add 0 = presentation.rotationCount := by
  have countsAsLists :
      presentation.carrier.map presentation.halfSpreadFiberCount =
        presentation.carrier.map fun value =>
          CountWhere.listCountWhere presentation.projectiveRepresentatives
            (presentation.halfSpreadAccepted value) := by
    apply Map.map_congr_left
    intro value _
    unfold halfSpreadFiberCount
    exact presentation.projectiveCountWhere_eq_length_filter _
  have swapped := CountWhere.listCountWhere_sum_swap presentation.carrier
    presentation.projectiveRepresentatives
    (fun value raw => presentation.halfSpreadAccepted value raw)
  have rawCounts :
      presentation.projectiveRepresentatives.map (fun raw =>
          CountWhere.listCountWhere presentation.carrier (fun value =>
            presentation.halfSpreadAccepted value raw)) =
        presentation.projectiveRepresentatives.map (fun raw =>
          if presentation.normNonzeroAccepted raw then 1 else 0) := by
    apply Map.map_congr_left
    intro raw _
    exact presentation.halfSpreadAccepted_count_over_carrier raw
  have rotationAsNorm : presentation.rotationCount =
      presentation.projectiveCountWhere
        presentation.normNonzeroAccepted := by
    unfold rotationCount
    exact presentation.projectiveCountWhere_congr
      (fun raw => (presentation.certifyNonNull raw).isSome)
      presentation.normNonzeroAccepted
      (FiniteOddFieldPresentation.certifyNonNull_isSome_eq_normNonzeroAccepted presentation)
  calc
    (presentation.carrier.map presentation.halfSpreadFiberCount).foldr
        Nat.add 0 =
      (presentation.carrier.map fun value =>
        CountWhere.listCountWhere presentation.projectiveRepresentatives
          (presentation.halfSpreadAccepted value)).foldr Nat.add 0 := by
      rw [countsAsLists]
    _ = (presentation.projectiveRepresentatives.map fun raw =>
        CountWhere.listCountWhere presentation.carrier (fun value =>
          presentation.halfSpreadAccepted value raw)).foldr Nat.add 0 := swapped
    _ = (presentation.projectiveRepresentatives.map fun raw =>
        if presentation.normNonzeroAccepted raw then 1 else 0).foldr
          Nat.add 0 := by rw [rawCounts]
    _ = CountWhere.listCountWhere presentation.projectiveRepresentatives
        presentation.normNonzeroAccepted :=
      (CountWhere.listCountWhere_eq_foldr_indicators
        presentation.projectiveRepresentatives
        presentation.normNonzeroAccepted).symm
    _ = presentation.projectiveCountWhere
        presentation.normNonzeroAccepted :=
      presentation.projectiveCountWhere_eq_length_filter
        presentation.normNonzeroAccepted |>.symm
    _ = presentation.rotationCount := rotationAsNorm.symm

/-- The paper's discriminant differs from `(-1) * h/(1-h)` by the displayed nonzero square `(1-h)²`. -/
theorem halfSpreadDiscriminant_affine_factorization (value : K)
    (notOne : value ≠ 1) :
    halfSpreadDiscriminant value =
      ((-1 : K) * (value / (1 - value))) * (1 - value) ^ 2 := by
  have complementNonzero :=
    one_sub_ne_zero_of_ne_one_counting notOne
  have complementCancel := ExplicitField.mul_inv_cancel
    (1 - value) complementNonzero
  unfold halfSpreadDiscriminant
  rw [ExplicitField.div_eq_mul_inv]
  symm
  calc
    ((-1 : K) * (value * (1 - value)⁻¹)) * (1 - value) ^ 2 =
        (-value * (1 - value)) *
          ((1 - value) * (1 - value)⁻¹) := by ring1
    _ = -value * (1 - value) := by rw [complementCancel, mul_one]

/-- Away from the half-turn value, the homogeneous half-spread fiber is the affine ternary quadric `Q(v) = value / (1 -
value)`. -/
theorem halfSpreadFiberCount_eq_vectorQuadranceCount (value : K)
    (notOne : value ≠ 1) :
    presentation.halfSpreadFiberCount value =
      presentation.vectorQuadranceCount (value / (1 - value)) := by
  letI : DecidableEq K := presentation.eqDecidable
  apply presentation.projectiveCountWhere_eq_vectorCountWhere_of_infinity_rejected
  · intro vector
    unfold halfSpreadAccepted
    change
      (decide ((1 : K) ^ 2 + vector.quadrance ≠ 0) &&
        decide (vector.quadrance =
          value * ((1 : K) ^ 2 + vector.quadrance))) =
        decide (vector.quadrance = value / (1 - value))
    apply Purelib.Data.Bool.Decide.eq_of_true_iff
    constructor
    · intro accepted
      apply decide_eq_true
      have acceptedParts := Purelib.Data.Bool.Decide.and_true_iff _ _ |>.mp accepted
      have equation := of_decide_eq_true acceptedParts.2
      apply eq_div_of_mul_eq_counting
        (one_sub_ne_zero_of_ne_one_counting
          notOne)
      calc
        vector.quadrance * (1 - value) =
            vector.quadrance - value * vector.quadrance := by ring1
        _ = value * ((1 : K) ^ 2 + vector.quadrance) -
            value * vector.quadrance :=
          congrArg (fun left => left - value * vector.quadrance) equation
        _ = value := by ring1
    · intro accepted
      have quadranceEquation := of_decide_eq_true accepted
      have complementNonzero :=
        one_sub_ne_zero_of_ne_one_counting
        notOne
      have complementCancel := ExplicitField.mul_inv_cancel
        (1 - value) complementNonzero
      have normEquation :
          (1 : K) ^ 2 + vector.quadrance = (1 - value)⁻¹ := by
        rw [quadranceEquation, ExplicitField.div_eq_mul_inv]
        calc
          1 ^ 2 + value * (1 - value)⁻¹ =
              (1 - value) * (1 - value)⁻¹ +
                value * (1 - value)⁻¹ := by rw [complementCancel]; ring1
          _ = (1 - value + value) * (1 - value)⁻¹ := by ring1
          _ = (1 - value)⁻¹ := by ring1
      apply Purelib.Data.Bool.Decide.and_true_iff _ _ |>.mpr
      constructor
      · apply decide_eq_true
        rw [normEquation]
        exact ExplicitField.inv_ne_zero complementNonzero
      · apply decide_eq_true
        rw [normEquation, quadranceEquation,
          ExplicitField.div_eq_mul_inv]
  · intro raw scalarZero
    unfold halfSpreadAccepted
    apply Bool.eq_false_iff.mpr
    intro accepted
    have acceptedParts := Purelib.Data.Bool.Decide.and_true_iff _ _ |>.mp accepted
    have normNonzero := of_decide_eq_true acceptedParts.1
    have equation := of_decide_eq_true acceptedParts.2
    have normQuadrance : raw.norm = raw.vector.quadrance := by
      unfold Proportion.norm
      rw [scalarZero]
      ring1
    have equationQuadrance :
        raw.vector.quadrance = value * raw.vector.quadrance := by
      calc
        raw.vector.quadrance = value * raw.norm := equation
        _ = value * raw.vector.quadrance := by rw [normQuadrance]
    have productZero :
        (1 - value) * raw.vector.quadrance = 0 := by
      calc
        (1 - value) * raw.vector.quadrance =
            raw.vector.quadrance - value * raw.vector.quadrance := by ring1
        _ = value * raw.vector.quadrance -
            value * raw.vector.quadrance :=
          congrArg (fun left => left - value * raw.vector.quadrance)
            equationQuadrance
        _ = 0 := by ring1
    have quadranceNonzero : raw.vector.quadrance ≠ 0 := by
      rw [← normQuadrance]
      exact normNonzero
    have productNonzero := ExplicitField.mul_ne_zero
      (one_sub_ne_zero_of_ne_one_counting
        notOne) quadranceNonzero
    exact productNonzero productZero

/-- A non-null scalar-zero proportion has homogeneous half-spread quotient one. -/
private theorem halfSpreadQuotient_eq_one_of_scalar_zero
    (proportion : Projective.Basic.NonNullProportion K)
    (scalarZero : proportion.scalar = 0) :
    proportion.vector.quadrance / proportion.toProportion.norm = 1 := by
  have normEq : proportion.toProportion.norm =
      proportion.vector.quadrance := by
    unfold Proportion.norm
    rw [scalarZero]
    ring1
  have quadranceNonzero : proportion.vector.quadrance ≠ 0 := by
    intro quadranceZero
    apply proportion.normNonzero
    rw [normEq, quadranceZero]
  rw [normEq, ExplicitField.div_eq_mul_inv,
    ExplicitField.mul_inv_cancel _ quadranceNonzero]

/-- A canonical representative in a non-half-turn fiber is necessarily in the scalar-one affine chart. -/
theorem halfSpreadFiber_scalar_eq_one {value : K}
    (notOne : value ≠ 1) (proportion : Projective.Basic.NonNullProportion K)
    (member : proportion ∈ presentation.halfSpreadFiber value) :
    proportion.scalar = 1 := by
  letI : DecidableEq K := presentation.eqDecidable
  have filtered := Filter.mem_filter.mp member
  have fiberEq := of_decide_eq_true filtered.2
  have rawMember := presentation.raw_mem_of_nonNull_mem filtered.1
  have rejectScalarZero (scalarZero : proportion.scalar = 0) : False := by
    apply notOne
    calc
      value = proportion.vector.quadrance /
          proportion.toProportion.norm := fiberEq.symm
      _ = 1 := halfSpreadQuotient_eq_one_of_scalar_zero
        proportion scalarZero
  rcases presentation.projectiveRepresentatives_cases rawMember with
      ⟨vector, rawEq⟩ |
      ⟨r, s, rawEq⟩ |
      ⟨s, rawEq⟩ | rawEq
  · exact congrArg Proportion.scalar rawEq
  · apply False.elim
    apply rejectScalarZero
    exact congrArg Proportion.scalar rawEq
  · apply False.elim
    apply rejectScalarZero
    exact congrArg Proportion.scalar rawEq
  · apply False.elim
    apply rejectScalarZero
    exact congrArg Proportion.scalar rawEq

/-- Elementwise homogeneous-to-affine reduction for a non-half-turn fiber. -/
theorem halfSpreadFiber_quadrance_eq_affineValue {value : K}
    (notOne : value ≠ 1) (proportion : Projective.Basic.NonNullProportion K)
    (member : proportion ∈ presentation.halfSpreadFiber value) :
    proportion.vector.quadrance = value / (1 - value) := by
  letI : DecidableEq K := presentation.eqDecidable
  have filtered := Filter.mem_filter.mp member
  have fiberEq := of_decide_eq_true filtered.2
  have scalarOne := presentation.halfSpreadFiber_scalar_eq_one notOne
    proportion member
  have normEq : proportion.toProportion.norm =
      1 + proportion.vector.quadrance := by
    unfold Proportion.norm
    rw [scalarOne]
    ring1
  have dividedCancel := ExplicitField.div_mul_cancel
    proportion.vector.quadrance proportion.normNonzero
  have quadranceEqProduct : proportion.vector.quadrance =
      value * proportion.toProportion.norm := by
    calc
      proportion.vector.quadrance =
          (proportion.vector.quadrance /
            proportion.toProportion.norm) *
              proportion.toProportion.norm := dividedCancel.symm
      _ = value * proportion.toProportion.norm := by rw [fiberEq]
  have product : proportion.vector.quadrance * (1 - value) = value := by
    calc
      proportion.vector.quadrance * (1 - value) =
          proportion.vector.quadrance -
            value * proportion.vector.quadrance := by ring1
      _ = value * proportion.toProportion.norm -
            value * proportion.vector.quadrance := by rw [quadranceEqProduct]
      _ = value * (1 + proportion.vector.quadrance) -
            value * proportion.vector.quadrance := by rw [normEq]
      _ = value := by ring1
  exact eq_div_of_mul_eq_counting
    (one_sub_ne_zero_of_ne_one_counting notOne)
      product

/-- The affine quadric at h divided by one minus h belongs to the h half-spread fiber when h differs from one. -/
public theorem affineQuadric_member_halfSpreadFiber {value : K}
    (notOne : value ≠ 1) (proportion : Projective.Basic.NonNullProportion K)
    (member : proportion ∈ presentation.affineQuadricRepresentatives
      (value / (1 - value))) :
    proportion ∈ presentation.halfSpreadFiber value := by
  letI : DecidableEq K := presentation.eqDecidable
  have classified :=
    (presentation.mem_affineQuadricRepresentatives_iff
      (value / (1 - value)) proportion).1 member
  have normEq : proportion.toProportion.norm =
      1 + proportion.vector.quadrance := by
    unfold Proportion.norm
    rw [classified.2.1]
    ring1
  have complementNonzero :=
    one_sub_ne_zero_of_ne_one_counting notOne
  have quotientCancel := ExplicitField.div_mul_cancel value
    complementNonzero
  have quadranceComplement :
      proportion.vector.quadrance * (1 - value) = value := by
    rw [classified.2.2]
    exact quotientCancel
  have valueTimesNorm : value * proportion.toProportion.norm =
      proportion.vector.quadrance := by
    rw [normEq]
    calc
      value * (1 + proportion.vector.quadrance) =
          value + value * proportion.vector.quadrance := by ring1
      _ = proportion.vector.quadrance * (1 - value) +
            value * proportion.vector.quadrance := by
          rw [quadranceComplement]
      _ = proportion.vector.quadrance := by ring1
  have quotientEq := eq_div_of_mul_eq_counting
    proportion.normNonzero
    valueTimesNorm
  unfold halfSpreadFiber
  apply Filter.mem_filter.mpr
  exact ⟨classified.1, decide_eq_true quotientEq.symm⟩

/-- Explicit finite-list bijection from every non-half-turn rotation fiber to the independently filtered affine quadric
`Q(v) = h/(1-h)`. The maps are identity on the cached normalized representatives; the proof establishes that the two
independently defined lists have exactly the same members. -/
@[expose] public def affineHalfSpreadFiberBijection (value : K) (notOne : value ≠ 1) :
    Bijection.ListBijection (presentation.halfSpreadFiber value)
      (presentation.affineQuadricRepresentatives
        (value / (1 - value))) where
  forward := fun proportion => proportion
  backward := fun proportion => proportion
  forward_mem := by
    intro proportion member
    apply (presentation.mem_affineQuadricRepresentatives_iff
      (value / (1 - value)) proportion).2
    have filtered := Filter.mem_filter.mp member
    exact
      ⟨filtered.1,
        presentation.halfSpreadFiber_scalar_eq_one notOne proportion member,
        presentation.halfSpreadFiber_quadrance_eq_affineValue notOne
          proportion member⟩
  backward_mem := fun proportion member =>
    presentation.affineQuadric_member_halfSpreadFiber notOne proportion member
  backward_forward := by intro _ _; rfl
  forward_backward := by intro _ _; rfl

/-- In the half-turn fiber, the homogeneous equation forces scalar coordinate zero, so the representative is an axis in
the projective plane at infinity. -/
theorem halfSpreadFiber_one_scalar_eq_zero
    (proportion : Projective.Basic.NonNullProportion K)
    (member : proportion ∈ presentation.halfSpreadFiber 1) :
    proportion.scalar = 0 := by
  letI : DecidableEq K := presentation.eqDecidable
  have filtered := Filter.mem_filter.mp member
  have fiberEq := of_decide_eq_true filtered.2
  have dividedCancel := ExplicitField.div_mul_cancel
    proportion.vector.quadrance proportion.normNonzero
  have quadranceEqNorm : proportion.vector.quadrance =
      proportion.toProportion.norm := by
    calc
      proportion.vector.quadrance =
          (proportion.vector.quadrance /
            proportion.toProportion.norm) *
              proportion.toProportion.norm := dividedCancel.symm
      _ = 1 * proportion.toProportion.norm := by rw [fiberEq]
      _ = proportion.toProportion.norm := by ring1
  have scalarSquareZero : proportion.scalar ^ 2 = 0 := by
    calc
      proportion.scalar ^ 2 = proportion.toProportion.norm -
          proportion.vector.quadrance := by
        unfold Proportion.norm
        ring1
      _ = proportion.vector.quadrance -
          proportion.vector.quadrance := by rw [← quadranceEqNorm]
      _ = 0 := by ring1
  exact Quadratic.Pair.Coordinates.eq_zero_of_square_eq_zero presentation.eqDecidable
    proportion.scalar scalarSquareZero

/-- A certified non-null projective axis belongs to the half-turn fiber. -/
public theorem projectiveAxis_member_halfSpreadFiber_one
    (proportion : Projective.Basic.NonNullProportion K)
    (member : proportion ∈
      presentation.projectiveNonNullAxisRepresentatives) :
    proportion ∈ presentation.halfSpreadFiber 1 := by
  letI : DecidableEq K := presentation.eqDecidable
  have classified :=
    (presentation.mem_projectiveNonNullAxisRepresentatives_iff
      proportion).1 member
  unfold halfSpreadFiber
  apply Filter.mem_filter.mpr
  exact
    ⟨classified.1,
      decide_eq_true
        (halfSpreadQuotient_eq_one_of_scalar_zero
          proportion classified.2)⟩

/-- Explicit bijection between the half-turn stratum and the independently listed non-null projective axes (the
projective plane at infinity with its null conic removed). -/
@[expose] public def halfTurnProjectiveAxisBijection :
    Bijection.ListBijection (presentation.halfSpreadFiber 1)
      presentation.projectiveNonNullAxisRepresentatives where
  forward := fun proportion => proportion
  backward := fun proportion => proportion
  forward_mem := by
    intro proportion member
    apply (presentation.mem_projectiveNonNullAxisRepresentatives_iff
      proportion).2
    have filtered := Filter.mem_filter.mp member
    exact
      ⟨filtered.1,
        presentation.halfSpreadFiber_one_scalar_eq_zero proportion member⟩
  backward_mem := fun proportion member =>
    presentation.projectiveAxis_member_halfSpreadFiber_one proportion member
  backward_forward := by intro _ _; rfl
  forward_backward := by intro _ _; rfl

/-- Membership in the projective fiber computes the same half-spread value on the represented rotation. -/
theorem halfSpread_rotation_eq_value_of_mem (value : K)
    (proportion : Projective.Basic.NonNullProportion K)
    (member : proportion ∈ presentation.halfSpreadFiber value) :
    Spread.halfSpread (NonNullProportion.rotation proportion) = value := by
  letI : DecidableEq K := presentation.eqDecidable
  have filtered := Filter.mem_filter.mp member
  rw [NonNullProportion.halfSpread_rotation proportion
    presentation.twoNonzero]
  exact of_decide_eq_true filtered.2

/-- Under the zero-fiber affine-quadric bijection, the identity is exactly the quadric origin. -/
theorem zeroFiber_rotation_identity_iff_vector_eq_zero
    (proportion : Projective.Basic.NonNullProportion K)
    (member : proportion ∈ presentation.halfSpreadFiber 0) :
    (NonNullProportion.rotation proportion).matrix = Matrix3.identity ↔
      proportion.vector = Coordinates3.Vector.zero := by
  letI : DecidableEq K := presentation.eqDecidable
  have zeroNotOne : (0 : K) ≠ 1 := by
    intro zeroOne
    exact FiniteOddFieldPresentation.one_ne_zero presentation zeroOne.symm
  have scalarOne := presentation.halfSpreadFiber_scalar_eq_one zeroNotOne
    proportion member
  have scalarNonzero : proportion.scalar ≠ 0 := by
    rw [scalarOne]
    exact FiniteOddFieldPresentation.one_ne_zero presentation
  have oneInverse : (1 : K)⁻¹ = 1 := by
    have cancel := ExplicitField.mul_inv_cancel (1 : K)
      (FiniteOddFieldPresentation.one_ne_zero presentation)
    simpa only [_root_.one_mul] using cancel
  have vectorNull : proportion.vector.quadrance = 0 := by
    simpa only [ExplicitField.zero_div] using
      presentation.halfSpreadFiber_quadrance_eq_affineValue zeroNotOne
        proportion member
  let vectorDefined :=
    (Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation)
      proportion.vector vectorNull
  have matrixCap : (NonNullProportion.rotation proportion).matrix =
      Cap.cap proportion.vector vectorDefined := by
    change (NonNullProportion.rotationMatrix proportion) = Cap.cap proportion.vector vectorDefined
    calc
      (NonNullProportion.rotationMatrix proportion) =
          Cap.cap (Coordinates3.Vector.scale proportion.scalar⁻¹ proportion.vector)
            (Charts.reciprocalAnchorCapDefined proportion.scalar proportion.vector
              scalarNonzero proportion.normNonzero) :=
        NonNullProportion.rotationMatrix_eq_cap proportion scalarNonzero
      _ = Cap.cap proportion.vector vectorDefined := by
        congr 1
        rw [scalarOne, oneInverse, Coordinates3.Vector.one_scale]
  constructor
  · intro matrixIdentity
    apply Cap.cap_injective presentation.twoNonzero proportion.vector Coordinates3.Vector.zero
      vectorDefined
      ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation)
        Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero)
    calc
      Cap.cap proportion.vector vectorDefined = (NonNullProportion.rotation proportion).matrix :=
        matrixCap.symm
      _ = Matrix3.identity := matrixIdentity
      _ = Cap.cap Coordinates3.Vector.zero
          ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation)
            Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) :=
        (((fun {K : Type _} [ExplicitField K] (presentation :
          Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) =>
          (Purelib.Geometry.Rotations.Cayley.FieldRealizations.cap_zero_eq_identity (K := K)
          (Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation
          Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) :
          Purelib.Geometry.Rotations.Cayley.Cap.cap (Coordinates3.Vector.zero :
          Coordinates3.Vector K)
          ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation)
          Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) =
          Purelib.LinearAlgebra.Coordinates3.Matrix3.identity)) presentation)).symm
  · intro vectorZero
    calc
      (NonNullProportion.rotation proportion).matrix = Cap.cap proportion.vector vectorDefined :=
        matrixCap
      _ = Cap.cap Coordinates3.Vector.zero
          ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation)
            Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) :=
        Purelib.Geometry.Rotations.Cayley.Cap.eq_of_vector_eq vectorZero
          _ _
      _ = Matrix3.identity := ((fun {K : Type _} [ExplicitField K] (presentation :
        Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation K) =>
        (Purelib.Geometry.Rotations.Cayley.FieldRealizations.cap_zero_eq_identity (K := K)
        (Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation
        Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) :
        Purelib.Geometry.Rotations.Cayley.Cap.cap (Coordinates3.Vector.zero :
        Coordinates3.Vector K)
        ((Purelib.Geometry.Rotations.Cayley.Cap.capDenominator_ne_zero_of_null_presentation presentation)
        Coordinates3.Vector.zero Coordinates3.Vector.quadrance_zero) =
        Purelib.LinearAlgebra.Coordinates3.Matrix3.identity)) presentation)

/-- The complementary points of the zero affine quadric are exactly the nonidentity parabolic stratum. -/
theorem zeroFiber_rotation_nonidentity_iff_vector_ne_zero
    (proportion : Projective.Basic.NonNullProportion K)
    (member : proportion ∈ presentation.halfSpreadFiber 0) :
    (NonNullProportion.rotation proportion).matrix ≠ Matrix3.identity ↔
      proportion.vector ≠ Coordinates3.Vector.zero := by
  constructor
  · intro matrixNonidentity vectorZero
    exact matrixNonidentity
      ((presentation.zeroFiber_rotation_identity_iff_vector_eq_zero
        proportion member).2 vectorZero)
  · intro vectorNonzero matrixIdentity
    exact vectorNonzero
      ((presentation.zeroFiber_rotation_identity_iff_vector_eq_zero
        proportion member).1 matrixIdentity)

/-- Every genuine middle affine quadric is precisely a semisimple rotation fiber: its represented rotations have half
spread different from both endpoints. -/
theorem middleFiber_rotation_semisimple {value : K}
    (valueNonzero : value ≠ 0) (notOne : value ≠ 1)
    (proportion : Projective.Basic.NonNullProportion K)
    (member : proportion ∈ presentation.halfSpreadFiber value) :
    Spread.halfSpread (NonNullProportion.rotation proportion) ≠ 0 ∧
      Spread.halfSpread (NonNullProportion.rotation proportion) ≠ 1 := by
  have spreadEq := presentation.halfSpread_rotation_eq_value_of_mem value
    proportion member
  constructor
  · intro spreadZero
    apply valueNonzero
    exact spreadEq.symm.trans spreadZero
  · intro spreadOne
    apply notOne
    exact spreadEq.symm.trans spreadOne

/-- Every point of the projective-axis quadric complement represents a half-turn rotation. -/
theorem projectiveAxis_rotation_halfTurn
    (proportion : Projective.Basic.NonNullProportion K)
    (member : proportion ∈
      presentation.projectiveNonNullAxisRepresentatives) :
    Spread.halfSpread (NonNullProportion.rotation proportion) = 1 := by
  exact presentation.halfSpread_rotation_eq_value_of_mem 1 proportion
    (presentation.projectiveAxis_member_halfSpreadFiber_one proportion member)

/-- The identity/parabolic half-spread fiber always has `q²` elements. -/
theorem halfSpreadFiberCount_zero :
    presentation.halfSpreadFiberCount 0 =
      presentation.carrier.length * presentation.carrier.length := by
  have zeroNotOne : (0 : K) ≠ 1 := by
    intro zeroOne
    exact FiniteOddFieldPresentation.one_ne_zero presentation zeroOne.symm
  rw [presentation.halfSpreadFiberCount_eq_vectorQuadranceCount 0 zeroNotOne,
    ExplicitField.zero_div, presentation.vectorQuadranceCount_zero]

set_option genInjectivity false in
/-- Exhaustive constructive count classification for a half-spread value other than the half-turn endpoint. The four
nonzero branches retain the displayed square witnesses (or rejecting functions) for both `-1` and the affine value
`h/(1-h)`. -/
inductive NonHalfTurnFiberCountClassification (value : K) where
  /-- The zero fiber has q squared elements. -/ | zero (valueZero : value = 0)
      (count : presentation.halfSpreadFiberCount value =
        presentation.carrier.length * presentation.carrier.length)
  /-- Square minus one and square affine value give q squared plus q elements. -/ | splitSquare (valueNonzero : value ≠
    0)
      (minusOneRoot affineRoot : K)
      (minusOneSquare : minusOneRoot ^ 2 = -1)
      (affineSquare : affineRoot ^ 2 = value / (1 - value))
      (count : presentation.halfSpreadFiberCount value =
        presentation.carrier.length * presentation.carrier.length +
          presentation.carrier.length)
  /-- Square minus one and nonsquare affine value give q squared minus q elements. -/ | splitNonsquare (valueNonzero :
    value ≠ 0)
      (minusOneRoot : K) (minusOneSquare : minusOneRoot ^ 2 = -1)
      (affineNoRoot : ∀ root : K,
        root ^ 2 ≠ value / (1 - value))
      (count : presentation.halfSpreadFiberCount value =
        presentation.carrier.length * presentation.carrier.length -
          presentation.carrier.length)
  /-- Nonsquare minus one and square affine value give q squared minus q elements. -/ | nonsplitSquare (valueNonzero :
    value ≠ 0)
      (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
      (affineRoot : K)
      (affineSquare : affineRoot ^ 2 = value / (1 - value))
      (count : presentation.halfSpreadFiberCount value =
        presentation.carrier.length * presentation.carrier.length -
          presentation.carrier.length)
  /-- Nonsquare minus one and nonsquare affine value give q squared plus q elements. -/ | nonsplitNonsquare
    (valueNonzero : value ≠ 0)
      (minusOneNoRoot : ∀ root : K, root ^ 2 ≠ -1)
      (affineNoRoot : ∀ root : K,
        root ^ 2 ≠ value / (1 - value))
      (count : presentation.halfSpreadFiberCount value =
        presentation.carrier.length * presentation.carrier.length +
          presentation.carrier.length)

constructive_injectivity NonHalfTurnFiberCountClassification

/-- Compute the exact non-half-turn fiber regime from the cached finite square tables. -/
@[expose] public def classifyNonHalfTurnFiberCount (value : K) (notOne : value ≠ 1) :
    presentation.NonHalfTurnFiberCountClassification value := by
  let affineValue := value / (1 - value)
  have reduction :=
    presentation.halfSpreadFiberCount_eq_vectorQuadranceCount value notOne
  have vectorSliced :=
    presentation.vectorQuadranceCount_eq_ternaryQuadranceSlicedCount affineValue
  cases presentation.classifyTernaryQuadranceCount affineValue with
  | zero affineZero count =>
      have valueZero : value = 0 := by
        have multiplied := congrArg (fun scalar => scalar * (1 - value))
          affineZero
        change value / (1 - value) * (1 - value) =
          0 * (1 - value) at multiplied
        rw [ExplicitField.div_mul_cancel value
          (one_sub_ne_zero_of_ne_one_counting
            notOne), zero_mul] at multiplied
        exact multiplied
      exact Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.NonHalfTurnFiberCountClassification.zero
        valueZero (by
        rw [valueZero]
        exact presentation.halfSpreadFiberCount_zero)
  | splitSquare affineNonzero minusOneRoot affineRoot minusOneSquare
      affineSquare count =>
      have valueNonzero : value ≠ 0 := by
        intro valueZero
        apply affineNonzero
        change value / (1 - value) = 0
        rw [valueZero, ExplicitField.zero_div]
      exact
        Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.NonHalfTurnFiberCountClassification.splitSquare
        valueNonzero
        minusOneRoot affineRoot minusOneSquare affineSquare
        (reduction.trans (vectorSliced.trans count))
  | splitNonsquare affineNonzero minusOneRoot minusOneSquare affineNoRoot
      count =>
      have valueNonzero : value ≠ 0 := by
        intro valueZero
        apply affineNonzero
        change value / (1 - value) = 0
        rw [valueZero, ExplicitField.zero_div]
      exact
        NonHalfTurnFiberCountClassification.splitNonsquare
        valueNonzero
        minusOneRoot minusOneSquare affineNoRoot
        (reduction.trans (vectorSliced.trans count))
  | nonsplitSquare affineNonzero minusOneNoRoot affineRoot affineSquare
      count =>
      have valueNonzero : value ≠ 0 := by
        intro valueZero
        apply affineNonzero
        change value / (1 - value) = 0
        rw [valueZero, ExplicitField.zero_div]
      exact
        NonHalfTurnFiberCountClassification.nonsplitSquare
        valueNonzero
        minusOneNoRoot affineRoot affineSquare
        (reduction.trans (vectorSliced.trans count))
  | nonsplitNonsquare affineNonzero minusOneNoRoot affineNoRoot count =>
      have valueNonzero : value ≠ 0 := by
        intro valueZero
        apply affineNonzero
        change value / (1 - value) = 0
        rw [valueZero, ExplicitField.zero_div]
      exact
        NonHalfTurnFiberCountClassification.nonsplitNonsquare
        valueNonzero
        minusOneNoRoot affineNoRoot
        (reduction.trans (vectorSliced.trans count))

set_option genInjectivity false in
/-- The paper-facing two-case classification for a genuine middle half-spread value. A square discriminant gives the
large fiber and a nonsquare discriminant gives the small fiber. -/
inductive MiddleHalfSpreadFiberCountClassification (value : K) where
  /-- A displayed discriminant square root certifies the q squared plus q fiber. -/ | large (discriminantRoot : K)
      (discriminantSquare : discriminantRoot ^ 2 =
        halfSpreadDiscriminant value)
      (count : presentation.halfSpreadFiberCount value =
        presentation.carrier.length * presentation.carrier.length +
          presentation.carrier.length)
  /-- Absence of a discriminant square root certifies the q squared minus q fiber. -/ | small (discriminantNoRoot : ∀
    root : K,
      root ^ 2 ≠ halfSpreadDiscriminant value)
      (count : presentation.halfSpreadFiberCount value =
        presentation.carrier.length * presentation.carrier.length -
          presentation.carrier.length)

constructive_injectivity MiddleHalfSpreadFiberCountClassification

/-- Compute the `q²+q`/`q²-q` regime directly from the square class of `-h(1-h)`. -/
@[expose] public def classifyMiddleHalfSpreadFiberCount (value : K)
    (valueNonzero : value ≠ 0) (notOne : value ≠ 1) :
    presentation.MiddleHalfSpreadFiberCountClassification value := by
  let affineValue := value / (1 - value)
  let complement := 1 - value
  have complementNonzero :=
    one_sub_ne_zero_of_ne_one_counting notOne
  change complement ≠ 0 at complementNonzero
  have complementSquareNonzero : complement ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      ExplicitField.mul_ne_zero complementNonzero complementNonzero
  have factorization :=
    halfSpreadDiscriminant_affine_factorization value
      notOne
  change halfSpreadDiscriminant value =
    ((-1 : K) * affineValue) * complement ^ 2 at factorization
  cases presentation.classifyNonHalfTurnFiberCount value notOne with
  | zero valueZero _ =>
      exact False.elim (valueNonzero valueZero)
  | splitSquare _ minusOneRoot affineRoot minusOneSquare affineSquare count =>
      refine
        Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.MiddleHalfSpreadFiberCountClassification.large
        (minusOneRoot * affineRoot * complement) ?_ count
      calc
        (minusOneRoot * affineRoot * complement) ^ 2 =
            minusOneRoot ^ 2 * affineRoot ^ 2 * complement ^ 2 := by ring1
        _ =
            ((-1 : K) * affineValue) * complement ^ 2 := by
          rw [minusOneSquare, affineSquare]
        _ = halfSpreadDiscriminant value :=
          factorization.symm
  | splitNonsquare _ minusOneRoot minusOneSquare affineNoRoot count =>
      let squareValue := (-1 : K) * complement ^ 2
      have squareValueNonzero : squareValue ≠ 0 :=
        ExplicitField.mul_ne_zero
          (minus_one_ne_zero_counting
            presentation) complementSquareNonzero
      have squareEquation : (minusOneRoot * complement) ^ 2 = squareValue := by
        unfold squareValue
        calc
          (minusOneRoot * complement) ^ 2 =
              minusOneRoot ^ 2 * complement ^ 2 := by ring1
          _ = (-1 : K) * complement ^ 2 := by rw [minusOneSquare]
      have productNoRoot := FiniteOddFieldPresentation.square_mul_nonsquare_noRoot squareValue
        (minusOneRoot * complement) affineValue squareValueNonzero
        squareEquation affineNoRoot
      refine
        Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.MiddleHalfSpreadFiberCountClassification.small
        ?_ count
      intro root rootSquare
      apply productNoRoot root
      calc
        root ^ 2 = halfSpreadDiscriminant value :=
          rootSquare
        _ = squareValue * affineValue := by
          rw [factorization]
          unfold squareValue
          ring1
  | nonsplitSquare _ minusOneNoRoot affineRoot affineSquare count =>
      let squareValue := affineValue * complement ^ 2
      have affineNonzero : affineValue ≠ 0 := by
        unfold affineValue
        exact ExplicitField.div_ne_zero valueNonzero complementNonzero
      have squareValueNonzero : squareValue ≠ 0 :=
        ExplicitField.mul_ne_zero affineNonzero complementSquareNonzero
      have squareEquation : (affineRoot * complement) ^ 2 = squareValue := by
        unfold squareValue
        calc
          (affineRoot * complement) ^ 2 =
              affineRoot ^ 2 * complement ^ 2 := by ring1
          _ = affineValue * complement ^ 2 := by rw [affineSquare]
      have productNoRoot := FiniteOddFieldPresentation.square_mul_nonsquare_noRoot squareValue
        (affineRoot * complement) (-1) squareValueNonzero squareEquation
        minusOneNoRoot
      refine
        Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.MiddleHalfSpreadFiberCountClassification.small
        ?_ count
      intro root rootSquare
      apply productNoRoot root
      calc
        root ^ 2 = halfSpreadDiscriminant value :=
          rootSquare
        _ = squareValue * (-1 : K) := by
          rw [factorization]
          unfold squareValue
          ring1
  | nonsplitNonsquare _ minusOneNoRoot affineNoRoot count =>
      let witness := (FiniteOddFieldPresentation.nonsquareMulNonsquareSquareWitness presentation)
        (-1) affineValue minusOneNoRoot affineNoRoot
      refine
        Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation.MiddleHalfSpreadFiberCountClassification.large
        (witness.root * complement) ?_ count
      calc
        (witness.root * complement) ^ 2 =
            witness.root ^ 2 * complement ^ 2 := by ring1
        _ =
            ((-1 : K) * affineValue) * complement ^ 2 := by
          rw [witness.equation]
        _ = halfSpreadDiscriminant value :=
          factorization.symm

/-- The complete explicit rotation carrier has the classical order `q(q²-1)`, proved from the affine excluded quadric
and the independently counted projective plane at infinity. -/
theorem rotationCount_formula :
    presentation.rotationCount = presentation.carrier.length *
      (presentation.carrier.length * presentation.carrier.length - 1) := by
  have infinityCount : presentation.infinityTNonNullCount +
      presentation.infinityRNonNullCount + 1 =
        presentation.carrier.length * presentation.carrier.length := by
    calc
      presentation.infinityTNonNullCount +
          presentation.infinityRNonNullCount + 1 =
        presentation.halfSpreadFiberCount 1 :=
          presentation.halfSpreadFiberCount_one_eq_infinityCounts.symm
      _ = presentation.carrier.length * presentation.carrier.length :=
        presentation.halfSpreadFiberCount_one
  have rotationAsAffine : presentation.rotationCount =
      presentation.affineNonNullCount +
        presentation.carrier.length * presentation.carrier.length := by
    calc
      presentation.rotationCount = presentation.affineNonNullCount +
          presentation.infinityTNonNullCount +
            presentation.infinityRNonNullCount + 1 :=
        presentation.rotationCount_eq_affineNonNullCount_add_infinityCounts
      _ = presentation.affineNonNullCount +
          (presentation.infinityTNonNullCount +
            presentation.infinityRNonNullCount + 1) := by ring1
      _ = presentation.affineNonNullCount +
          presentation.carrier.length * presentation.carrier.length := by
        rw [infinityCount]
  have totalAdd : presentation.rotationCount + presentation.carrier.length =
      presentation.carrier.length *
        (presentation.carrier.length * presentation.carrier.length) := by
    calc
      presentation.rotationCount + presentation.carrier.length =
          (presentation.affineNonNullCount +
            presentation.carrier.length * presentation.carrier.length) +
              presentation.carrier.length :=
        congrArg (fun count => count + presentation.carrier.length)
          rotationAsAffine
      _ = presentation.affineNonNullCount +
          (presentation.carrier.length * presentation.carrier.length +
            presentation.carrier.length) := by ring1
      _ = presentation.affineNonNullCount +
          presentation.excludedAnchorQuadric.length := by
        rw [presentation.excludedAnchorQuadric_length]
      _ = presentation.carrier.length *
          (presentation.carrier.length * presentation.carrier.length) :=
        presentation.affineNonNullCount_add_excludedAnchorQuadric
  calc
    presentation.rotationCount =
        presentation.carrier.length *
          (presentation.carrier.length * presentation.carrier.length) -
            presentation.carrier.length :=
      FiniteOddFieldPresentation.nat_eq_sub_of_add_eq_counting totalAdd
    _ = presentation.carrier.length *
        (presentation.carrier.length * presentation.carrier.length - 1) := by
      symm
      rw [Purelib.Data.Nat.Multiplication.left_sub_distrib, Nat.mul_one]

/-- The order formula stated directly for the duplicate-free rotation list, with the projective representative bijection
used as the cardinal bridge. -/
theorem rotationCarrierCount_formula_via_projectiveBijection :
    presentation.rotations.length = presentation.carrier.length *
      (presentation.carrier.length * presentation.carrier.length - 1) := by
  have projectiveLength := ListBijection.length_eq
    presentation.projectiveRotationBijection
    presentation.nonNullProjectiveRepresentatives_nodup
    presentation.rotations_nodup
  calc
    presentation.rotations.length =
        presentation.nonNullProjectiveRepresentatives.length :=
      projectiveLength.symm
    _ = presentation.rotationCount := by
      symm
      calc
        presentation.rotationCount =
            presentation.rotationEnumeration.values.length :=
          presentation.rotationCount_eq_rotationEnumeration_length
        _ = presentation.rotations.length := rfl
        _ = presentation.nonNullProjectiveRepresentatives.length :=
          projectiveLength.symm
    _ = presentation.carrier.length *
        (presentation.carrier.length * presentation.carrier.length - 1) :=
      presentation.rotationCount_formula

/-- Closed count of displayed non-null four-tuples before quotienting. The factor `q-1` is certified by the explicit
scale-orbit bijection, not by a quotient-cardinality theorem. -/
theorem allNonNullProportionRepresentatives_count_formula :
    presentation.allNonNullProportionRepresentatives.length =
      (presentation.carrier.length - 1) *
        (presentation.carrier.length *
          (presentation.carrier.length * presentation.carrier.length - 1)) := by
  have projectiveLength := ListBijection.length_eq
    presentation.projectiveRotationBijection
    presentation.nonNullProjectiveRepresentatives_nodup
    presentation.rotations_nodup
  calc
    presentation.allNonNullProportionRepresentatives.length =
        (presentation.carrier.length - 1) *
          presentation.nonNullProjectiveRepresentatives.length :=
      presentation.allNonNullProportionRepresentatives_length
    _ = (presentation.carrier.length - 1) *
        presentation.rotations.length := by rw [projectiveLength]
    _ = (presentation.carrier.length - 1) *
        (presentation.carrier.length *
          (presentation.carrier.length * presentation.carrier.length - 1)) := by
      rw [presentation.rotationCarrierCount_formula_via_projectiveBijection]

/-- Each of the two quadrance classes contains exactly half of the displayed rotation group. This proves the
equal-kernel assertion in Problem 69 without using a quotient cardinality or a choice of coset representatives. -/
theorem quadranceClassKernelCount_formula :
    presentation.quadranceClassKernelCount =
      (presentation.carrier.length *
        (presentation.carrier.length * presentation.carrier.length - 1)) / 2 := by
  let kernelLength := presentation.quadranceClassKernel.length
  have doubled : kernelLength + kernelLength = presentation.rotationCount :=
    presentation.quadranceClassKernel_twice_eq_rotationCount
  have kernelIsHalf : kernelLength = (kernelLength + kernelLength) / 2 := by
    symm
    calc
      (kernelLength + kernelLength) / 2 = (2 * kernelLength) / 2 := by
        congr 1
        ring1
      _ = kernelLength :=
        Purelib.Data.Nat.Division.mul_div_cancel_left kernelLength (by decide : 0 < 2)
  calc
    presentation.quadranceClassKernelCount = kernelLength :=
      presentation.quadranceClassKernelCount_eq_length
    _ = (kernelLength + kernelLength) / 2 := kernelIsHalf
    _ = presentation.rotationCount / 2 :=
      congrArg (fun count : Nat => count / 2) doubled
    _ = (presentation.carrier.length *
        (presentation.carrier.length * presentation.carrier.length - 1)) / 2 :=
      congrArg (fun count : Nat => count / 2)
        presentation.rotationCount_formula

/-- Efficient executable count of the nonzero affine null cone, equivalently the nonidentity parabolic rotations in the
scalar-one chart. -/
@[expose] public def parabolicCount : Nat := by
  letI : DecidableEq K := presentation.eqDecidable
  exact presentation.vectorCountWhere fun vector =>
    decide (vector.quadrance = 0) && decide (vector ≠ Coordinates3.Vector.zero)

/-- The parabolic counter equals the actual nonzero-null-vector list length. -/
theorem parabolicCount_eq_nonzeroNullVectors_length :
    presentation.parabolicCount = presentation.nonzeroNullVectors.length := by
  letI : DecidableEq K := presentation.eqDecidable
  unfold parabolicCount FiniteOddFieldPresentation.nonzeroNullVectors
  rw [presentation.vectorCountWhere_eq_length_filter]

/-- Adding the identity to the parabolic count gives the square of the field size. -/
theorem parabolicCount_add_one :
    presentation.parabolicCount + 1 =
      presentation.carrier.length * presentation.carrier.length := by
  rw [presentation.parabolicCount_eq_nonzeroNullVectors_length,
    presentation.nonzeroNullVectors_length_add_one,
    presentation.nullVectors_length_eq_vectorQuadranceCount_zero,
    presentation.vectorQuadranceCount_zero]

/-- There are q squared minus one nonidentity parabolic rotations over the displayed field. -/
theorem parabolicCount_formula :
    presentation.parabolicCount =
      presentation.carrier.length * presentation.carrier.length - 1 := by
  have added := presentation.parabolicCount_add_one
  calc
    presentation.parabolicCount =
        (presentation.parabolicCount + 1) - 1 :=
      (Purelib.Data.Nat.Subtraction.add_sub_cancel_right presentation.parabolicCount 1).symm
    _ = presentation.carrier.length * presentation.carrier.length - 1 :=
      congrArg (fun count => count - 1) added

set_option genInjectivity false in
/-- A single executable package for the completed finite counting clauses of Problem 69. It stores the carrier, the
value-by-value classifier, the quadrance-class switch, and the canonical preimage function alongside the closed count
and completeness certificates. -/
structure ProblemSixtyNineSolution where
  /-- The complete duplicate-free executable rotation carrier. -/ rotationCarrier :
    RotationEnumeration (K := K)
  /-- The retained rotation carrier is exactly the canonical enumeration. -/ rotationCarrierCanonical :
    rotationCarrier.values = presentation.rotationEnumeration.values
  /-- The complete duplicate-free executable matrix carrier. -/ rotationMatrixCarrier :
    RotationMatrixEnumeration (K := K)
  /-- The retained matrix carrier is exactly the canonical enumeration. -/ rotationMatrixCarrierCanonical :
    rotationMatrixCarrier.values =
      presentation.rotationMatrixEnumeration.values
  /-- The finite-list bijection between canonical proportions and rotations. -/ projectiveRotationEquivalence :
    Bijection.ListBijection
    presentation.nonNullProjectiveRepresentatives presentation.rotations
  /-- The finite-list bijection between raw non-null proportions and canonical scale coordinates. -/
    rawScaleOrbitEquivalence : Bijection.ListBijection
    presentation.allNonNullProportionRepresentatives
      presentation.scaleOrbitCoordinates
  /-- The raw proportion count includes the q minus one nonzero scales per canonical rotation. -/ rawProportionCount :
    presentation.allNonNullProportionRepresentatives.length =
      (presentation.carrier.length - 1) *
        (presentation.carrier.length *
          (presentation.carrier.length * presentation.carrier.length - 1))
  /-- The retained rotation list has q times q squared minus one elements. -/ rotationCarrierCount :
    presentation.rotations.length =
    presentation.carrier.length *
      (presentation.carrier.length * presentation.carrier.length - 1)
  /-- An executable identity, parabolic, half-turn or semisimple classification of each rotation. -/ classifyStratum : ∀
    rotation : Rotations.Basic.Rotation K,
    presentation.RotationStratum rotation
  /-- Each non-half-turn fiber is explicitly bijective with its affine ternary quadric. -/ affineFiberQuadricEquivalence
    : ∀ value : K, value ≠ 1 →
    Bijection.ListBijection (presentation.halfSpreadFiber value)
      (presentation.affineQuadricRepresentatives
        (value / (1 - value)))
  /-- The half-turn fiber is explicitly bijective with the non-null projective axes. -/
    halfTurnProjectiveAxisEquivalence : Bijection.ListBijection
    (presentation.halfSpreadFiber 1)
      presentation.projectiveNonNullAxisRepresentatives
  /-- The origin of the zero-fiber affine quadric corresponds exactly to the identity rotation. -/
    zeroFiberIdentityPoint : ∀ proportion : Projective.Basic.NonNullProportion K,
    proportion ∈ presentation.halfSpreadFiber 0 →
      ((NonNullProportion.rotation proportion).matrix = Matrix3.identity ↔
        proportion.vector = Coordinates3.Vector.zero)
  /-- A non-endpoint half-spread fiber contains only semisimple rotations. -/ middleFiberSemisimple : ∀ value : K, value
    ≠ 0 → value ≠ 1 →
    ∀ proportion : Projective.Basic.NonNullProportion K,
      proportion ∈ presentation.halfSpreadFiber value →
        Spread.halfSpread (NonNullProportion.rotation proportion) ≠ 0 ∧
          Spread.halfSpread (NonNullProportion.rotation proportion) ≠ 1
  /-- The efficient total counter has value q times q squared minus one. -/ totalCount : presentation.rotationCount =
    presentation.carrier.length *
    (presentation.carrier.length * presentation.carrier.length - 1)
  /-- The zero-half-spread fiber has q squared elements. -/ zeroFiberCount : presentation.halfSpreadFiberCount 0 =
    presentation.carrier.length * presentation.carrier.length
  /-- The half-turn fiber has q squared elements. -/ halfTurnFiberCount : presentation.halfSpreadFiberCount 1 =
    presentation.carrier.length * presentation.carrier.length
  /-- An executable square-discriminant classification and exact count for each non-endpoint fiber. -/
    middleFiberClassification : ∀ value : K, value ≠ 0 → value ≠ 1 →
    presentation.MiddleHalfSpreadFiberCountClassification value
  /-- Summing all displayed half-spread fiber counts gives the total count. -/ halfSpreadFiberCountSum :
    (presentation.carrier.map presentation.halfSpreadFiberCount).foldr
      Nat.add 0 = presentation.rotationCount
  /-- The retained square-class and cardinality classification for minus one. -/ minusOneCardinalityClassification :
    (FiniteOddFieldPresentation.MinusOneCardinalityClassification presentation)
  /-- There are q plus one canonical projective null directions. -/ nullDirectionCount :
    presentation.nullDirectionRepresentatives.length =
    presentation.carrier.length + 1
  /-- Every canonical null direction supports q minus one listed parabolic rotations. -/ parabolicDirectionFiberCount :
    ∀ direction : Coordinates3.Vector K,
    ∀ member : direction ∈ presentation.nullDirectionRepresentatives,
      (presentation.parabolicRotationsOverDirection direction member).length =
        presentation.carrier.length - 1
  /-- Recover canonical direction and scalar coordinates from a nonidentity zero-half-spread rotation. -/
    parabolicCoordinates : ∀ rotation : Rotations.Basic.Rotation K,
    ∀ _spreadZero : Spread.halfSpread rotation = 0,
    ∀ _nonidentity : rotation.matrix ≠ Matrix3.identity,
      presentation.ParabolicDirectionCoordinates rotation
  /-- The unipotent characteristic polynomial is equivalent to half spread zero. -/ characteristicParabolicEquivalence :
    ∀ rotation : Rotations.Basic.Rotation K,
    (∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3) ↔
        Spread.halfSpread rotation = 0
  /-- Recover parabolic coordinates from the characteristic polynomial and nonidentity evidence. -/
    parabolicCoordinatesFromCharacteristic : ∀ rotation : Rotations.Basic.Rotation K,
    (∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3) →
    rotation.matrix ≠ Matrix3.identity →
      presentation.ParabolicDirectionCoordinates rotation
  /-- The nonidentity parabolic count is q squared minus one. -/ parabolicAnchorCount : presentation.parabolicCount =
    presentation.carrier.length * presentation.carrier.length - 1
  /-- Every nonidentity zero-half-spread rotation has a displayed nonzero null cap anchor. -/ parabolicComplete : ∀
    rotation : Rotations.Basic.Rotation K,
    Spread.halfSpread rotation = 0 → rotation.matrix ≠ Matrix3.identity →
      ∃ vector : Coordinates3.Vector K, ∃ null : vector.quadrance = 0,
        vector ≠ Coordinates3.Vector.zero ∧
        vector ∈ presentation.nonzeroNullVectors ∧
          rotation = presentation.parabolicRotation vector null
  /-- Every nonidentity rotation with the unipotent characteristic polynomial has a displayed null cap anchor. -/
    parabolicCompleteFromCharacteristic : ∀ rotation : Rotations.Basic.Rotation K,
    (∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3) →
    rotation.matrix ≠ Matrix3.identity →
      ∃ vector : Coordinates3.Vector K, ∃ null : vector.quadrance = 0,
        vector ≠ Coordinates3.Vector.zero ∧
        vector ∈ presentation.nonzeroNullVectors ∧
          rotation = presentation.parabolicRotation vector null
  /-- The excluded affine null-norm quadric has q squared plus q elements. -/ excludedAffineCount :
    presentation.excludedAnchorQuadric.length =
    presentation.carrier.length * presentation.carrier.length +
      presentation.carrier.length
  /-- The excluded projective null-norm quadric has the square of q plus one elements. -/ excludedProjectiveCount :
    presentation.excludedProjectiveQuadricCount =
    (presentation.carrier.length + 1) *
      (presentation.carrier.length + 1)
  /-- Compute a rotation representing any displayed nonzero square class. -/ quadranceClassPreimage :
    SquareClass.Basic.SquareClassRepresentative K → Rotations.Basic.Rotation K
  /-- The computed rotation realizes its requested square-class representative. -/ quadranceClassPreimageRealizes : ∀
    target : SquareClass.Basic.SquareClassRepresentative K,
    letI : DecidableEq K := presentation.eqDecidable
    (RotationQuadranceClass.ofRotation
      (quadranceClassPreimage target) presentation.twoNonzero).Equivalent target
  /-- An explicit finite-list bijection exchanges the two quadrance-class fibers. -/ quadranceClassFiberSwitch :
    Bijection.ListBijection
    presentation.quadranceClassKernel
    presentation.quadranceClassNontrivialFiber
  /-- The square-norm kernel consists exactly of canonical proportions with unit representatives. -/
    quadranceClassKernelCharacterization : ∀ proportion : Projective.Basic.NonNullProportion K,
    proportion ∈ presentation.quadranceClassKernel ↔
      proportion ∈ presentation.nonNullProjectiveRepresentatives ∧
        (QuaternionObstruction.HasUnitRepresentative proportion)
  /-- The kernel has half the total number of rotations. -/ quadranceClassKernelCount :
    presentation.quadranceClassKernelCount =
    (presentation.carrier.length *
      (presentation.carrier.length * presentation.carrier.length - 1)) / 2

constructive_injectivity ProblemSixtyNineSolution

/-- Assemble the general odd-finite-field solution from the independently checked finite carriers and bijections. -/
@[expose] public def problemSixtyNineSolution :
    presentation.ProblemSixtyNineSolution where
  rotationCarrier := presentation.rotationEnumeration
  rotationCarrierCanonical := rfl
  rotationMatrixCarrier := presentation.rotationMatrixEnumeration
  rotationMatrixCarrierCanonical := rfl
  projectiveRotationEquivalence := presentation.projectiveRotationBijection
  rawScaleOrbitEquivalence := presentation.nonNullScaleOrbitBijection
  rawProportionCount :=
    presentation.allNonNullProportionRepresentatives_count_formula
  rotationCarrierCount :=
    presentation.rotationCarrierCount_formula_via_projectiveBijection
  classifyStratum := presentation.classifyRotationStratum
  affineFiberQuadricEquivalence := fun value notOne =>
    presentation.affineHalfSpreadFiberBijection value notOne
  halfTurnProjectiveAxisEquivalence :=
    presentation.halfTurnProjectiveAxisBijection
  zeroFiberIdentityPoint := fun proportion member =>
    presentation.zeroFiber_rotation_identity_iff_vector_eq_zero
      proportion member
  middleFiberSemisimple := fun _value valueNonzero notOne proportion member =>
    presentation.middleFiber_rotation_semisimple valueNonzero notOne
      proportion member
  totalCount := presentation.rotationCount_formula
  zeroFiberCount := presentation.halfSpreadFiberCount_zero
  halfTurnFiberCount := presentation.halfSpreadFiberCount_one
  middleFiberClassification := fun value valueNonzero notOne =>
    presentation.classifyMiddleHalfSpreadFiberCount value valueNonzero notOne
  halfSpreadFiberCountSum := presentation.halfSpreadFiberCounts_sum
  minusOneCardinalityClassification :=
    (FiniteOddFieldPresentation.classifyMinusOneCardinality presentation)
  nullDirectionCount := presentation.nullDirectionRepresentatives_length
  parabolicDirectionFiberCount := fun direction member =>
    presentation.parabolicRotationsOverDirection_length direction member
  parabolicCoordinates := fun rotation spreadZero nonidentity =>
    presentation.parabolicDirectionCoordinates rotation spreadZero nonidentity
  characteristicParabolicEquivalence := fun rotation =>
    Spread.characteristicUnipotent_iff_halfSpread_eq_zero rotation
      presentation.twoNonzero
  parabolicCoordinatesFromCharacteristic :=
    fun rotation characteristic nonidentity =>
      presentation.parabolicDirectionCoordinatesOfCharacteristic rotation
        characteristic nonidentity
  parabolicAnchorCount := presentation.parabolicCount_formula
  parabolicComplete := fun rotation spreadZero nonidentity =>
    presentation.parabolicRotation_complete rotation spreadZero nonidentity
  parabolicCompleteFromCharacteristic :=
    fun rotation characteristic nonidentity =>
      presentation.parabolicRotation_complete_of_characteristic rotation
        characteristic nonidentity
  excludedAffineCount := presentation.excludedAnchorQuadric_length
  excludedProjectiveCount :=
    presentation.excludedProjectiveQuadricCount_formula
  quadranceClassPreimage := presentation.quadranceClassPreimageRotation
  quadranceClassPreimageRealizes := fun target =>
    presentation.quadranceClassPreimage_realizes target
  quadranceClassFiberSwitch := presentation.quadranceClassFiberBijection
  quadranceClassKernelCharacterization := fun proportion =>
    presentation.mem_quadranceClassKernel_iff_hasUnitRepresentative proportion
  quadranceClassKernelCount := presentation.quadranceClassKernelCount_formula

end

/-!
# Certified rotation and projective occurrence counts

The displayed odd-field presentation retains its original finite scalar and
vector enumerations. Boolean filters and explicit bijections count canonical
projective representatives and the corresponding rotation strata.
-/

end Purelib.Algebra.Field.Finite.Odd.Presentation.FiniteOddFieldPresentation

end

section
public section

/-!
# Certified rotation and projective occurrence counts

The displayed odd-field presentation retains its original finite scalar and
vector enumerations. Boolean filters and explicit bijections count canonical
projective representatives and the corresponding rotation strata.
-/

namespace Purelib.Geometry.Rotations.FiniteField.Classification.FiniteOddFieldPresentation

open Purelib
open Purelib.Algebra.Field
open Purelib.Algebra.Field.Finite.Odd
open Purelib.Algebra.Field.Finite.Odd.Presentation
open Purelib.Algebra.Field.Finite.Odd.SquareClasses
open Purelib.Algebra.Field.SquareClass.Basic
open Purelib.Algebra.Field.SumsOfSquares
open Purelib.Algebra.Field.SumsOfSquares.Four
open Purelib.Algebra.Quadratic.Pair
open Purelib.Algebra.Quaternion
open Purelib.Algebra.Quaternion.Projective.Basic
open Purelib.Algebra.Quaternion.Projective.SquareClass
open Purelib.Algebra.Quaternion.Projective.UnitObstruction.NonNullProportion
open Purelib.Data.List
open Purelib.Data.List.Bijection
open Purelib.Geometry
open Purelib.Geometry.Rotations
open Purelib.Geometry.Rotations.Axis
open Purelib.Geometry.Rotations.Basic
open Purelib.Geometry.Rotations.Cayley
open Purelib.Geometry.Rotations.Projective.Action
open Purelib.Geometry.Rotations.Projective.Correspondence
open Purelib.Geometry.Rotations.Projective.SquareClass
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3

variable {K : Type*} [ExplicitField K]
section

/-- The counted finite square-norm list is exactly this kernel predicate on the canonical projective carrier. -/
theorem mem_quadranceClassKernel_iff_hasUnitRepresentative
    (presentation : Presentation.FiniteOddFieldPresentation K)
    (proportion : Projective.Basic.NonNullProportion K) :
    proportion ∈ presentation.quadranceClassKernel ↔
      proportion ∈ presentation.nonNullProjectiveRepresentatives ∧
        OpenProblems.Contains proportion :=
  presentation.mem_quadranceClassKernel_iff_hasUnitRepresentative proportion
end
end Purelib.Geometry.Rotations.FiniteField.Classification.FiniteOddFieldPresentation

end
