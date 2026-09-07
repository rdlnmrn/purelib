import CCL.Progressive.FiniteRelation
import CCL.Progressive.PolynomialRoots

/-!
# Persistent polynomial roots as a finite multivalued relation

The simple-root chamber already supplies the strongest collision-free case:
degree-many pairwise-separated rational owner boxes with fixed persistent
indices.  This adapter exposes those owners through the generic finite
relation interface while retaining exact box refinement as the continuation
witness.
-/

namespace CCL.ProgressivePolynomialRootRelation

abbrev GaussianPolynomial :=
  RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Box := RFAP.Boxes.Box
abbrev LocalOwner := CCL.ProgressivePolynomialRoots.LocalOwner
abbrev OwnerFamily := CCL.ProgressivePolynomialRoots.OwnerFamily
abbrev Fibre := CCL.FiniteMultivaluedRelation.Fibre

/-- Lift geometric separation proofs into the data universe expected by a
decidable finite pair classification. -/
def BoxSeparated (left right : Box) : Type := PLift (left.Separated right)

/-- Relation witness attached to one displayed owner box. -/
structure RootWitness (polynomial : GaussianPolynomial) (box : Box) where
  owner : LocalOwner polynomial
  owner_box : owner.box = box

/-- A pairwise-separated local owner family as one displayed finite fibre. -/
def ownerFibre {polynomial : GaussianPolynomial} {count : Nat}
    (family : OwnerFamily polynomial count) :
    Fibre Box BoxSeparated (RootWitness polynomial) :=
  CCL.FiniteMultivaluedRelation.Fibre.ofPairwiseSeparated count
    (fun label => (family.owner label).box)
    (fun label => ⟨family.owner label, rfl⟩)
    (fun left right different =>
      ⟨family.pairwiseSeparated left right different⟩)

@[simp] theorem ownerFibre_count
    {polynomial : GaussianPolynomial} {count : Nat}
    (family : OwnerFamily polynomial count) :
    (ownerFibre family).count = count := rfl

/-- Later owner boxes continue earlier owners exactly when they refine them. -/
def BoxContinues (old new : Box) : Prop := new.Refines old

theorem BoxContinues.refl (box : Box) : BoxContinues box box :=
  RFAP.Boxes.Box.refines_refl box

theorem BoxContinues.trans {first second third : Box}
    (firstSecond : BoxContinues first second)
    (secondThird : BoxContinues second third) :
    BoxContinues first third :=
  RFAP.Boxes.Box.Refines.trans secondThird firstSecond

/-- The same underlying finite label transported between two owner fibres
whose common count is explicit at this adapter boundary. -/
def sameLabelForward
    {firstPolynomial secondPolynomial : GaussianPolynomial} {count : Nat}
    (first : OwnerFamily firstPolynomial count)
    (second : OwnerFamily secondPolynomial count) :
    Fin (ownerFibre first).count → Fin (ownerFibre second).count :=
  Fin.cast (by rw [ownerFibre_count, ownerFibre_count])

def sameLabelBackward
    {firstPolynomial secondPolynomial : GaussianPolynomial} {count : Nat}
    (first : OwnerFamily firstPolynomial count)
    (second : OwnerFamily secondPolynomial count) :
    Fin (ownerFibre second).count → Fin (ownerFibre first).count :=
  Fin.cast (by rw [ownerFibre_count, ownerFibre_count])

theorem sameLabel_rightInverse
    {firstPolynomial secondPolynomial : GaussianPolynomial} {count : Nat}
    (first : OwnerFamily firstPolynomial count)
    (second : OwnerFamily secondPolynomial count)
    (label : Fin (ownerFibre second).count) :
    sameLabelForward first second (sameLabelBackward first second label) =
      label := by
  apply Fin.ext
  rfl

/-- Adapt a root-specific same-label nesting theorem to the generic finite
relation refinement. -/
def sameLabelRefinement
    {firstPolynomial secondPolynomial : GaussianPolynomial} {count : Nat}
    (first : OwnerFamily firstPolynomial count)
    (second : OwnerFamily secondPolynomial count)
    (nested : ∀ label : Fin count,
      (second.owner label).box.Refines (first.owner label).box) :
    CCL.FiniteMultivaluedRelation.Refinement (ownerFibre first)
      (ownerFibre second) BoxContinues :=
  CCL.FiniteMultivaluedRelation.Refinement.ofLabelEquivalence
    (sameLabelForward first second) (sameLabelBackward first second)
    (sameLabel_rightInverse first second)
    (by
      intro label
      let oldIndex : Fin count :=
        Fin.cast (ownerFibre_count first) label
      let newIndex : Fin count :=
        Fin.cast (ownerFibre_count second)
          (sameLabelForward first second label)
      have equal : newIndex = oldIndex := by
        apply Fin.ext
        rfl
      change (second.owner newIndex).box.Refines (first.owner oldIndex).box
      rw [equal]
      exact nested oldIndex)

/-- Fixed-polynomial simultaneous shrinking is a singleton-labelled finite
relation refinement. -/
def refineRelation
    {polynomial : GaussianPolynomial} {count : Nat}
    (family : OwnerFamily polynomial count)
    (degreeAtLeastTwo : 2 ≤ polynomial.natDegree)
    (squarefree : RFAP.Squarefree.SquarefreeCertificate polynomial)
    (epsilon : RFAP.ConstructiveFraction.Rational)
    (positive : 0 < epsilon) :
    CCL.FiniteMultivaluedRelation.Refinement (ownerFibre family)
      (ownerFibre (family.refine degreeAtLeastTwo squarefree epsilon positive))
      BoxContinues :=
  sameLabelRefinement family
    (family.refine degreeAtLeastTwo squarefree epsilon positive)
    (family.refine_nested degreeAtLeastTwo squarefree epsilon positive)

/-- Rouché transport followed by shrinking preserves the same explicit owner
labels even though the exact rational polynomial reading has changed. -/
def transportedRefinement
    {left right : CCL.ProgressivePolynomialRoots.CoefficientTable}
    {target : RFAP.ConstructiveFraction.Rational}
    {positive : 0 < target}
    (transfer : CCL.ProgressivePolynomialRoots.GuardedFamilyTransfer
      left right target positive)
    (epsilon : RFAP.ConstructiveFraction.Rational)
    (epsilonPositive : 0 < epsilon) :
    CCL.FiniteMultivaluedRelation.Refinement (ownerFibre transfer.family)
      (ownerFibre (transfer.refinedFamily epsilon epsilonPositive))
      BoxContinues :=
  sameLabelRefinement transfer.family
    (transfer.refinedFamily epsilon epsilonPositive)
    (transfer.refinedFamily_nested epsilon epsilonPositive)

theorem transported_owner_is_same_label
    {left right : CCL.ProgressivePolynomialRoots.CoefficientTable}
    {target : RFAP.ConstructiveFraction.Rational}
    {positive : 0 < target}
    (transfer : CCL.ProgressivePolynomialRoots.GuardedFamilyTransfer
      left right target positive)
    (epsilon : RFAP.ConstructiveFraction.Rational)
    (epsilonPositive : 0 < epsilon)
    (label : Fin left.degree) :
    (transportedRefinement transfer epsilon epsilonPositive).continues label =
      [sameLabelForward transfer.family
        (transfer.refinedFamily epsilon epsilonPositive) label] := rfl

end CCL.ProgressivePolynomialRootRelation
