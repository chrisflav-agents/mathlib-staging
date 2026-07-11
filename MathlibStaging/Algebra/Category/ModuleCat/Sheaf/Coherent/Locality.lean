/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import MathlibStaging.Algebra.Category.ModuleCat.Sheaf.Coherent.Basic
public import MathlibStaging.CategoryTheory.Sites.CoversTop.Over
public import MathlibStaging.Init

/-!
# Coherence is a local property

We show that for sheaves of modules on a small site `(C, J)` where `C` has pullbacks
and binary products:

- `SheafOfModules.IsCoherent.over`: coherence is stable under restriction to `Over X`;
- `SheafOfModules.IsCoherent.of_coversTop`: coherence can be checked on a covering of
  the terminal object.

The key technical ingredient is the transport of the relation-finiteness condition
across the equivalence `SheafOfModules.overOverEquivalence` between sheaves of modules
over `R.over Y.left` and over `(R.over X).over Y`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X), HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ (X : C) (Y : Over X), ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- Auxiliary statement for `SheafOfModules.HasFiniteTypeRelations.of_overOver`. -/
lemma isFiniteType_kernel_of_overOver {M : SheafOfModules.{u} R} {X : C} {Y : Over X}
    (h : (M.over X).HasFiniteTypeRelations Y) {I : Type u} [Finite I]
    (φ : free I ⟶ M.over Y.left) : (kernel φ).IsFiniteType := by
  have h1 := h ((mapFreeIso (overOverEquivalence (R := R) X Y).functor I
      (overOverEquivalenceUnitIso X Y).symm).hom ≫
    (overOverEquivalence (R := R) X Y).functor.map φ ≫ (overOverEquivalenceObjIso M X Y).hom)
  have h2 := (isFiniteType ((R.over X).over Y)).prop_of_iso
    (kernelIsIsoComp _ _ ≪≫ kernelCompMono _ _) h1
  have h3 := (isFiniteType ((R.over X).over Y)).prop_of_iso
    (PreservesKernel.iso (overOverEquivalence (R := R) X Y).functor φ).symm h2
  exact IsFiniteType.of_overOverEquivalence_functor_obj h3

/-- The relation-finiteness condition transports from `(M.over X, Y)` to `(M, Y.left)`. -/
lemma HasFiniteTypeRelations.of_overOver {M : SheafOfModules.{u} R} {X : C} {Y : Over X}
    (h : (M.over X).HasFiniteTypeRelations Y) : M.HasFiniteTypeRelations Y.left := by
  intro I _ φ
  exact isFiniteType_kernel_of_overOver h φ

/-- Auxiliary statement for `SheafOfModules.HasFiniteTypeRelations.overOver`. -/
lemma isFiniteType_kernel_overOver {M : SheafOfModules.{u} R} {X : C} {Y : Over X}
    (h : M.HasFiniteTypeRelations Y.left) {I : Type u} [Finite I]
    (ψ : free I ⟶ (M.over X).over Y) : (kernel ψ).IsFiniteType := by
  haveI : HasKernels (SheafOfModules.{u} (R.over Y.left)) := inferInstance
  haveI := HasKernels.has_limit ((overOverEquivalence (R := R) X Y).inverse.map ψ ≫
    (overOverEquivalenceInverseObjIso M X Y).hom)
  haveI := HasKernels.has_limit ((overOverEquivalence (R := R) X Y).inverse.map ψ)
  have h1 := h ((mapFreeIso (overOverEquivalence (R := R) X Y).inverse I
      (overOverEquivalenceInverseUnitIso X Y)).hom ≫
    (overOverEquivalence (R := R) X Y).inverse.map ψ ≫
    (overOverEquivalenceInverseObjIso M X Y).hom)
  have h2 := (isFiniteType (R.over Y.left)).prop_of_iso
    (kernelIsIsoComp _ _ ≪≫ kernelCompMono _ _) h1
  have h3 := (isFiniteType (R.over Y.left)).prop_of_iso
    (PreservesKernel.iso (overOverEquivalence (R := R) X Y).inverse ψ).symm h2
  exact IsFiniteType.of_overOverEquivalence_inverse_obj h3

/-- The relation-finiteness condition transports from `(M, Y.left)` to `(M.over X, Y)`. -/
lemma HasFiniteTypeRelations.overOver {M : SheafOfModules.{u} R} {X : C} {Y : Over X}
    (h : M.HasFiniteTypeRelations Y.left) : (M.over X).HasFiniteTypeRelations Y := by
  intro I _ ψ
  exact isFiniteType_kernel_overOver h ψ

variable [HasBinaryProducts C]

/-- The restriction of a coherent sheaf of modules to `Over X` is coherent. -/
lemma IsCoherent.over (M : SheafOfModules.{u} R) [M.IsCoherent] (X : C) :
    IsCoherent (R := R.over X) (M.over X) where
  isFiniteType := IsFiniteType.over M X
  hasFiniteTypeRelations Y :=
    HasFiniteTypeRelations.overOver (IsCoherent.hasFiniteTypeRelations M Y.left)

omit [HasBinaryProducts C] in
/-- Auxiliary statement for `SheafOfModules.IsCoherent.of_coversTop`: relation-finiteness
of the restriction of a kernel sheaf to an object of `Over W` whose underlying object
maps to a member of a cover on which `M` is coherent. -/
lemma isFiniteType_over_kernel_of_hasFiniteTypeRelations {M : SheafOfModules.{u} R} {W : C}
    {I' : Type u} [Finite I'] (ψ : free I' ⟶ M.over W) {V : C} (w : V ⟶ W)
    (hV : M.HasFiniteTypeRelations V) :
    IsFiniteType (R := (R.over W).over (Over.mk w)) ((kernel ψ).over (Over.mk w)) := by
  haveI : HasBinaryProducts (Over W) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  let χ : free I' ⟶ (M.over W).over (Over.mk w) :=
    (overFreeIso I' (Over.mk w)).hom ≫ ψ.over (Over.mk w)
  haveI : (kernel χ).IsFiniteType :=
    HasFiniteTypeRelations.overOver (Y := Over.mk w) hV χ
  haveI : (kernel (ψ.over (Over.mk w))).IsFiniteType :=
    IsFiniteType.of_iso (M := kernel χ) (kernelIsIsoComp _ _)
  exact IsFiniteType.of_iso (M := kernel (ψ.over (Over.mk w))) (overKernelIso ψ (Over.mk w)).symm

omit [HasBinaryProducts C] in
/-- Coherence is local: if `M` restricts to a coherent sheaf of modules on a covering
of the terminal object, then `M` is coherent. -/
lemma IsCoherent.of_coversTop (M : SheafOfModules.{u} R) {I : Type u}
    (X : I → C) (hX : J.CoversTop X)
    [∀ i, IsCoherent (R := R.over (X i)) (M.over (X i))] :
    M.IsCoherent where
  isFiniteType := .of_coversTop M X hX
  hasFiniteTypeRelations W := by
    intro I' _ ψ
    haveI (t : (i : I) × (V : C) × (V ⟶ X i) × (V ⟶ W)) :
        IsFiniteType (R := (R.over W).over (Over.mk t.2.2.2))
          ((kernel ψ).over (Over.mk t.2.2.2)) := by
      obtain ⟨i, V, g, w⟩ := t
      refine isFiniteType_over_kernel_of_hasFiniteTypeRelations ψ w ?_
      exact HasFiniteTypeRelations.of_overOver (Y := Over.mk g)
        (IsCoherent.hasFiniteTypeRelations (M.over (X i)) (Over.mk g))
    exact IsFiniteType.of_coversTop (kernel ψ) _ (hX.over' W)

end SheafOfModules
