/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import MathlibStaging.CategoryTheory.Sites.Over
public import MathlibStaging.Init

/-!
-/

@[expose] public section

universe w v' u' u

open CategoryTheory Limits

namespace SheafOfModules

section

variable {C : Type u'} [Category.{v'} C] [HasBinaryProducts C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

instance (X : C) : (overFunctor.{w} R X).IsLeftAdjoint :=
  inferInstanceAs (pushforward.{w} (𝟙 (R.over X))).IsLeftAdjoint

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The restriction of a free sheaf of modules to `Over X` is free. -/
noncomputable def overFreeIso (I : Type u) (X : C) :
    free (R := R.over X) I ≅ (free (R := R) I).over X :=
  mapFreeIso (overFunctor R X) I (Iso.refl _)

end

section

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- Sheaves of modules over `R.over Y.left` are equivalent to sheaves of modules over
`(R.over X).over Y`. -/
noncomputable def overOverEquivalence (X : C) (Y : Over X) :
    SheafOfModules.{u} (R.over Y.left) ≌ SheafOfModules.{u} ((R.over X).over Y) :=
  pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv Y)
    (S := (R.over X).over Y) (R := R.over Y.left) (𝟙 _) (𝟙 _)
    (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)

/-- The equivalence `overOverEquivalence` is compatible with restriction. -/
noncomputable def overOverEquivalenceObjIso (M : SheafOfModules.{u} R) (X : C) (Y : Over X) :
    (overOverEquivalence (R := R) X Y).functor.obj (M.over Y.left) ≅ (M.over X).over Y := by
  exact Iso.refl _

/-- The equivalence `overOverEquivalence` sends the unit to the unit. -/
noncomputable def overOverEquivalenceUnitIso (X : C) (Y : Over X) :
    (overOverEquivalence (R := R) X Y).functor.obj (unit (R.over Y.left)) ≅
      unit ((R.over X).over Y) := by
  exact Iso.refl _

/-- The inverse of the equivalence `overOverEquivalence` sends the unit to the unit. -/
noncomputable def overOverEquivalenceInverseUnitIso (X : C) (Y : Over X) :
    unit (R.over Y.left) ≅
      (overOverEquivalence (R := R) X Y).inverse.obj (unit ((R.over X).over Y)) := by
  exact Iso.refl _

/-- The inverse of the equivalence `overOverEquivalence` is compatible with restriction. -/
noncomputable def overOverEquivalenceInverseObjIso (M : SheafOfModules.{u} R) (X : C)
    (Y : Over X) :
    (overOverEquivalence (R := R) X Y).inverse.obj ((M.over X).over Y) ≅ M.over Y.left := by
  exact ((overOverEquivalence (R := R) X Y).unitIso.app (M.over Y.left)).symm

end

section

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

instance (X : C) : (overFunctor.{u} R X).IsRightAdjoint :=
  inferInstanceAs (pushforward.{u} (𝟙 (R.over X))).IsRightAdjoint

variable [HasSheafify J AddCommGrpCat.{u}] [∀ (X : C), HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ (X : C), (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The restriction functor to `Over X` commutes with kernels. -/
noncomputable def overKernelIso {M N : SheafOfModules.{u} R} (φ : M ⟶ N) (X : C) :
    (kernel φ).over X ≅ kernel (φ.over X) :=
  PreservesKernel.iso (overFunctor R X) φ

end

end SheafOfModules
