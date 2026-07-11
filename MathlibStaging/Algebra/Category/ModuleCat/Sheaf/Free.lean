/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import MathlibStaging.Init

/-!
-/

@[expose] public section

universe u v' u'

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The free sheaf of modules on a type with a unique element is the unit. -/
noncomputable def freePUnitIso : free (R := R) PUnit.{u + 1} ≅ unit R :=
  (isColimitFreeCofan PUnit.{u + 1}).coconePointUniqueUpToIso
    (Cofan.IsColimit.mk (Cofan.mk (unit R) (fun _ ↦ 𝟙 _)) (fun s ↦ s.inj PUnit.unit)
      (fun s j ↦ by cases j; exact Category.id_comp _)
      (fun s m hm ↦ by rw [← hm PUnit.unit]; exact (Category.id_comp m).symm))

/-- The free sheaf of modules on an empty type is zero. -/
lemma isZero_free_of_isEmpty (I : Type u) [IsEmpty I] : IsZero (free (R := R) I) :=
  (IsZero.iff_id_eq_zero _).mpr <|
    (freeHomEquiv _).injective (funext fun i ↦ (IsEmpty.false i).elim)

end SheafOfModules
