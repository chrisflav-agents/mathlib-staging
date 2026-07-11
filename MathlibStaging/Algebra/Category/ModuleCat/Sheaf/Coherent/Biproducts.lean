/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import MathlibStaging.Algebra.Category.ModuleCat.Sheaf.Coherent.Locality
public import MathlibStaging.Algebra.Category.ModuleCat.Sheaf.Coherent.Stability
public import MathlibStaging.Algebra.Category.ModuleCat.Sheaf.Free
public import MathlibStaging.Init

/-!
# Coherence of biproducts and free sheaves of modules

We show that for sheaves of modules on a small site `(C, J)` where `C` has pullbacks
and binary products:

- `SheafOfModules.IsFiniteType.biprod`: binary biproducts of finite type sheaves are
  of finite type;
- `SheafOfModules.IsCoherent.biprod`: binary biproducts of coherent sheaves are coherent;
- `SheafOfModules.IsCoherent.free`: if `unit R` is coherent, then `free I` is coherent
  for every finite `I`.

-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- For `φ : F ⟶ A ⊞ B`, the kernel of `φ` is the kernel of the map to `B` induced
on the kernel of `φ ≫ biprod.fst`. -/
noncomputable def CategoryTheory.Limits.kernelBiprodIso {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]
    {F A B : 𝒜} (φ : F ⟶ A ⊞ B) :
    kernel (kernel.ι (φ ≫ biprod.fst) ≫ φ ≫ biprod.snd) ≅ kernel φ where
  hom := kernel.lift φ (kernel.ι _ ≫ kernel.ι (φ ≫ biprod.fst)) (by
    ext
    · simp [kernel.condition (φ ≫ biprod.fst)]
    · simp [kernel.condition (kernel.ι (φ ≫ biprod.fst) ≫ φ ≫ biprod.snd)])
  inv := kernel.lift _ (kernel.lift (φ ≫ biprod.fst) (kernel.ι φ)
      (by rw [← Category.assoc, kernel.condition, zero_comp]))
    (by rw [kernel.lift_ι_assoc, ← Category.assoc, kernel.condition, zero_comp])
  hom_inv_id := by
    ext
    simp
  inv_hom_id := by
    ext
    simp

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] [HasPullbacks C] [HasBinaryProducts C]
  {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

omit [HasPullbacks C] in
/-- A binary biproduct of globally finitely generated sheaves of modules is of finite
type. -/
lemma isFiniteType_biprod_of_generatingSections {A B : SheafOfModules.{u} R}
    (σA : A.GeneratingSections) (σB : B.GeneratingSections)
    [Finite σA.I] [Finite σB.I] :
    IsFiniteType (R := R) (A ⊞ B) := by
  haveI : (σA.biprod σB).IsFiniteType := ⟨inferInstanceAs (Finite (σA.I ⊕ σB.I))⟩
  exact IsFiniteType.of_generatingSections (M := A ⊞ B) (σA.biprod σB)

/-- Auxiliary statement: global generators on one factor and generators of the
restriction on the other yield finiteness of the restricted biproduct. -/
lemma isFiniteType_over_biprod_of_generatingSections {A B : SheafOfModules.{u} R}
    (σA : A.GeneratingSections) [Finite σA.I] {W : C}
    (τB : GeneratingSections (R := R.over W) (B.over W)) [Finite τB.I] :
    IsFiniteType (R := R.over W) ((A ⊞ B).over W) := by
  haveI : HasBinaryProducts (Over W) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  haveI : PreservesBinaryBiproducts (overFunctor.{u} R W) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  haveI : Finite (σA.map (overFunctor R W) (Iso.refl _)).I := inferInstanceAs (Finite σA.I)
  have h1 := isFiniteType_biprod_of_generatingSections
    (σA.map (overFunctor R W) (Iso.refl _)) τB
  exact (isFiniteType (R.over W)).prop_of_iso
    ((overFunctor.{u} R W).mapBiprod A B).symm h1

/-- Auxiliary statement for `SheafOfModules.IsFiniteType.biprod`: if `A` admits finitely
many global generating sections and `B` is of finite type, then `A ⊞ B` is of finite
type. -/
lemma isFiniteType_biprod_of_generatingSections_left {A B : SheafOfModules.{u} R}
    (σA : A.GeneratingSections) [Finite σA.I] [B.IsFiniteType] :
    IsFiniteType (R := R) (A ⊞ B) := by
  obtain ⟨ρ, hρ⟩ := IsFiniteType.exists_localGeneratorsData B
  refine IsFiniteType.of_coversTop_of_forall (A ⊞ B) ρ.X ρ.coversTop (fun j ↦ ?_)
  haveI := LocalGeneratorsData.IsFiniteType.isFiniteType (p := ρ) j
  exact isFiniteType_over_biprod_of_generatingSections σA (ρ.generators j)

/-- Auxiliary statement: generators of the restriction of one factor and finiteness of
the other yield finiteness of the restricted biproduct. -/
lemma isFiniteType_over_biprod_of_generatingSections_left {A B : SheafOfModules.{u} R}
    {W : C} (τA : GeneratingSections (R := R.over W) (A.over W)) [Finite τA.I]
    [IsFiniteType (R := R.over W) (B.over W)] :
    IsFiniteType (R := R.over W) ((A ⊞ B).over W) := by
  haveI : HasBinaryProducts (Over W) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  haveI : PreservesBinaryBiproducts (overFunctor.{u} R W) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  have h1 := isFiniteType_biprod_of_generatingSections_left (B := B.over W) τA
  exact (isFiniteType (R.over W)).prop_of_iso
    ((overFunctor.{u} R W).mapBiprod A B).symm h1

/-- A binary biproduct of finite type sheaves of modules is of finite type. -/
lemma IsFiniteType.biprod {A B : SheafOfModules.{u} R} [A.IsFiniteType] [B.IsFiniteType] :
    IsFiniteType (R := R) (A ⊞ B) := by
  obtain ⟨σ, hσ⟩ := IsFiniteType.exists_localGeneratorsData A
  refine IsFiniteType.of_coversTop_of_forall (A ⊞ B) σ.X σ.coversTop (fun i ↦ ?_)
  haveI := LocalGeneratorsData.IsFiniteType.isFiniteType (p := σ) i
  haveI : IsFiniteType (R := R.over (σ.X i)) (B.over (σ.X i)) := .over B (σ.X i)
  exact isFiniteType_over_biprod_of_generatingSections_left (σ.generators i)

/-- Auxiliary statement for `SheafOfModules.IsCoherent.biprod`: relation-finiteness of
kernels of morphisms into a restricted binary biproduct of coherent sheaves. -/
lemma isFiniteType_kernel_to_biprod_over {A B : SheafOfModules.{u} R}
    [A.IsCoherent] [B.IsCoherent] {X : C} {I : Type u} [Finite I]
    (ψ : free I ⟶ A.over X ⊞ B.over X) : (kernel ψ).IsFiniteType := by
  haveI h1 := IsCoherent.isFiniteType_kernel (M := A) (ψ ≫ biprod.fst)
  haveI : IsCoherent (R := R.over X) (B.over X) := IsCoherent.over B X
  have h2 := isFiniteType_kernel_of_isCoherent (M := B.over X)
    (kernel.ι (ψ ≫ biprod.fst) ≫ ψ ≫ biprod.snd)
  exact (isFiniteType (R.over X)).prop_of_iso (kernelBiprodIso ψ) h2

/-- A binary biproduct of coherent sheaves of modules is coherent. -/
lemma IsCoherent.biprod {A B : SheafOfModules.{u} R} [A.IsCoherent] [B.IsCoherent] :
    IsCoherent (R := R) (A ⊞ B) where
  isFiniteType := .biprod
  hasFiniteTypeRelations X := by
    intro I _ ψ
    haveI : PreservesBinaryBiproducts (overFunctor.{u} R X) :=
      preservesBinaryBiproducts_of_preservesBinaryCoproducts _
    have h := isFiniteType_kernel_to_biprod_over (A := A) (B := B)
      (ψ ≫ ((overFunctor.{u} R X).mapBiprod A B).hom)
    exact (SheafOfModules.isFiniteType (R.over X)).prop_of_iso
      (kernelCompMono ψ ((overFunctor.{u} R X).mapBiprod A B).hom) h

/-- A zero sheaf of modules is coherent. -/
lemma isCoherent_of_isZero {M : SheafOfModules.{u} R} (h : IsZero M) : M.IsCoherent where
  isFiniteType := by
    let σ : M.GeneratingSections :=
      ⟨PEmpty.{u + 1}, fun i ↦ i.elim, ⟨fun g₁ g₂ _ ↦ h.eq_of_src g₁ g₂⟩⟩
    haveI : σ.IsFiniteType := ⟨inferInstanceAs (Finite PEmpty.{u + 1})⟩
    exact IsFiniteType.of_generatingSections (M := M) σ
  hasFiniteTypeRelations X := by
    intro I _ φ
    have hz : IsZero (M.over X) := by
      rw [IsZero.iff_id_eq_zero]
      calc 𝟙 (M.over X) = (overFunctor.{u} R X).map (𝟙 M) := by
            rw [CategoryTheory.Functor.map_id]
        _ = (overFunctor.{u} R X).map 0 := by rw [(IsZero.iff_id_eq_zero M).mp h]
        _ = 0 := Functor.map_zero _ _ _
    have h1 : IsFiniteType (R := R.over X) (free I) := by
      haveI : HasBinaryProducts (Over X) :=
        Over.ConstructProducts.over_binaryProduct_of_pullback
      exact IsFiniteType.of_generatingSections (M := free (R := R.over X) I)
        (freeGeneratingSections I)
    exact (SheafOfModules.isFiniteType (R.over X)).prop_of_iso
      (kernelIsoOfEq (f := φ) (g := 0) (hz.eq_of_tgt φ 0) ≪≫ kernelZeroIsoSource).symm h1

/-- If the unit is coherent, every free sheaf of modules on a finite type is coherent. -/
lemma IsCoherent.free [IsCoherent (R := R) (unit R)] (I : Type u) [Finite I] :
    IsCoherent (R := R) (SheafOfModules.free (R := R) I) := by
  have key : ∀ (n : ℕ) (I : Type u), (I ≃ Fin n) →
      IsCoherent (R := R) (SheafOfModules.free (R := R) I) := by
    intro n
    induction n with
    | zero =>
      intro I e
      haveI : IsEmpty I := e.isEmpty
      exact isCoherent_of_isZero (isZero_free_of_isEmpty I)
    | succ n ih =>
      intro I e
      haveI h1 : IsCoherent (R := R) (SheafOfModules.free (R := R) (ULift.{u} (Fin n))) :=
        ih _ Equiv.ulift
      haveI h2 : IsCoherent (R := R) (SheafOfModules.free (R := R) PUnit.{u + 1}) :=
        (isCoherent R).prop_of_iso freePUnitIso.symm ‹_›
      haveI h3 : IsCoherent (R := R)
          (SheafOfModules.free (R := R) (ULift.{u} (Fin n)) ⊞
            SheafOfModules.free (R := R) PUnit.{u + 1}) :=
        .biprod
      have e' : I ≃ (ULift.{u} (Fin n) ⊕ PUnit.{u + 1}) :=
        e.trans ((finSumFinEquiv (m := n) (n := 1)).symm.trans
          (Equiv.sumCongr Equiv.ulift.symm (Equiv.equivPUnit.{1, u + 1} (Fin 1))))
      exact (isCoherent R).prop_of_iso
        ((freeFunctor (R := R)).mapIso e'.toIso ≪≫ (freeSumIso _ _).symm ≪≫
          (biprod.isoCoprod _ _).symm).symm h3
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  exact key n I e

end SheafOfModules
