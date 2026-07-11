/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import MathlibStaging.Algebra.Category.ModuleCat.Sheaf.Coherent.Basic
public import MathlibStaging.Init

/-!
# Stability properties of coherent sheaves of modules

We prove the basic stability results for coherent sheaves of modules on a small
site `(C, J)` where `C` has pullbacks:

- `SheafOfModules.IsCoherent.of_mono`: a finite type subsheaf of a coherent sheaf
  is coherent.
- `SheafOfModules.isFiniteType_kernel_of_isCoherent`: the kernel of a morphism from
  a finite type sheaf to a coherent sheaf is of finite type.

We work over small sites since the sheafification and local bijectivity instances
for the involved sites (and their iterated slice sites) are then available; this
covers in particular sheaves on the site of opens of a topological space.

## References

- [Jean-Pierre Serre, *Faisceaux algébriques cohérents*][serre1955], §2
- https://stacks.math.columbia.edu/tag/01BY

-/

@[expose] public section

universe u

open CategoryTheory Limits

/-- If `π` is an epimorphism, the square

```
F --π ≫ φ--> M
|            ‖
π            𝟙
v            v
N ----φ----> M
```

is a pushout square. -/
lemma CategoryTheory.IsPushout.of_epi_comp_id {A : Type*} [Category A] {F N M : A}
    (π : F ⟶ N) (φ : N ⟶ M) [Epi π] : IsPushout (π ≫ φ) π (𝟙 M) φ :=
  IsPushout.of_isColimit (c := PushoutCocone.mk (𝟙 M) φ (by simp)) <|
    PushoutCocone.IsColimit.mk _ (fun s ↦ s.inl)
      (fun s ↦ by simp)
      (fun s ↦ by rw [← cancel_epi π]; simpa using s.condition)
      (fun s m h₁ h₂ ↦ by simpa using h₁)

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] [HasPullbacks C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

omit [HasPullbacks C] in
/-- A finite type subsheaf of a coherent sheaf of modules is coherent. -/
lemma IsCoherent.of_mono {N M : SheafOfModules.{u} R} (i : N ⟶ M) [Mono i]
    [N.IsFiniteType] [M.IsCoherent] : N.IsCoherent where
  isFiniteType := inferInstance
  hasFiniteTypeRelations X := by
    intro I _ φ
    haveI : Mono (i.over X) := inferInstance
    haveI : (kernel (φ ≫ i.over X)).IsFiniteType :=
      IsCoherent.isFiniteType_kernel (φ ≫ i.over X)
    exact IsFiniteType.of_iso (M := kernel (φ ≫ i.over X)) (kernelCompMono φ (i.over X))

/-- Auxiliary statement for `SheafOfModules.isFiniteType_kernel_of_isCoherent`: if the
restriction of `N` to `X` admits finitely many generating sections and `M` is coherent,
then the restriction of `kernel φ` to `X` is of finite type. -/
lemma isFiniteType_over_kernel_of_isCoherent {N M : SheafOfModules.{u} R} (φ : N ⟶ M)
    [M.IsCoherent] {X : C} (σ : (N.over X).GeneratingSections) [σ.IsFiniteType] :
    IsFiniteType (R := R.over X) ((kernel φ).over X) := by
  haveI : HasBinaryProducts (Over X) :=
    Over.ConstructProducts.over_binaryProduct_of_pullback
  haveI : (kernel (σ.π ≫ φ.over X)).IsFiniteType :=
    IsCoherent.isFiniteType_kernel (σ.π ≫ φ.over X)
  let κ : kernel (σ.π ≫ φ.over X) ⟶ kernel (φ.over X) :=
    kernel.map (σ.π ≫ φ.over X) (φ.over X) σ.π (𝟙 _) (by simp)
  haveI : Epi κ :=
    Abelian.epi_kernel_map_of_isPushout (.of_epi_comp_id σ.π (φ.over X))
  haveI : (kernel (φ.over X)).IsFiniteType :=
    IsFiniteType.of_epi (N := kernel (φ.over X)) κ
  exact IsFiniteType.of_iso (M := kernel (φ.over X)) (overKernelIso φ X).symm

/-- The kernel of a morphism from a finite type sheaf of modules to a coherent sheaf
of modules is of finite type. -/
lemma isFiniteType_kernel_of_isCoherent {N M : SheafOfModules.{u} R} (φ : N ⟶ M)
    [N.IsFiniteType] [M.IsCoherent] : (kernel φ).IsFiniteType := by
  obtain ⟨σ, hσ⟩ := IsFiniteType.exists_localGeneratorsData N
  haveI (i : σ.I) : IsFiniteType (R := R.over (σ.X i)) ((kernel φ).over (σ.X i)) :=
    haveI := LocalGeneratorsData.IsFiniteType.isFiniteType (p := σ) i
    isFiniteType_over_kernel_of_isCoherent φ (σ.generators i)
  exact IsFiniteType.of_coversTop (kernel φ) σ.X σ.coversTop

/-- The kernel of a morphism of coherent sheaves of modules is coherent. -/
lemma IsCoherent.kernel {M N : SheafOfModules.{u} R} (φ : M ⟶ N)
    [M.IsCoherent] [N.IsCoherent] : (Limits.kernel φ).IsCoherent :=
  haveI : (Limits.kernel φ).IsFiniteType := isFiniteType_kernel_of_isCoherent φ
  .of_mono (Limits.kernel.ι φ)

omit [HasPullbacks C] in
/-- The cokernel of a morphism into a finite type sheaf of modules is of finite type. -/
lemma isFiniteType_cokernel [HasBinaryProducts C] {M N : SheafOfModules.{u} R} (φ : M ⟶ N)
    [N.IsFiniteType] : (cokernel φ).IsFiniteType :=
  IsFiniteType.of_epi (N := cokernel φ) (cokernel.π φ)

omit [HasPullbacks C] in
/-- The image of a morphism of coherent sheaves of modules is coherent. -/
lemma IsCoherent.image [HasBinaryProducts C] {M N : SheafOfModules.{u} R} (φ : M ⟶ N)
    [M.IsCoherent] [N.IsCoherent] : (Abelian.image φ).IsCoherent :=
  haveI : (Abelian.image φ).IsFiniteType :=
    IsFiniteType.of_epi (N := Abelian.image φ) (Abelian.factorThruImage φ)
  .of_mono (Abelian.image.ι φ)

end SheafOfModules
