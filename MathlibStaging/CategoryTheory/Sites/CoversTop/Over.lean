/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import MathlibStaging.Init

/-!
-/

@[expose] public section

universe v' u'

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

/-- A family of objects covering the top induces, for every `W : C`, a family of objects
of `Over W` covering the top: the family of all objects of `Over W` whose underlying
object admits a morphism to some member of the family. -/
lemma CoversTop.over' {I : Type*} {X : I → C} (hX : J.CoversTop X) (W : C) :
    (J.over W).CoversTop
      (fun (t : (i : I) × (V : C) × (V ⟶ X i) × (V ⟶ W)) ↦ Over.mk t.2.2.2) := by
  intro U
  rw [mem_over_iff]
  refine J.superset_covering ?_ (hX U.left)
  rintro V g ⟨i, ⟨f⟩⟩
  exact ⟨Over.mk (g ≫ U.hom), Over.homMk g, 𝟙 _,
    ⟨⟨i, V, f, g ≫ U.hom⟩, ⟨Over.homMk (𝟙 _)⟩⟩, (Category.id_comp _).symm⟩

end CategoryTheory.GrothendieckTopology
