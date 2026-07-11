/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import MathlibStaging.Init

/-!
-/

@[expose] public section

universe v' u'

namespace CategoryTheory

open Limits

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

lemma coverPreserving_iteratedSliceForward {X : C} (Y : Over X) :
    CoverPreserving ((J.over X).over Y) (J.over Y.left) Y.iteratedSliceForward :=
  (Y.iteratedSliceEquiv.symm.toAdjunction.isCocontinuous_iff_coverPreserving
    (J := J.over Y.left) (K := (J.over X).over Y)).mp
    (inferInstanceAs (Y.iteratedSliceBackward.IsCocontinuous _ _))

lemma coverPreserving_iteratedSliceBackward {X : C} (Y : Over X) :
    CoverPreserving (J.over Y.left) ((J.over X).over Y) Y.iteratedSliceBackward :=
  (Y.iteratedSliceEquiv.toAdjunction.isCocontinuous_iff_coverPreserving
    (J := (J.over X).over Y) (K := J.over Y.left)).mp
    (inferInstanceAs (Y.iteratedSliceForward.IsCocontinuous _ _))

instance {X : C} (Y : Over X) (W : Over Y) :
    (Over.post Y.iteratedSliceEquiv.functor).IsContinuous (((J.over X).over Y).over W)
      ((J.over Y.left).over (Y.iteratedSliceEquiv.functor.obj W)) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    ((coverPreserving_iteratedSliceForward (J := J) Y).overPost W)

instance {X : C} (Y : Over X) (W : Over Y.left) :
    (Over.post Y.iteratedSliceEquiv.inverse).IsContinuous ((J.over Y.left).over W)
      (((J.over X).over Y).over (Y.iteratedSliceEquiv.inverse.obj W)) :=
  Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
    ((coverPreserving_iteratedSliceBackward (J := J) Y).overPost W)

end CategoryTheory
