/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.monad.algebra
import category_theory.adjunction

namespace category_theory
open category

universes v₁ v₂ u₁ u₂ -- morphism levels before object levels. See note [category_theory universes].

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
variables {L : C ⥤ D} {R : D ⥤ C}

namespace adjunction

/--
For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induces a monad on
the category `C`.
-/
@[simps]
def to_monad (h : L ⊣ R) : monad C :=
{ to_functor := L ⋙ R,
  η' := h.unit,
  μ' := whisker_right (whisker_left L h.counit) R,
  assoc' := λ X, by { dsimp, rw [←R.map_comp], simp },
  right_unit' := λ X, by { dsimp, rw [←R.map_comp], simp } }

/--
For a pair of functors `L : C ⥤ D`, `R : D ⥤ C`, an adjunction `h : L ⊣ R` induces a comonad on
the category `D`.
-/
@[simps]
def to_comonad (h : L ⊣ R) : comonad D :=
{ to_functor := R ⋙ L,
  ε' := h.counit,
  δ' := whisker_right (whisker_left R h.unit) L,
  coassoc' := λ X, by { dsimp, rw ← L.map_comp, simp },
  right_counit' := λ X, by { dsimp, rw ← L.map_comp, simp } }

@[simps {rhs_md := semireducible}]
def test {L : C ⥤ D} {R₁ R₂ : D ⥤ C} (h₁ : L ⊣ R₁) (h₂ : L ⊣ R₂) :
  h₁.to_monad ≅ h₂.to_monad :=
monad_iso.mk
  (iso_whisker_left L (adjunction.right_adjoint_uniq h₁ h₂))
  (λ X,
    begin
      dsimp [adjunction.right_adjoint_uniq_hom_app],
      rw [h₂.hom_equiv_unit, ←h₂.unit_naturality_assoc, h₁.hom_equiv_counit, L.map_id,
        ←R₂.map_comp, id_comp, h₁.left_triangle_components],
      dsimp,
      simp,
    end)
  (λ X,
  begin
    dsimp [adjunction.right_adjoint_uniq_hom_app],
    simp only [adjunction.hom_equiv_unit, adjunction.hom_equiv_counit],
    rw [L.map_id, id_comp, L.map_id, id_comp, assoc, assoc, ←R₂.map_comp, ←h₁.counit_naturality,
      R₂.map_comp, h₂.unit_naturality_assoc, ←R₁.map_comp_assoc, L.map_comp, assoc,
      h₂.counit_naturality, h₂.left_triangle_components_assoc],
    refl,
  end)
/-- The monad induced by the Eilenberg-Moore adjunction is the original monad.  -/
@[simps]
def adj_to_monad_iso (T : monad C) : T.adj.to_monad ≅ T :=
monad_iso.mk (nat_iso.of_components (λ X, iso.refl _) (by tidy))
  (λ X, by { dsimp, simp })
  (λ X, by { dsimp, simp })

/-- The comonad induced by the Eilenberg-Moore adjunction is the original comonad. -/
@[simps]
def adj_to_comonad_iso (G : comonad C) : G.adj.to_comonad ≅ G :=
comonad_iso.mk (nat_iso.of_components (λ X, iso.refl _) (by tidy))
  (λ X, by { dsimp, simp })
  (λ X, by { dsimp, simp })

end adjunction

/--
Gven any adjunction `L ⊣ R`, there is a comparison functor `category_theory.monad.comparison R`
sending objects `Y : D` to Eilenberg-Moore algebras for `L ⋙ R` with underlying object `R.obj X`.

We later show that this is full when `R` is full, faithful when `R` is faithful,
and essentially surjective when `R` is reflective.
-/
@[simps]
def monad.comparison (h : L ⊣ R) : D ⥤ h.to_monad.algebra :=
{ obj := λ X,
  { A := R.obj X,
    a := R.map (h.counit.app X),
    assoc' := by { dsimp, rw [← R.map_comp, ← adjunction.counit_naturality, R.map_comp], refl } },
  map := λ X Y f,
  { f := R.map f,
    h' := by { dsimp, rw [← R.map_comp, adjunction.counit_naturality, R.map_comp] } } }.

/--
The underlying object of `(monad.comparison R).obj X` is just `R.obj X`.
-/
@[simps]
def monad.comparison_forget (h : L ⊣ R) :
  monad.comparison h ⋙ h.to_monad.forget ≅ R :=
{ hom := { app := λ X, 𝟙 _, },
  inv := { app := λ X, 𝟙 _, } }.

def monad.free_comparison {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
  L ⋙ monad.comparison h ≅ h.to_monad.free :=
{ hom := { app := λ X, { f := 𝟙 _ } },
  inv := { app := λ X, { f := 𝟙 _ } } }

-- lemma monad.free_comparison_forget {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
--   iso_whisker_right (monad.free_comparison h) h.to_monad.forget = _ :=
-- begin
-- end

lemma monad.comparison_unique_aux {L : C ⥤ D} {R : D ⥤ C} {h : L ⊣ R}
  (K : D ⥤ h.to_monad.algebra)
  (hK₁ : K ⋙ h.to_monad.forget ≅ R)
  (hK₂ : L ⋙ K ≅ h.to_monad.free)
  (hK : ∀ X, (hK₂.hom.app X).f = hK₁.hom.app (L.obj X)) -- compatibility between hK₁ and hK₂
  (X : D) :
  R.map (L.map (hK₁.hom.app X)) ≫ R.map (h.counit.app X) = (K.obj X).a ≫ hK₁.hom.app X :=
begin
  have : ∀ Y, R.map (L.map (hK₂.hom.app Y).f) ≫ R.map (h.counit.app (L.obj Y))
            = (K.obj _).a ≫ (hK₂.hom.app _).f := λ Y, (hK₂.app Y).hom.h,
  simp_rw [hK] at this,
  have := this (R.obj X) =≫ R.map (h.counit.app X),
  rw [assoc, ←R.map_comp, ←R.map_comp] at this,
end

#exit

def monad.comparison_unique {L : C ⥤ D} {R : D ⥤ C} {h : L ⊣ R} (K : D ⥤ h.to_monad.algebra)
  (hK' : K ⋙ h.to_monad.forget ≅ R) :
  K ≅ monad.comparison h :=
nat_iso.of_components
  (λ X, monad.algebra.iso_mk (hK.app X) (begin dsimp, extract_goal end))
  (λ X Y f, by { ext, apply hK.hom.naturality f })

-- begin
--   let : Π B : D, R.obj (L.obj (K'.obj B).A) ⟶ (K'.obj B).A := λ B, (K'.obj B).a,

-- end

lemma monad.left_comparison (h : L ⊣ R) : L ⋙ monad.comparison h = h.to_monad.free := rfl

instance [faithful R] (h : L ⊣ R) :
  faithful (monad.comparison h) :=
{ map_injective' := λ X Y f g w, R.map_injective (congr_arg monad.algebra.hom.f w : _) }

instance (T : monad C) : full (monad.comparison T.adj) :=
{ preimage := λ X Y f, ⟨f.f, by simpa using f.h⟩ }

instance (T : monad C) : ess_surj (monad.comparison T.adj) :=
{ mem_ess_image := λ X,
  ⟨{ A := X.A, a := X.a, unit' := by simpa using X.unit, assoc' := by simpa using X.assoc },
    ⟨monad.algebra.iso_mk (iso.refl _) (by simp)⟩⟩ }

/--
Gven any adjunction `L ⊣ R`, there is a comparison functor `category_theory.comonad.comparison L`
sending objects `X : C` to Eilenberg-Moore coalgebras for `L ⋙ R` with underlying object
`L.obj X`.
-/
@[simps]
def comonad.comparison (h : L ⊣ R) : C ⥤ h.to_comonad.coalgebra :=
{ obj := λ X,
  { A := L.obj X,
    a := L.map (h.unit.app X),
    coassoc' := by { dsimp, rw [← L.map_comp, ← adjunction.unit_naturality, L.map_comp], refl } },
  map := λ X Y f,
  { f := L.map f,
    h' := by { dsimp, rw ← L.map_comp, simp } } }

/--
The underlying object of `(comonad.comparison L).obj X` is just `L.obj X`.
-/
@[simps]
def comonad.comparison_forget {L : C ⥤ D} {R : D ⥤ C} (h : L ⊣ R) :
  comonad.comparison h ⋙ h.to_comonad.forget ≅ L :=
{ hom := { app := λ X, 𝟙 _, },
  inv := { app := λ X, 𝟙 _, } }

lemma comonad.left_comparison (h : L ⊣ R) : R ⋙ comonad.comparison h = h.to_comonad.cofree := rfl

instance comonad.comparison_faithful_of_faithful [faithful L] (h : L ⊣ R) :
  faithful (comonad.comparison h) :=
{ map_injective' := λ X Y f g w, L.map_injective (congr_arg comonad.coalgebra.hom.f w : _) }

instance (G : comonad C) : full (comonad.comparison G.adj) :=
{ preimage := λ X Y f, ⟨f.f, by simpa using f.h⟩ }

instance (G : comonad C) : ess_surj (comonad.comparison G.adj) :=
{ mem_ess_image := λ X,
  ⟨{ A := X.A, a := X.a, counit' := by simpa using X.counit, coassoc' := by simpa using X.coassoc },
    ⟨comonad.coalgebra.iso_mk (iso.refl _) (by simp)⟩⟩ }

/--
A right adjoint functor `R : D ⥤ C` is *monadic* if the comparison functor `monad.comparison R`
from `D` to the category of Eilenberg-Moore algebras for the adjunction is an equivalence.
-/
class monadic_right_adjoint (R : D ⥤ C) extends is_right_adjoint R :=
(eqv : is_equivalence (monad.comparison (adjunction.of_right_adjoint R)))

/--
A left adjoint functor `L : C ⥤ D` is *comonadic* if the comparison functor `comonad.comparison L`
from `C` to the category of Eilenberg-Moore algebras for the adjunction is an equivalence.
-/
class comonadic_left_adjoint (L : C ⥤ D) extends is_left_adjoint L :=
(eqv : is_equivalence (comonad.comparison (adjunction.of_left_adjoint L)))

def monadic_of_iso (R₁ R₂ : D ⥤ C) [monadic_right_adjoint R₁] (i : R₁ ≅ R₂) :
  monadic_right_adjoint R₂ :=
{ to_is_right_adjoint := adjunction.right_adjoint_of_nat_iso i,
  eqv :=
  begin
    letI := adjunction.right_adjoint_of_nat_iso i,
    let z := adjunction.test (adjunction.of_right_adjoint R₁) (adjunction.of_nat_iso_right (adjunction.of_right_adjoint R₁) i),
    let z₂ : _ ≌ (adjunction.of_right_adjoint R₂).to_monad.algebra := monad.algebra_equiv_of_iso_monads z,
    let : monad.comparison (adjunction.of_right_adjoint R₂) ≅ monad.comparison (adjunction.of_right_adjoint R₁) ⋙ z₂.functor,
    { apply nat_iso.of_components _ _,
      { intro X,
        refine monad.algebra.iso_mk (i.symm.app X) _,
        dsimp [adjunction.test, adjunction.right_adjoint_uniq_inv_app],
        simp,
      }
    }
    -- -- have := z₂.functor,
  end

}

noncomputable instance (T : monad C) : monadic_right_adjoint T.forget :=
⟨(equivalence.of_fully_faithfully_ess_surj _ : is_equivalence (monad.comparison T.adj))⟩

noncomputable instance (G : comonad C) : comonadic_left_adjoint G.forget :=
⟨(equivalence.of_fully_faithfully_ess_surj _ : is_equivalence (comonad.comparison G.adj))⟩

-- TODO: This holds more generally for idempotent adjunctions, not just reflective adjunctions.
instance μ_iso_of_reflective [reflective R] : is_iso (adjunction.of_right_adjoint R).to_monad.μ :=
by { dsimp, apply_instance }

attribute [instance] monadic_right_adjoint.eqv
attribute [instance] comonadic_left_adjoint.eqv

namespace reflective

instance [reflective R] (X : (adjunction.of_right_adjoint R).to_monad.algebra) :
  is_iso ((adjunction.of_right_adjoint R).unit.app X.A) :=
⟨⟨X.a, ⟨X.unit, begin
    dsimp only [functor.id_obj],
    rw ← (adjunction.of_right_adjoint R).unit_naturality,
    dsimp only [functor.comp_obj, adjunction.to_monad_coe],
    rw [unit_obj_eq_map_unit, ←functor.map_comp, ←functor.map_comp],
    erw X.unit,
    simp,
  end⟩⟩⟩

instance comparison_ess_surj [reflective R] :
  ess_surj (monad.comparison (adjunction.of_right_adjoint R)) :=
begin
  refine ⟨λ X, ⟨(left_adjoint R).obj X.A, ⟨_⟩⟩⟩,
  symmetry,
  refine monad.algebra.iso_mk _ _,
  { exact as_iso ((adjunction.of_right_adjoint R).unit.app X.A) },
  dsimp only [functor.comp_map, monad.comparison_obj_a, as_iso_hom, functor.comp_obj,
    monad.comparison_obj_A, monad_to_functor_eq_coe, adjunction.to_monad_coe],
  rw [←cancel_epi ((adjunction.of_right_adjoint R).unit.app X.A), adjunction.unit_naturality_assoc,
      adjunction.right_triangle_components, comp_id],
  apply (X.unit_assoc _).symm,
end

instance comparison_full [full R] [is_right_adjoint R] :
  full (monad.comparison (adjunction.of_right_adjoint R)) :=
{ preimage := λ X Y f, R.preimage f.f }

end reflective

-- It is possible to do this computably since the construction gives the data of the inverse, not
-- just the existence of an inverse on each object.
/-- Any reflective inclusion has a monadic right adjoint.
    cf Prop 5.3.3 of [Riehl][riehl2017] -/
@[priority 100] -- see Note [lower instance priority]
noncomputable instance monadic_of_reflective [reflective R] : monadic_right_adjoint R :=
{ eqv := equivalence.of_fully_faithfully_ess_surj _ }

end category_theory
