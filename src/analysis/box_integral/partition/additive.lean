/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.partition.split_induction

/-!
# Box-additive functions
-/

namespace box_integral
open set box partition function
open_locale classical big_operators
noncomputable theory

variables {ι M : Type*}

/-- A function on `box ι` is called box additive if for every box `I` and a hyperplane
`{y | y i = x}` we have `f (I ∩ {y | y i ≤ x}) + f (I ∩ {y | x < y i}) = f I`.
We formualte this property in terms of `box_integral.box.split_lower` and
`box_integral.box.split_upper`. -/
structure box_additive_map (ι : Type*) (M : Type*) [has_add M] :=
(to_fun : box ι → M)
(map_split_add' : ∀ (I : box ι) (i x hl hu),
  to_fun ((I.split_lower i x).get hl) + to_fun ((I.split_upper i x).get hu) = to_fun I)

namespace box_additive_map

section has_add

variables {N : Type*} [has_add M] [has_add N]

instance : has_coe_to_fun (box_additive_map ι M) := ⟨_, to_fun⟩

initialize_simps_projections box_integral.box_additive_map (to_fun → apply)

@[simp] lemma to_fun_eq_coe (f : box_additive_map ι M) : f.to_fun = f := rfl

@[simp] lemma coe_mk (f : box ι → M) (h : _) : ⇑(mk f h) = f := rfl

lemma coe_injective : injective (λ (f : box_additive_map ι M) x, f x) :=
by { rintro ⟨f, hf⟩ ⟨g, hg⟩ (rfl : f = g), refl }

@[simp] lemma coe_inj {f g : box_additive_map ι M} : (f : box ι → M) = g ↔ f = g :=
coe_injective.eq_iff

@[simp] lemma map_split_add (f : box_additive_map ι M)
  {I : box ι} {i : ι} {x : ℝ} (hl : I.lower i < x) (hu : x < I.upper i) :
  f ((I.split_lower i x).get hl) + f ((I.split_upper i x).get hu) = f I :=
f.map_split_add' I i x hl hu

/-- If `g : M → N` is an additive map and `f` is a box additive map, then `g ∘ f` is a box additive
map. -/
@[simps { fully_applied := ff }] def map (f : box_additive_map ι M) (g : add_hom M N) :
  box_additive_map ι N :=
{ to_fun := g ∘ f,
  map_split_add' := λ J i x hl hu, by simp [← g.map_add] }

end has_add

section add_zero_class

variable [add_zero_class M]

@[simps { fully_applied := ff }] instance : has_zero (box_additive_map ι M) :=
⟨⟨0, λ I i x hl hu, add_zero 0⟩⟩

instance : inhabited (box_additive_map ι M) := ⟨0⟩

lemma map_split_get_or_else (f : box_additive_map ι M) (I : box ι) (i : ι) (x : ℝ) :
  ((I.split_lower i x).map f).get_or_else 0 + ((I.split_upper i x).map f).get_or_else 0 = f I :=
begin
  rw map_split_lower_add_upper_get_or_else_zero,
  split_ifs, exacts [f.map_split_add _ _, rfl]
end

/-- If `f : box ι → M` is box-additive on subboxes of `I`, then `J ↦ f (I ∩ J)` is box-additive on
all boxes. -/
@[simps { attrs := [] }] def of_additive_on_box (I : box ι) (f : box ι → M)
  (H : ∀ (J ≤ I) i x hl hu, f ((split_lower J i x).get hl) + f ((split_upper J i x).get hu) = f J) :
  box_additive_map ι M :=
{ to_fun := λ J, ((I.inter J).map f).get_or_else 0,
  map_split_add' :=
    begin
      replace H : ∀ (J ≤ I) (i x),
        f J = ((J.split_lower i x).map f).get_or_else 0 + ((J.split_upper i x).map f).get_or_else 0,
      { intros J hJ i x,
        rw map_split_lower_add_upper_get_or_else_zero,
        split_ifs, exacts [(H J hJ i x _ _).symm, rfl] },
      intros J i x hl hu,
      rw [eq_comm, part.get_or_else], split_ifs with hJ; dsimp at hJ,
      { convert H ((I.inter J).get hJ) (inter_get_le_left _) i x; { ext, simp [inter_assoc] } },
      { rw [part.get_or_else, part.get_or_else, dif_neg, dif_neg, add_zero],
        { exact mt (nonempty.mono (inter_subset_inter_right _ J.split_upper_get_le)) hJ },
        { exact mt (nonempty.mono (inter_subset_inter_right _ J.split_lower_get_le)) hJ } }
    end }

lemma of_additive_on_box_apply_of_le {I J : box ι} (Hle : J ≤ I) {f : box ι → M}
  (H : ∀ (J ≤ I) i x hl hu, f ((split_lower J i x).get hl) + f ((split_upper J i x).get hu) = f J) :
  of_additive_on_box I f H J = f J :=
by simp [of_additive_on_box_apply, inter_of_ge Hle]

end add_zero_class

section add_comm_monoid

variables [add_comm_monoid M]

instance : has_add (box_additive_map ι M) :=
⟨λ f g, ⟨f + g, λ I i x hl hu, by simp_rw [pi.add_apply, add_assoc,
  add_left_comm (g _) (f _), g.map_split_add, ← add_assoc, f.map_split_add]⟩⟩

instance : add_comm_monoid (box_additive_map ι M) :=
function.injective.add_comm_monoid _ coe_injective rfl (λ _ _, rfl)

lemma sum_partition_boxes [fintype ι] (f : box_additive_map ι M) {I : box ι} (π : partition I) :
  ∑ J in π.boxes, f J = f I :=
begin
  refine partition.split_induction_on' π
    (λ J s, ∑ J' in s, f J' = f J) (λ J hJ, _)
    (λ J hJ i x hl hu, _) (λ J hJ π πi H, _),
  { simp },
  { rw [finset.sum_pair, f.map_split_add],
    exact box.split_lower_get_ne_split_upper_get _ _ },
  { refine eq.congr _ rfl,
    exact (π.sum_bUnion_boxes (λ J, πi J) _).trans (finset.sum_congr rfl H) }
end

end add_comm_monoid

/-- Let `f` be a family of box additive maps on hyperplanes `{y | y i = x}`. Formally, for each real
`x`, `f x` is a box additive map on `{i}ᶜ → G`. -/
@[simps] def {u v} upper_sub_lower {ι : Type u} {G : Type v} [add_comm_group G]
  (i : ι) (f : ℝ → box_additive_map ↥({i}ᶜ : set ι) G) :
  box_additive_map ι G :=
{ to_fun := λ J : box ι, f (J.upper i) (comap coe J) - f (J.lower i) (comap coe J),
  map_split_add' :=
    begin
      intros J j x hl hu,
      rcases eq_or_ne i j with rfl|hne,
      { have : i ∉ ({i}ᶜ : set ι), from not_not.2 rfl,
        simp [comap_coe_split_upper_get_of_not_mem _ _ _ _ this,
          comap_coe_split_lower_get_of_not_mem _ _ _ _ this,
          min_eq_left (le_of_lt hu), max_eq_left (le_of_lt hl)] },
     { have A : j ∈ ({i}ᶜ : set ι), from hne.symm,
       simp only [comap_coe_split_upper_get_of_mem _ _ _ _ A,
         comap_coe_split_lower_get_of_mem _ _ _ _ A,
         split_lower_get_lower, split_lower_get_upper, split_upper_get_lower,
         split_upper_get_upper, update_noteq hne, sub_add_sub],
       rw [(f _).map_split_add, (f _).map_split_add] }
    end }

end box_additive_map

namespace box

/-- The volume of a box is the product `Π i, (I.upper i - I.lower i)`. -/
@[simps { attrs := [] }] def volume [fintype ι] : box_additive_map ι ℝ :=
{ to_fun := λ I, ∏ i, (I.upper i - I.lower i),
  map_split_add' :=
    begin
      rintros J i x (hl : J.lower i < x) (hu : x < J.upper i),
      simp only [← finset.prod_mul_prod_compl ({i} : finset ι), finset.prod_singleton, update_same,
        add_mul, split_lower, split_upper, ← sub_add_sub_cancel' x (J.lower i) (J.upper i),
        min_eq_left hu.le, max_eq_left hl.le],
      congr' 2; { apply finset.prod_congr rfl, intros j hj, rw update_noteq, simpa using hj }
    end }

lemma volume_pos [fintype ι] (I : box ι) : 0 < I.volume :=
finset.prod_pos (λ i _, sub_pos.2 $ I.lower_lt_upper i)

@[simp] lemma volume_comap_coe_mul [fintype ι] (i : ι) (I : box ι) :
  volume (comap (coe : ({i}ᶜ : set ι) → ι) I) * (I.upper i - I.lower i) = volume I :=
begin
  rw [volume_apply, volume_apply, ← finset.prod_compl_mul_prod ({i} : finset ι),
    finset.prod_singleton],
  congr' 1,
  convert (finset.prod_subtype _ _ _).symm; simp [funext_iff]
end

end box

end box_integral
