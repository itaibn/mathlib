/-
Copyright (c) 2021 Yourong Zang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yourong Zang, Yury Kudryashov
-/
import topology.separation
import topology.opens

/-!
# The Alexandroff Compactification

We construct the Alexandroff compactification of an arbitrary topological space `X` and prove
some properties inherited from `X`.

## Main defintion

* `alexandroff`: the Alexandroff compactification, we use coercion for the canonical embedding
  `X → alexandroff X`;
* `alexandroff.infty`: the extra point

## Main results
* The topological structure of `alexandroff X`
* The connectedness of `alexandroff X` for a noncompact, preconnected `X`
* `alexandroff X` is `T₀` for a T₀ space `X`
* `alexandroff X` is `T₁` for a T₁ space `X`
* `alexandroff X` is normal if `X` is locally compact and Hausdorff

## Tags

one-point compactification, compactness
-/

open set filter
open_locale classical topological_space filter

/-!
### Definition and basic properties

In this section we define `alexandroff X` to be the disjoint union of `X` and `∞`, implemented as
`option X`. Then we restate some lemmas about `option X` for `alexandroff X`.
-/

/-- The Alexandroff extension of an arbitrary topological space `X` -/
def alexandroff (X : Type*) := option X

namespace alexandroff

variables {X : Type*}

/-- The point at infinity -/
def infty : alexandroff X := none
localized "notation `∞` := alexandroff.infty" in alexandroff

instance : has_coe_t X (alexandroff X) := ⟨option.some⟩

instance : inhabited (alexandroff X) := ⟨∞⟩

lemma coe_injective : function.injective (coe : X → alexandroff X) :=
option.some_injective X

@[simp, norm_cast] lemma coe_eq_coe {x y : X} : (x : alexandroff X) = y ↔ x = y :=
coe_injective.eq_iff

@[simp] lemma coe_ne_infty (x : X) : (x : alexandroff X) ≠ ∞  .
@[simp] lemma infty_ne_coe (x : X) : ∞ ≠ (x : alexandroff X) .
@[simp] lemma some_eq_coe (x : X) : some x = (x : alexandroff X) := rfl
@[simp] lemma none_eq_infty : none = (∞ : alexandroff X) := rfl

/-- Recursor for `alexandroff` using the preferred forms `∞` and `↑x`. -/
@[elab_as_eliminator]
protected def rec (C : alexandroff X → Sort*) (h₁ : C ∞) (h₂ : Π x : X, C x) :
  Π (z : alexandroff X), C z :=
option.rec h₁ h₂

lemma is_compl_range_coe_infty : is_compl (range (coe : X → alexandroff X)) {∞} :=
is_compl_range_some_none X

@[simp] lemma range_coe_union_infty : (range (coe : X → alexandroff X) ∪ {∞}) = univ :=
range_some_union_none X

@[simp] lemma range_coe_inter_infty : (range (coe : X → alexandroff X) ∩ {∞}) = ∅ :=
range_some_inter_none X

@[simp] lemma compl_range_coe : (range (coe : X → alexandroff X))ᶜ = {∞} :=
compl_range_some X

lemma compl_infty : ({∞}ᶜ : set (alexandroff X)) = range (coe : X → alexandroff X) :=
(@is_compl_range_coe_infty X).symm.compl_eq

lemma compl_image_coe (s : set X) : (coe '' s : set (alexandroff X))ᶜ = coe '' sᶜ ∪ {∞} :=
by rw [coe_injective.compl_image_eq, compl_range_coe]

lemma ne_infty_iff_exists {x : alexandroff X} :
  x ≠ ∞ ↔ ∃ (y : X), (y : alexandroff X) = x :=
by induction x using alexandroff.rec; simp

instance : can_lift (alexandroff X) X :=
{ coe := coe,
  cond := λ x, x ≠ ∞,
  prf := λ x, ne_infty_iff_exists.1 }

lemma not_mem_range_coe_iff {x : alexandroff X} :
  x ∉ range (coe : X → alexandroff X) ↔ x = ∞ :=
by rw [← mem_compl_iff, compl_range_coe, mem_singleton_iff]

lemma infty_not_mem_range_coe : ∞ ∉ range (coe : X → alexandroff X) :=
not_mem_range_coe_iff.2 rfl

lemma infty_not_mem_image_coe {s : set X} : ∞ ∉ (coe : X → alexandroff X) '' s :=
not_mem_subset (image_subset_range _ _) infty_not_mem_range_coe

@[simp] lemma coe_preimage_infty : (coe : X → alexandroff X) ⁻¹' {∞} = ∅ :=
by { ext, simp }

/-!
### Topological space structure on `alexandroff X`

We define a topological space structure on `alexandroff X` so that `s` is open if and only if

* `coe ⁻¹' s` is open in `X`;
* if `∞ ∈ s`, then `(coe ⁻¹' s)ᶜ` is compact.

Then we reformulate this definition in a few different ways, and prove that
`coe : X → alexandroff X` is an open embedding. If `X` is not a compact space, then we also prove
that `coe` has dense range, so it is a dense embedding.
-/

variables [topological_space X]

instance : topological_space (alexandroff X) :=
{ is_open := λ s, (∞ ∈ s → is_compact ((coe : X → alexandroff X) ⁻¹' s)ᶜ) ∧
    is_open ((coe : X → alexandroff X) ⁻¹' s),
  is_open_univ := by simp,
  is_open_inter := λ s t,
  begin
    rintros ⟨hms, hs⟩ ⟨hmt, ht⟩,
    refine ⟨_, hs.inter ht⟩,
    rintros ⟨hms', hmt'⟩,
    simpa [compl_inter] using (hms hms').union (hmt hmt')
  end,
  is_open_sUnion := λ S ho,
  begin
    suffices : is_open (coe ⁻¹' ⋃₀ S : set X),
    { refine ⟨_, this⟩,
      rintro ⟨s, hsS : s ∈ S, hs : ∞ ∈ s⟩,
      refine compact_of_is_closed_subset ((ho s hsS).1 hs) this.is_closed_compl _,
      exact compl_subset_compl.mpr (preimage_mono $ subset_sUnion_of_mem hsS) },
    rw [preimage_sUnion],
    exact is_open_bUnion (λ s hs, (ho s hs).2)
  end }

variables {s : set (alexandroff X)} {t : set X}

lemma is_open_def :
  is_open s ↔ (∞ ∈ s → is_compact (coe ⁻¹' s : set X)ᶜ) ∧ is_open (coe ⁻¹' s : set X) :=
iff.rfl

lemma is_open_iff_of_mem' (h : ∞ ∈ s) :
  is_open s ↔ is_compact (coe ⁻¹' s : set X)ᶜ ∧ is_open (coe ⁻¹' s : set X) :=
by simp [is_open_def, h]

lemma is_open_iff_of_mem (h : ∞ ∈ s) :
  is_open s ↔ is_closed (coe ⁻¹' s : set X)ᶜ ∧ is_compact (coe ⁻¹' s : set X)ᶜ :=
by simp only [is_open_iff_of_mem' h, is_closed_compl_iff, and.comm]

lemma is_open_iff_of_not_mem (h : ∞ ∉ s) :
  is_open s ↔ is_open (coe ⁻¹' s : set X) :=
by simp [is_open_def, h]

lemma is_closed_iff_of_mem (h : ∞ ∈ s) :
  is_closed s ↔ is_closed (coe ⁻¹' s : set X) :=
have ∞ ∉ sᶜ, from λ H, H h,
by rw [← is_open_compl_iff, is_open_iff_of_not_mem this, ← is_open_compl_iff, preimage_compl]

lemma is_closed_iff_of_not_mem (h : ∞ ∉ s) :
  is_closed s ↔ is_closed (coe ⁻¹' s : set X) ∧ is_compact (coe ⁻¹' s : set X) :=
by rw [← is_open_compl_iff, is_open_iff_of_mem (mem_compl h), ← preimage_compl, compl_compl]

@[simp] lemma is_open_image_coe {s : set X} :
  is_open (coe '' s : set (alexandroff X)) ↔ is_open s :=
by rw [is_open_iff_of_not_mem infty_not_mem_image_coe, preimage_image_eq _ coe_injective]

lemma is_open_compl_image_coe {s : set X} :
  is_open (coe '' s : set (alexandroff X))ᶜ ↔ is_closed s ∧ is_compact s :=
begin
  rw [is_open_iff_of_mem, ← preimage_compl, compl_compl, preimage_image_eq _ coe_injective],
  exact infty_not_mem_image_coe
end

@[simp] lemma is_closed_image_coe {s : set X} :
  is_closed (coe '' s : set (alexandroff X)) ↔ is_closed s ∧ is_compact s :=
by rw [← is_open_compl_iff, is_open_compl_image_coe]

/-- An open set in `alexandroff X` constructed from a closed compact set in `X` -/
def opens_of_compl (s : set X) (h₁ : is_closed s) (h₂ : is_compact s) :
  topological_space.opens (alexandroff X) :=
⟨(coe '' s)ᶜ, is_open_compl_image_coe.2 ⟨h₁, h₂⟩⟩

lemma infty_mem_opens_of_compl {s : set X} (h₁ : is_closed s) (h₂ : is_compact s) :
  ∞ ∈ opens_of_compl s h₁ h₂ :=
mem_compl infty_not_mem_image_coe

@[continuity] lemma continuous_coe : continuous (coe : X → alexandroff X) :=
continuous_def.mpr (λ s hs, hs.right)

lemma is_open_map_coe  : is_open_map (coe : X → alexandroff X) :=
λ s, is_open_image_coe.2

lemma open_embedding_coe : open_embedding (coe : X → alexandroff X) :=
open_embedding_of_continuous_injective_open continuous_coe coe_injective is_open_map_coe

lemma is_open_range_coe : is_open (range (coe : X → alexandroff X)) :=
open_embedding_coe.open_range

lemma is_closed_infty : is_closed ({∞} : set (alexandroff X)) :=
by { rw [← compl_range_coe, is_closed_compl_iff], exact is_open_range_coe }

lemma nhds_coe_eq (x : X) : 𝓝 ↑x = map (coe : X → alexandroff X) (𝓝 x) :=
(open_embedding_coe.map_nhds_eq x).symm

lemma nhds_within_coe_image (s : set X) (x : X) :
  𝓝[coe '' s] (x : alexandroff X) = map coe (𝓝[s] x) :=
by rw [nhds_within, nhds_within, map_inf coe_injective, nhds_coe_eq, map_principal]

lemma comap_coe_nhds (x : X) : comap (coe : X → alexandroff X) (𝓝 x) = 𝓝 x :=
(open_embedding_coe.to_inducing.nhds_eq_comap x).symm

lemma nhds_infty_eq : 𝓝 (∞ : alexandroff X) = map coe (coclosed_compact X) ⊔ pure ∞ :=
begin
  refine (nhds_basis_opens ∞).ext ((has_basis_coclosed_compact.map _).sup_pure _) _ _,
  { rintro s ⟨hs, hso⟩,
    refine ⟨_, (is_open_iff_of_mem hs).mp hso, _⟩,
    simp [insert_subset, hs] },
  { rintro s ⟨h₁, h₂⟩,
    refine ⟨_, ⟨mem_compl infty_not_mem_image_coe, is_open_compl_image_coe.2 ⟨h₁, h₂⟩⟩, _⟩,
    rw compl_image_coe }
end

lemma has_basis_nhds_infty :
  (𝓝 (∞ : alexandroff X)).has_basis (λ s : set X, is_closed s ∧ is_compact s)
    (λ s, coe '' sᶜ ∪ {∞}) :=
begin
  rw nhds_infty_eq,
  exact (has_basis_coclosed_compact.map _).sup_pure _
end

@[simp] lemma comap_coe_nhds_infty : comap (coe : X → alexandroff X) (𝓝 ∞) = coclosed_compact X :=
by simp [nhds_infty_eq, comap_sup, comap_map coe_injective]

lemma le_nhds_infty {f : filter (alexandroff X)} :
  f ≤ 𝓝 ∞ ↔ ∀ s : set X, is_closed s → is_compact s → coe '' sᶜ ∪ {∞} ∈ f :=
by simp only [has_basis_nhds_infty.ge_iff, and_imp]

lemma ultrafilter_le_nhds_infty {f : ultrafilter (alexandroff X)} :
  (f : filter (alexandroff X)) ≤ 𝓝 ∞ ↔ ∀ s : set X, is_closed s → is_compact s → coe '' s ∉ f :=
by simp only [le_nhds_infty, ← compl_image_coe, ultrafilter.mem_coe,
  ultrafilter.compl_mem_iff_not_mem]

lemma tendsto_nhds_infty {α : Type*} {f : alexandroff X → α} {l : filter α} :
  tendsto f (𝓝 ∞) l ↔
    ∀ s ∈ l, f ∞ ∈ s ∧ ∃ t : set X, is_closed t ∧ is_compact t ∧ maps_to (f ∘ coe) tᶜ s :=
has_basis_nhds_infty.tendsto_left_iff.trans $ forall_congr $ λ s, forall_congr $ λ hs,
  by simp only [← exists_and_distrib_left, exists_prop, maps_to_union, maps_image_to,
    maps_to_singleton, and_comm, and_assoc, and.left_comm]

lemma continuous_at_infty {Y : Type*} [topological_space Y] {f : alexandroff X → Y} :
  continuous_at f ∞ ↔
    ∀ s ∈ 𝓝 (f ∞), ∃ t : set X, is_closed t ∧ is_compact t ∧ maps_to (f ∘ coe) tᶜ s :=
tendsto_nhds_infty.trans $ forall_congr $ λ s, forall_congr $ λ hs,
  and_iff_right $ mem_of_mem_nhds hs

lemma continuous_at_coe {Y : Type*} [topological_space Y] {f : alexandroff X → Y} {x : X} :
  continuous_at f x ↔ continuous_at (f ∘ coe) x :=
by rw [continuous_at, nhds_coe_eq, tendsto_map'_iff, continuous_at]

/-- If `X` is not a compact space, then the natural embedding `X → alexandroff X` has dense range.
-/
lemma dense_range_coe (h : ¬ is_compact (univ : set X)) :
  dense_range (coe : X → alexandroff X) :=
begin
  rw [dense_range, ← compl_infty, dense_compl_singleton, is_open_iff_of_mem (mem_singleton _),
    coe_preimage_infty, compl_empty],
  exact mt and.right h
end

lemma dense_embedding_coe (h : ¬is_compact (univ : set X)) :
  dense_embedding (coe : X → alexandroff X) :=
{ dense := dense_range_coe h, .. open_embedding_coe }

/-!
### Compactness and separation properties

In this section we prove that `alexandroff X` is a compact space; it is a T₀ (resp., T₁) space if
the original space satisfies the same separation axiom. If the original space is a locally compact
Hausdorff space, then `alexandroff X` is a normal (hence, regular and Hausdorff) space.

Finally, if the original space `X` is *not* compact and is a preconnected space, then
`alexandroff X` is a connected space. This statement cannot be an `instance` because it needs a
non-class argument `¬is_compact (univ : set X)`.
-/

/-- For any topological space `X`, its one point compactification is a compact space. -/
instance : compact_space (alexandroff X) :=
{ compact_univ :=
  begin
    refine is_compact_iff_ultrafilter_le_nhds.2 (λ f hf, _), clear hf,
    by_cases hf : (f : filter (alexandroff X)) ≤ 𝓝 ∞,
    { exact ⟨∞, mem_univ _, hf⟩ },
    { simp only [ultrafilter_le_nhds_infty, not_forall, not_not] at hf,
      rcases hf with ⟨s, h₁, h₂, hsf⟩,
      have hf : range (coe : X → alexandroff X) ∈ f,
        from mem_sets_of_superset hsf (image_subset_range _ _),
      have hsf' : s ∈ f.comap coe_injective hf, from (f.mem_comap _ _).2 hsf,
      rcases h₂.ultrafilter_le_nhds _ (le_principal_iff.2 hsf') with ⟨a, has, hle⟩,
      rw [ultrafilter.coe_comap, ← comap_coe_nhds, comap_le_comap_iff hf] at hle,
      exact ⟨a, mem_univ _, hle⟩ }
  end }

/-- The one point compactification of a `t0_space` space is a `t0_space`. -/
instance [t0_space X] : t0_space (alexandroff X) :=
begin
  refine ⟨λ x y hxy, _⟩,
  induction x using alexandroff.rec; induction y using alexandroff.rec,
  { exact (hxy rfl).elim },
  { use {∞}ᶜ, simp [is_closed_infty] },
  { use {∞}ᶜ, simp [is_closed_infty] },
  { rcases t0_space.t0 x y (mt coe_eq_coe.mpr hxy) with ⟨U, hUo, hU⟩,
    refine ⟨coe '' U, is_open_image_coe.2 hUo, _⟩,
    simpa }
end

/-- The one point compactification of a `t1_space` space is a `t1_space`. -/
instance [t1_space X] : t1_space (alexandroff X) :=
{ t1 := λ z,
  begin
    induction z using alexandroff.rec,
    { exact is_closed_infty },
    { simp only [← image_singleton, is_closed_image_coe],
      exact ⟨is_closed_singleton, is_compact_singleton⟩ }
  end }

/-- The one point compactification of a locally compact Hausdorff space is a normal (hence,
Hausdorff and regular) topological space. -/
instance [locally_compact_space X] [t2_space X] : normal_space (alexandroff X) :=
begin
  have key : ∀ z : X,
    ∃ u v : set (alexandroff X), is_open u ∧ is_open v ∧ ↑z ∈ u ∧ ∞ ∈ v ∧ u ∩ v = ∅,
  { intro z,
    rcases exists_open_with_compact_closure z with ⟨u, hu, huy', Hu⟩,
    refine ⟨coe '' u, (coe '' closure u)ᶜ, is_open_image_coe.2 hu,
      is_open_compl_image_coe.2 ⟨is_closed_closure, Hu⟩, mem_image_of_mem _ huy',
      mem_compl infty_not_mem_image_coe, _⟩,
    rw [← subset_compl_iff_disjoint, compl_compl],
    exact image_subset _ subset_closure },
  refine @normal_of_compact_t2 _ _ _ ⟨λ x y hxy, _⟩,
  induction x using alexandroff.rec; induction y using alexandroff.rec,
  { exact (hxy rfl).elim },
  { rcases key y with ⟨u, v, hu, hv, hxu, hyv, huv⟩,
    exact ⟨v, u, hv, hu, hyv, hxu, (inter_comm u v) ▸ huv⟩ },
  { exact key x },
  { exact separated_by_open_embedding open_embedding_coe (mt coe_eq_coe.mpr hxy) }
end

/-- If `X` is not a compact space, then `alexandroff X` is a connected space. -/
lemma connected_space_alexandroff [preconnected_space X] (h : ¬ is_compact (univ : set X)) :
  connected_space (alexandroff X) :=
{ to_preconnected_space := (dense_embedding_coe h).to_dense_inducing.preconnected_space,
  to_nonempty := infer_instance }

end alexandroff
