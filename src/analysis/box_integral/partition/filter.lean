/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.partition.subbox_induction
import analysis.box_integral.partition.additive

open set function filter metric finset bool
open_locale classical topological_space filter nnreal
noncomputable theory

namespace box_integral

variables {ι : Type*} [fintype ι] {I J : box ι} {c c₁ c₂ : ℝ≥0} {r r₁ r₂ : (ι → ℝ) → Ioi (0 : ℝ)}
  {π π₁ π₂ : tagged_prepartition I}

open tagged_prepartition

@[ext] structure integration_filter : Type :=
(bRiemann bHenstock bDistortion : bool)

variables {l l₁ l₂ : integration_filter}

namespace integration_filter

instance : bounded_lattice integration_filter :=
{ le := λ l₁ l₂, (l₁.1 ≤ l₂.1) ∧ (l₂.2 ≤ l₁.2) ∧ (l₂.3 ≤ l₁.3),
  le_refl := λ l, ⟨le_rfl, le_rfl, le_rfl⟩,
  le_trans := λ l₁ l₂ l₃ h₁₂ h₂₃, ⟨h₁₂.1.trans h₂₃.1, h₂₃.2.1.trans h₁₂.2.1, h₂₃.2.2.trans h₁₂.2.2⟩,
  le_antisymm := λ l₁ l₂ h₁₂ h₂₁, ext _ _ (le_antisymm h₁₂.1 h₂₁.1) (le_antisymm h₂₁.2.1 h₁₂.2.1)
    (le_antisymm h₂₁.2.2 h₁₂.2.2),
  inf := λ l₁ l₂, ⟨l₁.1 && l₂.1, l₁.2 || l₂.2, l₁.3 || l₂.3⟩,
  inf_le_left := λ l₁ l₂, ⟨band_le_left _ _, left_le_bor _ _, left_le_bor _ _⟩,
  inf_le_right := λ l₁ l₂, ⟨band_le_right _ _, right_le_bor _ _, right_le_bor _ _⟩,
  le_inf := λ l₁ l₂ l₃ h₁ h₂, ⟨le_band h₁.1 h₂.1, bor_le h₁.2.1 h₂.2.1, bor_le h₁.2.2 h₂.2.2⟩,
  sup := λ l₁ l₂, ⟨l₁.1 || l₂.1, l₁.2 && l₂.2, l₁.3 && l₂.3⟩,
  le_sup_left := λ l₁ l₂, ⟨left_le_bor _ _, band_le_left _ _, band_le_left _ _⟩,
  le_sup_right := λ l₁ l₂, ⟨right_le_bor _ _, band_le_right _ _, band_le_right _ _⟩,
  sup_le := λ l₁ l₂ l₃ h₁ h₂, ⟨bor_le h₁.1 h₂.1, le_band h₁.2.1 h₂.2.1, le_band h₁.2.2 h₂.2.2⟩,
  bot := ⟨ff, tt, tt⟩,
  bot_le := λ l, ⟨ff_le, le_tt, le_tt⟩,
  top := ⟨tt, ff, ff⟩,
  le_top := λ l, ⟨le_tt, ff_le, ff_le⟩ }

@[protect_proj] structure mem_base_set (l : integration_filter) (I : box ι) (c : ℝ≥0)
  (r : (ι → ℝ) → Ioi (0 : ℝ)) (π : tagged_prepartition I) : Prop :=
(is_subordinate : π.is_subordinate r)
(is_Henstock : l.bHenstock → π.is_Henstock)
(distortion_le : l.bDistortion → π.distortion ≤ c)
(exists_compl : l.bDistortion → ∃ π' : prepartition I, π'.Union = I \ π.Union ∧ π'.distortion ≤ c)

def r_cond (l : integration_filter) (r : (ι → ℝ) → Ioi (0 : ℝ)) : Prop := l.bRiemann → ∀ x, r x = r 0

def to_filter_distortion (l : integration_filter) (I : box ι) (c : ℝ≥0) :
  filter (tagged_prepartition I) :=
⨅ (r : (ι → ℝ) → Ioi (0 : ℝ)) (hr : l.r_cond r), 𝓟 {π | l.mem_base_set I c r π}

def to_filter (l : integration_filter) (I : box ι) :
  filter (tagged_prepartition I) :=
⨆ c : ℝ≥0, l.to_filter_distortion I c

def to_filter_distortion_Union (l : integration_filter) (I : box ι) (c : ℝ≥0)
  (π₀ : prepartition I) :=
l.to_filter_distortion I c ⊓ 𝓟 {π | π.Union = π₀.Union}

def to_filter_Union (l : integration_filter) (I : box ι) (π₀ : prepartition I) :=
⨆ c : ℝ≥0, l.to_filter_distortion_Union I c π₀

lemma r_cond_of_bRiemann_eq_ff (l : integration_filter) (hl : l.bRiemann = ff) :
  l.r_cond r :=
by simp [r_cond, hl]

lemma to_filter_inf_Union_eq (l : integration_filter) (I : box ι) (π₀ : prepartition I) :
  l.to_filter I ⊓ 𝓟 {π | π.Union = π₀.Union} = l.to_filter_Union I π₀ :=
(supr_inf_principal _ _).symm

lemma mem_base_set.mono' (I : box ι) (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂) {π : tagged_prepartition I}
  (hr : ∀ J ∈ π, r₁ (π.tag J) ≤ r₂ (π.tag J)) (hπ : l₁.mem_base_set I c₁ r₁ π) :
  l₂.mem_base_set I c₂ r₂ π :=
⟨hπ.1.mono' hr, λ h₂, hπ.2 (le_iff_imp.1 h.2.1 h₂),
  λ hD, (hπ.3 (le_iff_imp.1 h.2.2 hD)).trans hc,
  λ hD, (hπ.4 (le_iff_imp.1 h.2.2 hD)).imp $ λ π hπ, ⟨hπ.1, hπ.2.trans hc⟩⟩

@[mono] lemma mem_base_set.mono (I : box ι) (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂) {π : tagged_prepartition I}
  (hr : ∀ x ∈ I.Icc, r₁ x ≤ r₂ x) (hπ : l₁.mem_base_set I c₁ r₁ π) :
  l₂.mem_base_set I c₂ r₂ π :=
hπ.mono' I h hc $ λ J hJ, hr _ $ π.tag_mem_Icc J

lemma mem_base_set.exists_common_compl (h₁ : l.mem_base_set I c₁ r₁ π₁)
  (h₂ : l.mem_base_set I c₂ r₂ π₂) (hU : π₁.Union = π₂.Union) :
  ∃ π : prepartition I, π.Union = I \ π₁.Union ∧
    (l.bDistortion → π.distortion ≤ c₁) ∧ (l.bDistortion → π.distortion ≤ c₂) :=
begin
  wlog hc : c₁ ≤ c₂ := le_total c₁ c₂ using [c₁ c₂ r₁ r₂ π₁ π₂, c₂ c₁ r₂ r₁ π₂ π₁] tactic.skip,
  { by_cases hD : (l.bDistortion : Prop),
    { rcases h₁.4 hD with ⟨π, hπU, hπc⟩,
      exact ⟨π, hπU, λ _, hπc, λ _, hπc.trans hc⟩ },
    { exact ⟨π₁.to_prepartition.compl, π₁.to_prepartition.Union_compl,
        λ h, (hD h).elim, λ h, (hD h).elim⟩ } },
  { intros h₁ h₂ hU,
    simpa [hU, and_comm] using this h₂ h₁ hU.symm }
end

protected lemma mem_base_set.union_compl_to_subordinate (hπ₁ : l.mem_base_set I c r₁ π₁)
  (hle : ∀ x ∈ I.Icc, r₂ x ≤ r₁ x) {π₂ : prepartition I}
  (hU : π₂.Union = I \ π₁.Union) (hc : l.bDistortion → π₂.distortion ≤ c) :
  l.mem_base_set I c r₁ (π₁.union_compl_to_subordinate π₂ hU r₂) :=
⟨hπ₁.1.disj_union ((π₂.is_subordinate_to_subordinate r₂).mono hle) _,
  λ h, ((hπ₁.2 h).disj_union (π₂.is_Henstock_to_subordinate _) _),
  λ h, (distortion_union_compl_to_subordinate _ _ _ _).trans_le (max_le (hπ₁.3 h) (hc h)),
  λ _, ⟨⊥, by simp⟩⟩

protected lemma mem_base_set.filter (hπ : l.mem_base_set I c r π) (p : box ι → Prop) :
  l.mem_base_set I c r (π.filter p) :=
begin
  refine ⟨λ J hJ, hπ.1 J (π.mem_filter.1 hJ).1, λ hH J hJ, hπ.2 hH J (π.mem_filter.1 hJ).1,
    λ hD, (distortion_filter_le _ _).trans (hπ.3 hD), λ hD, _⟩,
  rcases hπ.4 hD with ⟨π₁, hπ₁U, hc⟩,
  set π₂ := π.filter (λ J, ¬p J),
  have : disjoint π₁.Union π₂.Union,
    by simpa [π₂, hπ₁U] using (disjoint_diff.mono_left sdiff_le).symm,
  refine ⟨π₁.disj_union π₂.to_prepartition this, _, _⟩,
  { suffices : ↑I \ π.Union ∪ π.Union \ (π.filter p).Union = ↑I \ (π.filter p).Union, by simpa *,
    have : (π.filter p).Union ⊆ π.Union, from bUnion_subset_bUnion_left (finset.filter_subset _ _),
    ext x, fsplit,
    { rintro (⟨hxI, hxπ⟩|⟨hxπ, hxp⟩),
      exacts [⟨hxI, mt (@this x) hxπ⟩, ⟨π.Union_subset hxπ, hxp⟩] },
    { rintro ⟨hxI, hxp⟩, by_cases hxπ : x ∈ π.Union,
      exacts [or.inr ⟨hxπ, hxp⟩, or.inl ⟨hxI, hxπ⟩] } },
  { have : (π.filter (λ J, ¬p J)).distortion ≤ c, from (distortion_filter_le _ _).trans (hπ.3 hD),
    simpa [hc] }
end

lemma bUnion_tagged_mem_base_set {π : prepartition I} {πi : Π J, tagged_prepartition J}
  (h : ∀ J ∈ π, l.mem_base_set J c r (πi J)) (hp : ∀ J ∈ π, (πi J).is_partition)
  (hc : l.bDistortion → π.compl.distortion ≤ c) :
  l.mem_base_set I c r (π.bUnion_tagged πi) :=
begin
  refine ⟨tagged_prepartition.is_subordinate_bUnion_tagged.2 $ λ J hJ, (h J hJ).1,
    λ hH, tagged_prepartition.is_Henstock_bUnion_tagged.2 $ λ J hJ, (h J hJ).2 hH,
    λ hD, _, λ hD, _⟩,
  { rw [prepartition.distortion_bUnion_tagged, finset.sup_le_iff],
    exact λ J hJ, (h J hJ).3 hD },
  { refine ⟨_, _, hc hD⟩,
    rw [π.Union_compl, ← π.Union_bUnion_partition hp], refl }
end

@[mono] lemma r_cond.mono (h : l₁ ≤ l₂) (hr :  l₂.r_cond r) : l₁.r_cond r :=
λ hR, hr (le_iff_imp.1 h.1 hR)

lemma r_cond.min (h₁ : l.r_cond r₁) (h₂ : l.r_cond r₂) : l.r_cond (λ x, min (r₁ x) (r₂ x)) :=
λ hR x, congr_arg2 min (h₁ hR x) (h₂ hR x)

@[mono] lemma to_filter_distortion_mono (I : box ι) (h : l₁ ≤ l₂) (hc : c₁ ≤ c₂) :
  l₁.to_filter_distortion I c₁ ≤ l₂.to_filter_distortion I c₂ :=
infi_le_infi $ λ r, infi_le_infi2 $ λ hr,
  ⟨hr.mono h, principal_mono.2 $ λ _, mem_base_set.mono I h hc (λ _ _, le_rfl)⟩

@[mono] lemma to_filter_mono (I : box ι) {l₁ l₂ : integration_filter} (h : l₁ ≤ l₂) :
  l₁.to_filter I ≤ l₂.to_filter I :=
supr_le_supr $ λ c, to_filter_distortion_mono I h le_rfl

@[mono] lemma to_filter_Union_mono (I : box ι) {l₁ l₂ : integration_filter} (h : l₁ ≤ l₂)
  (π₀ : prepartition I) :
  l₁.to_filter_Union I π₀ ≤ l₂.to_filter_Union I π₀ :=
supr_le_supr $ λ c, inf_le_inf_right _ $ to_filter_distortion_mono _ h le_rfl

lemma to_filter_Union_congr (I : box ι) (l : integration_filter) {π₁ π₂ : prepartition I}
  (h : π₁.Union = π₂.Union) : l.to_filter_Union I π₁ = l.to_filter_Union I π₂ :=
by simp only [to_filter_Union, to_filter_distortion_Union, h]

lemma has_basis_to_filter_distortion (l : integration_filter) (I : box ι) (c : ℝ≥0) :
  (l.to_filter_distortion I c).has_basis l.r_cond (λ r, {π | l.mem_base_set I c r π}) :=
has_basis_binfi_principal'
  (λ r₁ hr₁ r₂ hr₂, ⟨_, hr₁.min hr₂,
    λ _, mem_base_set.mono _ le_rfl le_rfl (λ x hx, min_le_left _ _),
    λ _, mem_base_set.mono _ le_rfl le_rfl (λ x hx, min_le_right _ _)⟩)
  ⟨λ _, ⟨1, @zero_lt_one ℝ _ _⟩, λ _ _, rfl⟩

lemma has_basis_to_filter_distortion_Union (l : integration_filter) (I : box ι) (c : ℝ≥0)
  (π₀ : prepartition I) :
  (l.to_filter_distortion_Union I c π₀).has_basis l.r_cond
    (λ r, {π | l.mem_base_set I c r π ∧ π.Union = π₀.Union}) :=
(l.has_basis_to_filter_distortion I c).inf_principal _

lemma has_basis_to_filter_Union (l : integration_filter) (I : box ι) (π₀ : prepartition I) :
  (l.to_filter_Union I π₀).has_basis (λ r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ), ∀ c, l.r_cond (r c))
    (λ r, {π | ∃ c, l.mem_base_set I c (r c) π ∧ π.Union = π₀.Union}) :=
have _ := λ c, l.has_basis_to_filter_distortion_Union I c π₀,
by simpa only [set_of_and, set_of_exists] using has_basis_supr this

lemma has_basis_to_filter_Union_top (l : integration_filter) (I : box ι) :
  (l.to_filter_Union I ⊤).has_basis (λ r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ), ∀ c, l.r_cond (r c))
    (λ r, {π | ∃ c, l.mem_base_set I c (r c) π ∧ π.is_partition}) :=
by simpa only [tagged_prepartition.is_partition_iff_Union_eq, prepartition.Union_top]
  using l.has_basis_to_filter_Union I ⊤

lemma has_basis_to_filter (l : integration_filter) (I : box ι) :
  (l.to_filter I).has_basis (λ r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ), ∀ c, l.r_cond (r c))
    (λ r, {π | ∃ c, l.mem_base_set I c (r c) π}) :=
by simpa only [set_of_exists] using has_basis_supr (l.has_basis_to_filter_distortion I)

lemma tendsto_embed_box_to_filter_Union_top (l : integration_filter) (h : I ≤ J) :
  tendsto (tagged_prepartition.embed_box I J h) (l.to_filter_Union I ⊤)
    (l.to_filter_Union J (prepartition.single J I h)) :=
begin
  simp only [to_filter_Union, tendsto_supr], intro c,
  set π₀ := (prepartition.single J I h),
  refine le_supr_of_le (max c π₀.compl.distortion) _,
  refine ((l.has_basis_to_filter_distortion_Union I c ⊤).tendsto_iff
    (l.has_basis_to_filter_distortion_Union J _ _)).2 (λ r hr, _),
  refine ⟨r, hr, λ π hπ, _⟩,
  rw [mem_set_of_eq, prepartition.Union_top] at hπ,
  refine ⟨⟨hπ.1.1, hπ.1.2, λ hD, le_trans (hπ.1.3 hD) (le_max_left _ _), λ hD, _⟩, _⟩,
  { refine ⟨_, π₀.Union_compl.trans _, le_max_right _ _⟩, congr' 1,
    exact (prepartition.Union_single h).trans hπ.2.symm },
  { exact hπ.2.trans (prepartition.Union_single _).symm }
end

lemma exists_mem_base_set_le_Union_eq (l : integration_filter) (π₀ : prepartition I)
  (hc₁ : π₀.distortion ≤ c) (hc₂ : π₀.compl.distortion ≤ c) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
  ∃ π, l.mem_base_set I c r π ∧ π.to_prepartition ≤ π₀ ∧ π.Union = π₀.Union :=
begin
  rcases π₀.exists_tagged_le_is_Henstock_is_subordinate_Union_eq r
    with ⟨π, hle, hH, hr, hd, hU⟩,
  refine ⟨π, ⟨hr, λ _, hH, λ _, hd.trans_le hc₁, λ hD, ⟨π₀.compl, _, hc₂⟩⟩, ⟨hle, hU⟩⟩,
  exact prepartition.compl_congr hU ▸ π.to_prepartition.Union_compl
end

lemma exists_mem_base_set_is_partition (l : integration_filter) (I : box ι)
  (hc : I.distortion ≤ c) (r : (ι → ℝ) → Ioi (0 : ℝ)) :
  ∃ π, l.mem_base_set I c r π ∧ π.is_partition :=
begin
  rw ← prepartition.distortion_top at hc,
  have hc' : (⊤ : prepartition I).compl.distortion ≤ c, by simp,
  simpa [is_partition_iff_Union_eq] using l.exists_mem_base_set_le_Union_eq ⊤ hc hc' r
end

lemma to_filter_distortion_Union_ne_bot (l : integration_filter) (I : box ι)
  (π₀ : prepartition I) (hc₁ : π₀.distortion ≤ c) (hc₂ : π₀.compl.distortion ≤ c) :
  (l.to_filter_distortion_Union I c π₀).ne_bot :=
((l.has_basis_to_filter_distortion I _).inf_principal _).ne_bot_iff.2 $ λ r hr,
  (l.exists_mem_base_set_le_Union_eq π₀ hc₁ hc₂ r).imp $ λ π hπ, ⟨hπ.1, hπ.2.2⟩

instance to_filter_distortion_Union_ne_bot' (l : integration_filter) (I : box ι)
  (π₀ : prepartition I) :
  (l.to_filter_distortion_Union I (max π₀.distortion π₀.compl.distortion) π₀).ne_bot :=
l.to_filter_distortion_Union_ne_bot I π₀ (le_max_left _ _) (le_max_right _ _)

instance to_filter_distortion_ne_bot (l : integration_filter) (I : box ι) :
  (l.to_filter_distortion I I.distortion).ne_bot :=
by simpa using (l.to_filter_distortion_Union_ne_bot' I ⊤).mono inf_le_left

instance to_filter_ne_bot (l : integration_filter) (I : box ι) : (l.to_filter I).ne_bot :=
(l.to_filter_distortion_ne_bot I).mono $ le_supr _ _

instance to_filter_Union_ne_bot (l : integration_filter) (I : box ι) (π₀ : prepartition I) :
  (l.to_filter_Union I π₀).ne_bot :=
(l.to_filter_distortion_Union_ne_bot' I π₀).mono $
  le_supr (λ c, l.to_filter_distortion_Union I c π₀) _

instance : decidable_rel ((≤) : integration_filter → integration_filter → Prop) :=
λ _ _, and.decidable

instance : decidable_eq integration_filter := λ x y, decidable_of_iff _ (ext_iff x y).symm

lemma eventually_is_partition (l : integration_filter) (I : box ι) :
  ∀ᶠ π in l.to_filter_Union I ⊤, tagged_prepartition.is_partition π :=
eventually_supr.2 $ λ c, eventually_inf_principal.2 $ eventually_of_forall $
  λ π h, π.is_partition_iff_Union_eq.2 (h.trans prepartition.Union_top)

def Riemann : integration_filter := ⟨tt, tt, ff⟩

def McShane : integration_filter := ⟨ff, ff, ff⟩

def Henstock : integration_filter := ⟨ff, tt, ff⟩

lemma Henstock_le_Riemann : Henstock ≤ Riemann := dec_trivial

lemma Henstock_le_McShane : Henstock ≤ McShane := dec_trivial

end integration_filter

end box_integral
