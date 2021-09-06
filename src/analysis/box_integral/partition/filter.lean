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

variables {ι : Type*} [fintype ι] {I J : box ι} {c : ℝ≥0} {r : (ι → ℝ) → ℝ}

namespace tagged_prepartition

def union_subordinate_compl (π : tagged_prepartition I) (r : (ι → ℝ) → ℝ) :
  tagged_prepartition I :=
(π.union_compl (π.to_prepartition.compl.to_subordinate r)).get (show _ = _, by simp)

@[simp] lemma distortion_union_subordinate_compl (π : tagged_prepartition I) (r : (ι → ℝ) → ℝ) :
  (π.union_subordinate_compl r).distortion = max π.distortion π.to_prepartition.compl.distortion :=
finset.sup_union.trans $ congr_arg (max _) $ prepartition.distortion_to_subordinate _ _

lemma is_partition_union_subordinate_compl (π : tagged_prepartition I) (r : (ι → ℝ) → ℝ) :
  is_partition (π.union_subordinate_compl r) :=
is_partition_union_compl_get _

end tagged_prepartition

@[ext] structure integration_filter : Type :=
(bRiemann bHenstock bDistortion : bool)

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

def to_set (l : integration_filter) (I : box ι) (c : ℝ≥0) (r : (ι → ℝ) → ℝ) :
  set (tagged_prepartition I) :=
{π | π.is_subordinate r ∧ (l.bHenstock → π.is_Henstock) ∧
  (l.bDistortion → π.distortion ≤ c ∧ π.to_prepartition.compl.distortion ≤ c)}

def r_cond (l : integration_filter) (I : box ι) (r : (ι → ℝ) → ℝ) : Prop :=
(∀ x ∈ I.Icc, 0 < r x) ∧ ∀ x ∈ I.Icc, l.bRiemann → r x = r I.upper

def to_filter_distortion (l : integration_filter) (I : box ι) (c : ℝ≥0) :
  filter (tagged_prepartition I) :=
⨅ (r : (ι → ℝ) → ℝ) (hr : l.r_cond I r), 𝓟 (l.to_set I c r)

def to_filter (l : integration_filter) (I : box ι) :
  filter (tagged_prepartition I) :=
⨆ c : ℝ≥0, l.to_filter_distortion I c

def to_filter_distortion_Union (l : integration_filter) (I : box ι) (c : ℝ≥0)
  (π₀ : prepartition I) :=
l.to_filter_distortion I c ⊓ 𝓟 {π | π.Union = π₀.Union}

def to_filter_Union (l : integration_filter) (I : box ι) (π₀ : prepartition I) :=
⨆ c : ℝ≥0, l.to_filter_distortion_Union I c π₀

lemma to_filter_inf_Union_eq (l : integration_filter) (I : box ι) (π₀ : prepartition I) :
  l.to_filter I ⊓ 𝓟 {π | π.Union = π₀.Union} = l.to_filter_Union I π₀ :=
(supr_inf_principal _ _).symm

lemma r_cond_of_bRiemann_eq_ff (l : integration_filter) (hl : l.bRiemann = ff) :
  l.r_cond I r ↔ ∀ x ∈ I.Icc, 0 < r x :=
by simp [r_cond, hl]

@[mono] lemma to_set_mono (I : box ι) {l₁ l₂ : integration_filter} (h : l₁ ≤ l₂)
  {c₁ c₂ : ℝ≥0} (hc : c₁ ≤ c₂) {r₁ r₂ : (ι → ℝ) → ℝ} (hr : ∀ x ∈ I.Icc, r₁ x ≤ r₂ x) :
  l₁.to_set I c₁ r₁ ⊆ l₂.to_set I c₂ r₂ :=
λ π ⟨hr', hH, hd⟩, ⟨hr'.mono hr, λ h₂, hH (le_iff_imp.1 h.2.1 h₂),
  λ h₃, (hd (le_iff_imp.1 h.2.2 h₃)).imp (λ h, h.trans hc) (λ h, h.trans hc)⟩

lemma union_subordinate_compl_mem_to_set {l : integration_filter} {c : ℝ≥0} {r₁ r₂ : (ι → ℝ) → ℝ}
  (hr₁ : ∀ x ∈ I.Icc, 0 < r₁ x) (hr₂ : ∀ x ∈ I.Icc, r₁ x ≤ r₂ x) {π : tagged_prepartition I}
  (hπ : π ∈ l.to_set I c r₂) :
  π.union_subordinate_compl r₁ ∈ l.to_set I c r₂ :=
begin
  refine ⟨hπ.1.union_compl ((prepartition.is_subordinate_to_subordinate _ hr₁).mono hr₂) _,
    λ hH, ((hπ.2.1 hH).union_compl (prepartition.is_Henstock_to_subordinate _ _) _),
    λ hd, _⟩,
  rw [π.distortion_union_subordinate_compl,
    (π.is_partition_union_subordinate_compl _).compl_eq_bot, prepartition.distortion_bot],
  exact ⟨max_le (hπ.2.2 hd).1 (hπ.2.2 hd).2, zero_le c⟩
end

lemma bUnion_tagged_mem_to_set {l : integration_filter} {c : ℝ≥0} {r : (ι → ℝ) → ℝ}
  {π : prepartition I} {πi : Π J, tagged_prepartition J}
  (h : ∀ J ∈ π, πi J ∈ l.to_set J c r) (hp : ∀ J ∈ π, (πi J).is_partition)
  (hc : l.bDistortion → π.compl.distortion ≤ c) :
  π.bUnion_tagged πi ∈ l.to_set I c r :=
begin
  refine ⟨tagged_prepartition.is_subordinate_bUnion_tagged.2 $ λ J hJ, (h J hJ).1,
    λ hH, tagged_prepartition.is_Henstock_bUnion_tagged.2 $ λ J hJ, (h J hJ).2.1 hH,
    λ hD, ⟨_, _⟩⟩,
  { rw [prepartition.distortion_bUnion_tagged, finset.sup_le_iff],
    exact λ J hJ, ((h J hJ).2.2 hD).1 },
  { convert hc hD using 2, apply prepartition.compl_congr,
    exact π.Union_bUnion_partition hp }
end

@[mono] lemma r_cond.mono {I : box ι} {l₁ l₂ : integration_filter} (h : l₁ ≤ l₂) {r : (ι → ℝ) → ℝ}
  (hr :  l₂.r_cond I r) : l₁.r_cond I r :=
⟨hr.1, λ x hx hR, hr.2 x hx (le_iff_imp.1 h.1 hR)⟩

lemma r_cond.to_subbox {I J : box ι} {l : integration_filter} {r : (ι → ℝ) → ℝ} (hr : l.r_cond I r)
  (hJ : J ≤ I) : l.r_cond J r :=
have J.Icc ⊆ I.Icc, from box.le_iff_Icc.1 hJ,
⟨λ x hx, hr.1 x (this hx),
  λ x hx hR, (hr.2 x (this hx) hR).trans (hr.2 _ (this J.upper_mem_Icc) hR).symm⟩

lemma r_cond.min {I : box ι} {l : integration_filter} {r₁ r₂ : (ι → ℝ) → ℝ}
  (h₁ : l.r_cond I r₁) (h₂ : l.r_cond I r₂) : l.r_cond I (λ x, min (r₁ x) (r₂ x)) :=
⟨λ x hx, lt_min (h₁.1 x hx) (h₂.1 x hx), λ x hx h, congr_arg2 min (h₁.2 x hx h) (h₂.2 x hx h)⟩

@[mono] lemma to_filter_distortion_mono (I : box ι) {l₁ l₂ : integration_filter} (h : l₁ ≤ l₂)
  {c₁ c₂ : ℝ≥0} (hc : c₁ ≤ c₂) :
  l₁.to_filter_distortion I c₁ ≤ l₂.to_filter_distortion I c₂ :=
infi_le_infi $ λ r, infi_le_infi2 $ λ hr,
  ⟨hr.mono h, principal_mono.2 $ to_set_mono I h hc (λ _ _, le_rfl)⟩

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
  (l.to_filter_distortion I c).has_basis (l.r_cond I) (l.to_set I c) :=
has_basis_binfi_principal'
  (λ r₁ hr₁ r₂ hr₂, ⟨_, hr₁.min hr₂,
    to_set_mono _ le_rfl le_rfl (λ x hx, min_le_left _ _),
    to_set_mono _ le_rfl le_rfl (λ x hx, min_le_right _ _)⟩)
  ⟨λ _, 1, λ x hx, zero_lt_one, λ _ _ _, rfl⟩

lemma has_basis_to_filter_distortion_Union (l : integration_filter) (I : box ι) (c : ℝ≥0)
  (π₀ : prepartition I) :
  (l.to_filter_distortion_Union I c π₀).has_basis (l.r_cond I)
    (λ r, l.to_set I c r ∩ {π | π.Union = π₀.Union}) :=
(l.has_basis_to_filter_distortion I c).inf_principal _

lemma has_basis_to_filter_Union (l : integration_filter) (I : box ι) (π₀ : prepartition I) :
  (l.to_filter_Union I π₀).has_basis (λ r : ℝ≥0 → (ι → ℝ) → ℝ, ∀ c, l.r_cond I (r c))
    (λ r, ⋃ c, l.to_set I c (r c) ∩ {π | π.Union = π₀.Union}) :=
have _ := λ c, l.has_basis_to_filter_distortion_Union I c π₀,
has_basis_supr this

lemma has_basis_to_filter_Union_top (l : integration_filter) (I : box ι) :
  (l.to_filter_Union I ⊤).has_basis (λ r : ℝ≥0 → (ι → ℝ) → ℝ, ∀ c, l.r_cond I (r c))
    (λ r, ⋃ c, l.to_set I c (r c) ∩ {π | π.is_partition}) :=
by simpa only [tagged_prepartition.is_partition_iff_Union_eq, prepartition.Union_top]
  using l.has_basis_to_filter_Union I ⊤

lemma has_basis_to_filter (l : integration_filter) (I : box ι) :
  (l.to_filter I).has_basis (λ r : ℝ≥0 → (ι → ℝ) → ℝ, ∀ c, l.r_cond I (r c))
    (λ r, ⋃ c, l.to_set I c (r c)) :=
has_basis_supr (l.has_basis_to_filter_distortion I)

lemma tendsto_embed_box_to_filter_Union_top (l : integration_filter) (h : I ≤ J) :
  tendsto (tagged_prepartition.embed_box I J h) (l.to_filter_Union I ⊤)
    (l.to_filter_Union J (prepartition.single J I h)) :=
begin
  simp only [to_filter_Union, tendsto_supr], intro c,
  refine le_supr_of_le (max c (prepartition.single J I h).compl.distortion) _,
  refine ((l.has_basis_to_filter_distortion_Union I c ⊤).tendsto_iff
    (l.has_basis_to_filter_distortion_Union J _ _)).2 (λ r hr, _),
  have : I.Icc ⊆ J.Icc, from box.le_iff_Icc.1 h,
  refine ⟨r, hr.to_subbox h, λ π hπ, _⟩,
  rw [mem_inter_eq, mem_set_of_eq, prepartition.Union_top] at hπ,
  rw [prepartition.Union_single],
  refine ⟨⟨hπ.1.1, hπ.1.2.1, λ hD, ⟨le_trans _ (le_max_left _ _), _⟩⟩, hπ.2⟩,
  { exact (hπ.1.2.2 hD).1 },
  { convert le_max_right _ _ using 3,
    exact prepartition.compl_congr ((prepartition.Union_single _).trans hπ.2.symm) }
end

lemma nonempty_to_set_inter_le_Union_eq (l : integration_filter) {I : box ι} (π₀ : prepartition I)
  {c : ℝ≥0} (hc₁ : π₀.distortion ≤ c) (hc₂ : π₀.compl.distortion ≤ c)
  {r : (ι → ℝ) → ℝ} (hr : ∀ x ∈ I.Icc, 0 < r x) :
  (l.to_set I c r ∩ {π | π.to_prepartition ≤ π₀ ∧ π.Union = π₀.Union}).nonempty :=
begin
  rcases π₀.exists_tagged_le_is_Henstock_is_subordinate_Union_eq hr
    with ⟨π, hle, hH, hr, hd, hU⟩,
  exact ⟨π, ⟨hr, λ _, hH, λ _, ⟨hd.trans_le hc₁, by rwa [prepartition.compl_congr hU]⟩⟩, ⟨hle, hU⟩⟩
end

lemma nonempty_to_set_inter_is_partition (l : integration_filter) (I : box ι) {c : ℝ≥0}
  (hc : I.distortion ≤ c) {r : (ι → ℝ) → ℝ} (hr : ∀ x ∈ I.Icc, 0 < r x) :
  (l.to_set I c r ∩ {π | π.is_partition}).nonempty :=
begin
  rcases (⊤ : prepartition I).exists_tagged_le_is_Henstock_is_subordinate_Union_eq hr
    with ⟨π, hle, hH, hr, hd, hU⟩,
  rw prepartition.distortion_top at hd,
  rw [prepartition.Union_top, ← tagged_prepartition.is_partition_iff_Union_eq] at hU,
  refine ⟨π, ⟨hr, λ _, hH, λ hD, ⟨hd.symm ▸ hc, _⟩⟩, hU⟩,
  rw [hU.compl_eq_bot, prepartition.distortion_bot], exact zero_le c
end

lemma to_filter_distortion_Union_ne_bot (l : integration_filter) (I : box ι)
  (π₀ : prepartition I) (hc₁ : π₀.distortion ≤ c) (hc₂ : π₀.compl.distortion ≤ c) :
  (l.to_filter_distortion_Union I c π₀).ne_bot :=
((l.has_basis_to_filter_distortion I _).inf_principal _).ne_bot_iff.2 $ λ r hr,
  (l.nonempty_to_set_inter_le_Union_eq π₀ hc₁ hc₂ hr.1).mono $
    inter_subset_inter_right _ $ λ π, and.right

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
