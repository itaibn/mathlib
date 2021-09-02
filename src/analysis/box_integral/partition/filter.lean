/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.partition.subbox_induction

open set function filter metric finset bool
open_locale classical topological_space filter nnreal
noncomputable theory

namespace box_integral

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

variables {ι : Type*} [fintype ι]

def to_set (l : integration_filter) (I : box ι) (c : ℝ≥0) (r : (ι → ℝ) → ℝ) :
  set (tagged_prepartition I) :=
{π | π.is_subordinate r ∧ (l.bHenstock → π.is_Henstock) ∧ (l.bDistortion → π.distortion ≤ c)}

def prepartition_filter_aux (l : integration_filter) (I : box ι) (c : ℝ≥0) :
  filter (tagged_prepartition I) :=
⨅ (r : (ι → ℝ) → ℝ) (h0 : ∀ x ∈ I.Icc, (0 < r x) ∧ (l.bRiemann → r x = r I.upper)),
  𝓟 (l.to_set I c r)

def prepartition_filter (l : integration_filter) (I : box ι) :
  filter (tagged_prepartition I) :=
⨆ c : ℝ≥0, l.prepartition_filter_aux I c

def partition_filter_aux (l : integration_filter) (I : box ι) (π₀ : prepartition I) (c : ℝ≥0) :=
l.prepartition_filter_aux I c ⊓ 𝓟 {π | π.to_prepartition ≤ π₀ ∧ π.Union = π₀.Union}

def partition_filter (l : integration_filter) (I : box ι) (π₀ : prepartition I) :=
l.prepartition_filter I ⊓ 𝓟 {π | π.to_prepartition ≤ π₀ ∧ π.Union = π₀.Union}

lemma supr_partition_filter_aux (l : integration_filter) (I : box ι) (π₀ : prepartition I) :
  (⨆ c, l.partition_filter_aux I π₀  c) = l.partition_filter I π₀ :=
supr_inf_principal _ _

@[mono] lemma to_set_mono (I : box ι) {l₁ l₂ : integration_filter} (h : l₁ ≤ l₂)
  {c₁ c₂ : ℝ≥0} (hc : c₁ ≤ c₂) {r₁ r₂ : (ι → ℝ) → ℝ} (hr : ∀ x ∈ I.Icc, r₁ x ≤ r₂ x) :
  l₁.to_set I c₁ r₁ ⊆ l₂.to_set I c₂ r₂ :=
λ π ⟨hr', hH, hd⟩, ⟨hr'.mono hr, λ h₂, hH (le_iff_imp.1 h.2.1 h₂),
      λ h₃, (hd (le_iff_imp.1 h.2.2 h₃)).trans hc⟩

@[mono] lemma prepartition_filter_aux_mono (I : box ι) {l₁ l₂ : integration_filter} (h : l₁ ≤ l₂)
  {c₁ c₂ : ℝ≥0} (hc : c₁ ≤ c₂) :
  l₁.prepartition_filter_aux I c₁ ≤ l₂.prepartition_filter_aux I c₂ :=
infi_le_infi $ λ r, infi_le_infi2 $ λ hr,
  ⟨λ x hx, ⟨(hr x hx).1, λ h₁, (hr x hx).2 (le_iff_imp.1 h.1 h₁)⟩,
    principal_mono.2 $ to_set_mono I h hc (λ _ _, le_rfl)⟩

@[mono] lemma prepartition_filter_mono (I : box ι) {l₁ l₂ : integration_filter} (h : l₁ ≤ l₂) :
  l₁.prepartition_filter I ≤ l₂.prepartition_filter I :=
supr_le_supr $ λ c, prepartition_filter_aux_mono I h le_rfl

@[mono] lemma partition_filter_aux_mono (I : box ι) {l₁ l₂ : integration_filter} (h : l₁ ≤ l₂)
  {c₁ c₂ : ℝ≥0} (hc : c₁ ≤ c₂) (π₀ : prepartition I) :
  l₁.partition_filter_aux I π₀ c₁ ≤ l₂.partition_filter_aux I π₀  c₂ :=
inf_le_inf_right _ $ prepartition_filter_aux_mono I h hc

@[mono] lemma partition_filter_mono (I : box ι) {l₁ l₂ : integration_filter} (h : l₁ ≤ l₂)
  (π₀ : prepartition I) :
  l₁.partition_filter I π₀ ≤ l₂.partition_filter I π₀ :=
inf_le_inf_right _ $ prepartition_filter_mono I h

lemma has_basis_prepartition_filter_aux (l : integration_filter) (I : box ι) (c : ℝ≥0) :
  (l.prepartition_filter_aux I c).has_basis
    (λ r : (ι → ℝ) → ℝ, ∀ x ∈ I.Icc, 0 < r x ∧ (l.bRiemann → r x = r I.upper))
    (l.to_set I c) :=
has_basis_binfi_principal'
  (λ r₁ hr₁ r₂ hr₂,
    ⟨λ x, min (r₁ x) (r₂ x), λ x hx, ⟨lt_min (hr₁ x hx).1 (hr₂ x hx).1,
      λ hR, congr_arg2 min ((hr₁ x hx).2 hR) ((hr₂ x hx).2 hR)⟩,
      to_set_mono _ le_rfl le_rfl (λ x hx, min_le_left _ _),
      to_set_mono _ le_rfl le_rfl (λ x hx, min_le_right _ _)⟩)
    ⟨λ _, 1, λ x hx, ⟨zero_lt_one, λ _, rfl⟩⟩

lemma has_basis_partition_filter_aux (l : integration_filter) (I : box ι) (π₀ : prepartition I)
  (c : ℝ≥0) :
  (l.partition_filter_aux I π₀ c).has_basis
    (λ r : (ι → ℝ) → ℝ, ∀ x ∈ I.Icc, 0 < r x ∧ (l.bRiemann → r x = r I.upper))
    (λ r, l.to_set I c r ∩ {π | π.to_prepartition ≤ π₀ ∧ π.Union = π₀.Union}) :=
(l.has_basis_prepartition_filter_aux I c).inf_principal _

lemma nonempty_to_set_inter_le_Union_eq (l : integration_filter) {I : box ι} (π₀ : prepartition I)
  {c : ℝ≥0} (hc : π₀.distortion ≤ c) {r : (ι → ℝ) → ℝ} (hr : ∀ x ∈ I.Icc, 0 < r x) :
  (l.to_set I c r ∩ {π | π.to_prepartition ≤ π₀ ∧ π.Union = π₀.Union}).nonempty :=
begin
  rcases π₀.exists_tagged_le_is_Henstock_is_subordinate_Union_eq hr
    with ⟨π, hle, hH, hr, hd, hU⟩,
  exact ⟨π, ⟨hr, λ _, hH, λ _, hd.trans_le hc⟩, ⟨hle, hU⟩⟩
end

instance partition_filter_aux_ne_bot (l : integration_filter) (I : box ι) (π₀ : prepartition I) :
  (l.partition_filter_aux I π₀ π₀.distortion).ne_bot :=
(l.has_basis_partition_filter_aux I _ _).ne_bot_iff.2 $ λ r hr,
  l.nonempty_to_set_inter_le_Union_eq π₀ le_rfl (λ x hx, (hr x hx).1)

instance prepartition_filter_aux_ne_bot (l : integration_filter) (I : box ι) :
  (l.prepartition_filter_aux I I.distortion).ne_bot :=
by simpa only [prepartition.distortion_top]
  using (l.partition_filter_aux_ne_bot I ⊤).mono inf_le_left

instance partition_filter_ne_bot (l : integration_filter) (I : box ι) (π₀ : prepartition I) :
  (l.partition_filter I π₀).ne_bot :=
(l.partition_filter_aux_ne_bot I π₀).mono $ inf_le_inf_right _ $ le_supr _ _

instance prepartition_filter_ne_bot (l : integration_filter) (I : box ι) :
  (l.prepartition_filter I).ne_bot :=
(l.partition_filter_ne_bot I ⊤).mono inf_le_left

instance : decidable_rel ((≤) : integration_filter → integration_filter → Prop) :=
λ _ _, and.decidable

instance : decidable_eq integration_filter := λ x y, decidable_of_iff _ (ext_iff x y).symm

def Riemann : integration_filter := ⟨tt, tt, ff⟩

def Riemann' : integration_filter := ⟨tt, ff, ff⟩

def McShane : integration_filter := ⟨ff, ff, ff⟩

def Henstock : integration_filter := ⟨ff, tt, ff⟩

end integration_filter

end box_integral
