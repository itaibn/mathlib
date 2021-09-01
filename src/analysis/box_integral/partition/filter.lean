/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.partition.subbox_induction

open set function filter metric finset
open_locale classical topological_space filter nnreal
noncomputable theory

namespace box_integral

variables {ι : Type*} [fintype ι] {I : box ι}

open tagged_partition box

def Riemann' : filter (tagged_partition I) :=
⨅ r > (0 : ℝ), 𝓟 {π | is_subordinate π (λ _, r)}

def Riemann : filter (tagged_partition I) :=
Riemann' ⊓ 𝓟 {π | is_Henstock π}

def McShane : filter (tagged_partition I) :=
⨅ (r : (ι → ℝ) → ℝ) (hr : ∀ x ∈ I.Icc, r x > 0), 𝓟 {π | is_subordinate π r}

def Henstock : filter (tagged_partition I) :=
McShane ⊓ 𝓟 {π | is_Henstock π}

def Henstock'_aux (c : ℝ≥0) : filter (tagged_partition I) :=
Henstock ⊓ 𝓟 {π | ∀ J ∈ π, distortion J ≤ c}

def Henstock' : filter (tagged_partition I) :=
⨆ c : ℝ≥0, Henstock'_aux c

lemma Henstock'_def : (@Henstock' _ _ I) =
  ⨆ c : ℝ≥0, McShane ⊓ 𝓟 {π | ∀ J ∈ π, π.tag J ∈ J.Icc ∧ distortion J ≤ c} :=
begin
  refine supr_congr id surjective_id (λ c, _),
  simp only [Henstock'_aux, Henstock, inf_assoc, inf_principal, forall_and_distrib, set_of_and,
    is_Henstock, id]
end

lemma has_basis_McShane :
  (@McShane _ _ I).has_basis (λ r : (ι → ℝ) → ℝ, ∀ x ∈ I.Icc, 0 < r x)
    (λ r, {π | π.is_subordinate r}) :=
begin
  refine has_basis_binfi_principal' (λ r hr r' hr', ⟨λ x, min (r x) (r' x), _, _, _⟩)
    ⟨1, λ _ _, zero_lt_one⟩,
  exacts [λ x hx, lt_min (hr x hx) (hr' x hx), λ π hπ, hπ.mono $ λ x hx, min_le_left _ _,
    λ π hπ, hπ.mono $ λ x hx, min_le_right _ _]
end

lemma has_basis_Henstock :
  (@Henstock _ _ I).has_basis (λ r : (ι → ℝ) → ℝ, ∀ x ∈ I.Icc, 0 < r x)
    (λ r, {π | π.is_subordinate r ∧ π.is_Henstock}) :=
has_basis_McShane.inf_principal _

lemma has_basis_Henstock'_aux (c : ℝ≥0) :
  (@Henstock'_aux _ _ I c).has_basis (λ r : (ι → ℝ) → ℝ, ∀ x ∈ I.Icc, 0 < r x)
    (λ r, {π | π.is_subordinate r ∧ π.is_Henstock ∧ ∀ (J ∈ π), (J : _).distortion ≤ c}) :=
by simpa only [Henstock'_aux, ← set_of_and, and.assoc]
  using (@has_basis_Henstock ι _ I).inf_principal {π | ∀ J ∈ π, distortion J ≤ c}

lemma has_basis_Henstock' :
  (@Henstock' _ _ I).has_basis (λ r : ℝ≥0 → (ι → ℝ) → ℝ, ∀ c (x ∈ I.Icc), 0 < r c x)
    (λ r, {π | ∃ c, π.is_subordinate (r c) ∧ π.is_Henstock ∧
      ∀ (J ∈ π), (J : _).distortion ≤ c}) :=
by simpa only [set_of_exists] using has_basis_supr has_basis_Henstock'_aux

lemma has_basis_Henstock'_nat :
  (@Henstock' _ _ I).has_basis
    (λ r : ℕ → (ι → ℝ) → ℝ, (∀ c (x ∈ I.Icc), 0 < r c x) ∧ (∀ {c₁ c₂}, c₁ ≤ c₂ → r c₂ ≤ r c₁))
    (λ r, {π | ∃ c, π.is_subordinate (r c) ∧ π.is_Henstock ∧
      ∀ (J ∈ π), (J : _).distortion ≤ c}) :=
begin
  refine has_basis_Henstock'.to_has_basis (λ r hr, _) (λ r hr, _),
  { refine ⟨λ n x, (finset.range (n + 1)).inf' nonempty_range_succ (λ n, r n x), ⟨_, _⟩, _⟩,
    { exact λ c x hx, (lt_inf'_iff _ _).2 (λ k hk, hr _ _ hx) },
    { intros m n hle x,
      refine le_inf' _ _ (λ k hk, inf'_le _ (range_mono _ hk)),
      exact add_le_add hle le_rfl },
    { rintro π ⟨n, hr, hH, hn⟩,
      exact ⟨n, hr.mono $ λ J hJ, inf'_le _ (finset.mem_range.2 n.lt_succ_self), hH, hn⟩ } },
  { refine ⟨λ c, r ⌈(c : ℝ)⌉₊, λ c x, hr.1 _ _, _⟩,
    rintro π ⟨c, hr, hH, hc⟩,
    refine ⟨_, hr, hH, λ J hJ, (hc J hJ).trans _⟩,
    rw [← nnreal.coe_le_coe, nnreal.coe_nat_cast], exact le_nat_ceil _ }
end

lemma has_basis_Henstock'_antimono :
  (@Henstock' _ _ I).has_basis
    (λ r : ℝ≥0 → (ι → ℝ) → ℝ, (∀ c (x ∈ I.Icc), 0 < r c x) ∧ (∀ {c₁ c₂}, c₁ ≤ c₂ → r c₂ ≤ r c₁))
    (λ r, {π | ∃ c, π.is_subordinate (r c) ∧ π.is_Henstock ∧ ∀ (J ∈ π), (J : _).distortion ≤ c}) :=
has_basis_Henstock'_nat.to_has_basis
  (λ r hr, ⟨λ c, r ⌈(c : ℝ)⌉₊, ⟨λ c x hx, hr.1 _ x hx, λ c₁ c₂ hle, hr.2 $ nat_ceil_mono hle⟩,
    λ π ⟨c, hc⟩, ⟨_, hc.1, hc.2.1, λ J hJ, (hc.2.2 J hJ).trans $
      by { rw [← nnreal.coe_le_coe, nnreal.coe_nat_cast], exact le_nat_ceil _ }⟩⟩)
  (λ r hr, ⟨r ∘ coe, ⟨λ n x hx, hr.1 n x hx, λ m n hle, hr.2 (nat.cast_le.2 hle)⟩,
    λ π ⟨m, hm⟩, ⟨m, hm⟩⟩)

lemma has_basis_Riemann' :
  (@Riemann' _ _ I).has_basis (λ r : ℝ, 0 < r) (λ r, {π | is_subordinate π  (λ _, r)}) :=
has_basis_binfi_principal' (λ r hr r' hr', ⟨min r r', lt_min hr hr',
  λ π hπ, hπ.mono (λ x hx, min_le_left r r'), λ π hπ, hπ.mono (λ x hx, min_le_right r r')⟩)
  ⟨1, zero_lt_one⟩

lemma has_basis_Riemann :
  (@Riemann _ _ I).has_basis (λ r : ℝ, 0 < r)
    (λ r, {π | is_subordinate π  (λ _, r) ∧ π.is_Henstock}) :=
has_basis_Riemann'.inf_principal {π | is_Henstock π}

lemma Henstock_le_McShane : @Henstock _ _ I ≤ McShane := inf_le_left

lemma McShane_le_Riemann' : @McShane _ _ I ≤ Riemann' :=
le_binfi $ λ r hr, binfi_le_of_le (λ _, r) (λ _ _, hr) le_rfl

lemma Henstock_le_Riemann : @Henstock _ _ I ≤ Riemann :=
inf_le_inf_right _ McShane_le_Riemann'

lemma Henstock'_le_Henstock : @Henstock' _ _ I ≤ Henstock :=
supr_le $ λ c, inf_le_left

lemma Riemann_le_Riemann' : @Riemann _ _ I ≤ Riemann' := inf_le_left

lemma Henstock'_aux_ne_bot {c : ℝ≥0} (h : distortion I ≤ c) : (@Henstock'_aux _ _ I c).ne_bot :=
(has_basis_Henstock'_aux c).ne_bot_iff.2 $ λ r hr,
  let ⟨π, hHen, hr, hsub⟩ := exists_is_Henstock_is_subordinate_homothetic I hr in
  ⟨π, hr, hHen, λ J hJ, let ⟨n, hn⟩ := hsub J hJ in (distortion_eq_of_sub_eq_div hn).trans_le h⟩

instance Henstock'_ne_bot : (@Henstock' _ _ I).ne_bot :=
(Henstock'_aux_ne_bot le_rfl).mono $ le_supr _ _

instance Henstock_ne_bot : (@Henstock _ _ I).ne_bot := ne_bot_of_le Henstock'_le_Henstock
instance McShane_ne_bot : (@McShane _ _ I).ne_bot := ne_bot_of_le Henstock_le_McShane
instance Riemann_ne_bot : (@Riemann _ _ I).ne_bot := ne_bot_of_le Henstock_le_Riemann
instance Riemann'_ne_bot : (@Riemann' _ _ I).ne_bot := ne_bot_of_le McShane_le_Riemann'

end box_integral
