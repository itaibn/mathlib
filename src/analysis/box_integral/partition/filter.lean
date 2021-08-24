import analysis.box_integral.partition.subbox_induction

open set function filter emetric
open_locale classical topological_space filter ennreal
noncomputable theory

namespace box_integral

variables {ι : Type*} [fintype ι] {I : box ι}

namespace marked_partition

def quasi_homothetic (π : marked_partition I) (c : ℝ) :=
∀ (J ∈ π) (i j : ι), ((J : _).upper i - J.lower i) / (J.upper j - J.lower j) ≤
  c * ((I.upper i - I.lower i) / (I.upper j - I.lower j))

lemma quasi_homothetic.mono {π : marked_partition I} {c₁ c₂ : ℝ} (h : π.quasi_homothetic c₁)
  (hc : c₁ ≤ c₂) : π.quasi_homothetic c₂ :=
λ J hJ i j, (h J hJ i j).trans $ mul_le_mul_of_nonneg_right hc $
  div_nonneg (sub_nonneg.2 $ I.lower_le_upper i) (sub_nonneg.2 $ I.lower_le_upper j)

end marked_partition

open marked_partition

def Riemann : filter (marked_partition I) :=
(⨅ r ≠ (0 : ℝ≥0∞), 𝓟 {π | ∀ J ∈ π, edist (J : _).lower J.upper ≤ r}) ⊓ 𝓟 {π | is_Henstock π}

def McShane : filter (marked_partition I) :=
⨅ (r : (ι → ℝ) → ℝ≥0∞) (hr : ∀ x ∈ I.Icc, r x ≠ 0), 𝓟 {π | is_subordinate π r}

def Henstock : filter (marked_partition I) :=
McShane ⊓ 𝓟 {π | is_Henstock π}

def Henstock_qh : filter (marked_partition I) :=
⨆ c : ℝ, Henstock ⊓ 𝓟 {π | π.quasi_homothetic c}

lemma has_basis_McShane :
  (@McShane _ _ I).has_basis (λ r : (ι → ℝ) → ℝ≥0∞, ∀ x ∈ I.Icc, r x ≠ 0)
    (λ r, {π | π.is_subordinate r}) :=
begin
  refine has_basis_binfi_principal' (λ r hr r' hr', ⟨λ x, min (r x) (r' x), _, _, _⟩)
    ⟨1, λ _ _, ennreal.zero_lt_one.ne'⟩,
  exacts [λ x hx, min_ne_bot.2 ⟨hr x hx, hr' x hx⟩, λ π hπ, hπ.mono $ λ x hx, min_le_left _ _,
    λ π hπ, hπ.mono $ λ x hx, min_le_right _ _]
end

lemma has_basis_Henstock :
  (@Henstock _ _ I).has_basis (λ r : (ι → ℝ) → ℝ≥0∞, ∀ x ∈ I.Icc, r x ≠ 0)
    (λ r, {π | π.is_subordinate r ∧ π.is_Henstock}) :=
has_basis_McShane.inf_principal _

lemma has_basis_Henstock_qh :
  (@Henstock_qh _ _ I).has_basis (λ r : ℝ → (ι → ℝ) → ℝ≥0∞, ∀ c (x ∈ I.Icc), r c x ≠ 0)
    (λ r, {π | ∃ c, π.is_subordinate (r c) ∧ π.is_Henstock ∧ π.quasi_homothetic c}) :=
begin
  have := λ c : ℝ, (@has_basis_Henstock ι _ I).inf_principal {π | π.quasi_homothetic c},
  simpa only [set_of_exists, and.assoc, ← set_of_and] using has_basis_supr this
end

lemma has_basis_Henstock_qh_Ici (b : ℝ) :
  (@Henstock_qh _ _ I).has_basis (λ r : Ici b → (ι → ℝ) → ℝ≥0∞, ∀ c (x ∈ I.Icc), r c x ≠ 0)
    (λ r, {π | ∃ c, π.is_subordinate (r c) ∧ π.is_Henstock ∧ π.quasi_homothetic c}) :=
has_basis_Henstock_qh.to_has_basis (λ r hr, ⟨λ c, r c, λ c, hr c, λ π ⟨c, hc⟩, ⟨c, hc⟩⟩) $
  λ r hr, ⟨λ c, r ⟨max c b, le_max_right c b⟩, λ c x hx, hr _ x hx,
    λ π ⟨c, hc⟩, ⟨⟨max c b, le_max_right c b⟩, hc.1, hc.2.1, hc.2.2.mono (le_max_left c b)⟩⟩

lemma has_basis_Riemann :
  (@Riemann _ _ I).has_basis (λ r : ℝ≥0∞, r ≠ 0)
    (λ r, {π | (∀ J ∈ π, edist (J : _).lower J.upper ≤ r) ∧ π.is_Henstock}) :=
begin
  convert (has_basis_binfi_principal' _ _).inf_principal _,
  exact λ r hr r' hr', ⟨min r r', min_ne_bot.2 ⟨hr, hr'⟩,
    λ π hπ J hJ, (hπ J hJ).trans $ min_le_left _ _,
    λ π hπ J hJ, (hπ J hJ).trans $ min_le_right _ _⟩,
  exact ⟨1, ennreal.zero_lt_one.ne'⟩
end

lemma Henstock_le_McShane : @Henstock _ _ I ≤ McShane := inf_le_left

lemma Henstock_le_Riemann : @Henstock _ _ I ≤ Riemann :=
begin
  refine (inf_le_inf_right _ $ le_binfi $ λ r hr, _),
  refine binfi_le_of_le (λ _, r / 2) (λ _ _, (ennreal.half_pos $ pos_iff_ne_zero.2 hr).ne') _,
  refine (principal_mono.2 $ λ π hπ J hJ, _),
  simpa only [two_mul, ennreal.add_halves] using hπ.edist_le hJ
end

lemma Henstock_qh_le_Henstock : @Henstock_qh _ _ I ≤ Henstock :=
supr_le $ λ c, inf_le_left

instance Henstock_qh_ne_bot : (@Henstock_qh _ _ I).ne_bot :=
has_basis_Henstock_qh.ne_bot_iff.2 $ λ r hr,
  let ⟨π, hHen, hr, hsub⟩ := exists_is_Henstock_is_subordinate_homothetic I (hr 1) in
  ⟨π, 1, hr, hHen, λ J hJ i j, let ⟨n, hn⟩ := hsub J hJ in by field_simp [hn]⟩

instance Henstock_ne_bot : (@Henstock _ _ I).ne_bot := ne_bot_of_le Henstock_qh_le_Henstock
instance McShane_ne_bot : (@McShane _ _ I).ne_bot := ne_bot_of_le Henstock_le_McShane
instance Riemann_ne_bot : (@Riemann _ _ I).ne_bot := ne_bot_of_le Henstock_le_Riemann

end box_integral
