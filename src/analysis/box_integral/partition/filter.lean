import analysis.box_integral.partition.subbox_induction

open set function filter emetric
open_locale classical topological_space filter ennreal nnreal
noncomputable theory

namespace box_integral

variables {ι : Type*} [fintype ι] {I : box ι}

namespace box

def distortion (I : box ι) : ℝ≥0 :=
finset.univ.sup $ λ i : ι, nndist (I : _).lower I.upper / nndist (I.lower i) (I.upper i)

lemma distortion_eq_of_sub_eq_div {I J : box ι} {r : ℝ}
  (h : ∀ i, I.upper i - I.lower i = (J.upper i - J.lower i) / r) :
  distortion I = distortion J :=
begin
  simp only [distortion, nndist_pi_def, real.nndist_eq', h, real.nnabs.map_div],
  congr' 1 with i,
  have : 0 < r,
  { by_contra hr,
    have := div_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 $ J.lower_le_upper i) (not_lt.1 hr),
    rw ← h at this,
    exact this.not_lt (sub_pos.2 $ I.lower_lt_upper i) },
  simp only [nnreal.finset_sup_div, div_div_div_cancel_right _ (real.nnabs.map_ne_zero.2 this.ne')]
end

lemma nndist_le_distortion_mul (I : box ι) (i : ι) :
  nndist I.lower I.upper ≤ I.distortion * nndist (I.lower i) (I.upper i) :=
calc nndist I.lower I.upper =
  (nndist I.lower I.upper / nndist (I.lower i) (I.upper i)) *  nndist (I.lower i) (I.upper i) :
  (div_mul_cancel _ $ mt nndist_eq_zero.1 (I.lower_lt_upper i).ne).symm
... ≤ I.distortion * nndist (I.lower i) (I.upper i) :
  mul_le_mul_right' (finset.le_sup $ finset.mem_univ i) _

lemma dist_le_distortion_mul (I : box ι) (i : ι) :
  dist I.lower I.upper ≤ I.distortion * (I.upper i - I.lower i) :=
have A : I.lower i - I.upper i < 0, from sub_neg.2 (I.lower_lt_upper i),
by simpa only [← nnreal.coe_le_coe, ← dist_nndist, nnreal.coe_mul, real.dist_eq,
  abs_of_neg A, neg_sub] using I.nndist_le_distortion_mul i

end box

open marked_partition box

def Riemann : filter (marked_partition I) :=
(⨅ r ≠ (0 : ℝ≥0∞), 𝓟 {π | ∀ J ∈ π, edist (J : _).lower J.upper ≤ r}) ⊓ 𝓟 {π | is_Henstock π}

def McShane : filter (marked_partition I) :=
⨅ (r : (ι → ℝ) → ℝ≥0∞) (hr : ∀ x ∈ I.Icc, r x ≠ 0), 𝓟 {π | is_subordinate π r}

def Henstock : filter (marked_partition I) :=
McShane ⊓ 𝓟 {π | is_Henstock π}

def Henstock' : filter (marked_partition I) :=
⨆ c : ℝ≥0, Henstock ⊓ 𝓟 {π | ∀ J ∈ π, distortion J ≤ c}

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

lemma has_basis_Henstock' :
  (@Henstock' _ _ I).has_basis (λ r : ℝ≥0 → (ι → ℝ) → ℝ≥0∞, ∀ c (x ∈ I.Icc), r c x ≠ 0)
    (λ r, {π | ∃ c, π.is_subordinate (r c) ∧ π.is_Henstock ∧
      ∀ (J ∈ π), (J : _).distortion ≤ c}) :=
begin
  have := λ c : ℝ≥0, (@has_basis_Henstock ι _ I).inf_principal {π | ∀ J ∈ π, distortion J ≤ c},
  simpa only [set_of_exists, and.assoc, ← set_of_and] using has_basis_supr this
end

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

lemma Henstock'_le_Henstock : @Henstock' _ _ I ≤ Henstock :=
supr_le $ λ c, inf_le_left

instance Henstock'_ne_bot : (@Henstock' _ _ I).ne_bot :=
has_basis_Henstock'.ne_bot_iff.2 $ λ r hr,
  let ⟨π, hHen, hr, hsub⟩ := exists_is_Henstock_is_subordinate_homothetic I (hr _) in
  ⟨π, distortion I, hr, hHen, λ J hJ,
    let ⟨n, hn⟩ := hsub J hJ in (distortion_eq_of_sub_eq_div hn).le⟩

instance Henstock_ne_bot : (@Henstock _ _ I).ne_bot := ne_bot_of_le Henstock'_le_Henstock
instance McShane_ne_bot : (@McShane _ _ I).ne_bot := ne_bot_of_le Henstock_le_McShane
instance Riemann_ne_bot : (@Riemann _ _ I).ne_bot := ne_bot_of_le Henstock_le_Riemann

end box_integral
