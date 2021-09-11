import analysis.box_integral.partition.filter
import analysis.box_integral.partition.measure
import topology.uniform_space.compact_separated

open_locale big_operators classical topological_space nnreal filter uniformity
open set finset function filter metric box_integral.integration_filter

noncomputable theory

namespace box_integral

universes u v w

variables {ι : Type u} {E : Type v} {F : Type w} [normed_group E] [normed_space ℝ E]
  [normed_group F] [normed_space ℝ F] {I J : box ι} {π : tagged_prepartition I}

open tagged_prepartition

def integral_sum (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ (E →L[ℝ] F))
  (π : tagged_prepartition I) : F :=
∑ J in π.boxes, vol J (f (π.tag J))

lemma integral_sum_bUnion_tagged (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ (E →L[ℝ] F))
  (π : prepartition I) (πi : Π J, tagged_prepartition J) :
  integral_sum f vol (π.bUnion_tagged πi) = ∑ J in π.boxes, integral_sum f vol (πi J) :=
begin
  refine (π.sum_bUnion_boxes _ _).trans (sum_congr rfl $ λ J hJ, sum_congr rfl $ λ J' hJ', _),
  rw π.tag_bUnion_tagged hJ hJ'
end

lemma integral_sum_bUnion_partition [fintype ι] (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ (E →L[ℝ] F))
  (π : tagged_prepartition I) (πi : Π J, prepartition J) (hπi : ∀ J ∈ π, (πi J).is_partition) :
  integral_sum f vol (π.bUnion_prepartition πi) = integral_sum f vol π :=
begin
  refine (π.to_prepartition.sum_bUnion_boxes _ _).trans (sum_congr rfl $ λ J hJ, _),
  calc ∑ J' in (πi J).boxes, vol J' (f (π.tag $ π.to_prepartition.bUnion_index πi J'))
      = ∑ J' in (πi J).boxes, vol J' (f (π.tag J)) :
    sum_congr rfl (λ J' hJ', by rw [prepartition.bUnion_index_of_mem _ hJ hJ'])
  ... = vol J (f (π.tag J)) :
    (vol.map ⟨λ g : E →L[ℝ] F, g (f (π.tag J)), rfl, λ _ _, rfl⟩).sum_partition_boxes
      le_top (hπi J hJ)
end

lemma integral_sum_inf_partition [fintype ι] (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ (E →L[ℝ] F))
  (π : tagged_prepartition I) {π' : prepartition I} (h : π'.is_partition) :
  integral_sum f vol (π.inf_prepartition π') = integral_sum f vol π :=
integral_sum_bUnion_partition f vol  π _ $ λ J hJ, h.restrict (prepartition.le_of_mem _ hJ)

lemma integral_sum_fiberwise {α} [fintype ι] (g : box ι → α) (f : (ι → ℝ) → E)
  (vol : ι →ᵇᵃ (E →L[ℝ] F)) (π : tagged_prepartition I) :
  ∑ y in π.boxes.image g, integral_sum f vol (π.filter (λ x, g x = y)) = integral_sum f vol π :=
π.to_prepartition.sum_fiberwise g (λ J, vol J (f $ π.tag J))

lemma integral_sum_sub_partitions [fintype ι] (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ (E →L[ℝ] F))
  {π₁ π₂ : tagged_prepartition I} (h₁ : π₁.is_partition) (h₂ : π₂.is_partition) :
  integral_sum f vol π₁ - integral_sum f vol π₂ =
    ∑ J in (π₁.to_prepartition ⊓ π₂.to_prepartition).boxes,
      (vol J (f $ (π₁.inf_prepartition π₂.to_prepartition).tag J) -
        vol J (f $ (π₂.inf_prepartition π₁.to_prepartition).tag J)) :=
begin
  rw [← integral_sum_inf_partition f vol π₁ h₂,
    ← integral_sum_inf_partition f vol π₂ h₁, integral_sum, integral_sum,
    finset.sum_sub_distrib],
  simp only [inf_prepartition_to_prepartition, inf_comm]
end

@[simp] lemma integral_sum_disj_union (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ (E →L[ℝ] F))
  {π₁ π₂ : tagged_prepartition I} (h : disjoint π₁.Union π₂.Union) :
  integral_sum f vol (π₁.disj_union π₂ h) = integral_sum f vol π₁ + integral_sum f vol π₂ :=
begin
  refine (prepartition.sum_disj_union_boxes h _).trans
    (congr_arg2 (+) (sum_congr rfl $ λ J hJ, _) (sum_congr rfl $ λ J hJ, _)),
  { rw disj_union_tag_of_mem_left _ hJ },
  { rw disj_union_tag_of_mem_right _ hJ }
end

@[simp] lemma integral_sum_add (f g : (ι → ℝ) → E) (vol : ι →ᵇᵃ (E →L[ℝ] F))
  (π : tagged_prepartition I) :
  integral_sum (f + g) vol π = integral_sum f vol π + integral_sum g vol π :=
by simp only [integral_sum, pi.add_apply, (vol _).map_add, finset.sum_add_distrib]

@[simp] lemma integral_sum_neg (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ (E →L[ℝ] F))
  (π : tagged_prepartition I) :
  integral_sum (-f) vol π = -integral_sum f vol π :=
by simp only [integral_sum, pi.neg_apply, (vol _).map_neg, finset.sum_neg_distrib]

@[simp] lemma integral_sum_smul (c : ℝ) (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ (E →L[ℝ] F))
  (π : tagged_prepartition I) :
  integral_sum (c • f) vol π = c • integral_sum f vol π :=
by simp only [integral_sum, finset.smul_sum, pi.smul_apply, continuous_linear_map.map_smul]

variables [fintype ι]

def has_integral (I : box ι) (l : integration_filter) (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ (E →L[ℝ] F))
  (y : F) : Prop :=
tendsto (integral_sum f vol) (l.to_filter_Union I ⊤) (𝓝 y)

def integrable (I : box ι) (l : integration_filter) (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ (E →L[ℝ] F)) :=
∃ y, has_integral I l f vol y

def integral (I : box ι) (l : integration_filter) (f : (ι → ℝ) → E) (vol : ι →ᵇᵃ (E →L[ℝ] F)) :=
if h : integrable I l f vol then h.some else 0

variables {l : integration_filter} {f g : (ι → ℝ) → E} {vol : ι →ᵇᵃ (E →L[ℝ] F)} {y y' : F}

lemma has_integral.tendsto (h : has_integral I l f vol y) :
  tendsto (integral_sum f vol) (l.to_filter_Union I ⊤) (𝓝 y) := h

lemma has_integral_iff : has_integral I l f vol y ↔
  ∀ ε > (0 : ℝ), ∃ δ : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ), (∀ c, l.r_cond (δ c)) ∧
    ∀ c π, l.mem_base_set I c (δ c) π → is_partition π → dist (integral_sum f vol π) y ≤ ε :=
((l.has_basis_to_filter_Union_top I).tendsto_iff nhds_basis_closed_ball).trans $
  by simp [@forall_swap ℝ≥0 (tagged_prepartition I)]

lemma has_integral_of_mul (a : ℝ) (h : ∀ ε : ℝ, 0 < ε →
  ∃ δ : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ), (∀ c, l.r_cond (δ c)) ∧ ∀ c π, l.mem_base_set I c (δ c) π →
    is_partition π → dist (integral_sum f vol π) y ≤ a * ε) :
  has_integral I l f vol y :=
begin
  refine has_integral_iff.2 (λ ε hε, _),
  rcases exists_pos_mul_lt hε a with ⟨ε', hε', ha⟩,
  rcases h ε' hε' with ⟨δ, hδ, H⟩,
  exact ⟨δ, hδ, λ c π hπ hπp, (H c π hπ hπp).trans ha.le⟩
end

lemma integrable_iff_cauchy [complete_space F] :
  integrable I l f vol ↔ cauchy ((l.to_filter_Union I ⊤).map (integral_sum f vol)) :=
cauchy_map_iff_exists_tendsto.symm

lemma integrable_iff_cauchy_basis [complete_space F] :
  integrable I l f vol ↔ ∀ ε > (0 : ℝ), ∃ r : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ), (∀ c, l.r_cond (r c)) ∧
    ∀ c₁ c₂ π₁ π₂, l.mem_base_set I c₁ (r c₁) π₁ → π₁.is_partition → l.mem_base_set I c₂ (r c₂) π₂ →
      π₂.is_partition → dist (integral_sum f vol π₁) (integral_sum f vol π₂) ≤ ε :=
begin
  rw [integrable_iff_cauchy, cauchy_map_iff',
    (l.has_basis_to_filter_Union_top _).prod_self.tendsto_iff uniformity_basis_dist_le],
  refine forall_congr (λ ε, forall_congr $ λ ε0, exists_congr $ λ r, _),
  simp only [exists_prop, prod.forall, set.mem_Union, exists_imp_distrib,
    prod_mk_mem_set_prod_eq, and_imp, mem_inter_eq, mem_set_of_eq],
  exact and_congr iff.rfl ⟨λ H c₁ c₂ π₁ π₂ h₁ hU₁ h₂ hU₂, H π₁ π₂ c₁ h₁ hU₁ c₂ h₂ hU₂,
    λ H π₁ π₂ c₁ h₁ hU₁ c₂ h₂ hU₂, H c₁ c₂ π₁ π₂ h₁ hU₁ h₂ hU₂⟩
end

lemma has_integral.mono {l₁ l₂ : integration_filter} (h : has_integral I l₁ f vol y)
  (hl : l₂ ≤ l₁) : has_integral I l₂ f vol y :=
h.mono_left $ integration_filter.to_filter_Union_mono _ hl _

protected lemma integrable.has_integral (h : integrable I l f vol) :
  has_integral I l f vol (integral I l f vol) :=
by { rw [integral, dif_pos h], exact classical.some_spec h }

lemma integrable.mono {l'} (h : integrable I l f vol) (hle : l' ≤ l) : integrable I l' f vol :=
⟨_, h.has_integral.mono hle⟩

lemma has_integral.unique (h : has_integral I l f vol y) (h' : has_integral I l f vol y') :
  y = y' :=
tendsto_nhds_unique h h'

lemma has_integral.integrable (h : has_integral I l f vol y) : integrable I l f vol := ⟨_, h⟩

lemma has_integral.integral_eq (h : has_integral I l f vol y) :
  integral I l f vol = y :=
h.integrable.has_integral.unique h

lemma has_integral.add (h : has_integral I l f vol y) (h' : has_integral I l g vol y') :
  has_integral I l (f + g) vol (y + y') :=
by simpa only [has_integral, ← integral_sum_add] using h.add h'

lemma integrable.add (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integrable I l (f + g) vol :=
(hf.has_integral.add hg.has_integral).integrable

lemma integral_add (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integral I l (f + g) vol = integral I l f vol + integral I l g vol :=
(hf.has_integral.add hg.has_integral).integral_eq

lemma has_integral.neg (hf : has_integral I l f vol y) : has_integral I l (-f) vol (-y) :=
by simpa only [has_integral, ← integral_sum_neg] using hf.neg

lemma integrable.neg (hf : integrable I l f vol) : integrable I l (-f) vol :=
hf.has_integral.neg.integrable

lemma integrable.of_neg (hf : integrable I l (-f) vol) : integrable I l f vol := neg_neg f ▸ hf.neg

@[simp] lemma integrable_neg : integrable I l (-f) vol ↔ integrable I l f vol :=
⟨λ h, h.of_neg, λ h, h.neg⟩

@[simp] lemma integral_neg : integral I l (-f) vol = -integral I l f vol :=
if h : integrable I l f vol then h.has_integral.neg.integral_eq
else by rw [integral, integral, dif_neg h, dif_neg (mt integrable.of_neg h), neg_zero]

lemma has_integral.sub (h : has_integral I l f vol y) (h' : has_integral I l g vol y') :
  has_integral I l (f - g) vol (y - y') :=
by simpa only [sub_eq_add_neg] using h.add h'.neg

lemma integrable.sub (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integrable I l (f - g) vol :=
(hf.has_integral.sub hg.has_integral).integrable

lemma integral_sub (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integral I l (f - g) vol = integral I l f vol - integral I l g vol :=
(hf.has_integral.sub hg.has_integral).integral_eq

lemma has_integral_zero : has_integral I l (λ _, (0:E)) vol 0 :=
by { dunfold has_integral, convert tendsto_const_nhds, ext π, simp [integral_sum] }

lemma integrable_zero : integrable I l (λ _, (0:E)) vol := ⟨0, has_integral_zero⟩

@[simp] lemma integral_zero : integral I l (λ _, (0:E)) vol = 0 :=
has_integral_zero.integral_eq

lemma has_integral_sum {α : Type*} {s : finset α} {f : α → (ι → ℝ) → E} {g : α → F}
  (h : ∀ i ∈ s, has_integral I l (f i) vol (g i)) :
  has_integral I l (λ x, ∑ i in s, f i x) vol (∑ i in s, g i) :=
begin
  induction s using finset.induction_on with a s ha ihs, { simp [has_integral_zero] },
  simp only [finset.sum_insert ha], rw finset.forall_mem_insert at h,
  exact h.1.add (ihs h.2)
end

lemma has_integral.smul (hf : has_integral I l f vol y) (c : ℝ) :
  has_integral I l (c • f) vol (c • y) :=
by simpa only [has_integral, ← integral_sum_smul]
  using (tendsto_const_nhds : tendsto _ _ (𝓝 c)).smul hf

lemma integrable.smul (hf : integrable I l f vol) (c : ℝ) :
  integrable I l (c • f) vol :=
(hf.has_integral.smul c).integrable

lemma integrable.of_smul {c : ℝ} (hf : integrable I l (c • f) vol) (hc : c ≠ 0) :
  integrable I l f vol :=
by { convert hf.smul c⁻¹, ext x, simp only [pi.smul_apply, inv_smul_smul' hc] }

@[simp] lemma integral_smul (c : ℝ) : integral I l (λ x, c • f x) vol = c • integral I l f vol :=
begin
  rcases eq_or_ne c 0 with rfl | hc, { simp },
  by_cases hf : integrable I l f vol,
  { exact (hf.has_integral.smul c).integral_eq },
  { have : ¬integrable I l (λ x, c • f x) vol, from mt (λ h, h.of_smul hc) hf,
    rw [integral, integral, dif_neg hf, dif_neg this, smul_zero] }
end

variables [fintype ι]

lemma has_integral_const (c : E) : has_integral I l (λ _, c) vol (vol I c) :=
tendsto_const_nhds.congr' $ (l.eventually_is_partition I).mono $ λ π hπ,
  ((vol.map ⟨λ g : E →L[ℝ] F, g c, rfl, λ _ _, rfl⟩).sum_partition_boxes le_top hπ).symm

@[simp] lemma integral_const (c : E) : integral I l (λ _, c) vol = vol I c :=
(has_integral_const c).integral_eq

lemma integrable_const (c : E) : integrable I l (λ _, c) vol :=
⟨_, has_integral_const c⟩

open measure_theory

lemma integral_nonneg {g : (ι → ℝ) → ℝ} (hg : ∀ x ∈ I.Icc, 0 ≤ g x)
  (μ : measure (ι → ℝ)) [is_locally_finite_measure μ] :
  0 ≤ integral I l g μ.to_box_additive.to_smul :=
begin
  by_cases hgi : integrable I l g μ.to_box_additive.to_smul,
  { refine ge_of_tendsto' hgi.has_integral (λ π, sum_nonneg $ λ J hJ, _),
    exact mul_nonneg ennreal.to_real_nonneg (hg _ $ π.tag_mem_Icc _) },
  { rw [integral, dif_neg hgi] }
end

lemma norm_integral_le_of_norm_le {g : (ι → ℝ) → ℝ} (hle : ∀ x ∈ I.Icc, ∥f x∥ ≤ g x)
  (μ : measure (ι → ℝ)) [is_locally_finite_measure μ]
  (hg : integrable I l g μ.to_box_additive.to_smul) :
  ∥(integral I l f μ.to_box_additive.to_smul : E)∥ ≤
    integral I l g μ.to_box_additive.to_smul :=
begin
  by_cases hfi : @integrable ι E E _ _ _ _ _ I l f μ.to_box_additive.to_smul,
  { refine le_of_tendsto_of_tendsto' hfi.has_integral.norm hg.has_integral (λ π, _),
    refine norm_sum_le_of_le _ (λ J hJ, _),
    simp only [box_additive_map.to_smul_apply, norm_smul, smul_eq_mul, real.norm_eq_abs,
      μ.to_box_additive_apply, abs_of_nonneg ennreal.to_real_nonneg],
    exact mul_le_mul_of_nonneg_left (hle _ $ π.tag_mem_Icc _) ennreal.to_real_nonneg },
  { rw [integral, dif_neg hfi, norm_zero],
    exact integral_nonneg (λ x hx, (norm_nonneg _).trans (hle x hx)) μ }
end

lemma norm_integral_le_of_le_const {c : ℝ} (hc : ∀ x ∈ I.Icc, ∥f x∥ ≤ c)
  (μ : measure (ι → ℝ)) [is_locally_finite_measure μ] :
  ∥(integral I l f μ.to_box_additive.to_smul : E)∥ ≤ (μ I).to_real * c :=
by simpa only [integral_const]
  using norm_integral_le_of_norm_le hc μ (integrable_const c)

namespace integrable

def convergence_r (h : integrable I l f vol) (ε : ℝ) : ℝ≥0 → (ι → ℝ) → Ioi (0 : ℝ) :=
if hε : 0 < ε then (has_integral_iff.1 h.has_integral ε hε).some
else λ _ _, ⟨1, mem_Ioi.2 zero_lt_one⟩

variables {c c₁ c₂ : ℝ≥0} {ε ε₁ ε₂ : ℝ} {π₁ π₂ : tagged_prepartition I}

lemma convergence_r_cond (h : integrable I l f vol) {ε : ℝ} (h₀ : 0 < ε) (c : ℝ≥0) :
  l.r_cond (h.convergence_r ε c) :=
begin
  rw [convergence_r, dif_pos h₀],
  exact (has_integral_iff.1 h.has_integral ε h₀).some_spec.1 _
end

lemma dist_integral_sum_integral_le_of_mem_base_set (h : integrable I l f vol) (h₀ : 0 < ε)
  (hπ : l.mem_base_set I c (h.convergence_r ε c) π) (hπp : π.is_partition) :
  dist (integral_sum f vol π) (integral I l f vol) ≤ ε :=
begin
  rw [convergence_r, dif_pos h₀] at hπ,
  exact (has_integral_iff.1 h.has_integral ε h₀).some_spec.2 c _ hπ hπp
end

lemma dist_integral_sum_le_of_mem_base_set (h : integrable I l f vol)
  (hpos₁ : 0 < ε₁) (hpos₂ : 0 < ε₂) (h₁ : l.mem_base_set I c₁ (h.convergence_r ε₁ c₁) π₁)
  (h₂ : l.mem_base_set I c₂ (h.convergence_r ε₂ c₂) π₂) (HU : π₁.Union = π₂.Union) :
  dist (integral_sum f vol π₁) (integral_sum f vol π₂) ≤ ε₁ + ε₂ :=
begin
  rcases h₁.exists_common_compl h₂ HU with ⟨π, hπU, hπc₁, hπc₂⟩,
  set r : (ι → ℝ) → Ioi (0 : ℝ) := λ x, min (h.convergence_r ε₁ c₁ x) (h.convergence_r ε₂ c₂ x),
  have hr : l.r_cond r := (h.convergence_r_cond hpos₁ c₁).min (h.convergence_r_cond hpos₂ c₂),
  set πr := π.to_subordinate r,
  have H₁ : dist (integral_sum f vol (π₁.union_compl_to_subordinate π hπU r))
    (integral I l f vol) ≤ ε₁,
  from  h.dist_integral_sum_integral_le_of_mem_base_set hpos₁
    (h₁.union_compl_to_subordinate (λ _ _, min_le_left _ _) hπU hπc₁)
    (is_partition_union_compl_to_subordinate _ _ _ _),
  rw HU at hπU,
  have H₂ : dist (integral_sum f vol (π₂.union_compl_to_subordinate π hπU r))
    (integral I l f vol) ≤ ε₂,
  from  h.dist_integral_sum_integral_le_of_mem_base_set hpos₂
    (h₂.union_compl_to_subordinate (λ _ _, min_le_right _ _) hπU hπc₂)
    (is_partition_union_compl_to_subordinate _ _ _ _),
  simpa [union_compl_to_subordinate] using (dist_triangle_right _ _ _).trans (add_le_add H₁ H₂)
end

lemma tendsto_integral_sum_to_filter_prod_self_inf_Union_eq_uniformity (h : integrable I l f vol) :
  tendsto
    (λ π : tagged_prepartition I × tagged_prepartition I,
      (integral_sum f vol π.1, integral_sum f vol π.2))
    ((l.to_filter I ×ᶠ l.to_filter I) ⊓ 𝓟 {π | π.1.Union = π.2.Union}) (𝓤 F) :=
begin
  refine (((l.has_basis_to_filter I).prod_self.inf_principal _).tendsto_iff
    uniformity_basis_dist_le).2 (λ ε ε0, _),
  replace ε0 := half_pos ε0,
  use [h.convergence_r (ε / 2), h.convergence_r_cond ε0], rintro ⟨π₁, π₂⟩ ⟨⟨h₁, h₂⟩, hU⟩,
  rw ← add_halves ε,
  exact h.dist_integral_sum_le_of_mem_base_set ε0 ε0 h₁.some_spec h₂.some_spec hU
end

lemma cauchy_map_integral_sum_to_filter_Union (h : integrable I l f vol) (π₀ : prepartition I) :
  cauchy ((l.to_filter_Union I π₀).map (integral_sum f vol)) :=
begin
  refine ⟨infer_instance, _⟩,
  rw [prod_map_map_eq, ← to_filter_inf_Union_eq, ← prod_inf_prod, prod_principal_principal],
  exact h.tendsto_integral_sum_to_filter_prod_self_inf_Union_eq_uniformity.mono_left
    (inf_le_inf_left _ $ principal_mono.2 $ λ π h, h.1.trans h.2.symm)
end

variable [complete_space F]

lemma to_subbox_aux (h : integrable I l f vol) (hJ : J ≤ I) :
  ∃ y : F, has_integral J l f vol y ∧
    tendsto (integral_sum f vol) (l.to_filter_Union I (prepartition.single I J hJ)) (𝓝 y) :=
begin
  refine (cauchy_map_iff_exists_tendsto.1
    (h.cauchy_map_integral_sum_to_filter_Union (prepartition.single I J hJ))).imp (λ y hy, ⟨_, hy⟩),
  convert hy.comp (l.tendsto_embed_box_to_filter_Union_top hJ) -- faster than `exact` here
end

lemma to_subbox (h : integrable I l f vol) (hJ : J ≤ I) : integrable J l f vol :=
(h.to_subbox_aux hJ).imp $ λ y, and.left

lemma tendsto_integral_sum_to_filter_Union_single (h : integrable I l f vol) (hJ : J ≤ I) :
  tendsto (integral_sum f vol) (l.to_filter_Union I (prepartition.single I J hJ))
    (𝓝 $ integral J l f vol) :=
let ⟨y, h₁, h₂⟩ := h.to_subbox_aux hJ in h₁.integral_eq.symm ▸ h₂

lemma dist_integral_sum_sum_integral_le_of_mem_base_set_of_Union_eq (h : integrable I l f vol)
  (h0 : 0 < ε) (hπ : l.mem_base_set I c (h.convergence_r ε c) π) {π₀ : prepartition I}
  (hU : π.Union = π₀.Union) :
  dist (integral_sum f vol π) (∑ J in π₀.boxes, integral J l f vol) ≤ ε :=
begin
  refine le_of_forall_pos_le_add (λ δ δ0, _),
  set δ' : ℝ := δ / (π₀.boxes.card + 1),
  have H0 : 0 < (π₀.boxes.card + 1 : ℝ) := nat.cast_add_one_pos _,
  have δ'0 : 0 < δ' := div_pos δ0 H0,
  set C := max π₀.distortion π₀.compl.distortion,
  suffices : ∀ J ∈ π₀, ∃ πi : tagged_prepartition J, πi.is_partition ∧
    dist (integral_sum f vol πi) (integral J l f vol) ≤ δ' ∧
    l.mem_base_set J C (h.convergence_r δ' C) πi,
  { choose! πi hπip hπiδ' hπiC,
    have : l.mem_base_set I C (h.convergence_r δ' C) (π₀.bUnion_tagged πi),
      from bUnion_tagged_mem_base_set hπiC hπip (λ _, le_max_right _ _),
    have hU' : π.Union = (π₀.bUnion_tagged πi).Union,
      from hU.trans (prepartition.Union_bUnion_partition _ hπip).symm,
    have := h.dist_integral_sum_le_of_mem_base_set h0 δ'0 hπ this hU',
    rw integral_sum_bUnion_tagged at this, 
    calc dist (integral_sum f vol π) (∑ J in π₀.boxes, integral J l f vol)
        ≤ dist (integral_sum f vol π) (∑ J in π₀.boxes, integral_sum f vol (πi J)) +
          dist (∑ J in π₀.boxes, integral_sum f vol (πi J)) (∑ J in π₀.boxes, integral J l f vol) :
      dist_triangle _ _ _
    ... ≤ (ε + δ') + ∑ J in π₀.boxes, δ' : add_le_add this (dist_sum_sum_le_of_le _ hπiδ')
    ... = ε + δ : by { field_simp [H0.ne'], ring } },
  intros J hJ,
  have Hle : J ≤ I := π₀.le_of_mem hJ,
  have HJi : integrable J l f vol := h.to_subbox Hle,
  set r := λ x, min (h.convergence_r δ' C x) (HJi.convergence_r δ' C x),
  have hr : l.r_cond r,
    from (h.convergence_r_cond δ'0 C).min (HJi.convergence_r_cond δ'0 C),
  have hJd : J.distortion ≤ C, from le_trans (finset.le_sup hJ) (le_max_left _ _),
  rcases l.exists_mem_base_set_is_partition J hJd r with ⟨πJ, hC, hp⟩,
  have hC₁ : l.mem_base_set J C (HJi.convergence_r δ' C) πJ,
  { refine hC.mono J le_rfl le_rfl (λ x hx, _), exact min_le_right _ _ },
  have hC₂ : l.mem_base_set J C (h.convergence_r δ' C) πJ,
  { refine hC.mono J le_rfl le_rfl (λ x hx, _), exact min_le_left _ _ },
  exact ⟨πJ, hp, HJi.dist_integral_sum_integral_le_of_mem_base_set δ'0 hC₁ hp, hC₂⟩
end

lemma dist_integral_sum_sum_integral_le_of_mem_base_set (h : integrable I l f vol)
  (h0 : 0 < ε) (hπ : l.mem_base_set I c (h.convergence_r ε c) π) :
  dist (integral_sum f vol π) (∑ J in π.boxes, integral J l f vol) ≤ ε :=
h.dist_integral_sum_sum_integral_le_of_mem_base_set_of_Union_eq h0 hπ rfl

lemma tendsto_integral_sum_sum_integral (h : integrable I l f vol) (π₀ : prepartition I) :
  tendsto (integral_sum f vol) (l.to_filter_Union I π₀) (𝓝 $ ∑ J in π₀.boxes, integral J l f vol) :=
begin
  refine ((l.has_basis_to_filter_Union I π₀).tendsto_iff nhds_basis_closed_ball).2 (λ ε ε0, _),
  refine ⟨h.convergence_r ε, h.convergence_r_cond ε0, _⟩,
  simp only [mem_inter_eq, set.mem_Union, mem_set_of_eq],
  rintro π ⟨c, hc, hU⟩,
  exact h.dist_integral_sum_sum_integral_le_of_mem_base_set_of_Union_eq ε0 hc hU
end

lemma sum_integral_congr (h : integrable I l f vol) {π₁ π₂ : prepartition I}
  (hU : π₁.Union = π₂.Union) :
  ∑ J in π₁.boxes, integral J l f vol = ∑ J in π₂.boxes, integral J l f vol :=
begin
  refine tendsto_nhds_unique (h.tendsto_integral_sum_sum_integral π₁) _,
  rw l.to_filter_Union_congr _ hU,
  exact h.tendsto_integral_sum_sum_integral π₂
end

@[simps] def to_box_additive (h : integrable I l f vol) : ι →ᵇᵃ[I] F :=
{ to_fun := λ J, integral J l f vol,
  sum_partition_boxes' := λ J hJ π hπ,
    begin
      replace hπ := hπ.Union_eq, rw ← prepartition.Union_top at hπ,
      rw [(h.to_subbox (with_top.coe_le_coe.1 hJ)).sum_integral_congr hπ,
        prepartition.top_boxes, sum_singleton]
    end }

end integrable

open measure_theory

variable (l)

lemma integrable_of_continuous_on [fintype ι] [complete_space E] {I : box ι} {f : (ι → ℝ) → E}
  (hc : continuous_on f I.Icc) (μ : measure (ι → ℝ)) [is_locally_finite_measure μ] :
  @integrable ι E E _ _ _ _ _ I l f μ.to_box_additive.to_smul :=
begin
  have huc := (is_compact_pi_Icc I.lower I.upper).uniform_continuous_on_of_continuous hc,
  rw metric.uniform_continuous_on_iff_le at huc,
  refine integrable_iff_cauchy_basis.2 (λ ε ε0, _),
  rcases exists_pos_mul_lt ε0 (μ.to_box_additive I) with ⟨ε', ε0', hε⟩,
  rcases huc ε' ε0' with ⟨δ, δ0 : 0 < δ, Hδ⟩,
  refine ⟨λ _ _, ⟨δ / 2, half_pos δ0⟩, λ _ _ _, rfl, λ c₁ c₂ π₁ π₂ h₁ h₁p h₂ h₂p, _⟩,
  simp only [dist_eq_norm, integral_sum_sub_partitions _ _ h₁p h₂p,
    box_additive_map.to_smul_apply, ← smul_sub],
  have : ∀ J ∈ π₁.to_prepartition ⊓ π₂.to_prepartition,
    ∥μ.to_box_additive J • (f ((π₁.inf_prepartition π₂.to_prepartition).tag J) -
      f ((π₂.inf_prepartition π₁.to_prepartition).tag J))∥ ≤ μ.to_box_additive J * ε',
  { intros J hJ,
    have : 0 ≤ μ.to_box_additive J, from ennreal.to_real_nonneg,
    rw [norm_smul, real.norm_eq_abs, abs_of_nonneg this, ← dist_eq_norm],
    refine mul_le_mul_of_nonneg_left _ this,
    refine Hδ _ _ (tagged_prepartition.tag_mem_Icc _ _) (tagged_prepartition.tag_mem_Icc _ _) _,
    rw [← add_halves δ],
    refine (dist_triangle_left _ _ J.upper).trans (add_le_add (h₁.1 _ _ _) (h₂.1 _ _ _)),
    { exact prepartition.bUnion_index_mem _ hJ },
    { exact box.le_iff_Icc.1 (prepartition.le_bUnion_index _ hJ) J.upper_mem_Icc },
    { rw inf_comm at hJ, exact prepartition.bUnion_index_mem _ hJ, },
    { rw inf_comm at hJ,
      exact box.le_iff_Icc.1 (prepartition.le_bUnion_index _ hJ) J.upper_mem_Icc } },
  refine (norm_sum_le_of_le _ this).trans _,
  rw [← finset.sum_mul, μ.to_box_additive.sum_partition_boxes le_top (h₁p.inf h₂p)],
  exact hε.le
end

variable {l}

lemma has_integral_of_bRiemann_eq_ff_of_forall_is_o [fintype ι] (hl : l.bRiemann = ff)
  (B : ι →ᵇᵃ[I] ℝ) (g : ι →ᵇᵃ[I] F)
  (H : ∀ (c : ℝ≥0) (x ∈ I.Icc) (ε > (0 : ℝ)), ∃ δ > 0, ∀ J ≤ I, J.Icc ⊆ metric.closed_ball x δ →
    (l.bHenstock → x ∈ J.Icc) → (l.bDistortion → J.distortion ≤ c) →
    dist (vol J (f x)) (g J) ≤ ε * B J) :
  has_integral I l f vol (g I) :=
begin
  refine has_integral_of_mul (B I) (λ ε ε0, _),
  simp only [subtype.exists'] at H,
  choose! δ Hδε using H,
  have Hpos : 0 < max (B I) 1, from zero_lt_one.trans_le (le_max_right _ _),
  refine ⟨λ c x, δ c x ε,
    λ c, l.r_cond_of_bRiemann_eq_ff hl,
    λ c π hπδ hπp, _⟩,
  rw [← g.sum_partition_boxes le_rfl hπp],
  have : ∀ J ∈ π, dist (vol J (f $ π.tag J)) (g J) ≤ ε * B J,
  { intros J hJ,
    exact Hδε _ _ (π.tag_mem_Icc _) _ ε0 _ (π.le_of_mem' _ hJ) (hπδ.1 J hJ)
      (λ hH, hπδ.2 hH J hJ) (λ hD, (finset.le_sup hJ).trans (hπδ.3 hD)) },
  refine (dist_sum_sum_le_of_le _ this).trans_eq _,
  rw [← finset.mul_sum, B.sum_partition_boxes le_rfl hπp, mul_comm]
end

/-
This is an incomplete proof of a version of the previous theorem that requires weaker condition
at countably many points. It seems that we should require `l.bHenstock` because otherwise
too many boxes can have the same tag.

lemma has_integral_of_bRiemann_eq_ff_of_forall_is_o' [fintype ι] (hl : l.bRiemann = ff)
  (B : ι →ᵇᵃ[I] ℝ) (hB0 : ∀ J, 0 ≤ B J) (g : ι →ᵇᵃ[I] F) (s : set (ι → ℝ)) (hs : s.countable)
  (H₁ : ∀ (c : ℝ≥0) (x ∈ I.Icc ∩ s) (ε > (0 : ℝ)), ∃ δ > 0, ∀ J ≤ I,
    J.Icc ⊆ metric.closed_ball x δ → (l.bHenstock → x ∈ J.Icc) →
    (l.bDistortion → J.distortion ≤ c) → dist (vol J (f x)) (g J) ≤ ε)
  (H₂ : ∀ (c : ℝ≥0) (x ∈ I.Icc \ s) (ε > (0 : ℝ)), ∃ δ > 0, ∀ J ≤ I,
    J.Icc ⊆ metric.closed_ball x δ → (l.bHenstock → x ∈ J.Icc) →
    (l.bDistortion → J.distortion ≤ c) → dist (vol J (f x)) (g J) ≤ ε * B J) :
  has_integral I l f vol (g I) :=
begin
  refine ((l.has_basis_to_filter_Union_top _).tendsto_iff metric.nhds_basis_closed_ball).2 _,
  intros ε ε0,
  choose! δ₁ δ₁0 Hδ₁ using H₁,
  choose! δ₂ δ₂0 Hδ₂ using H₂,
  rcases hs.exists_pos_forall_sum_le (half_pos ε0) with ⟨εs, hεs0, hεs⟩,
  rcases exists_pos_mul_lt (half_pos ε0) (B I) with ⟨ε', ε'0, hεI⟩,
  set δ := λ c x, if x ∈ s then δ₁ c x (εs x) else (δ₂ c) x ε',
  have δ0 : ∀ c (x ∈ I.Icc), 0 < δ c x,
  { intros c x hx,
    simp only [δ], split_ifs with hxs,
    exacts [δ₁0 c x ⟨hx, hxs⟩ _ (hεs0 _), δ₂0 c x ⟨hx, hxs⟩ _ ε'0] },
  refine ⟨δ, λ c, ⟨δ0 c, λ x hx hR, (bool.ff_ne_tt $ hl.symm.trans hR).elim⟩, _⟩,
  simp only [set.mem_Union, mem_inter_eq, mem_set_of_eq],
  rintro π ⟨c, hπδ, hπp⟩,
  rw [← g.sum_partition_boxes le_rfl hπp, mem_closed_ball, integral_sum,
    ← sum_filter_add_sum_filter_not π.boxes (λ J, π.tag J ∈ s),
    ← sum_filter_add_sum_filter_not π.boxes (λ J, π.tag J ∈ s), ← add_halves ε],
  refine dist_add_add_le_of_le _ _,
  { have : ∀ J ∈ π.boxes.filter (λ J, π.tag J ∈ s), dist (vol J (f $ π.tag J)) (g J) ≤ εs (π.tag J),
    { intros J hJ, rw mem_filter at hJ, cases hJ with hJ hJs,
      refine Hδ₁ c _ ⟨π.tag_mem_Icc _, hJs⟩ _ (hεs0 _) _ (π.le_of_mem' _ hJ) _
        (λ hH, hπδ.2.1 hH J hJ) (λ hD, (finset.le_sup hJ).trans (hπδ.2.2 hD).1),
      convert hπδ.1 J hJ, exact (dif_pos hJs).symm },
    refine (dist_sum_sum_le_of_le _ this).trans _, },
  
  have H₂ : ∀ J ∈ π.boxes.filter (λ J, π.tag J ∉ s), dist (vol J (f $ π.tag J)) (g J) ≤ ε' * B J,
  { intros J hJ, rw mem_filter at hJ, cases hJ with hJ hJs,
    refine Hδ₂ c _ ⟨π.tag_mem_Icc _, hJs⟩ _ ε'0 _ (π.le_of_mem' _ hJ) _ (λ hH, hπδ.2.1 hH J hJ)
      (λ hD, (finset.le_sup hJ).trans (hπδ.2.2 hD).1),
    convert hπδ.1 J hJ, exact (dif_neg hJs).symm },
  refine (dist_add_add_le_of_le (dist_sum_sum_le_of_le _ H₁) (dist_sum_sum_le_of_le _ H₂)).trans _,
  rw [← finset.mul_sum, B.sum_partition_boxes le_rfl hπp, div_mul_eq_mul_div],
  exact mul_le_mul_of_nonneg_left (le_max_left _ _) ε0.le
end
-/

lemma has_integral_bot_of_forall_is_o [fintype ι] (B : ι →ᵇᵃ[I] ℝ) (g : ι →ᵇᵃ[I] F)
  (H : ∀ (c : ℝ≥0) (x ∈ I.Icc) (ε > (0 : ℝ)), ∃ δ > 0, ∀ J ≤ I, J.Icc ⊆ metric.closed_ball x δ →
    x ∈ J.Icc → J.distortion ≤ c → dist (vol J (f x)) (g J) ≤ ε * B J) :
  has_integral I ⊥ f vol (g I) :=
has_integral_of_bRiemann_eq_ff_of_forall_is_o rfl B g $ λ c x hx ε hε,
  (H c x hx ε hε).imp $ λ δ hδ', hδ'.imp $ λ δ0 hδ J hJ hJδ hxJ hJc,
    hδ _ hJ hJδ (hxJ rfl) (hJc rfl)

end box_integral
