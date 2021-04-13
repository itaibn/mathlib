/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import analysis.normed_space.inner_product
import measure_theory.l2_space

/-! # Temporary file, please remove
-/

noncomputable theory
open topological_space measure_theory measure_theory.Lp filter
open_locale nnreal ennreal topological_space big_operators measure_theory

namespace measure_theory

variables {α β γ E E' F F' G G' H 𝕜 𝕂 : Type*} {p : ℝ≥0∞}
  [is_R_or_C 𝕜] -- 𝕜 for ℝ or ℂ
  [is_R_or_C 𝕂] [measurable_space 𝕂] -- 𝕂 for ℝ or ℂ, together with a measurable_space
  [measurable_space β] -- β for a generic measurable space
  -- E for L2
  [inner_product_space 𝕂 E] [measurable_space E] [borel_space E] [second_countable_topology E]
  -- E' for integrals on E
  [inner_product_space 𝕂 E'] [measurable_space E'] [borel_space E'] [second_countable_topology E']
  [normed_space ℝ E'] [complete_space E'] [is_scalar_tower ℝ 𝕂 E']
  -- F for Lp submodule
  [normed_group F] [normed_space 𝕂 F] [measurable_space F] [borel_space F]
  [second_countable_topology F]
  -- F' for integrals on F
  [normed_group F'] [normed_space 𝕂 F'] [measurable_space F'] [borel_space F']
  [second_countable_topology F'] [normed_space ℝ F'] [complete_space F']
  -- G for Lp add_subgroup
  [normed_group G] [measurable_space G] [borel_space G] [second_countable_topology G]
  -- G' for integrals on G
  [normed_group G'] [measurable_space G'] [borel_space G'] [second_countable_topology G']
  [normed_space ℝ G'] [complete_space G']
  -- H for measurable space and normed group (hypotheses of mem_ℒp)
  [measurable_space H] [normed_group H]

lemma mem_ℒ0_iff_ae_measurable [measurable_space α] {μ : measure α} {f : α → H} :
  mem_ℒp f 0 μ ↔ ae_measurable f μ :=
by { simp_rw mem_ℒp, refine and_iff_left _, simp, }

/-- Indicator of as set as as `simple_func`. -/
def indicator_simple_func [measurable_space α] [has_zero γ] (s : set α) (hs : measurable_set s)
  (c : γ) :
  simple_func α γ :=
simple_func.piecewise s hs (simple_func.const α c) (simple_func.const α 0)

lemma indicator_simple_func_coe [measurable_space α] [has_zero γ] {μ : measure α} {s : set α}
  {hs : measurable_set s} {c : γ} :
  (indicator_simple_func s hs c) =ᵐ[μ] s.indicator (λ (_x : α), c) :=
by simp only [indicator_simple_func, simple_func.coe_const, simple_func.const_zero,
  simple_func.coe_zero, set.piecewise_eq_indicator, simple_func.coe_piecewise]

lemma simple_func.coe_finset_sum_apply {ι} [measurable_space α] [add_comm_group γ]
  (f : ι → simple_func α γ) (s : finset ι) (x : α) :
  (∑ i in s, f i) x = ∑ i in s, f i x :=
begin
  haveI : decidable_eq ι := classical.dec_eq ι,
  refine finset.induction _ _ s,
  { simp, },
  intros j s hjs h_sum,
  rw [finset.sum_insert hjs, simple_func.coe_add, pi.add_apply, h_sum, ← finset.sum_insert hjs],
end

lemma simple_func.coe_finset_sum {ι} [measurable_space α] [add_comm_group γ]
  (f : ι → simple_func α γ) (s : finset ι) :
  ⇑(∑ i in s, f i) = ∑ i in s, f i :=
by { ext1 x, simp_rw finset.sum_apply, exact simple_func.coe_finset_sum_apply f s x, }

lemma L1.simple_func.coe_finset_sum {ι} [measurable_space α] {μ : measure α} (f : ι → (α →₁ₛ[μ] G))
  (s : finset ι) :
  ⇑(∑ i in s, f i) =ᵐ[μ] ∑ i in s, f i :=
begin
  haveI : decidable_eq ι := classical.dec_eq ι,
  refine finset.induction _ _ s,
  { simp only [finset.sum_empty],
    rw [← L1.simple_func.coe_coe, L1.simple_func.coe_zero],
    exact Lp.coe_fn_zero _ _ _, },
  intros j s hjs h_sum,
  rw [finset.sum_insert hjs, ← L1.simple_func.coe_coe, L1.simple_func.coe_add],
  refine (Lp.coe_fn_add _ _).trans _,
  rw [L1.simple_func.coe_coe, L1.simple_func.coe_coe],
  have h : ⇑(f j) + ⇑∑ (x : ι) in s, f x =ᵐ[μ] ⇑(f j) + ∑ (x : ι) in s, ⇑(f x),
  { refine h_sum.mono (λ x hx, _),
    rw [pi.add_apply, pi.add_apply, hx], },
  refine h.trans _,
  rw ← finset.sum_insert hjs,
end

lemma simple_func_eq_sum_indicator [measurable_space α] [add_comm_group γ]
  (f : simple_func α γ) :
  f = ∑ y in f.range,
    indicator_simple_func (f ⁻¹' ({y} : set γ)) (simple_func.measurable_set_fiber f y) y :=
begin
  ext,
  simp [indicator_simple_func],
  rw simple_func.coe_finset_sum_apply,
  simp_rw simple_func.piecewise_apply,
  simp only [simple_func.coe_const, function.const_apply, set.mem_preimage, set.mem_singleton_iff,
    pi.zero_apply, simple_func.coe_zero],
  haveI : decidable_eq γ := classical.dec_eq γ,
  have hfa : f a = ite (f a ∈ f.range) (f a) (0 : γ), by simp [simple_func.mem_range_self],
  have h := (finset.sum_ite_eq f.range (f a) (λ i, i)).symm,
  dsimp only at h,
  rw ← hfa at h,
  convert h,
  ext1,
  congr,
end

lemma simple_func.exists_forall_norm_le [measurable_space α] [has_norm γ] (f : simple_func α γ) :
  ∃ C, ∀ x, ∥f x∥ ≤ C :=
simple_func.exists_forall_le (simple_func.map (λ x, ∥x∥) f)

lemma snorm'_simple_func [normed_group γ] [measurable_space α] {p : ℝ} (f : simple_func α γ)
  (μ : measure α) :
  snorm' f p μ = (∑ y in f.range, (nnnorm y : ℝ≥0∞) ^ p * μ (f ⁻¹' {y})) ^ (1/p) :=
begin
  rw snorm',
  have h_map : (λ a, (nnnorm (f a) : ℝ≥0∞) ^ p)
    = simple_func.map (λ a : γ, (nnnorm a : ℝ≥0∞) ^ p) f,
  { simp, },
  simp_rw h_map,
  rw simple_func.lintegral_eq_lintegral,
  rw simple_func.map_lintegral,
end

lemma snorm_ess_sup_simple_func_lt_top [normed_group γ] [measurable_space α] (f : simple_func α γ)
  (μ : measure α) :
  snorm_ess_sup f μ < ∞ :=
begin
  rw snorm_ess_sup,
  obtain ⟨C, hfC⟩ := simple_func.exists_forall_norm_le f,
  simp_rw ← of_real_norm_eq_coe_nnnorm,
  refine (ess_sup_le_of_ae_le (ennreal.of_real C) (eventually_of_forall (λ x, _))).trans_lt
    ennreal.of_real_lt_top,
  exact ennreal.of_real_le_of_real (hfC x),
end

lemma simple_func.mem_ℒp_top [measurable_space α] (f : simple_func α H) (μ : measure α) :
  mem_ℒp f ∞ μ :=
⟨simple_func.ae_measurable f,
  by { rw snorm_exponent_top, exact snorm_ess_sup_simple_func_lt_top f μ}⟩

lemma simple_func.finite_measure_of_mem_ℒp [measurable_space α] {μ : measure α}
  (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞)
  (f : simple_func α H) (hf : mem_ℒp f p μ) (y : H) (hyf : y ∈ f.range) :
  y = 0 ∨ μ (f ⁻¹' {y}) < ∞ :=
begin
  have hp_pos_real : 0 < p.to_real, from ennreal.to_real_pos_iff.mpr ⟨hp_pos, hp_ne_top⟩,
  have hf_snorm := mem_ℒp.snorm_lt_top hf,
  rw [snorm_eq_snorm' hp_pos.ne.symm hp_ne_top, snorm'_simple_func,
    ← ennreal.lt_rpow_one_div_iff] at hf_snorm,
  swap, { simp [hp_pos_real], },
  rw ennreal.top_rpow_of_pos at hf_snorm,
  swap, { simp [hp_pos_real], },
  rw ennreal.sum_lt_top_iff at hf_snorm,
  specialize hf_snorm y hyf,
  rw ennreal.mul_lt_top_iff at hf_snorm,
  cases hf_snorm,
  { exact or.inr hf_snorm.2, },
  cases hf_snorm,
  { simp only [hp_pos_real, ennreal.rpow_eq_zero_iff, and_true, ennreal.coe_ne_top, or_false,
      nnnorm_eq_zero, ennreal.coe_eq_zero, false_and] at hf_snorm,
    exact or.inl hf_snorm, },
  { simp [hf_snorm], },
end

lemma simple_func.finite_measure_of_integrable [measurable_space α] {μ : measure α}
  (f : simple_func α H) (hf : integrable f μ) (y : H) (hyf : y ∈ f.range) :
  y = 0 ∨ μ (f ⁻¹' {y}) < ∞ :=
begin
  rw ← mem_ℒp_one_iff_integrable at hf,
  exact simple_func.finite_measure_of_mem_ℒp ennreal.zero_lt_one ennreal.coe_ne_top f hf y hyf,
end

lemma simple_func.mem_ℒp_of_integrable [measurable_space α] {μ : measure α} (p : ℝ≥0∞)
  {f : simple_func α H} (hf : integrable f μ) :
  mem_ℒp f p μ :=
begin
  refine ⟨simple_func.ae_measurable f, _⟩,
  by_cases hp0 : p = 0,
  { simp [hp0], },
  rw ← ne.def at hp0,
  by_cases hp_top : p = ∞,
  { simp only [hp_top, snorm_exponent_top],
    exact snorm_ess_sup_simple_func_lt_top f μ, },
  have hp_pos : 0 < p.to_real,
    from ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) hp0.symm, hp_top⟩,
  rw [snorm_eq_snorm' hp0 hp_top, snorm'_simple_func],
  refine ennreal.rpow_lt_top_of_nonneg _ _,
  { simp, },
  refine (ennreal.sum_lt_top (λ y hy, _)).ne,
  have hyμ := simple_func.finite_measure_of_integrable f hf y hy,
  cases hyμ,
  { simp [hyμ, hp_pos], },
  refine ennreal.mul_lt_top (ennreal.rpow_lt_top_of_nonneg ennreal.to_real_nonneg _) hyμ,
  exact ennreal.coe_ne_top,
end

lemma simple_func.mem_ℒp_of_finite_measure_range [measurable_space α] {μ : measure α} (p : ℝ≥0∞)
  {f : simple_func α H} (hf : ∀ y ∈ f.range, y = 0 ∨ μ (f ⁻¹' {y}) < ∞) :
  mem_ℒp f p μ :=
begin
  by_cases hp0 : p = 0,
  { rw [hp0, mem_ℒ0_iff_ae_measurable],
    exact simple_func.ae_measurable f, },
  rw ← ne.def at hp0,
  by_cases hp_top : p = ∞,
  { rw hp_top, exact simple_func.mem_ℒp_top f μ, },
  have hp_pos : 0 < p.to_real,
    from ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) hp0.symm, hp_top⟩,
  refine ⟨simple_func.ae_measurable f, _⟩,
  rw snorm_eq_snorm' hp0 hp_top,
  rw snorm'_simple_func,
  refine ennreal.rpow_lt_top_of_nonneg (by simp) (ne_of_lt _),
  refine ennreal.sum_lt_top_iff.mpr (λ y hy, _),
  cases hf y hy with h h,
  { simp [h, hp_pos], },
  { refine ennreal.mul_lt_top _ h,
    exact ennreal.rpow_lt_top_of_nonneg ennreal.to_real_nonneg ennreal.coe_ne_top, },
end

lemma simple_func.mem_ℒp_iff_integrable [measurable_space α] {μ : measure α} {f : simple_func α H}
  (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) :
  mem_ℒp f p μ ↔ integrable f μ :=
begin
  refine ⟨λ h, _, simple_func.mem_ℒp_of_integrable p⟩,
  rw ← mem_ℒp_one_iff_integrable,
  refine simple_func.mem_ℒp_of_finite_measure_range 1 _,
  exact simple_func.finite_measure_of_mem_ℒp hp_pos hp_ne_top f h,
end

lemma simple_func.mem_ℒp_of_finite_measure [measurable_space α] (p : ℝ≥0∞) (f : simple_func α H)
  (μ : measure α) [finite_measure μ] :
  mem_ℒp f p μ :=
begin
  obtain ⟨C, hfC⟩ := simple_func.exists_forall_norm_le f,
  exact mem_ℒp.of_bound (simple_func.ae_measurable f) C (eventually_of_forall hfC),
end

lemma mem_ℒ2_simple_func_L1 [measurable_space α] {μ : measure α} (f : α →₁ₛ[μ] G) :
  mem_ℒp f 2 μ :=
(mem_ℒp_congr_ae (L1.simple_func.to_simple_func_eq_to_fun f).symm).mpr
  (simple_func.mem_ℒp_of_integrable 2 (L1.simple_func.integrable _))

lemma simple_func.integrable [measurable_space α] {μ : measure α} [finite_measure μ]
  (f : simple_func α H) :
  integrable f μ :=
mem_ℒp_one_iff_integrable.mp (simple_func.mem_ℒp_of_finite_measure 1 f μ)

lemma simple_func.measure_preimage_ne_zero_lt_top [measurable_space α]
  {μ : measure α} (f : simple_func α H) (hf : integrable f μ) {s : finset H} (hs0 : (0 : H) ∉ s) :
  μ (f ⁻¹' s) < ∞ :=
begin
  rw ← simple_func.sum_measure_preimage_singleton,
  refine ennreal.sum_lt_top (λ y hy, _),
  have hf' := simple_func.finite_measure_of_integrable f hf y,
  by_cases hyf : y ∈ f.range,
  { cases hf' hyf with hy0 hyμ,
    { rw hy0 at hy,
      exact absurd hy hs0, },
    { exact hyμ, }, },
  rw ← simple_func.preimage_eq_empty_iff f y at hyf,
  simp [hyf],
end

lemma simple_func.preimage_set [measurable_space α] (f : simple_func α γ) (s : set γ)
  [decidable_pred s] :
  f ⁻¹' s = f ⁻¹' ↑(f.range.filter s) :=
begin
  sorry,
end

lemma simple_func.preimage_map_ne_zero_subset {δ} [measurable_space α] [has_zero δ] [has_zero γ]
  {f : simple_func α γ} (g : γ → δ) (hg : g 0 = 0)
  {s : finset δ} (hs0 : (0 : δ) ∉ s) [decidable_pred (λ z : γ, z ≠ 0)] :
  (f.map g) ⁻¹' s ⊆ f ⁻¹' (finset.filter (λ z, z ≠ (0 : γ)) f.range) :=
begin
  intro x,
  simp_rw [simple_func.map_preimage, set.mem_preimage, finset.mem_coe, finset.mem_filter],
  intro h,
  refine ⟨h.1, λ hf0, _⟩,
  rw [hf0, hg] at h,
  exact hs0 h.2,
end

lemma simple_func.preimage_map_ne_zero_subset' {δ} [measurable_space α] [has_zero δ] [has_zero γ]
  {f : simple_func α γ} (g : γ → δ) (hg : g 0 = 0)
  {s : set δ} (hs0 : (0 : δ) ∉ s) [decidable_pred (λ z : γ, z ≠ 0)] :
  (f.map g) ⁻¹' s ⊆ f ⁻¹' (finset.filter (λ z, z ≠ (0 : γ)) f.range) :=
begin
  haveI : decidable_pred s := classical.dec_pred s,
  have h_range : (f.map g) ⁻¹' s = (f.map g) ⁻¹' ↑((f.map g).range.filter s),
    from simple_func.preimage_set _ s,
  rw h_range,
  refine simple_func.preimage_map_ne_zero_subset g hg _,
  rw finset.mem_filter,
  push_neg,
  intro h,
  exact hs0,
end

lemma simple_func.preimage_map_singleton_ne_zero_subset {δ} [measurable_space α] [has_zero δ]
  [has_zero γ] {f : simple_func α γ} (g : γ → δ) (hg : g 0 = 0)
  {y : δ} (hy0 : y ≠ 0) [decidable_pred (λ z : γ, z ≠ 0)] :
  (f.map g) ⁻¹' {y} ⊆ f ⁻¹' (finset.filter (λ z, z ≠ (0 : γ)) f.range) :=
begin
  haveI : decidable_pred ({y} : set δ) := classical.dec_pred _,
  refine simple_func.preimage_map_ne_zero_subset' g hg (λ h, _),
  rw set.mem_singleton_iff at h,
  exact hy0 h.symm,
end

lemma simple_func.integrable_map [measurable_space α] [normed_group β] {μ : measure α}
  (f : simple_func α H) (hf : integrable f μ) (g : H → β) (hg : g 0 = 0) :
  integrable (f.map g) μ :=
begin
  have hf' := simple_func.finite_measure_of_integrable _ hf,
  refine ⟨(f.map g).ae_measurable, _⟩,
  rw has_finite_integral,
  have h_eq : (λ a, (nnnorm (f.map g a) : ℝ≥0∞)) = (f.map g).map (λ a, (nnnorm a : ℝ≥0∞)),
  { simp_rw simple_func.coe_map, },
  simp_rw h_eq,
  rw simple_func.lintegral_eq_lintegral,
  rw simple_func.lintegral,
  refine ennreal.sum_lt_top (λ z hz, _),
  rw [simple_func.range_map, finset.mem_image] at hz,
  obtain ⟨u, hu, huz⟩ := hz,
  haveI : decidable_eq β := classical.dec_eq β,
  rw [simple_func.range_map, finset.mem_image] at hu,
  obtain ⟨y, hy, hyu⟩ := hu,
  cases hf' y hy with h h,
  { rw [h, hg] at hyu,
    simp only [hyu.symm, nnnorm_zero, ennreal.coe_zero] at huz,
    simp [huz.symm], },
  { by_cases hz0 : z = 0,
    { simp [hz0], },
    nth_rewrite 0 huz.symm,
    refine ennreal.mul_lt_top ennreal.coe_lt_top _,
    have h_ss1 : ((f.map g).map (λ a, (nnnorm a : ℝ≥0∞))) ⁻¹' {z}
      ⊆ (f.map g) ⁻¹' (finset.filter (λ z, z ≠ (0 : β)) (f.map g).range),
    { refine simple_func.preimage_map_ne_zero_subset' _ _ _,
      { simp, },
      { intro h, rw set.mem_singleton_iff at h, exact hz0 h.symm, }, },
    haveI : decidable_pred (λ (z : H), z ≠ 0) := classical.dec_pred _,
    have h_ss2 : (f.map g) ⁻¹' (finset.filter (λ z, z ≠ (0 : β)) (f.map g).range)
      ⊆ f ⁻¹' (finset.filter (λ z, z ≠ (0 : H)) f.range),
    { refine simple_func.preimage_map_ne_zero_subset' g hg _,
      simp, },
    refine (measure_mono (set.subset.trans h_ss1 h_ss2)).trans_lt _,
    refine simple_func.measure_preimage_ne_zero_lt_top f hf _,
    simp, },
end



/-- Indicator of a set as an ` α →ₘ[μ] E`. -/
def indicator_ae [measurable_space α] (μ : measure α) {s : set α} (hs : measurable_set s) (c : H) :
  α →ₘ[μ] H :=
ae_eq_fun.mk (s.indicator (λ x, c)) ((ae_measurable_indicator_iff hs).mp ae_measurable_const)

lemma ae_measurable_indicator_ae [measurable_space α] (μ : measure α) {s : set α}
  (hs : measurable_set s) {c : H} :
  ae_measurable (s.indicator (λ _, c)) μ :=
(ae_measurable_indicator_iff hs).mp ae_measurable_const

lemma indicator_ae_coe [measurable_space α] {μ : measure α} {s : set α} {hs : measurable_set s}
  {c : H} :
  ⇑(indicator_ae μ hs c) =ᵐ[μ] s.indicator (λ _, c) :=
ae_eq_fun.coe_fn_mk (s.indicator (λ _, c)) (ae_measurable_indicator_ae μ hs)

lemma indicator_const_comp {δ} [has_zero γ] [has_zero δ] {s : set α} (c : γ) (f : γ → δ)
  (hf : f 0 = 0) :
  (λ x, f (s.indicator (λ x, c) x)) = s.indicator (λ x, f c) :=
(set.indicator_comp_of_zero hf).symm

lemma snorm_ess_sup_indicator_le [normed_group γ] [measurable_space α] {μ : measure α}
  (s : set α) (f : α → γ) :
  snorm_ess_sup (s.indicator f) μ ≤ snorm_ess_sup f μ :=
begin
  refine ess_sup_mono_ae (eventually_of_forall (λ x, _)),
  rw [ennreal.coe_le_coe, nnnorm_indicator_eq_indicator_nnnorm],
  exact set.indicator_le_self s _ x,
end

lemma snorm_ess_sup_indicator_const_le [normed_group γ] [measurable_space α] {μ : measure α}
  (s : set α) (c : γ) :
  snorm_ess_sup (s.indicator (λ x : α , c)) μ ≤ (nnnorm c : ℝ≥0∞) :=
begin
  refine (snorm_ess_sup_indicator_le s (λ x, c)).trans _,
  by_cases hμ0 : μ = 0,
  { simp [hμ0], },
  rw snorm_ess_sup_const c hμ0,
  exact le_rfl,
end

lemma snorm_ess_sup_indicator_const_eq [normed_group γ] [measurable_space α] {μ : measure α}
  (s : set α) (c : γ) (hμs : 0 < μ s) :
  snorm_ess_sup (s.indicator (λ x : α , c)) μ = (nnnorm c : ℝ≥0∞) :=
begin
  refine le_antisymm (snorm_ess_sup_indicator_const_le s c) _,
  rw snorm_ess_sup,
  by_contra h,
  push_neg at h,
  rw lt_iff_not_ge' at hμs,
  refine hμs (le_of_eq _),
  have hs_ss : s ⊆ {x | (nnnorm c : ℝ≥0∞) ≤ (nnnorm (s.indicator (λ x : α , c) x) : ℝ≥0∞)},
  { intros x hx_mem,
    simp [hx_mem], },
  refine measure_mono_null hs_ss _,
  have h' := ae_iff.mp (ae_lt_of_ess_sup_lt h),
  push_neg at h',
  exact h',
end

lemma snorm_indicator_const [normed_group γ] [measurable_space α] {μ : measure α} {s : set α}
  {c : γ} (hs : measurable_set s) (hp : 0 < p) (hp_top : p ≠ ∞) :
  snorm (s.indicator (λ x, c)) p μ = (nnnorm c) * (μ s) ^ (1 / p.to_real) :=
begin
  have hp_pos : 0 < p.to_real, from ennreal.to_real_pos_iff.mpr ⟨hp, hp_top⟩,
  rw snorm_eq_snorm' hp.ne.symm hp_top,
  rw snorm',
  simp_rw [nnnorm_indicator_eq_indicator_nnnorm, ennreal.coe_indicator],
  have h_indicator_pow : (λ a : α, s.indicator (λ (x : α), (nnnorm c : ℝ≥0∞)) a ^ p.to_real)
    = s.indicator (λ (x : α), ↑(nnnorm c) ^ p.to_real),
  { rw indicator_const_comp (nnnorm c : ℝ≥0∞) (λ x, x ^ p.to_real) _, simp [hp_pos], },
  rw [h_indicator_pow, lintegral_indicator _ hs, set_lintegral_const, ennreal.mul_rpow_of_nonneg],
  swap, { simp [hp_pos.le], },
  rw [← ennreal.rpow_mul, mul_one_div_cancel hp_pos.ne.symm, ennreal.rpow_one],
end

lemma snorm_indicator_const' [normed_group γ] [measurable_space α] {μ : measure α} {s : set α}
  {c : γ} (hs : measurable_set s) (hμs : 0 < μ s) (hp : 0 < p) :
  snorm (s.indicator (λ x, c)) p μ = (nnnorm c) * (μ s) ^ (1 / p.to_real) :=
begin
  by_cases hp_top : p = ∞,
  { simp [hp_top, snorm_ess_sup_indicator_const_eq s c hμs], },
  exact snorm_indicator_const hs hp hp_top,
end

lemma mem_ℒp_indicator_const (p : ℝ≥0∞) [measurable_space α] {μ : measure α} {s : set α}
  (hs : measurable_set s) (hμs : μ s < ∞) (c : H) :
  mem_ℒp (s.indicator (λ x : α , c)) p μ :=
begin
  refine ⟨(ae_measurable_indicator_iff hs).mp ae_measurable_const, _⟩,
  by_cases hp0 : p = 0,
  { simp [hp0], },
  rw ← ne.def at hp0,
  by_cases hp_top : p = ∞,
  { rw [hp_top, snorm_exponent_top],
    exact (snorm_ess_sup_indicator_const_le s c).trans_lt ennreal.coe_lt_top, },
  have hp_pos : 0 < p.to_real,
    from ennreal.to_real_pos_iff.mpr ⟨lt_of_le_of_ne (zero_le _) hp0.symm, hp_top⟩,
  rw snorm_eq_snorm' hp0 hp_top,
  simp_rw snorm',
  refine ennreal.rpow_lt_top_of_nonneg _ _,
  { simp only [hp_pos.le, one_div, inv_nonneg], },
  simp_rw [nnnorm_indicator_eq_indicator_nnnorm, ennreal.coe_indicator],
  have h_indicator_pow : (λ a : α, s.indicator (λ (x : α), (nnnorm c : ℝ≥0∞)) a ^ p.to_real)
    = s.indicator (λ (x : α), ↑(nnnorm c) ^ p.to_real),
  { rw indicator_const_comp (nnnorm c : ℝ≥0∞) (λ x, x ^ p.to_real) _, simp [hp_pos], },
  rw [h_indicator_pow, lintegral_indicator _ hs],
  simp [hp_pos, hμs.ne, not_le.mpr hp_pos, not_lt.mpr hp_pos.le],
end

lemma mem_ℒp_indicator_ae [measurable_space α] {μ : measure α} {s : set α} (hs : measurable_set s)
  (hμs : μ s < ∞) (c : H) :
  mem_ℒp (indicator_ae μ hs c) p μ :=
by { rw mem_ℒp_congr_ae indicator_ae_coe, exact mem_ℒp_indicator_const p hs hμs c }

section indicator_Lp
variables [measurable_space α] {μ : measure α} {s : set α} {hs : measurable_set s} {hμs : μ s < ∞}
  {c : G}

/-- Indicator of a set as an element of `Lp`. -/
def indicator_Lp (p : ℝ≥0∞) (hs : measurable_set s) (hμs : μ s < ∞) (c : G) : Lp G p μ :=
mem_ℒp.to_Lp (indicator_ae μ hs c) (mem_ℒp_indicator_ae hs hμs c)

lemma indicator_Lp_coe : ⇑(indicator_Lp p hs hμs c) =ᵐ[μ] indicator_ae μ hs c :=
mem_ℒp.coe_fn_to_Lp (mem_ℒp_indicator_ae hs hμs c)

lemma indicator_Lp_coe_fn (hs : measurable_set s) (hμs : μ s < ∞) (c : G) :
  ⇑(indicator_Lp p hs hμs c) =ᵐ[μ] s.indicator (λ _, c) :=
indicator_Lp_coe.trans indicator_ae_coe

lemma indicator_Lp_coe_fn_mem : ∀ᵐ (x : α) ∂μ, x ∈ s → (indicator_Lp p hs hμs c x) = c :=
(indicator_Lp_coe_fn hs hμs c).mono (λ x hx hxs, hx.trans (set.indicator_of_mem hxs _))

lemma indicator_Lp_coe_fn_nmem : ∀ᵐ (x : α) ∂μ, x ∉ s → (indicator_Lp p hs hμs c x) = 0 :=
(indicator_Lp_coe_fn hs hμs c).mono (λ x hx hxs, hx.trans (set.indicator_of_not_mem hxs _))

lemma norm_indicator_Lp (hp_pos : 0 < p) (hp_ne_top : p ≠ ∞) :
  ∥indicator_Lp p hs hμs c∥ = ∥c∥ * (μ s).to_real ^ (1 / p.to_real) :=
begin
  rw [norm_def, snorm_congr_ae (indicator_Lp_coe_fn hs hμs c),
    snorm_indicator_const hs hp_pos hp_ne_top, ennreal.to_real_mul, ennreal.to_real_rpow],
  congr,
end

lemma norm_indicator_Lp_top (hμs_pos : 0 < μ s) : ∥indicator_Lp ∞ hs hμs c∥ = ∥c∥ :=
begin
  rw [norm_def, snorm_congr_ae (indicator_Lp_coe_fn hs hμs c),
    snorm_indicator_const' hs hμs_pos ennreal.coe_lt_top],
  simp only [div_zero, ennreal.rpow_zero, mul_one, ennreal.coe_to_real, ennreal.top_to_real,
    coe_nnnorm],
end

lemma norm_indicator_Lp' (hp_pos : 0 < p) (hμs_pos : 0 < μ s) :
  ∥indicator_Lp p hs hμs c∥ = ∥c∥ * (μ s).to_real ^ (1 / p.to_real) :=
begin
  by_cases hp_top : p = ∞,
  { simp only [hp_top, div_zero, mul_one, ennreal.top_to_real, real.rpow_zero],
    rw hp_top,
    exact norm_indicator_Lp_top hμs_pos, },
  { exact norm_indicator_Lp hp_pos hp_top, },
end

end indicator_Lp



section indicator_L1s

variables [measurable_space α] {μ : measure α} {s : set α} {hs : measurable_set s} {hμs : μ s < ∞}
  {c : G}

lemma is_simple_func_indicator_ae (hs : measurable_set s) (hμs : μ s < ∞) (c : G) :
  ∃ (s : simple_func α G), (ae_eq_fun.mk s s.ae_measurable : α →ₘ[μ] G) = indicator_Lp 1 hs hμs c :=
⟨indicator_simple_func s hs c, ae_eq_fun.ext ((ae_eq_fun.coe_fn_mk _ _).trans
    ((indicator_simple_func_coe).trans (indicator_Lp_coe_fn _ _ _).symm))⟩

/-- Indicator of a set as a `L1.simple_func`. -/
def indicator_L1s (hs : measurable_set s) (hμs : μ s < ∞) (c : G) : α →₁ₛ[μ] G :=
⟨indicator_Lp 1 hs hμs c, is_simple_func_indicator_ae hs hμs c⟩

lemma indicator_L1s_coe : (indicator_L1s hs hμs c : α →₁[μ] G) = indicator_Lp 1 hs hμs c := rfl

lemma indicator_L1s_coe_fn : ⇑(indicator_L1s hs hμs c) =ᵐ[μ] s.indicator (λ _, c) :=
by { rw [(L1.simple_func.coe_coe _).symm, indicator_L1s_coe], exact indicator_Lp_coe_fn hs hμs c, }

lemma to_simple_func_indicator_L1s :
  L1.simple_func.to_simple_func (indicator_L1s hs hμs c) =ᵐ[μ] indicator_simple_func s hs c :=
(L1.simple_func.to_simple_func_eq_to_fun _).trans
  (indicator_L1s_coe_fn.trans indicator_simple_func_coe.symm)

lemma indicator_const_eq_smul {α} [add_comm_monoid γ] [semimodule ℝ γ] (s : set α) (c : γ) :
  s.indicator (λ (_x : α), c) = λ (x : α), s.indicator (λ (_x : α), (1 : ℝ)) x • c :=
by { ext1 x, by_cases h_mem : x ∈ s; simp [h_mem], }

lemma indicator_L1s_eq_smul [normed_space ℝ G] (c : G) :
  indicator_L1s hs hμs c =ᵐ[μ] λ x, ((@indicator_L1s α ℝ _ _ _ _ _ μ _ hs hμs 1) x) • c :=
begin
  have h : (λ (x : α), (indicator_L1s hs hμs (1:ℝ)) x • c) =ᵐ[μ] λ x,
    (s.indicator (λ _, (1:ℝ)) x) • c,
  { change (λ x, x • c) ∘ (indicator_L1s hs hμs (1:ℝ))
      =ᵐ[μ] λ (x : α), s.indicator (λ x, (1:ℝ)) x • c,
    exact eventually_eq.fun_comp indicator_L1s_coe_fn (λ x, x • c), },
  refine (indicator_L1s_coe_fn).trans (eventually_eq.trans _ h.symm),
  exact eventually_of_forall (λ x, by rw indicator_const_eq_smul s c),
end

lemma indicator_L1s_coe_ae_le (c : ℝ) : ∀ᵐ x ∂μ, abs (indicator_L1s hs hμs c x) ≤ abs c :=
begin
  refine (@indicator_L1s_coe_fn α ℝ _ _ _ _ _ μ s hs  hμs c).mono (λ x hx, _),
  rw hx,
  by_cases hx_mem : x ∈ s; simp [hx_mem, abs_nonneg c],
end

lemma norm_indicator_L1s : ∥indicator_L1s hs hμs c∥ = ∥c∥ * (μ s).to_real :=
by rw [L1.simple_func.norm_eq, indicator_L1s_coe,
  norm_indicator_Lp ennreal.zero_lt_one ennreal.coe_ne_top, ennreal.one_to_real, div_one,
  real.rpow_one]

end indicator_L1s

lemma ae_all_finset {ι} [measurable_space α] {μ : measure α} (p : ι → α → Prop) (s : finset ι) :
  (∀ᵐ x ∂μ, ∀ i ∈ s, p i x) ↔ ∀ i ∈ s, ∀ᵐ x ∂μ, p i x :=
begin
  refine ⟨λ h i hi, h.mono (λ x hx, hx i hi), _⟩,
  haveI : decidable_eq ι := classical.dec_eq ι,
  refine finset.induction _ _ s,
  { simp only [eventually_true, finset.not_mem_empty, forall_false_left, implies_true_iff], },
  intros i s his hs h_insert,
  have h : ∀ (i : ι), i ∈ s → (∀ᵐ (x : α) ∂μ, p i x),
    from λ j hj, h_insert j (finset.mem_insert_of_mem hj),
  specialize hs h,
  specialize h_insert i (finset.mem_insert_self i s),
  refine h_insert.mp (hs.mono (λ x hx1 hx2, _)),
  intros j hj,
  rw finset.mem_insert at hj,
  cases hj with hji hjs,
  { rwa hji, },
  { exact hx1 j hjs, },
end

lemma eventually_eq.finset_sum {ι} [measurable_space α] [add_comm_group γ]
  {μ : measure α} (f g : ι → α → γ) (s : finset ι) (hf : ∀ i ∈ s, f i =ᵐ[μ] g i) :
  ∑ i in s, f i =ᵐ[μ] ∑ i in s, g i :=
begin
  simp_rw eventually_eq at hf,
  rw ← ae_all_finset _ s at hf,
  refine hf.mono (λ x hx, _),
  rw [finset.sum_apply, finset.sum_apply],
  exact finset.sum_congr rfl hx,
end

lemma L1.simple_func.sum_to_simple_func_coe {ι} [measurable_space α] {μ : measure α}
  (f : ι → α →₁ₛ[μ] G) (s : finset ι) :
  L1.simple_func.to_simple_func (∑ i in s, f i)
    =ᵐ[μ] ∑ i in s, L1.simple_func.to_simple_func (f i) :=
begin
  refine (L1.simple_func.to_simple_func_eq_to_fun _).trans _,
  refine (L1.simple_func.coe_finset_sum _ s).trans _,
  refine eventually_eq.finset_sum _ _ s (λ i his, _),
  exact (L1.simple_func.to_simple_func_eq_to_fun _).symm,
end

lemma L1.simple_func.to_L1_coe_fn [measurable_space α] {μ : measure α} (f : simple_func α G)
  (hf : integrable f μ) :
  L1.simple_func.to_L1 f hf =ᵐ[μ] f :=
by { rw [←L1.simple_func.coe_coe, L1.simple_func.to_L1_eq_to_L1], exact integrable.coe_fn_to_L1 _, }

lemma L1.simple_func_eq_sum_indicator_L1s [measurable_space α] {μ : measure α} [finite_measure μ]
  (f : α →₁ₛ[μ] G) :
  f = ∑ y in (L1.simple_func.to_simple_func f).range,
    indicator_L1s (L1.simple_func.measurable f (measurable_set_singleton y))
    (measure_lt_top μ _) y :=
begin
  rw ← L1.simple_func.to_L1_to_simple_func (∑ y in (L1.simple_func.to_simple_func f).range,
    indicator_L1s (L1.simple_func.measurable f (measurable_set_singleton y))
    (measure_lt_top μ _) y),
  ext1,
  ext1,
  simp only [L1.simple_func.coe_coe, subtype.coe_mk],
  refine eventually_eq.trans _ (integrable.coe_fn_to_L1 _).symm,
  refine eventually_eq.trans _ (L1.simple_func.sum_to_simple_func_coe _ _).symm,
  have h_sum_eq : ∑ y in (L1.simple_func.to_simple_func f).range, (L1.simple_func.to_simple_func
    (indicator_L1s (L1.simple_func.measurable f (measurable_set_singleton y))
    (measure_lt_top μ _) y))
    =ᵐ[μ] ∑ y in (L1.simple_func.to_simple_func f).range, indicator_simple_func _
      (L1.simple_func.measurable f (measurable_set_singleton y)) y,
  { refine eventually_eq.finset_sum _ _ (L1.simple_func.to_simple_func f).range (λ i hi_mem, _),
    exact (to_simple_func_indicator_L1s), },
  refine eventually_eq.trans _ h_sum_eq.symm,
  nth_rewrite 0 ← L1.simple_func.to_L1_to_simple_func f,
  refine (L1.simple_func.to_L1_coe_fn _ _).trans _,
  have h_to_sum := simple_func_eq_sum_indicator (L1.simple_func.to_simple_func f),
  refine eventually_of_forall (λ x, _),
  apply_fun (λ f : simple_func α G, f.to_fun x) at h_to_sum,
  convert h_to_sum,
  rw ← simple_func.coe_finset_sum,
  refl,
end

/-- Composition of a function and a `L1.simple_func`, as a `L1.simple_func`. -/
def L1.simple_func.map [measurable_space α] {μ : measure α} (g : G → F) (f : α →₁ₛ[μ] G)
  (hg : g 0 = 0):
  (α →₁ₛ[μ] F) :=
L1.simple_func.to_L1 ((L1.simple_func.to_simple_func f).map g)
  (simple_func.integrable_map _ (L1.simple_func.integrable _) _ hg)

@[ext] lemma L1.simple_func.ext [measurable_space α] {μ : measure α} {f g : α →₁ₛ[μ] G} :
  ⇑f =ᵐ[μ] g → f = g :=
by { intro h, ext1, ext1, rwa [L1.simple_func.coe_coe, L1.simple_func.coe_coe], }

lemma L1.simple_func.map_coe [measurable_space α] {μ : measure α} (g : G → F) (f : α →₁ₛ[μ] G)
  (hg : g 0 = 0) :
  ⇑(L1.simple_func.map g f hg) =ᵐ[μ] g ∘ f :=
begin
  rw L1.simple_func.map,
  refine (L1.simple_func.to_L1_coe_fn _ _).trans _,
  rw simple_func.coe_map,
  exact eventually_eq.fun_comp (L1.simple_func.to_simple_func_eq_to_fun _) g,
end

lemma L1.simple_func.coe_fn_neg [measurable_space α] {μ : measure α} (f : α →₁ₛ[μ] G) :
  ⇑(-f) =ᵐ[μ] -f :=
begin
  rw [← L1.simple_func.coe_coe, ← L1.simple_func.coe_coe, L1.simple_func.coe_neg],
  exact Lp.coe_fn_neg _,
end




local notation `⟪`x`, `y`⟫` := @inner 𝕂 E _ x y
local notation `⟪`x`, `y`⟫'` := @inner 𝕂 E' _ x y

lemma inner_indicator_Lp [borel_space 𝕂] [measurable_space α] {μ : measure α} (f : Lp E 2 μ)
  {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : E) :
  inner (indicator_Lp 2 hs hμs c) f = ∫ x in s, ⟪c, f x⟫ ∂μ :=
begin
  simp_rw L2.inner_def,
  rw ← integral_add_compl hs (L2.integrable_inner _ f),
  have h_left : ∫ x in s, ⟪(indicator_Lp 2 hs hμs c) x, f x⟫ ∂μ = ∫ x in s, ⟪c, f x⟫ ∂μ,
  { suffices h_ae_eq : ∀ᵐ x ∂μ, x ∈ s → ⟪indicator_Lp 2 hs hμs c x, f x⟫ = ⟪c, f x⟫,
      from set_integral_congr_ae hs h_ae_eq,
    have h_indicator : ∀ᵐ (x : α) ∂μ, x ∈ s → (indicator_Lp 2 hs hμs c x) = c,
      from indicator_Lp_coe_fn_mem,
    refine h_indicator.mono (λ x hx hxs, _),
    congr,
    exact hx hxs, },
  have h_right : ∫ x in sᶜ, ⟪(indicator_Lp 2 hs hμs c) x, f x⟫ ∂μ = 0,
  { suffices h_ae_eq : ∀ᵐ x ∂μ, x ∉ s → ⟪indicator_Lp 2 hs hμs c x, f x⟫ = 0,
    { simp_rw ← set.mem_compl_iff at h_ae_eq,
      suffices h_int_zero : ∫ x in sᶜ, inner (indicator_Lp 2 hs hμs c x) (f x) ∂μ
        = ∫ x in sᶜ, (0 : 𝕂) ∂μ,
      { rw h_int_zero,
        simp, },
      exact set_integral_congr_ae hs.compl h_ae_eq, },
    have h_indicator : ∀ᵐ (x : α) ∂μ, x ∉ s → (indicator_Lp 2 hs hμs c x) = 0,
      from indicator_Lp_coe_fn_nmem,
    refine h_indicator.mono (λ x hx hxs, _),
    rw hx hxs,
    exact inner_zero_left, },
  rw [h_left, h_right, add_zero],
end

lemma integral_inner [borel_space 𝕂] [measurable_space α] {μ : measure α} {f : α → E'}
  (hf : integrable f μ) (c : E') :
  ∫ x, ⟪c, f x⟫' ∂μ = ⟪c, ∫ x, f x ∂μ⟫' :=
((@inner_right 𝕂 E' _ _ c).restrict_scalars ℝ).integral_comp_comm hf

lemma integral_zero_of_forall_integral_inner_zero [borel_space 𝕂] [measurable_space α]
  {μ : measure α} (f : α → E') (hf : integrable f μ) (hf_int : ∀ (c : E'), ∫ x, ⟪c, f x⟫' ∂μ = 0) :
  ∫ x, f x ∂μ = 0 :=
by { specialize hf_int (∫ x, f x ∂μ), rwa [integral_inner hf, inner_self_eq_zero] at hf_int }



end measure_theory
