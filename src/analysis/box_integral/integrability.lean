import analysis.box_integral.basic

open_locale classical nnreal ennreal topological_space big_operators

variables {ι E : Type*} [fintype ι] [normed_group E] [normed_space ℝ E]

open measure_theory metric set finset box_integral

lemma box_integral.has_integral_indicator_const {l : integration_filter} (hl : l.bRiemann = ff)
  {s : set (ι → ℝ)} (hs : measurable_set s) (I : box ι) (y : E)
  (μ : measure (ι → ℝ)) [is_locally_finite_measure μ] :
  @has_integral ι E E _ _ _ _ _ I l (s.indicator (λ _, y)) μ.to_box_additive.to_smul
    ((μ (s ∩ I)).to_real • y) :=
begin
  refine ((l.has_basis_to_filter_Union_top I).tendsto_iff nhds_basis_closed_ball).2 (λ ε ε0, _),
  simp only [exists_prop, l.r_cond_of_bRiemann_eq_ff hl, set.mem_Union, exists_imp_distrib,
    mem_inter_eq, and_imp, mem_set_of_eq],
  rcases exists_pos_mul_lt ε0 (∥y∥) with ⟨δ, δ0, hδ⟩,
  lift δ to ℝ≥0 using δ0.le, rw nnreal.coe_pos at δ0,
  have : μ (s ∩ I.Icc) ≠ ∞,
    from ne_top_of_le_ne_top (I.measure_Icc_lt_top μ).ne (measure_mono $ inter_subset_right _ _),
  rcases (hs.inter I.measurable_set_Icc).exists_is_closed_is_open_lt_add this
    (ennreal.coe_pos.2 δ0) with ⟨K, U, hKc, hUo, hKs, hsU, hμKU⟩,
  have : ∀ x ∈ s ∩ I.Icc, ∃ r > (0 : ℝ), closed_ball x r ⊆ U,
    from λ x hx, nhds_basis_closed_ball.mem_iff.1 (hUo.mem_nhds $ hsU hx),
  choose! rs hrs₀ hrsU,
  have : ∀ x ∈ I.Icc \ s, ∃ r > (0 : ℝ), closed_ball x r ⊆ Kᶜ,
    from λ x hx, nhds_basis_closed_ball.mem_iff.1 (hKc.is_open_compl.mem_nhds $
      λ hx', hx.2 (hKs hx').1),
  choose! rs' hrs'₀ hrs'K,
  set r : (ι → ℝ) → ℝ := s.piecewise rs rs',
  have hr0 : ∀ x ∈ I.Icc, 0 < r x,
  { intros x hx,
    simp only [r, set.piecewise], split_ifs with hxs,
    exacts [hrs₀ _ ⟨hxs, hx⟩, hrs'₀ _ ⟨hx, hxs⟩] },
  refine ⟨λ c, r, λ c, hr0, λ π c hπ hπp, le_trans _ hδ.le⟩, rw mul_comm,
  dsimp [integral_sum],
  simp only [mem_closed_ball, dist_eq_norm, ← indicator_smul_apply, sum_indicator_eq_sum_filter,
    ← sum_smul, ← sub_smul, norm_smul, real.norm_eq_abs],
  refine mul_le_mul_of_nonneg_right _ (norm_nonneg y),
/-  have : @integral_sum ι E E _ _ _ _ _ (s.indicator (λ (_x : ι → ℝ), y))
    μ.to_box_additive.to_smul π = (μ (⋃ (J ∈ π) (h : π.tag J ∈ s), J)).to_real • y,
  { }-/
end

lemma measure_theory.simple_func.has_box_integral (f : simple_func (ι → ℝ) E) (I : box ι)
  (μ : measure (ι → ℝ)) [is_locally_finite_measure μ] :
  @has_integral ι E E _ _ _ _ _ I l (s.indicator (λ _, y)) μ.to_box_additive.to_smul
    (f.integral (μ.restrict I))
