import analysis.box_integral.basic

open_locale classical nnreal ennreal

variables {ι E : Type*} [fintype ι] [normed_group E] [normed_space ℝ E]

open measure_theory metric set box_integral

lemma box_integral.has_integral_indicator_const {l : integration_filter} (hl : l.bRiemann = ff)
  {s : set (ι → ℝ)} (hs : measurable_set s) (I : box ι) (y : E)
  (μ : measure (ι → ℝ)) [locally_finite_measure μ] :
  @has_integral ι E E _ _ _ _ _ I l (s.indicator (λ _, y)) μ.to_box_additive.to_smul
    ((μ (s ∩ I)).to_real • y) :=
begin
  refine ((l.has_basis_to_filter_Union_top I).tendsto_iff nhds_basis_ball).2 (λ ε ε0, _),
  simp only [exists_prop, l.r_cond_of_bRiemann_eq_ff hl, set.mem_Union, exists_imp_distrib,
    mem_inter_eq, and_imp, mem_set_of_eq],
  rcases exists_pos_mul_lt ε0 (2 * ∥y∥) with ⟨δ, δ0, hδ⟩,
  lift δ to ℝ≥0 using δ0.le, rw nnreal.coe_pos at δ0,
  have : μ (s ∩ I) ≠ ∞,
    from ne_top_of_le_ne_top (I.measure_coe_lt_top μ).ne (measure_mono $ inter_subset_right _ _),
  rcases (hs.inter I.measurable_set_coe).exists_is_closed_is_open_diff_lt this
    (ennreal.coe_pos.2 δ0) with ⟨K, U, hKc, hUo, hKs, hsU, hμKU⟩,
end

lemma measure_theory.simple_func.has_box_integral (f : simple_fun (ι → ℝ) E) (I : box ι)
  (μ : measure (ι → ℝ)) [locally_finite_measure μ] :
  has_integral
