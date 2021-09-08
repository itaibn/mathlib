import analysis.box_integral.basic

open_locale classical nnreal ennreal topological_space big_operators

variables {ι E : Type*} [fintype ι] [normed_group E] [normed_space ℝ E]

open measure_theory metric set finset filter box_integral

namespace box_integral

lemma has_integral_indicator_const (l : integration_filter) (hl : l.bRiemann = ff)
  {s : set (ι → ℝ)} (hs : measurable_set s) (I : box ι) (y : E)
  (μ : measure (ι → ℝ)) [is_locally_finite_measure μ] :
  @has_integral ι E E _ _ _ _ _ I l (s.indicator (λ _, y)) μ.to_box_additive.to_smul
    ((μ (s ∩ I)).to_real • y) :=
begin
  refine has_integral_of_mul (∥y∥) (λ ε ε0, _),
  lift ε to ℝ≥0 using ε0.le, rw nnreal.coe_pos at ε0,
  have A : μ (s ∩ I.Icc) ≠ ∞,
    from ((measure_mono $ set.inter_subset_right _ _).trans_lt (I.measure_Icc_lt_top μ)).ne,
  have B : μ (s ∩ I) ≠ ∞,
    from ((measure_mono $ set.inter_subset_right _ _).trans_lt (I.measure_coe_lt_top μ)).ne,
  rcases (hs.inter I.measurable_set_Icc).exists_is_closed_is_open_lt_add A
    (ennreal.coe_pos.2 ε0) with ⟨K, U, hKc, hUo, hKs, hsU, hμKU⟩,
  replace hμKU : μ (U \ K) ≤ ε,
  { rw [measure_diff (hKs.trans hsU), ennreal.sub_le_iff_le_add'],
    exacts [hμKU.le, hUo.measurable_set, hKc.measurable_set,
      ne_top_of_le_ne_top A (measure_mono hKs)] },
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
  refine ⟨λ c, r, λ c, (l.r_cond_of_bRiemann_eq_ff hl).2 hr0, λ c π hπ hπp, _⟩, rw mul_comm,
  dsimp [integral_sum],
  simp only [mem_closed_ball, dist_eq_norm, ← indicator_smul_apply, sum_indicator_eq_sum_filter,
    ← sum_smul, ← sub_smul, norm_smul, real.norm_eq_abs, ← prepartition.filter_boxes,
    ← prepartition.measure_Union_to_real],
  refine mul_le_mul_of_nonneg_right _ (norm_nonneg y),
  set t := (π.to_prepartition.filter (λ J, π.tag J ∈ s)).Union,
  change abs ((μ t).to_real - (μ (s ∩ I)).to_real) ≤ ε,
  have htU : t ⊆ U ∩ I,
  { simp only [t, prepartition.Union_def, Union_subset_iff, prepartition.mem_filter, and_imp],
    refine λ J hJ hJs x hx, ⟨hrsU _ ⟨hJs, π.tag_mem_Icc J⟩  _, π.le_of_mem' J hJ hx⟩,
    simpa only [r, s.piecewise_eq_of_mem _ _ hJs] using hπ.1 J hJ (box.coe_subset_Icc hx) },
  refine abs_sub_le_iff.2 ⟨_, _⟩,
  { refine (ennreal.le_to_real_sub B).trans (ennreal.to_real_le_coe_of_le_coe _),
    refine (ennreal.sub_le_sub (measure_mono htU) le_rfl).trans (le_measure_diff.trans _),
    refine (measure_mono $ λ x hx, _).trans hμKU,
    exact ⟨hx.1.1, λ hxK, hx.2 ⟨(hKs hxK).1, hx.1.2⟩⟩ },
  { have hμt : μ t ≠ ∞ :=
      ((measure_mono (htU.trans (inter_subset_right _ _))).trans_lt (I.measure_coe_lt_top _)).ne,
    refine (ennreal.le_to_real_sub hμt).trans (ennreal.to_real_le_coe_of_le_coe _),
    refine le_measure_diff.trans ((measure_mono _).trans hμKU),
    rintro x ⟨⟨hxs, hxI⟩, hxt⟩,
    refine ⟨hsU ⟨hxs, box.coe_subset_Icc hxI⟩, λ hxK, hxt _⟩,
    simp only [t, prepartition.Union_def, prepartition.mem_filter, set.mem_Union, exists_prop],
    rcases hπp x hxI with ⟨J, hJπ, hxJ⟩,
    refine ⟨J, ⟨hJπ, _⟩, hxJ⟩,
    contrapose hxK,
    refine hrs'K _ ⟨π.tag_mem_Icc J, hxK⟩ _,
    simpa only [r, s.piecewise_eq_of_not_mem _ _ hxK] using hπ.1 J hJπ (box.coe_subset_Icc hxJ) }
end

lemma has_integral_zero_of_ae_eq_zero {l : integration_filter} {I : box ι} {f : (ι → ℝ) → E}
  {μ : measure (ι → ℝ)} [is_locally_finite_measure μ] (hf : f =ᵐ[μ.restrict I] 0)
  (hl : l.bRiemann = ff) :
  @has_integral ι E E _ _ _ _ _ I l f μ.to_box_additive.to_smul 0 :=
begin
  refine has_integral_iff.2 (λ ε ε0, _),
  lift ε to ℝ≥0 using ε0.lt.le, rw [gt_iff_lt, nnreal.coe_pos] at ε0,
  rcases nnreal.exists_pos_sum_of_encodable ε0 ℕ with ⟨δ, δ0, c, hδc, hcε⟩,
  haveI := fact.mk (I.measure_coe_lt_top μ),
  change μ.restrict I {x | f x ≠ 0} = 0 at hf,
  set N : (ι → ℝ) → ℕ := λ x, ⌈∥f x∥⌉₊,
  have N0 : ∀ {x}, N x = 0 ↔ f x = 0, by { intro x, simp [N] },
  have : ∀ n, ∃ U, is_open U ∧ N ⁻¹' {n} ⊆ U ∧ μ.restrict I U < δ n / n,
  { refine λ n, (N ⁻¹' {n}).exists_is_open_lt_of_lt _ _,
    cases n,
    { simpa [ennreal.div_zero (ennreal.coe_pos.2 (δ0 _)).ne']
        using measure_lt_top (μ.restrict I) _ },
    { refine (measure_mono_null _ hf).le.trans_lt _,
      { exact λ x hxN hxf, n.succ_ne_zero ((eq.symm hxN).trans $ N0.2 hxf) },
      { simp [(δ0 _).ne'] } } },
  choose U hUo hNU hμU,
  have : ∀ x, ∃ r > (0 : ℝ), closed_ball x r ⊆ U (N x),
    from λ x, nhds_basis_closed_ball.mem_iff.1 ((hUo _).mem_nhds (hNU _ rfl)),
  choose r hr0 hrU,
  refine ⟨λ _, r, λ c, (l.r_cond_of_bRiemann_eq_ff hl).2 (λ x _, hr0 x), λ c π hπ hπp, _⟩,
  rw [dist_eq_norm, sub_zero, ← integral_sum_fiberwise (λ J, N (π.tag J))],
  refine le_trans _ (nnreal.coe_lt_coe.2 hcε).le,
  refine (norm_sum_le_of_le _ _).trans
    (sum_le_has_sum _ (λ n _, (δ n).2) (nnreal.has_sum_coe.2 hδc)),
  rintro n -,
  dsimp [integral_sum],
  have : ∀ J ∈ π.filter (λ J, N (π.tag J) = n),
    ∥(μ ↑J).to_real • f (π.tag J)∥ ≤ (μ J).to_real * n,
  { intros J hJ, rw tagged_prepartition.mem_filter at hJ,
    rw [norm_smul, real.norm_eq_abs, abs_of_nonneg ennreal.to_real_nonneg],
    exact mul_le_mul_of_nonneg_left (hJ.2 ▸ le_nat_ceil _) ennreal.to_real_nonneg },
  refine (norm_sum_le_of_le _ this).trans _, clear this,
  rw [← sum_mul, ← prepartition.measure_Union_to_real],
  generalize hm : μ (π.filter (λ J, N (π.tag J) = n)).Union = m,
  have : m < δ n / n,
  { simp only [measure.restrict_apply (hUo _).measurable_set] at hμU,
    refine hm ▸ (measure_mono _).trans_lt (hμU _),
    simp only [set.subset_def, tagged_prepartition.mem_Union, exists_prop,
      tagged_prepartition.mem_filter],
    rintro x ⟨J, ⟨hJ, rfl⟩, hx⟩,
    exact ⟨hrU _ (hπ.1 _ hJ (box.coe_subset_Icc hx)), π.le_of_mem' J hJ hx⟩ },
  lift m to ℝ≥0 using ne_top_of_lt this,
  rw [ennreal.coe_to_real, ← nnreal.coe_nat_cast, ← nnreal.coe_mul, nnreal.coe_le_coe,
    ← ennreal.coe_le_coe, ennreal.coe_mul, ennreal.coe_nat, mul_comm],
  exact (mul_le_mul_left' this.le _).trans ennreal.mul_div_le
end

lemma has_integral.congr_ae {l : integration_filter} {I : box ι} {y : E} {f g : (ι → ℝ) → E}
  {μ : measure (ι → ℝ)} [is_locally_finite_measure μ]
  (hf : @has_integral ι E E _ _ _ _ _ I l f μ.to_box_additive.to_smul y)
  (hfg : f =ᵐ[μ.restrict I] g) (hl : l.bRiemann = ff) :
  @has_integral ι E E _ _ _ _ _ I l g μ.to_box_additive.to_smul y :=
begin
  have : (g - f) =ᵐ[μ.restrict I] 0, from hfg.mono (λ x hx, sub_eq_zero.2 hx.symm),
  simpa using hf.add (has_integral_zero_of_ae_eq_zero this hl)
end

end box_integral

namespace measure_theory

namespace simple_func

lemma has_box_integral (f : simple_func (ι → ℝ) E) (μ : measure (ι → ℝ))
  [is_locally_finite_measure μ] (I : box ι) (l : integration_filter) (hl : l.bRiemann = ff) :
  @has_integral ι E E _ _ _ _ _ I l f μ.to_box_additive.to_smul (f.integral (μ.restrict I)) :=
begin
  induction f using measure_theory.simple_func.induction with y s hs f g hd hfi hgi,
  { simpa [function.const, measure.restrict_apply hs]
      using box_integral.has_integral_indicator_const l hl hs I y μ },
  { letI := borel E, haveI : borel_space E := ⟨rfl⟩, haveI := fact.mk (I.measure_coe_lt_top μ),
    rw integral_add,
    exacts [hfi.add hgi, integrable_iff.2 $ λ _ _, measure_lt_top _ _,
      integrable_iff.2 $ λ _ _, measure_lt_top _ _] }
end

lemma box_integral_eq_integral (f : simple_func (ι → ℝ) E) (μ : measure (ι → ℝ))
  [is_locally_finite_measure μ] (I : box ι) (l : integration_filter) (hl : l.bRiemann = ff) :
  @box_integral.integral ι E E _ _ _ _ _ I l f μ.to_box_additive.to_smul =
    f.integral (μ.restrict I) :=
(f.has_box_integral μ I l hl).integral_eq

end simple_func

open topological_space

lemma integrable_on.has_box_integral [second_countable_topology E] [measurable_space E] [borel_space E]
  [complete_space E] {f : (ι → ℝ) → E} {μ : measure (ι → ℝ)} [is_locally_finite_measure μ]
  {I : box ι} (hf : integrable_on f I μ) (l : integration_filter) (hl : l.bRiemann = ff) :
  @has_integral ι E E _ _ _ _ _ I l f μ.to_box_additive.to_smul (∫ x in I, f x ∂ μ) :=
begin
  rcases hf.ae_measurable with ⟨g, hg, hfg⟩,
  rw integral_congr_ae hfg, have hgi : integrable_on g I μ := (integrable_congr hfg).1 hf,
  refine box_integral.has_integral.congr_ae _ hfg.symm hl,
  clear_dependent f,
  set f : ℕ → simple_func (ι → ℝ) E := simple_func.approx_on g hg univ 0 trivial,
  have hfi : ∀ n, integrable_on (f n) I μ, from simple_func.integrable_approx_on_univ hg hgi,
  have hfi' := λ n, ((f n).has_box_integral μ I l hl).integrable,
  have hfgi : tendsto (λ n, (f n).integral (μ.restrict I)) at_top (𝓝 $ ∫ x in I, g x ∂μ),
    from tendsto_integral_approx_on_univ_of_measurable hg hgi,
  have hfg_mono : ∀ x {m n}, m ≤ n → ∥f n x - g x∥ ≤ ∥f m x - g x∥,
  { intros x m n hmn,
    rw [← dist_eq_norm, ← dist_eq_norm, dist_nndist, dist_nndist, nnreal.coe_le_coe,
      ← ennreal.coe_le_coe, ← edist_nndist, ← edist_nndist],
    exact simple_func.edist_approx_on_mono hg _ x hmn },
  refine has_integral_of_mul ((μ I).to_real + 1 + 1) (λ ε ε0, _),
  lift ε to ℝ≥0 using ε0.le, rw nnreal.coe_pos at ε0, have ε0' := ennreal.coe_pos.2 ε0,
  obtain ⟨N₀, hN₀⟩ : ∃ N : ℕ, ∫ x in I, ∥f N x - g x∥ ∂μ ≤ ε,
  { have : tendsto (λ n, ∫⁻ x in I, ∥f n x - g x∥₊ ∂μ) at_top (𝓝 0),
      from simple_func.tendsto_approx_on_univ_L1_nnnorm hg hgi,
    refine (this.eventually (ge_mem_nhds ε0')).exists.imp (λ N hN, _),
    exact integral_coe_le_of_lintegral_coe_le hN },
  have : ∀ x, ∃ N₁, N₀ ≤ N₁ ∧ dist (f N₁ x) (g x) ≤ ε,
  { intro x,
    have : tendsto (λ n, f n x) at_top (𝓝 $ g x),
      from simple_func.tendsto_approx_on hg _ (subset_closure trivial),
    exact ((eventually_ge_at_top N₀).and $ this $ closed_ball_mem_nhds _ ε0).exists },
  choose Nx hNx hNxε,
  rcases nnreal.exists_pos_sum_of_encodable ε0 ℕ with ⟨δ, δ0, c, hδc, hcε⟩,
  set r : ℝ≥0 → (ι → ℝ) → ℝ := λ c x, (hfi' $ Nx x).convergence_r (δ $ Nx x) c x,
  refine ⟨r, λ c, _, λ c π hπ hπp, _⟩,
  { refine (l.r_cond_of_bRiemann_eq_ff hl).2 (λ x hx, _),
    exact ((hfi' $ Nx x).convergence_r_cond (δ0 _) _).1 x hx },
  refine (dist_triangle4 _ (∑ J in π.boxes, (μ J).to_real • f (Nx $ π.tag J) (π.tag J))
    (∑ J in π.boxes, ∫ x in J, f (Nx $ π.tag J) x ∂μ) _).trans _,
  rw [add_mul, add_mul, one_mul],
  refine add_le_add_three _ _ _,
  { rw [← hπp.Union_eq, π.to_prepartition.measure_Union_to_real, sum_mul, integral_sum],
    refine dist_sum_sum_le_of_le _ (λ J hJ, _), dsimp,
    rw [dist_eq_norm, ← smul_sub, norm_smul, real.norm_eq_abs,
      abs_of_nonneg ennreal.to_real_nonneg],
    refine mul_le_mul_of_nonneg_left _ ennreal.to_real_nonneg,
    rw [← dist_eq_norm'], exact hNxε _ },
  { rw [← π.to_prepartition.sum_fiberwise (λ J, Nx (π.tag J)),
      ← π.to_prepartition.sum_fiberwise (λ J, Nx (π.tag J))],
    refine le_trans _ (nnreal.coe_lt_coe.2 hcε).le,
    refine (dist_sum_sum_le_of_le _ (λ n hn, _)).trans
      (sum_le_has_sum _ (λ n _, (δ n).2) (nnreal.has_sum_coe.2 hδc)),
    have hNxn : ∀ J ∈ π.filter (λ J, Nx (π.tag J) = n), Nx (π.tag J) = n,
      from λ J hJ, (π.mem_filter.1 hJ).2,
    have hrn : ∀ J ∈ π.filter (λ J, Nx (π.tag J) = n),
      r c (π.tag J) = (hfi' n).convergence_r (δ n) c (π.tag J),
    { intros J hJ, have := hNxn J hJ, clear hJ, subst n },
    have : l.mem_base_set I c ((hfi' n).convergence_r (δ n) c) (π.filter (λ J, Nx (π.tag J) = n)),
      from (hπ.filter _).mono' _ le_rfl le_rfl (λ J hJ, (hrn J hJ).le),
    convert (hfi' n).dist_integral_sum_sum_integral_le_of_mem_base_set (δ0 _) this using 2,
    { refine sum_congr rfl (λ J hJ, _),
      simp [hNxn J hJ] },
    { refine sum_congr rfl (λ J hJ, _),
      rw [← simple_func.integral_eq_integral, simple_func.box_integral_eq_integral _ _ _ _ hl,
        hNxn J hJ],
      exact (hfi _).mono_set (prepartition.le_of_mem _ hJ) } },
  { refine le_trans _ hN₀,
    have hfi : ∀ n (J ∈ π), integrable_on (f n) ↑J  μ,
      from λ n J hJ, (hfi n).mono_set (π.le_of_mem' J hJ),
    have hgi : ∀ J ∈ π, integrable_on g ↑J μ, from λ J hJ, hgi.mono_set (π.le_of_mem' J hJ),
    have hfgi : ∀ n (J ∈ π), integrable_on (λ x, ∥f n x - g x∥) J μ,
      from λ n J hJ, ((hfi n J hJ).sub (hgi J hJ)).norm,
    rw [← hπp.Union_eq, prepartition.Union_def',
      integral_finset_bUnion π.boxes (λ J hJ, J.measurable_set_coe) hgi π.pairwise_disjoint,
      integral_finset_bUnion π.boxes (λ J hJ, J.measurable_set_coe) (hfgi _) π.pairwise_disjoint],
    refine dist_sum_sum_le_of_le _ (λ J hJ, _),
    rw [dist_eq_norm, ← integral_sub (hfi _ J hJ) (hgi J hJ)],
    refine norm_integral_le_of_norm_le (hfgi _ J hJ) (eventually_of_forall $ λ x, _),
    exact hfg_mono x (hNx (π.tag J)) }
end

end measure_theory
