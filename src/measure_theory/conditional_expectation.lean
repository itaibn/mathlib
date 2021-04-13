/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import analysis.normed_space.inner_product
import measure_theory.l2_space
import measure_theory.temp_simple_func

/-! # Conditional expectation

## Implementation notes

When several `measurable_space` structures are introduced, the "default" one is the last one.
For example, when writing `{m m0 : measurable_space α} {μ : measure α}`, `μ` is a measure with
respect to `m0`.

-/

noncomputable theory
open topological_space measure_theory measure_theory.Lp filter
open_locale nnreal ennreal topological_space big_operators measure_theory

/-- Like `ae_measurable`, but the `measurable_space` structures used for the measurability
statement and for the measure are different.

TODO: change the definition of ae_measurable to use ae_measurable' ? -/
def ae_measurable' {α β} [measurable_space β] (m : measurable_space α) {m0 : measurable_space α}
  (f : α → β) (μ : measure α) :
  Prop :=
∃ g : α → β, @measurable α β m _ g ∧ f =ᵐ[μ] g

lemma measurable.ae_measurable' {α β} [measurable_space β] {m m0 : measurable_space α} {f : α → β}
  {μ : measure α} (hf : @measurable α β m _ f) :
  ae_measurable' m f μ :=
⟨f, hf, eventually_eq.rfl⟩

namespace ae_measurable'

variables {α β : Type*} [measurable_space β] {f : α → β}

lemma mono {m2 m m0 : measurable_space α} (hm : m2 ≤ m)
  {μ : measure α} (hf : ae_measurable' m2 f μ) :
  ae_measurable' m f μ :=
by { obtain ⟨g, hg_meas, hfg⟩ := hf, exact ⟨g, measurable.mono hg_meas hm le_rfl, hfg⟩, }

lemma ae_measurable {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} (hf : ae_measurable' m f μ) :
  ae_measurable f μ :=
ae_measurable'.mono hm hf

lemma ae_measurable'_of_ae_measurable'_trim {m m0 m0' : measurable_space α} (hm0 : m0 ≤ m0')
  {μ : measure α} (hf : ae_measurable' m f (μ.trim hm0)) :
  ae_measurable' m f μ :=
by { obtain ⟨g, hg_meas, hfg⟩ := hf, exact ⟨g, hg_meas, ae_eq_of_ae_eq_trim hm0 hfg⟩, }

lemma congr_ae {m m0 : measurable_space α} {μ : measure α}
  {f g : α → β} (hf : ae_measurable' m f μ) (hfg : f =ᵐ[μ] g) :
  ae_measurable' m g μ :=
by { obtain ⟨f', hf'_meas, hff'⟩ := hf, exact ⟨f', hf'_meas, hfg.symm.trans hff'⟩, }

lemma add [has_add β] [has_measurable_add₂ β] {m m0 : measurable_space α}
  {μ : measure α} {f g : α → β} (hf : ae_measurable' m f μ) (hg : ae_measurable' m g μ) :
  ae_measurable' m (f+g) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  rcases hg with ⟨g', h_g'_meas, hgg'⟩,
  refine ⟨f' + g', @measurable.add α m _ _ _ _ f' g' h_f'_meas h_g'_meas, _⟩,
  exact hff'.add hgg',
end

lemma sub [add_group β] [has_measurable_sub₂ β] {m m0 : measurable_space α}
  {μ : measure α} {f g : α → β} (hf : ae_measurable' m f μ) (hg : ae_measurable' m g μ) :
  ae_measurable' m (f - g) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  rcases hg with ⟨g', h_g'_meas, hgg'⟩,
  refine ⟨f' - g', @measurable.sub α m _ _ _ _ f' g' h_f'_meas h_g'_meas, _⟩,
  exact hff'.sub hgg',
end

lemma neg [has_neg β] [has_measurable_neg β] {m m0 : measurable_space α}
  {μ : measure α} {f : α → β} (hf : ae_measurable' m f μ) :
  ae_measurable' m (-f) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  exact ⟨-f', @measurable.neg α m _ _ _ _ f' h_f'_meas, hff'.neg⟩,
end

lemma smul {δ} [has_scalar δ β] [measurable_space δ] [has_measurable_smul δ β]
  {m m0 : measurable_space α} {μ : measure α} (c : δ) {f : α → β} (hf : ae_measurable' m f μ) :
  ae_measurable' m (c • f) μ :=
begin
  rcases hf with ⟨f', h_f'_meas, hff'⟩,
  refine ⟨c • f', @measurable.const_smul α m _ _ _ _ _ _ f' h_f'_meas c, _⟩,
  exact eventually_eq.fun_comp hff' (λ x, c • x),
end

lemma restrict {m m0 : measurable_space α}
  {μ : measure α} (hf : ae_measurable' m f μ) (s : set α) :
  ae_measurable' m f (μ.restrict s) :=
by { obtain ⟨g, hg_meas, hfg⟩ := hf, exact ⟨g, hg_meas, ae_restrict_of_ae hfg⟩, }

end ae_measurable'

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

lemma ae_measurable.restrict [measurable_space α] {f : α → β} {μ : measure α}
  (hf : ae_measurable f μ) (s : set α) :
  ae_measurable f (μ.restrict s) :=
ae_measurable'.restrict hf s

notation α ` →₂[`:25 μ `] ` E := measure_theory.Lp E 2 μ

section L2_integrable

variables [opens_measurable_space 𝕂] [measurable_space α] {μ : measure α}

variables (𝕂 F)
/-- Subspace of L2 containing the integrable functions of L2. -/
def L2_integrable (μ : measure α) :
  submodule 𝕂 (α →₂[μ] F) :=
{ carrier := {f | integrable f μ},
  zero_mem' := (integrable_congr (Lp.coe_fn_zero _ _ _).symm).mp (integrable_zero _ _ _),
  add_mem' := λ f g hf hg, (integrable_congr (Lp.coe_fn_add _ _).symm).mp (hf.add hg),
  smul_mem' := λ c f hf, (integrable_congr (Lp.coe_fn_smul _ _).symm).mp (hf.smul c), }
variables {𝕂 F}

lemma dist_L2_integrable (f g : L2_integrable F 𝕂 μ) :
  dist f g = dist (f : α →₂[μ] F) (g : α →₂[μ] F) :=
rfl

lemma mem_L2_integrable_iff_integrable {f : α →₂[μ] F} :
  f ∈ L2_integrable F 𝕂 μ ↔ integrable f μ :=
by simp_rw [← set_like.mem_coe, ← submodule.mem_carrier, L2_integrable, set.mem_set_of_eq]

lemma L2_integrable.integrable (f : L2_integrable F 𝕂 μ) : integrable f μ :=
mem_L2_integrable_iff_integrable.mp f.mem

end L2_integrable

section Lp_sub

variables (𝕂 F)
/-- Lp subspace of functions `f` verifying `ae_measurable' m f μ`. -/
def Lp_sub [opens_measurable_space 𝕂] (m : measurable_space α) [measurable_space α] (p : ℝ≥0∞)
  (μ : measure α) :
  submodule 𝕂 (Lp F p μ) :=
{ carrier   := {f : (Lp F p μ) | ae_measurable' m f μ} ,
  zero_mem' := ⟨(0 : α → F), @measurable_zero _ α _ m _, Lp.coe_fn_zero _ _ _⟩,
  add_mem'  := λ f g hf hg, (hf.add hg).congr_ae (Lp.coe_fn_add f g).symm,
  smul_mem' := λ c f hf, (hf.smul c).congr_ae (Lp.coe_fn_smul c f).symm, }
variables {𝕂 F}

variables [opens_measurable_space 𝕂]

lemma mem_Lp_sub_iff_ae_measurable' {m m0 : measurable_space α} {μ : measure α} {f : Lp F p μ} :
  f ∈ Lp_sub F 𝕂 m p μ ↔ ae_measurable' m f μ :=
by simp_rw [← set_like.mem_coe, ← submodule.mem_carrier, Lp_sub, set.mem_set_of_eq]

lemma Lp_sub.ae_measurable' {m m0 : measurable_space α} {μ : measure α} (f : Lp_sub E 𝕂 m p μ) :
  ae_measurable' m f μ :=
mem_Lp_sub_iff_ae_measurable'.mp f.mem

lemma mem_Lp_sub_self {m0 : measurable_space α} (μ : measure α) (f : Lp F p μ) :
  f ∈ Lp_sub F 𝕂 m0 p μ :=
mem_Lp_sub_iff_ae_measurable'.mpr (Lp.ae_measurable f)

lemma Lp_sub_coe {m m0 : measurable_space α} {p : ℝ≥0∞} {μ : measure α} {f : Lp_sub F 𝕂 m p μ} :
  ⇑f = (f : Lp F p μ) :=
coe_fn_coe_base f

lemma mem_Lp_sub_indicator_Lp {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} {s : set α} (hs : @measurable_set α m s) {hμs : μ s < ∞} {c : F} :
  indicator_Lp p (hm s hs) hμs c ∈ Lp_sub F 𝕂 m p μ :=
⟨s.indicator (λ x : α, c),
  @measurable.indicator α _ m _ _ s (λ x, c) (@measurable_const _ α _ m _) hs,
  indicator_Lp_coe_fn (hm s hs) hμs c⟩

lemma ae_measurable'_of_tendsto' {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  {ι} [nonempty ι] [semilattice_sup ι] [hp : fact (1 ≤ p)] [complete_space G]
  (f : ι → Lp G p μ) (g : ι → α → G)
  (f_lim : Lp G p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) (hg : ∀ n, @measurable α _ m _ (g n))
  (h_tendsto : filter.at_top.tendsto f (𝓝 f_lim)) :
  ae_measurable' m f_lim μ :=
begin
  have hg_m0 : ∀ n, measurable (g n), from λ n, measurable.mono (hg n) hm le_rfl,
  have h_cauchy_seq := h_tendsto.cauchy_seq,
  have h_cau_g : tendsto (λ (n : ι × ι), snorm (g n.fst - g n.snd) p μ) at_top (𝓝 0),
  { rw cauchy_seq_Lp_iff_cauchy_seq_ℒp at h_cauchy_seq,
    suffices h_snorm_eq : ∀ n : ι × ι, snorm (⇑(f n.fst) - ⇑(f n.snd)) p μ
        = snorm (g n.fst - g n.snd) p μ,
      by { simp_rw h_snorm_eq at h_cauchy_seq, exact h_cauchy_seq, },
    exact λ n, snorm_congr_ae ((hfg n.fst).sub (hfg n.snd)), },
  have h_cau_g_m : tendsto (λ (n : ι × ι), @snorm α _ m _ (g n.fst - g n.snd) p (μ.trim hm))
      at_top (𝓝 0),
    { suffices h_snorm_trim : ∀ n : ι × ι, @snorm α _ m _ (g n.fst - g n.snd) p (μ.trim hm)
        = snorm (g n.fst - g n.snd) p μ,
      { simp_rw h_snorm_trim, exact h_cau_g, },
      refine λ n, snorm_trim _ _,
      exact @measurable.sub α m _ _ _ _ (g n.fst) (g n.snd) (hg n.fst) (hg n.snd), },
  have mem_Lp_g : ∀ n, @mem_ℒp α G m _ _ (g n) p (μ.trim hm),
  { refine λ n, ⟨@measurable.ae_measurable α _ m _ _ _ (hg n), _⟩,
    have h_snorm_fg : @snorm α _ m _ (g n) p (μ.trim hm) = snorm (f n) p μ,
      by { rw snorm_trim hm (hg n), exact snorm_congr_ae (hfg n).symm, },
    rw h_snorm_fg,
    exact Lp.snorm_lt_top (f n), },
  let g_Lp := λ n, @mem_ℒp.to_Lp α G m p _ _ _ _ _ (g n) (mem_Lp_g n),
  have h_g_ae_m := λ n, @mem_ℒp.coe_fn_to_Lp α G m p _ _ _ _ _ _ (mem_Lp_g n),
  have h_cau_seq_g_Lp : cauchy_seq g_Lp,
  { rw cauchy_seq_Lp_iff_cauchy_seq_ℒp,
    suffices h_eq : ∀ n : ι × ι, @snorm α _ m _ ((g_Lp n.fst) - (g_Lp n.snd)) p (μ.trim hm)
        = @snorm α _ m _ (g n.fst - g n.snd) p (μ.trim hm),
      by { simp_rw h_eq, exact h_cau_g_m, },
    exact λ n, @snorm_congr_ae α _ m _ _ _ _ _ ((h_g_ae_m n.fst).sub (h_g_ae_m n.snd)), },
  obtain ⟨g_Lp_lim, g_tendsto⟩ := cauchy_seq_tendsto_of_complete h_cau_seq_g_Lp,
  have h_g_lim_meas_m : @measurable α _ m _ g_Lp_lim,
    from @Lp.measurable α G m p (μ.trim hm) _ _ _ _ g_Lp_lim,
  refine ⟨g_Lp_lim, h_g_lim_meas_m, _⟩,
  have h_g_lim_meas : measurable g_Lp_lim, from measurable.mono h_g_lim_meas_m hm le_rfl,
  rw tendsto_Lp_iff_tendsto_ℒp' at g_tendsto h_tendsto,
  suffices h_snorm_zero : snorm (⇑f_lim - ⇑g_Lp_lim) p μ = 0,
  { rw @snorm_eq_zero_iff α G m0 p μ _ _ _ _ _ (ennreal.zero_lt_one.trans_le hp.elim).ne.symm
      at h_snorm_zero,
    { have h_add_sub : ⇑f_lim - ⇑g_Lp_lim + ⇑g_Lp_lim =ᵐ[μ] 0 + ⇑g_Lp_lim,
        from h_snorm_zero.add eventually_eq.rfl,
      simpa using h_add_sub, },
    { exact (Lp.ae_measurable f_lim).sub h_g_lim_meas.ae_measurable, }, },
  have h_tendsto' : tendsto (λ (n : ι), snorm (g n - ⇑f_lim) p μ) at_top (𝓝 0),
  { suffices h_eq : ∀ (n : ι), snorm (g n - ⇑f_lim) p μ = snorm (⇑(f n) - ⇑f_lim) p μ,
      by { simp_rw h_eq, exact h_tendsto, },
    exact λ n, snorm_congr_ae ((hfg n).symm.sub eventually_eq.rfl), },
  have g_tendsto' : tendsto (λ (n : ι), snorm (g n - ⇑g_Lp_lim) p μ) at_top (𝓝 0),
  { suffices h_eq : ∀ (n : ι), snorm (g n - ⇑g_Lp_lim) p μ
        = @snorm α _ m _ (⇑(g_Lp n) - ⇑g_Lp_lim) p (μ.trim hm),
      by { simp_rw h_eq, exact g_tendsto, },
    intro n,
    have h_eq_g : snorm (g n - ⇑g_Lp_lim) p μ = snorm (⇑(g_Lp n) - ⇑g_Lp_lim) p μ,
      from snorm_congr_ae ((ae_eq_of_ae_eq_trim hm (h_g_ae_m n).symm).sub eventually_eq.rfl),
    rw h_eq_g,
    refine (snorm_trim hm _).symm,
    refine @measurable.sub α m _ _ _ _ (g_Lp n) g_Lp_lim _ h_g_lim_meas_m,
    exact @Lp.measurable α G m p (μ.trim hm) _ _ _ _ (g_Lp n), },
  have sub_tendsto : tendsto (λ (n : ι), snorm (⇑f_lim - ⇑g_Lp_lim) p μ) at_top (𝓝 0),
  { let snorm_add := λ (n : ι), snorm (g n - ⇑f_lim) p μ + snorm (g n - ⇑g_Lp_lim) p μ,
    have h_add_tendsto : tendsto snorm_add at_top (𝓝 0),
      by { rw ← add_zero (0 : ℝ≥0∞), exact tendsto.add h_tendsto' g_tendsto', },
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h_add_tendsto
      (λ n, zero_le _) _,
    have h_add : (λ n, snorm (f_lim - g_Lp_lim) p μ)
        = λ n, snorm (f_lim - g n + (g n - g_Lp_lim)) p μ,
      by { ext1 n, congr, abel, },
    simp_rw h_add,
    refine λ n, (snorm_add_le _ _ hp.elim).trans _,
    { exact ((Lp.measurable f_lim).sub (hg_m0 n)).ae_measurable, },
    { exact ((hg_m0 n).sub h_g_lim_meas).ae_measurable, },
    refine add_le_add_right (le_of_eq _) _,
    rw [← neg_sub, snorm_neg], },
  exact tendsto_nhds_unique tendsto_const_nhds sub_tendsto,
end

lemma ae_measurable'_of_tendsto {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
  {ι} [nonempty ι] [semilattice_sup ι] [hp : fact (1 ≤ p)] [complete_space G]
  (f : ι → Lp G p μ) (hf : ∀ n, ae_measurable' m (f n) μ) (f_lim : Lp G p μ)
  (h_tendsto : filter.at_top.tendsto f (𝓝 f_lim)) :
  ae_measurable' m f_lim μ :=
ae_measurable'_of_tendsto' hm f (λ n, (hf n).some) f_lim (λ n, (hf n).some_spec.2)
  (λ n, (hf n).some_spec.1) h_tendsto

lemma is_seq_closed_ae_measurable' [complete_space G] {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [hp : fact (1 ≤ p)] :
  is_seq_closed {f : Lp G p μ | ae_measurable' m f μ} :=
is_seq_closed_of_def (λ F f F_mem F_tendsto_f, ae_measurable'_of_tendsto hm F F_mem f F_tendsto_f)

lemma is_closed_ae_measurable' [complete_space G] {m m0 : measurable_space α} (hm : m ≤ m0)
  {μ : measure α} [hp : fact (1 ≤ p)] :
  is_closed {f : Lp G p μ | ae_measurable' m f μ} :=
is_seq_closed_iff_is_closed.mp (is_seq_closed_ae_measurable' hm)

instance {m m0 : measurable_space α} [hm : fact (m ≤ m0)] {μ : measure α} [complete_space F]
  [hp : fact (1 ≤ p)] : complete_space (Lp_sub F 𝕂 m p μ) :=
is_closed.complete_space_coe (is_closed_ae_measurable' hm.elim)

end Lp_sub

section is_condexp

/-- `f` is a conditional expectation of `g` with respect to the measurable space structure `m`. -/
def is_condexp (m : measurable_space α) [m0 : measurable_space α] (f g : α → F') (μ : measure α) :
  Prop :=
ae_measurable' m f μ ∧ ∀ s (hs : @measurable_set α m s), ∫ a in s, f a ∂μ = ∫ a in s, g a ∂μ

variables {m₂ m m0 : measurable_space α} {μ : measure α} {f f₁ f₂ g g₁ g₂ : α → F'}

lemma is_condexp.refl (hf : ae_measurable' m f μ) : is_condexp m f f μ := ⟨hf, λ s hs, rfl⟩

lemma is_condexp.trans (hm2 : m₂ ≤ m) (hff₂ : is_condexp m₂ f₂ f μ) (hfg : is_condexp m f g μ)  :
  is_condexp m₂ f₂ g μ :=
⟨hff₂.1, λ s hs, (hff₂.2 s hs).trans (hfg.2 s (hm2 s hs))⟩

lemma is_condexp_congr_ae_left' (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) (hf₁ : is_condexp m f₁ g μ) :
  is_condexp m f₂ g μ :=
begin
  rcases hf₁ with ⟨⟨f, h_meas, h_eq⟩, h_int_eq⟩,
  refine ⟨⟨f, h_meas, hf12.symm.trans h_eq⟩, λ s hs, _⟩,
  rw set_integral_congr_ae (hm s hs) (hf12.mono (λ x hx hxs, hx.symm)),
  exact h_int_eq s hs,
end

lemma is_condexp_congr_ae_left (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) :
  is_condexp m f₁ g μ ↔ is_condexp m f₂ g μ :=
⟨λ h, is_condexp_congr_ae_left' hm hf12 h, λ h, is_condexp_congr_ae_left' hm hf12.symm h⟩

lemma is_condexp_congr_ae_right' (hm : m ≤ m0) (hg12 : g₁ =ᵐ[μ] g₂) (hf₁ : is_condexp m f g₁ μ) :
  is_condexp m f g₂ μ :=
begin
  rcases hf₁ with ⟨h_meas, h_int_eq⟩,
  refine ⟨h_meas, λ s hs, _⟩,
  rw set_integral_congr_ae (hm s hs) (hg12.mono (λ x hx hxs, hx.symm)),
  exact h_int_eq s hs,
end

lemma is_condexp_congr_ae_right (hm : m ≤ m0) (hg12 : g₁ =ᵐ[μ] g₂) :
  is_condexp m f g₁ μ ↔ is_condexp m f g₂ μ :=
⟨λ h, is_condexp_congr_ae_right' hm hg12 h, λ h, is_condexp_congr_ae_right' hm hg12.symm h⟩

lemma is_condexp_congr_ae' (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) (hg12 : g₁ =ᵐ[μ] g₂)
  (hfg₁ : is_condexp m f₁ g₁ μ) :
  is_condexp m f₂ g₂ μ :=
is_condexp_congr_ae_left' hm hf12 (is_condexp_congr_ae_right' hm hg12 hfg₁)

lemma is_condexp_congr_ae (hm : m ≤ m0) (hf12 : f₁ =ᵐ[μ] f₂) (hg12 : g₁ =ᵐ[μ] g₂) :
  is_condexp m f₁ g₁ μ ↔ is_condexp m f₂ g₂ μ :=
⟨λ h, is_condexp_congr_ae' hm hf12 hg12 h, λ h, is_condexp_congr_ae' hm hf12.symm hg12.symm h⟩

lemma is_condexp.neg (hfg : is_condexp m f g μ) :
  is_condexp m (-f) (-g) μ :=
begin
  rcases hfg with ⟨h_meas, h_int_eq⟩,
  refine ⟨h_meas.neg, (λ s hs, _)⟩,
  simp_rw pi.neg_apply,
  rw [integral_neg, integral_neg, h_int_eq s hs],
end

lemma is_condexp.add (hfg₁ : is_condexp m f₁ g₁ μ) (hfg₂ : is_condexp m f₂ g₂ μ)
  (hf₁ : integrable f₁ μ) (hg₁ : integrable g₁ μ) (hf₂ : integrable f₂ μ) (hg₂ : integrable g₂ μ) :
  is_condexp m (f₁ + f₂) (g₁ + g₂) μ :=
begin
  rcases hfg₁ with ⟨h_meas₁, h_int_eq₁⟩,
  rcases hfg₂ with ⟨h_meas₂, h_int_eq₂⟩,
  refine ⟨h_meas₁.add h_meas₂, (λ s hs, _)⟩,
  simp_rw pi.add_apply,
  rw [integral_add hf₁.integrable_on hf₂.integrable_on,
    integral_add hg₁.integrable_on hg₂.integrable_on, h_int_eq₁ s hs, h_int_eq₂ s hs],
end

lemma is_condexp.sub (hfg₁ : is_condexp m f₁ g₁ μ) (hfg₂ : is_condexp m f₂ g₂ μ)
  (hf₁ : integrable f₁ μ) (hg₁ : integrable g₁ μ) (hf₂ : integrable f₂ μ) (hg₂ : integrable g₂ μ) :
  is_condexp m (f₁ - f₂) (g₁ - g₂) μ :=
begin
  rcases hfg₁ with ⟨h_meas₁, h_int_eq₁⟩,
  rcases hfg₂ with ⟨h_meas₂, h_int_eq₂⟩,
  refine ⟨h_meas₁.sub h_meas₂, (λ s hs, _)⟩,
  simp_rw pi.sub_apply,
  rw [integral_sub hf₁.integrable_on hf₂.integrable_on,
    integral_sub hg₁.integrable_on hg₂.integrable_on, h_int_eq₁ s hs, h_int_eq₂ s hs],
end

end is_condexp

section is_condexp_properties

variables {m m0 : measurable_space α} {μ : measure α}

lemma is_condexp.nonneg (hm : m ≤ m0) {f g : α → ℝ} (hf : 0 ≤ᵐ[μ] f) (hgf : is_condexp m g f μ)
  (hg : integrable g μ) :
  0 ≤ᵐ[μ] g :=
begin
  obtain ⟨⟨f', h_meas, hff'⟩, h_int_eq⟩ := hgf,
  have h_int' : integrable f' μ := (integrable_congr hff').mp hg,
  have h_int'_m : @integrable α _ m _ _ f' (μ.trim hm),
    from integrable_trim_of_measurable hm h_meas h_int',
  refine eventually_le.trans (ae_eq_null_of_trim hm _) hff'.symm.le,
  refine @ae_nonneg_of_forall_set_ℝ α m (μ.trim hm) f' h_int'_m (λ s hs, _),
  rw ← set_integral_trim hm f' h_meas h_int' hs,
  specialize h_int_eq s hs,
  rw set_integral_congr_ae (hm s hs) (hff'.mono (λ x hx _, hx)) at h_int_eq,
  rw h_int_eq,
  exact integral_nonneg_of_ae (ae_restrict_of_ae hf),
end

lemma is_condexp.nonpos (hm : m ≤ m0) {f g : α → ℝ} (hf : f ≤ᵐ[μ] 0) (hgf : is_condexp m g f μ)
  (hg : integrable g μ) :
  g ≤ᵐ[μ] 0 :=
begin
  have hf_neg : 0 ≤ᵐ[μ] (-f),
  { refine (hf.mono (λ x hx, _)),
    rw [pi.zero_apply, ← neg_zero] at hx,
    rwa [pi.neg_apply, pi.zero_apply, le_neg], },
  have h_neg := is_condexp.nonneg hm hf_neg (is_condexp.neg hgf) hg.neg,
  refine h_neg.mono (λ x hx, _),
  rw [pi.neg_apply, pi.zero_apply, ← neg_zero] at hx,
  exact le_of_neg_le_neg hx,
end

lemma is_condexp.mono (hm : m ≤ m0) {f g fc gc : α → ℝ} (hfg : f ≤ᵐ[μ] g)
  (hf : is_condexp m fc f μ) (hfc_int : integrable fc μ) (hf_int : integrable f μ)
  (hg : is_condexp m gc g μ) (hgc_int : integrable gc μ) (hg_int : integrable g μ) :
  fc ≤ᵐ[μ] gc :=
begin
  suffices h_sub : (fc-gc) ≤ᵐ[μ] 0,
    from (h_sub.mono (λ x hx, by rwa [pi.sub_apply, pi.zero_apply, sub_nonpos] at hx)),
  have h_sub_fg : f - g ≤ᵐ[μ] 0,
    from hfg.mono (λ x hx, by rwa [pi.sub_apply, pi.zero_apply, sub_nonpos]),
  have h_sub_condexp : is_condexp m (fc - gc) (f-g) μ,
    from is_condexp.sub hf hg hfc_int hf_int hgc_int hg_int,
  exact is_condexp.nonpos hm h_sub_fg h_sub_condexp (hfc_int.sub hgc_int),
end

variables (𝕂)
lemma is_condexp.unique (hm : m ≤ m0) [borel_space 𝕂] {f₁ f₂ g : α → E'} (hf₁ : is_condexp m f₁ g μ)
  (h_int₁ : integrable f₁ μ) (hf₂ : is_condexp m f₂ g μ) (h_int₂ : integrable f₂ μ):
  f₁ =ᵐ[μ] f₂ :=
begin
  rcases hf₁ with ⟨⟨f₁', h_meas₁, hff'₁⟩, h_int_eq₁⟩,
  rcases hf₂ with ⟨⟨f₂', h_meas₂, hff'₂⟩, h_int_eq₂⟩,
  refine hff'₁.trans (eventually_eq.trans _ hff'₂.symm),
  have h : ∀ s : set α, @measurable_set α m s → ∫ x in s, f₁' x ∂μ = ∫ x in s, f₂' x ∂μ,
  { intros s hsm,
    have h₁ : ∫ x in s, f₁' x ∂μ = ∫ x in s, g x ∂μ,
    { rw ← h_int_eq₁ s hsm,
      exact set_integral_congr_ae (hm s hsm) (hff'₁.mono (λ x hx hxs, hx.symm)), },
    rw [h₁, ← h_int_eq₂ s hsm],
    exact set_integral_congr_ae (hm s hsm) (hff'₂.mono (λ x hx hxs, hx)), },
  refine ae_eq_of_ae_eq_trim hm _,
  have h_int₁' : integrable f₁' μ, from (integrable_congr hff'₁).mp h_int₁,
  have h_int₂' : integrable f₂' μ, from (integrable_congr hff'₂).mp h_int₂,
  refine @ae_eq_of_forall_set_integral_eq α E' 𝕂 _ _ _ _ _ _ _ _ _ m _ _ _ _ _ _ _,
  { exact integrable_trim_of_measurable hm h_meas₁ h_int₁', },
  { exact integrable_trim_of_measurable hm h_meas₂ h_int₂', },
  { intros s hs,
    specialize h s hs,
    rwa [set_integral_trim hm _ h_meas₁ h_int₁' hs,
      set_integral_trim hm _ h_meas₂ h_int₂' hs] at h, },
end
variables {𝕂}

lemma is_condexp.le_abs (hm : m ≤ m0) {f f_abs g : α → ℝ} (hfg : is_condexp m f g μ)
  (hfg_abs : is_condexp m f_abs (λ x, abs (g x)) μ) (hf : integrable f μ) (hg : integrable g μ)
  (hf_abs : integrable f_abs μ) :
  f ≤ᵐ[μ] f_abs :=
is_condexp.mono hm (eventually_of_forall (λ x, le_abs_self (g x))) hfg hf hg hfg_abs hf_abs
  (by { simp_rw [← real.norm_eq_abs], rwa integrable_norm_iff hg.1, })

/-- Replace this with a full statement of Jensen's inequality once we have the convexity results. -/
lemma is_condexp.jensen_norm (hm : m ≤ m0) {f f_abs g : α → ℝ} (hfg : is_condexp m f g μ)
  (hfg_abs : is_condexp m f_abs (λ x, abs (g x)) μ) (hf : integrable f μ) (hg : integrable g μ)
  (hf_abs : integrable f_abs μ) :
  ∀ᵐ x ∂μ, ∥f x∥ ≤ f_abs x :=
begin
  simp_rw [real.norm_eq_abs, abs_le],
  refine eventually.and _ (is_condexp.le_abs hm hfg hfg_abs hf hg hf_abs),
  simp_rw neg_le,
  refine is_condexp.le_abs hm hfg.neg _ hf.neg hg.neg hf_abs,
  simp_rw [pi.neg_apply, abs_neg],
  exact hfg_abs,
end

end is_condexp_properties

lemma ennreal.one_le_two : (1 : ℝ≥0∞) ≤ 2 := ennreal.coe_le_coe.2 (show (1 : ℝ≥0) ≤ 2, by norm_num)

section condexp_L2_clm

variables [borel_space 𝕂] {m m0 : measurable_space α} {μ : measure α}

variables (𝕂)
/-- Conditional expectation of a function in L2 with respect to a sigma-algebra -/
def condexp_L2_clm [complete_space E] (hm : m ≤ m0) :
  (α →₂[μ] E) →L[𝕂] (Lp_sub E 𝕂 m 2 μ) :=
@orthogonal_projection 𝕂 (α →₂[μ] E) _ _ (Lp_sub E 𝕂 m 2 μ)
  (by { haveI : fact (m ≤ m0) := ⟨hm⟩, exact infer_instance, })
variables {𝕂}

lemma integral_condexp_L2_eq_of_measure_finite (hm : m ≤ m0) {f : Lp E' 2 μ}
  (hf_int : integrable f μ) (h_condexp_int : integrable (condexp_L2_clm 𝕂 hm f) μ) {s : set α}
  (hs : @measurable_set α m s) (hμs : μ s < ∞) :
  ∫ x in s, condexp_L2_clm 𝕂 hm f x ∂μ = ∫ x in s, f x ∂μ :=
begin
  haveI : fact (m ≤ m0) := ⟨hm⟩,
  have h_inner_zero : ∀ (g : Lp E' 2 μ) (hg : g ∈ Lp_sub E' 𝕂 m 2 μ),
      inner (f - condexp_L2_clm 𝕂 hm f) g = (0 : 𝕂),
    from λ g hg, orthogonal_projection_inner_eq_zero f g hg,
  suffices h_sub : ∫ a in s, (f a - condexp_L2_clm 𝕂 hm f a) ∂μ = 0,
  { rw [integral_sub (hf_int.restrict s) (h_condexp_int.restrict s), sub_eq_zero] at h_sub,
    exact h_sub.symm, },
  refine integral_zero_of_forall_integral_inner_zero _ ((hf_int.sub h_condexp_int).restrict s) _,
  intro c,
  specialize h_inner_zero (indicator_Lp 2 (hm s hs) hμs c) (mem_Lp_sub_indicator_Lp hm hs),
  rw [inner_eq_zero_sym, inner_indicator_Lp] at h_inner_zero,
  rw ← h_inner_zero,
  refine set_integral_congr_ae (hm s hs) _,
  refine (Lp.coe_fn_sub f (condexp_L2_clm 𝕂 hm f)).mono (λ x hx hxs, _),
  congr,
  rw [hx, pi.sub_apply, Lp_sub_coe],
end

lemma is_condexp_condexp_L2 (hm : m ≤ m0) [finite_measure μ] (f : Lp E' 2 μ) :
  is_condexp m ((condexp_L2_clm 𝕂 hm f) : α → E') f μ :=
begin
  refine ⟨Lp_sub.ae_measurable' (condexp_L2_clm 𝕂 hm f), λ s hs, _⟩,
  have hf_int : integrable f μ, from Lp.integrable f ennreal.one_le_two,
  have h_condexp_int : integrable (condexp_L2_clm 𝕂 hm f) μ,
    from Lp.integrable (condexp_L2_clm 𝕂 hm f) ennreal.one_le_two,
  have hμs : μ s < ∞, from measure_lt_top μ s,
  exact integral_condexp_L2_eq_of_measure_finite hm hf_int h_condexp_int hs hμs,
end

end condexp_L2_clm

section coe_linear_maps

variables [measurable_space α] {μ : measure α}

lemma L1s_to_L2_add (f g : α →₁ₛ[μ] G) :
  (mem_ℒ2_simple_func_L1 (f+g)).to_Lp ⇑(f+g)
    = (mem_ℒ2_simple_func_L1 f).to_Lp f + (mem_ℒ2_simple_func_L1 g).to_Lp g :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_add _ _).symm),
  refine (Lp.coe_fn_add _ _).trans _,
  have hf : f.val =ᵐ[μ] mem_ℒp.to_Lp f (mem_ℒ2_simple_func_L1 f),
  { refine eventually_eq.trans _ (mem_ℒp.coe_fn_to_Lp _).symm,
    simp only [L1.simple_func.coe_coe, subtype.val_eq_coe], },
  have hg : g.val =ᵐ[μ] mem_ℒp.to_Lp g (mem_ℒ2_simple_func_L1 g),
  { refine eventually_eq.trans _ (mem_ℒp.coe_fn_to_Lp _).symm,
    simp only [L1.simple_func.coe_coe, subtype.val_eq_coe], },
  exact hf.add hg,
end

lemma L1s_to_L2_smul [opens_measurable_space 𝕂] (c : 𝕂) (f : α →₁ₛ[μ] E) :
  mem_ℒp.to_Lp ⇑(@has_scalar.smul _ _ L1.simple_func.has_scalar c f)
      (mem_ℒ2_simple_func_L1 (@has_scalar.smul _ _ L1.simple_func.has_scalar c f))
    = c • (mem_ℒp.to_Lp f (mem_ℒ2_simple_func_L1 f)) :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm),
  refine (Lp.coe_fn_smul _ _).trans _,
  suffices h : ⇑(f : Lp E 1 μ) =ᵐ[μ] (mem_ℒp.to_Lp ⇑f _),
    from eventually_eq.fun_comp h (λ x : E, c • x),
  refine eventually_eq.trans _ (mem_ℒp.coe_fn_to_Lp _).symm,
  simp,
end

/-- Linear map coercing a simple function of L1 to L2. -/
def L1s_to_L2_lm [opens_measurable_space 𝕂] : (α →₁ₛ[μ] E) →ₗ[𝕂] (α →₂[μ] E) :=
{ to_fun := λ f, mem_ℒp.to_Lp f (mem_ℒ2_simple_func_L1 f),
  map_add' := L1s_to_L2_add,
  map_smul' := L1s_to_L2_smul, }

lemma L1s_to_L2_coe_fn [opens_measurable_space 𝕂] (f : α →₁ₛ[μ] E) : L1s_to_L2_lm f =ᵐ[μ] f :=
mem_ℒp.coe_fn_to_Lp _

lemma integrable_L1s_to_L2 [opens_measurable_space 𝕂] (f : α →₁ₛ[μ] E) :
  integrable (L1s_to_L2_lm f) μ :=
(integrable_congr (L1s_to_L2_coe_fn f)).mpr (L1.integrable_coe_fn _)

/-- Linear map coercing a simple function of L1 to the subspace of integrable functions of L2. -/
def L1s_to_L2_integrable_lm [opens_measurable_space 𝕂] : (α →₁ₛ[μ] E) →ₗ[𝕂] (L2_integrable E 𝕂 μ) :=
{ to_fun := λ f, ⟨mem_ℒp.to_Lp f (mem_ℒ2_simple_func_L1 f),
    mem_L2_integrable_iff_integrable.mpr (integrable_L1s_to_L2 _)⟩,
  map_add' := λ f g,
    by { ext1, simp only [submodule.coe_add, submodule.coe_mk], exact L1s_to_L2_add f g, },
  map_smul' :=  λ c f,
    by { ext1, simp only [submodule.coe_smul, submodule.coe_mk], exact L1s_to_L2_smul c f, }, }

lemma L1s_to_L2_integrable_coe_fn [opens_measurable_space 𝕂] (f : α →₁ₛ[μ] E) :
  L1s_to_L2_integrable_lm f =ᵐ[μ] f :=
mem_ℒp.coe_fn_to_Lp _

lemma L2_integrable_to_L1_add (f g : α →₂[μ] G) (hf : integrable f μ) (hg : integrable g μ) :
  ((mem_ℒp_congr_ae (Lp.coe_fn_add _ _)).mpr
      (mem_ℒp_one_iff_integrable.mpr (hf.add hg))).to_Lp ⇑(f+g)
    = (mem_ℒp_one_iff_integrable.mpr hf).to_Lp f + (mem_ℒp_one_iff_integrable.mpr hg).to_Lp g :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_add _ _).symm),
  refine (Lp.coe_fn_add _ _).trans _,
  have hf : ⇑f =ᵐ[μ] mem_ℒp.to_Lp f (mem_ℒp_one_iff_integrable.mpr hf),
    from (mem_ℒp.coe_fn_to_Lp _).symm,
  have hg : g.val =ᵐ[μ] mem_ℒp.to_Lp g (mem_ℒp_one_iff_integrable.mpr hg),
    from (mem_ℒp.coe_fn_to_Lp _).symm,
  exact hf.add hg,
end

lemma L2_integrable_to_L1_smul [opens_measurable_space 𝕂] (c : 𝕂) (f : α →₂[μ] E)
  (hf : integrable f μ) :
  ((mem_ℒp_congr_ae (Lp.coe_fn_smul c _)).mpr
    (mem_ℒp_one_iff_integrable.mpr (hf.smul c))).to_Lp ⇑(c • f)
    = c • ((mem_ℒp_one_iff_integrable.mpr hf).to_Lp f) :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm),
  refine (Lp.coe_fn_smul _ _).trans _,
  suffices h : ⇑f =ᵐ[μ] (mem_ℒp.to_Lp ⇑f _), from eventually_eq.fun_comp h (λ x : E, c • x),
  exact (mem_ℒp.coe_fn_to_Lp _).symm,
end

/-- Linear map sending an integrable function of L2 to L1. -/
def L2_integrable_to_L1_lm [opens_measurable_space 𝕂] : (L2_integrable E 𝕂 μ) →ₗ[𝕂] (α →₁[μ] E) :=
{ to_fun    := λ f, (mem_ℒp_one_iff_integrable.mpr (L2_integrable.integrable f)).to_Lp f,
  map_add'  := λ f g, L2_integrable_to_L1_add f g (L2_integrable.integrable f)
    (L2_integrable.integrable g),
  map_smul' := λ c f, L2_integrable_to_L1_smul c f (L2_integrable.integrable f), }

variables [finite_measure μ]

lemma L2_to_L1_add (f g : α →₂[μ] G) :
  (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp (f+g)) ennreal.one_le_two).to_Lp ⇑(f+g)
    = (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two).to_Lp f
      + (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp g) ennreal.one_le_two).to_Lp g :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_add _ _).symm),
  refine (Lp.coe_fn_add _ _).trans _,
  have hf : ⇑f =ᵐ[μ] mem_ℒp.to_Lp f
    (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two),
  { exact (mem_ℒp.coe_fn_to_Lp _).symm, },
  have hg : g.val =ᵐ[μ] mem_ℒp.to_Lp g
    (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp g) ennreal.one_le_two),
  { exact (mem_ℒp.coe_fn_to_Lp _).symm, },
  exact hf.add hg,
end

lemma L2_to_L1_smul [borel_space 𝕂] (c : 𝕂) (f : α →₂[μ] E) :
  (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp (c • f)) ennreal.one_le_two).to_Lp ⇑(c • f)
    = c • ((mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two).to_Lp f) :=
begin
  ext1,
  refine (mem_ℒp.coe_fn_to_Lp _).trans (eventually_eq.trans _ (Lp.coe_fn_smul _ _).symm),
  refine (Lp.coe_fn_smul _ _).trans _,
  suffices h : ⇑f =ᵐ[μ] (mem_ℒp.to_Lp ⇑f _), from eventually_eq.fun_comp h (λ x : E, c • x),
  exact (mem_ℒp.coe_fn_to_Lp _).symm,
end

lemma continuous_L2_to_L1 : continuous (λ (f : α →₂[μ] G),
    (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two).to_Lp f) :=
begin
  rw metric.continuous_iff,
  intros f ε hε_pos,
  simp_rw dist_def,
  by_cases hμ0 : μ = 0,
  { simp only [hμ0, exists_prop, forall_const, gt_iff_lt, ennreal.zero_to_real, snorm_measure_zero],
    exact ⟨ε, hε_pos, λ h, h⟩, },
  have h_univ_pow_pos : 0 < (μ set.univ ^ (1 / (2 : ℝ))).to_real,
  { refine ennreal.to_real_pos_iff.mpr ⟨_, _⟩,
    { have hμ_univ_pos : 0 < μ set.univ,
      { refine lt_of_le_of_ne (zero_le _) (ne.symm _),
        rwa [ne.def, measure_theory.measure.measure_univ_eq_zero], },
      exact ennreal.rpow_pos hμ_univ_pos (measure_ne_top μ set.univ), },
    { refine ennreal.rpow_ne_top_of_nonneg _ (measure_ne_top μ set.univ),
      simp [zero_le_one], }, },
  refine ⟨ε / (μ set.univ ^ (1/(2 : ℝ))).to_real, div_pos hε_pos h_univ_pow_pos, λ g hfg, _⟩,
  rw lt_div_iff h_univ_pow_pos at hfg,
  refine lt_of_le_of_lt _ hfg,
  rw ← ennreal.to_real_mul,
  rw ennreal.to_real_le_to_real _ _,
  swap, { rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm, exact Lp.snorm_ne_top _, },
  swap, { rw snorm_congr_ae (Lp.coe_fn_sub _ _).symm,
    refine ennreal.mul_ne_top _ _,
    exact Lp.snorm_ne_top _,
    refine ennreal.rpow_ne_top_of_nonneg _ _,
    simp [zero_le_one],
    exact measure_ne_top μ set.univ, },
  refine (le_of_eq _).trans ((snorm_le_snorm_mul_rpow_measure_univ (ennreal.one_le_two)
    ((Lp.ae_measurable g).sub (Lp.ae_measurable f))).trans (le_of_eq _)),
  { refine snorm_congr_ae _,
    exact eventually_eq.sub
      ((Lp.mem_ℒp g).mem_ℒp_of_exponent_le ennreal.one_le_two).coe_fn_to_Lp
      ((Lp.mem_ℒp f).mem_ℒp_of_exponent_le ennreal.one_le_two).coe_fn_to_Lp, },
  { congr,
    simp only [ennreal.one_to_real, ennreal.to_real_bit0, div_one],
    norm_num, },
end

/-- Continuous linear map sending a function of L2 to L1. -/
def L2_to_L1_clm [borel_space 𝕂] : (α →₂[μ] E) →L[𝕂] (α →₁[μ] E) :=
{ to_fun    := λ f, (mem_ℒp.mem_ℒp_of_exponent_le (Lp.mem_ℒp f) ennreal.one_le_two).to_Lp f,
  map_add'  := L2_to_L1_add,
  map_smul' := L2_to_L1_smul,
  cont      := continuous_L2_to_L1, }

lemma L2_to_L1_coe_fn [borel_space 𝕂] (f : α →₂[μ] E) : L2_to_L1_clm f =ᵐ[μ] f :=
mem_ℒp.coe_fn_to_Lp _

end coe_linear_maps

section condexp_L1s

variables {m m0 : measurable_space α} (hm : m ≤ m0) [complete_space E] {μ : measure α}
  [finite_measure μ] [borel_space 𝕂]

variables (𝕂)
/-- Conditional expectation as a linear map from the simple functions of L1 to L1. -/
def condexp_L1s_lm : (α →₁ₛ[μ] E) →ₗ[𝕂] (α →₁[μ] E) :=
L2_to_L1_clm.to_linear_map.comp ((Lp_sub E 𝕂 m 2 μ).subtype.comp
  ((condexp_L2_clm 𝕂 hm).to_linear_map.comp L1s_to_L2_lm))

lemma condexp_L1s_lm_neg (f : α →₁ₛ[μ] E) : condexp_L1s_lm 𝕂 hm (-f) = -condexp_L1s_lm 𝕂 hm f :=
linear_map.map_neg (condexp_L1s_lm 𝕂 hm) f
variables {𝕂}

lemma condexp_L1s_ae_eq_condexp_L2 (f : α →₁ₛ[μ] E) :
  condexp_L1s_lm 𝕂 hm f =ᵐ[μ] condexp_L2_clm 𝕂 hm (L1s_to_L2_lm f) :=
(L2_to_L1_coe_fn _).trans (by refl)

lemma is_condexp_condexp_L2_L1s_to_L2 (f : α →₁ₛ[μ] E') :
  is_condexp m (condexp_L2_clm 𝕂 hm (L1s_to_L2_lm f) : α → E') f μ :=
is_condexp_congr_ae_right' hm (L1s_to_L2_coe_fn f) (is_condexp_condexp_L2 hm _)

variables (𝕂)
lemma is_condexp_condexp_L1s (f : α →₁ₛ[μ] E') :
  is_condexp m ((condexp_L1s_lm 𝕂 hm f) : α → E') f μ :=
is_condexp_congr_ae_left' hm (condexp_L1s_ae_eq_condexp_L2 hm _).symm
  (is_condexp_condexp_L2_L1s_to_L2 hm f)

lemma integral_condexp_L1s (f : α →₁ₛ[μ] E') {s : set α} (hs : @measurable_set α m s) :
  ∫ a in s, (condexp_L1s_lm 𝕂 hm f) a ∂μ = ∫ a in s, f a ∂μ :=
(is_condexp_condexp_L1s 𝕂 hm f).2 s hs
variables {𝕂}

end condexp_L1s

section condexp_L1s_ℝ

variables {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α} [finite_measure μ]

lemma condexp_L1s_nonneg {f : α →₁ₛ[μ] ℝ} (hf : 0 ≤ᵐ[μ] f) : 0 ≤ᵐ[μ] condexp_L1s_lm ℝ hm f :=
is_condexp.nonneg hm hf (is_condexp_condexp_L1s ℝ hm f) (Lp.integrable _ le_rfl)

lemma condexp_L1s_nonpos {f : α →₁ₛ[μ] ℝ} (hf : f ≤ᵐ[μ] 0) : condexp_L1s_lm ℝ hm f ≤ᵐ[μ] 0 :=
is_condexp.nonpos hm hf (is_condexp_condexp_L1s ℝ hm f) (Lp.integrable _ le_rfl)

lemma condexp_L1s_mono {f g : α →₁ₛ[μ] ℝ} (hfg : f ≤ᵐ[μ] g) :
  condexp_L1s_lm ℝ hm f ≤ᵐ[μ] condexp_L1s_lm ℝ hm g :=
is_condexp.mono hm hfg (is_condexp_condexp_L1s ℝ hm f) (Lp.integrable _ le_rfl)
  (Lp.integrable _ le_rfl) (is_condexp_condexp_L1s ℝ hm g) (Lp.integrable _ le_rfl)
  (Lp.integrable _ le_rfl)

lemma condexp_L1s_R_jensen_norm (f : α →₁ₛ[μ] ℝ) :
  ∀ᵐ x ∂μ, ∥condexp_L1s_lm ℝ hm f x∥
    ≤ condexp_L1s_lm ℝ hm (L1.simple_func.map (λ x, ∥x∥) f norm_zero) x :=
begin
  have h := is_condexp_congr_ae_right' hm (L1.simple_func.map_coe (λ (x : ℝ), ∥x∥) f norm_zero)
    (is_condexp_condexp_L1s ℝ hm (L1.simple_func.map (λ (x : ℝ), ∥x∥) f norm_zero)),
  exact is_condexp.jensen_norm hm (is_condexp_condexp_L1s ℝ hm f) h
      (Lp.integrable _ le_rfl) (Lp.integrable _ le_rfl) (Lp.integrable _ le_rfl),
end

--lemma condexp_L1s_R_jensen {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α}
--  [finite_measure μ] (f : α →₁ₛ[μ] ℝ) (F : ℝ → ℝ) (hF : convex_on (set.univ : set ℝ) F) :
--  ∀ᵐ x ∂μ, F (condexp_L1s_lm ℝ hm f x) ≤ condexp_L1s_lm ℝ hm (L1.simple_func.map F f) x :=
--begin
--  sorry
--end

lemma norm_condexp_L1s_le_R (f : α →₁ₛ[μ] ℝ) : ∥condexp_L1s_lm ℝ hm f∥ ≤ ∥f∥ :=
begin
  simp_rw [L1.simple_func.norm_eq, norm_def],
  rw ennreal.to_real_le_to_real (Lp.snorm_ne_top _) (Lp.snorm_ne_top _),
  simp_rw [snorm_eq_snorm' ennreal.zero_lt_one.ne.symm ennreal.coe_ne_top, ennreal.one_to_real,
    snorm', div_one, ennreal.rpow_one],
  let F := λ x : ℝ, ∥x∥,
  have h_left : ∫⁻ a, (nnnorm (((condexp_L1s_lm ℝ hm) f) a) : ℝ≥0∞) ∂μ
      = ∫⁻ a, ennreal.of_real (∥((condexp_L1s_lm ℝ hm) f) a∥) ∂μ,
    by { congr, ext1 x, rw ← of_real_norm_eq_coe_nnnorm, },
  have h_right : ∫⁻ a, (nnnorm ((f : Lp ℝ 1 μ) a) : ℝ≥0∞) ∂μ
      = ∫⁻ a, ennreal.of_real (∥(f : Lp ℝ 1 μ) a∥) ∂μ,
    by { congr, ext1 x, rw ← of_real_norm_eq_coe_nnnorm, },
  rw [h_left, h_right],
  have h_le : ∫⁻ a, ennreal.of_real (∥((condexp_L1s_lm ℝ hm) f) a∥) ∂μ
    ≤ ∫⁻ a, ennreal.of_real (condexp_L1s_lm ℝ hm (L1.simple_func.map F f norm_zero) a) ∂μ,
  { refine lintegral_mono_ae ((condexp_L1s_R_jensen_norm hm f).mono (λ x hx, _)),
    rwa ennreal.of_real_le_of_real_iff ((norm_nonneg _).trans hx), },
  refine h_le.trans _,
  have h_integral_eq := integral_condexp_L1s ℝ hm (L1.simple_func.map F f norm_zero)
    (@measurable_set.univ α m),
  rw [integral_univ, integral_univ] at h_integral_eq,
  rw ← (ennreal.to_real_le_to_real _ _),
  swap, { have h := Lp.snorm_ne_top (condexp_L1s_lm ℝ hm (L1.simple_func.map F f norm_zero)),
    rw [snorm_eq_snorm' (one_ne_zero) ennreal.coe_ne_top, snorm', ennreal.one_to_real, one_div_one,
      ennreal.rpow_one] at h,
    simp_rw [ennreal.rpow_one, ← of_real_norm_eq_coe_nnnorm, ← lt_top_iff_ne_top] at h,
    refine (lt_of_le_of_lt _ h).ne,
    refine lintegral_mono_ae (eventually_of_forall (λ x, ennreal.of_real_le_of_real _)),
    rw real.norm_eq_abs,
    exact le_abs_self _, },
  swap, { simp_rw of_real_norm_eq_coe_nnnorm,
    have h := Lp.snorm_ne_top (f : α →₁[μ] ℝ),
    rw [snorm_eq_snorm' (one_ne_zero) ennreal.coe_ne_top, snorm', ennreal.one_to_real, one_div_one,
      ennreal.rpow_one] at h,
    simp_rw ennreal.rpow_one at h,
    exact h, },
  rw [← integral_eq_lintegral_of_nonneg_ae _ (Lp.ae_measurable _),
    ← integral_eq_lintegral_of_nonneg_ae, h_integral_eq,
    integral_congr_ae (L1.simple_func.map_coe F f norm_zero)],
  { simp only [L1.simple_func.coe_coe], },
  { exact eventually_of_forall (by simp [norm_nonneg]), },
  { exact measurable.comp_ae_measurable measurable_norm (Lp.ae_measurable _), },
  { refine condexp_L1s_nonneg hm ((L1.simple_func.map_coe F f norm_zero).mono (λ x hx, _)),
    rw [hx, pi.zero_apply],
    simp only [norm_nonneg], },
end

lemma norm_condexp_L1s_indicator_L1s_R_le {s : set α} (hs : measurable_set s) (hμs : μ s < ∞)
  (c : ℝ) :
  ∥condexp_L1s_lm ℝ hm (indicator_L1s hs hμs c)∥ ≤ ∥c∥ * (μ s).to_real :=
(norm_condexp_L1s_le_R hm _).trans norm_indicator_L1s.le

end condexp_L1s_ℝ

section continuous_set_integral

variables [measurable_space α] {μ : measure α}

lemma Lp_to_Lp_restrict_add (f g : Lp G p μ) (s : set α) :
  ((Lp.mem_ℒp (f+g)).restrict s).to_Lp ⇑(f+g)
    = ((Lp.mem_ℒp f).restrict s).to_Lp f + ((Lp.mem_ℒp g).restrict s).to_Lp g :=
begin
  ext1,
  refine (ae_restrict_of_ae (Lp.coe_fn_add f g)).mp _,
  refine (Lp.coe_fn_add (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s))
    (mem_ℒp.to_Lp g ((Lp.mem_ℒp g).restrict s))).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp g).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp (f+g)).restrict s)).mono (λ x hx1 hx2 hx3 hx4 hx5, _),
  rw [hx4, hx1, pi.add_apply, hx2, hx3, hx5, pi.add_apply],
end

lemma Lp_to_Lp_restrict_smul [opens_measurable_space 𝕂] (c : 𝕂) (f : Lp F p μ) (s : set α) :
  ((Lp.mem_ℒp (c • f)).restrict s).to_Lp ⇑(c • f) = c • (((Lp.mem_ℒp f).restrict s).to_Lp f) :=
begin
  ext1,
  refine (ae_restrict_of_ae (Lp.coe_fn_smul c f)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)).mp _,
  refine (mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp (c • f)).restrict s)).mp _,
  refine (Lp.coe_fn_smul c (mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s))).mono
    (λ x hx1 hx2 hx3 hx4, _),
  rw [hx2, hx1, pi.smul_apply, hx3, hx4, pi.smul_apply],
end

variables (α F 𝕂)
/-- Linear map sending a function of `Lp F p μ` to the same function in `Lp F p (μ.restrict s)`. -/
def Lp_to_Lp_restrict_lm [borel_space 𝕂] (p : ℝ≥0∞) (s : set α) :
  @linear_map 𝕂 (Lp F p μ) (Lp F p (μ.restrict s)) _ _ _ _ _ :=
{ to_fun := λ f, mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s),
  map_add' := λ f g, Lp_to_Lp_restrict_add f g s,
  map_smul' := λ c f, Lp_to_Lp_restrict_smul c f s, }
variables {α F 𝕂}

lemma norm_Lp_to_Lp_restrict_le (s : set α) (f : Lp G p μ) :
  ∥mem_ℒp.to_Lp f ((Lp.mem_ℒp f).restrict s)∥ ≤ ∥f∥ :=
begin
  rw [norm_def, norm_def, ennreal.to_real_le_to_real (snorm_ne_top _) (snorm_ne_top _)],
  refine (le_of_eq _).trans (snorm_mono_measure measure.restrict_le_self),
  { exact s, },
  exact snorm_congr_ae (mem_ℒp.coe_fn_to_Lp _),
end

variables (α F 𝕂)
/-- Continuous linear map sending a function of `Lp F p μ` to the same function in
`Lp F p (μ.restrict s)`. -/
def Lp_to_Lp_restrict_clm [borel_space 𝕂] (μ : measure α) (p : ℝ≥0∞) [hp : fact(1 ≤ p)]
  (s : set α) :
  @continuous_linear_map 𝕂 _ (Lp F p μ) _ _ (Lp F p (μ.restrict s)) _ _ _ _ :=
@linear_map.mk_continuous 𝕂 (Lp F p μ) (Lp F p (μ.restrict s)) _ _ _ _ _
  (Lp_to_Lp_restrict_lm α F 𝕂 p s) 1
  (by { intro f, rw one_mul, exact norm_Lp_to_Lp_restrict_le s f, })

@[continuity]
lemma continuous_Lp_to_Lp_restrict [borel_space 𝕂] (p : ℝ≥0∞) [hp : fact(1 ≤ p)] (s : set α) :
  continuous (Lp_to_Lp_restrict_clm α F 𝕂 μ p s) :=
continuous_linear_map.continuous _
variables {α F 𝕂}

variables (𝕂)
lemma Lp_to_Lp_restrict_clm_coe_fn [borel_space 𝕂] [hp : fact(1 ≤ p)] (s : set α) (f : Lp F p μ) :
  Lp_to_Lp_restrict_clm α F 𝕂 μ p s f =ᵐ[μ.restrict s] f :=
mem_ℒp.coe_fn_to_Lp ((Lp.mem_ℒp f).restrict s)
variables {𝕂}

@[continuity]
lemma continuous_set_integral (s : set α) : continuous (λ f : α →₁[μ] G', ∫ x in s, f x ∂μ) :=
begin
  haveI : fact((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩,
  have h_comp : (λ f : α →₁[μ] G', ∫ x in s, f x ∂μ)
    = (integral (μ.restrict s)) ∘ (λ f, Lp_to_Lp_restrict_clm α G' ℝ μ 1 s f),
  { ext1 f,
    rw [function.comp_apply, integral_congr_ae (Lp_to_Lp_restrict_clm_coe_fn ℝ s f)], },
  rw h_comp,
  exact continuous_integral.comp (continuous_Lp_to_Lp_restrict α G' ℝ 1 s),
end

end continuous_set_integral

section condexp_def

variables {m m0 : measurable_space α} (hm : m ≤ m0) {μ : measure α} [finite_measure μ]
  [borel_space 𝕂]

variables (𝕂)
lemma condexp_L1s_indicator_L1s_eq {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : E') :
  condexp_L1s_lm 𝕂 hm (indicator_L1s hs hμs c) =ᵐ[μ]
    λ x, (condexp_L1s_lm ℝ hm (@indicator_L1s α ℝ _ _ _ _ _ μ _ hs hμs 1) x) • c :=
begin
  refine is_condexp.unique 𝕂 hm (is_condexp_condexp_L1s 𝕂 hm _) (Lp.integrable _ le_rfl) _ _,
  swap,
  { by_cases hc : c = 0,
    { simp [hc], },
    { exact (integrable_smul_const hc).mpr (Lp.integrable _ le_rfl), }, },
  obtain ⟨⟨f₁', h_meas₁, hff'₁⟩, h_int_eq₁⟩ := is_condexp_condexp_L1s ℝ hm
    (@indicator_L1s α ℝ _ _ _ _ _ μ _ hs hμs 1),
  refine ⟨_, _⟩,
  { refine ⟨λ x, (f₁' x) • c, _, _⟩,
    { exact @measurable.smul _ m _ _ _ _ _ _ f₁' _ h_meas₁ (@measurable_const _ _ _ m c), },
    { exact eventually_eq.fun_comp hff'₁ (λ x, x • c), }, },
  { intros t ht,
    have h_smul : ∫ a in t, (indicator_L1s hs hμs c) a ∂μ
        = ∫ a in t, ((indicator_L1s hs hμs (1 : ℝ)) a) • c ∂μ,
      from set_integral_congr_ae (hm t ht)  ((indicator_L1s_eq_smul c).mono (λ x hx hxs, hx)),
    refine eq.trans _ h_smul.symm,
    rw [integral_smul_const, integral_smul_const, h_int_eq₁ t ht], },
end
variables {𝕂}

lemma norm_condexp_L1s_indicator_L1s {s : set α} (hs : measurable_set s) (hμs : μ s < ∞) (c : E') :
  ∥condexp_L1s_lm 𝕂 hm (indicator_L1s hs hμs c)∥ ≤ ∥indicator_L1s hs hμs c∥ :=
begin
  rw [L1.simple_func.norm_eq, indicator_L1s_coe,
    norm_indicator_Lp ennreal.zero_lt_one ennreal.coe_ne_top, norm_def,
    snorm_congr_ae (condexp_L1s_indicator_L1s_eq 𝕂 hm hs hμs c),
    snorm_eq_snorm' ennreal.zero_lt_one.ne.symm ennreal.coe_ne_top, snorm'],
  simp_rw [ennreal.one_to_real, div_one, ennreal.rpow_one, real.rpow_one, nnnorm_smul,
    ennreal.coe_mul],
  rw [lintegral_mul_const _ (Lp.measurable _).nnnorm.ennreal_coe, ennreal.to_real_mul, mul_comm,
    ← of_real_norm_eq_coe_nnnorm, ennreal.to_real_of_real (norm_nonneg _)],
  swap, { apply_instance, },
  refine mul_le_mul le_rfl _ ennreal.to_real_nonneg (norm_nonneg _),
  suffices h_norm : ∥(condexp_L1s_lm ℝ hm) (indicator_L1s hs hμs (1 : ℝ))∥ ≤ (μ s).to_real,
  { rw [norm_def, snorm_eq_snorm' ennreal.zero_lt_one.ne.symm ennreal.coe_ne_top,
      snorm', ennreal.one_to_real, div_one] at h_norm,
    simp_rw ennreal.rpow_one at h_norm,
    exact h_norm, },
  refine (norm_condexp_L1s_indicator_L1s_R_le hm hs hμs (1 : ℝ)).trans _,
  simp only [one_mul, norm_one],
end

lemma norm_condexp_L1s_le (f : α →₁ₛ[μ] E') : ∥condexp_L1s_lm 𝕂 hm f∥ ≤ ∥f∥ :=
begin
  rw L1.simple_func.norm_eq_integral,
  rw simple_func.map_integral _ _ (L1.simple_func.integrable _),
  swap, { exact norm_zero, },
  nth_rewrite 0 L1.simple_func_eq_sum_indicator_L1s f,
  rw linear_map.map_sum,
  refine (norm_sum_le _ _).trans _,
  refine finset.sum_le_sum (λ x hxf, (norm_condexp_L1s_indicator_L1s hm _ _ x).trans _),
  rw [smul_eq_mul, mul_comm, norm_indicator_L1s],
end

lemma continuous_condexp_L1s : continuous (@condexp_L1s_lm α E' 𝕂 _ _ _ _ _ _ m m0 hm _ μ _ _) :=
linear_map.continuous_of_bound _ 1 (λ f, (norm_condexp_L1s_le hm f).trans (one_mul _).symm.le)

variables (𝕂)
/-- Conditional expectation as a continuous linear map from the simple functions in L1 to L1. -/
def condexp_L1s_clm : (α →₁ₛ[μ] E') →L[𝕂] (α →₁[μ] E') :=
{ to_linear_map := condexp_L1s_lm 𝕂 hm,
  cont := continuous_condexp_L1s hm, }

/-- Conditional expectation as a continuous linear map from L1 to L1. -/
def condexp_L1 : (α →₁[μ] E') →L[𝕂] (α →₁[μ] E') :=
@continuous_linear_map.extend 𝕂 (α →₁ₛ[μ] E') (α →₁[μ] E') (α →₁[μ] E') _ _ _ _ _ _ _
  (condexp_L1s_clm 𝕂 hm) _ (L1.simple_func.coe_to_L1 α E' 𝕂) L1.simple_func.dense_range
  L1.simple_func.uniform_inducing

lemma condexp_L1_eq_condexp_L1s (f : α →₁ₛ[μ] E') :
  condexp_L1 𝕂 hm (f : α →₁[μ] E') = condexp_L1s_clm 𝕂 hm f :=
begin
  refine uniformly_extend_of_ind L1.simple_func.uniform_inducing L1.simple_func.dense_range _ _,
  exact @continuous_linear_map.uniform_continuous 𝕂 (α →₁ₛ[μ] E') (α →₁[μ] E') _ _ _ _ _
    (@condexp_L1s_clm α E' 𝕂 _ _ _ _ _ _ _ _ _ _ _ hm μ _ _),
end
variables {𝕂}

lemma ae_measurable'_condexp_L1 (f : α →₁[μ] E') : ae_measurable' m (condexp_L1 𝕂 hm f) μ :=
begin
  refine @is_closed_property _ (α →₁[μ] E') _ _ _ L1.simple_func.dense_range _ _ f,
  { change is_closed ((condexp_L1 𝕂 hm) ⁻¹' {x : ↥(Lp E' 1 μ) | ae_measurable' m x μ}),
    haveI : fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩,
    exact is_closed.preimage (continuous_linear_map.continuous _) (is_closed_ae_measurable' hm), },
  { intro fs,
    rw condexp_L1_eq_condexp_L1s,
    obtain ⟨f', hf'_meas, hf'⟩ := (is_condexp_condexp_L1s 𝕂 hm fs).1,
    refine ⟨f', hf'_meas, _⟩,
    refine eventually_eq.trans (eventually_of_forall (λ x, _)) hf',
    refl, },
end

lemma integral_eq_condexp_L1 (f : α →₁[μ] E') (s : set α) (hs : @measurable_set α m s) :
  ∫ a in s, (condexp_L1 𝕂 hm f) a ∂μ = ∫ a in s, f a ∂μ :=
begin
  refine @is_closed_property _ (α →₁[μ] E') _ _ _ L1.simple_func.dense_range (is_closed_eq _ _) _ f,
  { change continuous ((λ (g : ↥(Lp E' 1 μ)), ∫ (a : α) in s, g a ∂μ) ∘ (condexp_L1 𝕂 hm)),
    continuity, },
  { continuity, },
  { simp_rw condexp_L1_eq_condexp_L1s,
    exact λ fs, (is_condexp_condexp_L1s 𝕂 hm fs).2 s hs, },
end

lemma is_condexp_condexp_L1 (f : α →₁[μ] E') : is_condexp m (condexp_L1 𝕂 hm f) f μ :=
⟨ae_measurable'_condexp_L1 hm f, integral_eq_condexp_L1 hm f⟩

variables (𝕂)
include 𝕂 hm
/-- Conditional expectation of an integrable function. This is an `m`-measurable function such
that for all `m`-measurable sets `s`, `∫ x in s, condexp 𝕂 hm f hf x ∂μ = ∫ x in s, f x ∂μ`. -/
def condexp (f : α → E') (hf : integrable f μ) : α → E' :=
(is_condexp_condexp_L1 hm (hf.to_L1 f)).1.some
omit 𝕂 hm
variables {𝕂}

end condexp_def

section condexp_properties
include 𝕂

variables {f f₂ g : α → E'} {m₂ m m0 : measurable_space α} {hm : m ≤ m0} {μ : measure α}
  [finite_measure μ] [borel_space 𝕂]

lemma measurable_condexp (hf : integrable f μ) : @measurable _ _ m _ (condexp 𝕂 hm f hf) :=
(is_condexp_condexp_L1 hm (hf.to_L1 f)).1.some_spec.1

lemma condexp_ae_eq_condexp_L1 (hf : integrable f μ) :
  condexp 𝕂 hm f hf =ᵐ[μ] condexp_L1 𝕂 hm (hf.to_L1 f) :=
(is_condexp_condexp_L1 hm (hf.to_L1 f)).1.some_spec.2.symm

lemma is_condexp_condexp (hf : integrable f μ) : is_condexp m (condexp 𝕂 hm f hf) f μ :=
is_condexp_congr_ae' hm (condexp_ae_eq_condexp_L1 hf).symm (integrable.coe_fn_to_L1 hf)
  (is_condexp_condexp_L1 hm (hf.to_L1 f))

lemma integrable_condexp (hf : integrable f μ) : integrable (condexp 𝕂 hm f hf) μ :=
(integrable_congr (condexp_ae_eq_condexp_L1 hf)).mpr (Lp.integrable _ le_rfl)

lemma integrable_trim_condexp (hf : integrable f μ) :
  @integrable α E' m _ _ (condexp 𝕂 hm f hf) (μ.trim hm) :=
integrable_trim_of_measurable hm (measurable_condexp hf) (integrable_condexp hf)

lemma set_integral_condexp_eq (hf : integrable f μ) {s : set α} (hs : @measurable_set α m s) :
  ∫ x in s, condexp 𝕂 hm f hf x ∂μ = ∫ x in s, f x ∂μ :=
(is_condexp_condexp hf).2 s hs

lemma integral_condexp (hf : integrable f μ) : ∫ x, condexp 𝕂 hm f hf x ∂μ = ∫ x, f x ∂μ :=
by rw [← integral_univ, set_integral_condexp_eq hf (@measurable_set.univ α m), integral_univ]

lemma condexp_comp (hm2 : m₂ ≤ m) (hm : m ≤ m0) (hf : integrable f μ) :
  condexp 𝕂 (hm2.trans hm) (condexp 𝕂 hm f hf) (integrable_condexp hf)
    =ᵐ[μ] condexp 𝕂 (hm2.trans hm) f hf :=
begin
  refine is_condexp.unique 𝕂 (hm2.trans hm) _ (integrable_condexp _)
    (is_condexp_condexp hf) (integrable_condexp hf),
  exact is_condexp.trans hm2 (is_condexp_condexp _) (is_condexp_condexp hf),
end

omit 𝕂
end condexp_properties

end measure_theory
