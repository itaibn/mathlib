import analysis.box_integral.stokes
import analysis.box_integral.integrability

namespace measure_theory

open set finset topological_space box_integral
open_locale big_operators classical

universes u v
variables {ι : Type u} {E : Type v} [fintype ι] [decidable_eq ι] [normed_group E] [normed_space ℝ E]
  [measurable_space E] [borel_space E] [second_countable_topology E] [complete_space E]

lemma integral_divergence_of_forall_has_deriv_within_at (f : ι → (ι → ℝ) → E)
  (f' : ι → (ι → ℝ) → (ι → ℝ) →L[ℝ] E) {a b : ι → ℝ} (hle : a ≤ b)
  (H : ∀ (x ∈ Icc a b) i, has_fderiv_within_at (f i) (f' i x) (Icc a b) x)
  (Hi : integrable_on (λ x, ∑ i, f' i x (pi.single i 1)) (Icc a b)) :
  ∫ x in Icc a b, ∑ i, f' i x (pi.single i 1) =
    ∑ i, ((∫ x : ({i}ᶜ : set ι) → ℝ in Icc (a ∘ coe) (b ∘ coe), f i (pi_insert_one i (b i) x)) -
      ∫ x : ({i}ᶜ : set ι) → ℝ in Icc (a ∘ coe) (b ∘ coe), f i (pi_insert_one i (a i) x)) :=
begin
  unfreezingI { obtain rfl : ‹decidable_eq ι› = λ a b, classical.prop_decidable _ := subsingleton.elim _ _ },
  simp only [volume_pi, ← set_integral_congr_set_ae measure.univ_pi_Ioc_ae_eq_Icc],
  by_cases heq : ∃ i, a i = b i,
  { rcases heq with ⟨i, hi⟩,
    have hi' : Ioc (a i) (b i) = ∅ := Ioc_eq_empty hi.not_lt,
    have : pi set.univ (λ j, Ioc (a j) (b j)) = ∅, from univ_pi_eq_empty hi',
    rw [this, integral_empty, sum_eq_zero],
    rintro j -,
    rcases eq_or_ne i j with (rfl|hne),
    { simp [hi] },
    { have : pi set.univ (λ i : ({j}ᶜ : set ι), Ioc ((a ∘ coe) i) ((b ∘ coe) i)) = ∅,
      { refine @univ_pi_eq_empty ({j}ᶜ : set ι) _ _ ⟨i, hne⟩ _, exact hi' },
      rw [this, integral_empty, integral_empty, sub_self] } },
  { push_neg at heq,
    obtain ⟨I, rfl, rfl⟩ : ∃ I : box_integral.box ι, I.lower = a ∧ I.upper = b,
      from ⟨⟨a, b, λ i, (hle i).lt_of_ne (heq i)⟩, rfl, rfl⟩,
    simp only [← box.coe_eq_pi, ← box.face_lower, ← box.face_upper],
    have A := ((Hi.mono_set box.coe_subset_Icc).has_box_integral ⊥ rfl),
    have B := has_integral_bot_divergence_of_forall_has_deriv_within_at I f f' H,
    have Hd : ∀ i, differentiable_on ℝ (f i) I.Icc, from λ i x hx, ⟨_, H x hx i⟩,
    refine (A.unique B).trans (sum_congr rfl $ λ i hi, _),
    refine congr_arg2 has_sub.sub _ _,
    { have := continuous_on_face_Icc I (Hd i).continuous_on i _ (right_mem_Icc.2 (hle i)),
      have := (this.integrable_on_compact box.is_compact_Icc).mono_set box.coe_subset_Icc,
      exact (this.has_box_integral ⊥ rfl).integral_eq, apply_instance },
    { have := continuous_on_face_Icc I (Hd i).continuous_on i _ (left_mem_Icc.2 (hle i)),
      have := (this.integrable_on_compact box.is_compact_Icc).mono_set box.coe_subset_Icc,
      exact (this.has_box_integral ⊥ rfl).integral_eq, apply_instance } }
end

end measure_theory
