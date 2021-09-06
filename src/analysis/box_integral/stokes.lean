import analysis.box_integral.basic
import analysis.box_integral.partition.additive
import analysis.calculus.fderiv

open_locale classical big_operators nnreal ennreal topological_space
open continuous_linear_map (lsmul) filter set finset metric
noncomputable theory

universes u v
variables {ι : Type u} {E : Type v} [normed_group E] [normed_space ℝ E]

section

variables {α : Type*}

def pi_insert_one (i : ι) (x : α) (f : ({i}ᶜ : set ι) → α) (j : ι) : α :=
if h : j = i then x else f ⟨j, h⟩

@[simp] lemma pi_insert_one_same (i : ι) (x : α) (f : ({i}ᶜ : set ι) → α) :
  pi_insert_one i x f i = x :=
dif_pos rfl

lemma pi_insert_one_of_ne {i j : ι} (h : j ≠ i) (x : α) (f : ({i}ᶜ : set ι) → α) :
  pi_insert_one i x f j = f ⟨j, h⟩ :=
dif_neg h

lemma continuous_pi_insert_one [topological_space α] (i : ι) (x : α) :
  continuous (pi_insert_one i x) :=
begin
  refine continuous_pi (λ j, _),
  rcases eq_or_ne j i with rfl|hne,
  { simp only [pi_insert_one_same, continuous_const] },
  { simp only [pi_insert_one_of_ne hne, continuous_apply] }
end

lemma isometry_pi_insert_one [fintype ι] [pseudo_emetric_space α] (i : ι) (x : α) :
  isometry (pi_insert_one i x) :=
begin
  refine λ f g, eq_of_forall_ge_iff (λ c, _),
  rw [edist_pi_le_iff, edist_pi_le_iff, set_coe.forall],
  refine forall_congr (λ j, _),
  rcases eq_or_ne j i with rfl|hne,
  { simp },
  { simp [pi_insert_one_of_ne, hne], refl }
end

lemma le_pi_insert_one [preorder α] {i : ι} {x : α} {f g} :
  f ≤ pi_insert_one i x g ↔ f i ≤ x ∧ ∀ j (hj : j ≠ i), f j ≤ g ⟨j, hj⟩ :=
begin
  rw [pi.le_def, ← @and_forall_ne _ _ i, pi_insert_one_same],
  refine and_congr iff.rfl (forall_congr $ λ j, forall_congr $ λ hj, _),
  rw [pi_insert_one_of_ne hj]
end

lemma pi_insert_one_le [preorder α] {i : ι} {x : α} {f g} :
  pi_insert_one i x g ≤ f ↔ x ≤ f i ∧ ∀ j (hj : j ≠ i), g ⟨j, hj⟩ ≤ f j :=
@le_pi_insert_one ι (order_dual α) _ _ _ _ _

lemma pi_insert_one_mem_Icc [preorder α] {i : ι} {x : α} {f g₁ g₂} :
  pi_insert_one i x f ∈ Icc (g₁ : ι → α) g₂ ↔ x ∈ Icc (g₁ i) (g₂ i) ∧
    ∀ j (hj : j ≠ i), f ⟨j, hj⟩ ∈ Icc (g₁ j) (g₂ j) :=
begin
  dsimp only [Icc, mem_set_of_eq],
  simp only [forall_and_distrib, pi_insert_one_le, le_pi_insert_one, and_assoc, and.left_comm]
end

lemma pi_insert_one_sub_eq_single [add_group α] (i : ι) (x y : α) (f) :
  pi_insert_one i x f - pi_insert_one i y f = pi.single i (x - y) :=
function.eq_update_iff.2 ⟨by simp, λ j hj, by simp [pi_insert_one_of_ne hj]⟩

end

namespace box_integral

variables (I : box ι)

lemma maps_to_pi_insert_one_face_Icc (I : box ι) (i : ι) (x : ℝ)
  (hx : x ∈ Icc (I.lower i) (I.upper i)) :
  maps_to (pi_insert_one i x) (I.face i).Icc I.Icc :=
λ y hy, pi_insert_one_mem_Icc.2 ⟨hx, λ j hj, ⟨hy.1 ⟨j, hj⟩, hy.2 ⟨j, hj⟩⟩⟩

lemma continuous_on_face_Icc {X : Type*} [topological_space X]
  {f : (ι → ℝ) → X} (hf : continuous_on f I.Icc) (i : ι) (x : ℝ)
  (hx : x ∈ Icc (I.lower i) (I.upper i)) :
  continuous_on (λ y, f (pi_insert_one i x y)) (I.face i).Icc :=
hf.comp (continuous_pi_insert_one i x).continuous_on (maps_to_pi_insert_one_face_Icc _ _ _ hx)

variable [fintype ι]
open measure_theory

lemma norm_volume_sub_integral_face_upper_sub_lower_smul_le [complete_space E] {I : box ι}
  {f : (ι → ℝ) → E} {i : ι} {f' : (ι → ℝ) →L[ℝ] E} (hfc : continuous_on f I.Icc)
  {x : ι → ℝ} (hxI : x ∈ I.Icc) {a : E} {ε : ℝ} (h0 : 0 < ε)
  (hε : ∀ y ∈ I.Icc, ∥f y - a - f' (y - x)∥ ≤ ε * ∥y - x∥) {c : ℝ≥0} (hc : I.distortion ≤ c) :
  ∥(volume : measure (ι → ℝ)).to_box_additive I • (f' (pi.single i 1)) -
    (integral (I.face i) ⊥ (f ∘ pi_insert_one i (I.upper i))
      (volume : measure (({i}ᶜ : set ι) → ℝ)).to_box_additive.to_smul -
      integral (I.face i) ⊥ (f ∘ pi_insert_one i (I.lower i))
        (volume : measure (({i}ᶜ : set ι) → ℝ)).to_box_additive.to_smul)∥ ≤
    2 * ε * c * (volume : measure (ι → ℝ)).to_box_additive I :=
begin
  have Hl : I.lower i ∈ Icc (I.lower i) (I.upper i), from left_mem_Icc.2 (I.lower_le_upper i),
  have Hu : I.upper i ∈ Icc (I.lower i) (I.upper i), from right_mem_Icc.2 (I.lower_le_upper i),
  have Hi : ∀ x ∈ Icc (I.lower i) (I.upper i),
    @integrable ({i}ᶜ : set ι) E E _ _ _ _ _ (I.face i) ⊥ (f ∘ pi_insert_one i x)
      (volume : measure (({i}ᶜ : set ι) → ℝ)).to_box_additive.to_smul,
    from λ x hx, integrable_of_continuous_on (continuous_on_face_Icc _ hfc _ _ hx) volume,
  rw [← integral_sub (Hi _ Hu) (Hi _ Hl), ← box.volume_face_mul i, mul_smul,
    ← box_additive_map.to_smul_apply, ← integral_const,
    ← integral_sub (integrable_const _) ((Hi _ Hu).sub (Hi _ Hl)), measure.to_box_additive_apply],
  simp only [(∘), pi.sub_def, ← f'.map_smul, ← pi.single_smul'', smul_eq_mul, mul_one],
  have : ∀ y ∈ (I.face i).Icc, ∥f' (pi.single i (I.upper i - I.lower i)) -
    (f (pi_insert_one i (I.upper i) y) - f (pi_insert_one i (I.lower i) y))∥ ≤ 2 * ε * diam I.Icc,
  { intros y hy,
    set g := λ y, f y - a - f' (y - x) with hg,
    change ∀ y ∈ I.Icc, ∥g y∥ ≤ ε * ∥y - x∥ at hε,
    clear_value g, obtain rfl : f = λ y, a + f' (y - x) + g y, by simp [hg],
    convert_to ∥g (pi_insert_one i (I.lower i) y) - g (pi_insert_one i (I.upper i) y)∥ ≤ _,
    { congr' 1, simp only [← pi_insert_one_sub_eq_single i _ _ y, f'.map_sub], abel },
    { have : ∀ z ∈ Icc (I.lower i) (I.upper i), pi_insert_one i z y ∈ I.Icc,
        from λ z hz, maps_to_pi_insert_one_face_Icc _ _ _ hz hy,
      replace hε : ∀ y ∈ I.Icc, ∥g y∥ ≤ ε * diam I.Icc,
      { intros y hy,
        refine (hε y hy).trans (mul_le_mul_of_nonneg_left _ h0.le),
        rw ← dist_eq_norm,
        exact dist_le_diam_of_mem (is_compact_pi_Icc I.lower I.upper).bounded hy hxI },
      rw [two_mul, add_mul],
      exact norm_sub_le_of_le (hε _ (this _ Hl)) (hε _ (this _ Hu)) } },
  refine (norm_integral_le_of_le_const this volume).trans _,
  rw [mul_left_comm (volume _).to_real, mul_assoc (2 * ε), mul_left_comm (c : ℝ)],
  refine mul_le_mul_of_nonneg_left _ (mul_nonneg zero_le_two h0.le),
  refine mul_le_mul_of_nonneg_left _ ennreal.to_real_nonneg,
  exact (I.diam_Icc_le_distortion_mul i).trans
    (mul_le_mul_of_nonneg_right hc $ sub_nonneg.2 $ I.lower_le_upper i)
end

lemma has_integral_bot_divergence_of_forall_has_deriv_within_at [complete_space E]
  (f : ι → (ι → ℝ) → E) (f' : ι → (ι → ℝ) → (ι → ℝ) →L[ℝ] E)
  (H : ∀ (x ∈ I.Icc) i, has_fderiv_within_at (f i) (f' i x) I.Icc x) :
  @has_integral ι E E _ _ _ _ _ I ⊥ (λ x, ∑ i, f' i x (pi.single i 1))
    (volume : measure (ι → ℝ)).to_box_additive.to_smul
    (∑ i, ((@integral _ E E _ _ _ _ _ (I.face i) ⊥ (λ x, f i (pi_insert_one i (I.upper i) x))
      (volume : measure (({i}ᶜ : set ι) → ℝ)).to_box_additive.to_smul) -
      @integral _ E E _ _ _ _ _ (I.face i) ⊥ (λ x, f i (pi_insert_one i (I.lower i) x))
        (volume : measure (({i}ᶜ : set ι) → ℝ)).to_box_additive.to_smul)) :=
begin
  refine has_integral_sum (λ i hi, _), clear hi,
  have Hd : differentiable_on ℝ (f i) I.Icc, from λ x hx, ⟨_, H x hx i⟩,
  set fI : ℝ → box ({i}ᶜ : set ι) → E := λ y J,
    @integral _ E E _ _ _ _ _ J ⊥ (λ x, f i (pi_insert_one i y x))
        (volume : measure (({i}ᶜ : set ι) → ℝ)).to_box_additive.to_smul,
  set fb : Icc (I.lower i) (I.upper i) → (({i}ᶜ : set ι) : Type u) →ᵇᵃ[↑(I.face i)] E :=
    λ x, (integrable_of_continuous_on ⊥ (continuous_on_face_Icc I Hd.continuous_on i x x.2)
      volume).to_box_additive,
  set F : ι →ᵇᵃ[I] E := box_additive_map.upper_sub_lower I i fI fb (λ x hx J, rfl),
  change has_integral I ⊥ (λ x, f' i x (pi.single i 1)) _ (F I),
  refine has_integral_bot_of_forall_is_o
    ((volume : measure (ι → ℝ)).to_box_additive.restrict I le_top) F (λ c x hx ε ε0, _),
  rcases exists_pos_mul_lt ε0 (2 * c) with ⟨ε', ε'0, hlt⟩,
  rcases (nhds_within_has_basis nhds_basis_closed_ball _).mem_iff.1 ((H x hx i).def ε'0)
    with ⟨δ, δ0, Hδ⟩,
  refine ⟨δ, δ0, λ J hle hJδ hxJ hJc, _⟩,
  rw dist_eq_norm,
  refine (norm_volume_sub_integral_face_upper_sub_lower_smul_le
    (Hd.continuous_on.mono $ (@box.Icc ι).monotone hle) hxJ ε'0 (λ y hy, Hδ _) hJc).trans _,
  { exact ⟨hJδ hy, box.le_iff_Icc.1 hle hy⟩ },
  { rw mul_right_comm (2 : ℝ), exact mul_le_mul_of_nonneg_right hlt.le ennreal.to_real_nonneg }
end
   
end box_integral
