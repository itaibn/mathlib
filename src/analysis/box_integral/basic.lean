import analysis.box_integral.partition.filter

open_locale big_operators classical topological_space
open set function filter

noncomputable theory

namespace box_integral

variables {ι E F : Type*} [normed_group E] [normed_space ℝ E] [normed_group F] [normed_space ℝ F]
  [fintype ι] {I : box ι} {π : marked_partition I}

open marked_partition

def integral_sum (f : (ι → ℝ) → E) (vol : box ι → (E →L[ℝ] F))
  (π : marked_partition I) : F :=
∑ᶠ J ∈ π, vol J (f (π.mark J))

@[simp] lemma integral_sum_add (f g : (ι → ℝ) → E) (vol : box ι → (E →L[ℝ] F))
  (π : marked_partition I) :
  integral_sum (f + g) vol π = integral_sum f vol π + integral_sum g vol π :=
begin
  simp only [integral_sum, pi.add_apply, (vol _).map_add],
  exact finsum_mem_add_distrib π.finite_boxes
end

@[simp] lemma integral_sum_neg (f : (ι → ℝ) → E) (vol : box ι → (E →L[ℝ] F))
  (π : marked_partition I) :
  integral_sum (-f) vol π = -integral_sum f vol π :=
by simp only [integral_sum, pi.neg_apply, (vol _).map_neg, finsum_neg_distrib]

@[simp] lemma integral_sum_smul (c : ℝ) (f : (ι → ℝ) → E) (vol : box ι → (E →L[ℝ] F))
  (π : marked_partition I) :
  integral_sum (c • f) vol π = c • integral_sum f vol π :=
by simp only [integral_sum, smul_finsum, pi.smul_apply, continuous_linear_map.map_smul]

def has_integral (I : box ι) (l : filter (marked_partition I)) (vol : box ι → (E →L[ℝ] F))
  (f : (ι → ℝ) → E) (y : F) : Prop :=
tendsto (integral_sum f vol) l (𝓝 y)

def integrable (I : box ι) (l : filter (marked_partition I)) (vol : box ι → (E →L[ℝ] F))
  (f : (ι → ℝ) → E) : Prop :=
∃ y, has_integral I l vol f y

def integral (I : box ι) (l : filter (marked_partition I)) (vol : box ι → (E →L[ℝ] F))
  (f : (ι → ℝ) → E) : F :=
if h : integrable I l vol f then classical.some h else 0

variables {l : filter (marked_partition I)}
  {f g : (ι → ℝ) → E} {vol : box ι → (E →L[ℝ] F)} {y y' : F}

lemma integrable_iff_cauchy [complete_space F] [ne_bot l] :
  integrable I l vol f ↔ cauchy (l.map (integral_sum f vol)) :=
cauchy_map_iff_exists_tendsto.symm

lemma has_integral.R_to_H (h : has_integral I Riemann vol f y) :
  has_integral I Henstock vol f y :=
h.mono_left Henstock_le_Riemann

lemma has_integral.MS_to_H (h : has_integral I McShane vol f y) :
  has_integral I Henstock vol f y :=
h.mono_left Henstock_le_McShane

lemma integrable.has_integral (h : integrable I l vol f) :
  has_integral I l vol f (integral I l vol f) :=
by { rw [integral, dif_pos h], exact classical.some_spec h }

lemma has_integral.unique [ne_bot l] (h : has_integral I l f vol y)
  (h' : has_integral I l f vol y') :
  y = y' :=
tendsto_nhds_unique h h'

lemma has_integral.integrable (h : has_integral I l f vol y) : integrable I l f vol := ⟨_, h⟩

lemma has_integral.integral_eq [ne_bot l] (h : has_integral I l f vol y) :
  integral I l f vol = y :=
h.integrable.has_integral.unique h

lemma has_integral.add (h : has_integral I l f vol y) (h' : has_integral I l g vol y') :
  has_integral I l (f + g) vol (y + y') :=
by simpa only [has_integral, ← integral_sum_add] using h.add h'

lemma integrable.add (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integrable I l (f + g) vol :=
(hf.has_integral.add hg.has_integral).integrable

lemma integral_add [ne_bot l] (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integral I l (f + g) vol = integral I l f vol + integral I l g vol :=
(hf.has_integral.add hg.has_integral).integral_eq

lemma has_integral.neg (hf : has_integral I l f vol y) : has_integral I l (-f) vol (-y) :=
by simpa only [has_integral, ← integral_sum_neg] using hf.neg

lemma integrable.neg (hf : integrable I l f vol) : integrable I l (-f) vol :=
hf.has_integral.neg.integrable

lemma integrable.of_neg (hf : integrable I l (-f) vol) : integrable I l f vol := neg_neg f ▸ hf.neg

@[simp] lemma integrable_neg : integrable I l (-f) vol ↔ integrable I l f vol :=
⟨λ h, h.of_neg, λ h, h.neg⟩

@[simp] lemma integral_neg [ne_bot l] : integral I l (-f) vol = -integral I l f vol :=
if h : integrable I l f vol then h.has_integral.neg.integral_eq
else by rw [integral, integral, dif_neg h, dif_neg (mt integrable.of_neg h), neg_zero]

lemma has_integral.sub (h : has_integral I l f vol y) (h' : has_integral I l g vol y') :
  has_integral I l (f - g) vol (y - y') :=
by simpa only [sub_eq_add_neg] using h.add h'.neg

lemma integrable.sub (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integrable I l (f - g) vol :=
(hf.has_integral.sub hg.has_integral).integrable

lemma integral_sub [ne_bot l] (hf : integrable I l f vol) (hg : integrable I l g vol) :
  integral I l (f - g) vol = integral I l f vol - integral I l g vol :=
(hf.has_integral.sub hg.has_integral).integral_eq

lemma has_integral_zero : has_integral I l (λ _, (0:E)) vol 0 :=
by { dunfold has_integral, convert tendsto_const_nhds, ext π, simp [integral_sum] }

lemma integrable_zero : integrable I l (λ _, (0:E)) vol := ⟨0, has_integral_zero⟩

@[simp] lemma integral_zero [ne_bot l] : integral I l (λ _, (0:E)) vol = 0 :=
has_integral_zero.integral_eq

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

@[simp] lemma integral_smul [ne_bot l] (c : ℝ) :
  integral I l (λ x, c • f x) vol = c • integral I l f vol :=
begin
  rcases em (c = 0) with rfl | hc, { simp },
  by_cases hf : integrable I l f vol,
  { exact (hf.has_integral.smul c).integral_eq },
  { have : ¬integrable I l (λ x, c • f x) vol, from mt (λ h, h.of_smul hc) hf,
    rw [integral, integral, dif_neg hf, dif_neg this, smul_zero] }
end

lemma Riemann_integrable_of_continuous_on (h : continuous_on f (Icc I.lower I.upper))

end box_integral
