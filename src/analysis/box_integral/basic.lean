import analysis.box_integral.partition.filter
import analysis.box_integral.partition.additive
import analysis.normed_space.operator_norm
import topology.uniform_space.compact_separated

open_locale big_operators classical topological_space nnreal filter
open set function filter continuous_linear_map (lsmul)

noncomputable theory

namespace box_integral

variables {ι E F : Type*} [normed_group E] [normed_space ℝ E] [normed_group F] [normed_space ℝ F]
  {I : box ι} {π : marked_partition I}

namespace partition

def union {I : box ι} {i : ι} {x : ℝ} {hx : x ∈ Ioo (I.lower i) (I.upper i)}
  (π₁ : partition (I.split_edge_lower i x hx))
  (π₂ : partition (I.split_edge_upper i x hx)) :
  partition I :=
{ boxes := π₁.boxes ∪ π₂.boxes,
  finite_boxes := π₁.finite_boxes.union π₂.finite_boxes,
  bUnion_boxes_coe := by rw [bUnion_union, bUnion_boxes_coe, bUnion_boxes_coe,
    box.union_coe_split_edge],
  pairwise_disjoint :=
    begin
      rintro J₁ (hJ₁|hJ₁) J₂ (hJ₂|hJ₂) Hne,
      exacts [π₁.pairwise_disjoint J₁ hJ₁ J₂ hJ₂ Hne,
        (I.disjoint_split_edge i x hx).mono (π₁.le_of_mem hJ₁) (π₂.le_of_mem hJ₂),
        (I.disjoint_split_edge i x hx).symm.mono (π₂.le_of_mem hJ₁) (π₁.le_of_mem hJ₂),
        π₂.pairwise_disjoint J₁ hJ₁ J₂ hJ₂ Hne]
    end }

end partition

namespace marked_partition

def union {I : box ι} {i : ι} {x : ℝ} {hx : x ∈ Ioo (I.lower i) (I.upper i)}
  (π₁ : marked_partition (I.split_edge_lower i x hx))
  (π₂ : marked_partition (I.split_edge_upper i x hx)) :
  marked_partition I :=
{ to_partition := π₁.to_partition.union π₂.to_partition,
  mark := λ J, if J ∈ π₁ then π₁.mark J else π₂.mark J,
  mark_mem_Icc := λ J,
    begin
      split_ifs,
      exacts [box.le_iff_Icc.1 (I.split_edge_lower_le i x hx) (π₁.mark_mem_Icc _),
        box.le_iff_Icc.1 (I.split_edge_upper_le i x hx) (π₂.mark_mem_Icc _)]
    end }

lemma is_subordinate.union [fintype ι] {I : box ι} {i : ι} {x : ℝ}
  {hx : x ∈ Ioo (I.lower i) (I.upper i)}
  {π₁ : marked_partition (I.split_edge_lower i x hx)}
  {π₂ : marked_partition (I.split_edge_upper i x hx)} {r : (ι → ℝ) → ℝ}
  (h₁ : is_subordinate π₁ r) (h₂ : is_subordinate π₂ r) :
  is_subordinate (π₁.union π₂) r :=
begin
  intros J hJ,
  by_cases hJ₁ : J ∈ π₁,
  { simp only [union, if_pos hJ₁, h₁ J hJ₁] },
  { simp only [union, if_neg hJ₁, h₂ J (hJ.resolve_left hJ₁)] }
end

lemma is_Henstock.union [fintype ι] {I : box ι} {i : ι} {x : ℝ}
  {hx : x ∈ Ioo (I.lower i) (I.upper i)}
  {π₁ : marked_partition (I.split_edge_lower i x hx)}
  {π₂ : marked_partition (I.split_edge_upper i x hx)}
  (h₁ : is_Henstock π₁) (h₂ : is_Henstock π₂) :
  is_Henstock (π₁.union π₂) :=
begin
  intros J hJ,
  by_cases hJ₁ : J ∈ π₁,
  { simp only [union, if_pos hJ₁, h₁ J hJ₁] },
  { simp only [union, if_neg hJ₁, h₂ J (hJ.resolve_left hJ₁)] }
end

lemma tendsto_union_Henstock [fintype ι] {I : box ι} {i : ι} {x : ℝ}
  (hx : x ∈ Ioo (I.lower i) (I.upper i)) :
  tendsto (λ π : marked_partition (I.split_edge_lower i x hx) ×
    marked_partition (I.split_edge_upper i x hx), π.1.union π.2)
    (Henstock ×ᶠ Henstock) Henstock :=
begin
  refine ((has_basis_Henstock.prod has_basis_Henstock).tendsto_iff has_basis_Henstock).2 _,
  refine λ r hr, ⟨(r, r), ⟨λ x hx, hr x _, λ x hx, hr x _⟩, _⟩,
  { exact box.le_iff_Icc.1 (I.split_edge_lower_le _ _ _) hx },
  { exact box.le_iff_Icc.1 (I.split_edge_upper_le _ _ _) hx },
  { rintro ⟨π₁, π₂⟩ ⟨⟨h₁r, h₁⟩, ⟨h₂r, h₂⟩⟩,
    exact ⟨h₁r.union h₂r, h₁.union h₂⟩ }
end

lemma tendsto_union_Henstock'_aux [fintype ι] {I : box ι} {i : ι} {x : ℝ}
  (hx : x ∈ Ioo (I.lower i) (I.upper i)) (c : ℝ≥0) :
  tendsto (λ π : marked_partition (I.split_edge_lower i x hx) ×
    marked_partition (I.split_edge_upper i x hx), π.1.union π.2)
    (Henstock'_aux c ×ᶠ Henstock'_aux c) (Henstock'_aux c) :=
begin
  rw [Henstock'_aux, Henstock'_aux, ← prod_inf_prod, prod_principal_principal],
  refine (tendsto_union_Henstock hx).inf (tendsto_principal_principal.2 _),
  rintro ⟨π₁, π₂⟩ ⟨h₁, h₂⟩ J (hJ|hJ),
  exacts [h₁ J hJ, h₂ J hJ]
end

lemma tendsto_union_Riemann [fintype ι] {I : box ι} {i : ι} {x : ℝ}
  (hx : x ∈ Ioo (I.lower i) (I.upper i)) :
  tendsto (λ π : marked_partition (I.split_edge_lower i x hx) ×
    marked_partition (I.split_edge_upper i x hx), π.1.union π.2)
    (Riemann ×ᶠ Riemann) Riemann :=
begin
  refine ((has_basis_Riemann.prod has_basis_Riemann).tendsto_iff has_basis_Riemann).2 _,
  refine λ r hr, ⟨(r, r), ⟨hr, hr⟩, _⟩,
  rintro ⟨π₁, π₂⟩ ⟨⟨h₁r, h₁⟩, ⟨h₂r, h₂⟩⟩,
  exact ⟨h₁r.union h₂r, h₁.union h₂⟩
end

end marked_partition

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

lemma has_integral.tendsto (h : has_integral I l vol f y) :
  tendsto (integral_sum f vol) l (𝓝 y) := h

lemma integrable_iff_cauchy [complete_space F] [ne_bot l] :
  integrable I l vol f ↔ cauchy (l.map (integral_sum f vol)) :=
cauchy_map_iff_exists_tendsto.symm

lemma integrable_iff_ex_basis [complete_space F] [ne_bot l] {ι' : Sort*} {p : ι' → Prop}
  {s : ι' → set (marked_partition I)} (h : has_basis l p s) :
  integrable I l vol f ↔
    ∀ ε > 0, ∃ j (hi : p j), ∀ π₁ π₂ ∈ s j, ∥integral_sum f vol π₁ - integral_sum f vol π₂∥ ≤ ε :=
by simp only [integrable_iff_cauchy, cauchy_map_iff, ‹ne_bot l›, true_and,
  h.prod_self.tendsto_iff metric.uniformity_basis_dist_le, prod.forall, set.mem_prod, and_imp,
  mem_set_of_eq, dist_eq_norm, gt_iff_lt]

lemma has_integral.R'_to_R [fintype ι] (h : has_integral I Riemann' vol f y) :
  has_integral I Riemann vol f y :=
h.mono_left Riemann_le_Riemann'

lemma has_integral.R_to_H [fintype ι] (h : has_integral I Riemann vol f y) :
  has_integral I Henstock vol f y :=
h.mono_left Henstock_le_Riemann

lemma has_integral.R'_to_MS [fintype ι] (h : has_integral I Riemann' vol f y) :
  has_integral I McShane vol f y :=
h.mono_left McShane_le_Riemann'

lemma has_integral.MS_to_H [fintype ι] (h : has_integral I McShane vol f y) :
  has_integral I Henstock vol f y :=
h.mono_left Henstock_le_McShane

lemma has_integral.H_to_H' [fintype ι] (h : has_integral I Henstock vol f y) :
  has_integral I Henstock' vol f y :=
h.mono_left Henstock'_le_Henstock

lemma integrable.has_integral (h : integrable I l vol f) :
  has_integral I l vol f (integral I l vol f) :=
by { rw [integral, dif_pos h], exact classical.some_spec h }

lemma integrable.mono {l'} (h : integrable I l vol f) (hle : l' ≤ l) : integrable I l' vol f :=
⟨_, h.has_integral.mono_left hle⟩

lemma integrable.R'_to_R [fintype ι] (h : integrable I Riemann' vol f) :
  integrable I Riemann vol f :=
h.mono Riemann_le_Riemann'

lemma integrable.R_to_H [fintype ι] (h : integrable I Riemann vol f) :
  integrable I Henstock vol f :=
h.mono Henstock_le_Riemann

lemma integrable.R'_to_MS [fintype ι] (h : integrable I Riemann' vol f) :
  integrable I McShane vol f :=
h.mono McShane_le_Riemann'

lemma integrable.MS_to_H [fintype ι] (h : integrable I McShane vol f) :
  integrable I Henstock vol f :=
h.mono Henstock_le_McShane

lemma integrable.H_to_H' [fintype ι] (h : integrable I Henstock vol f) :
  integrable I Henstock' vol f :=
h.mono Henstock'_le_Henstock

lemma has_integral.unique [ne_bot l] (h : has_integral I l vol f y)
  (h' : has_integral I l vol f y') :
  y = y' :=
tendsto_nhds_unique h h'

lemma has_integral.integrable (h : has_integral I l vol f y) : integrable I l vol f := ⟨_, h⟩

lemma has_integral.integral_eq [ne_bot l] (h : has_integral I l vol f y) :
  integral I l vol f = y :=
h.integrable.has_integral.unique h

lemma has_integral.add (h : has_integral I l vol f y) (h' : has_integral I l vol g y') :
  has_integral I l vol (f + g) (y + y') :=
by simpa only [has_integral, ← integral_sum_add] using h.add h'

lemma integrable.add (hf : integrable I l vol f) (hg : integrable I l vol g) :
  integrable I l vol (f + g) :=
(hf.has_integral.add hg.has_integral).integrable

lemma integral_add [ne_bot l] (hf : integrable I l vol f) (hg : integrable I l vol g) :
  integral I l vol (f + g) = integral I l vol f + integral I l vol g :=
(hf.has_integral.add hg.has_integral).integral_eq

lemma has_integral.neg (hf : has_integral I l vol f y) : has_integral I l vol (-f) (-y) :=
by simpa only [has_integral, ← integral_sum_neg] using hf.neg

lemma integrable.neg (hf : integrable I l vol f) : integrable I l vol (-f) :=
hf.has_integral.neg.integrable

lemma integrable.of_neg (hf : integrable I l vol (-f)) : integrable I l vol f := neg_neg f ▸ hf.neg

@[simp] lemma integrable_neg : integrable I l vol (-f) ↔ integrable I l vol f :=
⟨λ h, h.of_neg, λ h, h.neg⟩

@[simp] lemma integral_neg [ne_bot l] : integral I l vol (-f) = -integral I l vol f :=
if h : integrable I l vol f then h.has_integral.neg.integral_eq
else by rw [integral, integral, dif_neg h, dif_neg (mt integrable.of_neg h), neg_zero]

lemma has_integral.sub (h : has_integral I l vol f y) (h' : has_integral I l vol g y') :
  has_integral I l vol (f - g) (y - y') :=
by simpa only [sub_eq_add_neg] using h.add h'.neg

lemma integrable.sub (hf : integrable I l vol f) (hg : integrable I l vol g) :
  integrable I l vol (f - g) :=
(hf.has_integral.sub hg.has_integral).integrable

lemma integral_sub [ne_bot l] (hf : integrable I l vol f) (hg : integrable I l vol g) :
  integral I l vol (f - g) = integral I l vol f - integral I l vol g :=
(hf.has_integral.sub hg.has_integral).integral_eq

lemma has_integral_zero : has_integral I l vol (λ _, (0:E)) 0 :=
by { dunfold has_integral, convert tendsto_const_nhds, ext π, simp [integral_sum] }

lemma integrable_zero : integrable I l vol (λ _, (0:E)) := ⟨0, has_integral_zero⟩

@[simp] lemma integral_zero [ne_bot l] : integral I l vol (λ _, (0:E)) = 0 :=
has_integral_zero.integral_eq

lemma has_integral_sum {α : Type*} {s : finset α} {f : α → (ι → ℝ) → E} {g : α → F}
  (h : ∀ i ∈ s, has_integral I l vol (f i) (g i)) :
  has_integral I l vol (λ x, ∑ i in s, f i x) (∑ i in s, g i) :=
begin
  induction s using finset.induction_on with a s ha ihs, { simp [has_integral_zero] },
  simp only [finset.sum_insert ha], rw finset.forall_mem_insert at h,
  exact h.1.add (ihs h.2)
end

lemma has_integral.smul (hf : has_integral I l vol f y) (c : ℝ) :
  has_integral I l vol (c • f) (c • y) :=
by simpa only [has_integral, ← integral_sum_smul]
  using (tendsto_const_nhds : tendsto _ _ (𝓝 c)).smul hf

lemma integrable.smul (hf : integrable I l vol f) (c : ℝ) :
  integrable I l vol (c • f) :=
(hf.has_integral.smul c).integrable

lemma integrable.of_smul {c : ℝ} (hf : integrable I l vol (c • f)) (hc : c ≠ 0) :
  integrable I l vol f :=
by { convert hf.smul c⁻¹, ext x, simp only [pi.smul_apply, inv_smul_smul' hc] }

@[simp] lemma integral_smul [ne_bot l] (c : ℝ) :
  integral I l vol (λ x, c • f x) = c • integral I l vol f :=
begin
  rcases eq_or_ne c 0 with rfl | hc, { simp },
  by_cases hf : integrable I l vol f,
  { exact (hf.has_integral.smul c).integral_eq },
  { have : ¬integrable I l vol (λ x, c • f x), from mt (λ h, h.of_smul hc) hf,
    rw [integral, integral, dif_neg hf, dif_neg this, smul_zero] }
end

lemma integral_sum_bUnion_unmarked [fintype ι] (π : marked_partition I) (πi : Π J ∈ π, partition J)
  (hvol : box_additive_on vol I):
  integral_sum f vol (π.bUnion_unmarked πi) = integral_sum f vol π :=
begin
  refine (π.to_partition.finsum_mem_bUnion πi _).trans _,
  refine finsum_congr (λ J, finsum_congr $ λ hJ, _),
  have : ∀ x, box_additive_on (λ J', vol J' x) J,
    from λ x, (hvol.add_monoid_hom_comp (continuous_linear_map.apply ℝ F x)
      .to_linear_map.to_add_monoid_hom).restrict (π.to_partition.le_of_mem hJ),
  calc ∑ᶠ J' ∈ πi J hJ, vol J' (f (π.mark (π.to_partition.bUnion_index πi J'))) =
    ∑ᶠ J' ∈ πi J hJ, vol J' (f (π.mark J)) :
      finsum_mem_congr rfl (λ J' (hJ' : J' ∈ πi J hJ), by rw partition.bUnion_index_of_mem _ _ hJ')
  ... = vol J (f (π.mark J)) : (this _).finsum_mem_partition _
end

lemma integral_sum_inf_unmarked [fintype ι] (π : marked_partition I) (π' : partition I)
  (hvol : box_additive_on vol I):
  integral_sum f vol (π.inf_unmarked π') = integral_sum f vol π :=
integral_sum_bUnion_unmarked π _ hvol

@[simp] lemma integral_sum_union {i : ι} {x : ℝ} {hx : x ∈ Ioo (I.lower i) (I.upper i)}
  (π₁ : marked_partition (I.split_edge_lower i x hx))
  (π₂ : marked_partition (I.split_edge_upper i x hx)) :
  integral_sum f vol (π₁.union π₂) = integral_sum f vol π₁ + integral_sum f vol π₂ :=
begin
  have : disjoint π₁.boxes π₂.boxes,
  { rintro J ⟨h₁, h₂⟩,
    refine (π₁.to_partition.le_of_mem h₁ J.upper_mem i).2.not_lt _,
    simpa using (π₂.to_partition.le_of_mem h₂ J.upper_mem i).1 },
  simp only [integral_sum],
  refine (finsum_mem_union this π₁.finite_boxes π₂.finite_boxes).trans _,
  refine congr_arg2 (+) (finsum_mem_congr rfl $ λ J hJ, _) (finsum_mem_congr rfl $ λ J hJ, _);
    congr' 2,
  exacts [if_pos hJ, if_neg (λ h, this ⟨h, hJ⟩)]
end

lemma integral_sum_sub_partitions [fintype ι] (π₁ π₂ : marked_partition I)
  (hvol : box_additive_on vol I) :
  integral_sum f vol π₁ - integral_sum f vol π₂ =
    ∑ᶠ J ∈ π₁.to_partition ⊓ π₂.to_partition,
      (vol J (f $ (π₁.inf_unmarked π₂.to_partition).mark J) -
        vol J (f $ (π₂.inf_unmarked π₁.to_partition).mark J)) :=
begin
  erw [← integral_sum_inf_unmarked π₁ π₂.to_partition hvol,
    ← integral_sum_inf_unmarked π₂ π₁.to_partition hvol, integral_sum, integral_sum,
    finsum_mem_sub_distrib (partition.finite_boxes _)],
  congr' 1,
  rw inf_comm, refl
end

lemma has_integral_const [fintype ι] (hvol : box_additive_on vol I) (c : E) :
  has_integral I l vol (λ _, c) (vol I c) :=
begin
  refine tendsto_const_nhds.congr (λ π, _),
  rw [integral_sum, eq_comm],
  refine box_additive_on.finsum_mem_partition _ π.to_partition,
  exact hvol.add_monoid_hom_comp (continuous_linear_map.apply ℝ F c).to_linear_map.to_add_monoid_hom
end

lemma integral_const [fintype ι] [ne_bot l] (hvol : box_additive_on vol I) (c : E) :
  integral I l vol (λ _, c) = vol I c :=
(has_integral_const hvol c).integral_eq

lemma integrable_const [fintype ι] (hvol : box_additive_on vol I) (c : E) :
  integrable I l vol (λ _, c) :=
⟨_, has_integral_const hvol c⟩

def volume [fintype ι] (I : box ι) : E →L[ℝ] E := lsmul ℝ ℝ I.volume

@[simp] lemma volume_apply [fintype ι] (I : box ι) (x : E) : volume I x = I.volume • x := rfl

lemma box_additive_on_volume [fintype ι] (I : box ι) :
  box_additive_on (volume : box ι → E →L[ℝ] E) I :=
(box_additive_on_box_volume I).add_monoid_hom_comp
      (lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E).to_linear_map.to_add_monoid_hom

lemma norm_integral_le_of_le_const [fintype ι] [ne_bot l] {c : ℝ} (hc : ∀ x ∈ I.Icc, ∥f x∥ ≤ c) :
  ∥integral I l volume f∥ ≤ I.volume * c :=
begin
  have h0 : 0 ≤ c, from (norm_nonneg _).trans (hc I.upper I.upper_mem_Icc),
  by_cases hf : integrable I l volume f,
  { refine le_of_tendsto' hf.has_integral.norm (λ π, _),
    erw [integral_sum, π.to_partition.finsum_eq_sum],
    rw [← (box_additive_on_box_volume I).finsum_mem_partition π.to_partition,
      partition.finsum_eq_sum, finset.sum_mul],
    refine norm_sum_le_of_le _ (λ J hJ, _), rw finite.mem_to_finset at hJ,
    rw [volume_apply, norm_smul, real.norm_eq_abs, abs_of_pos J.volume_pos,
      mul_le_mul_left J.volume_pos],
    exact hc _ (π.mark_mem_Icc _) },
  { rw [integral, dif_neg hf, norm_zero],
    exact mul_nonneg I.volume_pos.le h0 }
end

lemma box_additive_on_integral_Riemann [fintype ι]
  (H : ∀ J ≤ I, integrable J Riemann volume f) :
  box_additive_on (λ J, integral J Riemann volume f) I :=
begin
  intros J hJ i x hx, simp only,
  have A := (H J hJ).has_integral.tendsto.comp (tendsto_union_Riemann hx),
  simp only [(∘), integral_sum_union] at A,
  have B := ((H (J.split_edge_lower i x hx) _).has_integral.tendsto.comp tendsto_fst).add
    ((H (J.split_edge_upper i x hx) _).has_integral.tendsto.comp tendsto_snd),
  exacts [tendsto_nhds_unique B A, (J.split_edge_lower_le _ _ _).trans hJ,
    (J.split_edge_upper_le _ _ _).trans hJ]
end

lemma box_additive_on_integral_Henstock [fintype ι]
  (H : ∀ J ≤ I, integrable J Henstock volume f) :
  box_additive_on (λ J, integral J Henstock volume f) I :=
begin
  intros J hJ i x hx,
  have A := (H J hJ).has_integral.tendsto.comp (tendsto_union_Henstock hx),
  simp only [(∘), integral_sum_union] at A,
  have B := ((H (J.split_edge_lower i x hx) _).has_integral.tendsto.comp tendsto_fst).add
    ((H (J.split_edge_upper i x hx) _).has_integral.tendsto.comp tendsto_snd),
  exacts [tendsto_nhds_unique B A, (J.split_edge_lower_le _ _ _).trans hJ,
    (J.split_edge_upper_le _ _ _).trans hJ]
end

lemma box_additive_on_integral_Henstock' [fintype ι]
  (H : ∀ J ≤ I, integrable J Henstock' volume f) :
  box_additive_on (λ J, integral J Henstock' volume f) I :=
begin
  intros J hJ i x hx,
  set c := max (J.split_edge_lower i x hx).distortion (J.split_edge_upper i x hx).distortion,
  haveI : (Henstock'_aux c).ne_bot := Henstock'_aux_ne_bot (le_max_left _ _),
  haveI : (Henstock'_aux c).ne_bot := Henstock'_aux_ne_bot (le_max_right _ _),
  replace H : ∀ J ≤ I, tendsto (integral_sum f volume) (Henstock'_aux c)
    (𝓝 (integral J Henstock' volume f)) := λ J hJ, tendsto_supr.1 ((H J hJ).has_integral.tendsto) c,
  have A := (H J hJ).comp (tendsto_union_Henstock'_aux hx c),
  simp only [(∘), integral_sum_union] at A,
  have B := H _ ((J.split_edge_lower_le _ _ hx).trans hJ),
  have C := H _ ((J.split_edge_upper_le _ _ hx).trans hJ),
  exact tendsto_nhds_unique ((B.comp tendsto_fst).add (C.comp tendsto_snd)) A
end

lemma Riemann'_integrable_of_continuous_on [fintype ι] [complete_space E]
  {I : box ι} {f : (ι → ℝ) → E} (hc : continuous_on f I.Icc) :
  integrable I Riemann' volume f :=
begin
  have huc := (is_compact_pi_Icc I.lower I.upper).uniform_continuous_on_of_continuous hc,
  rw metric.uniform_continuous_on_iff_le at huc,
  refine (integrable_iff_ex_basis has_basis_Riemann').2 (λ ε ε0, _),
  rcases huc (ε / I.volume) (div_pos ε0 I.volume_pos) with ⟨δ, δ0 : 0 < δ, Hδ⟩,
  use [δ / 2, half_pos δ0],
  rintros π₁ π₂ h₁ h₂,
  simp_rw [integral_sum_sub_partitions _ _ (box_additive_on_volume I),
    ← continuous_linear_map.map_sub, partition.finsum_eq_sum, volume_apply],
  have : ∀ J ∈ (π₁.to_partition ⊓ π₂.to_partition).finite_boxes.to_finset,
    ∥(J : _).volume • (f ((π₁.inf_unmarked π₂.to_partition).mark J) -
      f ((π₂.inf_unmarked π₁.to_partition).mark J))∥ ≤ J.volume * (ε / I.volume),
  { intros J hJ,
    rw [finite.mem_to_finset] at hJ,
    rw [norm_smul, real.norm_eq_abs, abs_of_pos J.volume_pos, mul_le_mul_left J.volume_pos,
      ← dist_eq_norm],
    refine Hδ _ _ (marked_partition.mark_mem_Icc _ _) (marked_partition.mark_mem_Icc _ _) _,
    rw [← add_halves δ],
    refine (dist_triangle_left _ _ J.upper).trans (add_le_add (h₁ _ _ _) (h₂ _ _ _)),
    { apply partition.bUnion_index_mem },
    { exact (@box.Icc ι).monotone (partition.le_bUnion_index _ hJ) J.upper_mem_Icc },
    { apply partition.bUnion_index_mem },
    { rw inf_comm at hJ,
      exact (@box.Icc ι).monotone (partition.le_bUnion_index _ hJ) J.upper_mem_Icc } },
  refine (norm_sum_le_of_le _ this).trans _,
  rw [← finset.sum_mul, ← partition.finsum_eq_sum,
    (box_additive_on_box_volume I).finsum_mem_partition, mul_div_cancel' _ I.volume_pos.ne']
end

lemma Henstock_integrable_of_continuous_on [fintype ι] [complete_space E]
  {I : box ι} {f : (ι → ℝ) → E} (hc : continuous_on f I.Icc) :
  integrable I Henstock volume f :=
(Riemann'_integrable_of_continuous_on hc).R'_to_MS.MS_to_H

lemma Henstock'_integrable_of_continuous_on [fintype ι] [complete_space E]
  {I : box ι} {f : (ι → ℝ) → E} (hc : continuous_on f I.Icc) :
  integrable I Henstock' volume f :=
(Henstock_integrable_of_continuous_on hc).H_to_H'

lemma has_integral_McShane_inf_principal_of_forall_is_o [fintype ι] (B : box ι → ℝ)
  (HB : box_additive_on B I) (g : box ι → F) (hg : box_additive_on g I) (p : (ι → ℝ) → box ι → Prop)
  (H : ∀ (x ∈ I.Icc) (ε > 0), ∃ δ > 0, ∀ J ≤ I, J.Icc ⊆ metric.closed_ball x δ → p x J →
    dist (vol J (f x)) (g J) ≤ ε * B J) :
  has_integral I (McShane ⊓ 𝓟 {π | ∀ J ∈ π, p (π.mark J) J}) vol f (g I) :=
begin
  refine ((has_basis_McShane.inf_principal _).tendsto_iff metric.nhds_basis_closed_ball).2 _,
  intros ε ε0,
  choose! δ δ0 Hδε using H, simp only [dist_eq_norm] at Hδε,
  have Hpos : 0 < max (B I) 1, from lt_max_iff.2 (or.inr zero_lt_one),
  refine ⟨λ x, δ x (ε / max (B I) 1), λ x hx, δ0 x hx _ (div_pos ε0 Hpos), _⟩,
  rintro π ⟨hπδ, hπp⟩, rw mem_set_of_eq at hπδ hπp,
  erw [metric.mem_closed_ball, ← hg.finsum_mem_partition π.to_partition, dist_eq_norm, integral_sum,
   π.to_partition.finsum_eq_sum, π.to_partition.finsum_eq_sum, ← finset.sum_sub_distrib],
  have : ∀ J ∈ π.finite_boxes.to_finset, ∥vol J (f $ π.mark J) - g J∥ ≤ ε / max (B I) 1 * B J,
  { intros J hJ,
    rw finite.mem_to_finset at hJ,
    exact Hδε _ (π.mark_mem_Icc _) _ (div_pos ε0 Hpos) _ (π.to_partition.le_of_mem hJ) (hπδ J hJ)
      (hπp _ hJ) },
  refine (norm_sum_le_of_le _ this).trans _,
  rw [← finset.mul_sum, ← π.to_partition.finsum_eq_sum, HB.finsum_mem_partition],
  rw [div_mul_eq_mul_div, div_le_iff Hpos],
  exact mul_le_mul_of_nonneg_left (le_max_left _ _) ε0.le
end

lemma has_integral_Henstock'_of_forall_is_o [fintype ι] (B : box ι → ℝ) (HB : box_additive_on B I)
  (g : box ι → F) (hg : box_additive_on g I)
  (H : ∀ (c : ℝ≥0) (x ∈ I.Icc) (ε > 0), ∃ δ > 0, ∀ J ≤ I, J.Icc ⊆ metric.closed_ball x δ →
    x ∈ J.Icc → J.distortion ≤ c → dist (vol J (f x)) (g J) ≤ ε * B J) :
  has_integral I Henstock' vol f (g I) :=
begin
  rw [Henstock'_def, has_integral, tendsto_supr],
  intro c, rw ← has_integral,
  convert has_integral_McShane_inf_principal_of_forall_is_o B HB g hg
    (λ x J, x ∈ J.Icc ∧ J.distortion ≤ c) _,
  simpa only [and_imp] using H c
end

end box_integral
