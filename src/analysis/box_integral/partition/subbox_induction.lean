import analysis.box_integral.partition.marked
import analysis.specific_limits

open set function filter emetric
open_locale classical topological_space filter ennreal
noncomputable theory

namespace box_integral

variables {ι : Type*}

namespace box

variables {I : box ι}

def split_center_box (I : box ι) (s : set ι) : box ι :=
{ lower := s.piecewise (λ i, (I.lower i + I.upper i) / 2) I.lower,
  upper := s.piecewise I.upper (λ i, (I.lower i + I.upper i) / 2),
  lower_lt_upper := λ i, by { dunfold set.piecewise, split_ifs;
    simp only [left_lt_add_div_two, add_div_two_lt_right, I.lower_lt_upper] } }

lemma mem_split_center_box {s : set ι} {y : ι → ℝ} :
  y ∈ I.split_center_box s ↔ y ∈ I ∧ ∀ i, (I.lower i + I.upper i) / 2 < y i ↔ i ∈ s :=
begin
  simp only [split_center_box, mem_def, ← forall_and_distrib],
  refine forall_congr (λ i, _),
  dunfold set.piecewise,
  split_ifs with hs; simp only [hs, iff_true, iff_false, not_lt],
  exacts [⟨λ H, ⟨⟨(left_lt_add_div_two.2 (I.lower_lt_upper i)).trans H.1, H.2⟩, H.1⟩, λ H, ⟨H.2, H.1.2⟩⟩,
    ⟨λ H, ⟨⟨H.1, H.2.trans (add_div_two_lt_right.2 (I.lower_lt_upper i)).le⟩, H.2⟩, λ H, ⟨H.1.1, H.2⟩⟩]
end

lemma split_center_box_le (I : box ι) (s : set ι) : I.split_center_box s ≤ I :=
λ x hx, (mem_split_center_box.1 hx).1

lemma disjoint_split_center_box (I : box ι) {s t : set ι} (h : s ≠ t) :
  disjoint (I.split_center_box s : set (ι → ℝ)) (I.split_center_box t) :=
begin
  rintro y ⟨hs, ht⟩, apply h,
  ext i,
  rw [mem_coe, mem_split_center_box] at hs ht,
  rw [← hs.2, ← ht.2]
end

lemma injective_split_center_box (I : box ι) : injective I.split_center_box :=
λ s t H, by_contra $ λ Hne, (I.disjoint_split_center_box Hne).ne (nonempty_coe _).ne_empty (H ▸ rfl)

lemma Union_coe_split_center_box (I : box ι) :
  (⋃ s, (I.split_center_box s : set (ι → ℝ))) = I :=
subset.antisymm (Union_subset $ λ s, I.split_center_box_le s) $
  λ y hy, mem_Union.2 ⟨{i | _ < y i}, mem_split_center_box.2 ⟨hy, λ i, iff.rfl⟩⟩

@[simp] lemma upper_sub_lower_split_center_box (I : box ι) (s : set ι) (i : ι) :
  (I.split_center_box s).upper i - (I.split_center_box s).lower i = (I.upper i - I.lower i) / 2 :=
by by_cases hs : i ∈ s; field_simp [split_center_box, hs, mul_two, two_mul]

def split_center [fintype ι] (I : box ι) : partition I :=
{ boxes := range I.split_center_box,
  finite_boxes := finite_range _,
  bUnion_boxes_coe := by rw [bUnion_range, Union_coe_split_center_box],
  pairwise_disjoint := by { rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ Hne,
    exact I.disjoint_split_center_box (mt (congr_arg _) Hne) } }

@[simp] lemma mem_split_center [fintype ι] {I J : box ι} :
  J ∈ I.split_center ↔ ∃ s, J = I.split_center_box s :=
mem_range.trans $ exists_congr $ λ s, eq_comm

lemma upper_sub_lower_of_mem_split_center [fintype ι] {J} (h : J ∈ I.split_center) (i : ι) :
  J.upper i - J.lower i = (I.upper i - I.lower i) / 2 :=
let ⟨s, hs⟩ := mem_split_center.1 h in hs.symm ▸ I.upper_sub_lower_split_center_box s i

@[elab_as_eliminator]
lemma subbox_induction_on [fintype ι] {p : box ι → Prop} (I : box ι)
  (H_ind : ∀ J ≤ I, (∀ J' ∈ J.split_center, p J') → p J)
  (H_nhds : ∀ z ∈ I.Icc, ∃ (U ∈ 𝓝[I.Icc] z), ∀ (J ≤ I) (n : ℕ), z ∈ J.Icc → J.Icc ⊆ U →
    (∀ i, J.upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ n) → p J) :
  p I :=
begin
  by_contra hpI,
  -- First we use `H_ind` to construct a decreasing sequence of boxes such that `∀ n, ¬(p n)`.
  replace H_ind := λ J hJ, not_imp_not.2 (H_ind J hJ),
  simp only [mem_split_center, exists_imp_distrib, forall_eq_apply_imp_iff', not_forall] at H_ind,
  choose! s hs using H_ind,
  set J : ℕ → box ι := λ n, (λ J, split_center_box J (s J))^[n] I,
  have J_succ : ∀ n, J (n + 1) = split_center_box (J n) (s $ J n),
    from λ n, iterate_succ_apply' _ _ _,
  -- Now we prove some properties of `J`
  have hJmono : monotone (order_dual.to_dual ∘ J),
    from monotone_nat_of_le_succ (λ n, by simpa [J_succ] using split_center_box_le _ _),
  have hJle : ∀ n, J n ≤ I, from λ n, (hJmono (zero_le n)),
  have hJp : ∀ n, ¬p (J n),
    from λ n, nat.rec_on n hpI (λ n, by simpa only [J_succ] using hs (J n) (hJle n)),
  have hJsub : ∀ n i, (J n).upper i - (J n).lower i = (I.upper i - I.lower i) / 2 ^ n,
  { intros n i, induction n with n ihn, { simp [J] },
    simp only [pow_succ', J_succ, upper_sub_lower_split_center_box, ihn, div_div_eq_div_mul] },
  have h0 : J 0 = I, from rfl,
  -- Now we clear unneeded assumptions
  clear_value J, clear hpI hs J_succ s,
  -- Let `z` be the unique common point of all `(J n).Icc`. Then `H_nhds` proves `p (J n)` for
  -- sufficiently lart `n`. This contradicts `hJp`.
  set z : ι → ℝ := ⨆ n, (J n).lower,
  have hzJ : ∀ n, z ∈ (J n).Icc,
    from mem_Inter.1 (csupr_mem_Inter_Icc_of_mono_decr_Icc
      ((@box.Icc ι).monotone.order_dual.comp hJmono) (λ n, (J n).lower_le_upper)),
  have hJl_mem : ∀ n, (J n).lower ∈ I.Icc, from λ n, le_iff_Icc.1 (hJle n) (J n).lower_mem_Icc,
  have hJu_mem : ∀ n, (J n).upper ∈ I.Icc, from λ n, le_iff_Icc.1 (hJle n) (J n).upper_mem_Icc,
  have hJlz : tendsto (λ n, (J n).lower) at_top (𝓝 z),
    from tendsto_at_top_csupr_pi' (monotone_lower.order_dual.comp hJmono)
      ⟨I.upper, λ x ⟨n, hn⟩, hn ▸ (hJl_mem n).2⟩,
  have hJuz : tendsto (λ n, (J n).upper) at_top (𝓝 z),
  { suffices : tendsto (λ n, (J n).upper - (J n).lower) at_top (𝓝 0), by simpa using hJlz.add this,
    refine tendsto_pi.2 (λ i, _),
    simpa [hJsub] using tendsto_const_nhds.div_at_top
      (tendsto_pow_at_top_at_top_of_one_lt (@one_lt_two ℝ _ _)) },
  replace hJlz : tendsto (λ n, (J n).lower) at_top (𝓝[Icc I.lower I.upper] z),
    from tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ hJlz
      (eventually_of_forall hJl_mem),
  replace hJuz : tendsto (λ n, (J n).upper) at_top (𝓝[Icc I.lower I.upper] z),
    from tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ hJuz
      (eventually_of_forall hJu_mem),
  rcases H_nhds z (h0 ▸ hzJ 0) with ⟨U, hUz, hU⟩,
  rcases (tendsto_lift'.1 (hJlz.Icc hJuz) U hUz).exists with ⟨n, hUn⟩,
  exact hJp n (hU (J n) (hJle n) n (hzJ n) hUn (hJsub n))
end


end box

namespace marked_partition

lemma exists_is_Henstock_is_subordinate_homothetic [fintype ι] (I : box ι) {r : (ι → ℝ) → ℝ≥0∞}
  (h0 : ∀ x ∈ I.Icc, r x ≠ 0) :
  ∃ π : marked_partition I, π.is_Henstock ∧ π.is_subordinate r ∧
    ∀ J ∈ π, ∃ n : ℕ, ∀ i, (J : _).upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ n :=
begin
  refine box.subbox_induction_on I (λ J hle hJ, _) (λ z hz, _),
  { choose! πi hHen hr n hn using hJ,
    refine ⟨J.split_center.bUnion_marked (λ J _, πi J), is_Henstock_bUnion.2 hHen,
      is_subordinate_bUnion.2 hr, λ J' hJ', _⟩,
    rcases J.split_center.mem_bUnion_marked.1 hJ' with ⟨J₁, h₁, h₂⟩,
    refine ⟨n J₁ J' + 1, λ i, _⟩,
    simp only [hn J₁ h₁ J' h₂, box.upper_sub_lower_of_mem_split_center h₁, pow_succ,
      div_div_eq_div_mul] },
  { replace h0 : 0 < r z, from pos_iff_ne_zero.2 (h0 z hz),
    refine ⟨I.Icc ∩ closed_ball z (r z),
      inter_mem_nhds_within _ (closed_ball_mem_nhds _ h0), _⟩,
    intros J Hle n Hmem HIcc Hsub,
    rw set.subset_inter_iff at HIcc,
    refine ⟨single _ _ Hmem, is_Henstock_single _, (is_subordinate_single _).2 HIcc.2, _⟩,
    simp only [mem_single, forall_eq],
    refine ⟨0, λ i, _⟩, simp }
end

end marked_partition

end box_integral

