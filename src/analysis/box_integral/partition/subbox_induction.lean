/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.partition.tagged
import analysis.box_integral.partition.split_induction
import analysis.specific_limits

/-!
# Induction on subboxes

In this file we prove (see
`box_integral.tagged_partition.exists_is_Henstock_is_subordinate_homothetic`) that for every box `I`
in `ℝⁿ` and a function `r : ℝⁿ → ℝ` positive on `I` there exists a tagged partition `π` of `I` such
that

* `π` is a Henstock partition;
* `π` is subordinate to `r`;
* each box in `π` is homothetic to `I` with coefficient of the form `1 / 2 ^ n`.

Later we will use this lemma to prove that the Henstock filter is nontrivial, hence the Henstock
integral is well-defined.

We prove this lemma using a special kind of induction principle formulated in
`box_integral.box.subbox_induction_on`. Let `p` be a predicate on `box ι`, let `I` be a box. Suppose
that the following two properties hold true.

* Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split it into
  `2 ^ n` boxes. If `p` holds true on each of these boxes, then it true on `J`.
* For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within `I.Icc` such
  that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I` with a
  coefficient of the form `1 / 2 ^ n`, then `p` is true on `J`.

Then `p I` is true.

## Tags

partition, tagged partition, Henstock integral
-/

open set finset function filter metric
open_locale classical topological_space filter ennreal
noncomputable theory

namespace box_integral

variables {ι : Type*}


variables [fintype ι] {I J : box ι}

namespace partition

/-- Split a box in `ℝⁿ` into `2 ^ n` boxes by hyperplanes passing through its center. -/
def split_center (I : box ι) : partition I :=
{ boxes := finset.univ.map (box.split_center_box_emb I),
  le_of_mem' := by simp [I.split_center_box_le],
  exists_mem' := λ x hx, by simp [hx],
  pairwise_disjoint :=
    begin
      rw [finset.coe_map, finset.coe_univ, image_univ],
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ Hne,
      exact I.disjoint_split_center_box (mt (congr_arg _) Hne)
    end }

@[simp] lemma mem_split_center : J ∈ split_center I ↔ ∃ s, J = I.split_center_box s :=
by simp [split_center, eq_comm]

lemma upper_sub_lower_of_mem_split_center (h : J ∈ split_center I) (i : ι) :
  J.upper i - J.lower i = (I.upper i - I.lower i) / 2 :=
let ⟨s, hs⟩ := mem_split_center.1 h in hs.symm ▸ I.upper_sub_lower_split_center_box s i

end partition

namespace box

open partition

/-- Let `p` be a predicate on `box ι`, let `I` be a box. Suppose that the following two properties
hold true.

* Consider a smaller box `J ≤ I`. The hyperplanes passing through the center of `J` split it into
  `2 ^ n` boxes. If `p` holds true on each of these boxes, then it true on `J`.
* For each `z` in the closed box `I.Icc` there exists a neighborhood `U` of `z` within `I.Icc` such
  that for every box `J ≤ I` such that `z ∈ J.Icc ⊆ U`, if `J` is homothetic to `I` with a
  coefficient of the form `1 / 2 ^ n`, then `p` is true on `J`.

Then `p I` is true. -/
@[elab_as_eliminator]
lemma subbox_induction_on {p : box ι → Prop} (I : box ι)
  (H_ind : ∀ J ≤ I, (∀ J' ∈ split_center J, p J') → p J)
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
    from tendsto_at_top_csupr (monotone_lower.order_dual.comp hJmono)
      ⟨I.upper, λ x ⟨n, hn⟩, hn ▸ (hJl_mem n).2⟩,
  have hJuz : tendsto (λ n, (J n).upper) at_top (𝓝 z),
  { suffices : tendsto (λ n, (J n).upper - (J n).lower) at_top (𝓝 0), by simpa using hJlz.add this,
    refine tendsto_pi_nhds.2 (λ i, _),
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

namespace tagged_partition

open partition

/-- Let `I` be a box in `ℝⁿ` and `r : ℝⁿ → ℝ` be a function positive on the corresponding closed
box. Then there exists a tagged partition `π` of `I` such that

* `π` is a Henstock partition;
* `π` is subordinate to `r`;
* each box in `π` is homothetic to `I` with coefficient of the form `1 / 2 ^ n`.

This lemma implies that the Henstock filter is nontrivial, hence the Henstock integral is
well-defined. -/
lemma exists_is_Henstock_is_subordinate_homothetic {I : box ι} {r : (ι → ℝ) → ℝ}
  (h0 : ∀ x ∈ I.Icc, 0 < r x) :
  ∃ π : tagged_partition I, π.is_Henstock ∧ π.is_subordinate r ∧
    (∀ J ∈ π, ∃ n : ℕ, ∀ i, (J : _).upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ n) ∧
    π.distortion = I.distortion :=
begin
  refine box.subbox_induction_on I (λ J hle hJ, _) (λ z hz, _),
  { choose! πi hHen hr Hn Hd using hJ, choose! n hn using Hn,
    refine ⟨(split_center J).bUnion_tagged πi, is_Henstock_bUnion.2 hHen,
      is_subordinate_bUnion.2 hr, (and_iff_left_of_imp _).2 _⟩,
    { refine λ H, partition.distortion_of_const _ (λ J' h', _),
      rcases H J' h' with ⟨n, hn⟩,
      exact box.distortion_eq_of_sub_eq_div hn },
    intros J' hJ',
    rcases (split_center J).mem_bUnion_tagged.1 hJ' with ⟨J₁, h₁, h₂⟩,
    refine ⟨n J₁ J' + 1, λ i, _⟩,
    simp only [hn J₁ h₁ J' h₂, upper_sub_lower_of_mem_split_center h₁, pow_succ,
      div_div_eq_div_mul] },
  { refine ⟨I.Icc ∩ closed_ball z (r z),
      inter_mem_nhds_within _ (closed_ball_mem_nhds _ (h0 z hz)), _⟩,
    intros J Hle n Hmem HIcc Hsub,
    rw set.subset_inter_iff at HIcc,
    refine ⟨single _ _ Hmem, is_Henstock_single _, (is_subordinate_single _).2 HIcc.2, _⟩,
    simp only [mem_single, forall_eq],
    refine ⟨⟨0, λ i, _⟩, distortion_single _⟩, simp }
end

end tagged_partition

namespace tagged_prepartition

/-- For any tagged prepartition `π` of `I` subordinate to a function `r` positive on `I.Icc`, there
exists a tagged partition `π'` such that

* `π'` is subordinate to the same function `r`;
* `π ⊆ π'` and their `tag` functions agree on `J ∈ π`;
* `π'` is Henstock outside of `π`, i.e., `π'.tag J ∈ J.Icc` for any box `J ∈ π'`, `J ∉ π`;
* `π'` has a predictable distortion; namely, its distortion equals the distortion of
  `π.to_prepartition.to_partition`. -/
lemma exists_tagged_partition_superset_is_subordinate {I : box ι} {r : (ι → ℝ) → ℝ}
  {π : tagged_prepartition I} (h0 : ∀ x ∈ I.Icc, 0 < r x) (hr : π.is_subordinate r) :
  ∃ π' : tagged_partition I, π'.is_subordinate r ∧ (∀ J ∈ π, J ∈ π') ∧
    (∀ J ∈ π, π.tag J = π'.tag J) ∧ (∀ J ∈ π', J ∉ π → π'.tag J ∈ J.Icc) ∧
    (π'.distortion = π.to_prepartition.to_partition.distortion) :=
begin
  set πp : partition I := π.to_prepartition.to_partition,
  have : ∀ J ∈ πp, ∃ π' : tagged_partition J, π'.is_Henstock ∧ π'.is_subordinate r ∧
    (∀ J' ∈ π', ∃ n : ℕ, ∀ i, (J' : _).upper i - J'.lower i = (J.upper i - J.lower i) / 2 ^ n) ∧
    π'.distortion = J.distortion,
    from λ J hJ, tagged_partition.exists_is_Henstock_is_subordinate_homothetic
      (λ x hx, h0 x (box.le_iff_Icc.1 (πp.le_of_mem hJ) hx)),
  choose! πi hiHen hir hsub Hd, clear hsub,
  set π' : partition I := πp.bUnion (π.boxes.piecewise (λ _, ⊤) (λ J, (πi J).to_partition)),
  set tag : box ι → ι → ℝ :=
     π.boxes.piecewise π.tag (λ J, (πi (πp.bUnion_index (λ J', (πi J').to_partition) J)).tag J),
  have Htag_π : ∀ J ∈ π, tag J = π.tag J, from λ J, π.boxes.piecewise_eq_of_mem _ _,
  have Htag_πi : ∀ J ∉ π, tag J = (πi (πp.bUnion_index (λ J', (πi J').to_partition) J)).tag J,
    from λ J, π.boxes.piecewise_eq_of_not_mem _ _,
  have HtagI : ∀ J, tag J ∈ I.Icc,
  { intro J,
    by_cases hJπ : J ∈ π,
    { rw Htag_π _ hJπ, exact π.tag_mem_Icc J },
    { rw Htag_πi _ hJπ,
      exact box.le_iff_Icc.1 (πp.bUnion_index_le _ _) ((πi _).tag_mem_Icc J) } },
  set πt : tagged_partition I := ⟨⟨π'.to_prepartition, tag, HtagI⟩, π'.exists_mem'⟩,
  have mem_πt : ∀ J, J ∈ πt → J ∉ π → ∃ Jp ∈ πp, Jp ∉ π ∧ J ∈ πi Jp,
  { rintros J hJ hJπ,
    replace hJ := πp.mem_bUnion.1 hJ, rcases hJ with ⟨Jp, hJp, hJ⟩,
    have : Jp ∉ π,
    { intro H,
      rw [π.boxes.piecewise_eq_of_mem _ _ H, partition.mem_top] at hJ,
      rw hJ at hJπ, exact hJπ H },
    rw [π.boxes.piecewise_eq_of_not_mem _ _ this] at hJ,
    exact ⟨Jp, hJp, this, hJ⟩ },
  have : ∀ p : (ι → ℝ) → box ι → Prop, (∀ J ∈ π, p (π.tag J) J) →
    (∀ J ∉ π, J ∈ πp → ∀ Ji ∈ πi J, p ((πi J).tag Ji) Ji) → ∀ J ∈ πt, p (πt.tag J) J,
  { rintros p hpπ hpπ' J hJ,
    by_cases hJπ : J ∈ π,
    { convert hpπ _ hJπ using 1,exact Htag_π _ hJπ },
    { rcases mem_πt J hJ hJπ with ⟨Jp, hJp, hJpπ, hJ⟩,
      simp only [πt, Htag_πi J hJπ],
      rw πp.bUnion_index_of_mem; [skip, exact hJp, exact hJ],
      exact hpπ' _ hJpπ hJp _ hJ } },
  refine ⟨πt, _, _, _, _, _⟩,
  { exact this (λ x J, J.Icc ⊆ closed_ball x (r x)) hr (λ J hJ hJp, (hir _ hJp)) },
  { intros J hJ,
    refine πp.mem_bUnion.2 ⟨J, π.to_prepartition.subset_to_partition hJ, _⟩,
    rw [π.boxes.piecewise_eq_of_mem _ _ hJ, partition.mem_top] },
  { exact λ J hJ, (Htag_π J hJ).symm },
  { intros J hJ hJ',
    rcases mem_πt J hJ hJ' with ⟨Jp, hJp, hJpπ, hJ⟩,
    simp only [πt, Htag_πi _ hJ'],
    rw [πp.bUnion_index_of_mem]; [skip, exact hJp, exact hJ],
    exact hiHen _ hJp _ hJ },
  { refine (πp.distortion_bUnion _).trans (sup_congr rfl $ λ J hJ, _),
    by_cases h : J ∈ π,
    { rw [π.boxes.piecewise_eq_of_mem _ _ h, partition.distortion_top] },
    { rw [π.boxes.piecewise_eq_of_not_mem _ _ h],
      exact Hd J hJ } }
end

def to_subordinate_tagged_partition (π : tagged_prepartition I) (r : (ι → ℝ) → ℝ)
  (h0 : ∀ x ∈ I.Icc, 0 < r x) (hr : π.is_subordinate r) :
  tagged_partition I :=
(exists_tagged_partition_superset_is_subordinate h0 hr).some

variables {π : tagged_prepartition I} {r : (ι → ℝ) → ℝ}

lemma is_subordinate.to_subordinate_tagged_partition (hr : π.is_subordinate r)
  (h0 : ∀ x ∈ I.Icc, 0 < r x) :
  (π.to_subordinate_tagged_partition r h0 hr).is_subordinate r :=
(exists_tagged_partition_superset_is_subordinate h0 hr).some_spec.1

lemma is_subordinate.mem_to_subordinate_tagged_partition (hr : π.is_subordinate r)
  (h0 : ∀ x ∈ I.Icc, 0 < r x) (hJ : J ∈ π) :
  J ∈ π.to_subordinate_tagged_partition r h0 hr :=
(exists_tagged_partition_superset_is_subordinate h0 hr).some_spec.2.1 _ hJ




end tagged_prepartition

end box_integral
