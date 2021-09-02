import analysis.box_integral.box.subbox_induction
import analysis.box_integral.partition.tagged

namespace box_integral

open set metric
open_locale classical topological_space
noncomputable theory

variables {ι : Type*} [fintype ι] {I J : box ι}

namespace prepartition

/-- Split a box in `ℝⁿ` into `2 ^ n` boxes by hyperplanes passing through its center. -/
def split_center (I : box ι) : prepartition I :=
{ boxes := finset.univ.map (box.split_center_box_emb I),
  le_of_mem' := by simp [I.split_center_box_le],
  pairwise_disjoint :=
    begin
      rw [finset.coe_map, finset.coe_univ, image_univ],
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ Hne,
      exact I.disjoint_split_center_box (mt (congr_arg _) Hne)
    end }

@[simp] lemma mem_split_center : J ∈ split_center I ↔ ∃ s, I.split_center_box s = J :=
by simp [split_center]

lemma is_partition_split_center (I : box ι) : is_partition (split_center I) :=
λ x hx, by simp [hx]

lemma upper_sub_lower_of_mem_split_center (h : J ∈ split_center I) (i : ι) :
  J.upper i - J.lower i = (I.upper i - I.lower i) / 2 :=
let ⟨s, hs⟩ := mem_split_center.1 h in hs ▸ I.upper_sub_lower_split_center_box s i

end prepartition

namespace box

open prepartition tagged_prepartition

@[elab_as_eliminator]
lemma subbox_induction_on {p : box ι → Prop} (I : box ι)
  (H_ind : ∀ J ≤ I, (∀ J' ∈ split_center J, p J') → p J)
  (H_nhds : ∀ z ∈ I.Icc, ∃ (U ∈ 𝓝[I.Icc] z), ∀ (J ≤ I) (n : ℕ), z ∈ J.Icc → J.Icc ⊆ U →
    (∀ i, J.upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ n) → p J) :
  p I :=
begin
  refine subbox_induction_on' I (λ J hle hs, H_ind J hle $ λ J' h', _) H_nhds,
  rcases mem_split_center.1 h' with ⟨s, rfl⟩,
  exact hs s
end

/-- Let `I` be a box in `ℝⁿ` and `r : ℝⁿ → ℝ` be a function positive on the corresponding closed
box. Then there exists a tagged partition `π` of `I` such that

* `π` is a Henstock partition;
* `π` is subordinate to `r`;
* each box in `π` is homothetic to `I` with coefficient of the form `1 / 2 ^ n`.

This lemma implies that the Henstock filter is nontrivial, hence the Henstock integral is
well-defined. -/
lemma exists_tagged_partition_is_Henstock_is_subordinate_homothetic (I : box ι) {r : (ι → ℝ) → ℝ}
  (h0 : ∀ x ∈ I.Icc, 0 < r x) :
  ∃ π : tagged_prepartition I, π.is_partition ∧ π.is_Henstock ∧ π.is_subordinate r ∧
    (∀ J ∈ π, ∃ n : ℕ, ∀ i, (J : _).upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ n) ∧
    π.distortion = I.distortion :=
begin
  refine box.subbox_induction_on I (λ J hle hJ, _) (λ z hz, _),
  { choose! πi hP hHen hr Hn Hd using hJ, choose! n hn using Hn,
    have hP : ((split_center J).bUnion_tagged πi).is_partition,
      from (is_partition_split_center _).bUnion_tagged hP,
    have hsub : ∀ (J' ∈ (split_center J).bUnion_tagged πi), ∃ n : ℕ, ∀ i,
      (J' : _).upper i - J'.lower i = (J.upper i - J.lower i) / 2 ^ n,
    { intros J' hJ',
      rcases (split_center J).mem_bUnion_tagged.1 hJ' with ⟨J₁, h₁, h₂⟩,
      refine ⟨n J₁ J' + 1, λ i, _⟩,
      simp only [hn J₁ h₁ J' h₂, upper_sub_lower_of_mem_split_center h₁, pow_succ,
        div_div_eq_div_mul] },
    refine ⟨_, hP, is_Henstock_bUnion_tagged.2 hHen, is_subordinate_bUnion_tagged.2 hr, hsub, _⟩,
    refine tagged_prepartition.distortion_of_const _ hP.nonempty_boxes (λ J' h', _),
    rcases hsub J' h' with ⟨n, hn⟩,
    exact box.distortion_eq_of_sub_eq_div hn },
  { refine ⟨I.Icc ∩ closed_ball z (r z),
      inter_mem_nhds_within _ (closed_ball_mem_nhds _ (h0 z hz)), _⟩,
    intros J Hle n Hmem HIcc Hsub,
    rw set.subset_inter_iff at HIcc,
    refine ⟨single _ _ le_rfl _ Hmem, is_partition_single _, is_Henstock_single _,
      (is_subordinate_single _ _).2 HIcc.2, _, distortion_single _ _⟩,
    simp only [tagged_prepartition.mem_single, forall_eq],
    refine ⟨0, λ i, _⟩, simp }
end

end box

namespace prepartition

open tagged_prepartition finset function

lemma exists_tagged_le_is_Henstock_is_subordinate_Union_eq {I : box ι} {r : (ι → ℝ) → ℝ}
  (h0 : ∀ x ∈ I.Icc, 0 < r x) (π : prepartition I) :
  ∃ π' : tagged_prepartition I, π'.to_prepartition ≤ π ∧
    π'.is_Henstock ∧ π'.is_subordinate r ∧ π'.distortion = π.distortion ∧
    π'.Union = π.Union :=
begin
  have := λ J hJ, box.exists_tagged_partition_is_Henstock_is_subordinate_homothetic J
    (λ x hx, h0 x (box.le_iff_Icc.1 (π.le_of_mem hJ) hx)),
  choose! πi πip πiH πir hsub πid, clear hsub,
  refine ⟨π.bUnion_tagged πi, bUnion_le _ _, is_Henstock_bUnion_tagged.2 πiH,
    is_subordinate_bUnion_tagged.2 πir, _, _⟩,
  { rw [distortion_bUnion_tagged],
    exact sup_congr rfl πid },
  { rw [Union_bUnion_tagged, Union_def],
    exact Union_congr id surjective_id
      (λ J, Union_congr id surjective_id $ λ hJ, (πip _ hJ).Union_eq) }
end

end prepartition

end box_integral

