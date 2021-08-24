import data.real.basic
import data.finset.pi_induction
import data.finset.pimage
import data.set.intervals.pi
import analysis.specific_limits

open_locale classical nnreal ennreal topological_space filter
open function filter

noncomputable theory

variables {ι : Type*}

@[ext] structure partition_box (ι : Type*) :=
(lower upper : ι → ℝ)
(lower_lt_upper : ∀ i, lower i < upper i)

attribute [simp] partition_box.lower_lt_upper

namespace partition_box

open set

variables (I J : partition_box ι) {x y : ι → ℝ}

instance : inhabited (partition_box ι) := ⟨⟨0, 1, λ i, zero_lt_one⟩⟩

protected def Icc : set (ι → ℝ) := Icc I.lower I.upper
protected def Ioc : set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc (I.lower i) (I.upper i)}

lemma Icc_def : I.Icc = Icc I.lower I.upper := rfl

lemma Ioc_def : I.Ioc = {x | ∀ i, x i ∈ Ioc (I.lower i) (I.upper i)} := rfl

lemma mem_Ioc : x ∈ I.Ioc ↔ ∀ i, I.lower i < x i ∧ x i ≤ I.upper i := iff.rfl

lemma Icc_eq_pi : I.Icc = pi univ (λ i, Icc (I.lower i) (I.upper i)) := (pi_univ_Icc _ _).symm
lemma Ioc_eq_pi : I.Ioc = pi univ (λ i, Ioc (I.lower i) (I.upper i)) :=
set.ext $ λ x, mem_univ_pi.symm

lemma lower_le_upper : I.lower ≤ I.upper := λ i, (I.lower_lt_upper i).le

@[simp] lemma upper_mem_Icc : I.upper ∈ I.Icc := right_mem_Icc.2 I.lower_le_upper
@[simp] lemma lower_mem_Icc : I.lower ∈ I.Icc := left_mem_Icc.2 I.lower_le_upper
@[simp] lemma upper_mem_Ioc : I.upper ∈ I.Ioc := λ i, right_mem_Ioc.2 $ I.lower_lt_upper i

lemma nonempty_Ioc : I.Ioc.nonempty := ⟨_, I.upper_mem_Ioc⟩

@[simp] protected lemma closure_Ioc : closure I.Ioc = I.Icc :=
by simp only [Ioc_eq_pi, closure_pi_set, closure_Ioc (I.lower_lt_upper _), Icc_eq_pi]

instance : has_le (partition_box ι) := ⟨λ I J, I.Ioc ⊆ J.Ioc⟩

lemma le_tfae :
  tfae [I ≤ J, I.Ioc ⊆ J.Ioc, I.Icc ⊆ J.Icc,
    J.lower ≤ I.lower ∧ I.upper ≤ J.upper] :=
begin
  tfae_have : 1 ↔ 2, from iff.rfl,
  tfae_have : 2 → 3, from λ h, by simpa only [partition_box.closure_Ioc] using closure_mono h,
  tfae_have : 3 ↔ 4, from Icc_subset_Icc_iff I.lower_le_upper,
  tfae_have : 4 → 2, from λ h x hx i, Ioc_subset_Ioc (h.1 i) (h.2 i) (hx i),
  tfae_finish
end

variables {I J}

lemma le_iff_Ioc : I ≤ J ↔ I.Ioc ⊆ J.Ioc := iff.rfl
lemma le_iff_Icc : I ≤ J ↔ I.Icc ⊆ J.Icc := (le_tfae I J).out 0 2
lemma le_iff_bounds : I ≤ J ↔ J.lower ≤ I.lower ∧ I.upper ≤ J.upper := (le_tfae I J).out 0 3

lemma Ioc_injective : injective (partition_box.Ioc : partition_box ι → set (ι → ℝ)) :=
begin
  intros I J h,
  simp only [subset.antisymm_iff, ← le_iff_Ioc, le_iff_bounds] at h,
  exact ext _ _ (le_antisymm h.2.1 h.1.1) (le_antisymm h.1.2 h.2.2)
end

instance : partial_order (partition_box ι) :=
{ le := (≤),
  .. partial_order.lift (partition_box.Ioc : partition_box ι → set (ι → ℝ)) Ioc_injective }

lemma monotone_lower : monotone (λ I : partition_box ι, order_dual.to_dual I.lower) :=
λ I J H, (le_iff_bounds.1 H).1

lemma monotone_upper : monotone (λ I : partition_box ι, I.upper) :=
λ I J H, (le_iff_bounds.1 H).2

lemma Ioc_inter_Ioc_nonempty_iff {I J : partition_box ι} :
  (I.Ioc ∩ J.Ioc).nonempty ↔ ∀ i, max (I.lower i) (J.lower i) < min (I.upper i) (J.upper i) :=
by simp only [Ioc_eq_pi, ← pi_inter_distrib, univ_pi_nonempty_iff, Ioc_inter_Ioc, set.nonempty_Ioc,
  sup_eq_max, inf_eq_min]

def inter (I J : partition_box ι) (H : (I.Ioc ∩ J.Ioc).nonempty) :
  partition_box ι :=
⟨_, _, Ioc_inter_Ioc_nonempty_iff.1 H⟩

@[simp] lemma inter_Ioc (H : (I.Ioc ∩ J.Ioc).nonempty) : (I.inter J H).Ioc = I.Ioc ∩ J.Ioc :=
by simp only [inter, Ioc_eq_pi, ← pi_inter_distrib, Ioc_inter_Ioc, sup_eq_max, inf_eq_min]

lemma inter_le_left (H : (I.Ioc ∩ J.Ioc).nonempty) : I.inter J H ≤ I :=
le_iff_Ioc.2 $ by simp only [inter_Ioc, inter_subset_left]

lemma inter_le_right (H : (I.Ioc ∩ J.Ioc).nonempty) : I.inter J H ≤ J :=
le_iff_Ioc.2 $ by simp only [inter_Ioc, inter_subset_right]

@[simp] lemma le_inter_iff (H : (I.Ioc ∩ J.Ioc).nonempty) {I'} :
  I' ≤ I.inter J H ↔ I' ≤ I ∧ I' ≤ J :=
by simp only [le_iff_Ioc, inter_Ioc, subset_inter_iff]

lemma Union_inter_Ioc : (⋃ H, (I.inter J H).Ioc) = I.Ioc ∩ J.Ioc := 
by simp only [inter_Ioc, Union_nonempty_self]

@[simps] def split_lower (I : partition_box ι) (i : ι) (x : Ioo (I.lower i) (I.upper i)) :
  partition_box ι :=
⟨I.lower, update I.upper i x, forall_lt_update_iff.2 ⟨x.2.1, λ j _, I.lower_lt_upper j⟩⟩

lemma mem_split_lower_Ioc (I : partition_box ι) {i x} {y : ι → ℝ} :
  y ∈ (I.split_lower i x).Ioc ↔ y ∈ I.Ioc ∧ y i ≤ x :=
begin
  simp only [mem_Ioc, forall_and_distrib, split_lower, and_assoc],
  refine and_congr_right (λ H, (@le_update_iff _ _ _ _ y I.upper i x).trans _),
  refine (and_comm _ _).trans (and_congr_left $ λ Hi, iff.trans _ (@and_forall_ne _ _ i)),
  exact (and_iff_right_of_imp $ λ Hne, Hi.trans x.2.2.le).symm
end

@[simps] def split_upper (I : partition_box ι) (i : ι) (x : Ioo (I.lower i) (I.upper i)) :
  partition_box ι :=
⟨update I.lower i x, I.upper, forall_update_lt_iff.2 ⟨x.2.2, λ j _, I.lower_lt_upper j⟩⟩

lemma mem_split_upper_Ioc (I : partition_box ι) {i x} {y : ι → ℝ} :
  y ∈ (I.split_upper i x).Ioc ↔ y ∈ I.Ioc ∧ ↑x < y i :=
begin
  simp only [mem_Ioc, forall_and_distrib, split_upper, and_assoc, forall_update_lt_iff],
  exact ⟨λ ⟨Hi, Hne, Hle⟩, ⟨and_forall_ne.1 ⟨x.2.1.trans Hi, Hne⟩, Hle, Hi⟩,
    λ ⟨Hlt, Hle, Hi⟩, ⟨Hi, λ j _, Hlt j, Hle⟩⟩
end

lemma disjoint_Ioc_split (I : partition_box ι) (i x) :
  disjoint (I.split_lower i x).Ioc (I.split_upper i x).Ioc :=
λ y ⟨hl, hu⟩, (I.mem_split_lower_Ioc.1 hl).2.not_lt (I.mem_split_upper_Ioc.1 hu).2

lemma union_Ioc_split (I : partition_box ι) (i x) :
  (I.split_lower i x).Ioc ∪ (I.split_upper i x).Ioc = I.Ioc :=
begin
  ext1 y,
  simp only [mem_union_eq, mem_split_lower_Ioc, mem_split_upper_Ioc, ← and_or_distrib_left,
    le_or_lt, and_true]
end

lemma split_lower_le (I : partition_box ι) (i x) : I.split_lower i x ≤ I :=
by simp only [le_iff_Ioc, ← I.union_Ioc_split i x, subset_union_left]

lemma split_upper_le (I : partition_box ι) (i x) : I.split_upper i x ≤ I :=
by simp only [le_iff_Ioc, ← I.union_Ioc_split i x, subset_union_right]

open finset

def split_center (I : partition_box ι) (s : set ι) : partition_box ι :=
{ lower := s.piecewise (λ i, (I.lower i + I.upper i) / 2) I.lower,
  upper := s.piecewise I.upper (λ i, (I.lower i + I.upper i) / 2),
  lower_lt_upper := λ i, by { dunfold set.piecewise, split_ifs;
    simp only [left_lt_add_div_two, add_div_two_lt_right, I.lower_lt_upper] } }

lemma mem_split_center_Ioc {s : set ι} {y : ι → ℝ} :
  y ∈ (I.split_center s).Ioc ↔ y ∈ I.Ioc ∧ ∀ i, (I.lower i + I.upper i) / 2 < y i ↔ i ∈ s :=
begin
  simp only [split_center, mem_Ioc, ← forall_and_distrib],
  refine forall_congr (λ i, _),
  dunfold set.piecewise,
  split_ifs with hs; simp only [hs, iff_true, iff_false, not_lt],
  exacts [⟨λ H, ⟨⟨(left_lt_add_div_two.2 (I.lower_lt_upper i)).trans H.1, H.2⟩, H.1⟩, λ H, ⟨H.2, H.1.2⟩⟩,
    ⟨λ H, ⟨⟨H.1, H.2.trans (add_div_two_lt_right.2 (I.lower_lt_upper i)).le⟩, H.2⟩, λ H, ⟨H.1.1, H.2⟩⟩]
end

lemma split_center_le (I : partition_box ι) (s : set ι) : I.split_center s ≤ I :=
λ x hx, (mem_split_center_Ioc.1 hx).1

lemma disjoint_split_center_Ioc (I : partition_box ι) {s t : set ι} (h : s ≠ t) :
  disjoint (I.split_center s).Ioc (I.split_center t).Ioc :=
begin
  rintro y ⟨hs, ht⟩, apply h,
  ext i,
  rw mem_split_center_Ioc at hs ht,
  rw [← hs.2, ← ht.2]
end

lemma injective_split_center (I : partition_box ι) : injective I.split_center :=
λ s t H, by_contra $ λ Hne, (I.disjoint_split_center_Ioc Hne).ne (nonempty_Ioc _).ne_empty (H ▸ rfl)

lemma Union_split_center_Ioc (I : partition_box ι) :
  (⋃ s, (I.split_center s).Ioc) = I.Ioc :=
subset.antisymm (Union_subset $ λ s, I.split_center_le s) $
  λ y hy, mem_Union.2 ⟨{i | _ < y i}, mem_split_center_Ioc.2 ⟨hy, λ i, iff.rfl⟩⟩

@[simp] lemma upper_sub_lower_split_center (I : partition_box ι) (s : set ι) (i : ι) :
  (I.split_center s).upper i - (I.split_center s).lower i = (I.upper i - I.lower i) / 2 :=
by by_cases hs : i ∈ s; field_simp [split_center, hs, mul_two, two_mul]

lemma subbox_induction_seq {p : partition_box ι → Prop} (I : partition_box ι)
  (H_ind : ∀ J ≤ I, (∀ s, p (J.split_center s)) → p J) :
  ∃ J : ℕ → partition_box ι, J 0 = I ∧ (∀ n, J n ≤ I) ∧ (∀ n, J (n + 1) ≤ J n) ∧
    (∀ n i, (J n).upper i - (J n).lower i = (I.upper i - I.lower i) / 2 ^ n) ∧ ∀ n, p (J n) → p I :=
begin
  choose! s hs using λ J hJ, forall_imp_iff_exists_imp.1 (H_ind J hJ), clear H_ind,
  set f : partition_box ι → partition_box ι := λ J, J.split_center (s J),
  refine ⟨λ n, f^[n] I, rfl, _⟩,
  have : ∀ n, f^[n + 1] I ≤ (f^[n] I),
  { intro n, rw iterate_succ_apply', apply split_center_le },
  simp only [← forall_and_distrib, this, true_and],
  apply nat.rec, { simp },
  rintro n ⟨Hle, Hsub, Himp⟩,
  refine ⟨(this n).trans Hle, λ i, _, λ h, Himp (hs _ Hle _)⟩,
  { simp [iterate_succ_apply', Hsub, pow_succ', div_div_eq_div_mul] },
  { rwa iterate_succ_apply' at h }
end

@[elab_as_eliminator]
lemma subbox_induction_on {p : partition_box ι → Prop} (I : partition_box ι)
  (H_ind : ∀ J ≤ I, (∀ s, p (J.split_center s)) → p J)
  (H_nhds : ∀ z ∈ I.Icc, ∃ (U ∈ 𝓝[I.Icc] z), ∀ (J ≤ I) (n : ℕ),
    z ∈ J.Icc → J.Icc ⊆ U → (∀ i, J.upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ n) → p J) :
  p I :=
begin
  rcases I.subbox_induction_seq H_ind with ⟨J, hI, Hle, H_mono', H_sub, H_imp⟩,
  set z : ι → ℝ := ⨆ n, (J n).lower,
  have hz : ∀ n, z ∈ (J n).Icc,
    from mem_Inter.1 (csupr_mem_Inter_Icc_of_mono_decr_Icc_nat (λ n, le_iff_Icc.1 $ H_mono' n)
      (λ n, (J n).lower_le_upper)),
  have H_mono : monotone (order_dual.to_dual ∘ J), from monotone_nat_of_le_succ H_mono',
  have mono_l : monotone (λ n, (J n).lower), from monotone_lower.order_dual.comp H_mono,
  have mono_u : monotone (λ n, order_dual.to_dual $ (J n).upper),
    from monotone_upper.order_dual.comp H_mono,
  have Jl_mem : ∀ n, (J n).lower ∈ I.Icc,
    from λ n, hI.symm ▸ (le_iff_Icc.1 (Hle n)) (J n).lower_mem_Icc,
  have Ju_mem : ∀ n, (J n).upper ∈ I.Icc,
    from λ n, hI.symm ▸ (le_iff_Icc.1 (Hle n)) (J n).upper_mem_Icc,
  rcases H_nhds z (hI ▸ hz 0) with ⟨U, hUz, hU⟩,
  have Hl : tendsto (λ n, (J n).lower) at_top (𝓝 z),
    from tendsto_at_top_csupr_pi' mono_l ⟨I.upper, λ x ⟨n, hn⟩, hn ▸ (Jl_mem n).2⟩,
  have Hu : tendsto (λ n, (J n).upper) at_top (𝓝 z),
  { suffices : tendsto (λ n, (J n).upper - (J n).lower) at_top (𝓝 0),
      by simpa using Hl.add this,
    refine tendsto_pi.2 (λ i, _),
    simpa [H_sub] using tendsto_const_nhds.div_at_top
      (tendsto_pow_at_top_at_top_of_one_lt (@one_lt_two ℝ _ _)) },
  replace Hl : tendsto (λ n, (J n).lower) at_top (𝓝[Icc I.lower I.upper] z),
    from tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ Hl
      (eventually_of_forall Jl_mem),
  replace Hu : tendsto (λ n, (J n).upper) at_top (𝓝[Icc I.lower I.upper] z),
    from tendsto_nhds_within_of_tendsto_nhds_of_eventually_within _ Hu
      (eventually_of_forall Ju_mem),
  rcases (tendsto_lift'.1 (Hl.Icc Hu) U hUz).exists with ⟨n, hUn⟩,
  exact H_imp n (hU (J n) (Hle n) n (hz n) hUn (H_sub n))
end

/-
def pi_box (I : partition_box ι) (s t : ι → finset ℝ) :
  part (partition_box ι) :=
{ dom := ∀ i, (insert (I.lower i) (s i)).max' (finset.insert_nonempty _ _) <
    (insert (I.upper i) (t i)).min' (finset.insert_nonempty _ _),
  get := λ H, ⟨_, _, H⟩ }

lemma mem_Ioc_iff_of_mem_pi_box {s t : ι → finset ℝ} (H : J ∈ I.pi_box s t) {x : ι → ℝ} :
  x ∈ J.Ioc ↔ x ∈ I.Ioc ∧ (∀ i (z ∈ s i), z < x i) ∧ ∀ i (z ∈ t i), x i ≤ z :=
begin
  rcases H with ⟨H, rfl⟩,
  simp [pi_box, mem_Ioc, forall_and_distrib, and_assoc, and_comm, and.left_comm]
end

lemma mem_pi_box_get_Ioc_iff {s t : ι → finset ℝ} (H : (I.pi_box s t).dom) {x : ι → ℝ} :
  x ∈ ((I.pi_box s t).get H).Ioc ↔ x ∈ I.Ioc ∧ (∀ i (z ∈ s i), z < x i) ∧ ∀ i (z ∈ t i), x i ≤ z :=
mem_Ioc_iff_of_mem_pi_box (part.get_mem H)

lemma le_of_mem_pi_box {s t : ι → finset ℝ} (H : J ∈ I.pi_box s t) : J ≤ I :=
λ x hx, ((mem_Ioc_iff_of_mem_pi_box H).1 hx).1

lemma pi_box_get_le {s t : ι → finset ℝ} (H : (I.pi_box s t).dom) : (I.pi_box s t).get H ≤ I :=
le_of_mem_pi_box $ part.get_mem H

lemma pi_box_dom_iff {s t : ι → finset ℝ} :
  (I.pi_box s t).dom ↔ (∀ i (x ∈ s i), x < I.upper i) ∧
    (∀ i (x ∈ t i), I.lower i < x) ∧ (∀ i (x ∈ s i) (y ∈ t i), x < y) :=
begin
  dsimp only [pi_box],
  simp [I.lower_lt_upper, max'_lt_iff, forall_and_distrib, and_comm, and_assoc, and.left_comm]
end

lemma pi_box_dom_iff_ex {s t : ι → finset ℝ} :
  (I.pi_box s t).dom ↔ ∃ x ∈ I.Ioc, (∀ i (z ∈ s i), z < (x : _) i) ∧ (∀ i (z ∈ t i), x i ≤ z) :=
begin
  refine ⟨λ H, _, _⟩,
  { have : ((I.pi_box s t).get H).upper ∈ ((I.pi_box s t).get H).Ioc,
      from upper_mem_Ioc _,
    exact ⟨_, pi_box_get_le H this, ((mem_pi_box_get_Ioc_iff H).1 this).2⟩ },
  { rintro ⟨x, hx, hs, ht⟩,
    exact pi_box_dom_iff.2 ⟨λ i z hz, (hs i z hz).trans_le (hx i).2,
      λ i z hz, (hx i).1.trans_le (ht i z hz),
      λ i zs hzs zt hzt, (hs i zs hzs).trans_le (ht i zt hzt)⟩ }
end

lemma ex_mem_pi_box_mem_Ioc_iff {s t : ι → finset ℝ} {x : ι → ℝ} :
  (∃ J ∈ I.pi_box s t, x ∈ (J : _).Ioc) ↔
    x ∈ I.Ioc ∧ (∀ i (z ∈ s i), z < x i) ∧ ∀ i (z ∈ t i), x i ≤ z :=
begin
  refine ⟨λ ⟨J, hJ, hx⟩, (mem_Ioc_iff_of_mem_pi_box hJ).1 hx, λ H, _⟩,
  have : (I.pi_box s t).dom, from pi_box_dom_iff_ex.2 ⟨x, H.1, H.2⟩,
  exact ⟨part.get _ this, part.get_mem this, (mem_pi_box_get_Ioc_iff _).2 H⟩
end
-/

def pi_box (I : partition_box ι) (s : ι → finset ℝ) (x : I.Ioc) : partition_box ι :=
{ lower :=
    λ i, (insert (I.lower i) $ (s i).filter (λ y, y < x.1 i)).max' (finset.insert_nonempty _ _),
  upper :=
    λ i, (insert (I.upper i) $ (s i).filter (λ y, x.1 i ≤ y)).min' (finset.insert_nonempty _ _),
  lower_lt_upper := λ i,
    begin
      simp only [max'_lt_iff, lt_min'_iff, forall_mem_insert, mem_filter],
      exact ⟨⟨I.lower_lt_upper i, λ y hy, hy.2.trans_le (x.2 i).2⟩,
        λ y hy, ⟨(x.2 i).1.trans_le hy.2, λ z hz, hz.2.trans_le hy.2⟩⟩
    end }

lemma mem_pi_box_Ioc_iff' (I : partition_box ι) (s : ι → finset ℝ) (x : I.Ioc) {y : ι → ℝ} :
  y ∈ (I.pi_box s x).Ioc ↔ y ∈ I.Ioc ∧ ∀ i (z ∈ s i), z < x.1 i ↔ z < y i :=
by simp only [pi_box, mem_Ioc, set.mem_Ioc, max'_lt_iff, le_min'_iff,
  forall_mem_insert, mem_filter, ← forall_and_distrib, and_imp,
  le_imp_le_iff_lt_imp_lt, ← iff_def, and_assoc, and.left_comm]

@[simp] lemma pi_box_empty (I : partition_box ι) (x : I.Ioc) : I.pi_box (λ _, ∅) x = I :=
Ioc_injective $ set.ext $ λ y, by simp [mem_pi_box_Ioc_iff']

lemma pi_box_filter_Ioo (I : partition_box ι) (s : ι → finset ℝ) :
  I.pi_box (λ i, (s i).filter (λ x, x ∈ Ioo (I.lower i) (I.upper i))) = I.pi_box s :=
begin
  refine funext (λ x, Ioc_injective $ set.ext $ λ y, _),
  simp only [mem_pi_box_Ioc_iff', mem_filter, and_imp],
  refine and_congr_right (λ hy, forall_congr $ λ i, forall_congr $ λ z, forall_congr $
    λ hz, imp_iff_right_iff.2 _),
  simp_rw [mem_Ioo, or_iff_not_imp_left, not_and_distrib, not_lt],
  rintro (hz|hz),
  { simp only [hz.trans_lt (x.2 i).1, hz.trans_lt (hy i).1] },
  { simp only [((x.2 i).2.trans hz).not_lt, ((hy i).2.trans hz).not_lt] }
end

lemma mem_pi_box_Ioc_iff (I : partition_box ι) (s : ι → finset ℝ) {x y : I.Ioc} :
  (y : ι → ℝ) ∈ (I.pi_box s x).Ioc ↔ ∀ i (z ∈ s i), z < x.1 i ↔ z < y.1 i :=
by simp only [mem_pi_box_Ioc_iff', y.coe_prop, true_and, subtype.val_eq_coe]

lemma mem_pi_box_Ioc_self (I : partition_box ι) (s : ι → finset ℝ) (x : I.Ioc) :
  (x : ι → ℝ) ∈ (I.pi_box s x).Ioc :=
(I.mem_pi_box_Ioc_iff s).2 $ λ i z hz, iff.rfl

lemma pi_box_le (I : partition_box ι) (s : ι → finset ℝ) (x : I.Ioc) : I.pi_box s x ≤ I :=
λ y hy, ((I.mem_pi_box_Ioc_iff' s x).1 hy).1

lemma mem_pi_box_Ioc_tfae (I : partition_box ι) (s : ι → finset ℝ) (x y : I.Ioc) :
  tfae [↑y ∈ (I.pi_box s x).Ioc,
    ↑x ∈ (I.pi_box s y).Ioc,
    ∀ i (z ∈ s i), z < x.1 i ↔ z < y.1 i,
    ∀ i, (s i).filter (λ z, z < x.1 i) = (s i).filter (λ z, z < y.1 i),
    I.pi_box s x = I.pi_box s y,
    ((I.pi_box s x).Ioc ∩ (I.pi_box s y).Ioc).nonempty] :=
begin
  tfae_have : 1 ↔ 3, from I.mem_pi_box_Ioc_iff s,
  tfae_have : 1 ↔ 2, by simp only [mem_pi_box_Ioc_iff, *, iff.comm],
  tfae_have : 3 ↔ 4, by simp only [finset.ext_iff, mem_filter, and.congr_right_iff],
  tfae_have : 5 → 1, from λ h, h.symm ▸ I.mem_pi_box_Ioc_self s y,
  tfae_have : 1 → 6, from λ H, ⟨y, H, I.mem_pi_box_Ioc_self s y⟩,
  tfae_have : 6 → 5,
  { rintro ⟨z, hx, hy⟩,
    rw mem_pi_box_Ioc_iff' at hx hy,
    refine Ioc_injective (set.ext $ λ z', _),
    simp only [mem_pi_box_Ioc_iff', hx.2, hy.2] { contextual := tt } },
  tfae_finish
end

lemma pi_box_eq_of_nonempty_inter_Ioc (I : partition_box ι) (s : ι → finset ℝ) {x y : I.Ioc}
  (H : ((I.pi_box s x).Ioc ∩ (I.pi_box s y).Ioc).nonempty) :
  I.pi_box s x = I.pi_box s y :=
((mem_pi_box_Ioc_tfae I s x y).out 4 5).mpr H

lemma pi_box_eq_iff_mem_Ioc (I : partition_box ι) (s : ι → finset ℝ) {x y : I.Ioc} :
  I.pi_box s x = I.pi_box s y ↔ ↑x ∈ (I.pi_box s y).Ioc :=
(mem_pi_box_Ioc_tfae I s x y).out 4 1

lemma pi_box_eq_of_le_of_mem {I J : partition_box ι} {s : ι → finset ℝ} {x : I.Ioc}
  (Hle : I ≤ J) (Hmem₁ : ∀ i, I.lower i ∈ s i) (Hmem₂ : ∀ i, I.upper i ∈ s i) :
  I.pi_box s x = J.pi_box s ⟨x, Hle x.2⟩ :=
begin
  refine Ioc_injective (set.ext $ λ y, _),
  simp only [mem_pi_box_Ioc_iff'],
  refine and_congr_left (λ Hy, ⟨λ h, Hle h, λ h i, ⟨_, _⟩⟩),
  { exact (Hy i _ (Hmem₁ i)).mp (x.2 i).1 },
  { exact le_of_not_lt (λ Hlt, (x.2 i).2.not_lt $ (Hy i _ (Hmem₂ i)).mpr Hlt) }
end

lemma pi_box_update_insert (I : partition_box ι) (s : ι → finset ℝ) (i : ι)
  (x : ℝ) (y : I.Ioc) :
  I.pi_box (update s i (insert x (s i))) y =
    if h : x ∈ Ioo ((I.pi_box s y).lower i) ((I.pi_box s y).upper i) then
      if y.1 i ≤ x then (I.pi_box s y).split_lower i ⟨x, h⟩
      else (I.pi_box s y).split_upper i ⟨x, h⟩
    else I.pi_box s y :=
begin
  -- TODO: Why does `split_ifs` fail after `refine Ioc_injective (set.ext $ λ z, _)`?
  -- TODO: Why does `simp` fail to use `forall_and_distrib`?
  split_ifs with hx hi; refine Ioc_injective (set.ext $ λ z, _);
    simp only [mem_pi_box_Ioc_iff', finset.mem_update_insert, or_imp_distrib, and_imp,
      mem_split_lower_Ioc, mem_split_upper_Ioc, subtype.coe_mk, and_assoc, and.congr_right_iff];
    refine λ hz, ⟨λ H, _, λ H, _⟩,
  { refine ⟨λ j z' hz', (H j z').1 hz', le_of_not_lt _⟩,
    rw [← (H i x).2 rfl rfl], exact hi.not_lt },
  { refine λ j z', ⟨H.1 j z', _⟩,
    rintro rfl rfl, simp only [H.2.not_lt, hi.not_lt] },
  { exact ⟨λ j z' hz', (H j z').1 hz', ((H i x).2 rfl rfl).1 $ not_le.1 hi⟩ },
  { refine λ j z', ⟨H.1 j z', _⟩,
    rintro rfl rfl, simp only [not_le.1 hi, H.2] },
  { exact λ j z', (H j z').1 },
  { refine λ j z', ⟨H j z', _⟩,
    rintro rfl rfl,
    lift z to I.Ioc using hz,
    rw [← subtype.val_eq_coe, ← mem_pi_box_Ioc_iff, ← pi_box_eq_iff_mem_Ioc] at H,
    rw [mem_Ioo, not_and_distrib, not_lt, not_lt] at hx, cases hx,
    { simp only [subtype.val_eq_coe, hx.trans_lt (I.mem_pi_box_Ioc_self s y j).1],
      rw ← H at hx, simp only [hx.trans_lt (I.mem_pi_box_Ioc_self s z j).1] },
    { simp only [subtype.val_eq_coe, ((I.mem_pi_box_Ioc_self s y j).2.trans hx).not_lt],
      rw ← H at hx, simp only [((I.mem_pi_box_Ioc_self s z j).2.trans hx).not_lt] } }
end

lemma disjoint_pi_box_Ioc (I : partition_box ι) (s : ι → finset ℝ) {x y : I.Ioc}
  (H : I.pi_box s x ≠ I.pi_box s y) : disjoint (I.pi_box s x).Ioc (I.pi_box s y).Ioc :=
λ z hz, H $ I.pi_box_eq_of_nonempty_inter_Ioc s ⟨z, hz⟩

lemma finite_range_pi_box [fintype ι] (I : partition_box ι) (s : ι → finset ℝ) :
  finite (set.range $ I.pi_box s) :=
begin
  set f : set.range (I.pi_box s) →
    finset.univ.pi (λ i : ι, (s i).powerset) :=
    λ J, ⟨λ i hi, (s i).filter (λ z, z < J.2.some.1 i),
      finset.mem_pi.2 $ λ i hi, finset.mem_powerset.2 $ filter_subset _ _⟩,
  have : injective f,
  { intros J₁ J₂ H,
    simp only [f, subtype.mk_eq_mk, function.funext_iff, finset.mem_univ, forall_true_left] at H,
    rw [subtype.ext_iff, ← J₁.coe_prop.some_spec, ← J₂.coe_prop.some_spec],
    exact ((I.mem_pi_box_Ioc_tfae s J₁.2.some J₂.2.some).out 3 4).1 H },
  exact ⟨fintype.of_injective f this⟩
end

lemma pi_box_center (I : partition_box ι) (x : I.Ioc) :
  I.pi_box (λ i, {(I.lower i + I.upper i) / 2}) x =
    I.split_center {i | (I.lower i + I.upper i) / 2 < x.1 i} :=
begin
  refine Ioc_injective (set.ext $ λ y, _),
  simp only [mem_pi_box_Ioc_iff', mem_split_center_Ioc, mem_set_of_eq, finset.mem_singleton],
  -- TODO: why `simp` fails to use `forall_eq`?
  exact and_congr iff.rfl (forall_congr $ λ i, forall_eq.trans iff.comm)
end

end partition_box

@[ext, protect_proj]
structure pi_partition (I : partition_box ι) :=
(boxes : finset (partition_box ι))
(bUnion_boxes_Ioc : (⋃ J ∈ boxes, partition_box.Ioc J) = I.Ioc)
(disjoint_Ioc : set.pairwise_on (boxes : set (partition_box ι)) (disjoint on partition_box.Ioc))

attribute [simp] pi_partition.bUnion_boxes_Ioc

namespace pi_partition

variables {I J J' : partition_box ι} (π : pi_partition I) {x : ι → ℝ}

open finset

lemma le_of_mem (hJ : J ∈ π.boxes) : J ≤ I :=
partition_box.le_iff_Ioc.2 $ π.bUnion_boxes_Ioc ▸ set.subset_bUnion_of_mem hJ

lemma lower_le_lower (hJ : J ∈ π.boxes) : I.lower ≤ J.lower :=
(partition_box.le_iff_bounds.1 (π.le_of_mem hJ)).1

lemma upper_le_upper (hJ : J ∈ π.boxes) : J.upper ≤ I.upper :=
(partition_box.le_iff_bounds.1 (π.le_of_mem hJ)).2

lemma eq_of_mem_Ioc (h : J ∈ π.boxes) (h' : J' ∈ π.boxes) (hx : x ∈ J.Ioc) (hx' : x ∈ J'.Ioc) :
  J = J' :=
by_contra $ λ H, π.disjoint_Ioc _ h _ h' H ⟨hx, hx'⟩

protected lemma exists_unique (hx : x ∈ I.Ioc) : ∃! J ∈ π.boxes, x ∈ partition_box.Ioc J :=
begin
  simp only [← π.bUnion_boxes_Ioc, set.mem_Union] at hx,
  rcases hx with ⟨J, h, hx⟩,
  exact exists_unique.intro2 J h hx (λ J' h' hx', π.eq_of_mem_Ioc h' h hx' hx),
end

protected lemma «exists» (hx : x ∈ I.Ioc) : ∃ J ∈ π.boxes, x ∈ partition_box.Ioc J :=
(π.exists_unique hx).exists2

lemma eq_of_le_of_le {J''} (h : J ∈ π.boxes) (h' : J' ∈ π.boxes) (hle : J'' ≤ J) (hle' : J'' ≤ J') :
  J = J' :=
π.eq_of_mem_Ioc h h' (hle J''.upper_mem_Ioc) (hle' J''.upper_mem_Ioc)

lemma eq_of_le (h : J ∈ π.boxes) (h' : J' ∈ π.boxes) (hle : J ≤ J') : J = J' :=
π.eq_of_le_of_le h h' le_rfl hle

lemma exists_mem_boxes_mem_Ioc_iff {p : ∀ x, x ∈ I.Ioc → Prop} :
  (∃ (J ∈ π.boxes) (x ∈ (J : _).Ioc), p x (π.le_of_mem ‹_› ‹_›)) ↔ ∃ x ∈ I.Ioc, p x ‹_› :=
⟨λ ⟨J, hJ, x, hx, hp⟩, ⟨x, _, hp⟩,
  λ ⟨x, hx, hp⟩, let ⟨J, hJ, hx'⟩ := π.exists hx in ⟨J, hJ, x, hx', hp⟩⟩

lemma eq_of_boxes_subset {π π' : pi_partition I} (h : π.boxes ⊆ π'.boxes) : π = π' :=
ext _ _ $ subset.antisymm h $ λ J' hJ',
  let ⟨x, hx'⟩ := J'.nonempty_Ioc, ⟨J, hJ, hx⟩ := π.exists (π'.le_of_mem hJ' hx')
  in π'.eq_of_mem_Ioc (h hJ) hJ' hx hx' ▸ hJ

instance : has_le (pi_partition I) := ⟨λ π π', ∀ ⦃I⦄, I ∈ π.boxes → ∃ I' ∈ π'.boxes, I ≤ I'⟩

instance : partial_order (pi_partition I) :=
{ le := (≤),
  le_refl := λ π I hI, ⟨I, hI, le_rfl⟩,
  le_trans := λ π₁ π₂ π₃ h₁₂ h₂₃ I₁ hI₁,
    let ⟨I₂, hI₂, hI₁₂⟩ := h₁₂ hI₁, ⟨I₃, hI₃, hI₂₃⟩ := h₂₃ hI₂ in ⟨I₃, hI₃, hI₁₂.trans hI₂₃⟩,
  le_antisymm :=
    begin
      refine λ π π' h h', eq_of_boxes_subset (λ J hJ, _),
      rcases h hJ with ⟨J', hJ', hle⟩, rcases h' hJ' with ⟨J'', hJ'', hle'⟩,
      obtain rfl : J = J'', from π.eq_of_le hJ hJ'' (hle.trans hle'),
      obtain rfl : J' = J, from le_antisymm ‹_› ‹_›,
      assumption
    end }

instance : has_top (pi_partition I) :=
⟨{ boxes := {I},
   bUnion_boxes_Ioc := set_bUnion_singleton _ _,
   disjoint_Ioc := λ J₁ h₁ J₂ h₂ Hne, (Hne $ by rw [mem_singleton.1 h₁, mem_singleton.1 h₂]).elim }⟩

@[simp] lemma top_boxes : (⊤ : pi_partition I).boxes = {I} := rfl

lemma mem_top_boxes {I J : partition_box ι} : I ∈ (⊤ : pi_partition J).boxes ↔ I = J :=
mem_singleton

instance : inhabited (pi_partition I) := ⟨⊤⟩

private def sigma_boxes (πi : Π J ∈ π.boxes, pi_partition J) : finset (partition_box ι) :=
π.boxes.attach.bUnion (λ J, (πi J J.2).boxes)

private lemma mem_sigma_boxes'' (πi : Π J ∈ π.boxes, pi_partition J) {J} :
  J ∈ (sigma_boxes π πi) ↔ ∃ J' ∈ π.boxes, J ∈ (πi J' ‹_›).boxes :=
by simp [sigma_boxes, mem_bUnion, subtype.exists]; refl

private lemma coe_sigma_boxes (πi : Π J ∈ π.boxes, pi_partition J) :
  (sigma_boxes π πi : set (partition_box ι)) = ⋃ J ∈ π.boxes, (πi J ‹_›).boxes :=
set.ext $ λ J, by simp only [mem_coe, mem_sigma_boxes'', set.mem_Union]

protected def sigma (πi : Π J ∈ π.boxes, pi_partition J) : pi_partition I :=
{ boxes := sigma_boxes π πi,
  bUnion_boxes_Ioc := by simp [mem_sigma_boxes'', set.Union_comm],
  disjoint_Ioc :=
    begin
      simp only [coe_sigma_boxes, set.pairwise_on, set.mem_Union, mem_coe],
      rintro J₁' ⟨J₁, hJ₁, hJ₁'⟩ J₂' ⟨J₂, hJ₂, hJ₂'⟩ Hne x ⟨hx₁, hx₂⟩, apply Hne,
      obtain rfl : J₁ = J₂,
        from π.eq_of_mem_Ioc hJ₁ hJ₂ ((πi J₁ hJ₁).le_of_mem hJ₁' hx₁)
          ((πi J₂ hJ₂).le_of_mem hJ₂' hx₂),
      exact (πi J₁ hJ₁).eq_of_mem_Ioc hJ₁' hJ₂' hx₁ hx₂
    end }

lemma mem_sigma_boxes {πi : Π J ∈ π.boxes, pi_partition J} :
  J ∈ (π.sigma πi).boxes ↔ ∃ J' ∈ π.boxes, J ∈ (πi J' ‹J' ∈ π.boxes›).boxes :=
mem_sigma_boxes'' π πi

lemma mem_sigma_boxes' {πi : Π J ∈ π.boxes, pi_partition J} :
  J ∈ sigma_boxes π πi ↔ ∃! J' ∈ π.boxes, J ∈ (πi J' ‹J' ∈ π.boxes›).boxes :=
begin
  refine π.mem_sigma_boxes.trans ⟨_, λ h, h.exists.imp (λ J hJ, hJ.exists)⟩,
  rintro ⟨J', hJ', hJ⟩,
  refine exists_unique.intro2 J' hJ' hJ (λ J'' hJ'' h, _),
  exact π.eq_of_le_of_le hJ'' hJ' (le_of_mem _ h) (le_of_mem _ hJ)
end

lemma sigma_le (πi : Π J ∈ π.boxes, pi_partition J) : π.sigma πi ≤ π :=
λ J hJ, let ⟨J', hJ', hJ⟩ := π.mem_sigma_boxes.1 hJ in ⟨J', hJ', (πi J' hJ').le_of_mem hJ⟩

lemma forall_mem_sigma_boxes {πi : Π J ∈ π.boxes, pi_partition J}
  {p : ∀ J, J ∈ (π.sigma πi).boxes → Prop} :
  (∀ J hJ, p J hJ) ↔
    ∀ (J ∈ π.boxes) (J' ∈ (πi J ‹_›).boxes), p J' (π.mem_sigma_boxes.2 ⟨J, ‹_›, ‹_›⟩) :=
⟨λ H J hJ J' hJ', H _ _, λ H J hJ, let ⟨J', hJ', hJJ'⟩ := π.mem_sigma_boxes.1 hJ in H J' hJ' J hJJ'⟩

def restrict (π : pi_partition J) (I : partition_box ι) (H : I ≤ J) :
  pi_partition I :=
{ boxes := π.boxes.bUnion (λ J', option.to_finset $ part.to_option ⟨_, I.inter J'⟩),
  bUnion_boxes_Ioc := by simpa [part.mem_eq, ← set.inter_Union, set.Union_nonempty_self,
    set.inter_eq_left_iff_subset],
  disjoint_Ioc :=
    begin
      simp only [set.pairwise_on, mem_coe, mem_bUnion, option.mem_to_finset, part.mem_to_option],
      rintro _ ⟨J, HJ, h, rfl⟩ _ ⟨J', HJ', h', rfl⟩ Hne,
      rw [on_fun, partition_box.inter_Ioc, partition_box.inter_Ioc],
      refine ((π.disjoint_Ioc J HJ J' HJ' _).inf_left' _).inf_right' _,
      rintro rfl, exact Hne rfl
    end }

lemma mem_restrict_boxes (π : pi_partition J) {I J' : partition_box ι} (H : I ≤ J) :
  J' ∈ (π.restrict I H).boxes ↔ ∃ (J'' ∈ π.boxes) H, J' = I.inter J'' H :=
by simp [restrict, part.mem_eq, eq_comm]

instance : has_inf (pi_partition I) :=
⟨λ π π', π.sigma (λ J hJ, π'.restrict J $ π.le_of_mem hJ)⟩

lemma mem_inf_boxes (π₁ π₂ : pi_partition J) {I : partition_box ι} :
  I ∈ (π₁ ⊓ π₂).boxes ↔ ∃ (J₁ ∈ π₁.boxes) (J₂ ∈ π₂.boxes) H, I = (J₁ : _).inter J₂ H :=
π₁.mem_sigma_boxes.trans $ exists_congr $ λ J₁, exists_congr $ λ hJ₁, mem_restrict_boxes _ _

lemma inter_mem_inf (π₁ π₂ : pi_partition J) {I₁ I₂ : partition_box ι}
  (H₁ : I₁ ∈ π₁.boxes) (H₂ : I₂ ∈ π₂.boxes) (H : (I₁.Ioc ∩ I₂.Ioc).nonempty) :
  I₁.inter I₂ H ∈ (π₁ ⊓ π₂).boxes :=
(π₁.mem_inf_boxes π₂).2 ⟨I₁, H₁, I₂, H₂, H, rfl⟩

instance : semilattice_inf_top (pi_partition I) :=
{ le := (≤),
  top := ⊤,
  le_top := λ π J hJ, ⟨I, mem_singleton.2 rfl, π.le_of_mem hJ⟩,
  inf := (⊓),
  inf_le_left := λ π π', π.sigma_le _,
  inf_le_right := λ π₁ π₂ J'' hJ'',
    begin
      rcases (π₁.mem_inf_boxes π₂).1 hJ'' with ⟨J₁, mem₁, J₂, mem₂, H, rfl⟩,
      exact ⟨J₂, mem₂, partition_box.inter_le_right _⟩
    end,
  le_inf := λ π π₁ π₂ h₁ h₂ J hJ,
    begin
      rcases h₁ hJ with ⟨J₁, mem₁, le₁⟩, rcases h₂ hJ with ⟨J₂, mem₂, le₂⟩,
      refine ⟨_, π₁.inter_mem_inf π₂ mem₁ mem₂ _, (partition_box.le_inter_iff _).2 ⟨le₁, le₂⟩⟩,
      exact ⟨J.upper, le₁ J.upper_mem_Ioc, le₂ J.upper_mem_Ioc⟩
    end,
  .. pi_partition.partial_order }

def split_single (I : partition_box ι) (i : ι) (x : set.Ioo (I.lower i) (I.upper i)) :
  pi_partition I :=
{ boxes := {I.split_lower i x, I.split_upper i x},
  bUnion_boxes_Ioc :=
    by rw [set_bUnion_insert, set_bUnion_singleton, partition_box.union_Ioc_split],
  disjoint_Ioc :=
    begin
      rw [coe_insert, coe_singleton, set.pairwise_on_pair_of_symmetric],
      exacts [λ _, I.disjoint_Ioc_split _ _, λ J₁ J₂ h, h.symm]
    end }

@[simp] lemma mem_split_single_boxes (I : partition_box ι) (i : ι)
  (x : set.Ioo (I.lower i) (I.upper i)) {J : partition_box ι} :
  J ∈ (split_single I i x).boxes ↔ J = I.split_lower i x ∨ J = I.split_upper i x :=
by simp [split_single]

def pi [fintype ι] (I : partition_box ι) (s : ι → finset ℝ) :
  pi_partition I :=
{ boxes := (I.finite_range_pi_box s).to_finset,
  bUnion_boxes_Ioc :=
    begin
      ext1 x,
      simp only [set.finite.mem_to_finset, set.mem_Union, exists_prop, set.exists_range_iff'],
      exact ⟨λ ⟨J, hx⟩, I.pi_box_le _ _ hx, λ hx, ⟨⟨x, hx⟩, I.mem_pi_box_Ioc_self _ _⟩⟩
    end,
  disjoint_Ioc :=
    begin
      rw set.finite.coe_to_finset,
      rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ Hne,
      exact I.disjoint_pi_box_Ioc s Hne
    end }

@[simp] lemma mem_pi_boxes [fintype ι] {I J : partition_box ι} {s : ι → finset ℝ} :
  J ∈ (pi I s).boxes ↔ ∃ x : I.Ioc, I.pi_box s x = J :=
set.finite.mem_to_finset _

lemma pi_filter_Ioo [fintype ι] (I : partition_box ι) (s : ι → finset ℝ) :
  pi I (λ i, (s i).filter $ λ z, z ∈ set.Ioo (I.lower i) (I.upper i)) = pi I s :=
by { ext J, simp only [mem_pi_boxes, partition_box.pi_box_filter_Ioo] }

@[simp] lemma pi_empty [fintype ι] (I : partition_box ι) :
  pi I (λ _, ∅) = ⊤ :=
by { ext J, have : ∃ x, x ∈ I.Ioc, from ⟨_, I.upper_mem_Ioc⟩, simp [this, eq_comm] }

lemma sigma_pi_of_subset [fintype ι] (π : pi_partition I) (s : ι → finset ℝ)
  (Hl : ∀ (J ∈ π.boxes) i, (J : _).lower i ∈ s i) (Hu : ∀ (J ∈ π.boxes) i, (J : _).upper i ∈ s i) :
  π.sigma (λ J hJ, pi J s) = pi I s :=
begin
  refine eq_of_boxes_subset (π.forall_mem_sigma_boxes.2 $ λ J hJ J' hJ', _),
  rcases mem_pi_boxes.1 hJ' with ⟨⟨x, hx⟩, rfl⟩,
  suffices : partition_box.pi_box J s ⟨x, hx⟩ = I.pi_box s ⟨x, _⟩,
  { rw this, exact mem_pi_boxes.2 ⟨⟨x, le_of_mem _ hJ hx⟩, rfl⟩ },
  exact partition_box.pi_box_eq_of_le_of_mem _ (Hl J hJ) (Hu J hJ)
end

lemma exists_sigma_pi_eq [fintype ι] (π₁ π₂ : pi_partition I) :
  ∃ s : ι → finset ℝ, π₁.sigma (λ J hJ, pi J s) = pi I s ∧ π₂.sigma (λ J hJ, pi J s) = pi I s :=
by refine ⟨λ i, (π₁.boxes.image (λ J : partition_box ι, J.lower i)) ∪
    (π₁.boxes.image (λ J : partition_box ι, J.upper i)) ∪
    (π₂.boxes.image (λ J : partition_box ι, J.lower i)) ∪
    (π₂.boxes.image (λ J : partition_box ι, J.upper i)),
  π₁.sigma_pi_of_subset _ _ _, π₂.sigma_pi_of_subset _ _ _⟩;
    intros J hJ i; simp [mem_image_of_mem _ hJ]

lemma pi_update_insert [fintype ι] (I : partition_box ι) (s : ι → finset ℝ) (i : ι) (x : ℝ) :
  pi I (update s i (insert x (s i))) = (pi I s).sigma
    (λ J hJ, if hx : x ∈ set.Ioo (J.lower i) (J.upper i) then split_single J i ⟨x, hx⟩ else ⊤) :=
begin
  refine (eq_of_boxes_subset $ λ J, _),
  simp only [mem_pi_boxes, partition_box.pi_box_update_insert, mem_sigma_boxes, exists_prop],
  rintro ⟨y, hy⟩,
  refine ⟨_, ⟨y, rfl⟩, _⟩,
  -- TODO: `split_ifs` fails; why?
  by_cases h₁ : x ∈ set.Ioo ((I.pi_box s y).lower i) ((I.pi_box s y).upper i),
  { rw [dif_pos h₁] at hy ⊢,
    rw mem_split_single_boxes,
    by_cases h₂ : y.1 i ≤ x,
    { rw if_pos h₂ at hy, exact or.inl hy.symm },
    { rw if_neg h₂ at hy, exact or.inr hy.symm } },
  { rw dif_neg h₁ at hy ⊢,
    exact mem_top_boxes.2 hy.symm }
end

lemma split_sigma_induction_pi [fintype ι] {p : Π J : partition_box ι, pi_partition J → Prop}
  (H_top : ∀ J ≤ I, p J ⊤) (H_split : ∀ (J ≤ I) i x, p J (split_single J i x))
  (H_sigma : ∀ (J ≤ I) (π : pi_partition J) (πi : Π J' ∈ π.boxes, pi_partition J'), p J π →
    (∀ J' ∈ π.boxes, p J' (πi J' ‹_›)) → p J (π.sigma πi))
  (s : ι → finset ℝ) {J : partition_box ι} (hJ : J ≤ I) :
  p J (pi J s) :=
begin
  refine finset.induction_on_pi s _ _, { simp [H_top J hJ] },
  clear s, intros s i a ha ihs,
  rw pi_update_insert,
  refine H_sigma J hJ _ _ ihs (λ J' hJ', _),
  have : J' ≤ I, from (le_of_mem _ hJ').trans hJ, 
  split_ifs,
  exacts [H_split _ this _ _, H_top _ this]
end

lemma split_sigma_induction [fintype ι] {p : Π J : partition_box ι, pi_partition J → Prop}
  (H_top : ∀ J ≤ I, p J ⊤) (H_split : ∀ (J ≤ I) i x, p J (split_single J i x))
  (H_sigma : ∀ (J ≤ I) (π : pi_partition J) (πi : Π J' ∈ π.boxes, pi_partition J'), p J π →
    (∀ J' ∈ π.boxes, p J' (πi J' ‹_›)) → p J (π.sigma πi))
  (H_sigma_rev : ∀ (J ≤ I) (π : pi_partition J) (πi : Π J' ∈ π.boxes, pi_partition J'),
    (∀ J' ∈ π.boxes, p J' (πi J' ‹_›)) → p J (π.sigma πi) → p J π)
  {J : partition_box ι} (hJ : J ≤ I) (π : pi_partition J) :
  p J π :=
begin
  have := split_sigma_induction_pi H_top H_split H_sigma,
  rcases exists_sigma_pi_eq π π with ⟨s, hs, -⟩,
  refine H_sigma_rev J hJ π (λ J' _, pi J' s) (λ J' hJ', this _ ((π.le_of_mem hJ').trans hJ)) _,
  rw hs,
  exact this _ hJ
end

def split_center [fintype ι] (I : partition_box ι) : pi_partition I :=
{ boxes := (finset.univ : finset (set ι)).image I.split_center,
  bUnion_boxes_Ioc := by simp [I.Union_split_center_Ioc],
  disjoint_Ioc :=
    begin
      simp only [coe_image, coe_univ, set.image_univ],
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩ Hne,
      exact I.disjoint_split_center_Ioc (mt (congr_arg I.split_center) Hne)
    end }

@[simp] lemma mem_split_center_boxes [fintype ι] {I J : partition_box ι} :
  J ∈ (split_center I).boxes ↔ ∃ s, J = I.split_center s :=
by simp [split_center, @eq_comm _ J]

@[simp] lemma coe_split_center_boxes [fintype ι] (I : partition_box ι) :
  ↑(split_center I).boxes = set.range I.split_center :=
by simp [split_center]

def equiv_split_center [fintype ι] (I : partition_box ι) :
  set ι ≃ (split_center I).boxes :=
(equiv.of_injective _ I.injective_split_center).trans $ equiv.set.of_eq $
  (coe_split_center_boxes I).symm

@[simp] lemma pi_center [fintype ι] (I : partition_box ι) :
  pi I (λ i, {(I.lower i + I.upper i) / 2}) = split_center I :=
begin
  refine eq_of_boxes_subset (λ J, _),
  simp only [mem_pi_boxes, mem_split_center_boxes, I.pi_box_center],
  rintro ⟨x, rfl⟩, exact ⟨_, rfl⟩
end

/-
def is_almost_homothetic (π : pi_partition I) (r : set.Ioi (1 : ℝ)) :=
  ∀ (J ∈ π.boxes) (i j : ι), ((J : _).upper i - J.lower i) / (J.upper j - J.lower j) <
    r * ((I.upper i - I.lower i) / (I.upper j - I.lower j))

def is_homothetic (π : pi_partition I) : Prop :=
∀ J ∈ π.boxes, ∃ ε : ℝ, (J : _).upper - J.lower = ε • (I.upper - I.lower)

lemma is_homothetic.exists_pos {π : pi_partition I} (h : π.is_homothetic) :
  ∀ J ∈ π.boxes, ∃ ε : ℝ, 0 < ε ∧ (J : _).upper - J.lower = ε • (I.upper - I.lower) :=
begin
  intros J hJ, rcases h J hJ with ⟨ε, hε⟩,
  rcases is_empty_or_nonempty ι with hι|⟨⟨i⟩⟩,
  { exactI ⟨1, zero_lt_one, subsingleton.elim _ _⟩ },
  { refine ⟨ε, _, hε⟩,
    have := congr_fun hε i, dsimp at this,
    rw [← div_eq_iff (sub_pos.2 $ I.lower_lt_upper i).ne'] at this, rw ← this,
    simp only [div_pos, sub_pos.2, partition_box.lower_lt_upper] }
end

lemma is_homothetic.almost {π : pi_partition I} (h : π.is_homothetic) (r : set.Ioi (1 : ℝ)) :
  π.is_almost_homothetic r :=
begin
  intros J hJ i j,
  rcases h.exists_pos J hJ with ⟨ε, ε0, hε⟩,
  simp only [funext_iff] at hε, dsimp at hε,
  rw [hε, hε, mul_div_mul_left _ _ ε0.ne'],
  refine lt_mul_of_one_lt_left _ r.2,
  simp only [div_pos, sub_pos.2, partition_box.lower_lt_upper]
end
-/

end pi_partition

structure marked_pi_partition (I : partition_box ι) extends pi_partition I :=
(mark : Π (J ∈ boxes), ι → ℝ)
(mark_mem_Icc : ∀ J ∈ boxes, mark J ‹_› ∈ I.Icc)

attribute [simp] marked_pi_partition.mark_mem_Icc

namespace pi_partition

variables {I : partition_box ι}

private def sigma_mark (π : pi_partition I) (πi : Π J ∈ π.boxes, marked_pi_partition J)
  (J : partition_box ι) (hJ : J ∈ (π.sigma (λ J hJ, (πi J hJ).to_pi_partition)).boxes) : ι → ℝ :=
have ∃ J' ∈ π.boxes, J ∈ (πi J' ‹_›).boxes, from π.mem_sigma_boxes.1 hJ,
(πi this.some this.some_spec.fst).mark J this.some_spec.snd

private lemma sigma_mark_def (π : pi_partition I) (πi : Π J ∈ π.boxes, marked_pi_partition J)
  {J J' : partition_box ι} (hJ : J ∈ π.boxes) (hJ' : J' ∈ (πi J hJ).boxes) :
  sigma_mark π πi J' (π.mem_sigma_boxes.2 ⟨J, hJ, hJ'⟩) = (πi J hJ).mark J' hJ' :=
begin
  unfold sigma_mark,
  have : ∃ J ∈ π.boxes, J' ∈ (πi J ‹_›).boxes, from ⟨J, hJ, hJ'⟩,
  suffices : this.some = J, by subst J,
  exact (π.mem_sigma_boxes'.1 (π.mem_sigma_boxes.2 this)).unique2
    this.some_spec.fst this.some_spec.snd hJ hJ'
end

def sigma_marked (π : pi_partition I) (πi : Π J ∈ π.boxes, marked_pi_partition J) :
  marked_pi_partition I :=
{ to_pi_partition := π.sigma (λ J hJ, (πi J hJ).to_pi_partition),
  mark := sigma_mark π πi,
  mark_mem_Icc := π.forall_mem_sigma_boxes.2 $ λ J hJ J' hJ',
    by { rw sigma_mark_def,
         exact partition_box.le_iff_Icc.1 (π.le_of_mem hJ) ((πi _ _).mark_mem_Icc _ _) } }

@[simp] lemma mark_sigma_marked (π : pi_partition I) (πi : Π J ∈ π.boxes, marked_pi_partition J)
  {J J' : partition_box ι} (hJ : J ∈ π.boxes) (hJ' : J' ∈ (πi J hJ).boxes) :
  (π.sigma_marked πi).mark J' (π.mem_sigma_boxes.2 ⟨J, hJ, hJ'⟩) = (πi J hJ).mark J' hJ' :=
sigma_mark_def π πi hJ hJ'

end pi_partition

namespace marked_pi_partition

def single_box (I : partition_box ι) (x : ι → ℝ) (h : x ∈ I.Icc) :
  marked_pi_partition I :=
⟨⊤, λ J _, x, λ J hJ, h⟩

instance (I : partition_box ι) : has_top (marked_pi_partition I) :=
⟨single_box I I.upper I.upper_mem_Icc⟩

instance (I : partition_box ι) : inhabited (marked_pi_partition I) := ⟨⊤⟩

lemma forall_mem_single {p : partition_box ι → (ι → ℝ) → Prop} {I : partition_box ι} {x : ι → ℝ}
  (h : x ∈ I.Icc) :
  (∀ J ∈ (single_box I x h).boxes, p J ((single_box I x h).mark J ‹_›)) ↔ p I x :=
by simp [single_box]

section

variables {I : partition_box ι} (π : marked_pi_partition I) {x : ι → ℝ}

def is_Henstock : Prop := ∀ J ∈ π.boxes, π.mark J ‹_› ∈ J.Icc

lemma is_Henstock_single (h : x ∈ I.Icc) : is_Henstock (single_box I x h) :=
(forall_mem_single h).2 h

lemma _root_.pi_partition.is_Henstock_sigma_marked (π : pi_partition I)
  (πi : Π J ∈ π.boxes, marked_pi_partition J) (H : ∀ J ∈ π.boxes, (πi J ‹_›).is_Henstock) :
  (π.sigma_marked πi).is_Henstock :=
π.forall_mem_sigma_boxes.2 $ λ J hJ J' hJ', by simp [H J hJ J' hJ']

end

variables [fintype ι] {I : partition_box ι} (π : marked_pi_partition I) {x : ι → ℝ}
  {r : (ι → ℝ) → ℝ≥0∞}

open emetric

def is_subordinate (π : marked_pi_partition I) (r : (ι → ℝ) → ℝ≥0∞) :=
∀ (J ∈ π.boxes), (J : _).Icc ⊆ closed_ball (π.mark J ‹_›) (r $ π.mark J ‹_›)

lemma is_subordinate_single (h : x ∈ I.Icc) :
  (single_box I x h).is_subordinate r ↔ I.Icc ⊆ closed_ball x (r x) :=
@forall_mem_single _ (λ J z, (J : _).Icc ⊆ closed_ball z (r z)) _ _ h

lemma _root_.pi_partition.is_subordinate_sigma_marked (π : pi_partition I) {r : (ι → ℝ) → ℝ≥0∞}
  (πi : Π J ∈ π.boxes, marked_pi_partition J) (H : ∀ J ∈ π.boxes, (πi J ‹_›).is_subordinate r) :
  (π.sigma_marked πi).is_subordinate r :=
π.forall_mem_sigma_boxes.2 $ λ J hJ J' hJ', by simp [H J hJ J' hJ']

lemma exists_is_subordinate (r : (ι → ℝ) → ℝ≥0∞) (hr : ∀ x ∈ I.Icc, r x ≠ 0) :
  ∃ π : marked_pi_partition I, π.is_subordinate r ∧ π.is_Henstock ∧
    ∀ J ∈ π.boxes, ∃ n : ℕ, ∀ i, (J : _).upper i - J.lower i = (I.upper i - I.lower i) / 2 ^ n :=
begin
  apply partition_box.subbox_induction_on I,
  { intros J Hle H,
    have : ∀ J' ∈ (pi_partition.split_center J).boxes,
      ∃ π : marked_pi_partition J', π.is_subordinate r ∧ π.is_Henstock ∧
        ∀ J'' ∈ π.boxes, ∃ n : ℕ, ∀ i,
          (J'' : _).upper i - J''.lower i = (J'.upper i - J'.lower i) / 2 ^ n,
    { simp only [pi_partition.mem_split_center_boxes],
      rintro _ ⟨s, rfl⟩, exact H s },
    choose! πi hr hHen hsub,
    refine ⟨(pi_partition.split_center J).sigma_marked (λ J' hJ', πi J'),
      pi_partition.is_subordinate_sigma_marked _ _ hr,
      pi_partition.is_Henstock_sigma_marked _ _ hHen,
      (pi_partition.forall_mem_sigma_boxes _).2 $ λ J' hJ' J'' (hJ'' : J'' ∈ (πi J').boxes), _⟩,
    rcases hsub J' hJ' J'' hJ'' with ⟨n, hn⟩,
    rcases pi_partition.mem_split_center_boxes.1 hJ' with ⟨s, rfl⟩,
    refine ⟨n + 1, λ i, _⟩,
    simp [hn, pow_succ, div_div_eq_div_mul] },
  { intros z hz,
    have h0 : 0 < r z, from pos_iff_ne_zero.2 (hr z hz),
    refine ⟨I.Icc ∩ closed_ball z (r z),
      inter_mem_nhds_within _ (closed_ball_mem_nhds _ h0), _⟩,
    intros J Hle n Hmem HIcc Hsub,
    rw set.subset_inter_iff at HIcc,
    refine ⟨single_box _ _ Hmem, (is_subordinate_single _).2 HIcc.2, is_Henstock_single _, _⟩,
    simp only [single_box, pi_partition.mem_top_boxes, forall_eq],
    refine ⟨0, λ i, _⟩, simp }
end

lemma is_subordinate.mono {π : marked_pi_partition I} {r r' : (ι → ℝ) → ℝ≥0∞}
  (h : ∀ x ∈ I.Icc, r x ≤ r' x) (hr : π.is_subordinate r) :
  π.is_subordinate r' :=
λ J hJ x hx, closed_ball_subset_closed_ball (h _ $ π.mark_mem_Icc _ _) (hr _ _ hx)

lemma is_subordinate.ediam_le {π : marked_pi_partition I} {r : (ι → ℝ) → ℝ≥0∞}
  (h : π.is_subordinate r) {J : partition_box ι} (hJ : J ∈ π.boxes) :
  diam J.Icc ≤ 2 * r (π.mark J hJ) :=
calc diam J.Icc ≤ diam (closed_ball (π.mark J hJ) (r $ π.mark J hJ)) : diam_mono (h J hJ)
            ... ≤ 2 * r (π.mark J hJ)                                : diam_closed_ball

end marked_pi_partition

namespace box_integral

variables {E F : Type*} [normed_group E] [normed_space ℝ E] [normed_group F] [normed_space ℝ F]
  [fintype ι] {I : partition_box ι} {π : marked_pi_partition I}

open marked_pi_partition

def integral_sum (f : (ι → ℝ) → E) (vol : partition_box ι → (E →L[ℝ] F))
  (π : marked_pi_partition I) : F :=
π.boxes.attach.sum $ λ J, vol J $ f $ π.center J J.coe_prop

@[simp] lemma integral_sum_add (f g : (ι → ℝ) → E) (vol : partition_box ι → (E →L[ℝ] F))
  (π : marked_pi_partition I) :
  integral_sum (f + g) vol π = integral_sum f vol π + integral_sum g vol π :=
by simp only [integral_sum, finset.sum_add_distrib, pi.add_apply, (vol _).map_add]

@[simp] lemma integral_sum_neg (f : (ι → ℝ) → E) (vol : partition_box ι → (E →L[ℝ] F))
  (π : marked_pi_partition I) :
  integral_sum (-f) vol π = -integral_sum f vol π :=
by simp only [integral_sum, finset.sum_neg_distrib, pi.neg_apply, (vol _).map_neg]

@[simp] lemma integral_sum_smul (c : ℝ) (f : (ι → ℝ) → E) (vol : partition_box ι → (E →L[ℝ] F))
  (π : marked_pi_partition I) :
  integral_sum (c • f) vol π = c • integral_sum f vol π :=
by simp only [integral_sum, finset.smul_sum, pi.smul_apply, continuous_linear_map.map_smul]

def has_integral (I : partition_box ι) (l : filter (marked_pi_partition I)) (f : (ι → ℝ) → E)
  (vol : partition_box ι → (E →L[ℝ] F)) (y : F) : Prop :=
tendsto (integral_sum f vol) l (𝓝 y)

def integrable (I : partition_box ι) (l : filter (marked_pi_partition I)) (f : (ι → ℝ) → E)
  (vol : partition_box ι → (E →L[ℝ] F)) : Prop :=
∃ y, has_integral I l f vol y

def integral (I : partition_box ι) (l : filter (marked_pi_partition I)) (f : (ι → ℝ) → E)
  (vol : partition_box ι → (E →L[ℝ] F)) : F :=
if h : integrable I l f vol then classical.some h else 0

variables {l : filter (marked_pi_partition I)}
  {f g : (ι → ℝ) → E} {vol : partition_box ι → (E →L[ℝ] F)} {y y' : F}

lemma integrable_iff_Cauchy [complete_space F] [ne_bot l] :
  integrable I l f vol ↔ cauchy (l.map (integral_sum f vol)) :=
cauchy_map_iff_exists_tendsto.symm

lemma has_integral.R_to_H (h : has_integral I Riemann f vol y) :
  has_integral I Henstock f vol y :=
h.mono_left Henstock_le_Riemann

lemma has_integral.MS_to_H (h : has_integral I McShane f vol y) :
  has_integral I Henstock f vol y :=
h.mono_left Henstock_le_McShane

lemma integrable.has_integral (h : integrable I l f vol) :
  has_integral I l f vol (integral I l f vol) :=
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
