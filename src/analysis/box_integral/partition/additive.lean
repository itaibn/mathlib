import analysis.box_integral.partition.basic

noncomputable theory
open_locale classical
open function set

namespace box_integral

variables {ι G : Type*} [add_comm_group G]

namespace box

def split_edge_lower (I : box ι) (i : ι) (x : ℝ) (hx : x ∈ Ioo (I.lower i) (I.upper i)) :
  box ι :=
⟨I.lower, update I.upper i x, forall_lt_update_iff.2 ⟨hx.1, λ j _, I.lower_lt_upper j⟩⟩

def split_edge_upper (I : box ι) (i : ι) (x : ℝ) (hx : x ∈ Ioo (I.lower i) (I.upper i)) :
  box ι :=
⟨update I.lower i x, I.upper, forall_update_lt_iff.2 ⟨hx.2, λ j _, I.lower_lt_upper j⟩⟩

@[simp] lemma mem_split_edge_lower (I : box ι) {i x hx} {y : ι → ℝ} :
  y ∈ I.split_edge_lower i x hx ↔ y ∈ I ∧ y i ≤ x :=
begin
  simp only [mem_def, mem_Ioc, forall_and_distrib, split_edge_lower, and_assoc],
  refine and_congr_right (λ H, (@le_update_iff _ _ _ _ y I.upper i x).trans _),
  refine (and_comm _ _).trans (and_congr_left $ λ Hi, iff.trans _ (@and_forall_ne _ _ i)),
  exact (and_iff_right_of_imp $ λ Hne, Hi.trans hx.2.le).symm
end

@[simp] lemma coe_split_edge_lower (I : box ι) {i x hx} :
  (I.split_edge_lower i x hx : set (ι → ℝ)) = I ∩ {y | y i ≤ x} :=
set.ext $ λ y, I.mem_split_edge_lower

@[simp] lemma mem_split_edge_upper (I : box ι) {i x hx} {y : ι → ℝ} :
  y ∈ I.split_edge_upper i x hx ↔ y ∈ I ∧ x < y i :=
begin
  simp only [mem_def, mem_Ioc, forall_and_distrib, split_edge_upper, and_assoc,
    forall_update_lt_iff],
  exact ⟨λ ⟨Hi, Hne, Hle⟩, ⟨and_forall_ne.1 ⟨hx.1.trans Hi, Hne⟩, Hle, Hi⟩,
    λ ⟨Hlt, Hle, Hi⟩, ⟨Hi, λ j _, Hlt j, Hle⟩⟩
end

@[simp] lemma coe_split_edge_upper (I : box ι) {i x hx} :
  (I.split_edge_upper i x hx : set (ι → ℝ)) = I ∩ {y | x < y i} :=
set.ext $ λ y, I.mem_split_edge_upper

lemma disjoint_split_edge (I : box ι) (i x hx) :
  disjoint (I.split_edge_lower i x hx : set (ι → ℝ)) (I.split_edge_upper i x hx) :=
λ y ⟨hl, hu⟩, (I.mem_split_edge_lower.1 hl).2.not_lt (I.mem_split_edge_upper.1 hu).2

lemma union_coe_split_edge (I : box ι) (i x hx) :
  (I.split_edge_lower i x hx : set (ι → ℝ)) ∪ (I.split_edge_upper i x hx) = I :=
by simp [← inter_union_distrib_left, ← set_of_or, le_or_lt]

lemma split_edge_lower_le (I : box ι) (i x hx) : I.split_edge_lower i x hx ≤ I :=
by simp only [← coe_subset_coe, ← I.union_coe_split_edge i x hx, subset_union_left]

lemma split_edge_upper_le (I : box ι) (i x hx) : I.split_edge_upper i x hx ≤ I :=
by simp only [← coe_subset_coe, ← I.union_coe_split_edge i x hx, subset_union_right]

end box

namespace partition

def split_edge (I : box ι) (i : ι) (x : ℝ) :
  partition I :=
if hx : x ∈ Ioo (I.lower i) (I.upper i) then
  { boxes := {I.split_edge_lower i x hx, I.split_edge_upper i x hx},
    finite_boxes := (finite_singleton _).insert _,
    bUnion_boxes_coe := by rw [bUnion_pair, I.union_coe_split_edge],
    pairwise_disjoint := (pairwise_on_pair_of_symmetric $ symmetric_disjoint.comap _).2 $
      λ _, I.disjoint_split_edge i x hx }
else ⊤

lemma mem_split_edge_of_mem {I J : box ι} {i : ι} {x : ℝ} (h : x ∈ Ioo (I.lower i) (I.upper i)) :
  J ∈ split_edge I i x ↔ J = I.split_edge_lower i x h ∨ J = I.split_edge_upper i x h :=
by rw [split_edge, dif_pos h, mem_mk, mem_insert_iff, mem_singleton_iff]

lemma mem_split_edge_of_not_mem {I J : box ι} {i : ι} {x : ℝ}
  (h : x ∉ Ioo (I.lower i) (I.upper i)) :
  J ∈ split_edge I i x ↔ J = I :=
by rw [split_edge, dif_neg h, mem_top]

lemma mem_split_edge_iff_coe {I J : box ι} {i : ι} {x : ℝ} :
  J ∈ split_edge I i x ↔ (J : set (ι → ℝ)) =
    I ∩ {y | y i ≤ x} ∨ (J : set (ι → ℝ)) = I ∩ {y | x < y i} :=
begin
  by_cases hx : x ∈ Ioo (I.lower i) (I.upper i),
  { rw [mem_split_edge_of_mem hx, ← box.injective_coe.eq_iff, ← box.injective_coe.eq_iff,
      I.coe_split_edge_lower, I.coe_split_edge_upper] },
  { rw [mem_split_edge_of_not_mem hx],
    rw [mem_Ioo, not_and_distrib, not_lt, not_lt] at hx,
    cases hx,
    { have A : (I : set (ι → ℝ)) ⊆ {y : ι → ℝ | x < y i}, from λ y hy, hx.trans_lt (hy i).1,
      have B : (I : set (ι → ℝ)) ∩ {y : ι → ℝ | y i ≤ x} = ∅,
        by simpa [← subset_compl_iff_disjoint, compl_set_of] using A,
      simp [B, inter_eq_self_of_subset_left A] },
    { have A : (I : set (ι → ℝ)) ⊆ {y : ι → ℝ | y i ≤ x}, from λ y hy, (hy i).2.trans hx,
      have B : (I : set (ι → ℝ)) ∩ {y : ι → ℝ | x < y i} = ∅,
        by simpa [← subset_compl_iff_disjoint, compl_set_of] using A,
      simp [B, inter_eq_self_of_subset_left A] } }
end

@[simp] lemma restrict_split_edge {I J : box ι} (h : I ≤ J) (i : ι) (x : ℝ) :
  restrict (split_edge J i x) I h = split_edge I i x :=
begin
  ext J' hJ',
  simp only [mem_split_edge_iff_coe, box.exists_eq_inter_iff, exists_prop, mem_restrict] at hJ' ⊢,
  rcases hJ' with ⟨J'', (H''|H''), Heq⟩; [left, right];
    rw [Heq, H'', ← inter_assoc, inter_eq_self_of_subset_left (box.coe_subset_coe.2 h)],
end

end partition

def box_additive_on (lower upper : ι → ℝ) (f : (ι → ℝ) → (ι → ℝ) → G) :=
∀ ⦃l u i x⦄, lower ≤ l → l ≤ u → u ≤ upper → l i ≤ x → x ≤ u i →
  f l u = f l (update u i x) + f (update l i x) u

namespace box_additive_on

variables {lower upper l u : ι → ℝ} {f : (ι → ℝ) → (ι → ℝ) → G} {i : ι}

lemma zero_of_eq (h : box_additive_on lower upper f) (hl : lower ≤ l) (hlu : l ≤ u) (hu : u ≤ upper)
  (hi : l i = u i) : f l u = 0 :=
begin
  have := h hl hlu hu le_rfl hi.le,
  rwa [update_eq_self, hi, update_eq_self, self_eq_add_left] at this
end



end box_additive_on

end box_integral
