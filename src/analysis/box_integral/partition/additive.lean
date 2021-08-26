import analysis.box_integral.partition.basic

noncomputable theory
open_locale classical big_operators
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

lemma split_edge_lower_ne_upper (I : box ι) (i x hx) :
  I.split_edge_lower i x hx ≠ I.split_edge_upper i x hx :=
mt coe_inj.2 $ (I.disjoint_split_edge i x hx).ne (I.split_edge_lower i x hx).coe_ne_empty

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

lemma coe_eq_of_mem_split_edge_of_mem_le {I J : box ι} {i : ι} {x : ℝ} {y : ι → ℝ}
  (h₁ : J ∈ split_edge I i x) (h₂ : y ∈ J) (h₃ : y i ≤ x) :
  (J : set (ι → ℝ)) = I ∩ {y | y i ≤ x} :=
(mem_split_edge_iff_coe.1 h₁).resolve_right $ λ H,
  by { rw [← box.mem_coe, H] at h₂, exact h₃.not_lt h₂.2 }

lemma coe_eq_of_mem_split_edge_of_lt_mem {I J : box ι} {i : ι} {x : ℝ} {y : ι → ℝ}
  (h₁ : J ∈ split_edge I i x) (h₂ : y ∈ J) (h₃ : x < y i) :
  (J : set (ι → ℝ)) = I ∩ {y | x < y i} :=
(mem_split_edge_iff_coe.1 h₁).resolve_left $ λ H,
  by { rw [← box.mem_coe, H] at h₂, exact h₃.not_le h₂.2 }

@[simp] lemma restrict_split_edge {I J : box ι} (h : I ≤ J) (i : ι) (x : ℝ) :
  restrict (split_edge J i x) I h = split_edge I i x :=
begin
  ext J' hJ',
  simp only [mem_split_edge_iff_coe, box.mem_inter, exists_prop, mem_restrict] at hJ' ⊢,
  rcases hJ' with ⟨J'', (H''|H''), Heq⟩; [left, right];
    rw [Heq, H'', ← inter_assoc, inter_eq_self_of_subset_left (box.coe_subset_coe.2 h)]
end

lemma inf_split_edge {I : box ι} (π : partition I) (i : ι) (x : ℝ) :
  π ⊓ split_edge I i x = π.bUnion (λ J hJ, split_edge J i x) :=
by simp only [inf_def, restrict_split_edge]

def split_many (I : box ι) (s : finset (ι × ℝ)) : partition I :=
s.inf (λ p, split_edge I p.1 p.2)

@[simp] lemma split_many_empty (I : box ι) : split_many I ∅ = ⊤ := finset.inf_empty

@[simp] lemma split_many_insert (I : box ι) (s : finset (ι × ℝ)) (p : ι × ℝ) :
  split_many I (insert p s) = split_many I s ⊓ split_edge I p.1 p.2 :=
by rw [split_many, finset.inf_insert, inf_comm, split_many]

lemma split_many_le_split_edge (I : box ι) {s : finset (ι × ℝ)} {p : ι × ℝ} (hp : p ∈ s) :
  split_many I s ≤ split_edge I p.1 p.2 :=
finset.inf_le hp

lemma inf_split_many {I : box ι} (π : partition I) (s : finset (ι × ℝ)) :
  π ⊓ split_many I s = π.bUnion (λ J hJ, split_many J s) :=
begin
  induction s using finset.induction_on with p s hp ihp,
  { simp },
  { simp_rw [split_many_insert, ← inf_assoc, ihp, inf_split_edge, bUnion_assoc] }
end

lemma split_many_le_of_subset {I : box ι} (π : partition I) (s : finset (ι × ℝ))
  (H : ∀ (J ∈ π) i, (i, (J : _).lower i) ∈ s ∧ (i, J.upper i) ∈ s) :
  split_many I s ≤ π :=
begin
  refine le_def'.2 (λ J hJ J' hJ' x hx hx' y hy i, ⟨_, _⟩),
  { rcases split_many_le_split_edge I (H _ hJ' i).1 hJ
      with ⟨Jl, Hmem : Jl ∈ split_edge I i (J'.lower i), Hle⟩,
    have := Hle hx,
    rw [← box.coe_subset_coe, coe_eq_of_mem_split_edge_of_lt_mem Hmem this (hx' i).1] at Hle,
    exact (Hle hy).2 },
  { rcases split_many_le_split_edge I (H _ hJ' i).2 hJ
      with ⟨Jl, Hmem : Jl ∈ split_edge I i (J'.upper i), Hle⟩,
    have := Hle hx,
    rw [← box.coe_subset_coe, coe_eq_of_mem_split_edge_of_mem_le Hmem this (hx' i).2] at Hle,
    exact (Hle hy).2 }
end

lemma exists_split_many_le [fintype ι] {I : box ι} (π : partition I) : ∃ s, split_many I s ≤ π :=
have finite (⋃ J ∈ π, ⋃ i, {(i, (J : _).lower i), (i, J.upper i)} : set (ι × ℝ)),
  from π.finite_boxes.bUnion (λ J hJ, finite_Union $ λ i, (finite_singleton _).insert _),
⟨this.to_finset, π.split_many_le_of_subset _ $ λ J hJ i,
  ⟨this.mem_to_finset.2 $ set.mem_bUnion hJ $ mem_Union.2 ⟨i, mem_insert _ _⟩,
    this.mem_to_finset.2 $ set.mem_bUnion hJ $ mem_Union.2 ⟨i, mem_insert_of_mem _ rfl⟩⟩⟩

@[elab_as_eliminator]
lemma split_edge_induction_on [fintype ι] {I : box ι} (π : partition I)
  {p : Π J : box ι, partition J → Prop}
  (H_top : ∀ J ≤ I, p J ⊤) (H_split : ∀ (J ≤ I) i x, p J (split_edge J i x))
  (H_bUnion : ∀ (J ≤ I) (π : partition J) (πi : Π J', partition J'),
    (∀ J' ∈ π, p J' (πi J')) → (p J (π.bUnion (λ J' _, πi J')) ↔ p J π)) : p I π :=
begin
  have : ∀ (s : finset (ι × ℝ)) (J ≤ I), p J (split_many J s),
  { intros s J hle, induction s using finset.induction_on with p s hps ihs,
    { simpa using H_top J hle },
    { rw [split_many_insert, inf_split_edge],
      rwa H_bUnion J hle,
      exact λ J' hJ', H_split _ (le_trans (le_of_mem _ hJ') hle) _ _ } },
  rcases exists_split_many_le π with ⟨s, hs⟩,
  rw [← inf_eq_right, inf_split_many] at hs,
  rw [← H_bUnion I le_rfl, hs],
  exacts [this s I le_rfl, λ J hJ, this s J (le_of_mem _ hJ)]
end

@[elab_as_eliminator]
lemma split_edge_induction_on' [fintype ι] {I : box ι} (π : partition I)
  (p : box ι → set (box ι) → Prop) (H_top : ∀ J ≤ I, p J {J})
  (H_split : ∀ (J ≤ I) i x hx, p J {J.split_edge_lower i x hx, J.split_edge_upper i x hx})
  (H_bUnion : ∀ (J ≤ I) (π : partition J) (πi : Π J', partition J'),
    (∀ J' ∈ π, p J' (πi J').boxes) → (p J (π.bUnion (λ J' _, πi J')).boxes ↔ p J π.boxes)) :
  p I π.boxes :=
begin
  refine box_integral.partition.split_edge_induction_on π H_top (λ J hJ i x, _) H_bUnion,
  by_cases hx : x ∈ Ioo (J.lower i) (J.upper i),
  { convert H_split J hJ i x hx, ext y, exact mem_split_edge_of_mem hx },
  { rw [split_edge, dif_neg hx], exact H_top J hJ }
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

lemma finsum_mem_partition [fintype ι] {I : box ι} (h : box_additive_on I.lower I.upper f)
  (π : partition I) :
  ∑ᶠ J ∈ π, f (J : _).lower J.upper = f I.lower I.upper :=
begin
  refine partition.split_edge_induction_on' π
    (λ J s, ∑ᶠ J' ∈ s, f (J' : _).lower J'.upper = f J.lower J.upper) (λ J hJ, _)
    (λ J hJ i x hx, _) (λ J hJ π πi H, _),
  { simp },
  { rw finsum_mem_pair (J.split_edge_lower_ne_upper _ _ _),
    exact (h (box.monotone_lower hJ) J.lower_le_upper (box.monotone_upper hJ) hx.1.le
      hx.2.le).symm },
  { refine eq.congr _ rfl,
    dsimp only [partition.bUnion],
    refine (finsum_mem_bUnion _ π.finite_boxes (λ J _, (πi J).finite_boxes)).trans _,
    { rintros J₁ h₁ J₂ h₂ hne J' ⟨h₁' : J' ∈ πi J₁, h₂' : J' ∈ πi J₂⟩,
      exact hne (π.eq_of_le_of_le h₁ h₂ ((πi J₁).le_of_mem h₁') ((πi J₂).le_of_mem h₂')) },
    { exact finsum_mem_congr rfl H } }
end

end box_additive_on


end box_integral
