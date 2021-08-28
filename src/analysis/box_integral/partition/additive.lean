import analysis.box_integral.partition.basic

noncomputable theory
open_locale classical big_operators
open function set

namespace box_integral

variables {ι M : Type*} [add_comm_monoid M]

namespace box

@[simps] def split_edge_lower (I : box ι) (i : ι) (x : ℝ) (hx : x ∈ Ioo (I.lower i) (I.upper i)) :
  box ι :=
⟨I.lower, update I.upper i x, forall_lt_update_iff.2 ⟨hx.1, λ j _, I.lower_lt_upper j⟩⟩

@[simps] def split_edge_upper (I : box ι) (i : ι) (x : ℝ) (hx : x ∈ Ioo (I.lower i) (I.upper i)) :
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

lemma comap_split_edge_lower_of_not_mem_range {ι' : Type*} (I : box ι) (i x hx)
  (f : ι' → ι) (h : i ∉ range f) :
  comap f (split_edge_lower I i x hx) = comap f I :=
begin
  simp only [comap, preorder_hom.coe_fun_mk, split_edge_lower, funext_iff, (∘)],
  exact ⟨λ _, rfl, λ j, update_noteq (mt (λ hi, mem_range.2 ⟨_, hi⟩) h) _ _⟩
end

lemma comap_split_edge_upper_of_not_mem_range {ι' : Type*} (I : box ι) (i x hx)
  (f : ι' → ι) (h : i ∉ range f) :
  comap f (split_edge_upper I i x hx) = comap f I :=
begin
  simp only [comap, preorder_hom.coe_fun_mk, split_edge_upper, funext_iff, (∘)],
  exact ⟨λ j, update_noteq (mt (λ hi, mem_range.2 ⟨_, hi⟩) h) _ _, λ j, rfl⟩
end

lemma comap_coe_split_edge_lower_of_not_mem (I : box ι) (i x hx) {s : set ι} (hi : i ∉ s) :
  comap (coe : s → ι) (split_edge_lower I i x hx) = comap coe I :=
comap_split_edge_lower_of_not_mem_range I i x hx coe $ by rwa [subtype.range_coe]

lemma comap_coe_split_edge_upper_of_not_mem (I : box ι) (i x hx) {s : set ι} (hi : i ∉ s) :
  comap (coe : s → ι) (split_edge_upper I i x hx) = comap coe I :=
comap_split_edge_upper_of_not_mem_range I i x hx coe $ by rwa [subtype.range_coe]

lemma comap_coe_split_edge_lower_of_mem (I : box ι) (i x hx) {s : set ι} (hi : i ∈ s) :
  comap (coe : s → ι) (split_edge_lower I i x hx) = split_edge_lower (comap coe I) ⟨i, hi⟩ x hx :=
begin
  simp only [comap, split_edge_lower, eq_update_iff, true_and, preorder_hom.coe_fun_mk,
    eq_self_iff_true, comp_app],
  refine ⟨update_same _ _ _, λ j hj, update_noteq _ _ _⟩,
  rintro rfl, simpa only [subtype.coe_eta] using hj
end

lemma comap_coe_split_edge_upper_of_mem (I : box ι) (i x hx) {s : set ι} (hi : i ∈ s) :
  comap (coe : s → ι) (split_edge_upper I i x hx) = split_edge_upper (comap coe I) ⟨i, hi⟩ x hx :=
begin
  simp only [comap, split_edge_upper, eq_update_iff, and_true, preorder_hom.coe_fun_mk,
    eq_self_iff_true, comp_app],
  refine ⟨update_same _ _ _, λ j hj, update_noteq _ _ _⟩,
  rintro rfl, simpa only [subtype.coe_eta] using hj
end

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

@[to_additive] lemma finprod_mem_bUnion {M : Type*} [comm_monoid M] {I : box ι} (π : partition I)
  (πi : Π J ∈ π, partition J) (f : Π J ∈ π.bUnion πi, M) :
  ∏ᶠ J ∈ π.bUnion πi, f J ‹_› = ∏ᶠ (J ∈ π) (J' ∈ πi J ‹_›), f J' (π.mem_bUnion.2 ⟨J, ‹_›, ‹_›⟩) :=
begin
  refine finprod_mem_bUnion' _ π.finite_boxes (λ J hJ, (πi J hJ).finite_boxes) _,
  rintros J₁ h₁ J₂ h₂ hne J' ⟨h₁' : J' ∈ πi J₁ h₁, h₂' : J' ∈ πi J₂ h₂⟩,
  exact hne (π.eq_of_le_of_le h₁ h₂ ((πi J₁ h₁).le_of_mem h₁') ((πi J₂ h₂).le_of_mem h₂'))
end

end partition

open box partition

def box_additive_on (f : box ι → M) (I : box ι) : Prop :=
∀ (J ≤ I) i x hx, f (split_edge_lower J i x hx) + f (split_edge_upper J i x hx) = f J

namespace box_additive_on

variables {I J : box ι} {f : box ι → M} {i : ι}

lemma add_monoid_hom_comp {N : Type*} [add_comm_monoid N] (h : box_additive_on f I) (g : M →+ N) :
  box_additive_on (g ∘ f) I :=
λ J hJ i x hx, by rw [← g.map_add, h J hJ i x hx]

lemma restrict (h : box_additive_on f I) (hle : J ≤ I) : box_additive_on f J :=
λ J' hJ' i x hx, h J' (hJ'.trans hle) i x hx

lemma finsum_mem_partition [fintype ι] (h : box_additive_on f I)
  (π : partition I) :
  ∑ᶠ J ∈ π, f J = f I :=
begin
  refine partition.split_edge_induction_on' π
    (λ J s, ∑ᶠ J' ∈ s, f J' = f J) (λ J hJ, _)
    (λ J hJ i x hx, _) (λ J hJ π πi H, _),
  { simp },
  { rw finsum_mem_pair (J.split_edge_lower_ne_upper _ _ _),
    exact h J hJ i x hx },
  { refine eq.congr _ rfl,
    exact (π.finsum_mem_bUnion (λ J _, πi J) _).trans (finsum_mem_congr rfl H) }
end

end box_additive_on

open finset

lemma box_additive_on_box_volume [fintype ι] (I : box ι) :
  box_additive_on volume I :=
begin
  intros J hJ i x hx,
  simp only [← prod_mul_prod_compl ({i} : finset ι), finset.prod_singleton, update_same,
    add_mul, split_edge_lower, split_edge_upper, ← sub_add_sub_cancel' x (J.lower i) (J.upper i),
    box.volume],
  congr' 2; { apply prod_congr rfl, intros j hj, rw update_noteq, simpa using hj }
end

lemma box_additive_on_upper_sub_lower {G : Type*} [fintype ι] [add_comm_group G]
  (I : box ι) (i : ι) (f : ℝ → box ({i}ᶜ : set ι) → G)
  (H : ∀ x ∈ Icc (I.lower i) (I.upper i), box_additive_on (f x) (comap coe I)) :
  box_additive_on (λ J : box ι, (f (J.upper i) (comap coe J) - f (J.lower i) (comap coe J))) I :=
begin
  intros J hJ j x hx,
  rcases eq_or_ne i j with rfl|hne,
  { have : i ∉ ({i}ᶜ : set ι), from not_not.2 rfl,
    simp [comap_coe_split_edge_upper_of_not_mem _ _ _ _ this,
      comap_coe_split_edge_lower_of_not_mem _ _ _ _ this] },
  { have A : j ∈ ({i}ᶜ : set ι), from hne.symm,
    simp only [comap_coe_split_edge_upper_of_mem _ _ _ _ A,
      comap_coe_split_edge_lower_of_mem _ _ _ _ A,
      split_edge_lower_lower, split_edge_lower_upper, split_edge_upper_lower,
      split_edge_upper_upper, update_noteq hne],
    have := λ y hy, H y hy (comap coe J) ((comap coe).monotone hJ) ⟨j, A⟩ x hx,
    rw [← this, ← this],
    { abel },
    exacts [⟨monotone_lower hJ i, (J.lower_le_upper i).trans (monotone_upper hJ i)⟩,
      ⟨(monotone_lower hJ i).trans (J.lower_le_upper i), monotone_upper hJ i⟩]}
end

end box_integral
