/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.partition.basic

noncomputable theory
open_locale classical big_operators
open function set

namespace box_integral

variables {ι M : Type*}

namespace box

/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `box_integral.box.split_lower I i x` is the box `I ∩ {y | y i ≤ x}`
(if it is nonempty). -/
@[simps] def split_lower (I : box ι) (i : ι) (x : ℝ) :
  part (box ι) :=
{ dom := I.lower i < x,
  get := λ hx, ⟨I.lower, update I.upper i (min x (I.upper i)),
    forall_lt_update_iff.2 ⟨lt_min hx $ I.lower_lt_upper i, λ j _, I.lower_lt_upper j⟩⟩ }

@[simp] lemma mem_split_lower_get_iff (I : box ι) {i x hx} {y : ι → ℝ} :
  y ∈ (I.split_lower i x).get hx ↔ y ∈ I ∧ y i ≤ x :=
begin
  simp only [mem_def, mem_Ioc, forall_and_distrib, split_lower, and_assoc],
  refine and_congr_right (λ H, (@le_update_iff _ _ _ _ y I.upper i _).trans _),
  rw [le_min_iff, and_assoc, and_forall_ne i, and_comm]
end

lemma mem_split_lower_get (I : box ι) {i x} {y : ι → ℝ} (h₁ : y ∈ I) (h₂ : y i ≤ x) :
  y ∈ (I.split_lower i x).get ((h₁ i).1.trans_le h₂) :=
I.mem_split_lower_get_iff.2 ⟨h₁, h₂⟩

@[simp] lemma coe_split_lower_get (I : box ι) {i x hx} :
  ((I.split_lower i x).get hx : set (ι → ℝ)) = I ∩ {y | y i ≤ x} :=
set.ext $ λ y, I.mem_split_lower_get_iff

lemma split_lower_get_le (I : box ι) {i x hx} : (I.split_lower i x).get hx ≤ I :=
coe_subset_coe.1 $ by simp only [coe_split_lower_get, inter_subset_left]

lemma mem_split_lower {I J : box ι} {i x} :
  J ∈ I.split_lower i x ↔ (J : set (ι → ℝ)) = I ∩ {y | y i ≤ x} :=
begin
  refine ⟨λ ⟨H, Heq⟩, Heq ▸ coe_split_lower_get _, λ H, ⟨_, injective_coe _⟩⟩,
  { have := J.upper_mem, rw [← mem_coe, H] at this,
    exact (this.1 i).1.trans_le this.2 },
  { rw [coe_split_lower_get, H] }
end

@[simp] lemma Union_coe_mem_split_lower (I : box ι) (i : ι) (x : ℝ) :
  (⋃ J ∈ I.split_lower i x, ↑J : set (ι → ℝ)) = I ∩ {y | y i ≤ x} :=
begin
  ext y, simp only [mem_Union], fsplit,
  { rintro ⟨J, hJ, hy⟩, rwa mem_split_lower.1 hJ at hy },
  { exact λ hy, ⟨_, ⟨_, rfl⟩, I.mem_split_lower_get hy.1 hy.2⟩ }
end

lemma split_lower_of_le_lower (I : box ι) {i x} (h : x ≤ I.lower i) :
  I.split_lower i x = part.none :=
part.eq_none_iff'.2 h.not_lt

lemma split_lower_of_upper_le (I : box ι) {i x} (h : I.upper i ≤ x) :
  I.split_lower i x = part.some I :=
begin
  rw ← @part.get_eq_iff_eq_some _ (I.split_lower i x) ((I.lower_lt_upper i).trans_le h),
  ext y, simpa using (show y ∈ I → y i ≤ x, from λ hy, (hy i).2.trans h)
end

/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `box_integral.box.split_upper I i x hx` is the box `I ∩ {y | x < y i}`
(if it is nonempty). -/
@[simps] def split_upper (I : box ι) (i : ι) (x : ℝ) :
  part (box ι) :=
{ dom := x < I.upper i,
  get := λ hx, ⟨update I.lower i (max x (I.lower i)), I.upper,
    forall_update_lt_iff.2 ⟨max_lt hx $ I.lower_lt_upper i, λ j _, I.lower_lt_upper j⟩⟩ }

@[simp] lemma mem_split_upper_get_iff (I : box ι) {i x hx} {y : ι → ℝ} :
  y ∈ (I.split_upper i x).get hx ↔ y ∈ I ∧ x < y i :=
begin
  simp only [mem_def, mem_Ioc, forall_and_distrib, split_upper, forall_update_lt_iff],
  rw [max_lt_iff, and_assoc (x < y i), and_forall_ne i, and_assoc, and_comm]
end

@[simp] lemma mem_split_upper_get (I : box ι) {i x} {y : ι → ℝ} (h₁ : y ∈ I) (h₂ : x < y i) :
  y ∈ (I.split_upper i x).get (h₂.trans_le (h₁ i).2) :=
I.mem_split_upper_get_iff.2 ⟨h₁, h₂⟩

@[simp] lemma coe_split_upper_get (I : box ι) {i x hx} :
  ((I.split_upper i x).get hx : set (ι → ℝ)) = I ∩ {y | x < y i} :=
set.ext $ λ y, I.mem_split_upper_get_iff

lemma split_upper_get_le (I : box ι) {i x hx} : (I.split_upper i x).get hx ≤ I :=
coe_subset_coe.1 $ by simp only [coe_split_upper_get, inter_subset_left]

lemma mem_split_upper {I J : box ι} {i x} :
  J ∈ I.split_upper i x ↔ (J : set (ι → ℝ)) = I ∩ {y | x < y i} :=
begin
  refine ⟨λ ⟨H, Heq⟩, Heq ▸ coe_split_upper_get _, λ H, ⟨_, injective_coe _⟩⟩,
  { have := J.upper_mem, rw [← mem_coe, H] at this,
    exact lt_of_lt_of_le this.2 (this.1 i).2 },
  { rw [coe_split_upper_get, H] }
end

@[simp] lemma Union_coe_mem_split_upper (I : box ι) (i : ι) (x : ℝ) :
  (⋃ J ∈ I.split_upper i x, ↑J : set (ι → ℝ)) = I ∩ {y | x < y i} :=
begin
  ext y, simp only [mem_Union], fsplit,
  { rintro ⟨J, hJ, hy⟩, rwa mem_split_upper.1 hJ at hy },
  { exact λ hy, ⟨_, ⟨_, rfl⟩, I.mem_split_upper_get hy.1 hy.2⟩ }
end

lemma split_upper_of_le_lower (I : box ι) {i x} (h : x ≤ I.lower i) :
  I.split_upper i x = part.some I :=
begin
  rw ← @part.get_eq_iff_eq_some _ (I.split_upper i x) (h.trans_lt (I.lower_lt_upper i)),
  ext y, simpa using (show y ∈ I → x < y i, from λ hy, h.trans_lt (hy i).1)
end

lemma split_upper_of_upper_le (I : box ι) {i x} (h : I.upper i ≤ x) :
  I.split_upper i x = part.none :=
part.eq_none_iff'.2 h.not_lt

lemma map_split_lower_add_upper_get_or_else_zero {M : Type*} [add_zero_class M] (I : box ι) (i : ι)
  (x : ℝ) (f : box ι → M) :
  ((I.split_lower i x).map f).get_or_else 0 + ((I.split_upper i x).map f).get_or_else 0 =
    if h : x ∈ Ioo (I.lower i) (I.upper i) then
      f ((I.split_lower i x).get (and.left h)) + f ((I.split_upper i x).get (and.right h))
    else f I :=
begin
  split_ifs with hx,
  { rw [part.get_or_else, part.get_or_else, dif_pos, dif_pos, part.map_get, part.map_get] },
  { rw [mem_Ioo, not_and_distrib, not_lt, not_lt] at hx, cases hx,
    { simp [split_upper_of_le_lower _ hx, split_lower_of_le_lower _ hx] },
    { simp [split_upper_of_upper_le _ hx, split_lower_of_upper_le _ hx] } }
end

lemma comap_split_lower_get_of_not_mem_range {ι' : Type*} (I : box ι) (i x hx)
  (f : ι' → ι) (h : i ∉ range f) :
  comap f ((split_lower I i x).get hx) = comap f I :=
begin
  simp only [comap, preorder_hom.coe_fun_mk, split_lower, funext_iff, (∘)],
  exact ⟨λ _, rfl, λ j, update_noteq (mt (λ hi, mem_range.2 ⟨_, hi⟩) h) _ _⟩
end

lemma comap_split_upper_get_of_not_mem_range {ι' : Type*} (I : box ι) (i x hx)
  (f : ι' → ι) (h : i ∉ range f) :
  comap f ((split_upper I i x).get hx) = comap f I :=
begin
  simp only [comap, preorder_hom.coe_fun_mk, split_upper, funext_iff, (∘)],
  exact ⟨λ j, update_noteq (mt (λ hi, mem_range.2 ⟨_, hi⟩) h) _ _, λ j, rfl⟩
end

lemma comap_coe_split_lower_get_of_not_mem (I : box ι) (i x hx) {s : set ι} (hi : i ∉ s) :
  comap (coe : s → ι) ((split_lower I i x).get hx) = comap coe I :=
comap_split_lower_get_of_not_mem_range I i x hx coe $ by rwa [subtype.range_coe]

lemma comap_coe_split_upper_get_of_not_mem (I : box ι) (i x hx) {s : set ι} (hi : i ∉ s) :
  comap (coe : s → ι) ((split_upper I i x).get hx) = comap coe I :=
comap_split_upper_get_of_not_mem_range I i x hx coe $ by rwa [subtype.range_coe]

lemma comap_coe_split_lower_get_of_mem (I : box ι) (i x hx) {s : set ι} (hi : i ∈ s) :
  comap (coe : s → ι) ((split_lower I i x).get hx) =
    (split_lower (comap coe I) (⟨i, hi⟩ : s) x).get hx :=
begin
  simp only [comap, preorder_hom.coe_fun_mk, split_lower, eq_self_iff_true, true_and],
  erw [eq_update_iff, comp_app, subtype.coe_mk],
  refine ⟨update_same _ _ _, λ j hj, update_noteq _ _ _⟩,
  rintro rfl, simpa only [subtype.coe_eta] using hj
end

lemma comap_coe_split_upper_get_of_mem (I : box ι) (i x hx) {s : set ι} (hi : i ∈ s) :
  comap (coe : s → ι) ((split_upper I i x).get hx) =
    (split_upper (comap coe I) (⟨i, hi⟩ : s) x).get hx :=
begin
  simp only [comap, preorder_hom.coe_fun_mk, split_upper, eq_self_iff_true, and_true],
  erw [eq_update_iff, comp_app, subtype.coe_mk],
  refine ⟨update_same _ _ _, λ j hj, update_noteq _ _ _⟩,
  rintro rfl, simpa only [subtype.coe_eta] using hj
end

end box

namespace prepartition

variables {I J : box ι} {i : ι} {x : ℝ}

/-- The partition of `I : box ι` into the boxes `I ∩ {y | y ≤ x i}` and `I ∩ {y | x i < y}`.
One of these boxes can be empty, then this partition is just the single-box partition `⊤`. -/
def split (I : box ι) (i : ι) (x : ℝ) : prepartition I :=
((subsingle I (I.split_lower i x) $ λ J ⟨H, hJ⟩, hJ ▸ I.split_lower_get_le).union_compl
  (subsingle I (I.split_upper i x) $ λ J ⟨H, hJ⟩, hJ ▸ I.split_upper_get_le)).get $
  by simp [diff_eq (I : set (ι → ℝ)) {y | y i ≤ x}, compl_set_of]

@[simp] lemma mem_split_iff : J ∈ split I i x ↔ J ∈ I.split_lower i x ∨ J ∈ I.split_upper i x :=
by simp [split]

lemma mem_split_iff' : J ∈ split I i x ↔
  (J : set (ι → ℝ)) = I ∩ {y | y i ≤ x} ∨ (J : set (ι → ℝ)) = I ∩ {y | x < y i} :=
by simp [mem_split_iff, box.mem_split_lower, box.mem_split_upper]

lemma is_partition_split (I : box ι) (i : ι) (x : ℝ) : is_partition (split I i x) :=
is_partition_union_compl_get _

@[simp] lemma Union_split (I : box ι) (i : ι) (x : ℝ) : (split I i x).Union = I :=
(is_partition_split I i x).Union_eq

/-- If `I.lower i < x < I.upper i`, then the hyperplane `{y | y i = x}` splits `I` into two
boxes. -/
lemma split_boxes_of_mem_Ioo (h : x ∈ Ioo (I.lower i) (I.upper i)) :
  (split I i x).boxes = {(I.split_lower i x).get h.1, (I.split_upper i x).get h.2} :=
begin
  ext J,
  simp only [finset.mem_insert, finset.mem_singleton, mem_boxes, mem_split_iff, part.eq_get_iff_mem]
end

/-- If `x ∉ (I.lower i, I.upper i)`, then the hyperplane `{y | y i = x}` does not split `I`. -/
lemma split_of_not_mem_Ioo (h : x ∉ Ioo (I.lower i) (I.upper i)) : split I i x = ⊤ :=
begin
  refine ((is_partition_top I).subset_iff_eq.1 $ λ J hJ, _).symm,
  rcases mem_top.1 hJ with rfl, clear hJ,
  rw [mem_split_iff],
  rw [mem_Ioo, not_and_distrib, not_lt, not_lt] at h,
  cases h; [right, left];
    simp only [box.split_lower_of_upper_le, box.split_upper_of_le_lower, h, part.mem_some]
end

lemma coe_eq_of_mem_split_of_mem_le {y : ι → ℝ} (h₁ : J ∈ split I i x) (h₂ : y ∈ J) (h₃ : y i ≤ x) :
  (J : set (ι → ℝ)) = I ∩ {y | y i ≤ x} :=
(mem_split_iff'.1 h₁).resolve_right $ λ H,
  by { rw [← box.mem_coe, H] at h₂, exact h₃.not_lt h₂.2 }

lemma coe_eq_of_mem_split_of_lt_mem {y : ι → ℝ} (h₁ : J ∈ split I i x) (h₂ : y ∈ J) (h₃ : x < y i) :
  (J : set (ι → ℝ)) = I ∩ {y | x < y i} :=
(mem_split_iff'.1 h₁).resolve_left $ λ H,
  by { rw [← box.mem_coe, H] at h₂, exact h₃.not_le h₂.2 }

@[simp] lemma restrict_split (h : I ≤ J) (i : ι) (x : ℝ) : (split J i x).restrict I = split I i x :=
begin
  refine ((is_partition_split J i x).restrict h).subset_iff_eq.1 (λ J' hJ', _),
  simp only [mem_split_iff', box.mem_inter, exists_prop, mem_restrict] at hJ' ⊢,
  rcases hJ' with ⟨J'', (H''|H''), Heq⟩; [left, right];
    rw [Heq, H'', ← inter_assoc, inter_eq_self_of_subset_left (box.coe_subset_coe.2 h)]
end

lemma inf_split (π : prepartition I) (i : ι) (x : ℝ) :
  π ⊓ split I i x = π.bUnion (λ J, split J i x) :=
bUnion_congr_of_le rfl $ λ J hJ, restrict_split hJ i x

/-- Split a box along many hyperplanes `{y | y i = x}`; each hyperplane is given by the pair
`(i x)`. -/
def split_many (I : box ι) (s : finset (ι × ℝ)) : prepartition I :=
s.inf (λ p, split I p.1 p.2)

@[simp] lemma split_many_empty (I : box ι) : split_many I ∅ = ⊤ := finset.inf_empty

@[simp] lemma split_many_insert (I : box ι) (s : finset (ι × ℝ)) (p : ι × ℝ) :
  split_many I (insert p s) = split_many I s ⊓ split I p.1 p.2 :=
by rw [split_many, finset.inf_insert, inf_comm, split_many]

lemma split_many_le_split (I : box ι) {s : finset (ι × ℝ)} {p : ι × ℝ} (hp : p ∈ s) :
  split_many I s ≤ split I p.1 p.2 :=
finset.inf_le hp

lemma is_partition_split_many (I : box ι) (s : finset (ι × ℝ)) :
  is_partition (split_many I s) :=
finset.induction_on s (by simp only [split_many_empty, is_partition_top]) $
  λ a s ha hs, by simpa only [split_many_insert, inf_split]
    using hs.bUnion (λ J hJ, is_partition_split _ _ _)

lemma inf_split_many {I : box ι} (π : prepartition I) (s : finset (ι × ℝ)) :
  π ⊓ split_many I s = π.bUnion (λ J, split_many J s) :=
begin
  induction s using finset.induction_on with p s hp ihp,
  { simp },
  { simp_rw [split_many_insert, ← inf_assoc, ihp, inf_split, bUnion_assoc] }
end

lemma nonempty_inter_imp_le_of_subset_of_mem_split_many {I J Js : box ι} {s : finset (ι × ℝ)}
  (H : ∀ i, {(i, J.lower i), (i, J.upper i)} ⊆ s) (HJs : Js ∈ split_many I s)
  (Hn : (J ∩ Js : set (ι → ℝ)).nonempty) : Js ≤ J :=
begin
  simp only [finset.insert_subset, finset.singleton_subset_iff] at H,
  rcases Hn with ⟨x, hx, hxs⟩,
  refine λ y hy i, ⟨_, _⟩,
  { rcases split_many_le_split I (H i).1 HJs with ⟨Jl, Hmem : Jl ∈ split I i (J.lower i), Hle⟩,
    have := Hle hxs,
    rw [← box.coe_subset_coe, coe_eq_of_mem_split_of_lt_mem Hmem this (hx i).1] at Hle,
    exact (Hle hy).2 },
  { rcases split_many_le_split I (H i).2 HJs with ⟨Jl, Hmem : Jl ∈ split I i (J.upper i), Hle⟩,
    have := Hle hxs,
    rw [← box.coe_subset_coe, coe_eq_of_mem_split_of_mem_le Hmem this (hx i).2] at Hle,
    exact (Hle hy).2 }
end

section fintype

variable [fintype ι]

lemma exists_split_many_forall_nonempty_imp_le (s : finset (box ι)) :
  ∃ t : finset (ι × ℝ), ∀ (I : box ι) (J ∈ s) (J' ∈ split_many I t),
    (J ∩ J' : set (ι → ℝ)).nonempty → J' ≤ J :=
begin
  refine ⟨s.bUnion (λ J, finset.univ.bUnion (λ i, {(i, J.lower i), (i, J.upper i)})),
    λ I J hJ J' hJ', nonempty_inter_imp_le_of_subset_of_mem_split_many (λ i, _) hJ'⟩,
  exact λ p hp, finset.mem_bUnion.2 ⟨J, hJ, finset.mem_bUnion.2 ⟨i, finset.mem_univ _, hp⟩⟩
end

/-- If `π` is a partition of `I`, then there exists a finite set `s` of hyperplanes such that
`split_many I s ≤ π`. -/
lemma is_partition.exists_split_many_le {I : box ι} {π : prepartition I}
  (h : is_partition π) : ∃ s, split_many I s ≤ π :=
(exists_split_many_forall_nonempty_imp_le π.boxes).imp $ λ s hs, h.le_iff.2 $
  λ Js hJs J hJ x hxs hx, hs I J hJ _ hJs ⟨x, hx, hxs⟩

/-- For every prepartition `π` of `I` there exists a prepartition that covers exactly
`I \ π.Union`. -/
lemma exists_Union_eq_diff (π : prepartition I) :
  ∃ π' : prepartition I, π'.Union = I \ π.Union :=
begin
  rcases exists_split_many_forall_nonempty_imp_le π.boxes with ⟨s, hs⟩,
  refine ⟨(split_many I s).filter (λ J', ∀ J ∈ π, disjoint (J : set (ι → ℝ)) J'), _⟩,
  ext x,
  simp only [not_exists, exists_prop, mem_Union, mem_filter, not_and, box.mem_coe, mem_diff],
  fsplit,
  { rintro ⟨J', ⟨hJ's, hJ'⟩, hx'⟩,
    exact ⟨le_of_mem _ hJ's hx', λ J hJ hx, hJ' J hJ ⟨hx, hx'⟩⟩ },
  { rintro ⟨hxI, hxπ⟩,
    rcases is_partition_split_many I s x hxI with ⟨J', hJ', hx'⟩,
    refine ⟨J', ⟨hJ', λ J hJ y hy, _⟩, hx'⟩,
    exact hxπ J hJ (hs I J hJ J' hJ' ⟨y, hy⟩ hx') }
end

def compl (π : prepartition I) : prepartition I := π.exists_Union_eq_diff.some

@[simp] lemma Union_compl (π : prepartition I) : π.compl.Union = I \ π.Union :=
π.exists_Union_eq_diff.some_spec

/-- Since the definition of `box_integral.prepartition.compl` uses `Exists.some`,
the result depends only on `π.Union`. -/
lemma compl_congr {π₁ π₂ : prepartition I} (h : π₁.Union = π₂.Union) :
  π₁.compl = π₂.compl :=
by { dunfold compl, congr' 1, rw h }

@[to_additive]
protected lemma prod_bUnion_boxes {M : Type*} [comm_monoid M] {I : box ι} (π : partition I)
  (πi : Π J, partition J) (f : box ι → M) :
  ∏ J in (π.bUnion πi).boxes, f J = ∏ J in π.boxes, ∏ J' in (πi J).boxes, f J' :=
begin
  refine finset.prod_bUnion (λ J₁ h₁ J₂ h₂ hne, finset.disjoint_left.2 $ λ J' h₁' h₂', _),
  exact hne (π.eq_of_le_of_le h₁ h₂ ((πi J₁).le_of_mem h₁') ((πi J₂).le_of_mem h₂'))
end

end partition

end box_integral
