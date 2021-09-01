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

/-- Given a box `I` and `x ∈ (I.lower i, I.upper i)`, the hyperplane `{y : ι → ℝ | y i = x}` splits
`I` into two boxes. `box_integral.box.split_upper I i x hx` is the box `I ∩ {y | x < y i}`
(if it is nonempty). -/
@[simps] def split_upper (I : box ι) (i : ι) (x : ℝ) :
  part (box ι) :=
{ dom := x < I.upper i,
  get := λ hx, ⟨update I.lower i (max x (I.lower i)), I.upper,
    forall_update_lt_iff.2 ⟨max_lt hx $ I.lower_lt_upper i, λ j _, I.lower_lt_upper j⟩⟩ }

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

@[simp] lemma mem_split_lower {I J : box ι} {i x} :
  J ∈ I.split_lower i x ↔ (J : set (ι → ℝ)) = I ∩ {y | y i ≤ x} :=
begin
  refine ⟨λ ⟨H, Heq⟩, Heq ▸ coe_split_lower_get _, λ H, ⟨_, injective_coe _⟩⟩,
  { have := J.upper_mem, rw [← mem_coe, H] at this,
    exact (this.1 i).1.trans_le this.2 },
  { rw [coe_split_lower_get, H] }
end

@[simp] lemma exists_coe_eq_inter_eval_le_iff {I : box ι} {i x y} :
  (∃ J : box ι, (J : set (ι → ℝ)) = I ∩ {y | y i ≤ x} ∧ y ∈ J) ↔ y ∈ I ∧ y i ≤ x :=
begin
  fsplit,
  { rintro ⟨J, hJ, hy⟩,
    rwa [← mem_coe, hJ] at hy },
  { rintro ⟨hI, hx⟩,
    refine ⟨_, mem_split_lower.1 ⟨_, rfl⟩, I.mem_split_lower_get hI hx⟩ }
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

@[simp] lemma mem_split_upper {I J : box ι} {i x} :
  J ∈ I.split_upper i x ↔ (J : set (ι → ℝ)) = I ∩ {y | x < y i} :=
begin
  refine ⟨λ ⟨H, Heq⟩, Heq ▸ coe_split_upper_get _, λ H, ⟨_, injective_coe _⟩⟩,
  { have := J.upper_mem, rw [← mem_coe, H] at this,
    exact lt_of_lt_of_le this.2 (this.1 i).2 },
  { rw [coe_split_upper_get, H] }
end

@[simp] lemma exists_coe_eq_inter_lt_eval_iff {I : box ι} {i x y} :
  (∃ J : box ι, (J : set (ι → ℝ)) = I ∩ {y | x < y i} ∧ y ∈ J) ↔ y ∈ I ∧ x < y i :=
begin
  fsplit,
  { rintro ⟨J, hJ, hy⟩,
    rwa [← mem_coe, hJ] at hy },
  { rintro ⟨hI, hx⟩,
    refine ⟨_, mem_split_upper.1 ⟨_, rfl⟩, I.mem_split_upper_get hI hx⟩ }
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
      
lemma disjoint_of_mem_split_lower_of_mem_split_upper {I Jl Ju : box ι} {i : ι} {x : ℝ}
  (Hl : Jl ∈ I.split_lower i x) (Hu : Ju ∈ I.split_upper i x) :
  disjoint (Jl : set (ι → ℝ)) Ju :=
begin
  rw [mem_split_lower.1 Hl, mem_split_upper.1 Hu],
  refine (disjoint.inf_left' _ _).inf_right' _,
  exact λ y hy, @not_lt_of_le _ _ (y i) x hy.1 hy.2
end

lemma ne_of_mem_split_lower_of_mem_split_upper {I Jl Ju : box ι} {i : ι} {x : ℝ}
  (hl : Jl ∈ I.split_lower i x) (hu : Ju ∈ I.split_upper i x) : Jl ≠ Ju :=
ne_of_disjoint_coe (disjoint_of_mem_split_lower_of_mem_split_upper hl hu)

lemma disjoint_split_lower_get_split_upper_get {I : box ι} {i : ι} {x : ℝ} (hl hu) :
  disjoint ((I.split_lower i x).get hl : set (ι → ℝ)) ((I.split_upper i x).get hu) :=
disjoint_of_mem_split_lower_of_mem_split_upper (part.get_mem _) (part.get_mem _)

lemma split_lower_get_ne_split_upper_get {I : box ι} {i : ι} {x : ℝ} (hl hu) :
  (I.split_lower i x).get hl ≠ (I.split_upper i x).get hu :=
ne_of_mem_split_lower_of_mem_split_upper (part.get_mem _) (part.get_mem _)

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

namespace partition

private def split_boxes (I : box ι) (i : ι) (x : ℝ) : finset (box ι) :=
(I.split_lower i x).to_finset ∪ (I.split_upper i x).to_finset

private lemma mem_split_boxes {I J : box ι} {i x} :
  J ∈ split_boxes I i x ↔ J ∈ I.split_lower i x ∨ J ∈ I.split_upper i x :=
by simp [split_boxes]

/-- The partition of `I : box ι` into the boxes `I ∩ {y | y ≤ x i}` and `I ∩ {y | x i < y}`.
One of these boxes can be empty, then this partition is just the single-box partition `⊤`. -/
def split (I : box ι) (i : ι) (x : ℝ) :
  partition I :=
{ boxes := split_boxes I i x,
  le_of_mem' := λ J hJ, by { rcases mem_split_boxes.1 hJ with ⟨H, rfl⟩|⟨H, rfl⟩,
    exacts [I.split_lower_get_le, I.split_upper_get_le] },
  exists_mem' := λ y hy, by simp [mem_split_boxes, exists_or_distrib, or_and_distrib_right,
    ← and_or_distrib_left, le_or_lt, hy],
  pairwise_disjoint :=
    begin
      simp only [pairwise_on, finset.mem_coe, mem_split_boxes],
      rintro J₁ (h₁|h₁) J₂ (h₂|h₂) Hne,
      exacts [(Hne $ part.mem_unique h₁ h₂).elim,
        box.disjoint_of_mem_split_lower_of_mem_split_upper h₁ h₂,
        (box.disjoint_of_mem_split_lower_of_mem_split_upper h₂ h₁).symm,
        (Hne $ part.mem_unique h₁ h₂).elim]
    end }

lemma mem_split_iff {I J : box ι} {i : ι} {x : ℝ} :
  J ∈ split I i x ↔ J ∈ I.split_lower i x ∨ J ∈ I.split_upper i x :=
mem_split_boxes

lemma mem_split_iff' {I J : box ι} {i : ι} {x : ℝ} :
  J ∈ split I i x ↔ (J : set (ι → ℝ)) = I ∩ {y | y i ≤ x} ∨
    (J : set (ι → ℝ)) = I ∩ {y | x < y i} :=
by simp [mem_split_iff]

/-- If `I.lower i < x < I.upper i`, then the hyperplane `{y | y i = x}` splits `I` into two
boxes. -/
lemma split_boxes_of_mem_Ioo {I : box ι} {i : ι} {x : ℝ} (h : x ∈ Ioo (I.lower i) (I.upper i)) :
  (split I i x).boxes = {(I.split_lower i x).get h.1, (I.split_upper i x).get h.2} :=
begin
  ext J,
  simp only [finset.mem_insert, finset.mem_singleton, mem_boxes, mem_split_iff, part.eq_get_iff_mem]
end

/-- If `x ∉ (I.lower i, I.upper i)`, then the hyperplane `{y | y i = x}` does not split `I`. -/
lemma split_of_not_mem_Ioo {I : box ι} {i : ι} {x : ℝ} (h : x ∉ Ioo (I.lower i) (I.upper i)) :
  split I i x = ⊤ :=
begin
  symmetry, ext J hJ,
  rcases mem_top.1 hJ with rfl, clear hJ,
  rw [mem_split_iff],
  rw [mem_Ioo, not_and_distrib, not_lt, not_lt] at h,
  cases h; [right, left];
    simp only [box.split_lower_of_upper_le, box.split_upper_of_le_lower, h, part.mem_some]
end

lemma coe_eq_of_mem_split_of_mem_le {I J : box ι} {i : ι} {x : ℝ} {y : ι → ℝ}
  (h₁ : J ∈ split I i x) (h₂ : y ∈ J) (h₃ : y i ≤ x) :
  (J : set (ι → ℝ)) = I ∩ {y | y i ≤ x} :=
(mem_split_iff'.1 h₁).resolve_right $ λ H,
  by { rw [← box.mem_coe, H] at h₂, exact h₃.not_lt h₂.2 }

lemma coe_eq_of_mem_split_of_lt_mem {I J : box ι} {i : ι} {x : ℝ} {y : ι → ℝ}
  (h₁ : J ∈ split I i x) (h₂ : y ∈ J) (h₃ : x < y i) :
  (J : set (ι → ℝ)) = I ∩ {y | x < y i} :=
(mem_split_iff'.1 h₁).resolve_left $ λ H,
  by { rw [← box.mem_coe, H] at h₂, exact h₃.not_le h₂.2 }

@[simp] lemma restrict_split_get {I J : box ι} (h : I ≤ J) (i : ι) (x : ℝ) :
   ((split J i x).restrict I).get h = split I i x :=
begin
  ext J' hJ',
  simp only [mem_split_iff', box.mem_inter, exists_prop, mem_restrict_get] at hJ' ⊢,
  rcases hJ' with ⟨J'', (H''|H''), Heq⟩; [left, right];
    rw [Heq, H'', ← inter_assoc, inter_eq_self_of_subset_left (box.coe_subset_coe.2 h)]
end

@[simp] lemma restrict_split {I J : box ι} (h : I ≤ J) (i : ι) (x : ℝ) :
   (split J i x).restrict I = part.some (split I i x) :=
part.get_eq_iff_eq_some.1 $ restrict_split_get h i x

@[simp] lemma restrict_split_to_prepartition {I J : box ι} (h : I ≤ J) (i : ι) (x : ℝ) :
   (split J i x).to_prepartition.restrict I = (split I i x).to_prepartition :=
by rw [← restrict_get_to_prepartition _ _ h, restrict_split_get h]

lemma inf_split {I : box ι} (π : partition I) (i : ι) (x : ℝ) :
  π ⊓ split I i x = π.bUnion (λ J, split J i x) :=
injective_to_prepartition $ prepartition.bUnion_congr_of_le rfl  $
  λ J hJ, by rw [← restrict_get_to_prepartition _ _ hJ, restrict_split_get]

/-- Split a box along many hyperplanes `{y | y i = x}`; each hyperplane is given by the pair
`(i x)`. -/
def split_many (I : box ι) (s : finset (ι × ℝ)) : partition I :=
s.inf (λ p, split I p.1 p.2)

@[simp] lemma split_many_empty (I : box ι) : split_many I ∅ = ⊤ := finset.inf_empty

@[simp] lemma split_many_insert (I : box ι) (s : finset (ι × ℝ)) (p : ι × ℝ) :
  split_many I (insert p s) = split_many I s ⊓ split I p.1 p.2 :=
by rw [split_many, finset.inf_insert, inf_comm, split_many]

lemma split_many_le_split (I : box ι) {s : finset (ι × ℝ)} {p : ι × ℝ} (hp : p ∈ s) :
  split_many I s ≤ split I p.1 p.2 :=
finset.inf_le hp

lemma inf_split_many {I : box ι} (π : partition I) (s : finset (ι × ℝ)) :
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

lemma exists_split_many_forall_nonempty_imp_le [fintype ι] (s : finset (box ι)) :
  ∃ t : finset (ι × ℝ), ∀ (I : box ι) (J ∈ s) (J' ∈ split_many I t),
    (J ∩ J' : set (ι → ℝ)).nonempty → J' ≤ J :=
begin
  refine ⟨s.bUnion (λ J, finset.univ.bUnion (λ i, {(i, J.lower i), (i, J.upper i)})),
    λ I J hJ J' hJ', nonempty_inter_imp_le_of_subset_of_mem_split_many (λ i, _) hJ'⟩,
  exact λ p hp, finset.mem_bUnion.2 ⟨J, hJ, finset.mem_bUnion.2 ⟨i, finset.mem_univ _, hp⟩⟩
end

lemma exists_split_many_le [fintype ι] {I : box ι} (π : partition I) : ∃ s, split_many I s ≤ π :=
(exists_split_many_forall_nonempty_imp_le π.boxes).imp $ λ s hs, le_def'.2 $
  λ Js hJs J hJ x hxs hx, hs I J hJ _ hJs ⟨x, hx, hxs⟩

end partition

namespace prepartition

variables [fintype ι] {I : box ι} (π : prepartition I)

lemma exists_partition_superset : ∃ π' : partition I, π ⊆ π'.to_prepartition :=
begin
  rcases partition.exists_split_many_forall_nonempty_imp_le π.boxes with ⟨s, hs⟩,
  refine ⟨⟨π.discarding_union (partition.split_many I s).to_prepartition, λ x hx, _⟩,
    left_subset_discarding_union _ _⟩,
  simp only [← mem_Union, ← box.mem_coe],
  erw [bUnion_mem_discarding_union_of_nonempty_inter_imp_le (hs I)],
  rcases (partition.split_many I s).exists_mem hx with ⟨J, hJ, hx⟩,
  exact or.inr (mem_Union.2 ⟨J, mem_Union.2 ⟨hJ, hx⟩⟩)
end

def to_partition : partition I := π.exists_partition_superset.some

lemma subset_to_partition : π ⊆ π.to_partition.to_prepartition :=
π.exists_partition_superset.some_spec

end prepartition

namespace partition

@[elab_as_eliminator]
lemma split_induction_on [fintype ι] {I : box ι} (π : partition I)
  {p : Π J : box ι, partition J → Prop}
  (H_top : ∀ J ≤ I, p J ⊤) (H_split : ∀ (J ≤ I) i x, p J (split J i x))
  (H_bUnion : ∀ (J ≤ I) (π : partition J) (πi : Π J', partition J'),
    (∀ J' ∈ π, p J' (πi J')) → (p J (π.bUnion (λ J', πi J')) ↔ p J π)) : p I π :=
begin
  have : ∀ (s : finset (ι × ℝ)) (J ≤ I), p J (split_many J s),
  { intros s J hle, induction s using finset.induction_on with p s hps ihs,
    { simpa using H_top J hle },
    { rw [split_many_insert, inf_split],
      rwa H_bUnion J hle,
      exact λ J' hJ', H_split _ (le_trans (le_of_mem _ hJ') hle) _ _ } },
  rcases exists_split_many_le π with ⟨s, hs⟩,
  rw [← inf_eq_right, inf_split_many] at hs,
  rw [← H_bUnion I le_rfl, hs],
  exacts [this s I le_rfl, λ J hJ, this s J (le_of_mem _ hJ)]
end

@[elab_as_eliminator]
lemma split_induction_on' [fintype ι] {I : box ι} (π : partition I)
  (p : box ι → finset (box ι) → Prop) (H_top : ∀ J ≤ I, p J {J})
  (H_split : ∀ (J ≤ I) i x hl hu, p J {(J.split_lower i x).get hl, (J.split_upper i x).get hu})
  (H_bUnion : ∀ (J ≤ I) (π : partition J) (πi : Π J', partition J'),
    (∀ J' ∈ π, p J' (πi J').boxes) → (p J (π.bUnion (λ J', πi J')).boxes ↔ p J π.boxes)) :
  p I π.boxes :=
begin
  refine box_integral.partition.split_induction_on π H_top (λ J hJ i x, _) H_bUnion,
  by_cases hx : x ∈ Ioo (J.lower i) (J.upper i),
  { rw split_boxes_of_mem_Ioo hx, exact H_split J hJ i x hx.1 hx.2 },
  { rw [split_of_not_mem_Ioo hx, top_boxes], exact H_top J hJ }
end

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
