/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.instances.real

/-!
# Rectangular boxes in `ℝⁿ`

In this file we define rectangular boxes in `ℝⁿ`. As usual, we represent `ℝⁿ` as the type of
functions `ι → ℝ` (usually `ι = fin n` for some `n`). When we need to interpret a box `[l, u]` as a
set, we use the product `{x | ∀ i, l i < x i ∧ x i ≤ u i}` of half-open intervals `(l i, u i]`. We
exclude `l i` because this way boxes of a partition are disjoint as sets in `ℝⁿ`.

Currently, the only use cases for these constructions are the definitions of Riemann-style integrals
(Riemann, Henstock-Kurzweil, McShane).

## Main definitions

We use the same structure `box_integral.box` both for ambient boxes and for elements of a partition.
Each box is stored as two points `lower upper : ι → ℝ` and a proof of `∀ i, lower i < upper i`. We
define instances `has_mem (ι → ℝ) (box ι)` and `has_coe_t (box ι) (set $ ι → ℝ)` so that each box is
interpreted as the set `{x | ∀ i, x i ∈ set.Ioc (I.lower i) (I.upper i)}`. This way boxes of a
partition are pairwise disjoint and their union is exactly the original box.

We require boxes to be nonempty, because this way coercion to sets is injective. If needed, the
empty box can be represented as `⊥ : with_bot (box_integral.box ι)`.

We define the following operations on boxes:

* coercion to `set (ι → ℝ)` and `has_mem (ι → ℝ) (box_integral.box ι)` as described above;
* a `partial_order` instance such that `I ≤ J` is equivalent to `(I : set (ι → ℝ)) ⊆ J`;
* `box_integral.box.Icc`: the closed box `set.Icc I.lower I.upper`; defined as a bundled monotone
  map from `box ι` to `set (ι → ℝ)`;
* `box_integral.box.inter`: intersection of two boxes; this is a partial function in the sense that
  its codomain is `part (box ι)`;
* `box_integral.box.volume`: volume of a box defined as the product of `I.upper i - I.lower i` over
  all `i : ι`.

## Tags

rectangular box
-/

open set function metric

noncomputable theory
open_locale classical nnreal

namespace box_integral

variables {ι : Type*}

/-!
### Rectangular box: definition and partial order
-/

/-- A nontrivial rectangular box in `ι → ℝ` with corners `lower` and `upper`. Repesents the product
of half-open intervals `(lower i, upper i]`. -/
structure box (ι : Type*) :=
(lower upper : ι → ℝ)
(lower_lt_upper : ∀ i, lower i < upper i)

attribute [simp] box.lower_lt_upper

namespace box

variables (I J : box ι) {x y : ι → ℝ}

instance : inhabited (box ι) := ⟨⟨0, 1, λ i, zero_lt_one⟩⟩

lemma lower_le_upper : I.lower ≤ I.upper := λ i, (I.lower_lt_upper i).le

instance : has_mem (ι → ℝ) (box ι) := ⟨λ x I, ∀ i, x i ∈ Ioc (I.lower i) (I.upper i)⟩
instance : has_coe_t (box ι) (set $ ι → ℝ) := ⟨λ I, {x | x ∈ I}⟩

@[simp] lemma mem_mk {l u x : ι → ℝ} {H} : x ∈ mk l u H ↔ ∀ i, x i ∈ Ioc (l i) (u i) := iff.rfl
@[simp, norm_cast] lemma mem_coe : x ∈ (I : set (ι → ℝ)) ↔ x ∈ I := iff.rfl

lemma mem_def : x ∈ I ↔ ∀ i, x i ∈ Ioc (I.lower i) (I.upper i) := iff.rfl

lemma mem_univ_Ioc {I : box ι}  : x ∈ pi univ (λ i, Ioc (I.lower i) (I.upper i)) ↔ x ∈ I :=
mem_univ_pi

lemma coe_eq_pi : (I : set (ι → ℝ)) = pi univ (λ i, Ioc (I.lower i) (I.upper i)) :=
set.ext $ λ x, mem_univ_Ioc.symm

@[simp] lemma upper_mem : I.upper ∈ I := λ i, right_mem_Ioc.2 $ I.lower_lt_upper i

lemma exists_mem : ∃ x, x ∈ I := ⟨_, I.upper_mem⟩
lemma nonempty_coe : set.nonempty (I : set (ι → ℝ)) := I.exists_mem
@[simp] lemma coe_ne_empty : (I : set (ι → ℝ)) ≠ ∅ := I.nonempty_coe.ne_empty

instance : has_le (box ι) := ⟨λ I J, ∀ ⦃x⦄, x ∈ I → x ∈ J⟩

lemma le_def : I ≤ J ↔ ∀ x ∈ I, x ∈ J := iff.rfl

lemma le_tfae :
  tfae [I ≤ J,
    (I : set (ι → ℝ)) ⊆ J,
    Icc I.lower I.upper ⊆ Icc J.lower J.upper,
    J.lower ≤ I.lower ∧ I.upper ≤ J.upper] :=
begin
  tfae_have : 1 ↔ 2, from iff.rfl,
  tfae_have : 2 → 3, from λ h, by simpa [coe_eq_pi, closure_pi_set] using closure_mono h,
  tfae_have : 3 ↔ 4, from Icc_subset_Icc_iff I.lower_le_upper,
  tfae_have : 4 → 2, from λ h x hx i, Ioc_subset_Ioc (h.1 i) (h.2 i) (hx i),
  tfae_finish
end

variables {I J}

@[simp, norm_cast] lemma coe_subset_coe : (I : set (ι → ℝ)) ⊆ J ↔ I ≤ J := iff.rfl
lemma le_iff_bounds : I ≤ J ↔ J.lower ≤ I.lower ∧ I.upper ≤ J.upper := (le_tfae I J).out 0 3

lemma injective_coe : injective (coe : box ι → set (ι → ℝ)) :=
begin
  rintros ⟨l₁, u₁, h₁⟩ ⟨l₂, u₂, h₂⟩ h,
  simp only [subset.antisymm_iff, coe_subset_coe, le_iff_bounds] at h,
  congr,
  exacts [le_antisymm h.2.1 h.1.1, le_antisymm h.1.2 h.2.2]
end

@[simp, norm_cast] lemma coe_inj : (I : set (ι → ℝ)) = J ↔ I = J :=
injective_coe.eq_iff

@[ext] lemma ext (H : ∀ x, x ∈ I ↔ x ∈ J) : I = J :=
injective_coe $ set.ext H

lemma ne_of_disjoint_coe (h : disjoint (I : set (ι → ℝ)) J) : I ≠ J :=
mt coe_inj.2 $ h.ne I.coe_ne_empty

instance : partial_order (box ι) :=
{ le := (≤),
  .. partial_order.lift (coe : box ι → set (ι → ℝ)) injective_coe }

/-- Closed box corresponding to `I : box_integral.box ι`. -/
protected def Icc : box ι ↪o set (ι → ℝ) :=
order_embedding.of_map_le_iff (λ I : box ι, Icc I.lower I.upper) (λ I J, (le_tfae I J).out 2 0)

lemma Icc_def : I.Icc = Icc I.lower I.upper := rfl

@[simp] lemma upper_mem_Icc (I : box ι) : I.upper ∈ I.Icc := right_mem_Icc.2 I.lower_le_upper
@[simp] lemma lower_mem_Icc (I : box ι) : I.lower ∈ I.Icc := left_mem_Icc.2 I.lower_le_upper

lemma Icc_eq_pi : I.Icc = pi univ (λ i, Icc (I.lower i) (I.upper i)) := (pi_univ_Icc _ _).symm

lemma le_iff_Icc : I ≤ J ↔ I.Icc ⊆ J.Icc := (le_tfae I J).out 0 2

lemma monotone_lower : monotone (λ I : box ι, order_dual.to_dual I.lower) :=
λ I J H, (le_iff_bounds.1 H).1

lemma monotone_upper : monotone (λ I : box ι, I.upper) :=
λ I J H, (le_iff_bounds.1 H).2

/-!
### Intersection of two boxes

Since two nonempty boxes can be disjoint, we can't define a `has_inf` instance on
`box_integral.box ι`. So, we define a function `box_integral.box.inter` that takes a proof of
`(I ∩ J : set (ι → ℝ)).nonempty` as an argument.
-/

lemma nonempty_coe_inter_coe {I J : box ι} :
  (I ∩ J : set (ι → ℝ)).nonempty ↔ ∀ i, max (I.lower i) (J.lower i) < min (I.upper i) (J.upper i) :=
by simp only [coe_eq_pi, ← pi_inter_distrib, univ_pi_nonempty_iff, Ioc_inter_Ioc, set.nonempty_Ioc,
  sup_eq_max, inf_eq_min]

/-- Intersection of two boxes. Since two nonempty boxes can be disjoint, this function that takes a
proof of `(I ∩ J : set (ι → ℝ)).nonempty` as an argument. -/
@[simps dom] def inter (I J : box ι) : part (box ι) :=
{ dom := (I ∩ J : set (ι → ℝ)).nonempty,
  get := λ H, ⟨_, _, nonempty_coe_inter_coe.1 H⟩ }

@[simp, norm_cast] lemma coe_inter_get (H : (I ∩ J : set (ι → ℝ)).nonempty) :
  ((I.inter J).get H : set (ι → ℝ)) = I ∩ J :=
by simp only [inter, coe_eq_pi, ← pi_inter_distrib, Ioc_inter_Ioc, sup_eq_max, inf_eq_min]

@[simp] lemma mem_inter_get_iff (H : (I ∩ J : set (ι → ℝ)).nonempty) :
  x ∈ (I.inter J).get H ↔ x ∈ I ∧ x ∈ J :=
by simp only [← mem_coe, coe_inter_get, mem_inter_eq]

lemma mem_inter_get (hI : x ∈ I) (hJ : x ∈ J) :
  x ∈ (I.inter J).get ⟨x, hI, hJ⟩ :=
(mem_inter_get_iff _).2 ⟨hI, hJ⟩

@[simp] lemma mem_inter {J'} : J' ∈ I.inter J ↔ (J' : set (ι → ℝ)) = I ∩ J :=
⟨λ ⟨H, Heq⟩, Heq ▸ coe_inter_get H,
  λ H, ⟨by simpa [H] using J'.nonempty_coe, injective_coe $ by rw [coe_inter_get, H]⟩⟩

lemma mem_inter' {J'} : J' ∈ I.inter J ↔ ∀ x, x ∈ J' ↔ x ∈ I ∧ x ∈ J :=
by simp [set.ext_iff]

lemma bUnion_mem_inter_coe (I J : box ι) : (⋃ J' ∈ I.inter J, (J' : set (ι → ℝ))) = I ∩ J :=
by simp [-mem_inter, part.mem_eq]

@[simp] lemma bUnion_coe_eq_inter_coe (I J : box ι) :
  (⋃ (J' : box ι) (hJ' : (J' : set (ι → ℝ)) = I ∩ J), (J' : set (ι → ℝ))) = I ∩ J :=
by simpa using bUnion_mem_inter_coe I J

lemma le_left_of_mem_inter {J' : box ι} (h : J' ∈ I.inter J) : J' ≤ I :=
λ x hx, ((mem_inter'.1 h x).1 hx).1

lemma le_right_of_mem_inter {J' : box ι} (h : J' ∈ I.inter J) : J' ≤ J :=
λ x hx, ((mem_inter'.1 h x).1 hx).2

lemma inter_get_le_left (H : (I ∩ J : set (ι → ℝ)).nonempty) : (I.inter J).get H ≤ I :=
λ x hx, ((mem_inter_get_iff H).1 hx).1

lemma inter_get_le_right (H : (I ∩ J : set (ι → ℝ)).nonempty) : (I.inter J).get H ≤ J :=
λ x hx, ((mem_inter_get_iff H).1 hx).2

@[simp] lemma le_inter_get_iff (H : (I ∩ J : set (ι → ℝ)).nonempty) {I'} :
  I' ≤ (I.inter J).get H ↔ I' ≤ I ∧ I' ≤ J :=
by simp only [le_def, mem_inter_get_iff, forall_and_distrib]

lemma le_inter_get {J₁ J₂} (h₁ : I ≤ J₁) (h₂ : I ≤ J₂) :
  I ≤ (J₁.inter J₂).get ⟨I.upper, h₁ I.upper_mem, h₂ I.upper_mem⟩ :=
(le_inter_get_iff _).2 ⟨h₁, h₂⟩

lemma inter_comm :
  I.inter J = J.inter I :=
by { ext, simp [inter_comm] }

lemma inter_of_le (h : I ≤ J) : I.inter J = part.some I :=
part.eq_some_iff.2 $ mem_inter.2 $ eq.symm $ by simpa

lemma inter_of_ge (h : I ≤ J) : J.inter I = part.some I :=
by rw [inter_comm, inter_of_le h]

instance : has_sup (box ι) :=
⟨λ I J, ⟨I.lower ⊓ J.lower, I.upper ⊔ J.upper,
  λ i, (min_le_left _ _).trans_lt $ (I.lower_lt_upper i).trans_le (le_max_left _ _)⟩⟩

instance : semilattice_sup (box ι) :=
{ le_sup_left := λ I J, le_iff_bounds.2 ⟨inf_le_left, le_sup_left⟩,
  le_sup_right := λ I J, le_iff_bounds.2 ⟨inf_le_right, le_sup_right⟩,
  sup_le := λ I₁ I₂ J h₁ h₂, le_iff_bounds.2 ⟨le_inf (monotone_lower h₁) (monotone_lower h₂),
    sup_le (monotone_upper h₁) (monotone_upper h₂)⟩,
  .. box.partial_order, .. box.has_sup }

/-- `comap f I` is the box with corners `I.lower ∘ f` and `I.upper ∘ f`. Note that this definition
ignores the values of `I.lower and `I.upper` outside of `range f`. -/
@[simps] def comap {ι' : Type*} (f : ι → ι') : box ι' →ₘ box ι :=
{ to_fun := λ I, ⟨I.lower ∘ f, I.upper ∘ f, λ i, I.lower_lt_upper (f i)⟩,
  monotone' := λ I J Hle x hx i,
    Ioc_subset_Ioc ((le_iff_bounds.1 Hle).1 _) ((le_iff_bounds.1 Hle).2 _) (hx _) }

section distortion

variable [fintype ι]

/-- Distortion of a box `I` is the maximum of the ratios of the lengths of its edges. -/
def distortion (I : box ι) : ℝ≥0 :=
finset.univ.sup $ λ i : ι, nndist (I : _).lower I.upper / nndist (I.lower i) (I.upper i)

lemma distortion_eq_of_sub_eq_div {I J : box ι} {r : ℝ}
  (h : ∀ i, I.upper i - I.lower i = (J.upper i - J.lower i) / r) :
  distortion I = distortion J :=
begin
  simp only [distortion, nndist_pi_def, real.nndist_eq', h, real.nnabs.map_div],
  congr' 1 with i,
  have : 0 < r,
  { by_contra hr,
    have := div_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 $ J.lower_le_upper i) (not_lt.1 hr),
    rw ← h at this,
    exact this.not_lt (sub_pos.2 $ I.lower_lt_upper i) },
  simp only [nnreal.finset_sup_div, div_div_div_cancel_right _ (real.nnabs.map_ne_zero.2 this.ne')]
end

lemma nndist_le_distortion_mul (I : box ι) (i : ι) :
  nndist I.lower I.upper ≤ I.distortion * nndist (I.lower i) (I.upper i) :=
calc nndist I.lower I.upper =
  (nndist I.lower I.upper / nndist (I.lower i) (I.upper i)) *  nndist (I.lower i) (I.upper i) :
  (div_mul_cancel _ $ mt nndist_eq_zero.1 (I.lower_lt_upper i).ne).symm
... ≤ I.distortion * nndist (I.lower i) (I.upper i) :
  mul_le_mul_right' (finset.le_sup $ finset.mem_univ i) _

lemma dist_le_distortion_mul (I : box ι) (i : ι) :
  dist I.lower I.upper ≤ I.distortion * (I.upper i - I.lower i) :=
have A : I.lower i - I.upper i < 0, from sub_neg.2 (I.lower_lt_upper i),
by simpa only [← nnreal.coe_le_coe, ← dist_nndist, nnreal.coe_mul, real.dist_eq,
  abs_of_neg A, neg_sub] using I.nndist_le_distortion_mul i

lemma diam_Icc_le_distortion_mul (I : box ι) (i : ι) :
  diam I.Icc ≤ I.distortion * (I.upper i - I.lower i) :=
have (0 : ℝ) ≤ I.distortion * (I.upper i - I.lower i),
  from mul_nonneg I.distortion.coe_nonneg (sub_nonneg.2 $ I.lower_le_upper _),
diam_le_of_forall_dist_le this $ λ x hx y hy,
  (real.dist_le_of_mem_pi_Icc hx hy).trans (dist_le_distortion_mul I i)

end distortion

/-- For a box `I`, the hyperplanes passing through its center split `I` into `2 ^ card ι` boxes.
`box_integral.box.split_center_box I s` is one of these boxes. See also
`box_integral.partition.split_center` for the corresponding `box_integral.partition`. -/
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

@[simp] lemma exists_mem_split_center_box {I : box ι} {x : ι → ℝ} :
  (∃ s, x ∈ I.split_center_box s) ↔ x ∈ I :=
⟨λ ⟨s, hs⟩, I.split_center_box_le s hs,
  λ hx, ⟨{i | _ < x i}, mem_split_center_box.2 ⟨hx, λ i, iff.rfl⟩⟩⟩

/-- `box_integral.box.split_center_box` bundled as a `function.embeddinge`. -/
@[simps] def split_center_box_emb (I : box ι) : set ι ↪ box ι :=
⟨split_center_box I, injective_split_center_box I⟩

@[simp] lemma Union_coe_split_center_box (I : box ι) :
  (⋃ s, (I.split_center_box s : set (ι → ℝ))) = I :=
by { ext x, simp }

@[simp] lemma upper_sub_lower_split_center_box (I : box ι) (s : set ι) (i : ι) :
  (I.split_center_box s).upper i - (I.split_center_box s).lower i = (I.upper i - I.lower i) / 2 :=
by by_cases hs : i ∈ s; field_simp [split_center_box, hs, mul_two, two_mul]

end box

end box_integral
