/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import topology.instances.real

/-!
# Partitions of rectangular boxes in `ℝⁿ`

In this file we define partitions of rectangular boxes in `ℝⁿ`. As usual, we represent `ℝⁿ` as the
type of functions `ι → ℝ` (usually `ι = fin n` for some `n`). When we need to interpret a box
`[l, u]` as a set, we use the product `{x | ∀ i, l i < x i ∧ x i ≤ u i}` of half-open intervals
`(l i, u i]`. We exclude `l i` because this way boxes of a partition are disjoint as sets in `ℝⁿ`.

Currently, the only use cases for these constructions are the definitions of Riemann-style integrals
(Riemann, Henstock-Kurzweil, McShane).

## Main definitions

### Boxes

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
* `box_integral.box.Icc`: the closed box `set.Icc I.lower I.upper`;
* `box_integral.box.inter`: intersection of two boxes; this function assumes that the boxes have
  nonempty intersection;

-/

open set function

noncomputable theory
open_locale classical

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
def inter (I J : box ι) (H : (I ∩ J : set (ι → ℝ)).nonempty) :
  box ι :=
⟨_, _, nonempty_coe_inter_coe.1 H⟩

@[simp, norm_cast] lemma coe_inter (H : (I ∩ J : set (ι → ℝ)).nonempty) :
  (I.inter J H : set (ι → ℝ)) = I ∩ J :=
by simp only [inter, coe_eq_pi, ← pi_inter_distrib, Ioc_inter_Ioc, sup_eq_max, inf_eq_min]

@[simp] lemma mem_inter (H : (I ∩ J : set (ι → ℝ)).nonempty) :
  x ∈ I.inter J H ↔ x ∈ I ∧ x ∈ J :=
by simp only [← mem_coe, coe_inter, mem_inter_eq]

lemma inter_le_left (H : (I ∩ J : set (ι → ℝ)).nonempty) : I.inter J H ≤ I :=
λ x hx, ((mem_inter H).1 hx).1

lemma inter_le_right (H : (I ∩ J : set (ι → ℝ)).nonempty) : I.inter J H ≤ J :=
λ x hx, ((mem_inter H).1 hx).2

@[simp] lemma le_inter_iff (H : (I ∩ J : set (ι → ℝ)).nonempty) {I'} :
  I' ≤ I.inter J H ↔ I' ≤ I ∧ I' ≤ J :=
by simp only [le_def, mem_inter, forall_and_distrib]

lemma le_inter {J₁ J₂} (h₁ : I ≤ J₁) (h₂ : I ≤ J₂) :
  I ≤ J₁.inter J₂ ⟨I.upper, h₁ I.upper_mem, h₂ I.upper_mem⟩ :=
(le_inter_iff _).2 ⟨h₁, h₂⟩

lemma inter_comm (H : (I ∩ J : set (ι → ℝ)).nonempty) :
  I.inter J H = J.inter I (by rwa inter_comm) :=
ext $ λ x, by simp [and.comm]

instance : has_sup (box ι) :=
⟨λ I J, ⟨I.lower ⊓ J.lower, I.upper ⊔ J.upper,
  λ i, (min_le_left _ _).trans_lt $ (I.lower_lt_upper i).trans_le (le_max_left _ _)⟩⟩

instance : semilattice_sup (box ι) :=
{ le_sup_left := λ I J, le_iff_bounds.2 ⟨inf_le_left, le_sup_left⟩,
  le_sup_right := λ I J, le_iff_bounds.2 ⟨inf_le_right, le_sup_right⟩,
  sup_le := λ I₁ I₂ J h₁ h₂, le_iff_bounds.2 ⟨le_inf (monotone_lower h₁) (monotone_lower h₂),
    sup_le (monotone_upper h₁) (monotone_upper h₂)⟩,
  .. box.partial_order, .. box.has_sup }

end box

structure partition (I : box ι) :=
(boxes : set (box ι))
(finite_boxes : finite boxes)
(bUnion_boxes_coe : (⋃ J ∈ boxes, ↑(J : box ι)) = (I : set (ι → ℝ)))
(pairwise_disjoint : boxes.pairwise_on (disjoint on (coe : box ι → set (ι → ℝ))))

namespace partition

variables {I J J₁ J₂ : box ι} (π : partition I) {x : ι → ℝ}

instance : has_mem (box ι) (partition I) := ⟨λ J π, J ∈ π.boxes⟩

@[simp] lemma mem_boxes : J ∈ π.boxes ↔ J ∈ π := iff.rfl
@[simp] lemma mem_mk {s h₁ h₂ h₃} : J ∈ (mk s h₁ h₂ h₃ : partition I) ↔ J ∈ s := iff.rfl

@[simp] lemma bUnion_mem_coe (π : partition I) :
  (⋃ J ∈ π, ↑J) = (I : set (ι → ℝ)) :=
π.bUnion_boxes_coe

lemma disjoint_coe_of_mem (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (h : J₁ ≠ J₂) :
  disjoint (J₁ : set (ι → ℝ)) J₂ :=
π.pairwise_disjoint J₁ h₁ J₂ h₂ h

lemma eq_of_mem_of_mem (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hx₁ : x ∈ J₁) (hx₂ : x ∈ J₂) :
  J₁ = J₂ :=
by_contra $ λ H, π.disjoint_coe_of_mem h₁ h₂ H ⟨hx₁, hx₂⟩

lemma eq_of_le_of_le (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hle₁ : J ≤ J₁) (hle₂ : J ≤ J₂) :
  J₁ = J₂ :=
π.eq_of_mem_of_mem h₁ h₂ (hle₁ J.upper_mem) (hle₂ J.upper_mem)

lemma eq_of_le (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hle : J₁ ≤ J₂) : J₁ = J₂ :=
π.eq_of_le_of_le h₁ h₂ le_rfl hle

lemma le_of_mem (hJ : J ∈ π) : J ≤ I :=
box.coe_subset_coe.1 $ π.bUnion_boxes_coe ▸ set.subset_bUnion_of_mem hJ

lemma lower_le_lower (hJ : J ∈ π) : I.lower ≤ J.lower :=
box.monotone_lower (π.le_of_mem hJ)

lemma upper_le_upper (hJ : J ∈ π) : J.upper ≤ I.upper :=
box.monotone_upper (π.le_of_mem hJ)

protected lemma exists_unique (hx : x ∈ I) : ∃! J ∈ π, x ∈ J :=
begin
  simp only [← box.mem_coe, ← π.bUnion_mem_coe, set.mem_Union] at hx,
  rcases hx with ⟨J, h, hx⟩,
  exact exists_unique.intro2 J h hx (λ J' h' hx', π.eq_of_mem_of_mem h' h hx' hx),
end

protected lemma «exists» (hx : x ∈ I) : ∃ J ∈ π, x ∈ J :=
(π.exists_unique hx).exists2

@[ext] lemma eq_of_mem_imp_mem {π π' : partition I} (h : ∀ J ∈ π, J ∈ π') : π = π' :=
begin
  suffices : π.boxes = π'.boxes, { cases π, cases π', congr, exact this },
  refine subset.antisymm h (λ J' hJ', _),
  rcases J'.exists_mem with ⟨x, hx'⟩, rcases π.exists (π'.le_of_mem hJ' hx') with ⟨J, hJ, hx⟩,
  exact π'.eq_of_mem_of_mem (h J hJ) hJ' hx hx' ▸ hJ
end

instance : order_top (partition I) :=
{ le := λ π π', ∀ ⦃I⦄, I ∈ π → ∃ I' ∈ π', I ≤ I',
  le_refl := λ π I hI, ⟨I, hI, le_rfl⟩,
  le_trans := λ π₁ π₂ π₃ h₁₂ h₂₃ I₁ hI₁,
    let ⟨I₂, hI₂, hI₁₂⟩ := h₁₂ hI₁, ⟨I₃, hI₃, hI₂₃⟩ := h₂₃ hI₂ in ⟨I₃, hI₃, hI₁₂.trans hI₂₃⟩,
  le_antisymm :=
    begin
      refine λ π π' h h', eq_of_mem_imp_mem (λ J hJ, _),
      rcases h hJ with ⟨J', hJ', hle⟩, rcases h' hJ' with ⟨J'', hJ'', hle'⟩,
      obtain rfl : J = J'', from π.eq_of_le hJ hJ'' (hle.trans hle'),
      obtain rfl : J' = J, from le_antisymm ‹_› ‹_›,
      assumption
    end,
  top := ⟨{I}, finite_singleton _, bUnion_singleton _ _, pairwise_on_singleton _ _⟩,
  le_top := λ π J hJ, ⟨I, rfl, π.le_of_mem hJ⟩ }

instance : inhabited (partition I) := ⟨⊤⟩

lemma le_def {π π' : partition I} : π ≤ π' ↔ ∀ I ∈ π, ∃ I' ∈ π', I ≤ I' := iff.rfl

@[simp] lemma mem_top : J ∈ (⊤ : partition I) ↔ J = I := iff.rfl

def bUnion (πi : Π J ∈ π, partition J) : partition I :=
{ boxes := ⋃ J ∈ π, (πi J ‹_›).boxes,
  finite_boxes := π.finite_boxes.bUnion $ λ J hJ, (πi J hJ).finite_boxes,
  bUnion_boxes_coe := by simp [Union_comm],
  pairwise_disjoint :=
    begin
      simp only [pairwise_on, mem_Union],
      rintro J₁' ⟨J₁, hJ₁, hJ₁'⟩ J₂' ⟨J₂, hJ₂, hJ₂'⟩ Hne x ⟨hx₁, hx₂⟩, apply Hne,
      obtain rfl : J₁ = J₂,
        from π.eq_of_mem_of_mem hJ₁ hJ₂ ((πi J₁ hJ₁).le_of_mem hJ₁' hx₁)
          ((πi J₂ hJ₂).le_of_mem hJ₂' hx₂),
      exact (πi J₁ hJ₁).eq_of_mem_of_mem hJ₁' hJ₂' hx₁ hx₂
    end }

@[simp] lemma mem_bUnion {πi : Π J ∈ π, partition J} :
  J ∈ π.bUnion πi ↔ ∃ J' ∈ π, J ∈ πi J' ‹_› :=
by simp [bUnion]

lemma bUnion_le (πi : Π J ∈ π, partition J) : π.bUnion πi ≤ π :=
λ J hJ, let ⟨J', hJ', hJ⟩ := π.mem_bUnion.1 hJ in ⟨J', hJ', (πi J' hJ').le_of_mem hJ⟩

/-- Given a box `J ∈ π.bUnion πi`, returns the box `J' ∈ π` such that `J ∈ πi J' _`. -/
def bUnion_index (πi : Π J ∈ π, partition J) (J : box ι) (hJ : J ∈ π.bUnion πi) :
  box ι :=
(π.mem_bUnion.1 hJ).some

lemma bUnion_index_mem {πi : Π J ∈ π, partition J} (hJ : J ∈ π.bUnion πi) :
  π.bUnion_index πi J hJ ∈ π :=
(π.mem_bUnion.1 hJ).some_spec.fst

lemma mem_bUnion_index {πi : Π J ∈ π, partition J} (hJ : J ∈ π.bUnion πi) :
  J ∈ πi (π.bUnion_index πi J hJ) (π.bUnion_index_mem hJ) :=
(π.mem_bUnion.1 hJ).some_spec.snd

lemma le_bUnion_index {πi : Π J ∈ π, partition J} (hJ : J ∈ π.bUnion πi) :
  J ≤ π.bUnion_index πi J hJ :=
le_of_mem _ (π.mem_bUnion_index hJ)

lemma bUnion_index_le {πi : Π J ∈ π, partition J} (hJ : J ∈ π.bUnion πi) :
  π.bUnion_index πi J hJ ≤ I:=
le_of_mem _ (π.bUnion_index_mem hJ)

/-- Uniqueness property of `box_integral.partition.bUnion_index`. -/
lemma bUnion_index_of_mem {πi : Π J ∈ π, partition J} (hJ : J ∈ π) {J'} (hJ' : J' ∈ πi J hJ) :
  π.bUnion_index πi J' (π.mem_bUnion.2 ⟨J, hJ, hJ'⟩) = J :=
π.eq_of_le_of_le (π.bUnion_index_mem _) hJ (π.le_bUnion_index _) (le_of_mem _ hJ')

def restrict (π : partition I) (J : box ι) (H : J ≤ I) :
  partition J :=
{ boxes := ⋃ (J' ∈ π) H, {J.inter J' H},
  finite_boxes := π.finite_boxes.bUnion $ λ J' hJ', finite_Union_Prop $
    λ _, finite_singleton _,
  bUnion_boxes_coe := by simp_rw [bUnion_Union, bUnion_singleton,
    box.coe_inter,  Union_nonempty_self, ← inter_Union, π.bUnion_mem_coe,
    inter_eq_left_iff_subset, box.coe_subset_coe, H],
  pairwise_disjoint :=
    begin
      simp only [set.pairwise_on, mem_Union, mem_singleton_iff, on_fun],
      rintro _ ⟨J₁, HJ₁, h₁, rfl⟩ _ ⟨J₂, HJ₂, h₂, rfl⟩ Hne,
      rw [box.coe_inter, box.coe_inter],
      refine ((π.disjoint_coe_of_mem HJ₁ HJ₂ _).inf_left' _).inf_right' _,
      rintro rfl, exact Hne rfl
    end }

@[simp] lemma mem_restrict (H : J ≤ I) :
  J₁ ∈ π.restrict J H ↔ ∃ (J' ∈ π) h, J₁ = J.inter J' h :=
by simp [restrict]

@[mono] lemma restrict_mono {π₁ π₂ : partition I} (H : J ≤ I) (Hle : π₁ ≤ π₂) :
  π₁.restrict J H ≤ π₂.restrict J H :=
begin
  simp only [le_def, exists_prop, mem_restrict] at Hle ⊢,
  rintro _ ⟨J₁, Hmem₁, Hne, rfl⟩,
  rcases Hle J₁ Hmem₁ with ⟨J₂, Hmem₂, Hle₂⟩,
  exact ⟨_, ⟨J₂, Hmem₂, _, rfl⟩,
    box.le_inter (box.inter_le_left _) (le_trans (box.inter_le_right _) Hle₂)⟩,
end

lemma monotone_restrict (H : J ≤ I) : monotone (λ π, restrict π J H) :=
λ π₁ π₂, restrict_mono H

instance : has_inf (partition I) :=
⟨λ π₁ π₂, π₁.bUnion (λ J hJ, π₂.restrict J (π₁.le_of_mem hJ))⟩

@[simp] lemma mem_inf {π₁ π₂ : partition I} :
  J ∈ π₁ ⊓ π₂ ↔ ∃ (J₁ ∈ π₁) (J₂ ∈ π₂) h, J = box.inter J₁ J₂ h :=
by simp [has_inf.inf]

lemma inter_mem_inf {π₁ π₂ : partition I} (h₁ : J₁ ∈ π₁) (h₂ : J₂ ∈ π₂)
  (H : (J₁ ∩ J₂ : set (ι → ℝ)).nonempty) :
  J₁.inter J₂ H ∈ π₁ ⊓ π₂ :=
mem_inf.2 ⟨J₁, h₁, J₂, h₂, H, rfl⟩

instance : semilattice_inf_top (partition I) :=
{ inf_le_left := λ π₁ π₂, π₁.bUnion_le _,
  inf_le_right := λ π₁ π₂ J hJ, let ⟨J₁, hJ₁, J₂, hJ₂, Hne, hJ⟩ := mem_inf.1 hJ
    in hJ.symm ▸ ⟨J₂, hJ₂, box.inter_le_right _⟩,
  le_inf := λ π π₁ π₂ h₁ h₂ J hJ, let ⟨J₁, hJ₁, hle₁⟩ := h₁ hJ, ⟨J₂, hJ₂, hle₂⟩ := h₂ hJ in
    ⟨_, inter_mem_inf hJ₁ hJ₂ _, box.le_inter hle₁ hle₂⟩,
  .. partition.order_top, .. partition.has_inf }

end partition

end box_integral
