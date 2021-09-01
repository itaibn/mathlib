/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.partition.prepartition

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
* `box_integral.box.Icc`: the closed box `set.Icc I.lower I.upper`; defined as a bundled monotone
  map from `box ι` to `set (ι → ℝ)`;
* `box_integral.box.inter`: intersection of two boxes; this is a partial function in the sense that
  its codomain is `part (box ι)`;
* `box_integral.box.volume`: volume of a box defined as the product of `I.upper i - I.lower i` over
  all `i : ι`.

### Partitions

Partition of a box `I` in `ℝⁿ` (see `box_integral.partition`) is a finite set of pairwise disjoint
boxes such that their union is exactly `I`. We use `boxes : finset (box ι)` to store the set of
boxes. In this file we define the following operations on partitions:

* `box_integral.partition.bUnion`: split each box of a partition into smaller boxes;
* `box_integral.partition.restrict`: restrict a partition to a smaller box.

We also define a `semilattice_inf_top` structure on `box_integral.partition I` for all
`I : box_integral.box ι`.

## Tags

partition
-/

namespace box_integral

open set finset function box
open_locale classical nnreal
noncomputable theory

variables {ι : Type*}

/-- Partition of a box `I` in `ℝⁿ` is a finite set of pairwise disjoint boxes such that their union
is exactly `I`. -/
structure partition (I : box ι) extends prepartition I :=
(exists_mem' : ∀ x ∈ I, ∃ J ∈ boxes, x ∈ J)

namespace partition

variables {I J J₁ J₂ : box ι} (π : partition I) {x : ι → ℝ}

instance : has_mem (box ι) (partition I) := ⟨λ J π, J ∈ π.boxes⟩

@[simp] lemma mem_to_prepartition : J ∈ π.to_prepartition ↔ J ∈ π := iff.rfl
lemma mem_boxes : J ∈ π.boxes ↔ J ∈ π := iff.rfl
@[simp] lemma mem_mk {π h} : J ∈ (mk π h : partition I) ↔ J ∈ π := iff.rfl

lemma exists_mem (h : x ∈ I) : ∃ J ∈ π, x ∈ J := π.exists_mem' x h

lemma le_of_mem (hJ : J ∈ π) : J ≤ I := π.le_of_mem' J hJ

@[simp] lemma bUnion_mem_coe (π : partition I) :
  (⋃ J ∈ π, ↑J) = (I : set (ι → ℝ)) :=
begin
  ext x,
  simp only [mem_Union],
  refine ⟨_, π.exists_mem⟩,
  rintro ⟨J, hJ, hx⟩,
  exact π.le_of_mem hJ hx
end

lemma disjoint_coe_of_mem (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (h : J₁ ≠ J₂) :
  disjoint (J₁ : set (ι → ℝ)) J₂ :=
π.pairwise_disjoint J₁ h₁ J₂ h₂ h

lemma eq_of_mem_of_mem (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hx₁ : x ∈ J₁) (hx₂ : x ∈ J₂) :
  J₁ = J₂ :=
π.to_prepartition.eq_of_mem_of_mem h₁ h₂ hx₁ hx₂

lemma eq_of_le_of_le (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hle₁ : J ≤ J₁) (hle₂ : J ≤ J₂) :
  J₁ = J₂ :=
π.to_prepartition.eq_of_le_of_le h₁ h₂ hle₁ hle₂

lemma eq_of_le (h₁ : J₁ ∈ π) (h₂ : J₂ ∈ π) (hle : J₁ ≤ J₂) : J₁ = J₂ :=
π.eq_of_le_of_le h₁ h₂ le_rfl hle

lemma disjoint_boxes_of_disjoint (h : disjoint (I : set (ι → ℝ)) J) (π : partition I)
  (π' : partition J) : disjoint π.boxes π'.boxes :=
π.to_prepartition.disjoint_boxes_of_disjoint h _

lemma lower_le_lower (hJ : J ∈ π) : I.lower ≤ J.lower :=
monotone_lower (π.le_of_mem hJ)

lemma upper_le_upper (hJ : J ∈ π) : J.upper ≤ I.upper :=
monotone_upper (π.le_of_mem hJ)

protected lemma exists_unique (hx : x ∈ I) : ∃! J ∈ π, x ∈ J :=
begin
  rcases π.exists_mem hx with ⟨J, h, hx⟩,
  exact exists_unique.intro2 J h hx (λ J' h' hx', π.eq_of_mem_of_mem h' h hx' hx),
end

lemma nonempty_boxes : π.boxes.nonempty := let ⟨J, hJ, _⟩ := π.exists_mem I.upper_mem in ⟨J, hJ⟩

lemma injective_to_prepartition : injective (to_prepartition : partition I → prepartition I) :=
by { rintro ⟨π₁, h₁⟩ ⟨π₂, h₂⟩ (rfl : π₁ = π₂), refl }

lemma injective_boxes : injective (λ π : partition I, π.boxes) :=
prepartition.injective_boxes.comp injective_to_prepartition

@[simp] lemma to_prepartition_inj {π π' : partition I} :
  π.to_prepartition = π'.to_prepartition ↔ π = π' :=
injective_to_prepartition.eq_iff

@[simp] lemma boxes_inj {π π' : partition I} : π.boxes = π'.boxes ↔ π = π' :=
injective_boxes.eq_iff

@[simp] lemma boxes_subset_iff {π π' : partition I} : π.boxes ⊆ π'.boxes ↔ π = π' :=
begin
  refine ⟨λ H, injective_boxes (subset.antisymm H _), λ H, H ▸ finset.subset.refl _⟩,
  rintro J' (hJ' : J' ∈ π'),
  rcases J'.exists_mem with ⟨x, hx'⟩, rcases π.exists_mem (π'.le_of_mem hJ' hx') with ⟨J, hJ, hx⟩,
  exact π'.eq_of_mem_of_mem (H hJ) hJ' hx hx' ▸ hJ
end

@[ext] lemma eq_of_mem_imp_mem {π π' : partition I} (h : ∀ J ∈ π, J ∈ π') : π = π' :=
boxes_subset_iff.1 h

instance : partial_order (partition I) :=
partial_order.lift to_prepartition injective_to_prepartition

@[simps] instance : has_top (partition I) := ⟨⟨⊤, by simp⟩⟩

@[simp] lemma mem_top : J ∈ (⊤ : partition I) ↔ J = I := mem_singleton

instance : order_top (partition I) :=
{ le_top := λ π J hJ, ⟨I, mem_top.2 rfl, π.le_of_mem hJ⟩,
  .. partition.partial_order, .. partition.has_top }

instance : inhabited (partition I) := ⟨⊤⟩

lemma le_def {π π' : partition I} : π ≤ π' ↔ ∀ J ∈ π, ∃ J' ∈ π', J ≤ J' := iff.rfl

lemma le_def' {π π' : partition I} : π ≤ π' ↔ ∀ (J ∈ π) (J' ∈ π') (x ∈ J) (h' : x ∈ J'), J ≤ J' :=
begin
  refine ⟨λ H J hJ J' hJ' x hx hx', _, λ H J hJ, _⟩,
  { rcases H hJ with ⟨J'', hJ'', Hle⟩,
    rwa π'.eq_of_mem_of_mem hJ' hJ'' hx' (Hle hx) },
  { rcases π'.exists_mem (π.le_of_mem hJ J.upper_mem) with ⟨J', hJ', hx'⟩,
    exact ⟨J', hJ', H J hJ J' hJ' J.upper J.upper_mem hx'⟩ }
end

lemma top_boxes : (⊤ : partition I).boxes = {I} := rfl

/-- Given a partition `π` of a box `I` and a collection of partitions `πi J` of all boxes `J ∈ π`,
returns the partition of `I` into the union of the boxes of all `πi J`.

Though we only use the values of `πi` on the boxes of `π`, we require `πi` to be a globally defined
function. -/
@[simps] def bUnion (πi : Π J : box ι, partition J) : partition I :=
{ to_prepartition := π.to_prepartition.bUnion (λ J, (πi J).to_prepartition),
  exists_mem' := λ x hx,
    let ⟨J, hJ, hxJ⟩ := π.exists_mem hx, ⟨J', hJ', hxJ'⟩ := (πi J).exists_mem hxJ
    in ⟨J', π.to_prepartition.mem_bUnion.2 ⟨J, hJ, hJ'⟩, hxJ'⟩ }

variables {πi : Π J : box ι, partition J}

@[simp] lemma mem_bUnion : J ∈ π.bUnion πi ↔ ∃ J' ∈ π, J ∈ πi J' := π.to_prepartition.mem_bUnion

@[simp] lemma bUnion_boxes : (π.bUnion πi).boxes = π.boxes.bUnion (λ J, (πi J).boxes) := rfl

lemma bUnion_le (πi : Π J, partition J) : π.bUnion πi ≤ π := π.to_prepartition.bUnion_le _

@[simp] lemma bUnion_top : π.bUnion (λ _, ⊤) = π :=
injective_to_prepartition $ π.to_prepartition.bUnion_top

@[congr] lemma bUnion_congr {π₁ π₂ : partition I} {πi₁ πi₂ : Π J, partition J}
  (h : π₁ = π₂) (hi : ∀ J ∈ π₁, πi₁ J = πi₂ J) :
  π₁.bUnion πi₁ = π₂.bUnion πi₂ :=
injective_to_prepartition $ prepartition.bUnion_congr (by rw h) $
  λ J hJ, by rw [hi J hJ]

lemma bUnion_congr_of_le {π₁ π₂ : partition I} {πi₁ πi₂ : Π J, partition J}
  (h : π₁ = π₂) (hi : ∀ J ≤ I, πi₁ J = πi₂ J) :
  π₁.bUnion πi₁ = π₂.bUnion πi₂ :=
bUnion_congr h $ λ J hJ, hi J (π₁.le_of_mem hJ)

/-- Given a box `J ∈ π.bUnion πi`, returns the box `J' ∈ π` such that `J ∈ πi J' _`.
For `J ∉ π.bUnion πi`, returns some box `J' ∈ π`. -/
def bUnion_index (πi : Π J, partition J) (J : box ι) :
  box ι :=
π.to_prepartition.bUnion_index (λ J, (πi J).to_prepartition) J

lemma bUnion_index_mem (hJ : J ∈ π.bUnion πi) : π.bUnion_index πi J ∈ π :=
π.to_prepartition.bUnion_index_mem hJ

lemma bUnion_index_le (πi : Π J, partition J) (J : box ι) : π.bUnion_index πi J ≤ I :=
π.to_prepartition.bUnion_index_le _ J

lemma mem_bUnion_index (hJ : J ∈ π.bUnion πi) : J ∈ πi (π.bUnion_index πi J) :=
π.to_prepartition.mem_bUnion_index hJ

lemma le_bUnion_index (hJ : J ∈ π.bUnion πi) : J ≤ π.bUnion_index πi J :=
π.to_prepartition.le_bUnion_index hJ

/-- Uniqueness property of `box_integral.partition.bUnion_index`. -/
lemma bUnion_index_of_mem (hJ : J ∈ π) {J'} (hJ' : J' ∈ πi J) : π.bUnion_index πi J' = J :=
π.to_prepartition.bUnion_index_of_mem hJ hJ'

lemma bUnion_assoc (πi : Π J, partition J) (πi' : box ι → Π J : box ι, partition J) :
  π.bUnion (λ J, (πi J).bUnion (πi' J)) = (π.bUnion πi).bUnion (λ J, πi' (π.bUnion_index πi J) J) :=
injective_to_prepartition $ π.to_prepartition.bUnion_assoc _ _

@[simps] instance : has_inf (partition I) :=
⟨λ π₁ π₂,
  { to_prepartition := π₁.to_prepartition ⊓ π₂.to_prepartition,
    exists_mem' := λ x hx,
      let ⟨J₁, hJ₁, hx₁⟩ := π₁.exists_mem hx, ⟨J₂, hJ₂, hx₂⟩ := π₂.exists_mem hx
      in ⟨_, prepartition.mem_inf.2 ⟨J₁, hJ₁, J₂, hJ₂, part.get_mem _⟩, mem_inter_get hx₁ hx₂⟩ }⟩

@[simp] lemma mem_inf {π₁ π₂ : partition I} :
  J ∈ π₁ ⊓ π₂ ↔ ∃ (J₁ ∈ π₁) (J₂ ∈ π₂), J ∈ box.inter J₁ J₂ :=
prepartition.mem_inf

lemma inter_get_mem_inf {π₁ π₂ : partition I} (h₁ : J₁ ∈ π₁) (h₂ : J₂ ∈ π₂)
  (H : (J₁ ∩ J₂ : set (ι → ℝ)).nonempty) :
  (J₁.inter J₂).get H ∈ π₁ ⊓ π₂ :=
mem_inf.2 ⟨J₁, h₁, J₂, h₂, H, rfl⟩

instance : semilattice_inf_top (partition I) :=
{ inf_le_left := λ π₁ π₂, @inf_le_left _ _ π₁.to_prepartition π₂.to_prepartition,
  inf_le_right := λ π₁ π₂, @inf_le_right _ _ π₁.to_prepartition π₂.to_prepartition,
  le_inf := λ π π₁ π₂, @_root_.le_inf _ _ π.to_prepartition _ _,
  .. partition.order_top, .. partition.has_inf }

def restrict (π : partition I) (J : box ι) : part (partition J) :=
{ dom := J ≤ I,
  get := λ Hle, ⟨π.to_prepartition.restrict J, λ x hx,
    let ⟨J', hJ', hx'⟩ := π.exists_mem (show x ∈ I, from Hle hx)
    in ⟨_, π.to_prepartition.mem_restrict.2 ⟨_, hJ', part.get_mem _⟩, box.mem_inter_get hx hx'⟩⟩ }

@[simp] lemma restrict_get_to_prepartition (π : partition I) (J : box ι) (Hle : J ≤ I) :
  ((π.restrict J).get Hle).to_prepartition = π.to_prepartition.restrict J := rfl

@[simp] lemma mem_restrict_get (π : partition I) {J J' : box ι} (Hle : J ≤ I) :
  J' ∈ (π.restrict J).get Hle ↔ ∃ J₁ ∈ π, J' ∈ J.inter J₁ :=
π.to_prepartition.mem_restrict

variable [fintype ι]

def distortion : ℝ≥0 := π.to_prepartition.distortion

lemma distortion_le_of_mem (h : J ∈ π) : J.distortion ≤ π.distortion :=
le_sup h

lemma distortion_le_iff {c : ℝ≥0} : π.distortion ≤ c ↔ ∀ J ∈ π, box.distortion J ≤ c :=
sup_le_iff

lemma distortion_bUnion (π : partition I) (πi : Π J, partition J) :
  (π.bUnion πi).distortion = π.boxes.sup (λ J, (πi J).distortion) :=
sup_bUnion _ _

lemma distortion_of_const {c : ℝ≥0} (hc : ∀ J ∈ π, box.distortion J = c) : π.distortion = c :=
(sup_congr rfl hc).trans $ sup_const π.nonempty_boxes _

@[simp] lemma distortion_top : distortion (⊤ : partition I) = I.distortion := sup_singleton

end partition

end box_integral
