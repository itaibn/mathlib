/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.box_integral.partition.basic

/-!
# Tagged partitions

A tagged partition is a partition enriched with a tagged point for each box of the partition. For
simplicity we require that the function `box_integral.tagged_partition.tag` is defined on all boxes
`J : box ι` but use its values only on boxes of the partition. Given
`π : box_integral.tagged_partition I`, we require that each `box_integral.tagged_partition π J`
belongs to `box_integral.box.Icc I`. If for every `J ∈ π`, `π.tag J` belongs to `J.Icc`, then `π` is
called a *Henstock* partition. We do not include this assumption into the definition of a tagged
partition because McShane integral is defined as a limit along tagged partitions without this
requirement.
-/

noncomputable theory
open_locale classical ennreal nnreal
open set function

namespace box_integral

variables {ι : Type*}

/-- A tagged partition is a partition enriched with a tagged point for each box of the partition. -/
structure tagged_prepartition (I : box ι) extends prepartition I :=
(tag : box ι → ι → ℝ)
(tag_mem_Icc : ∀ J, tag J ∈ I.Icc)

namespace tagged_prepartition

variables {I J J₁ J₂ : box ι} (π : tagged_prepartition I) {x : ι → ℝ}

instance : has_mem (box ι) (tagged_prepartition I) := ⟨λ J π, J ∈ π.boxes⟩

@[simp] lemma mem_to_prepartition {π : tagged_prepartition I} :
  J ∈ π.to_prepartition ↔ J ∈ π := iff.rfl

@[simp] lemma mem_mk (π : prepartition I) (f h) :
  J ∈ mk π f h ↔ J ∈ π := iff.rfl

def Union : set (ι → ℝ) := π.to_prepartition.Union

lemma Union_def : π.Union = ⋃ J ∈ π, ↑J := rfl

@[simp] lemma mem_Union : x ∈ π.Union ↔ ∃ J ∈ π, x ∈ J := set.mem_bUnion_iff

lemma subset_Union (h : J ∈ π) : ↑J ⊆ π.Union := subset_bUnion_of_mem h

lemma Union_subset : π.Union ⊆ I := bUnion_subset π.le_of_mem'

def is_partition := π.to_prepartition.is_partition

lemma is_partition_iff_Union_eq : is_partition π ↔ π.Union = I :=
prepartition.is_partition_iff_Union_eq

end tagged_prepartition

namespace prepartition

variables {I J : box ι}

/-- Given a partition `π` of `I : box_integral.box ι` and a collection of tagged partitions
`πi J` of all boxes `J ∈ π`, returns the tagged partition of `I` into all the boxes of `πi J`
with tags coming from `(πi J).tag`. -/
def bUnion_tagged (π : prepartition I) (πi : Π J, tagged_prepartition J) :
  tagged_prepartition I :=
{ to_prepartition := π.bUnion (λ J, (πi J).to_prepartition),
  tag := λ J, (πi (π.bUnion_index (λ J, (πi J).to_prepartition) J)).tag J,
  tag_mem_Icc := λ J, box.le_iff_Icc.1 (π.bUnion_index_le _ _) ((πi _).tag_mem_Icc _) }

@[simp] lemma mem_bUnion_tagged (π : prepartition I) {πi : Π J, tagged_prepartition J} :
  J ∈ π.bUnion_tagged πi ↔ ∃ J' ∈ π, J ∈ πi J' :=
π.mem_bUnion

lemma tag_bUnion_tagged (π : prepartition I) {πi : Π J, tagged_prepartition J} (hJ : J ∈ π) {J'}
  (hJ' : J' ∈ πi J) :
  (π.bUnion_tagged πi).tag J' = (πi J).tag J' :=
begin
  have : J' ∈ π.bUnion_tagged πi, from π.mem_bUnion.2 ⟨J, hJ, hJ'⟩,
  obtain rfl := π.bUnion_index_of_mem hJ hJ',
  refl
end

@[simp] lemma Union_bUnion_tagged (π : prepartition I) (πi : Π J, tagged_prepartition J) :
  (π.bUnion_tagged πi).Union = ⋃ J ∈ π, (πi J).Union :=
Union_bUnion _ _

lemma forall_bUnion_tagged (p : (ι → ℝ) → box ι → Prop) (π : prepartition I)
  (πi : Π J, tagged_prepartition J) :
  (∀ J ∈ π.bUnion_tagged πi, p ((π.bUnion_tagged πi).tag J) J) ↔
    ∀ (J ∈ π) (J' ∈ πi J), p ((πi J).tag J') J' :=
begin
  simp only [bex_imp_distrib, mem_bUnion_tagged],
  refine ⟨λ H J hJ J' hJ', _, λ H J' J hJ hJ', _⟩,
  { rw ← π.tag_bUnion_tagged hJ hJ', exact H J' J hJ hJ' },
  { rw π.tag_bUnion_tagged hJ hJ', exact H J hJ J' hJ' }
end

lemma is_partition.bUnion_tagged {π : prepartition I} (h : is_partition π)
  {πi : Π J, tagged_prepartition J} (hi : ∀ J ∈ π, (πi J).is_partition) :
  (π.bUnion_tagged πi).is_partition :=
h.bUnion hi

end prepartition

namespace tagged_prepartition

variables {I J : box ι} {π π₁ π₂ : tagged_prepartition I} {x : ι → ℝ}

/-- Given a tagged partition `π` of `I` and a (not tagged) partition `πi J hJ` of each `J ∈ π`,
returns the tagged partition of `I` into all the boxes of all `πi J hJ`. The tag of a box `J`
is defined to be the `π.tag` of the box of the partition `π` that includes `J`.

Note that usually the result is not a Henstock partition. -/
def bUnion_prepartition (π : tagged_prepartition I) (πi : Π J, prepartition J) :
  tagged_prepartition I :=
{ to_prepartition := π.to_prepartition.bUnion πi,
  tag := λ J, π.tag (π.to_prepartition.bUnion_index πi J),
  tag_mem_Icc := λ J, π.tag_mem_Icc _ }

lemma is_partition.bUnion_prepartition {π : tagged_prepartition I} (h : is_partition π)
  {πi : Π J, prepartition J} (hi : ∀ J ∈ π, (πi J).is_partition) :
  (π.bUnion_prepartition πi).is_partition :=
h.bUnion hi

/-- Given two partitions `π₁` and `π₁`, one of them tagged and the other is not, returns the tagged
partition with `to_partition = π₁.to_partition ⊓ π₂` and tags coming from `π₁`.

Note that usually the result is not a Henstock partition. -/
def inf_prepartition (π : tagged_prepartition I) (π' : prepartition I) :
  tagged_prepartition I :=
π.bUnion_prepartition $ λ J, π'.restrict J

@[simp] lemma inf_prepartition_to_prepartition (π : tagged_prepartition I) (π' : prepartition I) :
  (π.inf_prepartition π').to_prepartition = π.to_prepartition ⊓ π' := rfl

lemma mem_inf_prepartition_comm :
  J ∈ π₁.inf_prepartition π₂.to_prepartition ↔ J ∈ π₂.inf_prepartition π₁.to_prepartition :=
by simp only [← mem_to_prepartition, inf_prepartition_to_prepartition, inf_comm]

lemma is_partition.inf_prepartition (h₁ : π₁.is_partition) {π₂ : prepartition I}
  (h₂ : π₂.is_partition) :
  (π₁.inf_prepartition π₂).is_partition :=
h₁.inf h₂

open metric

/-- A tagged partition is said to be a Henstock partition if for each `J ∈ π`, the tag of `J`
belongs to `J.Icc`. -/
def is_Henstock (π : tagged_prepartition I) : Prop := ∀ J ∈ π, π.tag J ∈ J.Icc

@[simp] lemma is_Henstock_bUnion_tagged
  {π : prepartition I} {πi : Π J, tagged_prepartition J} :
  is_Henstock (π.bUnion_tagged πi) ↔ ∀ J ∈ π, (πi J).is_Henstock :=
π.forall_bUnion_tagged (λ x J, x ∈ J.Icc) πi

/-- A tagged partition `π` is subordinate to `r : (ι → ℝ) → ℝ` if each box `J ∈ π` is included by
the closed ball with center `π.tag J` and radius `r (π.tag J)`. -/
def is_subordinate [fintype ι] (π : tagged_prepartition I) (r : (ι → ℝ) → ℝ) : Prop :=
∀ J ∈ π, (J : _).Icc ⊆ closed_ball (π.tag J) (r $ π.tag J)

@[simp] lemma is_subordinate_bUnion_tagged [fintype ι]
  {π : prepartition I} {πi : Π J, tagged_prepartition J} {r : (ι → ℝ) → ℝ} :
  is_subordinate (π.bUnion_tagged πi) r ↔ ∀ J ∈ π, (πi J).is_subordinate r :=
π.forall_bUnion_tagged (λ x J, J.Icc ⊆ closed_ball x (r x)) πi

lemma is_subordinate.bUnion_prepartition [fintype ι] {r : (ι → ℝ) → ℝ} (h : is_subordinate π r)
  (πi : Π J, prepartition J) : is_subordinate (π.bUnion_prepartition πi) r :=
λ J hJ, subset.trans (box.le_iff_Icc.1 $ π.to_prepartition.le_bUnion_index hJ) $
  h _ $ π.to_prepartition.bUnion_index_mem hJ

lemma is_subordinate.inf_prepartition [fintype ι] {r : (ι → ℝ) → ℝ}
  (h : is_subordinate π r) (π' : prepartition I) : is_subordinate (π.inf_prepartition π') r :=
h.bUnion_prepartition _

lemma is_subordinate.mono [fintype ι] {π : tagged_prepartition I} {r r' : (ι → ℝ) → ℝ}
  (h : ∀ x ∈ I.Icc, r x ≤ r' x) (hr : π.is_subordinate r) :
  π.is_subordinate r' :=
λ J hJ x hx, closed_ball_subset_closed_ball (h _ $ π.tag_mem_Icc _) (hr _ hJ hx)

lemma is_subordinate.nonneg [fintype ι] {π : tagged_prepartition I} {r : (ι → ℝ) → ℝ}
  (h : π.is_subordinate r) (hJ : J ∈ π) : 0 ≤ r (π.tag J) :=
calc 0 ≤ dist J.upper (π.tag J) : dist_nonneg
   ... ≤ r (π.tag J)            : h J hJ J.upper_mem_Icc

lemma is_subordinate.diam_le [fintype ι] {π : tagged_prepartition I} {r : (ι → ℝ) → ℝ}
  (h : π.is_subordinate r) (hJ : J ∈ π.boxes) :
  diam J.Icc ≤ 2 * r (π.tag J) :=
calc diam J.Icc ≤ diam (closed_ball (π.tag J) (r $ π.tag J)) :
  diam_mono (h J hJ) bounded_closed_ball
            ... ≤ 2 * r (π.tag J) : diam_closed_ball (h.nonneg hJ)

/-- Tagged partition with single box and prescribed tag. -/
@[simps { fully_applied := ff }]
def single (I J : box ι) (hJ :  J ≤ I) (x : ι → ℝ) (h : x ∈ I.Icc) : tagged_prepartition I :=
⟨prepartition.single I J hJ, λ J, x, λ J, h⟩

@[simp] lemma mem_single {J'} (hJ : J ≤ I) (h : x ∈ I.Icc) : J' ∈ single I J hJ x h ↔ J' = J :=
finset.mem_singleton

instance (I : box ι) : inhabited (tagged_prepartition I) := ⟨single I I le_rfl I.upper I.upper_mem_Icc⟩

lemma is_partition_single_iff (hJ : J ≤ I) (h : x ∈ I.Icc) :
  (single I J hJ x h).is_partition ↔ J = I :=
prepartition.is_partition_single_iff hJ

lemma is_partition_single (h : x ∈ I.Icc) : (single I I le_rfl x h).is_partition :=
prepartition.is_partition_top I

lemma forall_mem_single (p : (ι → ℝ) → (box ι) → Prop) (hJ : J ≤ I) (h : x ∈ I.Icc) :
  (∀ J' ∈ single I J hJ x h, p ((single I J hJ x h).tag J') J') ↔ p x J :=
by simp

@[simp] lemma is_Henstock_single_iff (hJ : J ≤ I) (h : x ∈ I.Icc) :
  is_Henstock (single I J hJ x h) ↔ x ∈ J.Icc :=
forall_mem_single (λ x J, x ∈ J.Icc) hJ h

@[simp] lemma is_Henstock_single (h : x ∈ I.Icc) : is_Henstock (single I I le_rfl x h) :=
(is_Henstock_single_iff (le_refl I) h).2 h

@[simp] lemma is_subordinate_single [fintype ι] (hJ : J ≤ I) (h : x ∈ I.Icc) {r : (ι → ℝ) → ℝ} :
  is_subordinate (single I J hJ x h) r ↔ J.Icc ⊆ closed_ball x (r x) :=
forall_mem_single (λ x J, J.Icc ⊆ closed_ball x (r x)) hJ h

/-- Union of two tagged prepartitions with disjoint unions of boxes. -/
def disj_union (π₁ : tagged_prepartition I) :
  tagged_prepartition I →. tagged_prepartition I := λ π₂,
{ dom := disjoint π₁.Union π₂.Union,
  get := λ H,
    { to_prepartition := (π₁.to_prepartition.disj_union π₂.to_prepartition).get H,
      tag := π₁.boxes.piecewise π₁.tag π₂.tag,
      tag_mem_Icc := λ J, by { dunfold finset.piecewise, split_ifs,
        exacts [π₁.tag_mem_Icc J, π₂.tag_mem_Icc J]  } } }

@[simp] lemma disj_union_get_boxes (h : disjoint π₁.Union π₂.Union) : 
  ((π₁.disj_union π₂).get h).boxes = π₁.boxes ∪ π₂.boxes := rfl

@[simp] lemma mem_disj_union_get (h : disjoint π₁.Union π₂.Union) :
  J ∈ (π₁.disj_union π₂).get h ↔ J ∈ π₁ ∨ J ∈ π₂ :=
finset.mem_union

lemma disj_union_tag_of_mem_left (h : disjoint π₁.Union π₂.Union) (hJ : J ∈ π₁) :
  ((π₁.disj_union π₂).get h).tag J = π₁.tag J :=
dif_pos hJ

lemma disj_union_tag_of_mem_right (h : disjoint π₁.Union π₂.Union) (hJ : J ∈ π₂) :
  ((π₁.disj_union π₂).get h).tag J = π₂.tag J :=
dif_neg $ λ h₁, h ⟨π₁.subset_Union h₁ J.upper_mem, π₂.subset_Union hJ J.upper_mem⟩

def union_compl (π : tagged_prepartition I) : tagged_prepartition I →. tagged_prepartition I :=
@pfun.restrict _ _ π.disj_union {π' | π'.Union = I \ π.Union} $ λ π' (H : π'.Union = _),
  disjoint_sdiff_self_right.mono_right H.le

@[simp] lemma union_compl_get_boxes {π₁ π₂ : tagged_prepartition I} (h : π₂.Union = I \ π₁.Union) :
  ((π₁.union_compl π₂).get h).boxes = π₁.boxes ∪ π₂.boxes := rfl

@[simp] lemma mem_union_compl_get (h : π₂.Union = I \ π₁.Union) :
  J ∈ (π₁.union_compl π₂).get h ↔ J ∈ π₁ ∨ J ∈ π₂ :=
finset.mem_union

lemma union_compl_tag_of_mem_left (h : π₂.Union = I \ π₁.Union) (hJ : J ∈ π₁) :
  ((π₁.union_compl π₂).get h).tag J = π₁.tag J :=
dif_pos hJ

lemma union_compl_tag_of_mem_right (h : π₂.Union = I \ π₁.Union) (hJ : J ∈ π₂) :
  ((π₁.union_compl π₂).get h).tag J = π₂.tag J :=
disj_union_tag_of_mem_right _ hJ

lemma is_partition_union_compl_get (h : π₂.Union = I \ π₁.Union) :
  is_partition ((π₁.union_compl π₂).get h) :=
prepartition.is_partition_union_compl_get h

section distortion

variables [fintype ι] (π)
open finset

def distortion : ℝ≥0 := π.to_prepartition.distortion

lemma distortion_le_of_mem (h : J ∈ π) : J.distortion ≤ π.distortion :=
le_sup h

lemma distortion_le_iff {c : ℝ≥0} : π.distortion ≤ c ↔ ∀ J ∈ π, box.distortion J ≤ c :=
sup_le_iff

@[simp] lemma _root_.box_integral.prepartition.distortion_bUnion_tagged (π : prepartition I)
  (πi : Π J, tagged_prepartition J) :
  (π.bUnion_tagged πi).distortion = π.boxes.sup (λ J, (πi J).distortion) :=
sup_bUnion _ _

@[simp] lemma distortion_bUnion_prepartition (π : tagged_prepartition I)
  (πi : Π J, prepartition J) :
  (π.bUnion_prepartition πi).distortion = π.boxes.sup (λ J, (πi J).distortion) :=
sup_bUnion _ _

@[simp] lemma distortion_disj_union_get (h : disjoint π₁.Union π₂.Union) :
  ((π₁.disj_union π₂).get h).distortion = max π₁.distortion π₂.distortion :=
sup_union

lemma distortion_union_compl_get (h : π₂.Union = I \ π₁.Union) :
  ((π₁.union_compl π₂).get h).distortion = max π₁.distortion π₂.distortion :=
sup_union

lemma distortion_of_const {c} (h₁ : π.boxes.nonempty) (h₂ : ∀ J ∈ π, box.distortion J = c) :
  π.distortion = c :=
(sup_congr rfl h₂).trans (sup_const h₁ _)

lemma distortion_single (hJ : J ≤ I) (h : x ∈ I.Icc) :
  distortion (single I J hJ x h) = J.distortion :=
sup_singleton

end distortion

end tagged_prepartition

end box_integral
