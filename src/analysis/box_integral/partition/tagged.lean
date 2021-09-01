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

end prepartition

namespace tagged_prepartition

variables {I J : box ι} {x : ι → ℝ}

/-- Given a tagged partition `π` of `I` and a (not tagged) partition `πi J hJ` of each `J ∈ π`,
returns the tagged partition of `I` into all the boxes of all `πi J hJ`. The tag of a box `J`
is defined to be the `π.tag` of the box of the partition `π` that includes `J`.

Note that usually the result is not a Henstock partition. -/
def bUnion_prepartition (π : tagged_prepartition I) (πi : Π J, prepartition J) :
  tagged_prepartition I :=
{ to_prepartition := π.to_prepartition.bUnion πi,
  tag := λ J, π.tag (π.to_prepartition.bUnion_index πi J),
  tag_mem_Icc := λ J, π.tag_mem_Icc _ }

/-- Given two partitions `π₁` and `π₁`, one of them tagged and the other is not, returns the tagged
partition with `to_partition = π₁.to_partition ⊓ π₂` and tags coming from `π₁`.

Note that usually the result is not a Henstock partition. -/
def inf_prepartition (π : tagged_prepartition I) (π' : prepartition I) :
  tagged_prepartition I :=
π.bUnion_prepartition $ λ J, π'.restrict J

@[simp] lemma inf_prepartition_to_prepartition (π : tagged_prepartition I) (π' : prepartition I) :
  (π.inf_prepartition π').to_prepartition = π.to_prepartition ⊓ π' := rfl

lemma mem_inf_prepartition_comm {π π' : tagged_prepartition I} :
  J ∈ π.inf_prepartition π'.to_prepartition ↔ J ∈ π'.inf_prepartition π.to_prepartition :=
by simp only [← mem_to_prepartition, inf_prepartition_to_prepartition, inf_comm]

open metric

/-- A tagged partition is said to be a Henstock partition if for each `J ∈ π`, the tag of `J`
belongs to `J.Icc`. -/
def is_Henstock (π : tagged_prepartition I) : Prop := ∀ J ∈ π, π.tag J ∈ J.Icc

@[simp] lemma is_Henstock_bUnion {π : prepartition I} {πi : Π J, tagged_prepartition J} :
  is_Henstock (π.bUnion_tagged πi) ↔ ∀ J ∈ π, (πi J).is_Henstock :=
π.forall_bUnion_tagged (λ x J, x ∈ J.Icc) πi

/-- A tagged partition `π` is subordinate to `r : (ι → ℝ) → ℝ` if each box `J ∈ π` is included by
the closed ball with center `π.tag J` and radius `r (π.tag J)`. -/
def is_subordinate [fintype ι] (π : tagged_prepartition I) (r : (ι → ℝ) → ℝ) : Prop :=
∀ J ∈ π, (J : _).Icc ⊆ closed_ball (π.tag J) (r $ π.tag J)

@[simp] lemma is_subordinate_bUnion [fintype ι] {π : prepartition I}
  {πi : Π J, tagged_prepartition J} {r : (ι → ℝ) → ℝ} :
  is_subordinate (π.bUnion_tagged πi) r ↔ ∀ J ∈ π, (πi J).is_subordinate r :=
π.forall_bUnion_tagged (λ x J, J.Icc ⊆ closed_ball x (r x)) πi

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
def single (I : box ι) (x : ι → ℝ) (h : x ∈ I.Icc) : tagged_prepartition I :=
⟨⊤, λ J, x, λ J, h⟩

@[simp] lemma mem_single (h : x ∈ I.Icc) : J ∈ single I x h ↔ J = I := finset.mem_singleton

instance (I : box ι) : inhabited (tagged_prepartition I) := ⟨single I I.upper I.upper_mem_Icc⟩

lemma forall_mem_single (p : (ι → ℝ) → (box ι) → Prop) {I : box ι} (h : x ∈ I.Icc) :
  (∀ J ∈ (single I x h).boxes, p ((single I x h).tag J) J) ↔ p x I :=
by simp

@[simp] lemma is_Henstock_single (h : x ∈ I.Icc) : is_Henstock (single I x h) :=
(forall_mem_single (λ x J, x ∈ J.Icc) h).2 h

@[simp] lemma is_subordinate_single [fintype ι] (h : x ∈ I.Icc) {r : (ι → ℝ) → ℝ} :
  is_subordinate (single I x h) r ↔ I.Icc ⊆ closed_ball x (r x) :=
forall_mem_single (λ x J, J.Icc ⊆ closed_ball x (r x)) h

end tagged_prepartition

/-- A tagged partition is a partition enriched with a tagged point for each box of the partition. -/
structure tagged_partition (I : box ι) extends tagged_prepartition I :=
(exists_mem' : ∀ x ∈ I, ∃ J ∈ boxes, x ∈ J)

namespace tagged_partition

variables {I J J₁ J₂ : box ι} (π : tagged_partition I) {x : ι → ℝ}

instance : has_mem (box ι) (tagged_partition I) := ⟨λ J π, J ∈ π.boxes⟩

@[simp] lemma mem_to_tagged_prepartition {π : tagged_partition I} :
  J ∈ π.to_tagged_prepartition ↔ J ∈ π := iff.rfl

@[simp] lemma mem_mk (π : tagged_prepartition I) (h) :
  J ∈ mk π h ↔ J ∈ π := iff.rfl

/-- Forget tags in a `box_integral.tagged_partition`. -/
@[simps] def to_partition : partition I := { to_prepartition := π.1.1, .. π }

@[simp] lemma mem_to_partition : J ∈ π.to_partition ↔ J ∈ π := iff.rfl

end tagged_partition

namespace partition

variables {I J : box ι}

/-- Given a partition `π` of `I : box_integral.box ι` and a collection of tagged partitions
`πi J` of all boxes `J ∈ π`, returns the tagged partition of `I` into all the boxes of `πi J`
with tags coming from `(πi J).tag`. -/
def bUnion_tagged (π : partition I) (πi : Π J, tagged_partition J) :
  tagged_partition I :=
{ to_tagged_prepartition := π.to_prepartition.bUnion_tagged (λ J, (πi J).to_tagged_prepartition),
  .. π.bUnion (λ J, (πi J).to_partition) }

@[simp] lemma mem_bUnion_tagged (π : partition I) {πi : Π J, tagged_partition J} :
  J ∈ π.bUnion_tagged πi ↔ ∃ J' ∈ π, J ∈ πi J' :=
π.to_prepartition.mem_bUnion_tagged

lemma tag_bUnion_tagged (π : partition I) {πi : Π J, tagged_partition J} (hJ : J ∈ π) {J'}
  (hJ' : J' ∈ πi J) :
  (π.bUnion_tagged πi).tag J' = (πi J).tag J' :=
π.to_prepartition.tag_bUnion_tagged hJ hJ'

lemma forall_bUnion_tagged (p : (ι → ℝ) → box ι → Prop) (π : partition I)
  (πi : Π J, tagged_partition J) :
  (∀ J ∈ π.bUnion_tagged πi, p ((π.bUnion_tagged πi).tag J) J) ↔
    ∀ (J ∈ π) (J' ∈ πi J), p ((πi J).tag J') J' :=
π.to_prepartition.forall_bUnion_tagged p _

end partition

namespace tagged_partition

variables {I J : box ι} {x : ι → ℝ}

/-- Given a tagged partition `π` of `I` and a (not tagged) partition `πi J hJ` of each `J ∈ π`,
returns the tagged partition of `I` into all the boxes of all `πi J hJ`. The tag of a box `J`
is defined to be the `π.tag` of the box of the partition `π` that includes `J`.

Note that usually the result is not a Henstock partition. -/
def bUnion_partition (π : tagged_partition I) (πi : Π J, partition J) :
  tagged_partition I :=
{ to_tagged_prepartition := π.to_tagged_prepartition.bUnion_prepartition
    (λ J, (πi J).to_prepartition),
  .. π.to_partition.bUnion πi }

/-- Given two partitions `π₁` and `π₁`, one of them tagged and the other is not, returns the tagged
partition with `to_partition = π₁.to_partition ⊓ π₂` and tags coming from `π₁`.

Note that usually the result is not a Henstock partition. -/
def inf_partition (π : tagged_partition I) (π' : partition I) :
  tagged_partition I :=
{ to_tagged_prepartition := π.to_tagged_prepartition.inf_prepartition π'.to_prepartition,
  .. (π.to_partition ⊓ π') }

@[simp] lemma inf_partition_to_partition (π : tagged_partition I) (π' : partition I) :
  (π.inf_partition π').to_partition = π.to_partition ⊓ π' := rfl

lemma mem_inf_partition_comm {π π' : tagged_partition I} :
  J ∈ π.inf_partition π'.to_partition ↔ J ∈ π'.inf_partition π.to_partition :=
tagged_prepartition.mem_inf_prepartition_comm

open metric

/-- A tagged partition is said to be a Henstock partition if for each `J ∈ π`, the tag of `J`
belongs to `J.Icc`. -/
def is_Henstock (π : tagged_partition I) : Prop := ∀ J ∈ π, π.tag J ∈ J.Icc

@[simp] lemma is_Henstock_to_tagged_prepartition {π : tagged_partition I} :
  π.to_tagged_prepartition.is_Henstock ↔ is_Henstock π := iff.rfl

@[simp] lemma is_Henstock_bUnion {π : partition I} {πi : Π J, tagged_partition J} :
  is_Henstock (π.bUnion_tagged πi) ↔ ∀ J ∈ π, (πi J).is_Henstock :=
tagged_prepartition.is_Henstock_bUnion

/-- A tagged partition `π` is subordinate to `r : (ι → ℝ) → ℝ` if each box `J ∈ π` is included by
the closed ball with center `π.tag J` and radius `r (π.tag J)`. -/
def is_subordinate [fintype ι] (π : tagged_partition I) (r : (ι → ℝ) → ℝ) : Prop :=
∀ J ∈ π, (J : _).Icc ⊆ closed_ball (π.tag J) (r $ π.tag J)

@[simp] lemma is_subordinate_to_tagged_prepartition [fintype ι] {π : tagged_partition I}
  {r : (ι → ℝ) → ℝ} :
  π.to_tagged_prepartition.is_subordinate r ↔ is_subordinate π r := iff.rfl

@[simp] lemma is_subordinate_bUnion [fintype ι] {π : partition I}
  {πi : Π J, tagged_partition J} {r : (ι → ℝ) → ℝ} :
  is_subordinate (π.bUnion_tagged πi) r ↔ ∀ J ∈ π, (πi J).is_subordinate r :=
tagged_prepartition.is_subordinate_bUnion

lemma is_subordinate.mono [fintype ι] {π : tagged_partition I} {r r' : (ι → ℝ) → ℝ}
  (h : ∀ x ∈ I.Icc, r x ≤ r' x) (hr : π.is_subordinate r) :
  π.is_subordinate r' :=
tagged_prepartition.is_subordinate.mono h hr

lemma is_subordinate.nonneg [fintype ι] {π : tagged_partition I} {r : (ι → ℝ) → ℝ}
  (h : π.is_subordinate r) (hJ : J ∈ π) : 0 ≤ r (π.tag J) :=
tagged_prepartition.is_subordinate.nonneg h hJ

lemma is_subordinate.diam_le [fintype ι] {π : tagged_partition I} {r : (ι → ℝ) → ℝ}
  (h : π.is_subordinate r) (hJ : J ∈ π.boxes) :
  diam J.Icc ≤ 2 * r (π.tag J) :=
tagged_prepartition.is_subordinate.diam_le h hJ

/-- Tagged partition with single box and prescribed tag. -/
@[simps { fully_applied := ff }]
def single (I : box ι) (x : ι → ℝ) (h : x ∈ I.Icc) : tagged_partition I :=
⟨tagged_prepartition.single I x h, by simp⟩

@[simp] lemma mem_single (h : x ∈ I.Icc) : J ∈ single I x h ↔ J = I := finset.mem_singleton

instance (I : box ι) : inhabited (tagged_partition I) := ⟨single I I.upper I.upper_mem_Icc⟩

lemma forall_mem_single (p : (ι → ℝ) → (box ι) → Prop) {I : box ι} (h : x ∈ I.Icc) :
  (∀ J ∈ (single I x h).boxes, p ((single I x h).tag J) J) ↔ p x I :=
by simp

@[simp] lemma is_Henstock_single (h : x ∈ I.Icc) : is_Henstock (single I x h) :=
(forall_mem_single (λ x J, x ∈ J.Icc) h).2 h

@[simp] lemma is_subordinate_single [fintype ι] (h : x ∈ I.Icc) {r : (ι → ℝ) → ℝ} :
  is_subordinate (single I x h) r ↔ I.Icc ⊆ closed_ball x (r x) :=
forall_mem_single (λ x J, J.Icc ⊆ closed_ball x (r x)) h

def distortion [fintype ι] (π : tagged_partition I) : ℝ≥0 := π.to_partition.distortion

lemma distortion_le_of_mem [fintype ι] {π : tagged_partition I} (h : J ∈ π) :
  J.distortion ≤ π.distortion :=
finset.le_sup h

lemma distortion_le_iff [fintype ι] {π : tagged_partition I} {c : ℝ≥0} :
  π.distortion ≤ c ↔ ∀ J ∈ π, box.distortion J ≤ c :=
finset.sup_le_iff

@[simp] lemma distortion_single [fintype ι] (h : x ∈ I.Icc) :
  distortion (single I x h) = I.distortion :=
finset.sup_singleton

end tagged_partition

end box_integral
