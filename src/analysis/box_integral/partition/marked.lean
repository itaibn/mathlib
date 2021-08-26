import analysis.box_integral.partition.basic

noncomputable theory
open_locale classical ennreal

namespace box_integral

variables {ι : Type*}

structure marked_partition (I : box ι) extends partition I :=
(mark' : Π J ∈ boxes, ι → ℝ)
(mark_mem_Icc' : ∀ J ∈ boxes, mark' J ‹_› ∈ I.Icc)

namespace marked_partition

variables {I J J₁ J₂ : box ι} (π : marked_partition I) {x : ι → ℝ}

instance : has_mem (box ι) (marked_partition I) := ⟨λ J π, J ∈ π.boxes⟩

@[simp] lemma mem_to_partition {π : marked_partition I} :
  J ∈ π.to_partition ↔ J ∈ π := iff.rfl

@[simp] lemma mem_mk (π : partition I) (f hf) :
  J ∈ mk π f hf ↔ J ∈ π := iff.rfl

def mark (π : marked_partition I) (J : box ι) : ι → ℝ :=
if h : J ∈ π then π.mark' J h else I.upper

lemma mark_of_mem (h : J ∈ π) : π.mark J = π.mark' J h := dif_pos h

lemma mark_of_not_mem (h : J ∉ π) : π.mark J = I.upper := dif_neg h

lemma mark_mem_Icc (J : box ι) : π.mark J ∈ I.Icc :=
by { unfold mark, split_ifs, exacts [π.mark_mem_Icc' _ _, I.upper_mem_Icc] }

end marked_partition

namespace partition

variables {I J : box ι}

def bUnion_marked (π : partition I) (πi : Π J ∈ π, marked_partition J) :
  marked_partition I :=
{ to_partition := π.bUnion (λ J hJ, (πi J ‹_›).to_partition),
  mark' := λ J hJ, (πi (π.bUnion_index _ J)
    (π.bUnion_index_mem (λ J hJ, (πi J ‹_›).to_partition) J)).mark J,
  mark_mem_Icc' := λ J hJ, box.le_iff_Icc.1 (π.bUnion_index_le _ _) ((πi _ _).mark_mem_Icc _) }

@[simp] lemma mem_bUnion_marked (π : partition I) {πi : Π J ∈ π, marked_partition J} :
  J ∈ π.bUnion_marked πi ↔ ∃ J' ∈ π, J ∈ πi J' ‹_› :=
π.mem_bUnion

lemma mark_bUnion_marked (π : partition I) {πi : Π J ∈ π, marked_partition J}
  (hJ : J ∈ π) {J'} (hJ' : J' ∈ πi J hJ) :
  (π.bUnion_marked πi).mark J' = (πi J hJ).mark J' :=
begin
  have : J' ∈ π.bUnion_marked πi, from π.mem_bUnion.2 ⟨J, hJ, hJ'⟩,
  obtain rfl := π.bUnion_index_of_mem hJ hJ',
  simp_rw [marked_partition.mark_of_mem _ this, bUnion_marked]
end

lemma forall_bUnion_marked (p : (ι → ℝ) → box ι → Prop) (π : partition I)
  (πi : Π J ∈ π, marked_partition J) :
  (∀ J ∈ π.bUnion_marked πi, p ((π.bUnion_marked πi).mark J) J) ↔
    ∀ (J ∈ π) (J' ∈ πi J ‹_›), p ((πi J ‹_›).mark J') J' :=
begin
  simp only [bex_imp_distrib, mem_bUnion_marked],
  refine ⟨λ H J hJ J' hJ', _, λ H J' J hJ hJ', _⟩,
  { rw ← π.mark_bUnion_marked hJ hJ', exact H J' J hJ hJ' },
  { rw π.mark_bUnion_marked hJ hJ', exact H J hJ J' hJ' }
end

end partition

namespace marked_partition

variables {I J : box ι} {x : ι → ℝ}

open emetric

def is_Henstock (π : marked_partition I) : Prop := ∀ J ∈ π, π.mark J ∈ J.Icc

@[simp] lemma is_Henstock_bUnion {π : partition I} {πi : Π J ∈ π, marked_partition J} :
  is_Henstock (π.bUnion_marked πi) ↔ ∀ J ∈ π, (πi J ‹_›).is_Henstock :=
π.forall_bUnion_marked (λ x J, x ∈ J.Icc) πi

def is_subordinate [fintype ι] (π : marked_partition I) (r : (ι → ℝ) → ℝ≥0∞) : Prop :=
∀ J ∈ π, (J : _).Icc ⊆ closed_ball (π.mark J) (r $ π.mark J)

@[simp] lemma is_subordinate_bUnion [fintype ι] {π : partition I} {πi : Π J ∈ π, marked_partition J}
  {r : (ι → ℝ) → ℝ≥0∞} :
  is_subordinate (π.bUnion_marked πi) r ↔ ∀ J ∈ π, (πi J ‹_›).is_subordinate r :=
π.forall_bUnion_marked (λ x J, J.Icc ⊆ closed_ball x (r x)) πi

lemma is_subordinate.mono [fintype ι] {π : marked_partition I} {r r' : (ι → ℝ) → ℝ≥0∞}
  (h : ∀ x ∈ I.Icc, r x ≤ r' x) (hr : π.is_subordinate r) :
  π.is_subordinate r' :=
λ J hJ x hx, closed_ball_subset_closed_ball (h _ $ π.mark_mem_Icc _) (hr _ hJ hx)

lemma is_subordinate.ediam_le [fintype ι] {π : marked_partition I} {r : (ι → ℝ) → ℝ≥0∞}
  (h : π.is_subordinate r) (hJ : J ∈ π.boxes) :
  diam J.Icc ≤ 2 * r (π.mark J) :=
calc diam J.Icc ≤ diam (closed_ball (π.mark J) (r $ π.mark J)) : diam_mono (h J hJ)
            ... ≤ 2 * r (π.mark J)                             : diam_closed_ball

lemma is_subordinate.edist_le [fintype ι] {π : marked_partition I} {r : (ι → ℝ) → ℝ≥0∞}
  (h : π.is_subordinate r) (hJ : J ∈ π.boxes) :
  edist J.lower J.upper ≤ 2 * r (π.mark J) :=
edist_le_of_diam_le J.lower_mem_Icc J.upper_mem_Icc (h.ediam_le hJ)

def single (I : box ι) (x : ι → ℝ) (h : x ∈ I.Icc) : marked_partition I :=
⟨⊤, λ J _, x, λ J hJ, h⟩

@[simp] lemma mem_single (h : x ∈ I.Icc) : J ∈ single I x h ↔ J = I := iff.rfl

@[simp] lemma mark_single (h : x ∈ I.Icc) : (single I x h).mark I = x := mark_of_mem _ rfl

instance (I : box ι) : inhabited (marked_partition I) := ⟨single I I.upper I.upper_mem_Icc⟩

lemma forall_mem_single (p : (ι → ℝ) → (box ι) → Prop) {I : box ι} (h : x ∈ I.Icc) :
  (∀ J ∈ (single I x h).boxes, p ((single I x h).mark J) J) ↔ p x I :=
by simp

@[simp] lemma is_Henstock_single (h : x ∈ I.Icc) : is_Henstock (single I x h) :=
(forall_mem_single (λ x J, x ∈ J.Icc) h).2 h

@[simp] lemma is_subordinate_single [fintype ι] (h : x ∈ I.Icc) {r : (ι → ℝ) → ℝ≥0∞} :
  is_subordinate (single I x h) r ↔ I.Icc ⊆ closed_ball x (r x) :=
forall_mem_single (λ x J, J.Icc ⊆ closed_ball x (r x)) h

end marked_partition

end box_integral
