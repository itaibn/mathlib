import analysis.box_integral.partition.box
import data.finset.pimage

open set finset function
open_locale classical nnreal
noncomputable theory

namespace box_integral

variables {ι : Type*}

structure prepartition (I : box ι) :=
(boxes : finset (box ι))
(le_of_mem' : ∀ J ∈ boxes, J ≤ I)
(pairwise_disjoint : pairwise_on ↑boxes (disjoint on (coe : box ι → set (ι → ℝ))))

namespace prepartition

variables {I J J₁ J₂ : box ι} (π : prepartition I) {x : ι → ℝ}

instance : has_mem (box ι) (prepartition I) := ⟨λ J π, J ∈ π.boxes⟩

@[simp] lemma mem_boxes : J ∈ π.boxes ↔ J ∈ π := iff.rfl
@[simp] lemma mem_mk {s h₁ h₂} : J ∈ (mk s h₁ h₂ : prepartition I) ↔ J ∈ s := iff.rfl

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

lemma le_of_mem (hJ : J ∈ π) : J ≤ I := π.le_of_mem' J hJ

lemma disjoint_boxes_of_disjoint (h : disjoint (I : set (ι → ℝ)) J) (π : prepartition I)
  (π' : prepartition J) : disjoint π.boxes π'.boxes :=
finset.disjoint_left.2 $ λ J hJ hJ', h ⟨π.le_of_mem hJ J.upper_mem, (π'.le_of_mem hJ' J.upper_mem)⟩

lemma lower_le_lower (hJ : J ∈ π) : I.lower ≤ J.lower := box.monotone_lower (π.le_of_mem hJ)

lemma upper_le_upper (hJ : J ∈ π) : J.upper ≤ I.upper := box.monotone_upper (π.le_of_mem hJ)

lemma injective_boxes : function.injective (boxes : prepartition I → finset (box ι)) :=
by { rintro ⟨s₁, h₁, h₁'⟩ ⟨s₂, h₂, h₂'⟩ (rfl : s₁ = s₂), refl }

@[ext] lemma ext {π₁ π₂ : prepartition I} (h : ∀ J, J ∈ π₁ ↔ J ∈ π₂) : π₁ = π₂ :=
injective_boxes $ finset.ext h

instance : has_subset (prepartition I) := ⟨λ π₁ π₂, ∀ ⦃J⦄, J ∈ π₁ → J ∈ π₂⟩

lemma subset_def {π₁ π₂ : prepartition I} : π₁ ⊆ π₂ ↔ ∀ J ∈ π₁, J ∈ π₂ := iff.rfl

@[simp] lemma boxes_subset_boxes {π₁ π₂ : prepartition I} : π₁.boxes ⊆ π₂.boxes ↔ π₁ ⊆ π₂ := iff.rfl

lemma subset.antisymm {π₁ π₂ : prepartition I} (h : π₁ ⊆ π₂) (h' : π₂ ⊆ π₁) : π₁ = π₂ :=
injective_boxes $ finset.subset.antisymm h h'

instance : has_le (prepartition I) := ⟨λ π π', ∀ ⦃I⦄, I ∈ π → ∃ I' ∈ π', I ≤ I'⟩

instance : order_top (prepartition I) :=
{ le := (≤),
  le_refl := λ π I hI, ⟨I, hI, le_rfl⟩,
  le_trans := λ π₁ π₂ π₃ h₁₂ h₂₃ I₁ hI₁,
    let ⟨I₂, hI₂, hI₁₂⟩ := h₁₂ hI₁, ⟨I₃, hI₃, hI₂₃⟩ := h₂₃ hI₂ in ⟨I₃, hI₃, hI₁₂.trans hI₂₃⟩,
  le_antisymm :=
    begin
      suffices : ∀ {π₁ π₂ : prepartition I}, π₁ ≤ π₂ → π₂ ≤ π₁ → π₁ ⊆ π₂,
        from λ π₁ π₂ h₁ h₂, subset.antisymm (this h₁ h₂) (this h₂ h₁),
      intros π₁ π₂ h₁ h₂ J hJ,
      rcases h₁ hJ with ⟨J', hJ', hle⟩, rcases h₂ hJ' with ⟨J'', hJ'', hle'⟩,
      obtain rfl : J = J'', from π₁.eq_of_le hJ hJ'' (hle.trans hle'),
      obtain rfl : J' = J, from le_antisymm ‹_› ‹_›,
      assumption
    end,
  top := ⟨{I}, by simp, by simp⟩,
  le_top := λ π J hJ, ⟨I, by simp, π.le_of_mem hJ⟩ }

instance : order_bot (prepartition I) :=
{ bot := ⟨∅, λ J hJ, false.elim hJ, λ J hJ, false.elim hJ⟩,
  bot_le := λ π J hJ, false.elim hJ,
  .. prepartition.order_top }

instance : inhabited (prepartition I) := ⟨⊤⟩

lemma le_def {π π' : prepartition I} : π ≤ π' ↔ ∀ J ∈ π, ∃ J' ∈ π', J ≤ J' := iff.rfl

@[simp] lemma mem_top : J ∈ (⊤ : prepartition I) ↔ J = I := finset.mem_singleton

@[simp] lemma top_boxes : (⊤ : prepartition I).boxes = {I} := rfl

@[simp] lemma not_mem_bot : J ∉ (⊥ : prepartition I) := id

@[simp] lemma bot_boxes : (⊥ : prepartition I).boxes = ∅ := rfl

private def bUnion_boxes' (π : prepartition I) (πi : Π J : box ι, prepartition J) : finset (box ι) :=
π.boxes.bUnion $ λ J, (πi J).boxes

private lemma mem_bUnion_boxes' {πi : Π J : box ι, prepartition J} :
  J ∈ bUnion_boxes' π πi ↔ ∃ J₁ ∈ π, J ∈ πi J₁ :=
by simp [bUnion_boxes']

/-- Given a partition `π` of a box `I` and a collection of partitions `πi J` of all boxes `J ∈ π`,
returns the partition of `I` into the union of the boxes of all `πi J`.

Though we only use the values of `πi` on the boxes of `π`, we require `πi` to be a globally defined
function. -/
def bUnion (πi : Π J : box ι, prepartition J) : prepartition I :=
{ boxes := bUnion_boxes' π πi,
  le_of_mem' := λ J hJ, let ⟨J', hJ', hJ⟩ := (mem_bUnion_boxes' π).1 hJ in
    ((πi J').le_of_mem hJ).trans (π.le_of_mem hJ'),
  pairwise_disjoint :=
    begin
      simp only [pairwise_on, finset.mem_coe, mem_bUnion_boxes'],
      rintro J₁' ⟨J₁, hJ₁, hJ₁'⟩ J₂' ⟨J₂, hJ₂, hJ₂'⟩ Hne x ⟨hx₁, hx₂⟩, apply Hne,
      obtain rfl : J₁ = J₂,
        from π.eq_of_mem_of_mem hJ₁ hJ₂ ((πi J₁).le_of_mem hJ₁' hx₁)
          ((πi J₂).le_of_mem hJ₂' hx₂),
      exact (πi J₁).eq_of_mem_of_mem hJ₁' hJ₂' hx₁ hx₂
    end }

variables {πi : Π J : box ι, prepartition J}

@[simp] lemma mem_bUnion : J ∈ π.bUnion πi ↔ ∃ J' ∈ π, J ∈ πi J' := mem_bUnion_boxes' π

@[simp] lemma bUnion_boxes : (π.bUnion πi).boxes = π.boxes.bUnion (λ J, (πi J).boxes) := rfl

lemma bUnion_le (πi : Π J, prepartition J) : π.bUnion πi ≤ π :=
λ J hJ, let ⟨J', hJ', hJ⟩ := π.mem_bUnion.1 hJ in ⟨J', hJ', (πi J').le_of_mem hJ⟩

@[simp] lemma bUnion_top : π.bUnion (λ _, ⊤) = π := by { ext, simp }

@[congr] lemma bUnion_congr {π₁ π₂ : prepartition I} {πi₁ πi₂ : Π J, prepartition J}
  (h : π₁ = π₂) (hi : ∀ J ∈ π₁, πi₁ J = πi₂ J) :
  π₁.bUnion πi₁ = π₂.bUnion πi₂ :=
by { subst π₂, ext J, simp [hi] { contextual := tt } }

lemma bUnion_congr_of_le {π₁ π₂ : prepartition I} {πi₁ πi₂ : Π J, prepartition J}
  (h : π₁ = π₂) (hi : ∀ J ≤ I, πi₁ J = πi₂ J) :
  π₁.bUnion πi₁ = π₂.bUnion πi₂ :=
bUnion_congr h $ λ J hJ, hi J (π₁.le_of_mem hJ)

/-- Given a box `J ∈ π.bUnion πi`, returns the box `J' ∈ π` such that `J ∈ πi J' _`.
For `J ∉ π.bUnion πi`, returns some box `J' ∈ π`. -/
def bUnion_index (πi : Π J, prepartition J) (J : box ι) :
  box ι :=
if hJ : J ∈ π.bUnion πi then (π.mem_bUnion.1 hJ).some else I

lemma bUnion_index_mem (hJ : J ∈ π.bUnion πi) :
  π.bUnion_index πi J ∈ π :=
by { rw [bUnion_index, dif_pos hJ], exact (π.mem_bUnion.1 hJ).some_spec.fst }

lemma bUnion_index_le (πi : Π J, prepartition J) (J : box ι) : π.bUnion_index πi J ≤ I :=
begin
  by_cases hJ : J ∈ π.bUnion πi,
  { exact π.le_of_mem (π.bUnion_index_mem hJ) },
  { rw [bUnion_index, dif_neg hJ], exact le_rfl }
end

lemma mem_bUnion_index (hJ : J ∈ π.bUnion πi) : J ∈ πi (π.bUnion_index πi J) :=
by convert (π.mem_bUnion.1 hJ).some_spec.snd; exact dif_pos hJ

lemma le_bUnion_index (hJ : J ∈ π.bUnion πi) : J ≤ π.bUnion_index πi J :=
le_of_mem _ (π.mem_bUnion_index hJ)

/-- Uniqueness property of `box_integral.partition.bUnion_index`. -/
lemma bUnion_index_of_mem (hJ : J ∈ π) {J'} (hJ' : J' ∈ πi J) : π.bUnion_index πi J' = J :=
have J' ∈ π.bUnion πi, from π.mem_bUnion.2 ⟨J, hJ, hJ'⟩,
π.eq_of_le_of_le (π.bUnion_index_mem this) hJ (π.le_bUnion_index this) (le_of_mem _ hJ')

lemma bUnion_assoc (πi : Π J, prepartition J) (πi' : box ι → Π J : box ι, prepartition J) :
  π.bUnion (λ J, (πi J).bUnion (πi' J)) = (π.bUnion πi).bUnion (λ J, πi' (π.bUnion_index πi J) J) :=
begin
  ext J,
  simp only [mem_bUnion, exists_prop],
  fsplit,
  { rintro ⟨J₁, hJ₁, J₂, hJ₂, hJ⟩,
    refine ⟨J₂, ⟨J₁, hJ₁, hJ₂⟩, _⟩,
    rwa π.bUnion_index_of_mem hJ₁ hJ₂ },
  { rintro ⟨J₁, ⟨J₂, hJ₂, hJ₁⟩, hJ⟩,
    refine ⟨J₂, hJ₂, J₁, hJ₁, _⟩,
    rwa π.bUnion_index_of_mem hJ₂ hJ₁ at hJ }
end

/-- Restrict a partition to a smaller box. -/
@[simps] def restrict (π : prepartition I) (J : box ι) :
  prepartition J :=
{ boxes := π.boxes.pimage J.inter,
  le_of_mem' := λ J' hJ',
    by { rcases mem_pimage.1 hJ' with ⟨J₂, hJ₂, H, rfl⟩, exact box.inter_get_le_left _ },
  pairwise_disjoint :=
    begin
      simp only [pairwise_on, on_fun, finset.coe_pimage, pfun.mem_image, forall_exists_index,
        finset.mem_coe, mem_boxes, box.mem_inter, ← box.coe_inj, ne.def] { contextual := tt },
      rintro - J₁ h₁ - - J₂ h₂ - Hne,
      refine ((π.disjoint_coe_of_mem h₁ h₂ _).inf_left' _).inf_right' _,
      rintro rfl, exact Hne rfl
    end }

@[simp] lemma mem_restrict : J₁ ∈ π.restrict J ↔ ∃ (J' ∈ π), J₁ ∈ J.inter J' :=
by simp [restrict]

@[mono] lemma restrict_mono {π₁ π₂ : prepartition I} (Hle : π₁ ≤ π₂) :
  π₁.restrict J ≤ π₂.restrict J :=
begin
  simp only [le_def, exists_prop, mem_restrict] at Hle ⊢,
  rintro _ ⟨J₁, Hmem₁, Hne, rfl⟩,
  rcases Hle J₁ Hmem₁ with ⟨J₂, Hmem₂, Hle₂⟩,
  exact ⟨_, ⟨J₂, Hmem₂, _, rfl⟩,
    box.le_inter_get (box.inter_get_le_left _) (le_trans (box.inter_get_le_right _) Hle₂)⟩
end

lemma monotone_restrict : monotone (λ π : prepartition I, restrict π J) :=
λ π₁ π₂, restrict_mono

@[simp] lemma restrict_self : π.restrict I = π :=
begin
  ext J, rw [mem_restrict], fsplit,
  { rintro ⟨J₁, hJ₁, hJ⟩,
    rw [box.inter_of_ge (π.le_of_mem hJ₁), part.mem_some_iff] at hJ,
    rwa hJ },
  { refine λ hJ, ⟨J, hJ, _⟩,
    rw [box.inter_of_ge (π.le_of_mem hJ), part.mem_some_iff] }
end

@[simp] lemma restrict_bUnion (πi : Π J, prepartition J) (hJ : J ∈ π) :
  (π.bUnion πi).restrict J = πi J :=
begin
  ext J', simp only [mem_restrict, exists_prop, mem_bUnion], fsplit,
  { rintro ⟨J₁, ⟨J₂, hJ₂, hJ₁⟩, hJi⟩,
    obtain rfl : J = J₂ := π.eq_of_le_of_le hJ hJ₂ (box.le_left_of_mem_inter hJi)
      ((box.le_right_of_mem_inter hJi).trans $ le_of_mem _ hJ₁),
    rw [box.inter_of_ge (le_of_mem _ hJ₁), part.mem_some_iff] at hJi, rwa hJi },
  { refine λ hJ', ⟨J', ⟨J, hJ, hJ'⟩, _⟩,
    rw [box.inter_of_ge (le_of_mem _ hJ'), part.mem_some_iff] }
end

lemma bUnion_le_iff {πi : Π J, prepartition J} {π' : prepartition I} :
  π.bUnion πi ≤ π' ↔ ∀ J ∈ π, πi J ≤ π'.restrict J :=
begin
  fsplit; intros H J hJ,
  { rw ← π.restrict_bUnion πi hJ, exact restrict_mono H },
  { rw mem_bUnion at hJ, rcases hJ with ⟨J₁, h₁, hJ⟩,
    rcases H J₁ h₁ hJ with ⟨J₂, h₂, Hle⟩,
    rw mem_restrict at h₂, rcases h₂ with ⟨J₃, h₃, H, rfl⟩,
    exact ⟨J₃, h₃, Hle.trans $ box.inter_get_le_right _⟩ }
end

instance : has_inf (prepartition I) :=
⟨λ π₁ π₂, π₁.bUnion (λ J, π₂.restrict J)⟩

lemma inf_def (π₁ π₂ : prepartition I) :
  π₁ ⊓ π₂ = π₁.bUnion (λ J, π₂.restrict J) :=
rfl

@[simp] lemma mem_inf {π₁ π₂ : prepartition I} :
  J ∈ π₁ ⊓ π₂ ↔ ∃ (J₁ ∈ π₁) (J₂ ∈ π₂), J ∈ box.inter J₁ J₂ :=
by simp only [inf_def, mem_bUnion, box.mem_inter, mem_restrict]

lemma inter_get_mem_inf {π₁ π₂ : prepartition I} (h₁ : J₁ ∈ π₁) (h₂ : J₂ ∈ π₂)
  (H : (J₁ ∩ J₂ : set (ι → ℝ)).nonempty) :
  (J₁.inter J₂).get H ∈ π₁ ⊓ π₂ :=
mem_inf.2 ⟨J₁, h₁, J₂, h₂, H, rfl⟩

instance : semilattice_inf_top (prepartition I) :=
{ inf_le_left := λ π₁ π₂, π₁.bUnion_le _,
  inf_le_right := λ π₁ π₂, (bUnion_le_iff _).2 (λ J hJ, le_rfl),
  le_inf := λ π π₁ π₂ h₁ h₂ J hJ, let ⟨J₁, hJ₁, hle₁⟩ := h₁ hJ, ⟨J₂, hJ₂, hle₂⟩ := h₂ hJ in
    ⟨_, inter_get_mem_inf hJ₁ hJ₂ _, box.le_inter_get hle₁ hle₂⟩,
  .. prepartition.order_top, .. prepartition.has_inf }

instance : semilattice_inf_bot (prepartition I) :=
{ .. prepartition.order_bot, .. prepartition.semilattice_inf_top }

protected def Union : set (ι → ℝ) := ⋃ J ∈ π, ↑J

@[simp] lemma mem_Union : x ∈ π.Union ↔ ∃ J ∈ π, x ∈ J := set.mem_bUnion_iff

lemma subset_Union (h : J ∈ π) : ↑J ⊆ π.Union := subset_bUnion_of_mem h

@[simps { fully_applied := tt }]
def filter (π : prepartition I) (p : box ι → Prop) : prepartition I :=
{ boxes := π.boxes.filter p,
  le_of_mem' := λ J hJ, π.le_of_mem (mem_filter.1 hJ).1,
  pairwise_disjoint := λ J₁ h₁ J₂ h₂, π.disjoint_coe_of_mem (mem_filter.1 h₁).1
    (mem_filter.1 h₂).1 }

@[simp] lemma mem_filter {p : box ι → Prop} : J ∈ π.filter p ↔ J ∈ π ∧ p J := finset.mem_filter

lemma filter_of_true {p : box ι → Prop} (hp : ∀ J ∈ π, p J) : π.filter p = π :=
by { ext J, simpa using hp J }

@[simp] lemma filter_true : π.filter (λ _, true) = π := π.filter_of_true (λ _ _, trivial)

def disj_union (π₁ π₂ : prepartition I) : part (prepartition I) :=
{ dom := disjoint π₁.Union π₂.Union,
  get := λ H,
  { boxes := π₁.boxes ∪ π₂.boxes,
    le_of_mem' := λ J hJ, (finset.mem_union.1 hJ).elim π₁.le_of_mem π₂.le_of_mem,
    pairwise_disjoint :=
      suffices ∀ (J₁ ∈ π₁) (J₂ ∈ π₂), J₁ ≠ J₂ → disjoint (J₁ : set (ι → ℝ)) J₂,
        by simpa [pairwise_on_union_of_symmetric (symmetric_disjoint.comap _), pairwise_disjoint],
      λ J₁ h₁ J₂ h₂ _, H.mono (π₁.subset_Union h₁) (π₂.subset_Union h₂) }}

@[simp] lemma mem_disj_union_get {π₁ π₂ : prepartition I} (H : disjoint π₁.Union π₂.Union) :
  J ∈ (π₁.disj_union π₂).get H ↔ J ∈ π₁ ∨ J ∈ π₂ :=
finset.mem_union

lemma mem_of_mem_disj_union {π₁ π₂ π₃ : prepartition I} (H : π₃ ∈ π₁.disj_union π₂) :
  J ∈ π₃ ↔ J ∈ π₁ ∨ J ∈ π₂ :=
by { rcases H with ⟨H, rfl⟩, exact mem_disj_union_get H }

def distortion [fintype ι] : ℝ≥0 := π.boxes.sup box.distortion

lemma distortion_le_of_mem [fintype ι] (h : J ∈ π) : J.distortion ≤ π.distortion :=
le_sup h

lemma distortion_le_iff [fintype ι] {c : ℝ≥0} : π.distortion ≤ c ↔ ∀ J ∈ π, box.distortion J ≤ c :=
sup_le_iff

lemma distortion_bUnion [fintype ι] (π : prepartition I) (πi : Π J, prepartition J) :
  (π.bUnion πi).distortion = π.boxes.sup (λ J, (πi J).distortion) :=
sup_bUnion _ _

end prepartition

end box_integral
