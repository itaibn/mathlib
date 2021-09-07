import analysis.box_integral.partition.additive
import measure_theory.measure.lebesgue

open set
noncomputable theory
open_locale ennreal big_operators classical

variables {ι : Type*} [fintype ι]

namespace box_integral

open measure_theory

namespace box

variables (I : box ι)

lemma measurable_set_coe : measurable_set (I : set (ι → ℝ)) :=
begin
  rw [coe_eq_pi],
  haveI := fintype.encodable ι,
  exact measurable_set.univ_pi (λ i, measurable_set_Ioc)
end

lemma measurable_set_Icc : measurable_set I.Icc := measurable_set_Icc

lemma measure_Icc_lt_top (μ : measure (ι → ℝ)) [is_locally_finite_measure μ] : μ I.Icc < ∞ :=
@is_compact.is_finite_measure _ _ _ μ _ _ (is_compact_pi_Icc I.lower I.upper)

lemma measure_coe_lt_top (μ : measure (ι → ℝ)) [is_locally_finite_measure μ] : μ I < ∞ :=
(measure_mono $ coe_subset_Icc).trans_lt (I.measure_Icc_lt_top μ)

end box

end box_integral

open box_integral box_integral.box

namespace measure_theory

namespace measure

@[simps] def to_box_additive (μ : measure (ι → ℝ)) [is_locally_finite_measure μ] :
  ι →ᵇᵃ[⊤] ℝ :=
{ to_fun := λ J, (μ J).to_real,
  sum_partition_boxes' := λ J hJ π hπ,
    begin
      erw [← ennreal.to_real_sum, ← hπ.Union_eq, π.Union_def,
        measure_bUnion_finset π.pairwise_disjoint],
      exacts [λ J hJ, J.measurable_set_coe, λ J hJ, J.measure_coe_lt_top μ]
    end}

end measure

end measure_theory

namespace box_integral

namespace box

open measure_theory

@[simp] lemma volume_apply (I : box ι) :
  (volume : measure (ι → ℝ)).to_box_additive I = ∏ i, (I.upper i - I.lower i) :=
by rw [measure.to_box_additive_apply, coe_eq_pi, real.volume_pi_Ioc_to_real I.lower_le_upper]

lemma volume_face_mul (i : ι) (I : box ι) :
  (volume : measure (({i}ᶜ : set ι) → ℝ)).to_box_additive (I.face i) *
    (I.upper i - I.lower i) = (volume : measure (ι → ℝ)).to_box_additive I  :=
begin
  rw [volume_apply, volume_apply, ← finset.prod_compl_mul_prod ({i} : finset ι),
    finset.prod_singleton],
  congr' 1,
  convert (finset.prod_subtype _ _ _).symm; simp [function.funext_iff]
end

end box

end box_integral
