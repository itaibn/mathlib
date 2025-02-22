/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import measure_theory.function.continuous_map_dense
import measure_theory.function.l2_space
import measure_theory.measure.haar
import analysis.complex.circle
import topology.metric_space.emetric_paracompact
import topology.continuous_function.stone_weierstrass

/-!

# Fourier analysis on the circle

This file contains basic technical results for a development of Fourier series.

## Main definitions

* `haar_circle`, Haar measure on the circle, normalized to have total measure `1`
* instances `measure_space`, `is_probability_measure` for the circle with respect to this measure
* for `n : ℤ`, `fourier n` is the monomial `λ z, z ^ n`, bundled as a continuous map from `circle`
  to `ℂ`
* for `n : ℤ` and `p : ℝ≥0∞`, `fourier_Lp p n` is an abbreviation for the monomial `fourier n`
  considered as an element of the Lᵖ-space `Lp ℂ p haar_circle`, via the embedding
  `continuous_map.to_Lp`

## Main statements

The theorem `span_fourier_closure_eq_top` states that the span of the monomials `fourier n` is
dense in `C(circle, ℂ)`, i.e. that its `submodule.topological_closure` is `⊤`.  This follows from
the Stone-Weierstrass theorem after checking that it is a subalgebra, closed under conjugation, and
separates points.

The theorem `span_fourier_Lp_closure_eq_top` states that for `1 ≤ p < ∞` the span of the monomials
`fourier_Lp` is dense in `Lp ℂ p haar_circle`, i.e. that its `submodule.topological_closure` is
`⊤`.  This follows from the previous theorem using general theory on approximation of Lᵖ functions
by continuous functions.

The theorem `orthonormal_fourier` states that the monomials `fourier_Lp 2 n` form an orthonormal
set (in the L² space of the circle).

By definition, a Hilbert basis for an inner product space is an orthonormal set whose span is
dense.  Thus, the last two results together establish that the functions `fourier_Lp 2 n` form a
Hilbert basis for L².

## TODO

Once mathlib has general theory showing that a Hilbert basis of an inner product space induces a
unitary equivalence with L², the results in this file will give Fourier series applications such
as Parseval's formula.

-/

noncomputable theory
open_locale ennreal
open topological_space continuous_map measure_theory measure_theory.measure algebra submodule set

local attribute [instance] fact_one_le_two_ennreal

/-! ### Choice of measure on the circle -/

section haar_circle
/-! We make the circle into a measure space, using the Haar measure normalized to have total
measure 1. -/

instance : measurable_space circle := borel circle
instance : borel_space circle := ⟨rfl⟩

/-- Haar measure on the circle, normalized to have total measure 1. -/
def haar_circle : measure circle := haar_measure positive_compacts_univ

instance : is_probability_measure haar_circle := ⟨haar_measure_self⟩

instance : measure_space circle :=
{ volume := haar_circle,
  .. circle.measurable_space }

end haar_circle

/-! ### Monomials on the circle -/

section fourier

/-- The family of monomials `λ z, z ^ n`, parametrized by `n : ℤ` and considered as bundled
continuous maps from `circle` to `ℂ`. -/
@[simps] def fourier (n : ℤ) : C(circle, ℂ) :=
{ to_fun := λ z, z ^ n,
  continuous_to_fun := continuous_subtype_coe.fpow n $ λ z, or.inl (nonzero_of_mem_circle z) }

@[simp] lemma fourier_zero {z : circle} : fourier 0 z = 1 := rfl

@[simp] lemma fourier_neg {n : ℤ} {z : circle} : fourier (-n) z = complex.conj (fourier n z) :=
by simp [← coe_inv_circle_eq_conj z]

@[simp] lemma fourier_add {m n : ℤ} {z : circle} :
  fourier (m + n) z = (fourier m z) * (fourier n z) :=
by simp [fpow_add (nonzero_of_mem_circle z)]

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ`; equivalently, polynomials in
`z` and `conj z`. -/
def fourier_subalgebra : subalgebra ℂ C(circle, ℂ) := algebra.adjoin ℂ (range fourier)

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ` is in fact the linear span of
these functions. -/
lemma fourier_subalgebra_coe : fourier_subalgebra.to_submodule = span ℂ (range fourier) :=
begin
  apply adjoin_eq_span_of_subset,
  refine subset.trans _ submodule.subset_span,
  intros x hx,
  apply submonoid.closure_induction hx (λ _, id) ⟨0, rfl⟩,
  rintros _ _ ⟨m, rfl⟩ ⟨n, rfl⟩,
  refine ⟨m + n, _⟩,
  ext1 z,
  exact fourier_add,
end

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ` separates points. -/
lemma fourier_subalgebra_separates_points : fourier_subalgebra.separates_points :=
begin
  intros x y hxy,
  refine ⟨_, ⟨fourier 1, _, rfl⟩, _⟩,
  { exact subset_adjoin ⟨1, rfl⟩ },
  { simp [hxy] }
end

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ` is invariant under complex
conjugation. -/
lemma fourier_subalgebra_conj_invariant :
  conj_invariant_subalgebra (fourier_subalgebra.restrict_scalars ℝ) :=
begin
  rintros _ ⟨f, hf, rfl⟩,
  change _ ∈ fourier_subalgebra,
  change _ ∈ fourier_subalgebra at hf,
  apply adjoin_induction hf,
  { rintros _ ⟨n, rfl⟩,
    suffices : fourier (-n) ∈ fourier_subalgebra,
    { convert this,
      ext1,
      simp },
    exact subset_adjoin ⟨-n, rfl⟩ },
  { intros c,
    exact fourier_subalgebra.algebra_map_mem (complex.conj c) },
  { intros f g hf hg,
    convert fourier_subalgebra.add_mem hf hg,
    exact alg_hom.map_add _ f g, },
  { intros f g hf hg,
    convert fourier_subalgebra.mul_mem hf hg,
    exact alg_hom.map_mul _ f g, }
end

/-- The subalgebra of `C(circle, ℂ)` generated by `z ^ n` for `n ∈ ℤ` is dense. -/
lemma fourier_subalgebra_closure_eq_top : fourier_subalgebra.topological_closure = ⊤ :=
continuous_map.subalgebra_complex_topological_closure_eq_top_of_separates_points
  fourier_subalgebra
  fourier_subalgebra_separates_points
  fourier_subalgebra_conj_invariant

/-- The linear span of the monomials `z ^ n` is dense in `C(circle, ℂ)`. -/
lemma span_fourier_closure_eq_top : (span ℂ (range fourier)).topological_closure = ⊤ :=
begin
  rw ← fourier_subalgebra_coe,
  exact congr_arg subalgebra.to_submodule fourier_subalgebra_closure_eq_top,
end

/-- The family of monomials `λ z, z ^ n`, parametrized by `n : ℤ` and considered as elements of
the `Lp` space of functions on `circle` taking values in `ℂ`. -/
abbreviation fourier_Lp (p : ℝ≥0∞) [fact (1 ≤ p)] (n : ℤ) : Lp ℂ p haar_circle :=
to_Lp p haar_circle ℂ (fourier n)

/-- For each `1 ≤ p < ∞`, the linear span of the monomials `z ^ n` is dense in
`Lp ℂ p haar_circle`. -/
lemma span_fourier_Lp_closure_eq_top {p : ℝ≥0∞} [fact (1 ≤ p)] (hp : p ≠ ∞) :
  (span ℂ (range (fourier_Lp p))).topological_closure = ⊤ :=
begin
  convert (continuous_map.to_Lp_dense_range ℂ hp haar_circle ℂ).topological_closure_map_submodule
    span_fourier_closure_eq_top,
  rw [map_span, range_comp],
  simp
end

/-- For `n ≠ 0`, a rotation by `n⁻¹ * real.pi` negates the monomial `z ^ n`. -/
lemma fourier_add_half_inv_index {n : ℤ} (hn : n ≠ 0) (z : circle) :
  fourier n ((exp_map_circle (n⁻¹ * real.pi) * z)) = - fourier n z :=
begin
  have : ↑n * ((↑n)⁻¹ * ↑real.pi * complex.I) = ↑real.pi * complex.I,
  { have : (n:ℂ) ≠ 0 := by exact_mod_cast hn,
    field_simp,
    ring },
  simp [mul_fpow, ← complex.exp_int_mul, complex.exp_pi_mul_I, this]
end

/-- The monomials `z ^ n` are an orthonormal set with respect to Haar measure on the circle. -/
lemma orthonormal_fourier : orthonormal ℂ (fourier_Lp 2) :=
begin
  rw orthonormal_iff_ite,
  intros i j,
  rw continuous_map.inner_to_Lp haar_circle (fourier i) (fourier j),
  split_ifs,
  { simp [h, is_probability_measure.measure_univ, ← fourier_neg, ← fourier_add, -fourier_to_fun] },
  simp only [← fourier_add, ← fourier_neg, is_R_or_C.conj_to_complex],
  have hij : -i + j ≠ 0,
  { rw add_comm,
    exact sub_ne_zero.mpr (ne.symm h) },
  exact integral_zero_of_mul_left_eq_neg (is_mul_left_invariant_haar_measure _)
    (fourier_add_half_inv_index hij)
end

end fourier
