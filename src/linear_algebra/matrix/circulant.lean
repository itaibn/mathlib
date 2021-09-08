/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang
-/
import linear_algebra.matrix.symmetric
import data.polynomial.monomial
import data.matrix.pequiv
import data.equiv.fin

/-!
# Circulant matrices

This file contains the definition and basic results about circulant matrices.

## Main results

- `matrix.circulant`: introduce the definition of a circulant matrix
                generated by a given vector `v : I → α`.

## Implementation notes

`fin.foo` is the `fin n` version of `foo`.
Namely, the index type of the circulant matrices in discussion is `fin n`.

## Tags

circulant, matrix
-/

variables {α β I J R : Type*} {n : ℕ}

namespace matrix

open function
open_locale matrix big_operators

/-- Given the condition `[has_sub I]` and a vector `v : I → α`,
    we define `circulant v` to be the circulant matrix generated by `v` of type `matrix I I α`. -/
def circulant [has_sub I] (v : I → α) : matrix I I α
| i j := v (i - j)

lemma circulant_col_zero_eq [add_group I] (v : I → α) :
  (λ i, (circulant v) i 0) = v :=
by ext; simp [circulant]

lemma circulant_injective [add_group I] : injective (λ v : I → α, circulant v) :=
begin
  intros v w h,
  dsimp at h,
  rw [← circulant_col_zero_eq v, ← circulant_col_zero_eq w, h]
end

lemma fin.circulant_injective : ∀ n, injective (λ v : fin n → α, circulant v)
| 0     := dec_trivial
| (n+1) := circulant_injective

lemma circulant_inj [add_group I] {v w : I → α} :
  circulant v = circulant w ↔ v = w :=
circulant_injective.eq_iff

lemma fin.circulant_inj {v w : fin n → α} :
  circulant v = circulant w ↔ v = w :=
(fin.circulant_injective n).eq_iff

lemma transpose_circulant [add_group I] (v : I → α) :
  (circulant v)ᵀ =  circulant (λ i, v (-i)) :=
by ext; simp [circulant]

lemma conj_transpose_circulant [has_star α] [add_group I] (v : I → α) :
  (circulant v)ᴴ = circulant (star (λ i, v (-i))) :=
by ext; simp [circulant]

lemma fin.transpose_circulant : ∀ {n} (v : fin n → α), (circulant v)ᵀ =  circulant (λ i, v (-i))
| 0     := dec_trivial
| (n+1) := transpose_circulant

lemma fin.conj_transpose_circulant [has_star α] :
  ∀ {n} (v : fin n → α), (circulant v)ᴴ = circulant (star (λ i, v (-i)))
| 0     := dec_trivial
| (n+1) := conj_transpose_circulant

lemma map_circulant [has_sub I] (v : I → α) (f : α → β) :
  (circulant v).map f = circulant (λ i, f (v i)) :=
by ext; simp [circulant]

lemma circulant_neg [has_neg α] [has_sub I] (v : I → α) :
  circulant (- v) = - circulant v :=
by ext; simp [circulant]

lemma circulant_add [has_add α] [has_sub I] (v w : I → α) :
  circulant (v + w) = circulant v + circulant w :=
by ext; simp [circulant]

lemma circulant_sub [has_sub α] [has_sub I] (v w : I → α) :
  circulant (v - w) = circulant v - circulant w :=
by ext; simp [circulant]

lemma circulant_mul [semiring α] [fintype I] [add_comm_group I] (v w : I → α) :
  circulant v ⬝ circulant w = circulant (mul_vec (circulant v) w) :=
begin
  ext i j,
  simp only [mul_apply, mul_vec, circulant, dot_product],
  refine fintype.sum_equiv (equiv.sub_right j) _ _ _,
  intro x,
  simp only [equiv.sub_right_apply],
  congr' 2,
  abel
end

lemma fin.circulant_mul [semiring α] :
  ∀ {n} (v w : fin n → α), circulant v ⬝ circulant w = circulant (mul_vec (circulant v) w)
| 0     := dec_trivial
| (n+1) := circulant_mul

/-- circulant matrices commute in multiplication under certain condations. -/
lemma circulant_mul_comm
  [comm_semigroup α] [add_comm_monoid α] [fintype I] [add_comm_group I] (v w : I → α) :
  circulant v ⬝ circulant w = circulant w ⬝ circulant v :=
begin
  ext i j,
  simp only [mul_apply, circulant, mul_comm],
  refine fintype.sum_equiv ((equiv.sub_left i).trans (equiv.add_right j)) _ _ _,
  intro x,
  congr' 2,
  { simp },
  { simp only [equiv.coe_add_right, function.comp_app,
               equiv.coe_trans, equiv.sub_left_apply],
    abel }
end

lemma fin.circulant_mul_comm [comm_semigroup α] [add_comm_monoid α] :
  ∀ {n} (v w : fin n → α), circulant v ⬝ circulant w = circulant w ⬝ circulant v
| 0     := dec_trivial
| (n+1) := circulant_mul_comm

/-- `k • circulant v` is another circulantcluant matrix `circulant (k • v)`. -/
lemma circulant_smul [has_sub I] [has_scalar R α] {k : R} {v : I → α} :
  circulant (k • v) = k • circulant v :=
by {ext, simp [circulant]}

lemma circulant_zero [has_zero α] [has_sub I]:
  circulant 0 = (0 : matrix I I α) :=
by ext; simp [circulant]

/-- The identity matrix is a circulant matrix. -/
lemma one_eq_circulant [has_zero α] [has_one α] [decidable_eq I] [add_group I]:
  (1 : matrix I I α) = circulant (pi.single 0 1) :=
by { ext i j, simp only [circulant, one_apply, pi.single_apply, sub_eq_zero], congr }

/-- An alternative version of `one_eq_circulant`. -/
lemma one_eq_circulant' [has_zero α] [has_one α] [decidable_eq I] [add_group I] :
  (1 : matrix I I α) = circulant (λ i, (1 : matrix I I α) i 0) :=
by { ext i j, simp only [circulant, one_apply, sub_eq_zero], congr }

lemma fin.one_eq_circulant [has_zero α] [has_one α] :
  ∀ n, (1 : matrix (fin n) (fin n) α) = circulant (λ i, ite (↑i = 0) 1 0)
| 0     := dec_trivial
| (n+1) :=
begin
  ext i j,
  simp only [circulant, one_apply, ← @fin.coe_zero n, fin.coe_injective.eq_iff, sub_eq_zero],
  congr,
end

/-- For a one-ary predicate `p`, `p` applied to every entry of `circulant v` is true
    if `p` applied to every entry of `v` is true. -/
lemma pred_circulant_entry_of_pred_vec_entry [has_sub I] {p : α → Prop} {v : I → α} :
  (∀ k, p (v k)) → ∀ i j, p ((circulant v) i j) :=
begin
  intros h i j,
  simp [circulant],
  exact h (i - j),
end

/-- Given a set `S`, every entry of `circulant v` is in `S` if every entry of `v` is in `S`. -/
lemma circulant_entry_in_of_vec_entry_in [has_sub I] {S : set α} {v : I → α} :
  (∀ k, v k ∈ S) → ∀ i j, (circulant v) i j ∈ S :=
@pred_circulant_entry_of_pred_vec_entry α I _ S v

/-- The circulant matrix `circulant v` is symmetric iff `∀ i j, v (j - i) = v (i - j)`. -/
lemma circulant_is_symm_ext_iff' [has_sub I] {v : I → α} :
  (circulant v).is_symm ↔ ∀ i j, v (j - i) = v (i - j) :=
by simp [is_symm.ext_iff, circulant]

/-- The circulant matrix `circulant v` is symmetric iff `v (- i) = v i` if `[add_group I]`. -/
lemma circulant_is_symm_ext_iff [add_group I] {v : I → α} :
  (circulant v).is_symm ↔ ∀ i, v (- i) = v i :=
begin
  rw [circulant_is_symm_ext_iff'],
  split,
  { intros h i, convert h i 0; simp },
  { intros h i j, convert h (i - j), simp }
end

lemma fin.circulant_is_sym_ext_iff :
  ∀ {n} {v : fin n → α}, (circulant v).is_symm ↔ ∀ i, v (- i) = v i
| 0     := λ v, by simp only [circulant_is_symm_ext_iff', is_empty.forall_iff]
| (n+1) := λ v, circulant_is_symm_ext_iff

/-- If `circulant v` is symmetric, `∀ i j : I, v (j - i) = v (i - j)`. -/
lemma circulant_is_sym_apply' [has_sub I] {v : I → α} (h : (circulant v).is_symm) (i j : I) :
  v (j - i) = v (i - j) :=
circulant_is_symm_ext_iff'.1 h i j

/-- If `circulant v` is symmetric, `∀ i j : I, v (- i) = v i`. -/
lemma circulant_is_sym_apply [add_group I] {v : I → α} (h : (circulant v).is_symm) (i : I) :
  v (-i) = v i :=
circulant_is_symm_ext_iff.1 h i

lemma fin.circulant_is_sym_apply {v : fin n → α} (h : (circulant v).is_symm) (i : fin n) :
  v (-i) = v i :=
fin.circulant_is_sym_ext_iff.1 h i

/-- The associated polynomial `(v 0) + (v 1) * X + ... + (v (n-1)) * X ^ (n-1)` to `circulant v`.-/
noncomputable
def circulant_poly [semiring α] (v : fin n → α) : polynomial α :=
∑ i : fin n, polynomial.monomial i (v i)

/-- `circulant_perm n` is the cyclic permutation over `fin n`. -/
def circulant_perm : Π n, equiv.perm (fin n) := λ n, equiv.symm (fin_rotate n)

/-- `circulant_P α n` is the cyclic permutation matrix of order `n` with entries of type `α`. -/
def circulant_P (α) [has_zero α] [has_one α] (n : ℕ) : matrix (fin n) (fin n) α :=
(circulant_perm n).to_pequiv.to_matrix

end matrix
