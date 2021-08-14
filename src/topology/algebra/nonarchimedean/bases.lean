/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/

import algebra.algebra.basic
import algebra.module.submodule
import topology.algebra.nonarchimedean.basic
import topology.algebra.filter_basis

/-!
# Bases for topological algebraic structures
-/

open set filter function lattice add_group_with_zero_nhd

structure subgroups_basis {A ι : Type*} [ring A] (B : ι → add_subgroup A) : Prop :=
(inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j)
(mul : ∀ i, ∃ j, (B j : set A) * B j ⊆ B i)
(left_mul : ∀ x : A, ∀ i, ∃ j, (B j : set A) ⊆ (λ y : A, x*y) ⁻¹' (B i))
(right_mul : ∀ x : A, ∀ i, ∃ j, (B j : set A) ⊆ (λ y : A, y*x) ⁻¹' (B i))

namespace subgroups_basis

variables {A ι : Type*} [ring A]

lemma of_comm {A ι : Type*} [comm_ring A] (B : ι → add_subgroup A)
(inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j)
(mul : ∀ i, ∃ j, (B j : set A) * B j ⊆ B i)
(left_mul : ∀ x : A, ∀ i, ∃ j, (B j : set A) ⊆ (λ y : A, x*y) ⁻¹' (B i)) : subgroups_basis B :=
{ inter := inter,
  mul := mul,
  left_mul := left_mul,
  right_mul := begin
    intros x i,
    cases left_mul x i with j hj,
    use j,
    simpa [mul_comm] using hj
  end }

def to_ring_filter_basis [nonempty ι] {B : ι → add_subgroup A}
  (hB : subgroups_basis B) : ring_filter_basis A :=
{ sets := {U | ∃ i, U = B i},
  nonempty := by { inhabit ι, exact ⟨B (default ι), default ι, rfl⟩ },
  inter_sets := begin
    rintros _ _ ⟨i, rfl⟩ ⟨j, rfl⟩,
    cases hB.inter i j with k hk,
    use [B k, k, rfl, hk]
  end,
  zero' := by { rintros _ ⟨i, rfl⟩, exact (B i).zero_mem },
  add' := begin
    rintros _ ⟨i, rfl⟩,
    use [B i, i, rfl],
    rintros x ⟨y, z, y_in, z_in, rfl⟩,
    exact (B i).add_mem y_in z_in
  end,
  neg' := begin
    rintros _ ⟨i, rfl⟩,
    use [B i, i, rfl],
    intros x x_in,
    exact (B i).neg_mem x_in
  end,
  conj' := begin
    rintros x₀ _ ⟨i, rfl⟩,
    use [B i, i, rfl],
    simp
  end,
  mul' := begin
    rintros _ ⟨i, rfl⟩,
    cases hB.mul i with k hk,
    use [B k, k, rfl, hk]
  end,
  mul_left' := begin
    rintros x₀ _ ⟨i, rfl⟩,
    cases hB.left_mul x₀ i with k hk,
    use [B k, k, rfl, hk]
  end,
  mul_right' := begin
    rintros x₀ _ ⟨i, rfl⟩,
    cases hB.right_mul x₀ i with k hk,
    use [B k, k, rfl, hk]
  end }

variables [nonempty ι] {B : ι → add_subgroup A} (hB : subgroups_basis B)

def topology : topological_space A :=
hB.to_ring_filter_basis.to_add_group_filter_basis.topology

def open_add_subgroup (i : ι) : @open_add_subgroup A _ hB.topology:=
{ is_open' := begin
    letI := hB.topology,
    rw is_open_iff_mem_nhds,
    intros a a_in,
    rw (hB.to_ring_filter_basis.to_add_group_filter_basis.nhds_has_basis a).mem_iff,
    use [B i, i, rfl],
    rintros - ⟨b, b_in, rfl⟩,
    exact (B i).add_mem a_in b_in
  end,
  ..B i }

lemma nonarchimedean : @nonarchimedean_ring A _ hB.topology :=
begin
  letI := hB.topology,
  constructor,
  intros U hU,
  obtain ⟨-, ⟨i, rfl⟩, hi : (B i : set A) ⊆ U⟩ :=
    hB.to_ring_filter_basis.to_add_group_filter_basis.nhds_zero_has_basis.mem_iff.mp hU,
  exact ⟨hB.open_add_subgroup i, hi⟩
end

end subgroups_basis

variables {ι R A : Type*} [comm_ring R] [comm_ring A] [algebra R A]

-- TODO: rename and move
instance toto : has_scalar A (submodule R A) :=
⟨λ a S, submodule.map ((linear_map.lsmul A A a).restrict_scalars R) S⟩

structure submodules_basis (B : ι → submodule R A) : Prop :=
(inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j)
(left_mul : ∀ (a : A) i, ∃ j, a • B j ≤ B i)
(mul      : ∀ i, ∃ j, (B j : set A) * B j ⊆ B i)

namespace submodules_basis

variables {B : ι → submodule R A} (hB : submodules_basis B)

def to_subgroups_basis (hB : submodules_basis B) :
  subgroups_basis (λ i, (B i).to_add_subgroup) :=
begin
  apply subgroups_basis.of_comm (λ i, (B i).to_add_subgroup) hB.inter hB.mul,
  intros a i,
  rcases hB.left_mul a i with ⟨j, hj⟩,
  use j,
  rintros b (b_in : b ∈ B j),
  exact hj ⟨b, b_in, rfl⟩
end

end submodules_basis
