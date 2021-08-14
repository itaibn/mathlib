/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/

import topology.algebra.nonarchimedean.bases
import algebra.lie.ideal_operations
/-!
# Adic topology

Given a commutative ring `R` and an ideal `I` in `R`, this file constructs the unique
topology on `R` which is compatible with the ring structure and such that a set is a neighborhood
of zero if and only if it contains a power of `I`. This topology is non-archimedean: every
neighborhood of zero contains an open subgroup, namely a power of `I`.

It also studies the predicate `is_adic` which states that a given topological ring structure is
adic, proving a characterization and showing that raising an ideal to a positive power does not
change the associated topology.

Finally, it defines `with_ideal`, a class registering an ideal in a ring and providing the
corresponding adic topology to the type class inference system.


## Main definitions and results

* `ideal.adic_basis`: the basis of submodules given by powers of an ideal.
* `ideal.adic_topology`: the adic topology associated to an ideal. It has the above basis
  for neighborhoods of zero.
* `ideal.nonarchimedean`: the adic topology is non-archimedean
* `is_ideal_adic_iff`: A topological ring is `J`-adic if and only if it admits the powers of `J` as
  a basis of open neighborhoods of zero.
* `with_ideal`: a class registering an ideal in a ring.

-/

variables {R : Type*} [comm_ring R]

open set topological_add_group submodule filter
open_locale topological_space


namespace ideal

lemma adic_basis (I : ideal R) : submodules_basis (λ n : ℕ, (I^n : ideal R)) :=
{ inter := begin
    intros i j,
    use (i + j),
    rw pow_add,
    exact mul_le_inf
  end,
  left_mul := begin
    intros r n,
    use n,
    rintro a ⟨x, hx, rfl⟩,
    exact (I ^ n).smul_mem r hx
  end,
  mul := begin
    intro n,
    use n,
    rintro a ⟨x, b, hx, hb, rfl⟩,
    exact (I^n).smul_mem x hb
  end }

/-- The adic topology associated to an ideal `I`. This topology admits powers of `I` as a basis of
neighborhoods of zero. It is compatible with the ring structure and is non-archimedean. -/
def adic_topology (I : ideal R) : topological_space R :=
(adic_basis I).to_subgroups_basis.topology

lemma nonarchimedean (I : ideal R) : @nonarchimedean_ring R _ I.adic_topology :=
I.adic_basis.to_subgroups_basis.nonarchimedean

/-- For the `I`-adic topology, the neighborhoods of zero has basis given by the powers of `I`. -/
lemma has_basis_nhds_zero_adic (I : ideal R) :
  has_basis (@nhds R I.adic_topology (0 : R)) (λ n : ℕ, true) (λ n, ((I^n : ideal R) : set R)) :=
⟨begin
  intros U,
  rw I.adic_basis.to_subgroups_basis.to_ring_filter_basis.to_add_group_filter_basis
      .nhds_zero_has_basis.mem_iff,
  split,
  { rintros ⟨-, ⟨i, rfl⟩, h⟩,
    use [i, trivial, h] },
  { rintros ⟨i, -, h⟩,
    use [(I^i : ideal R), i, rfl, h] }
end⟩

end ideal

section is_adic

/-- Given a topology on a ring `R` and an ideal `J`, `is_adic J` means the topology is the
`J`-adic one. -/
def is_adic [H : topological_space R] (J : ideal R) : Prop :=
H = J.adic_topology

/-- A topological ring is `J`-adic if and only if it admits the powers of `J` as a basis of
open neighborhoods of zero. -/
lemma is_ideal_adic_iff [top : topological_space R] [topological_ring R] {J : ideal R} :
  is_adic J ↔ (∀ n : ℕ, is_open ((J^n : ideal R) : set R)) ∧
              (∀ s ∈ 𝓝 (0 : R), ∃ n : ℕ, ((J^n : ideal R) : set R) ⊆ s) :=
begin
  split,
  { intro H,
    change _ = _ at H,
    rw H,
    letI := J.adic_topology,
    split,
    { intro n,
      exact (J.adic_basis.to_subgroups_basis.open_add_subgroup n).is_open' },
    { intros s hs,
      simpa using J.has_basis_nhds_zero_adic.mem_iff.mp hs } },
  { rintro ⟨H₁, H₂⟩,
    apply topological_add_group.ext,
    { apply @topological_ring.to_topological_add_group },
    { apply (subgroups_basis.to_ring_filter_basis _).to_add_group_filter_basis
             .is_topological_add_group },
    { ext s,
      letI := ideal.adic_basis J,
      rw J.has_basis_nhds_zero_adic.mem_iff,
      split; intro H,
      { rcases H₂ s H with ⟨n, h⟩,
        use [n, trivial, h] },
      { rcases H with ⟨n, -, hn⟩,
        rw mem_nhds_iff,
        refine ⟨_, hn, H₁ n, (J^n).zero_mem⟩ } } }
end

variables [topological_space R] [topological_ring R]

lemma is_ideal_adic_pow {J : ideal R} (h : is_adic J) {n : ℕ} (hn : 0 < n) :
  is_adic (J^n) :=
begin
  rw is_ideal_adic_iff at h ⊢,
  split,
  { intro m, rw ← pow_mul, apply h.left },
  { intros V hV,
    cases h.right V hV with m hm,
    use m,
    refine set.subset.trans _ hm,
    cases n, { exfalso, exact nat.not_succ_le_zero 0 hn },
    rw [← pow_mul, nat.succ_mul],
    apply ideal.pow_le_pow,
    apply nat.le_add_left }
end

lemma is_bot_adic_iff {A : Type*} [comm_ring A] [topological_space A] [topological_ring A] :
is_adic (⊥ : ideal A) ↔ discrete_topology A :=
begin
  rw is_ideal_adic_iff,
  split,
  { rintro ⟨h, h'⟩,
    rw discrete_topology_iff_open_singleton_zero,
    simpa using h 1 },
  { introsI,
    split,
    { simp, },
    { intros U U_nhds,
      use 1,
      simp [mem_of_mem_nhds U_nhds] } },
end

end is_adic

/-- The `R` is equipped with a preferred ideal. -/
class with_ideal (R : Type*) [comm_ring R] :=
(I : ideal R)

namespace with_ideal

variables [with_ideal R]

@[priority 100] instance : topological_space R := I.adic_topology

@[priority 100] instance : topological_ring R :=
ring_filter_basis.is_topological_ring _

@[priority 100] instance : nonarchimedean_ring R :=
I.nonarchimedean

end with_ideal
