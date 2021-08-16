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
# Neighborhood bases for non-archimedean rings and modules

This files contains special families of filter bases on rings and modules that give rise to
non-archimedean topologies.

The main definition is `ring_subgroups_basis` which is a predicate on a family of
additive subgroups of a ring. The predicate ensures there is a topology
`ring_subgroups_basis.topology` which is compatible with a ring structure and admits the given
family as a basis of neighborhoods of zero. In particular the given subgroups become open subgroups
(bundled in `ring_subgroups_basis.open_add_subgroup`) and we get a non-archimedean topological ring
(`ring_subgroups_basis.nonarchimedean`).

A special case of this construction is given by `submodules_basis` where the subgroups are
sub-modules in a commutative algebra. This important example gives rises to the adic topology
(studied in its own file).

-/

open set filter function lattice add_group_with_zero_nhd
open_locale topological_space filter

/-- A family of additive subgroups on a ring `A` is a subgroups basis if it satisfies some
axioms ensuring there is a topology on `A` which is compatiable with the ring structure and
admits this family as a basis of neighborhoods of zero. -/
structure ring_subgroups_basis {A ι : Type*} [ring A] (B : ι → add_subgroup A) : Prop :=
(inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j)
(mul : ∀ i, ∃ j, (B j : set A) * B j ⊆ B i)
(left_mul : ∀ x : A, ∀ i, ∃ j, (B j : set A) ⊆ (λ y : A, x*y) ⁻¹' (B i))
(right_mul : ∀ x : A, ∀ i, ∃ j, (B j : set A) ⊆ (λ y : A, y*x) ⁻¹' (B i))

namespace ring_subgroups_basis

variables {A ι : Type*} [ring A]

lemma of_comm {A ι : Type*} [comm_ring A] (B : ι → add_subgroup A)
(inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j)
(mul : ∀ i, ∃ j, (B j : set A) * B j ⊆ B i)
(left_mul : ∀ x : A, ∀ i, ∃ j, (B j : set A) ⊆ (λ y : A, x*y) ⁻¹' (B i)) : ring_subgroups_basis B :=
{ inter := inter,
  mul := mul,
  left_mul := left_mul,
  right_mul := begin
    intros x i,
    cases left_mul x i with j hj,
    use j,
    simpa [mul_comm] using hj
  end }

/-- Every subgroups basis on a ring leads to a ring filter basis. -/
def to_ring_filter_basis [nonempty ι] {B : ι → add_subgroup A}
  (hB : ring_subgroups_basis B) : ring_filter_basis A :=
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

variables [nonempty ι] {B : ι → add_subgroup A} (hB : ring_subgroups_basis B)

/-- The topology defined from a subgroups basis, admitting the given subgroups as a basis
of neighborhoods of zero. -/
def topology : topological_space A :=
hB.to_ring_filter_basis.to_add_group_filter_basis.topology

/-- Given a subgroups basis, the basis elements as open additive subgroups in the associated
topology. -/
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

@[priority 100] instance nonarchimedean : @nonarchimedean_ring A _ hB.topology :=
begin
  letI := hB.topology,
  constructor,
  intros U hU,
  obtain ⟨-, ⟨i, rfl⟩, hi : (B i : set A) ⊆ U⟩ :=
    hB.to_ring_filter_basis.to_add_group_filter_basis.nhds_zero_has_basis.mem_iff.mp hU,
  exact ⟨hB.open_add_subgroup i, hi⟩
end

end ring_subgroups_basis

variables {ι R A : Type*} [comm_ring R] [comm_ring A] [algebra R A]

-- TODO: rename and move
instance toto : has_scalar A (submodule R A) :=
⟨λ a S, submodule.map ((linear_map.lsmul A A a).restrict_scalars R) S⟩

/-- A family of submodules in a commutative `R`-algebra `A` is a submodules basis if it satisfies
some axioms ensuring there is a topology on `A` which is compatiable with the ring structure and
admits this family as a basis of neighborhoods of zero. -/
structure submodules_ring_basis (B : ι → submodule R A) : Prop :=
(inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j)
(left_mul : ∀ (a : A) i, ∃ j, a • B j ≤ B i)
(mul      : ∀ i, ∃ j, (B j : set A) * B j ⊆ B i)

namespace submodules_ring_basis

variables {B : ι → submodule R A} (hB : submodules_ring_basis B)

lemma to_ring_subgroups_basis (hB : submodules_ring_basis B) :
  ring_subgroups_basis (λ i, (B i).to_add_subgroup) :=
begin
  apply ring_subgroups_basis.of_comm (λ i, (B i).to_add_subgroup) hB.inter hB.mul,
  intros a i,
  rcases hB.left_mul a i with ⟨j, hj⟩,
  use j,
  rintros b (b_in : b ∈ B j),
  exact hj ⟨b, b_in, rfl⟩
end

/-- The topology associated to a basis of submodules in an algebra. -/
def topology [nonempty ι] (hB : submodules_ring_basis B) : topological_space A :=
hB.to_ring_subgroups_basis.topology

end submodules_ring_basis

variables {M : Type*} [add_comm_group M] [module R M]

/-- A family of submodules in a  `R`-module `M` is a submodules basis if it satisfies
some axioms ensuring there is a topology on `M` which is compatiable with the module structure and
admits this family as a basis of neighborhoods of zero. -/
structure submodules_basis [topological_space R]
  (B : ι → submodule R M) : Prop :=
(inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j)
(smul : ∀ (m : M) (i : ι), ∀ᶠ a in 𝓝 (0 : R), a • m ∈ B i)

namespace submodules_basis

variables [topological_space R] [nonempty ι] {B : ι → submodule R M}
          (hB : submodules_basis B)

include hB

/-- The image of a submodules basis is a module filter basis. -/
def to_module_filter_basis : module_filter_basis R M :=
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
  smul' := begin
    rintros _ ⟨i, rfl⟩,
    use [univ, univ_mem, B i, i, rfl],
    rintros _ ⟨a, m, -, hm, rfl⟩,
    exact (B i).smul_mem _ hm
  end,
  smul_left' := begin
    rintros x₀ _ ⟨i, rfl⟩,
    use [B i, i, rfl],
    intros m,
    exact (B i).smul_mem _
  end,
  smul_right' := begin
    rintros m₀ _ ⟨i, rfl⟩,
    exact hB.smul m₀ i
  end }

/-- The topology associated to a basis of submodules in a module. -/
def topology : topological_space M :=
hB.to_module_filter_basis.to_add_group_filter_basis.topology

/-- Given a submodules basis, the basis elements as open additive subgroups in the associated
topology. -/
def open_add_subgroup (i : ι) : @open_add_subgroup M _ hB.topology :=
{ is_open' := begin
    letI := hB.topology,
    rw is_open_iff_mem_nhds,
    intros a a_in,
    rw (hB.to_module_filter_basis.to_add_group_filter_basis.nhds_has_basis a).mem_iff,
    use [B i, i, rfl],
    rintros - ⟨b, b_in, rfl⟩,
    exact (B i).add_mem a_in b_in
  end,
  ..(B i).to_add_subgroup }

@[priority 100]
instance nonarchimedean (hB : submodules_basis B) : @nonarchimedean_add_group M _ hB.topology:=
begin
  letI := hB.topology,
  constructor,
  intros U hU,
  obtain ⟨-, ⟨i, rfl⟩, hi : (B i : set M) ⊆ U⟩ :=
    hB.to_module_filter_basis.to_add_group_filter_basis.nhds_zero_has_basis.mem_iff.mp hU,
  exact ⟨hB.open_add_subgroup i, hi⟩
end

end submodules_basis

/-- Given a ring filter basis on a commutative ring `R`, define a compatibility condition
on a family of submodules of a `R`-module `M`. This compatibility condition allows to get
a topological module structure. -/
structure ring_filter_basis.submodules_basis (BR : ring_filter_basis R)
  (B : ι → submodule R M) : Prop :=
(inter : ∀ i j, ∃ k, B k ≤ B i ⊓ B j)
(smul : ∀ (m : M) (i : ι), ∃ U ∈ BR, U ⊆ (λ a, a • m) ⁻¹' B i)


lemma ring_filter_basis.submodules_basis_is_basis (BR : ring_filter_basis R) {B : ι → submodule R M}
  (hB : BR.submodules_basis B) : @submodules_basis ι R _ M _ _ BR.topology B  :=
{ inter := hB.inter,
  smul := begin
    letI := BR.topology,
    intros m i,
    rcases hB.smul m i with ⟨V, V_in, hV⟩,
    exact mem_of_superset (BR.to_add_group_filter_basis.mem_nhds_zero V_in) hV
  end }

/-- The module filter basis associated to a ring filter basis and a compatible submodule basis.
This allows to build a topological module structure compatible with the given module structure
and the topology associated to the given ring filter basis. -/
def ring_filter_basis.module_filter_basis [nonempty ι] (BR : ring_filter_basis R)
  {B : ι → submodule R M} (hB : BR.submodules_basis B) :
  @module_filter_basis R M _ BR.topology _ _ :=
@submodules_basis.to_module_filter_basis  ι R _ M _ _ BR.topology _ _
  (BR.submodules_basis_is_basis hB)
