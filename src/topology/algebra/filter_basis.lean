/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/

import order.filter.bases
import topology.algebra.ring
/-!

# Group filter bases

A `group_filter_basis` is a `filter_basis` on a group with some properties relating
the basis to the group structure. The main theorem is that a `group_filter_basis`
on a group gives a topology on the group which makes it into a topological group
with neighborhoods of the neutral element generated by the given basis.

-/
open filter set topological_space function
open_locale topological_space

universe u

/-- A `group_filter_basis` on a group is a `filter_basis` satisfying some additional axioms.
  Example : if `G` is a topological group then the neighbourhoods of the identity are a
  `group_filter_basis`. Conversely given a `group_filter_basis` one can define a topological
  group structure on `G`.  -/
class group_filter_basis (G : Type u) [group G] extends filter_basis G :=
(one' : ∀ {U}, U ∈ sets → (1 : G) ∈ U)
(mul' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V * V ⊆ U)
(inv' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x⁻¹) ⁻¹' U)
(conj' : ∀ x₀, ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x₀*x*x₀⁻¹) ⁻¹' U)

/-- A `add_group_filter_basis` on an additive group is a `filter_basis` satisfying some additional
  axioms. Example : if `G` is a topological group then the neighbourhoods of the identity are a
  `add_group_filter_basis`. Conversely given a `add_group_filter_basis` one can define a
  topological group structure on `G`.  -/
class add_group_filter_basis (A : Type u) [add_group A] extends filter_basis A :=
(zero' : ∀ {U}, U ∈ sets → (0 : A) ∈ U)
(add' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V + V ⊆ U)
(neg' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, -x) ⁻¹' U)
(conj' : ∀ x₀, ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x₀+x+-x₀) ⁻¹' U)

attribute [to_additive] group_filter_basis
attribute [to_additive] group_filter_basis.one'
attribute [to_additive] group_filter_basis.mul'
attribute [to_additive] group_filter_basis.inv'
attribute [to_additive] group_filter_basis.conj'
attribute [to_additive] group_filter_basis.to_filter_basis

@[to_additive]
def group_filter_basis_of_comm {G : Type*} [comm_group G]
  (sets                   : set (set G))
  (nonempty               : sets.nonempty)
  (inter_sets  : ∀ (x y), x ∈ sets → y ∈ sets → ∃ z ∈ sets, z ⊆ x ∩ y)
  (one : ∀ U ∈ sets, (1 : G) ∈ U)
  (mul : ∀ U ∈ sets, ∃ V ∈ sets, V * V ⊆ U)
  (inv : ∀ U ∈ sets, ∃ V ∈ sets, V ⊆ (λ x, x⁻¹) ⁻¹' U) : group_filter_basis G :=
{ sets := sets,
  nonempty := nonempty,
  inter_sets := inter_sets,
  one' := one,
  mul' := mul,
  inv' := inv,
  conj' := λ x U U_in, ⟨U, U_in, by simp⟩ }


namespace group_filter_basis
variables {G : Type u} [group G] {B : group_filter_basis G}

@[to_additive]
instance group_filter_basis.has_mem : has_mem (set G) (group_filter_basis G) :=
⟨λ s f, s ∈ f.sets⟩

@[to_additive] lemma one {U : set G} : U ∈ B → (1 : G) ∈ U := group_filter_basis.one'

@[to_additive] lemma mul {U : set G} : U ∈ B → ∃ V ∈ B, V*V ⊆ U := group_filter_basis.mul'

@[to_additive] lemma inv {U : set G} : U ∈ B → ∃ V ∈ B, V ⊆ (λ x, x⁻¹) ⁻¹' U :=
group_filter_basis.inv'

@[to_additive]
lemma conj : ∀ x₀, ∀ {U}, U ∈ B → ∃ V ∈ B, V ⊆ (λ x, x₀*x*x₀⁻¹) ⁻¹' U :=
group_filter_basis.conj'

@[to_additive]
lemma prod_subset_self (B : group_filter_basis G) {U : set G} (h : U ∈ B) : U ⊆ U * U :=
λ x x_in, ⟨1, x, one h, x_in, one_mul x⟩

/-- The neighborhood function of a `group_filter_basis` -/
@[to_additive]
def N (B : group_filter_basis G) : G → filter G :=
λ x, map (λ y, x*y) B.to_filter_basis.filter

@[simp, to_additive]
lemma N_one (B : group_filter_basis G) : B.N 1 = B.to_filter_basis.filter :=
by simp only [N, one_mul, map_id']

-- The next lemma connects to the new mathlib filter.has_basis
@[to_additive]
protected lemma has_basis (B : group_filter_basis G) (x : G) :
  has_basis (B.N x) (λ V : set G, V ∈ B) (λ V, (λ y, x*y) '' V) :=
has_basis.map (λ y, x * y) to_filter_basis.has_basis

-- This lemma is now redundant because of the above one
/- @[to_additive]
lemma mem_N (f : group_filter_basis G) (x : G) (U : set G) :
  U ∈ f.N x ↔ ∃ V ∈ f, (λ y, x*y) '' V ⊆ U :=
(f.has_basis x).mem_iff -/

-- The following is an internal technical lemma but it will be used twice.
@[to_additive]
lemma N_is_nice (B : group_filter_basis G) :
  (pure ≤ B.N) ∧
  ∀ {a s}, s ∈ B.N a → ∃ t ∈ B.N a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ B.N a' :=
begin
  split,
  { intros x U U_in,
    rw (B.has_basis x).mem_iff at U_in,
    rcases U_in with ⟨V, V_in, H⟩,
    simpa [mem_pure_sets] using H (mem_image_of_mem _ (group_filter_basis.one V_in)), },
  { intros x U U_in,
    rw (B.has_basis x).mem_iff at U_in,
    rcases U_in with ⟨V, V_in, H⟩,
    rcases group_filter_basis.mul V_in with ⟨W, W_in, hW⟩,
    use [(λ y, x*y) '' W, image_mem_map (filter_basis.mem_filter_of_mem _ W_in)],
    split,
    { rw image_subset_iff at H ⊢,
      exact ((B.prod_subset_self W_in).trans hW).trans H },
    { rintros y ⟨t, tW, rfl⟩,
      rw (B.has_basis _).mem_iff,
      use [W, W_in],
      apply subset.trans _ H, clear H,
      rintros z ⟨w, wW, rfl⟩,
      exact ⟨t*w, hW (mul_mem_mul tW wW), by simp [mul_assoc]⟩ } }
end

/-- The topological space structure coming a group filter basis. -/
@[to_additive]
def topology (B : group_filter_basis G) : topological_space G :=
topological_space.mk_of_nhds B.N

/- /-- The topological space structure coming a group filter basis. Version using tc resolution -/
@[to_additive]
def to_topological_space [B : group_filter_basis G] : topological_space G :=
B.topology -/

@[to_additive]
lemma nhds_eq (B : group_filter_basis G) {x₀ : G} :
  @nhds G (B.topology) x₀ = B.N x₀ :=
by rw [topological_space.nhds_mk_of_nhds _ x₀ B.N_is_nice.1 B.N_is_nice.2]

@[to_additive]
lemma nhds_one_eq (B : group_filter_basis G) :
  @nhds G (B.topology) (1 : G) = B.to_filter_basis.filter :=
by { rw B.nhds_eq, simp only [N, one_mul], exact map_id }

@[to_additive]
lemma nhds_has_basis (B : group_filter_basis G) (x₀ : G) :
has_basis (@nhds G B.topology x₀) (λ V : set G, V ∈ B) (λ V, (λ y, x₀ * y) '' V)  :=
by { rw B.nhds_eq, apply B.has_basis }

@[to_additive]
lemma nhds_one_has_basis (B : group_filter_basis G) :
has_basis (@nhds G B.topology 1) (λ V : set G, V ∈ B) id  :=
by { rw B.nhds_one_eq, exact B.to_filter_basis.has_basis }

/-- If a group is endowed with a topological structure coming from
a group filter basis then it's a topological group. -/
@[to_additive]
instance is_topological_group (B : group_filter_basis G) :
  @topological_group G B.topology _ :=
begin
  letI := B.topology,
  have basis := B.nhds_one_has_basis,
  have basis' := basis.prod basis,
  refine topological_group.of_nhds_one _ _ _ _,
  { rw basis'.tendsto_iff basis,
    suffices : ∀ U ∈ B, ∃ V W, (V ∈ B ∧ W ∈ B) ∧ ∀ a b, a ∈ V → b ∈ W → a * b ∈ U, by simpa,
    intros U U_in,
    rcases mul U_in with ⟨V, V_in, hV⟩,
    use [V, V, V_in, V_in],
    intros a b a_in b_in,
    exact hV ⟨a, b, a_in, b_in, rfl⟩ },
  { rw basis.tendsto_iff basis,
    intros U U_in,
    simpa using inv U_in },
  { intro x₀,
    rw [nhds_eq, nhds_one_eq],
    refl },
  { intro x₀,
    rw basis.tendsto_iff basis,
    intros U U_in,
    exact conj x₀ U_in }
end

end group_filter_basis

class ring_filter_basis (R : Type u) [ring R] extends add_group_filter_basis R :=
(mul' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V * V ⊆ U)
(mul_left' : ∀ (x₀ : R) {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x₀*x) ⁻¹' U)
(mul_right' : ∀ (x₀ : R) {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x*x₀) ⁻¹' U)

namespace ring_filter_basis

variables {R : Type u} [ring R]

instance group_filter_basis.has_mem : has_mem (set R) (ring_filter_basis R) :=
⟨λ s B, s ∈ B.sets⟩

lemma mul {B : ring_filter_basis R} {U : set R} (hU : U ∈ B) : ∃ V ∈ B, V * V ⊆ U :=
mul' hU

lemma mul_left {B : ring_filter_basis R} (x₀ : R) {U : set R} (hU : U ∈ B) :
  ∃ V ∈ B, V ⊆ (λ x, x₀*x) ⁻¹' U :=
mul_left' x₀ hU

lemma mul_right {B : ring_filter_basis R} (x₀ : R) {U : set R} (hU : U ∈ B) :
  ∃ V ∈ B, V ⊆ (λ x, x*x₀) ⁻¹' U :=
mul_right' x₀ hU

/-- If a ring is endowed with a topological structure coming from
a ring filter basis then it's a topological ring. -/
instance is_topological_ring {R : Type u} [ring R] (B : ring_filter_basis R) :
  @topological_ring R B.to_add_group_filter_basis.topology _ :=
begin
  let B' := B.to_add_group_filter_basis,
  letI := B'.topology,
  have basis := B'.nhds_zero_has_basis,
  have basis' := basis.prod basis,
  haveI := B'.is_topological_add_group,
  apply topological_ring.of_add_group_of_nhds_zero,
  { rw basis'.tendsto_iff basis,
    suffices : ∀ U ∈ B', ∃ V W, (V ∈ B' ∧ W ∈ B') ∧ ∀ a b, a ∈ V → b ∈ W → a * b ∈ U, by simpa,
    intros U U_in,
    rcases mul U_in with ⟨V, V_in, hV⟩,
    use [V, V, V_in, V_in],
    intros a b a_in b_in,
    exact hV ⟨a, b, a_in, b_in, rfl⟩ },
  { intro x₀,
    rw basis.tendsto_iff basis,
    intros U,
    simpa using mul_left x₀ },
  { intro x₀,
    rw basis.tendsto_iff basis,
    intros U,
    simpa using mul_right x₀ },
end

end ring_filter_basis
