import tactic
import order.filter.bases
/-!

# Group flter bases

A `group_filter_basis` is a `filter_basis` on a group with some properties relating
the basis to the group structure. The main theorem is that to give a `group_filter_basis`
on a group is to give a topology on the group which makes it into a topological group.

-/

universe u

/-- A `group_filter_basis` on a group is a `filter_basis` satisfying some additional axioms.
  Example : if `G` is a topological group then the neighbourhoods of the identity are a
  `group_filter_basis`. Conversely given a `group_filter_basis` one can define a topological
  group structure on `G`.  -/
class group_filter_basis (G : Type u) [group G] extends filter_basis G :=
(one' : ∀ {U}, U ∈ sets → (1 : G) ∈ U)
(mul' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V * V ⊆ U)
(inv' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, x⁻¹) ⁻¹' U)
(conj' : ∀ x₀, ∀ U ∈ sets, ∃ V ∈ sets, V ⊆ (λ x, x₀*x*x₀⁻¹) ⁻¹' U)

/-- A `group_filter_basis` on a group is a `filter_basis` satisfying some additional axioms.
  Example : if `G` is a topological group then the neighbourhoods of the identity are a
  `group_filter_basis`. Conversely given a `group_filter_basis` one can define a topological
  group structure on `G`.  -/
class add_group_filter_basis (A : Type u) [add_group A] extends filter_basis A :=
(zero' : ∀ {U}, U ∈ sets → (0 : A) ∈ U)
(add' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V + V ⊆ U)
(neg' : ∀ {U}, U ∈ sets → ∃ V ∈ sets, V ⊆ (λ x, -x) ⁻¹' U)
(conj' : ∀ x₀, ∀ U ∈ sets, ∃ V ∈ sets, V ⊆ (λ x, x₀+x-x₀) ⁻¹' U)

-- all ripped off from
-- https://github.com/leanprover-community/lean-perfectoid-spaces/src/for_mathlib/topological_groups.lean

attribute [to_additive] group_filter_basis
attribute [to_additive] group_filter_basis.one'
attribute [to_additive] group_filter_basis.mul'
attribute [to_additive] group_filter_basis.inv'
attribute [to_additive] group_filter_basis.conj'
attribute [to_additive] group_filter_basis.to_filter_basis

namespace group_filter_basis
variables {G : Type u} [group G] {B : group_filter_basis G}

open filter

@[to_additive]
instance group_filter_basis.has_mem : has_mem (set G) (group_filter_basis G) :=
⟨λ s f, s ∈ f.sets⟩

-- doesn't seem to fire as a simp lemma :-(
@[simp, to_additive] lemma one {U : set G} : U ∈ B → (1 : G) ∈ U := group_filter_basis.one'

@[to_additive]
lemma prod_subset_self (B : group_filter_basis G) {U : set G} (h : U ∈ B) : U ⊆ U * U :=
λ x x_in, ⟨1, x, one h, x_in, one_mul x⟩ -- `simp *` didn't work :-(

/-- The neighborhood function of a `group_filter_basis` -/
@[to_additive]
def N (B : group_filter_basis G) : G → filter G :=
λ x, map (λ y, x*y) B.to_filter_basis.filter

@[simp, to_additive]
lemma N_one (B : group_filter_basis G) : B.N 1 = B.to_filter_basis.filter :=
by simpa [N, map_id]

@[to_additive]
lemma mem_N (f : group_filter_basis G) (x : G) (U : set G) :
  U ∈ f.N x ↔ ∃ V ∈ f, (λ y, x*y) '' V ⊆ U :=
sorry -- by simpa [N, mem_map, set.image_subset_iff]

end group_filter_basis
