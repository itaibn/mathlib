import topology.algebra.nonarchimedean.bases
import algebra.lie.ideal_operations


variables {R : Type*} [comm_ring R]

open set topological_add_group submodule filter
open_locale topological_space


namespace ideal

def adic_basis (I : ideal R) : submodules_basis (λ n : ℕ, (I^n : ideal R)) :=
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

def adic_topology (I : ideal R) : topological_space R :=
(adic_basis I).to_subgroups_basis.topology

lemma nonarchimedean (I : ideal R) : @nonarchimedean_ring R _ I.adic_topology :=
I.adic_basis.to_subgroups_basis.nonarchimedean

/-- For the `I`-adic topology, the neighborhoods of zero has basis given by the powers of `I`. -/
lemma has_basis_nhds_zero_adic (I : ideal R) :
  has_basis (@nhds R I.adic_topology (0 : R)) (λ n : ℕ, true) (λ n, ((I^n : ideal R) : set R)) :=
⟨begin
  intros U,
  rw I.adic_basis.to_subgroups_basis.to_ring_filter_basis.to_add_group_filter_basis.nhds_zero_has_basis.mem_iff,
  split,
  { rintros ⟨-, ⟨i, rfl⟩, h⟩,
    use [i, trivial, h] },
  { rintros ⟨i, -, h⟩,
    use [(I^i : ideal R), i, rfl, h] }
end⟩

end ideal

def is_adic [H : topological_space R] [topological_ring R] (J : ideal R) : Prop :=
H = J.adic_topology

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
    { apply (subgroups_basis.to_ring_filter_basis _).to_add_group_filter_basis.is_topological_add_group },
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

class with_ideal (R : Type*) [comm_ring R] :=
(I : ideal R)

namespace with_ideal

variables [with_ideal R]

instance : topological_space R := I.adic_topology

instance : topological_ring R :=
ring_filter_basis.is_topological_ring _

instance : nonarchimedean_ring R :=
I.nonarchimedean

end with_ideal

variables [topological_space R] [topological_ring R]

lemma is_ideal_adic_pow {J : ideal R} (h : is_adic J) {n : ℕ} (hn : n > 0) :
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
