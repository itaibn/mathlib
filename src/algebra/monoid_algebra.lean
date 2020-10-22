/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Yury G. Kudryashov, Scott Morrison
-/
import algebra.algebra.basic

/-!
# Monoid algebras

When the domain of a `finsupp` has a multiplicative or additive structure, we can define
a convolution product. To mathematicians this structure is known as the "monoid algebra",
i.e. the finite formal linear combinations over a given semiring of elements of the monoid.
The "group ring" ℤ[G] or the "group algebra" k[G] are typical uses.

In this file we define `monoid_algebra k G := G →₀ k`, and `add_monoid_algebra k G`
in the same way, and then define the convolution product on these.

When the domain is additive, this is used to define polynomials:
```
polynomial α := add_monoid_algebra ℕ α
mv_polynomial σ α := add_monoid_algebra (σ →₀ ℕ) α
```

When the domain is multiplicative, e.g. a group, this will be used to define the group ring.

## Implementation note
Unfortunately because additive and multiplicative structures both appear in both cases,
it doesn't appear to be possible to make much use of `to_additive`, and we just settle for
saying everything twice.

Similarly, I attempted to just define `add_monoid_algebra k G := monoid_algebra k (multiplicative G)`,
but the definitional equality `multiplicative G = G` leaks through everywhere, and
seems impossible to use.
-/

noncomputable theory
open_locale classical big_operators

open finset finsupp

universes u₁ u₂ u₃
variables (k : Type u₁) (G : Type u₂)

/-! ### Multiplicative monoids -/
section
variables [semiring k]

/--
The monoid algebra over a semiring `k` generated by the monoid `G`.
It is the type of finite formal `k`-linear combinations of terms of `G`,
endowed with the convolution product.
-/
@[derive [inhabited, add_comm_monoid, has_coe_to_fun]]
def monoid_algebra : Type (max u₁ u₂) := G →₀ k

end

namespace monoid_algebra

variables {k G}

/-! #### Semiring structure -/
section semiring

variables [semiring k] [monoid G]

/-- The product of `f g : monoid_algebra k G` is the finitely supported function
  whose value at `a` is the sum of `f x * g y` over all pairs `x, y`
  such that `x * y = a`. (Think of the group ring of a group.) -/
instance : has_mul (monoid_algebra k G) :=
⟨λf g, f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ * a₂) (b₁ * b₂)⟩

lemma mul_def {f g : monoid_algebra k G} :
  f * g = (f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ * a₂) (b₁ * b₂)) :=
rfl
/-- The unit of the multiplication is `single 1 1`, i.e. the function
  that is `1` at `1` and zero elsewhere. -/
instance : has_one (monoid_algebra k G) :=
⟨single 1 1⟩

lemma one_def : (1 : monoid_algebra k G) = single 1 1 :=
rfl

instance : semiring (monoid_algebra k G) :=
{ one       := 1,
  mul       := (*),
  zero      := 0,
  add       := (+),
  one_mul   := assume f, by simp only [mul_def, one_def, sum_single_index, zero_mul,
    single_zero, sum_zero, zero_add, one_mul, sum_single],
  mul_one   := assume f, by simp only [mul_def, one_def, sum_single_index, mul_zero,
    single_zero, sum_zero, add_zero, mul_one, sum_single],
  zero_mul  := assume f, by simp only [mul_def, sum_zero_index],
  mul_zero  := assume f, by simp only [mul_def, sum_zero_index, sum_zero],
  mul_assoc := assume f g h, by simp only [mul_def, sum_sum_index, sum_zero_index, sum_add_index,
    sum_single_index, single_zero, single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff,
    add_mul, mul_add, add_assoc, mul_assoc, zero_mul, mul_zero, sum_zero, sum_add],
  left_distrib  := assume f g h, by simp only [mul_def, sum_add_index, mul_add, mul_zero,
    single_zero, single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff, sum_add],
  right_distrib := assume f g h, by simp only [mul_def, sum_add_index, add_mul, mul_zero, zero_mul,
    single_zero, single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff, sum_zero,
    sum_add],
  .. finsupp.add_comm_monoid }

variables {R : Type*} [semiring R]

/-- A non-commutative version of `monoid_algebra.lift`: given a additive homomorphism `f : k →+ R`
and a multiplicative monoid homomorphism `g : G →* R`, returns the additive homomorphism from
`monoid_algebra k G` such that `lift_nc f g (single a b) = f b * g a`. If `f` is a ring homomorphism
and the range of either `f` or `g` is in center of `R`, then the result is a ring homomorphism.  If
`R` is a `k`-algebra and `f = algebra_map k R`, then the result is an algebra homomorphism called
`monoid_algebra.lift`. -/
def lift_nc (f : k →+ R) (g : G →* R) : monoid_algebra k G →+ R :=
lift_add_hom (λ x : G, (add_monoid_hom.mul_right (g x)).comp f)

@[simp] lemma lift_nc_single (f : k →+ R) (g : G →* R) (a : G) (b : k) :
  lift_nc f g (single a b) = f b * g a :=
lift_add_hom_apply_single _ _ _

@[simp] lemma lift_nc_one (f : k →+* R) (g : G →* R) : lift_nc (f : k →+ R) g 1 = 1 :=
by simp [one_def]

lemma lift_nc_mul (f : k →+* R) (g : G →* R)
  (a b : monoid_algebra k G) (h_comm : ∀ {x y}, y ∈ a.support → commute (f (b x)) (g y)) :
  lift_nc (f : k →+ R) g (a * b) = lift_nc (f : k →+ R) g a * lift_nc (f : k →+ R) g b :=
begin
  conv_rhs { rw [← sum_single a, ← sum_single b] },
  simp_rw [mul_def, (lift_nc _ g).map_finsupp_sum, lift_nc_single, finsupp.sum_mul, finsupp.mul_sum],
  refine finset.sum_congr rfl (λ y hy, finset.sum_congr rfl (λ x hx, _)),
  simp [mul_assoc, (h_comm hy).left_comm]
end

end semiring

instance [comm_semiring k] [comm_monoid G] : comm_semiring (monoid_algebra k G) :=
{ mul_comm := assume f g,
  begin
    simp only [mul_def, finsupp.sum, mul_comm],
    rw [finset.sum_comm],
    simp only [mul_comm]
  end,
  .. monoid_algebra.semiring }

instance [semiring k] [nontrivial k] [monoid G] : nontrivial (monoid_algebra k G) :=
finsupp.nontrivial

/-! #### Derived instances -/
section derived_instances

instance [semiring k] [subsingleton k] : unique (monoid_algebra k G) :=
finsupp.unique_of_right

instance [ring k] : add_group (monoid_algebra k G) :=
finsupp.add_group

instance [ring k] [monoid G] : ring (monoid_algebra k G) :=
{ neg := has_neg.neg,
  add_left_neg := add_left_neg,
  .. monoid_algebra.semiring }

instance [comm_ring k] [comm_monoid G] : comm_ring (monoid_algebra k G) :=
{ mul_comm := mul_comm, .. monoid_algebra.ring}

instance {R : Type*} [semiring R] [semiring k] [semimodule R k] : has_scalar R (monoid_algebra k G) :=
finsupp.has_scalar

instance {R : Type*} [semiring R] [semiring k] [semimodule R k] : semimodule R (monoid_algebra k G) :=
finsupp.semimodule G k

instance [group G] [semiring k] : distrib_mul_action G (monoid_algebra k G) :=
finsupp.comap_distrib_mul_action_self

end derived_instances

section misc_theorems

variables [semiring k] [monoid G]
local attribute [reducible] monoid_algebra

lemma mul_apply (f g : monoid_algebra k G) (x : G) :
  (f * g) x = (f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, if a₁ * a₂ = x then b₁ * b₂ else 0) :=
begin
  rw [mul_def],
  simp only [finsupp.sum_apply, single_apply],
end

lemma mul_apply_antidiagonal (f g : monoid_algebra k G) (x : G) (s : finset (G × G))
  (hs : ∀ {p : G × G}, p ∈ s ↔ p.1 * p.2 = x) :
  (f * g) x = ∑ p in s, (f p.1 * g p.2) :=
let F : G × G → k := λ p, if p.1 * p.2 = x then f p.1 * g p.2 else 0 in
calc (f * g) x = (∑ a₁ in f.support, ∑ a₂ in g.support, F (a₁, a₂)) :
  mul_apply f g x
... = ∑ p in f.support.product g.support, F p : finset.sum_product.symm
... = ∑ p in (f.support.product g.support).filter (λ p : G × G, p.1 * p.2 = x), f p.1 * g p.2 :
  (finset.sum_filter _ _).symm
... = ∑ p in s.filter (λ p : G × G, p.1 ∈ f.support ∧ p.2 ∈ g.support), f p.1 * g p.2 :
  sum_congr (by { ext, simp only [mem_filter, mem_product, hs, and_comm] }) (λ _ _, rfl)
... = ∑ p in s, f p.1 * g p.2 : sum_subset (filter_subset _) $ λ p hps hp,
  begin
    simp only [mem_filter, mem_support_iff, not_and, not_not] at hp ⊢,
    by_cases h1 : f p.1 = 0,
    { rw [h1, zero_mul] },
    { rw [hp hps h1, mul_zero] }
  end

lemma support_mul (a b : monoid_algebra k G) :
  (a * b).support ⊆ a.support.bind (λa₁, b.support.bind $ λa₂, {a₁ * a₂}) :=
subset.trans support_sum $ bind_mono $ assume a₁ _,
  subset.trans support_sum $ bind_mono $ assume a₂ _, support_single_subset

@[simp] lemma single_mul_single {a₁ a₂ : G} {b₁ b₂ : k} :
  (single a₁ b₁ : monoid_algebra k G) * single a₂ b₂ = single (a₁ * a₂) (b₁ * b₂) :=
(sum_single_index (by simp only [zero_mul, single_zero, sum_zero])).trans
  (sum_single_index (by rw [mul_zero, single_zero]))

@[simp] lemma single_pow {a : G} {b : k} :
  ∀ n : ℕ, (single a b : monoid_algebra k G)^n = single (a^n) (b ^ n)
| 0 := rfl
| (n+1) := by simp only [pow_succ, single_pow n, single_mul_single]

section

variables (k G)

/-- Embedding of a monoid into its monoid algebra. -/
def of : G →* monoid_algebra k G :=
{ to_fun := λ a, single a 1,
  map_one' := rfl,
  map_mul' := λ a b, by rw [single_mul_single, one_mul] }

end

@[simp] lemma of_apply (a : G) : of k G a = single a 1 := rfl

lemma mul_single_apply_aux (f : monoid_algebra k G) {r : k}
  {x y z : G} (H : ∀ a, a * x = z ↔ a = y) :
  (f * single x r) z = f y * r :=
have A : ∀ a₁ b₁, (single x r).sum (λ a₂ b₂, ite (a₁ * a₂ = z) (b₁ * b₂) 0) =
  ite (a₁ * x = z) (b₁ * r) 0,
from λ a₁ b₁, sum_single_index $ by simp,
calc (f * single x r) z = sum f (λ a b, if (a = y) then (b * r) else 0) :
  -- different `decidable` instances make it not trivial
  by { simp only [mul_apply, A, H], congr, funext, split_ifs; refl }
... = if y ∈ f.support then f y * r else 0 : f.support.sum_ite_eq' _ _
... = f y * r : by split_ifs with h; simp at h; simp [h]

lemma mul_single_one_apply (f : monoid_algebra k G) (r : k) (x : G) :
  (f * single 1 r) x = f x * r :=
f.mul_single_apply_aux $ λ a, by rw [mul_one]

lemma single_mul_apply_aux (f : monoid_algebra k G) {r : k} {x y z : G}
  (H : ∀ a, x * a = y ↔ a = z) :
  (single x r * f) y = r * f z :=
have f.sum (λ a b, ite (x * a = y) (0 * b) 0) = 0, by simp,
calc (single x r * f) y = sum f (λ a b, ite (x * a = y) (r * b) 0) :
  (mul_apply _ _ _).trans $ sum_single_index this
... = f.sum (λ a b, ite (a = z) (r * b) 0) :
  by { simp only [H], congr' with g s, split_ifs; refl  }
... = if z ∈ f.support then (r * f z) else 0 : f.support.sum_ite_eq' _ _
... = _ : by split_ifs with h; simp at h; simp [h]

lemma single_one_mul_apply (f : monoid_algebra k G) (r : k) (x : G) :
  (single 1 r * f) x = r * f x :=
f.single_mul_apply_aux $ λ a, by rw [one_mul]

end misc_theorems

/-! #### Algebra structure -/
section algebra

local attribute [reducible] monoid_algebra

lemma single_one_comm [comm_semiring k] [monoid G] (r : k) (f : monoid_algebra k G) :
  single 1 r * f = f * single 1 r :=
by { ext, rw [single_one_mul_apply, mul_single_one_apply, mul_comm] }

/-- `finsupp.single 1` as a `ring_hom` -/
@[simps] def single_one_ring_hom [semiring k] [monoid G] : k →+* monoid_algebra k G :=
{ map_one' := rfl,
  map_mul' := λ x y, by rw [single_add_hom, single_mul_single, one_mul],
  ..finsupp.single_add_hom 1}

/--
The instance `algebra k (monoid_algebra A G)` whenever we have `algebra k A`.

In particular this provides the instance `algebra k (monoid_algebra k G)`.
-/
instance {A : Type*} [comm_semiring k] [semiring A] [algebra k A] [monoid G] :
  algebra k (monoid_algebra A G) :=
{ smul_def' := λ r a, by { ext, simp [single_one_mul_apply, algebra.smul_def''], },
  commutes' := λ r f, by { ext, simp [single_one_mul_apply, mul_single_one_apply, algebra.commutes], },
  ..single_one_ring_hom.comp (algebra_map k A) }

/-- `finsupp.single 1` as a `alg_hom` -/
@[simps]
def single_one_alg_hom {A : Type*} [comm_semiring k] [semiring A] [algebra k A] [monoid G] :
  A →ₐ[k] monoid_algebra A G :=
{ commutes' := λ r, by { ext, simp, refl, }, ..single_one_ring_hom}

@[simp] lemma coe_algebra_map {A : Type*} [comm_semiring k] [semiring A] [algebra k A] [monoid G] :
  (algebra_map k (monoid_algebra A G) : k → monoid_algebra A G) = single 1 ∘ (algebra_map k A) :=
rfl

lemma single_eq_algebra_map_mul_of [comm_semiring k] [monoid G] (a : G) (b : k) :
  single a b = (algebra_map k (monoid_algebra k G) : k → monoid_algebra k G) b * of k G a :=
by simp

lemma single_algebra_map_eq_algebra_map_mul_of {A : Type*} [comm_semiring k] [semiring A] [algebra k A] [monoid G] (a : G) (b : k) :
  single a (algebra_map k A b) = (algebra_map k (monoid_algebra A G) : k → monoid_algebra A G) b * of A G a :=
by simp

end algebra

section lift

variables (k G) [comm_semiring k] [monoid G] (A : Type u₃) [semiring A] [algebra k A]

/-- A `k`-algebra homomorphism from `monoid_algebra k G` is uniquely defined by its
values on the functions `single a 1`. -/
@[ext] lemma alg_hom_ext ⦃φ₁ φ₂ : monoid_algebra k G →ₐ[k] A⦄
  (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
alg_hom.to_linear_map_inj $ finsupp.lhom_ext h

/-- Any monoid homomorphism `G →* A` can be lifted to an algebra homomorphism
`monoid_algebra k G →ₐ[k] A`. -/
def lift : (G →* A) ≃ (monoid_algebra k G →ₐ[k] A) :=
{ inv_fun := λ f, (f : monoid_algebra k G →* A).comp (of k G),
  to_fun := λ F, {
    to_fun := lift_nc ((algebra_map k A : k →+* A) : k →+ A) F,
    map_one' := lift_nc_one _ _,
    map_mul' := λ f g, lift_nc_mul _ _ _ _ $ λ _ _ _, algebra.commutes _ _,
    commutes' := λ r, by simp,
    .. lift_nc ((algebra_map k A : k →+* A) : k →+ A) F },
  left_inv := λ f, by { ext, simp  },
  right_inv := λ F, by { ext, simp } }

variables {k G A}

lemma lift_apply' (F : G →* A) (f : monoid_algebra k G) :
  lift k G A F f = f.sum (λ a b, (algebra_map k A b) * F a) := rfl

lemma lift_apply (F : G →* A) (f : monoid_algebra k G) :
  lift k G A F f = f.sum (λ a b, b • F a) :=
by simp only [lift_apply', algebra.smul_def]

lemma lift_def (F : G →* A) :
  ⇑(lift k G A F) = lift_nc ((algebra_map k A : k →+* A) : k →+ A) F :=
rfl

@[simp] lemma lift_symm_apply (F : monoid_algebra k G →ₐ[k] A) (x : G) :
  (lift k G A).symm F x = F (single x 1) := rfl

lemma lift_of (F : G →* A) (x) :
  lift k G A F (of k G x) = F x :=
by rw [of_apply, ← lift_symm_apply, equiv.symm_apply_apply]

@[simp] lemma lift_single (F : G →* A) (a b) :
  lift k G A F (single a b) = b • F a :=
by rw [lift_def, lift_nc_single, algebra.smul_def, ring_hom.coe_add_monoid_hom]

lemma lift_unique' (F : monoid_algebra k G →ₐ[k] A) :
  F = lift k G A ((F : monoid_algebra k G →* A).comp (of k G)) :=
((lift k G A).apply_symm_apply F).symm

/-- Decomposition of a `k`-algebra homomorphism from `monoid_algebra k G` by
its values on `F (single a 1)`. -/
lemma lift_unique (F : monoid_algebra k G →ₐ[k] A) (f : monoid_algebra k G) :
  F f = f.sum (λ a b, b • F (single a 1)) :=
by conv_lhs { rw lift_unique' F, simp [lift_apply] }

end lift

section
local attribute [reducible] monoid_algebra

variables (k)
/-- When `V` is a `k[G]`-module, multiplication by a group element `g` is a `k`-linear map. -/
def group_smul.linear_map [group G] [comm_ring k]
  (V : Type u₃) [add_comm_group V] [module (monoid_algebra k G) V] (g : G) :
  (semimodule.restrict_scalars k (monoid_algebra k G) V) →ₗ[k]
  (semimodule.restrict_scalars k (monoid_algebra k G) V) :=
{ to_fun    := λ v, (single g (1 : k) • v : V),
  map_add'  := λ x y, smul_add (single g (1 : k)) x y,
  map_smul' := λ c x,
  by simp only [semimodule.restrict_scalars_smul_def, coe_algebra_map, ←mul_smul, single_one_comm], }.

@[simp]
lemma group_smul.linear_map_apply [group G] [comm_ring k]
  (V : Type u₃) [add_comm_group V] [module (monoid_algebra k G) V] (g : G) (v : V) :
  (group_smul.linear_map k V g) v = (single g (1 : k) • v : V) :=
rfl

section
variables {k}
variables [group G] [comm_ring k]
  {V : Type u₃} {gV : add_comm_group V} {mV : module (monoid_algebra k G) V}
  {W : Type u₃} {gW : add_comm_group W} {mW : module (monoid_algebra k G) W}
  (f : (semimodule.restrict_scalars k (monoid_algebra k G) V) →ₗ[k]
       (semimodule.restrict_scalars k (monoid_algebra k G) W))
  (h : ∀ (g : G) (v : V), f (single g (1 : k) • v : V) = (single g (1 : k) • (f v) : W))
include h

/-- Build a `k[G]`-linear map from a `k`-linear map and evidence that it is `G`-equivariant. -/
def equivariant_of_linear_of_comm : V →ₗ[monoid_algebra k G] W :=
{ to_fun := f,
  map_add' := λ v v', by simp,
  map_smul' := λ c v,
  begin
  apply finsupp.induction c,
  { simp, },
  { intros g r c' nm nz w,
    rw [add_smul, linear_map.map_add, w, add_smul, add_left_inj,
      single_eq_algebra_map_mul_of, ←smul_smul, ←smul_smul],
    erw [f.map_smul, h g v],
    refl, }
  end, }

@[simp]
lemma equivariant_of_linear_of_comm_apply (v : V) : (equivariant_of_linear_of_comm f h) v = f v :=
rfl

end
end

section
universe ui
variable {ι : Type ui}
local attribute [reducible] monoid_algebra

lemma prod_single [comm_semiring k] [comm_monoid G]
  {s : finset ι} {a : ι → G} {b : ι → k} :
  (∏ i in s, single (a i) (b i)) = single (∏ i in s, a i) (∏ i in s, b i) :=
finset.induction_on s rfl $ λ a s has ih, by rw [prod_insert has, ih,
  single_mul_single, prod_insert has, prod_insert has]

end

section -- We now prove some additional statements that hold for group algebras.
variables [semiring k] [group G]
local attribute [reducible] monoid_algebra

@[simp]
lemma mul_single_apply (f : monoid_algebra k G) (r : k) (x y : G) :
  (f * single x r) y = f (y * x⁻¹) * r :=
f.mul_single_apply_aux $ λ a, eq_mul_inv_iff_mul_eq.symm

@[simp]
lemma single_mul_apply (r : k) (x : G) (f : monoid_algebra k G) (y : G) :
  (single x r * f) y = r * f (x⁻¹ * y) :=
f.single_mul_apply_aux $ λ z, eq_inv_mul_iff_mul_eq.symm

lemma mul_apply_left (f g : monoid_algebra k G) (x : G) :
  (f * g) x = (f.sum $ λ a b, b * (g (a⁻¹ * x))) :=
calc (f * g) x = sum f (λ a b, (single a b * g) x) :
  by rw [← finsupp.sum_apply, ← finsupp.sum_mul, f.sum_single]
... = _ : by simp only [single_mul_apply, finsupp.sum]


-- If we'd assumed `comm_semiring`, we could deduce this from `mul_apply_left`.
lemma mul_apply_right (f g : monoid_algebra k G) (x : G) :
  (f * g) x = (g.sum $ λa b, (f (x * a⁻¹)) * b) :=
calc (f * g) x = sum g (λ a b, (f * single a b) x) :
  by rw [← finsupp.sum_apply, ← finsupp.mul_sum, g.sum_single]
... = _ : by simp only [mul_single_apply, finsupp.sum]

end

end monoid_algebra

/-! ### Additive monoids -/
section
variables [semiring k]

/--
The monoid algebra over a semiring `k` generated by the additive monoid `G`.
It is the type of finite formal `k`-linear combinations of terms of `G`,
endowed with the convolution product.
-/
@[derive [inhabited, add_comm_monoid, has_coe_to_fun]]
def add_monoid_algebra := G →₀ k

end

namespace add_monoid_algebra

variables {k G}

/-! #### Semiring structure -/
section semiring

variables [semiring k] [add_monoid G]

/-- The product of `f g : add_monoid_algebra k G` is the finitely supported function
  whose value at `a` is the sum of `f x * g y` over all pairs `x, y`
  such that `x + y = a`. (Think of the product of multivariate
  polynomials where `α` is the additive monoid of monomial exponents.) -/
instance : has_mul (add_monoid_algebra k G) :=
⟨λf g, f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ + a₂) (b₁ * b₂)⟩

lemma mul_def {f g : add_monoid_algebra k G} :
  f * g = (f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, single (a₁ + a₂) (b₁ * b₂)) :=
rfl

/-- The unit of the multiplication is `single 1 1`, i.e. the function
  that is `1` at `0` and zero elsewhere. -/
instance : has_one (add_monoid_algebra k G) :=
⟨single 0 1⟩

lemma one_def : (1 : add_monoid_algebra k G) = single 0 1 :=
rfl

instance : semiring (add_monoid_algebra k G) :=
{ one       := 1,
  mul       := (*),
  zero      := 0,
  add       := (+),
  one_mul   := assume f, by simp only [mul_def, one_def, sum_single_index, zero_mul,
    single_zero, sum_zero, zero_add, one_mul, sum_single],
  mul_one   := assume f, by simp only [mul_def, one_def, sum_single_index, mul_zero,
    single_zero, sum_zero, add_zero, mul_one, sum_single],
  zero_mul  := assume f, by simp only [mul_def, sum_zero_index],
  mul_zero  := assume f, by simp only [mul_def, sum_zero_index, sum_zero],
  mul_assoc := assume f g h, by simp only [mul_def, sum_sum_index, sum_zero_index, sum_add_index,
    sum_single_index, single_zero, single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff,
    add_mul, mul_add, add_assoc, mul_assoc, zero_mul, mul_zero, sum_zero, sum_add],
  left_distrib  := assume f g h, by simp only [mul_def, sum_add_index, mul_add, mul_zero,
    single_zero, single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff, sum_add],
  right_distrib := assume f g h, by simp only [mul_def, sum_add_index, add_mul, mul_zero, zero_mul,
    single_zero, single_add, eq_self_iff_true, forall_true_iff, forall_3_true_iff, sum_zero,
    sum_add],
  .. finsupp.add_comm_monoid }

variables {R : Type*} [semiring R]

/-- A non-commutative version of `add_monoid_algebra.lift`: given a additive homomorphism `f : k →+
R` and a multiplicative monoid homomorphism `g : multiplicative G →* R`, returns the additive
homomorphism from `add_monoid_algebra k G` such that `lift_nc f g (single a b) = f b * g a`. If `f`
is a ring homomorphism and the range of either `f` or `g` is in center of `R`, then the result is a
ring homomorphism.  If `R` is a `k`-algebra and `f = algebra_map k R`, then the result is an algebra
homomorphism called `add_monoid_algebra.lift`. -/
def lift_nc (f : k →+ R) (g : multiplicative G →* R) : add_monoid_algebra k G →+ R :=
lift_add_hom (λ x : G, (add_monoid_hom.mul_right (g $ multiplicative.of_add x)).comp f)

@[simp] lemma lift_nc_single (f : k →+ R) (g : multiplicative G →* R) (a : G) (b : k) :
  lift_nc f g (single a b) = f b * g (multiplicative.of_add a) :=
lift_add_hom_apply_single _ _ _

@[simp] lemma lift_nc_one (f : k →+* R) (g : multiplicative G →* R) : lift_nc (f : k →+ R) g 1 = 1 :=
@monoid_algebra.lift_nc_one k (multiplicative G) _ _ _ _ f g

lemma lift_nc_mul (f : k →+* R) (g : multiplicative G →* R) (a b : add_monoid_algebra k G)
  (h_comm : ∀ {x y}, y ∈ a.support → commute (f (b x)) (g $ multiplicative.of_add y)) :
  lift_nc (f : k →+ R) g (a * b) = lift_nc (f : k →+ R) g a * lift_nc (f : k →+ R) g b :=
@monoid_algebra.lift_nc_mul k (multiplicative G) _ _ _ _ f g a b @h_comm

end semiring

instance [comm_semiring k] [add_comm_monoid G] : comm_semiring (add_monoid_algebra k G) :=
{ mul_comm := @mul_comm (monoid_algebra k $ multiplicative G) _,
  .. add_monoid_algebra.semiring }

instance [semiring k] [nontrivial k] [add_monoid G] : nontrivial (add_monoid_algebra k G) :=
finsupp.nontrivial

/-! #### Derived instances -/
section derived_instances

instance [semiring k] [subsingleton k] : unique (add_monoid_algebra k G) :=
finsupp.unique_of_right

instance [ring k] : add_group (add_monoid_algebra k G) :=
finsupp.add_group

instance [ring k] [add_monoid G] : ring (add_monoid_algebra k G) :=
{ neg := has_neg.neg,
  add_left_neg := add_left_neg,
  .. add_monoid_algebra.semiring }

instance [comm_ring k] [add_comm_monoid G] : comm_ring (add_monoid_algebra k G) :=
{ mul_comm := mul_comm, .. add_monoid_algebra.ring}

variables {R : Type*}

instance [semiring R] [semiring k] [semimodule R k] : has_scalar R (add_monoid_algebra k G) :=
finsupp.has_scalar

instance [semiring R] [semiring k] [semimodule R k] : semimodule R (add_monoid_algebra k G) :=
finsupp.semimodule G k

/-! It is hard to state the equivalent of `distrib_mul_action G (add_monoid_algebra k G)`
because we've never discussed actions of additive groups. -/

end derived_instances

section misc_theorems

variables [semiring k] [add_monoid G]
local attribute [reducible] add_monoid_algebra

lemma mul_apply (f g : add_monoid_algebra k G) (x : G) :
  (f * g) x = (f.sum $ λa₁ b₁, g.sum $ λa₂ b₂, if a₁ + a₂ = x then b₁ * b₂ else 0) :=
@monoid_algebra.mul_apply k (multiplicative G) _ _ _ _ _

lemma mul_apply_antidiagonal (f g : add_monoid_algebra k G) (x : G) (s : finset (G × G))
  (hs : ∀ {p : G × G}, p ∈ s ↔ p.1 + p.2 = x) :
  (f * g) x = ∑ p in s, (f p.1 * g p.2) :=
@monoid_algebra.mul_apply_antidiagonal k (multiplicative G) _ _ _ _ _ s @hs

lemma support_mul (a b : add_monoid_algebra k G) :
  (a * b).support ⊆ a.support.bind (λa₁, b.support.bind $ λa₂, {a₁ + a₂}) :=
@monoid_algebra.support_mul k (multiplicative G) _ _ _ _

lemma single_mul_single {a₁ a₂ : G} {b₁ b₂ : k} :
  (single a₁ b₁ : add_monoid_algebra k G) * single a₂ b₂ = single (a₁ + a₂) (b₁ * b₂) :=
@monoid_algebra.single_mul_single k (multiplicative G) _ _ _ _ _ _

section

variables (k G)

/-- Embedding of a monoid into its monoid algebra. -/
def of : multiplicative G →* add_monoid_algebra k G :=
{ to_fun := λ a, single a 1,
  map_one' := rfl,
  map_mul' := λ a b, by { rw [single_mul_single, one_mul], refl } }

end

@[simp] lemma of_apply (a : multiplicative G) : of k G a = single a.to_add 1 := rfl

lemma mul_single_apply_aux (f : add_monoid_algebra k G) (r : k)
  (x y z : G) (H : ∀ a, a + x = z ↔ a = y) :
  (f * single x r) z = f y * r :=
@monoid_algebra.mul_single_apply_aux k (multiplicative G) _ _ _ _ _ _ _ H

lemma mul_single_zero_apply (f : add_monoid_algebra k G) (r : k) (x : G) :
  (f * single 0 r) x = f x * r :=
f.mul_single_apply_aux r _ _ _ $ λ a, by rw [add_zero]

lemma single_mul_apply_aux (f : add_monoid_algebra k G) (r : k) (x y z : G)
  (H : ∀ a, x + a = y ↔ a = z) :
  (single x r * f) y = r * f z :=
@monoid_algebra.single_mul_apply_aux k (multiplicative G) _ _ _ _ _ _ _ H

lemma single_zero_mul_apply (f : add_monoid_algebra k G) (r : k) (x : G) :
  (single 0 r * f) x = r * f x :=
f.single_mul_apply_aux r _ _ _ $ λ a, by rw [zero_add]

end misc_theorems

/-! #### Algebra structure -/
section algebra

variables {R : Type*}
local attribute [reducible] add_monoid_algebra

/-- `finsupp.single 0` as a `ring_hom` -/
@[simps] def single_zero_ring_hom [semiring k] [add_monoid G] : k →+* add_monoid_algebra k G :=
{ map_one' := rfl,
  map_mul' := λ x y, by rw [single_add_hom, single_mul_single, zero_add],
  ..finsupp.single_add_hom 0}

/--
The instance `algebra R (add_monoid_algebra k G)` whenever we have `algebra R k`.

In particular this provides the instance `algebra k (add_monoid_algebra k G)`.
-/
instance [comm_semiring R] [semiring k] [algebra R k] [add_monoid G] :
  algebra R (add_monoid_algebra k G) :=
{ smul_def' := λ r a, by { ext, simp [single_zero_mul_apply, algebra.smul_def''], },
  commutes' := λ r f, by { ext, simp [single_zero_mul_apply, mul_single_zero_apply, algebra.commutes], },
  ..single_zero_ring_hom.comp (algebra_map R k) }

/-- `finsupp.single 0` as a `alg_hom` -/
@[simps] def single_zero_alg_hom [comm_semiring R] [semiring k] [algebra R k] [add_monoid G] :
  k →ₐ[R] add_monoid_algebra k G :=
{ commutes' := λ r, by { ext, simp, refl, }, ..single_zero_ring_hom}

@[simp] lemma coe_algebra_map [comm_semiring R] [semiring k] [algebra R k] [add_monoid G] :
  (algebra_map R (add_monoid_algebra k G) : R → add_monoid_algebra k G) = single 0 ∘ (algebra_map R k) :=
rfl

end algebra

section lift

variables {k G} [comm_semiring k] [add_monoid G] {A : Type u₃} [semiring A] [algebra k A]

/-- A `k`-algebra homomorphism from `monoid_algebra k G` is uniquely defined by its
values on the functions `single a 1`. -/
@[ext] lemma alg_hom_ext ⦃φ₁ φ₂ : add_monoid_algebra k G →ₐ[k] A⦄
  (h : ∀ x, φ₁ (single x 1) = φ₂ (single x 1)) : φ₁ = φ₂ :=
alg_hom.to_linear_map_inj $ finsupp.lhom_ext h

variables (k G A)

/-- Any monoid homomorphism `G →* A` can be lifted to an algebra homomorphism
`monoid_algebra k G →ₐ[k] A`. -/
def lift : (multiplicative G →* A) ≃ (add_monoid_algebra k G →ₐ[k] A) :=
{ inv_fun := λ f, (f : add_monoid_algebra k G →* A).comp (of k G),
  to_fun := λ F, {
    to_fun := lift_nc ((algebra_map k A : k →+* A) : k →+ A) F,
    .. @monoid_algebra.lift k (multiplicative G) _ _ A _ _ F},
  .. @monoid_algebra.lift k (multiplicative G) _ _ A _ _ }

variables {k G A}

lemma lift_apply' (F : multiplicative G →* A) (f : monoid_algebra k G) :
  lift k G A F f = f.sum (λ a b, (algebra_map k A b) * F (multiplicative.of_add a)) := rfl

lemma lift_apply (F : multiplicative G →* A) (f : monoid_algebra k G) :
  lift k G A F f = f.sum (λ a b, b • F (multiplicative.of_add a)) :=
by simp only [lift_apply', algebra.smul_def]

lemma lift_def (F : multiplicative G →* A) :
  ⇑(lift k G A F) = lift_nc ((algebra_map k A : k →+* A) : k →+ A) F :=
rfl

@[simp] lemma lift_symm_apply (F : add_monoid_algebra k G →ₐ[k] A) (x : multiplicative G) :
  (lift k G A).symm F x = F (single x.to_add 1) := rfl

lemma lift_of (F : multiplicative G →* A) (x : multiplicative G) :
  lift k G A F (of k G x) = F x :=
by rw [of_apply, ← lift_symm_apply, equiv.symm_apply_apply]

@[simp] lemma lift_single (F : multiplicative G →* A) (a b) :
  lift k G A F (single a b) = b • F (multiplicative.of_add a) :=
by rw [lift_def, lift_nc_single, algebra.smul_def, ring_hom.coe_add_monoid_hom]

lemma lift_unique' (F : add_monoid_algebra k G →ₐ[k] A) :
  F = lift k G A ((F : add_monoid_algebra k G →* A).comp (of k G)) :=
((lift k G A).apply_symm_apply F).symm

/-- Decomposition of a `k`-algebra homomorphism from `monoid_algebra k G` by
its values on `F (single a 1)`. -/
lemma lift_unique (F : add_monoid_algebra k G →ₐ[k] A) (f : monoid_algebra k G) :
  F f = f.sum (λ a b, b • F (single a 1)) :=
by conv_lhs { rw lift_unique' F, simp [lift_apply] }

lemma alg_hom_ext_iff {φ₁ φ₂ : add_monoid_algebra k G →ₐ[k] A} :
  (∀ x, φ₁ (finsupp.single x 1) = φ₂ (finsupp.single x 1)) ↔ φ₁ = φ₂ :=
⟨λ h, alg_hom_ext h, by rintro rfl _; refl⟩

end lift

section
local attribute [reducible] add_monoid_algebra

universe ui
variable {ι : Type ui}

lemma prod_single [comm_semiring k] [add_comm_monoid G]
  {s : finset ι} {a : ι → G} {b : ι → k} :
  (∏ i in s, single (a i) (b i)) = single (∑ i in s, a i) (∏ i in s, b i) :=
finset.induction_on s rfl $ λ a s has ih, by rw [prod_insert has, ih,
  single_mul_single, sum_insert has, prod_insert has]

end

end add_monoid_algebra
