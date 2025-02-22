/-
Copyright (c) 2018 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Johannes Hölzl
-/
import algebra.algebra.restrict_scalars
import algebra.algebra.subalgebra
import order.liminf_limsup
import topology.algebra.group_completion
import topology.instances.ennreal
import topology.metric_space.algebra
import topology.metric_space.completion
import topology.sequences
import topology.locally_constant.algebra
import topology.continuous_function.algebra

/-!
# Normed spaces

Since a lot of elementary properties don't require `∥x∥ = 0 → x = 0` we start setting up the
theory of `semi_normed_group` and we specialize to `normed_group` at the end.
-/

variables {α : Type*} {β : Type*} {γ : Type*} {ι : Type*}

noncomputable theory
open filter metric
open_locale topological_space big_operators nnreal ennreal uniformity

/-- Auxiliary class, endowing a type `α` with a function `norm : α → ℝ`. This class is designed to
be extended in more interesting classes specifying the properties of the norm. -/
class has_norm (α : Type*) := (norm : α → ℝ)

export has_norm (norm)

notation `∥` e `∥` := norm e

/-- A seminormed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥`
defines a pseudometric space structure. -/
class semi_normed_group (α : Type*) extends has_norm α, add_comm_group α, pseudo_metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))

/-- A normed group is an additive group endowed with a norm for which `dist x y = ∥x - y∥` defines
a metric space structure. -/
class normed_group (α : Type*) extends has_norm α, add_comm_group α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))

/-- A normed group is a seminormed group. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_group.to_semi_normed_group [β : normed_group α] : semi_normed_group α :=
{ ..β }

/-- Construct a seminormed group from a translation invariant pseudodistance -/
def semi_normed_group.of_add_dist [has_norm α] [add_comm_group α] [pseudo_metric_space α]
  (H1 : ∀ x:α, ∥x∥ = dist x 0)
  (H2 : ∀ x y z : α, dist x y ≤ dist (x + z) (y + z)) : semi_normed_group α :=
{ dist_eq := λ x y, begin
    rw H1, apply le_antisymm,
    { rw [sub_eq_add_neg, ← add_right_neg y], apply H2 },
    { have := H2 (x-y) 0 y, rwa [sub_add_cancel, zero_add] at this }
  end }

/-- Construct a seminormed group from a translation invariant pseudodistance -/
def semi_normed_group.of_add_dist' [has_norm α] [add_comm_group α] [pseudo_metric_space α]
  (H1 : ∀ x:α, ∥x∥ = dist x 0)
  (H2 : ∀ x y z : α, dist (x + z) (y + z) ≤ dist x y) : semi_normed_group α :=
{ dist_eq := λ x y, begin
    rw H1, apply le_antisymm,
    { have := H2 (x-y) 0 y, rwa [sub_add_cancel, zero_add] at this },
    { rw [sub_eq_add_neg, ← add_right_neg y], apply H2 }
  end }

/-- A seminormed group can be built from a seminorm that satisfies algebraic properties. This is
formalised in this structure. -/
structure semi_normed_group.core (α : Type*) [add_comm_group α] [has_norm α] : Prop :=
(norm_zero : ∥(0 : α)∥ = 0)
(triangle : ∀ x y : α, ∥x + y∥ ≤ ∥x∥ + ∥y∥)
(norm_neg : ∀ x : α, ∥-x∥ = ∥x∥)

/-- Constructing a seminormed group from core properties of a seminorm, i.e., registering the
pseudodistance and the pseudometric space structure from the seminorm properties. -/
noncomputable def semi_normed_group.of_core (α : Type*) [add_comm_group α] [has_norm α]
  (C : semi_normed_group.core α) : semi_normed_group α :=
{ dist := λ x y, ∥x - y∥,
  dist_eq := assume x y, by refl,
  dist_self := assume x, by simp [C.norm_zero],
  dist_triangle := assume x y z,
    calc ∥x - z∥ = ∥x - y + (y - z)∥ : by rw sub_add_sub_cancel
            ... ≤ ∥x - y∥ + ∥y - z∥  : C.triangle _ _,
  dist_comm := assume x y,
    calc ∥x - y∥ = ∥ -(y - x)∥ : by simp
             ... = ∥y - x∥ : by { rw [C.norm_neg] } }

instance : normed_group punit :=
{ norm := function.const _ 0,
  dist_eq := λ _ _, rfl, }

@[simp] lemma punit.norm_eq_zero (r : punit) : ∥r∥ = 0 := rfl

instance : normed_group ℝ :=
{ norm := λ x, abs x,
  dist_eq := assume x y, rfl }

lemma real.norm_eq_abs (r : ℝ) : ∥r∥ = abs r := rfl

section semi_normed_group
variables [semi_normed_group α] [semi_normed_group β]

lemma dist_eq_norm (g h : α) : dist g h = ∥g - h∥ :=
semi_normed_group.dist_eq _ _

lemma dist_eq_norm' (g h : α) : dist g h = ∥h - g∥ :=
by rw [dist_comm, dist_eq_norm]

@[simp] lemma dist_zero_right (g : α) : dist g 0 = ∥g∥ :=
by rw [dist_eq_norm, sub_zero]

@[simp] lemma dist_zero_left : dist (0:α) = norm :=
funext $ λ g, by rw [dist_comm, dist_zero_right]

lemma tendsto_norm_cocompact_at_top [proper_space α] :
  tendsto norm (cocompact α) at_top :=
by simpa only [dist_zero_right] using tendsto_dist_right_cocompact_at_top (0:α)

lemma norm_sub_rev (g h : α) : ∥g - h∥ = ∥h - g∥ :=
by simpa only [dist_eq_norm] using dist_comm g h

@[simp] lemma norm_neg (g : α) : ∥-g∥ = ∥g∥ :=
by simpa using norm_sub_rev 0 g

@[simp] lemma dist_add_left (g h₁ h₂ : α) : dist (g + h₁) (g + h₂) = dist h₁ h₂ :=
by simp [dist_eq_norm]

@[simp] lemma dist_add_right (g₁ g₂ h : α) : dist (g₁ + h) (g₂ + h) = dist g₁ g₂ :=
by simp [dist_eq_norm]

@[simp] lemma dist_neg_neg (g h : α) : dist (-g) (-h) = dist g h :=
by simp only [dist_eq_norm, neg_sub_neg, norm_sub_rev]

@[simp] lemma dist_sub_left (g h₁ h₂ : α) : dist (g - h₁) (g - h₂) = dist h₁ h₂ :=
by simp only [sub_eq_add_neg, dist_add_left, dist_neg_neg]

@[simp] lemma dist_sub_right (g₁ g₂ h : α) : dist (g₁ - h) (g₂ - h) = dist g₁ g₂ :=
by simpa only [sub_eq_add_neg] using dist_add_right _ _ _

/-- **Triangle inequality** for the norm. -/
lemma norm_add_le (g h : α) : ∥g + h∥ ≤ ∥g∥ + ∥h∥ :=
by simpa [dist_eq_norm] using dist_triangle g 0 (-h)

lemma norm_add_le_of_le {g₁ g₂ : α} {n₁ n₂ : ℝ} (H₁ : ∥g₁∥ ≤ n₁) (H₂ : ∥g₂∥ ≤ n₂) :
  ∥g₁ + g₂∥ ≤ n₁ + n₂ :=
le_trans (norm_add_le g₁ g₂) (add_le_add H₁ H₂)

lemma dist_add_add_le (g₁ g₂ h₁ h₂ : α) :
  dist (g₁ + g₂) (h₁ + h₂) ≤ dist g₁ h₁ + dist g₂ h₂ :=
by simpa only [dist_add_left, dist_add_right] using dist_triangle (g₁ + g₂) (h₁ + g₂) (h₁ + h₂)

lemma dist_add_add_le_of_le {g₁ g₂ h₁ h₂ : α} {d₁ d₂ : ℝ}
  (H₁ : dist g₁ h₁ ≤ d₁) (H₂ : dist g₂ h₂ ≤ d₂) :
  dist (g₁ + g₂) (h₁ + h₂) ≤ d₁ + d₂ :=
le_trans (dist_add_add_le g₁ g₂ h₁ h₂) (add_le_add H₁ H₂)

lemma dist_sub_sub_le (g₁ g₂ h₁ h₂ : α) :
  dist (g₁ - g₂) (h₁ - h₂) ≤ dist g₁ h₁ + dist g₂ h₂ :=
by simpa only [sub_eq_add_neg, dist_neg_neg] using dist_add_add_le g₁ (-g₂) h₁ (-h₂)

lemma dist_sub_sub_le_of_le {g₁ g₂ h₁ h₂ : α} {d₁ d₂ : ℝ}
  (H₁ : dist g₁ h₁ ≤ d₁) (H₂ : dist g₂ h₂ ≤ d₂) :
  dist (g₁ - g₂) (h₁ - h₂) ≤ d₁ + d₂ :=
le_trans (dist_sub_sub_le g₁ g₂ h₁ h₂) (add_le_add H₁ H₂)

lemma abs_dist_sub_le_dist_add_add (g₁ g₂ h₁ h₂ : α) :
  abs (dist g₁ h₁ - dist g₂ h₂) ≤ dist (g₁ + g₂) (h₁ + h₂) :=
by simpa only [dist_add_left, dist_add_right, dist_comm h₂]
  using abs_dist_sub_le (g₁ + g₂) (h₁ + h₂) (h₁ + g₂)

@[simp] lemma norm_nonneg (g : α) : 0 ≤ ∥g∥ :=
by { rw[←dist_zero_right], exact dist_nonneg }

@[simp] lemma norm_zero : ∥(0:α)∥ = 0 :=  by rw [← dist_zero_right, dist_self]

@[nontriviality] lemma norm_of_subsingleton [subsingleton α] (x : α) : ∥x∥ = 0 :=
by rw [subsingleton.elim x 0, norm_zero]

lemma norm_sum_le {β} : ∀(s : finset β) (f : β → α), ∥∑ a in s, f a∥ ≤ ∑ a in s, ∥ f a ∥ :=
finset.le_sum_of_subadditive norm norm_zero norm_add_le

lemma norm_sum_le_of_le {β} (s : finset β) {f : β → α} {n : β → ℝ} (h : ∀ b ∈ s, ∥f b∥ ≤ n b) :
  ∥∑ b in s, f b∥ ≤ ∑ b in s, n b :=
le_trans (norm_sum_le s f) (finset.sum_le_sum h)

lemma dist_sum_sum_le_of_le {β} (s : finset β) {f g : β → α} {d : β → ℝ}
  (h : ∀ b ∈ s, dist (f b) (g b) ≤ d b) :
  dist (∑ b in s, f b) (∑ b in s, g b) ≤ ∑ b in s, d b :=
begin
  simp only [dist_eq_norm, ← finset.sum_sub_distrib] at *,
  exact norm_sum_le_of_le s h
end

lemma dist_sum_sum_le {β} (s : finset β) (f g : β → α) :
  dist (∑ b in s, f b) (∑ b in s, g b) ≤ ∑ b in s, dist (f b) (g b) :=
dist_sum_sum_le_of_le s (λ _ _, le_rfl)

lemma norm_sub_le (g h : α) : ∥g - h∥ ≤ ∥g∥ + ∥h∥ :=
by simpa [dist_eq_norm] using dist_triangle g 0 h

lemma norm_sub_le_of_le {g₁ g₂ : α} {n₁ n₂ : ℝ} (H₁ : ∥g₁∥ ≤ n₁) (H₂ : ∥g₂∥ ≤ n₂) :
  ∥g₁ - g₂∥ ≤ n₁ + n₂ :=
le_trans (norm_sub_le g₁ g₂) (add_le_add H₁ H₂)

lemma dist_le_norm_add_norm (g h : α) : dist g h ≤ ∥g∥ + ∥h∥ :=
by { rw dist_eq_norm, apply norm_sub_le }

lemma abs_norm_sub_norm_le (g h : α) : abs(∥g∥ - ∥h∥) ≤ ∥g - h∥ :=
by simpa [dist_eq_norm] using abs_dist_sub_le g h 0

lemma norm_sub_norm_le (g h : α) : ∥g∥ - ∥h∥ ≤ ∥g - h∥ :=
le_trans (le_abs_self _) (abs_norm_sub_norm_le g h)

lemma dist_norm_norm_le (g h : α) : dist ∥g∥ ∥h∥ ≤ ∥g - h∥ :=
abs_norm_sub_norm_le g h

lemma norm_le_insert (u v : α) : ∥v∥ ≤ ∥u∥ + ∥u - v∥ :=
calc ∥v∥ = ∥u - (u - v)∥ : by abel
... ≤ ∥u∥ + ∥u - v∥ : norm_sub_le u _

lemma norm_le_insert' (u v : α) : ∥u∥ ≤ ∥v∥ + ∥u - v∥ :=
by { rw norm_sub_rev, exact norm_le_insert v u }

lemma ball_0_eq (ε : ℝ) : ball (0:α) ε = {x | ∥x∥ < ε} :=
set.ext $ assume a, by simp

lemma mem_ball_iff_norm {g h : α} {r : ℝ} :
  h ∈ ball g r ↔ ∥h - g∥ < r :=
by rw [mem_ball, dist_eq_norm]

lemma add_mem_ball_iff_norm {g h : α} {r : ℝ} :
  g + h ∈ ball g r ↔ ∥h∥ < r :=
by rw [mem_ball_iff_norm, add_sub_cancel']

lemma mem_ball_iff_norm' {g h : α} {r : ℝ} :
  h ∈ ball g r ↔ ∥g - h∥ < r :=
by rw [mem_ball', dist_eq_norm]

@[simp] lemma mem_ball_0_iff {ε : ℝ} {x : α} : x ∈ ball (0 : α) ε ↔ ∥x∥ < ε :=
by rw [mem_ball, dist_zero_right]

lemma mem_closed_ball_iff_norm {g h : α} {r : ℝ} :
  h ∈ closed_ball g r ↔ ∥h - g∥ ≤ r :=
by rw [mem_closed_ball, dist_eq_norm]

lemma add_mem_closed_ball_iff_norm {g h : α} {r : ℝ} :
  g + h ∈ closed_ball g r ↔ ∥h∥ ≤ r :=
by rw [mem_closed_ball_iff_norm, add_sub_cancel']

lemma mem_closed_ball_iff_norm' {g h : α} {r : ℝ} :
  h ∈ closed_ball g r ↔ ∥g - h∥ ≤ r :=
by rw [mem_closed_ball', dist_eq_norm]

lemma norm_le_of_mem_closed_ball {g h : α} {r : ℝ} (H : h ∈ closed_ball g r) :
  ∥h∥ ≤ ∥g∥ + r :=
calc
  ∥h∥ = ∥g + (h - g)∥ : by rw [add_sub_cancel'_right]
  ... ≤ ∥g∥ + ∥h - g∥  : norm_add_le _ _
  ... ≤ ∥g∥ + r : by { apply add_le_add_left, rw ← dist_eq_norm, exact H }

lemma norm_le_norm_add_const_of_dist_le {a b : α} {c : ℝ} (h : dist a b ≤ c) :
  ∥a∥ ≤ ∥b∥ + c :=
norm_le_of_mem_closed_ball h

lemma norm_lt_of_mem_ball {g h : α} {r : ℝ} (H : h ∈ ball g r) :
  ∥h∥ < ∥g∥ + r :=
calc
  ∥h∥ = ∥g + (h - g)∥ : by rw [add_sub_cancel'_right]
  ... ≤ ∥g∥ + ∥h - g∥  : norm_add_le _ _
  ... < ∥g∥ + r : by { apply add_lt_add_left, rw ← dist_eq_norm, exact H }

lemma norm_lt_norm_add_const_of_dist_lt {a b : α} {c : ℝ} (h : dist a b < c) :
  ∥a∥ < ∥b∥ + c :=
norm_lt_of_mem_ball h

lemma bounded_iff_forall_norm_le {s : set α} : bounded s ↔ ∃ C, ∀ x ∈ s, ∥x∥ ≤ C :=
begin
  rw bounded_iff_subset_ball (0 : α),
  exact exists_congr (λ r, by simp [(⊆), set.subset]),
end

@[simp] lemma mem_sphere_iff_norm (v w : α) (r : ℝ) : w ∈ sphere v r ↔ ∥w - v∥ = r :=
by simp [dist_eq_norm]

@[simp] lemma mem_sphere_zero_iff_norm {w : α} {r : ℝ} : w ∈ sphere (0:α) r ↔ ∥w∥ = r :=
by simp [dist_eq_norm]

@[simp] lemma norm_eq_of_mem_sphere {r : ℝ} (x : sphere (0:α) r) : ∥(x:α)∥ = r :=
mem_sphere_zero_iff_norm.mp x.2

lemma ne_zero_of_norm_pos {g : α} : 0 < ∥ g ∥ → g ≠ 0 :=
begin
  intros hpos hzero,
  rw [hzero, norm_zero] at hpos,
  exact lt_irrefl 0 hpos,
end

lemma nonzero_of_mem_sphere {r : ℝ} (hr : 0 < r) (x : sphere (0:α) r) : (x:α) ≠ 0 :=
begin
  refine ne_zero_of_norm_pos _,
  rwa norm_eq_of_mem_sphere x,
end

lemma nonzero_of_mem_unit_sphere (x : sphere (0:α) 1) : (x:α) ≠ 0 :=
by { apply nonzero_of_mem_sphere, norm_num }

/-- We equip the sphere, in a seminormed group, with a formal operation of negation, namely the
antipodal map. -/
instance {r : ℝ} : has_neg (sphere (0:α) r) :=
{ neg := λ w, ⟨-↑w, by simp⟩ }

@[simp] lemma coe_neg_sphere {r : ℝ} (v : sphere (0:α) r) :
  (((-v) : sphere _ _) : α) = - (v:α) :=
rfl

namespace isometric

/-- Addition `y ↦ y + x` as an `isometry`. -/
protected def add_right (x : α) : α ≃ᵢ α :=
{ isometry_to_fun := isometry_emetric_iff_metric.2 $ λ y z, dist_add_right _ _ _,
  .. equiv.add_right x }

@[simp] lemma add_right_to_equiv (x : α) :
  (isometric.add_right x).to_equiv = equiv.add_right x := rfl

@[simp] lemma coe_add_right (x : α) : (isometric.add_right x : α → α) = λ y, y + x := rfl

lemma add_right_apply (x y : α) : (isometric.add_right x : α → α) y = y + x := rfl

@[simp] lemma add_right_symm (x : α) :
  (isometric.add_right x).symm = isometric.add_right (-x) :=
ext $ λ y, rfl

/-- Addition `y ↦ x + y` as an `isometry`. -/
protected def add_left (x : α) : α ≃ᵢ α :=
{ isometry_to_fun := isometry_emetric_iff_metric.2 $ λ y z, dist_add_left _ _ _,
  to_equiv := equiv.add_left x }

@[simp] lemma add_left_to_equiv (x : α) :
  (isometric.add_left x).to_equiv = equiv.add_left x := rfl

@[simp] lemma coe_add_left (x : α) : ⇑(isometric.add_left x) = (+) x := rfl

@[simp] lemma add_left_symm (x : α) :
  (isometric.add_left x).symm = isometric.add_left (-x) :=
ext $ λ y, rfl

variable (α)

/-- Negation `x ↦ -x` as an `isometry`. -/
protected def neg : α ≃ᵢ α :=
{ isometry_to_fun := isometry_emetric_iff_metric.2 $ λ x y, dist_neg_neg _ _,
  to_equiv := equiv.neg α }

variable {α}

@[simp] lemma neg_symm : (isometric.neg α).symm = isometric.neg α := rfl

@[simp] lemma neg_to_equiv : (isometric.neg α).to_equiv = equiv.neg α := rfl

@[simp] lemma coe_neg : ⇑(isometric.neg α) = has_neg.neg := rfl

end isometric

theorem normed_group.tendsto_nhds_zero {f : γ → α} {l : filter γ} :
  tendsto f l (𝓝 0) ↔ ∀ ε > 0, ∀ᶠ x in l, ∥ f x ∥ < ε :=
metric.tendsto_nhds.trans $ by simp only [dist_zero_right]

lemma normed_group.tendsto_nhds_nhds {f : α → β} {x : α} {y : β} :
  tendsto f (𝓝 x) (𝓝 y) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x', ∥x' - x∥ < δ → ∥f x' - y∥ < ε :=
by simp_rw [metric.tendsto_nhds_nhds, dist_eq_norm]

lemma normed_group.cauchy_seq_iff {u : ℕ → α} :
  cauchy_seq u ↔ ∀ ε > 0, ∃ N, ∀ m n, N ≤ m → N ≤ n → ∥u m - u n∥ < ε :=
by simp [metric.cauchy_seq_iff, dist_eq_norm]

lemma cauchy_seq.add {u v : ℕ → α} (hu : cauchy_seq u) (hv : cauchy_seq v) : cauchy_seq (u + v) :=
begin
  rw normed_group.cauchy_seq_iff at *,
  intros ε ε_pos,
  rcases hu (ε/2) (half_pos ε_pos) with ⟨Nu, hNu⟩,
  rcases hv (ε/2) (half_pos ε_pos) with ⟨Nv, hNv⟩,
  use max Nu Nv,
  intros m n hm hn,
  replace hm := max_le_iff.mp hm,
  replace hn := max_le_iff.mp hn,

  calc ∥(u + v) m - (u + v) n∥ = ∥u m + v m - (u n + v n)∥ : rfl
  ... = ∥(u m - u n) + (v m - v n)∥ : by abel
  ... ≤ ∥u m - u n∥ + ∥v m - v n∥ : norm_add_le _ _
  ... < ε : by linarith only [hNu m n hm.1 hn.1, hNv m n hm.2 hn.2]
end

open finset

lemma cauchy_seq_sum_of_eventually_eq {u v : ℕ → α} {N : ℕ} (huv : ∀ n ≥ N, u n = v n)
  (hv : cauchy_seq (λ n, ∑ k in range (n+1), v k)) : cauchy_seq (λ n, ∑ k in range (n + 1), u k) :=
begin
  let d : ℕ → α := λ n, ∑ k in range (n + 1), (u k - v k),
  rw show (λ n, ∑ k in range (n + 1), u k) = d + (λ n, ∑ k in range (n + 1), v k),
    by { ext n, simp [d] },
  have : ∀ n ≥ N, d n = d N,
  { intros n hn,
    dsimp [d],
    rw eventually_constant_sum _ hn,
    intros m hm,
    simp [huv m hm] },
  exact (tendsto_at_top_of_eventually_const this).cauchy_seq.add hv
end

/-- A homomorphism `f` of seminormed groups is Lipschitz, if there exists a constant `C` such that
for all `x`, one has `∥f x∥ ≤ C * ∥x∥`. The analogous condition for a linear map of
(semi)normed spaces is in `normed_space.operator_norm`. -/
lemma add_monoid_hom.lipschitz_of_bound (f : α →+ β) (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  lipschitz_with (real.to_nnreal C) f :=
lipschitz_with.of_dist_le' $ λ x y, by simpa only [dist_eq_norm, f.map_sub] using h (x - y)

lemma lipschitz_on_with_iff_norm_sub_le {f : α → β} {C : ℝ≥0} {s : set α} :
  lipschitz_on_with C f s ↔  ∀ (x ∈ s) (y ∈ s), ∥f x - f y∥ ≤ C * ∥x - y∥ :=
by simp only [lipschitz_on_with_iff_dist_le_mul, dist_eq_norm]

lemma lipschitz_on_with.norm_sub_le {f : α → β} {C : ℝ≥0} {s : set α} (h : lipschitz_on_with C f s)
  {x y : α} (x_in : x ∈ s) (y_in : y ∈ s) : ∥f x - f y∥ ≤ C * ∥x - y∥ :=
lipschitz_on_with_iff_norm_sub_le.mp h x x_in y y_in

lemma lipschitz_with_iff_norm_sub_le {f : α → β} {C : ℝ≥0} :
  lipschitz_with C f ↔ ∀ x y, ∥f x - f y∥ ≤ C * ∥x - y∥ :=
by simp only [lipschitz_with_iff_dist_le_mul, dist_eq_norm]

/-- A homomorphism `f` of seminormed groups is continuous, if there exists a constant `C` such that
for all `x`, one has `∥f x∥ ≤ C * ∥x∥`.
The analogous condition for a linear map of normed spaces is in `normed_space.operator_norm`. -/
lemma add_monoid_hom.continuous_of_bound (f : α →+ β) (C : ℝ) (h : ∀x, ∥f x∥ ≤ C * ∥x∥) :
  continuous f :=
(f.lipschitz_of_bound C h).continuous

lemma is_compact.exists_bound_of_continuous_on {γ : Type*} [topological_space γ]
  {s : set γ} (hs : is_compact s) {f : γ → α} (hf : continuous_on f s) :
  ∃ C, ∀ x ∈ s, ∥f x∥ ≤ C :=
begin
  have : bounded (f '' s) := (hs.image_of_continuous_on hf).bounded,
  rcases bounded_iff_forall_norm_le.1 this with ⟨C, hC⟩,
  exact ⟨C, λ x hx, hC _ (set.mem_image_of_mem _ hx)⟩,
end

lemma add_monoid_hom.isometry_iff_norm (f : α →+ β) : isometry f ↔ ∀ x, ∥f x∥ = ∥x∥ :=
begin
  simp only [isometry_emetric_iff_metric, dist_eq_norm, ← f.map_sub],
  refine ⟨λ h x, _, λ h x y, h _⟩,
  simpa using h x 0
end

lemma add_monoid_hom.isometry_of_norm (f : α →+ β) (hf : ∀ x, ∥f x∥ = ∥x∥) : isometry f :=
f.isometry_iff_norm.2 hf

lemma controlled_sum_of_mem_closure {s : add_subgroup α} {g : α}
  (hg : g ∈ closure (s : set α)) {b : ℕ → ℝ} (b_pos : ∀ n, 0 < b n) :
  ∃ v : ℕ → α,
    tendsto (λ n, ∑ i in range (n+1), v i) at_top (𝓝 g) ∧
    (∀ n, v n ∈ s) ∧
    ∥v 0 - g∥ < b 0 ∧
    ∀ n > 0, ∥v n∥ < b n :=
begin
  obtain ⟨u : ℕ → α, u_in : ∀ n, u n ∈ s, lim_u : tendsto u at_top (𝓝 g)⟩ :=
    mem_closure_iff_seq_limit.mp hg,
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, ∀ n ≥ n₀, ∥u n - g∥ < b 0,
  { have : {x | ∥x - g∥ < b 0} ∈ 𝓝 g,
    { simp_rw ← dist_eq_norm,
      exact metric.ball_mem_nhds _ (b_pos _) },
    exact filter.tendsto_at_top'.mp lim_u _ this },
  set z : ℕ → α := λ n, u (n + n₀),
  have lim_z : tendsto z at_top (𝓝 g) := lim_u.comp (tendsto_add_at_top_nat n₀),
  have mem_𝓤 : ∀ n, {p : α × α | ∥p.1 - p.2∥ < b (n + 1)} ∈ 𝓤 α :=
  λ n, by simpa [← dist_eq_norm] using metric.dist_mem_uniformity (b_pos $ n+1),
  obtain ⟨φ : ℕ → ℕ, φ_extr : strict_mono φ,
          hφ : ∀ n, ∥z (φ $ n + 1) - z (φ n)∥ < b (n + 1)⟩ :=
    lim_z.cauchy_seq.subseq_mem mem_𝓤,
  set w : ℕ → α := z ∘ φ,
  have hw : tendsto w at_top (𝓝 g),
    from lim_z.comp φ_extr.tendsto_at_top,
  set v : ℕ → α := λ i, if i = 0 then w 0 else w i - w (i - 1),
  refine ⟨v, tendsto.congr (finset.eq_sum_range_sub' w) hw , _,
          hn₀ _ (n₀.le_add_left _), _⟩,
  { rintro ⟨⟩,
    { change w 0 ∈ s,
      apply u_in },
    { apply s.sub_mem ; apply u_in }, },
  { intros l hl,
    obtain ⟨k, rfl⟩ : ∃ k, l = k+1, exact nat.exists_eq_succ_of_ne_zero (ne_of_gt hl),
    apply hφ },
end

lemma controlled_sum_of_mem_closure_range {j : α →+ β} {h : β}
  (Hh : h ∈ (closure $ (j.range : set β))) {b : ℕ → ℝ} (b_pos : ∀ n, 0 < b n) :
  ∃ g : ℕ → α,
    tendsto (λ n, ∑ i in range (n+1), j (g i)) at_top (𝓝 h) ∧
    ∥j (g 0) - h∥ < b 0 ∧
    ∀ n > 0, ∥j (g n)∥ < b n :=
begin
  rcases controlled_sum_of_mem_closure Hh b_pos with ⟨v, sum_v, v_in, hv₀, hv_pos⟩,
  choose g hg using v_in,
  change ∀ (n : ℕ), j (g n) = v n at hg,
  refine ⟨g, by simpa [← hg] using sum_v, by simpa [hg 0] using hv₀, λ n hn,
          by simpa [hg] using hv_pos n hn⟩
end

section nnnorm

/-- Auxiliary class, endowing a type `α` with a function `nnnorm : α → ℝ≥0`. -/
class has_nnnorm (α : Type*) := (nnnorm : α → ℝ≥0)

export has_nnnorm (nnnorm)

notation `∥`e`∥₊` := nnnorm e

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_group.to_has_nnnorm : has_nnnorm α := ⟨λ a, ⟨norm a, norm_nonneg a⟩⟩

@[simp, norm_cast] lemma coe_nnnorm (a : α) : (∥a∥₊ : ℝ) = norm a := rfl

lemma nndist_eq_nnnorm (a b : α) : nndist a b = ∥a - b∥₊ := nnreal.eq $ dist_eq_norm _ _

@[simp] lemma nnnorm_zero : ∥(0 : α)∥₊ = 0 :=
nnreal.eq norm_zero

lemma nnnorm_add_le (g h : α) : ∥g + h∥₊ ≤ ∥g∥₊ + ∥h∥₊ :=
nnreal.coe_le_coe.2 $ norm_add_le g h

@[simp] lemma nnnorm_neg (g : α) : ∥-g∥₊ = ∥g∥₊ :=
nnreal.eq $ norm_neg g

lemma nndist_nnnorm_nnnorm_le (g h : α) : nndist ∥g∥₊ ∥h∥₊ ≤ ∥g - h∥₊ :=
nnreal.coe_le_coe.2 $ dist_norm_norm_le g h

lemma of_real_norm_eq_coe_nnnorm (x : β) : ennreal.of_real ∥x∥ = (∥x∥₊ : ℝ≥0∞) :=
ennreal.of_real_eq_coe_nnreal _

lemma edist_eq_coe_nnnorm_sub (x y : β) : edist x y = (∥x - y∥₊ : ℝ≥0∞) :=
by rw [edist_dist, dist_eq_norm, of_real_norm_eq_coe_nnnorm]

lemma edist_eq_coe_nnnorm (x : β) : edist x 0 = (∥x∥₊ : ℝ≥0∞) :=
by rw [edist_eq_coe_nnnorm_sub, _root_.sub_zero]

lemma mem_emetric_ball_0_iff {x : β} {r : ℝ≥0∞} : x ∈ emetric.ball (0 : β) r ↔ ↑∥x∥₊ < r :=
by rw [emetric.mem_ball, edist_eq_coe_nnnorm]

lemma nndist_add_add_le (g₁ g₂ h₁ h₂ : α) :
  nndist (g₁ + g₂) (h₁ + h₂) ≤ nndist g₁ h₁ + nndist g₂ h₂ :=
nnreal.coe_le_coe.2 $ dist_add_add_le g₁ g₂ h₁ h₂

lemma edist_add_add_le (g₁ g₂ h₁ h₂ : α) :
  edist (g₁ + g₂) (h₁ + h₂) ≤ edist g₁ h₁ + edist g₂ h₂ :=
by { simp only [edist_nndist], norm_cast, apply nndist_add_add_le }

lemma nnnorm_sum_le {β} : ∀(s : finset β) (f : β → α),
  ∥∑ a in s, f a∥₊ ≤ ∑ a in s, ∥f a∥₊ :=
finset.le_sum_of_subadditive nnnorm nnnorm_zero nnnorm_add_le

lemma add_monoid_hom.lipschitz_of_bound_nnnorm (f : α →+ β) (C : ℝ≥0) (h : ∀ x, ∥f x∥₊ ≤ C * ∥x∥₊) :
  lipschitz_with C f :=
@real.to_nnreal_coe C ▸ f.lipschitz_of_bound C h

end nnnorm

lemma lipschitz_with.neg {α : Type*} [pseudo_emetric_space α] {K : ℝ≥0} {f : α → β}
  (hf : lipschitz_with K f) : lipschitz_with K (λ x, -f x) :=
λ x y, by simpa only [edist_dist, dist_neg_neg] using hf x y

lemma lipschitz_with.add {α : Type*} [pseudo_emetric_space α] {Kf : ℝ≥0} {f : α → β}
  (hf : lipschitz_with Kf f) {Kg : ℝ≥0} {g : α → β} (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf + Kg) (λ x, f x + g x) :=
λ x y,
calc edist (f x + g x) (f y + g y) ≤ edist (f x) (f y) + edist (g x) (g y) :
  edist_add_add_le _ _ _ _
... ≤ Kf * edist x y + Kg * edist x y :
  add_le_add (hf x y) (hg x y)
... = (Kf + Kg) * edist x y :
  (add_mul _ _ _).symm

lemma lipschitz_with.sub {α : Type*} [pseudo_emetric_space α] {Kf : ℝ≥0} {f : α → β}
  (hf : lipschitz_with Kf f) {Kg : ℝ≥0} {g : α → β} (hg : lipschitz_with Kg g) :
  lipschitz_with (Kf + Kg) (λ x, f x - g x) :=
by simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma antilipschitz_with.add_lipschitz_with {α : Type*} [pseudo_metric_space α] {Kf : ℝ≥0}
  {f : α → β} (hf : antilipschitz_with Kf f) {Kg : ℝ≥0} {g : α → β} (hg : lipschitz_with Kg g)
  (hK : Kg < Kf⁻¹) : antilipschitz_with (Kf⁻¹ - Kg)⁻¹ (λ x, f x + g x) :=
begin
  refine antilipschitz_with.of_le_mul_dist (λ x y, _),
  rw [nnreal.coe_inv, ← div_eq_inv_mul],
  rw le_div_iff (nnreal.coe_pos.2 $ nnreal.sub_pos.2 hK),
  rw [mul_comm, nnreal.coe_sub (le_of_lt hK), sub_mul],
  calc ↑Kf⁻¹ * dist x y - Kg * dist x y ≤ dist (f x) (f y) - dist (g x) (g y) :
    sub_le_sub (hf.mul_le_dist x y) (hg.dist_le_mul x y)
  ... ≤ _ : le_trans (le_abs_self _) (abs_dist_sub_le_dist_add_add _ _ _ _)
end

lemma antilipschitz_with.add_sub_lipschitz_with {α : Type*} [pseudo_metric_space α] {Kf : ℝ≥0}
  {f : α → β} (hf : antilipschitz_with Kf f) {Kg : ℝ≥0} {g : α → β} (hg : lipschitz_with Kg (g - f))
  (hK : Kg < Kf⁻¹) : antilipschitz_with (Kf⁻¹ - Kg)⁻¹ g :=
by simpa only [pi.sub_apply, add_sub_cancel'_right] using hf.add_lipschitz_with hg hK

/-- A group homomorphism from an `add_comm_group` to a `semi_normed_group` induces a
`semi_normed_group` structure on the domain.

See note [reducible non-instances] -/
@[reducible]
def semi_normed_group.induced [add_comm_group γ] (f : γ →+ α) : semi_normed_group γ :=
{ norm    := λ x, ∥f x∥,
  dist_eq := λ x y, by simpa only [add_monoid_hom.map_sub, ← dist_eq_norm],
  .. pseudo_metric_space.induced f semi_normed_group.to_pseudo_metric_space, }

/-- A subgroup of a seminormed group is also a seminormed group,
with the restriction of the norm. -/
instance add_subgroup.semi_normed_group (s : add_subgroup α) : semi_normed_group s :=
semi_normed_group.induced s.subtype

/-- If `x` is an element of a subgroup `s` of a seminormed group `E`, its norm in `s` is equal to
its norm in `E`. -/
@[simp] lemma coe_norm_subgroup {E : Type*} [semi_normed_group E] {s : add_subgroup E} (x : s) :
  ∥x∥ = ∥(x:E)∥ :=
rfl

/-- A submodule of a seminormed group is also a seminormed group, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance submodule.semi_normed_group {𝕜 : Type*} {_ : ring 𝕜}
  {E : Type*} [semi_normed_group E] {_ : module 𝕜 E} (s : submodule 𝕜 E) : semi_normed_group s :=
{ norm := λx, norm (x : E),
  dist_eq := λx y, dist_eq_norm (x : E) (y : E) }

/-- If `x` is an element of a submodule `s` of a normed group `E`, its norm in `E` is equal to its
norm in `s`.

See note [implicit instance arguments]. -/
@[simp, norm_cast] lemma submodule.norm_coe {𝕜 : Type*} {_ : ring 𝕜}
  {E : Type*} [semi_normed_group E] {_ : module 𝕜 E} {s : submodule 𝕜 E} (x : s) :
  ∥(x : E)∥ = ∥x∥ :=
rfl

@[simp] lemma submodule.norm_mk {𝕜 : Type*} {_ : ring 𝕜}
  {E : Type*} [semi_normed_group E] {_ : module 𝕜 E} {s : submodule 𝕜 E} (x : E) (hx : x ∈ s) :
  ∥(⟨x, hx⟩ : s)∥ = ∥x∥ :=
rfl

/-- seminormed group instance on the product of two seminormed groups, using the sup norm. -/
instance prod.semi_normed_group : semi_normed_group (α × β) :=
{ norm := λx, max ∥x.1∥ ∥x.2∥,
  dist_eq := assume (x y : α × β),
    show max (dist x.1 y.1) (dist x.2 y.2) = (max ∥(x - y).1∥ ∥(x - y).2∥), by simp [dist_eq_norm] }

lemma prod.semi_norm_def (x : α × β) : ∥x∥ = (max ∥x.1∥ ∥x.2∥) := rfl

lemma prod.nnsemi_norm_def (x : α × β) : ∥x∥₊ = max (∥x.1∥₊) (∥x.2∥₊) :=
by { have := x.semi_norm_def, simp only [← coe_nnnorm] at this, exact_mod_cast this }

lemma semi_norm_fst_le (x : α × β) : ∥x.1∥ ≤ ∥x∥ :=
le_max_left _ _

lemma semi_norm_snd_le (x : α × β) : ∥x.2∥ ≤ ∥x∥ :=
le_max_right _ _

lemma semi_norm_prod_le_iff {x : α × β} {r : ℝ} :
  ∥x∥ ≤ r ↔ ∥x.1∥ ≤ r ∧ ∥x.2∥ ≤ r :=
max_le_iff

/-- seminormed group instance on the product of finitely many seminormed groups,
using the sup norm. -/
instance pi.semi_normed_group {π : ι → Type*} [fintype ι] [∀i, semi_normed_group (π i)] :
  semi_normed_group (Πi, π i) :=
{ norm := λf, ((finset.sup finset.univ (λ b, ∥f b∥₊) : ℝ≥0) : ℝ),
  dist_eq := assume x y,
    congr_arg (coe : ℝ≥0 → ℝ) $ congr_arg (finset.sup finset.univ) $ funext $ assume a,
    show nndist (x a) (y a) = ∥x a - y a∥₊, from nndist_eq_nnnorm _ _ }

/-- The seminorm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
lemma pi_semi_norm_le_iff {π : ι → Type*} [fintype ι] [∀i, semi_normed_group (π i)] {r : ℝ}
  (hr : 0 ≤ r) {x : Πi, π i} : ∥x∥ ≤ r ↔ ∀i, ∥x i∥ ≤ r :=
by simp only [← dist_zero_right, dist_pi_le_iff hr, pi.zero_apply]

/-- The seminorm of an element in a product space is `< r` if and only if the norm of each
component is. -/
lemma pi_semi_norm_lt_iff {π : ι → Type*} [fintype ι] [∀i, semi_normed_group (π i)] {r : ℝ}
  (hr : 0 < r) {x : Πi, π i} : ∥x∥ < r ↔ ∀i, ∥x i∥ < r :=
by simp only [← dist_zero_right, dist_pi_lt_iff hr, pi.zero_apply]

lemma semi_norm_le_pi_norm {π : ι → Type*} [fintype ι] [∀i, semi_normed_group (π i)] (x : Πi, π i)
  (i : ι) : ∥x i∥ ≤ ∥x∥ :=
(pi_semi_norm_le_iff (norm_nonneg x)).1 (le_refl _) i

@[simp] lemma pi_semi_norm_const [nonempty ι] [fintype ι] (a : α) : ∥(λ i : ι, a)∥ = ∥a∥ :=
by simpa only [← dist_zero_right] using dist_pi_const a 0

@[simp] lemma pi_nnsemi_norm_const [nonempty ι] [fintype ι] (a : α) :
  ∥(λ i : ι, a)∥₊ = ∥a∥₊ :=
nnreal.eq $ pi_semi_norm_const a

lemma tendsto_iff_norm_tendsto_zero {f : ι → β} {a : filter ι} {b : β} :
  tendsto f a (𝓝 b) ↔ tendsto (λ e, ∥f e - b∥) a (𝓝 0) :=
by { convert tendsto_iff_dist_tendsto_zero, simp [dist_eq_norm] }

lemma is_bounded_under_of_tendsto {l : filter ι} {f : ι → α} {c : α}
  (h : filter.tendsto f l (𝓝 c)) : is_bounded_under (≤) l (λ x, ∥f x∥) :=
⟨∥c∥ + 1, @tendsto.eventually ι α f _ _ (λ k, ∥k∥ ≤ ∥c∥ + 1) h (filter.eventually_iff_exists_mem.mpr
  ⟨metric.closed_ball c 1, metric.closed_ball_mem_nhds c zero_lt_one,
    λ y hy, norm_le_norm_add_const_of_dist_le hy⟩)⟩

lemma tendsto_zero_iff_norm_tendsto_zero {f : γ → β} {a : filter γ} :
  tendsto f a (𝓝 0) ↔ tendsto (λ e, ∥f e∥) a (𝓝 0) :=
by { rw [tendsto_iff_norm_tendsto_zero], simp only [sub_zero] }

/-- Special case of the sandwich theorem: if the norm of `f` is eventually bounded by a real
function `g` which tends to `0`, then `f` tends to `0`.
In this pair of lemmas (`squeeze_zero_norm'` and `squeeze_zero_norm`), following a convention of
similar lemmas in `topology.metric_space.basic` and `topology.algebra.ordered`, the `'` version is
phrased using "eventually" and the non-`'` version is phrased absolutely. -/
lemma squeeze_zero_norm' {f : γ → α} {g : γ → ℝ} {t₀ : filter γ}
  (h : ∀ᶠ n in t₀, ∥f n∥ ≤ g n)
  (h' : tendsto g t₀ (𝓝 0)) : tendsto f t₀ (𝓝 0) :=
tendsto_zero_iff_norm_tendsto_zero.mpr
  (squeeze_zero' (eventually_of_forall (λ n, norm_nonneg _)) h h')

/-- Special case of the sandwich theorem: if the norm of `f` is bounded by a real function `g` which
tends to `0`, then `f` tends to `0`.  -/
lemma squeeze_zero_norm {f : γ → α} {g : γ → ℝ} {t₀ : filter γ}
  (h : ∀ (n:γ), ∥f n∥ ≤ g n)
  (h' : tendsto g t₀ (𝓝 0)) :
  tendsto f t₀ (𝓝 0) :=
squeeze_zero_norm' (eventually_of_forall h) h'

lemma tendsto_norm_sub_self (x : α) : tendsto (λ g : α, ∥g - x∥) (𝓝 x) (𝓝 0) :=
by simpa [dist_eq_norm] using tendsto_id.dist (tendsto_const_nhds : tendsto (λ g, (x:α)) (𝓝 x) _)

lemma tendsto_norm {x : α} : tendsto (λg : α, ∥g∥) (𝓝 x) (𝓝 ∥x∥) :=
by simpa using tendsto_id.dist (tendsto_const_nhds : tendsto (λ g, (0:α)) _ _)

lemma tendsto_norm_zero : tendsto (λg : α, ∥g∥) (𝓝 0) (𝓝 0) :=
by simpa using tendsto_norm_sub_self (0:α)

@[continuity]
lemma continuous_norm : continuous (λg:α, ∥g∥) :=
by simpa using continuous_id.dist (continuous_const : continuous (λ g, (0:α)))

@[continuity]
lemma continuous_nnnorm : continuous (λ (a : α), ∥a∥₊) :=
continuous_subtype_mk _ continuous_norm

lemma lipschitz_with_one_norm : lipschitz_with 1 (norm : α → ℝ) :=
by simpa only [dist_zero_left] using lipschitz_with.dist_right (0 : α)

lemma uniform_continuous_norm : uniform_continuous (norm : α → ℝ) :=
lipschitz_with_one_norm.uniform_continuous

lemma uniform_continuous_nnnorm : uniform_continuous (λ (a : α), ∥a∥₊) :=
uniform_continuous_subtype_mk uniform_continuous_norm _

section

variables {l : filter γ} {f : γ → α} {a : α}

lemma filter.tendsto.norm {a : α} (h : tendsto f l (𝓝 a)) : tendsto (λ x, ∥f x∥) l (𝓝 ∥a∥) :=
tendsto_norm.comp h

lemma filter.tendsto.nnnorm (h : tendsto f l (𝓝 a)) :
  tendsto (λ x, ∥f x∥₊) l (𝓝 (∥a∥₊)) :=
tendsto.comp continuous_nnnorm.continuous_at h

end

section

variables [topological_space γ] {f : γ → α} {s : set γ} {a : γ} {b : α}

lemma continuous.norm (h : continuous f) : continuous (λ x, ∥f x∥) := continuous_norm.comp h

lemma continuous.nnnorm (h : continuous f) : continuous (λ x, ∥f x∥₊) :=
continuous_nnnorm.comp h

lemma continuous_at.norm (h : continuous_at f a) : continuous_at (λ x, ∥f x∥) a := h.norm

lemma continuous_at.nnnorm (h : continuous_at f a) : continuous_at (λ x, ∥f x∥₊) a := h.nnnorm

lemma continuous_within_at.norm (h : continuous_within_at f s a) :
  continuous_within_at (λ x, ∥f x∥) s a :=
h.norm

lemma continuous_within_at.nnnorm (h : continuous_within_at f s a) :
  continuous_within_at (λ x, ∥f x∥₊) s a :=
h.nnnorm

lemma continuous_on.norm (h : continuous_on f s) : continuous_on (λ x, ∥f x∥) s :=
λ x hx, (h x hx).norm

lemma continuous_on.nnnorm (h : continuous_on f s) : continuous_on (λ x, ∥f x∥₊) s :=
λ x hx, (h x hx).nnnorm

end

/-- If `∥y∥→∞`, then we can assume `y≠x` for any fixed `x`. -/
lemma eventually_ne_of_tendsto_norm_at_top {l : filter γ} {f : γ → α}
  (h : tendsto (λ y, ∥f y∥) l at_top) (x : α) :
  ∀ᶠ y in l, f y ≠ x :=
begin
  have : ∀ᶠ y in l, 1 + ∥x∥ ≤ ∥f y∥ := h (mem_at_top (1 + ∥x∥)),
  refine this.mono (λ y hy hxy, _),
  subst x,
  exact not_le_of_lt zero_lt_one (add_le_iff_nonpos_left.1 hy)
end

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_group.has_lipschitz_add : has_lipschitz_add α :=
{ lipschitz_add := ⟨2, lipschitz_with.prod_fst.add lipschitz_with.prod_snd⟩ }

/-- A seminormed group is a uniform additive group, i.e., addition and subtraction are uniformly
continuous. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_uniform_group : uniform_add_group α :=
⟨(lipschitz_with.prod_fst.sub lipschitz_with.prod_snd).uniform_continuous⟩

@[priority 100] -- see Note [lower instance priority]
instance normed_top_group : topological_add_group α :=
by apply_instance -- short-circuit type class inference

lemma nat.norm_cast_le [has_one α] : ∀ n : ℕ, ∥(n : α)∥ ≤ n * ∥(1 : α)∥
| 0 := by simp
| (n + 1) := by { rw [n.cast_succ, n.cast_succ, add_mul, one_mul],
                  exact norm_add_le_of_le (nat.norm_cast_le n) le_rfl }

lemma semi_normed_group.mem_closure_iff {s : set α} {x : α} :
  x ∈ closure s ↔ ∀ ε > 0, ∃ y ∈ s, ∥x - y∥ < ε :=
by simp [metric.mem_closure_iff, dist_eq_norm]

lemma norm_le_zero_iff' [separated_space α] {g : α} :
  ∥g∥ ≤ 0 ↔ g = 0 :=
begin
  have : g = 0 ↔ g ∈ closure ({0} : set α),
  by simpa only [separated_space.out, mem_id_rel, sub_zero] using group_separation_rel g (0 : α),
  rw [this, semi_normed_group.mem_closure_iff],
  simp [forall_lt_iff_le']
end

lemma norm_eq_zero_iff' [separated_space α] {g : α} : ∥g∥ = 0 ↔ g = 0 :=
begin
  conv_rhs { rw ← norm_le_zero_iff' },
  split ; intro h,
  { rw h },
  { exact le_antisymm h (norm_nonneg g) }
end

lemma norm_pos_iff' [separated_space α] {g : α} : 0 < ∥g∥ ↔ g ≠ 0 :=
begin
  rw lt_iff_le_and_ne,
  simp only [norm_nonneg, true_and],
  rw [ne_comm],
  exact not_iff_not_of_iff (norm_eq_zero_iff'),
end

end semi_normed_group

section normed_group

/-- Construct a normed group from a translation invariant distance -/
def normed_group.of_add_dist [has_norm α] [add_comm_group α] [metric_space α]
  (H1 : ∀ x:α, ∥x∥ = dist x 0)
  (H2 : ∀ x y z : α, dist x y ≤ dist (x + z) (y + z)) : normed_group α :=
{ dist_eq := λ x y, begin
    rw H1, apply le_antisymm,
    { rw [sub_eq_add_neg, ← add_right_neg y], apply H2 },
    { have := H2 (x-y) 0 y, rwa [sub_add_cancel, zero_add] at this }
  end }

/-- A normed group can be built from a norm that satisfies algebraic properties. This is
formalised in this structure. -/
structure normed_group.core (α : Type*) [add_comm_group α] [has_norm α] : Prop :=
(norm_eq_zero_iff : ∀ x : α, ∥x∥ = 0 ↔ x = 0)
(triangle : ∀ x y : α, ∥x + y∥ ≤ ∥x∥ + ∥y∥)
(norm_neg : ∀ x : α, ∥-x∥ = ∥x∥)

/-- The `semi_normed_group.core` induced by a `normed_group.core`. -/
lemma normed_group.core.to_semi_normed_group.core {α : Type*} [add_comm_group α] [has_norm α]
  (C : normed_group.core α) : semi_normed_group.core α :=
{ norm_zero := (C.norm_eq_zero_iff 0).2 rfl,
  triangle := C.triangle,
  norm_neg := C.norm_neg }

/-- Constructing a normed group from core properties of a norm, i.e., registering the distance and
the metric space structure from the norm properties. -/
noncomputable def normed_group.of_core (α : Type*) [add_comm_group α] [has_norm α]
  (C : normed_group.core α) : normed_group α :=
{ eq_of_dist_eq_zero := λ x y h,
  begin
    rw [dist_eq_norm] at h,
    exact sub_eq_zero.mp ((C.norm_eq_zero_iff _).1 h)
  end
  ..semi_normed_group.of_core α (normed_group.core.to_semi_normed_group.core C) }

variables [normed_group α] [normed_group β]

@[simp] lemma norm_eq_zero {g : α} : ∥g∥ = 0 ↔ g = 0 :=
dist_zero_right g ▸ dist_eq_zero

@[simp] lemma norm_pos_iff {g : α} : 0 < ∥ g ∥ ↔ g ≠ 0 :=
dist_zero_right g ▸ dist_pos

@[simp] lemma norm_le_zero_iff {g : α} : ∥g∥ ≤ 0 ↔ g = 0 :=
by { rw [← dist_zero_right], exact dist_le_zero }

lemma eq_of_norm_sub_le_zero {g h : α} (a : ∥g - h∥ ≤ 0) : g = h :=
by rwa [← sub_eq_zero, ← norm_le_zero_iff]

lemma eq_of_norm_sub_eq_zero {u v : α} (h : ∥u - v∥ = 0) : u = v :=
begin
  apply eq_of_dist_eq_zero,
  rwa dist_eq_norm
end

lemma norm_sub_eq_zero_iff {u v : α} : ∥u - v∥ = 0 ↔ u = v :=
begin
  convert dist_eq_zero,
  rwa dist_eq_norm
end

@[simp] lemma nnnorm_eq_zero {a : α} : ∥a∥₊ = 0 ↔ a = 0 :=
by simp only [nnreal.eq_iff.symm, nnreal.coe_zero, coe_nnnorm, norm_eq_zero]

/-- An injective group homomorphism from an `add_comm_group` to a `normed_group` induces a
`normed_group` structure on the domain.

See note [reducible non-instances]. -/
@[reducible]
def normed_group.induced [add_comm_group γ]
  (f : γ →+ α) (h : function.injective f) : normed_group γ :=
{ .. semi_normed_group.induced f,
  .. metric_space.induced f h normed_group.to_metric_space, }

/-- A subgroup of a normed group is also a normed group, with the restriction of the norm. -/
instance add_subgroup.normed_group (s : add_subgroup α) : normed_group s :=
normed_group.induced s.subtype subtype.coe_injective

/-- A submodule of a normed group is also a normed group, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance submodule.normed_group {𝕜 : Type*} {_ : ring 𝕜}
  {E : Type*} [normed_group E] {_ : module 𝕜 E} (s : submodule 𝕜 E) : normed_group s :=
{ ..submodule.semi_normed_group s }

/-- normed group instance on the product of two normed groups, using the sup norm. -/
instance prod.normed_group : normed_group (α × β) := { ..prod.semi_normed_group }

lemma prod.norm_def (x : α × β) : ∥x∥ = (max ∥x.1∥ ∥x.2∥) := rfl

lemma prod.nnnorm_def (x : α × β) : ∥x∥₊ = max (∥x.1∥₊) (∥x.2∥₊) :=
by { have := x.norm_def, simp only [← coe_nnnorm] at this, exact_mod_cast this }

lemma norm_fst_le (x : α × β) : ∥x.1∥ ≤ ∥x∥ :=
le_max_left _ _

lemma norm_snd_le (x : α × β) : ∥x.2∥ ≤ ∥x∥ :=
le_max_right _ _

lemma norm_prod_le_iff {x : α × β} {r : ℝ} :
  ∥x∥ ≤ r ↔ ∥x.1∥ ≤ r ∧ ∥x.2∥ ≤ r :=
max_le_iff

/-- normed group instance on the product of finitely many normed groups, using the sup norm. -/
instance pi.normed_group {π : ι → Type*} [fintype ι] [∀i, normed_group (π i)] :
  normed_group (Πi, π i) := { ..pi.semi_normed_group }

/-- The norm of an element in a product space is `≤ r` if and only if the norm of each
component is. -/
lemma pi_norm_le_iff {π : ι → Type*} [fintype ι] [∀i, normed_group (π i)] {r : ℝ} (hr : 0 ≤ r)
  {x : Πi, π i} : ∥x∥ ≤ r ↔ ∀i, ∥x i∥ ≤ r :=
by simp only [← dist_zero_right, dist_pi_le_iff hr, pi.zero_apply]

/-- The norm of an element in a product space is `< r` if and only if the norm of each
component is. -/
lemma pi_norm_lt_iff {π : ι → Type*} [fintype ι] [∀i, normed_group (π i)] {r : ℝ} (hr : 0 < r)
  {x : Πi, π i} : ∥x∥ < r ↔ ∀i, ∥x i∥ < r :=
by simp only [← dist_zero_right, dist_pi_lt_iff hr, pi.zero_apply]

lemma norm_le_pi_norm {π : ι → Type*} [fintype ι] [∀i, normed_group (π i)] (x : Πi, π i) (i : ι) :
  ∥x i∥ ≤ ∥x∥ :=
(pi_norm_le_iff (norm_nonneg x)).1 (le_refl _) i

@[simp] lemma pi_norm_const [nonempty ι] [fintype ι] (a : α) : ∥(λ i : ι, a)∥ = ∥a∥ :=
by simpa only [← dist_zero_right] using dist_pi_const a 0

@[simp] lemma pi_nnnorm_const [nonempty ι] [fintype ι] (a : α) :
  ∥(λ i : ι, a)∥₊ = ∥a∥₊ :=
nnreal.eq $ pi_norm_const a

lemma tendsto_norm_nhds_within_zero : tendsto (norm : α → ℝ) (𝓝[{0}ᶜ] 0) (𝓝[set.Ioi 0] 0) :=
(continuous_norm.tendsto' (0 : α) 0 norm_zero).inf $ tendsto_principal_principal.2 $
  λ x, norm_pos_iff.2

end normed_group

section semi_normed_ring

/-- A seminormed ring is a ring endowed with a seminorm which satisfies the inequality
`∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class semi_normed_ring (α : Type*) extends has_norm α, ring α, pseudo_metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

/-- A normed ring is a ring endowed with a norm which satisfies the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class normed_ring (α : Type*) extends has_norm α, ring α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul : ∀ a b, norm (a * b) ≤ norm a * norm b)

/-- A normed ring is a seminormed ring. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_ring.to_semi_normed_ring [β : normed_ring α] : semi_normed_ring α :=
{ ..β }

/-- A seminormed commutative ring is a commutative ring endowed with a seminorm which satisfies
the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class semi_normed_comm_ring (α : Type*) extends semi_normed_ring α :=
(mul_comm : ∀ x y : α, x * y = y * x)

/-- A normed commutative ring is a commutative ring endowed with a norm which satisfies
the inequality `∥x y∥ ≤ ∥x∥ ∥y∥`. -/
class normed_comm_ring (α : Type*) extends normed_ring α :=
(mul_comm : ∀ x y : α, x * y = y * x)

/-- A normed commutative ring is a seminormed commutative ring. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_comm_ring.to_semi_normed_comm_ring [β : normed_comm_ring α] :
  semi_normed_comm_ring α := { ..β }

instance : normed_comm_ring punit :=
{ norm_mul := λ _ _, by simp,
  ..punit.normed_group,
  ..punit.comm_ring, }

/-- A mixin class with the axiom `∥1∥ = 1`. Many `normed_ring`s and all `normed_field`s satisfy this
axiom. -/
class norm_one_class (α : Type*) [has_norm α] [has_one α] : Prop :=
(norm_one : ∥(1:α)∥ = 1)

export norm_one_class (norm_one)

attribute [simp] norm_one

@[simp] lemma nnnorm_one [semi_normed_group α] [has_one α] [norm_one_class α] : ∥(1 : α)∥₊ = 1 :=
nnreal.eq norm_one

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_comm_ring.to_comm_ring [β : semi_normed_comm_ring α] : comm_ring α := { ..β }

@[priority 100] -- see Note [lower instance priority]
instance normed_ring.to_normed_group [β : normed_ring α] : normed_group α := { ..β }

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_ring.to_semi_normed_group [β : semi_normed_ring α] :
  semi_normed_group α := { ..β }

instance prod.norm_one_class [normed_group α] [has_one α] [norm_one_class α]
  [normed_group β] [has_one β] [norm_one_class β] :
  norm_one_class (α × β) :=
⟨by simp [prod.norm_def]⟩

variables [semi_normed_ring α]

lemma norm_mul_le (a b : α) : (∥a*b∥) ≤ (∥a∥) * (∥b∥) :=
semi_normed_ring.norm_mul _ _

/-- A subalgebra of a seminormed ring is also a seminormed ring, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance subalgebra.semi_normed_ring {𝕜 : Type*} {_ : comm_ring 𝕜}
  {E : Type*} [semi_normed_ring E] {_ : algebra 𝕜 E} (s : subalgebra 𝕜 E) : semi_normed_ring s :=
{ norm_mul := λ a b, norm_mul_le a.1 b.1,
  ..s.to_submodule.semi_normed_group }

/-- A subalgebra of a normed ring is also a normed ring, with the restriction of the norm.

See note [implicit instance arguments]. -/
instance subalgebra.normed_ring {𝕜 : Type*} {_ : comm_ring 𝕜}
  {E : Type*} [normed_ring E] {_ : algebra 𝕜 E} (s : subalgebra 𝕜 E) : normed_ring s :=
{ ..s.semi_normed_ring }

lemma list.norm_prod_le' : ∀ {l : list α}, l ≠ [] → ∥l.prod∥ ≤ (l.map norm).prod
| [] h := (h rfl).elim
| [a] _ := by simp
| (a :: b :: l) _ :=
  begin
    rw [list.map_cons, list.prod_cons, @list.prod_cons _ _ _ ∥a∥],
    refine le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left _ (norm_nonneg _)),
    exact list.norm_prod_le' (list.cons_ne_nil b l)
  end

lemma list.norm_prod_le [norm_one_class α] : ∀ l : list α, ∥l.prod∥ ≤ (l.map norm).prod
| [] := by simp
| (a::l) := list.norm_prod_le' (list.cons_ne_nil a l)

lemma finset.norm_prod_le' {α : Type*} [normed_comm_ring α] (s : finset ι) (hs : s.nonempty)
  (f : ι → α) :
  ∥∏ i in s, f i∥ ≤ ∏ i in s, ∥f i∥ :=
begin
  rcases s with ⟨⟨l⟩, hl⟩,
  have : l.map f ≠ [], by simpa using hs,
  simpa using list.norm_prod_le' this
end

lemma finset.norm_prod_le {α : Type*} [normed_comm_ring α] [norm_one_class α] (s : finset ι)
  (f : ι → α) :
  ∥∏ i in s, f i∥ ≤ ∏ i in s, ∥f i∥ :=
begin
  rcases s with ⟨⟨l⟩, hl⟩,
  simpa using (l.map f).norm_prod_le
end

/-- If `α` is a seminormed ring, then `∥a^n∥≤ ∥a∥^n` for `n > 0`. See also `norm_pow_le`. -/
lemma norm_pow_le' (a : α) : ∀ {n : ℕ}, 0 < n → ∥a^n∥ ≤ ∥a∥^n
| 1 h := by simp
| (n+2) h := by { rw [pow_succ _ (n+1),  pow_succ _ (n+1)],
  exact le_trans (norm_mul_le a (a^(n+1)))
           (mul_le_mul (le_refl _)
                       (norm_pow_le' (nat.succ_pos _)) (norm_nonneg _) (norm_nonneg _)) }

/-- If `α` is a seminormed ring with `∥1∥=1`, then `∥a^n∥≤ ∥a∥^n`. See also `norm_pow_le'`. -/
lemma norm_pow_le [norm_one_class α] (a : α) : ∀ (n : ℕ), ∥a^n∥ ≤ ∥a∥^n
| 0 := by simp
| (n+1) := norm_pow_le' a n.zero_lt_succ

lemma eventually_norm_pow_le (a : α) : ∀ᶠ (n:ℕ) in at_top, ∥a ^ n∥ ≤ ∥a∥ ^ n :=
eventually_at_top.mpr ⟨1, λ b h, norm_pow_le' a (nat.succ_le_iff.mp h)⟩

/-- In a seminormed ring, the left-multiplication `add_monoid_hom` is bounded. -/
lemma mul_left_bound (x : α) :
  ∀ (y:α), ∥add_monoid_hom.mul_left x y∥ ≤ ∥x∥ * ∥y∥ :=
norm_mul_le x

/-- In a seminormed ring, the right-multiplication `add_monoid_hom` is bounded. -/
lemma mul_right_bound (x : α) :
  ∀ (y:α), ∥add_monoid_hom.mul_right x y∥ ≤ ∥x∥ * ∥y∥ :=
λ y, by {rw mul_comm, convert norm_mul_le y x}

/-- Seminormed ring structure on the product of two seminormed rings, using the sup norm. -/
instance prod.semi_normed_ring [semi_normed_ring β] : semi_normed_ring (α × β) :=
{ norm_mul := assume x y,
  calc
    ∥x * y∥ = ∥(x.1*y.1, x.2*y.2)∥ : rfl
        ... = (max ∥x.1*y.1∥  ∥x.2*y.2∥) : rfl
        ... ≤ (max (∥x.1∥*∥y.1∥) (∥x.2∥*∥y.2∥)) :
          max_le_max (norm_mul_le (x.1) (y.1)) (norm_mul_le (x.2) (y.2))
        ... = (max (∥x.1∥*∥y.1∥) (∥y.2∥*∥x.2∥)) : by simp[mul_comm]
        ... ≤ (max (∥x.1∥) (∥x.2∥)) * (max (∥y.2∥) (∥y.1∥)) :
          by apply max_mul_mul_le_max_mul_max; simp [norm_nonneg]
        ... = (max (∥x.1∥) (∥x.2∥)) * (max (∥y.1∥) (∥y.2∥)) : by simp [max_comm]
        ... = (∥x∥*∥y∥) : rfl,
  ..prod.semi_normed_group }

end semi_normed_ring

section normed_ring

variables [normed_ring α]

lemma units.norm_pos [nontrivial α] (x : units α) : 0 < ∥(x:α)∥ :=
norm_pos_iff.mpr (units.ne_zero x)

/-- Normed ring structure on the product of two normed rings, using the sup norm. -/
instance prod.normed_ring [normed_ring β] : normed_ring (α × β) :=
{ norm_mul := norm_mul_le,
  ..prod.semi_normed_group }

end normed_ring

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_ring_top_monoid [semi_normed_ring α] : has_continuous_mul α :=
⟨ continuous_iff_continuous_at.2 $ λ x, tendsto_iff_norm_tendsto_zero.2 $
    begin
      have : ∀ e : α × α, ∥e.1 * e.2 - x.1 * x.2∥ ≤ ∥e.1∥ * ∥e.2 - x.2∥ + ∥e.1 - x.1∥ * ∥x.2∥,
      { intro e,
        calc ∥e.1 * e.2 - x.1 * x.2∥ ≤ ∥e.1 * (e.2 - x.2) + (e.1 - x.1) * x.2∥ :
          by rw [mul_sub, sub_mul, sub_add_sub_cancel]
        ... ≤ ∥e.1∥ * ∥e.2 - x.2∥ + ∥e.1 - x.1∥ * ∥x.2∥ :
          norm_add_le_of_le (norm_mul_le _ _) (norm_mul_le _ _) },
      refine squeeze_zero (λ e, norm_nonneg _) this _,
      convert ((continuous_fst.tendsto x).norm.mul ((continuous_snd.tendsto x).sub
        tendsto_const_nhds).norm).add
        (((continuous_fst.tendsto x).sub tendsto_const_nhds).norm.mul _),
      show tendsto _ _ _, from tendsto_const_nhds,
      simp
    end ⟩

/-- A seminormed ring is a topological ring. -/
@[priority 100] -- see Note [lower instance priority]
instance semi_normed_top_ring [semi_normed_ring α] : topological_ring α := { }

/-- A normed field is a field with a norm satisfying ∥x y∥ = ∥x∥ ∥y∥. -/
class normed_field (α : Type*) extends has_norm α, field α, metric_space α :=
(dist_eq : ∀ x y, dist x y = norm (x - y))
(norm_mul' : ∀ a b, norm (a * b) = norm a * norm b)

/-- A nondiscrete normed field is a normed field in which there is an element of norm different from
`0` and `1`. This makes it possible to bring any element arbitrarily close to `0` by multiplication
by the powers of any element, and thus to relate algebra and topology. -/
class nondiscrete_normed_field (α : Type*) extends normed_field α :=
(non_trivial : ∃x:α, 1<∥x∥)

namespace normed_field

section normed_field

variables [normed_field α]

@[simp] lemma norm_mul (a b : α) : ∥a * b∥ = ∥a∥ * ∥b∥ :=
normed_field.norm_mul' a b

@[priority 100] -- see Note [lower instance priority]
instance to_normed_comm_ring : normed_comm_ring α :=
{ norm_mul := λ a b, (norm_mul a b).le, ..‹normed_field α› }

@[priority 900]
instance to_norm_one_class : norm_one_class α :=
⟨mul_left_cancel' (mt norm_eq_zero.1 (@one_ne_zero α _ _)) $
  by rw [← norm_mul, mul_one, mul_one]⟩

@[simp] lemma nnnorm_mul (a b : α) : ∥a * b∥₊ = ∥a∥₊ * ∥b∥₊ :=
nnreal.eq $ norm_mul a b

/-- `norm` as a `monoid_hom`. -/
@[simps] def norm_hom : monoid_with_zero_hom α ℝ := ⟨norm, norm_zero, norm_one, norm_mul⟩

/-- `nnnorm` as a `monoid_hom`. -/
@[simps] def nnnorm_hom : monoid_with_zero_hom α ℝ≥0 :=
⟨nnnorm, nnnorm_zero, nnnorm_one, nnnorm_mul⟩

@[simp] lemma norm_pow (a : α) : ∀ (n : ℕ), ∥a ^ n∥ = ∥a∥ ^ n :=
(norm_hom.to_monoid_hom : α →* ℝ).map_pow a

@[simp] lemma nnnorm_pow (a : α) (n : ℕ) : ∥a ^ n∥₊ = ∥a∥₊ ^ n :=
(nnnorm_hom.to_monoid_hom : α →* ℝ≥0).map_pow a n

@[simp] lemma norm_prod (s : finset β) (f : β → α) :
  ∥∏ b in s, f b∥ = ∏ b in s, ∥f b∥ :=
(norm_hom.to_monoid_hom : α →* ℝ).map_prod f s

@[simp] lemma nnnorm_prod (s : finset β) (f : β → α) :
  ∥∏ b in s, f b∥₊ = ∏ b in s, ∥f b∥₊ :=
(nnnorm_hom.to_monoid_hom : α →* ℝ≥0).map_prod f s

@[simp] lemma norm_div (a b : α) : ∥a / b∥ = ∥a∥ / ∥b∥ :=
(norm_hom : monoid_with_zero_hom α ℝ).map_div a b

@[simp] lemma nnnorm_div (a b : α) : ∥a / b∥₊ = ∥a∥₊ / ∥b∥₊ :=
(nnnorm_hom : monoid_with_zero_hom α ℝ≥0).map_div a b

@[simp] lemma norm_inv (a : α) : ∥a⁻¹∥ = ∥a∥⁻¹ :=
(norm_hom : monoid_with_zero_hom α ℝ).map_inv' a

@[simp] lemma nnnorm_inv (a : α) : ∥a⁻¹∥₊ = ∥a∥₊⁻¹ :=
nnreal.eq $ by simp

@[simp] lemma norm_fpow : ∀ (a : α) (n : ℤ), ∥a^n∥ = ∥a∥^n :=
(norm_hom : monoid_with_zero_hom α ℝ).map_fpow

@[simp] lemma nnnorm_fpow : ∀ (a : α) (n : ℤ), ∥a ^ n∥₊ = ∥a∥₊ ^ n :=
(nnnorm_hom : monoid_with_zero_hom α ℝ≥0).map_fpow

@[priority 100] -- see Note [lower instance priority]
instance : has_continuous_inv' α :=
begin
  refine ⟨λ r r0, tendsto_iff_norm_tendsto_zero.2 _⟩,
  have r0' : 0 < ∥r∥ := norm_pos_iff.2 r0,
  rcases exists_between r0' with ⟨ε, ε0, εr⟩,
  have : ∀ᶠ e in 𝓝 r, ∥e⁻¹ - r⁻¹∥ ≤ ∥r - e∥ / ∥r∥ / ε,
  { filter_upwards [(is_open_lt continuous_const continuous_norm).eventually_mem εr],
    intros e he,
    have e0 : e ≠ 0 := norm_pos_iff.1 (ε0.trans he),
    calc ∥e⁻¹ - r⁻¹∥ = ∥r - e∥ / ∥r∥ / ∥e∥ : by field_simp [mul_comm]
    ... ≤ ∥r - e∥ / ∥r∥ / ε :
      div_le_div_of_le_left (div_nonneg (norm_nonneg _) (norm_nonneg _)) ε0 he.le },
  refine squeeze_zero' (eventually_of_forall $ λ _, norm_nonneg _) this _,
  refine (continuous_const.sub continuous_id).norm.div_const.div_const.tendsto' _ _ _,
  simp
end

end normed_field

variables (α) [nondiscrete_normed_field α]

lemma exists_one_lt_norm : ∃x : α, 1 < ∥x∥ := ‹nondiscrete_normed_field α›.non_trivial

lemma exists_norm_lt_one : ∃x : α, 0 < ∥x∥ ∧ ∥x∥ < 1 :=
begin
  rcases exists_one_lt_norm α with ⟨y, hy⟩,
  refine ⟨y⁻¹, _, _⟩,
  { simp only [inv_eq_zero, ne.def, norm_pos_iff],
    rintro rfl,
    rw norm_zero at hy,
    exact lt_asymm zero_lt_one hy },
  { simp [inv_lt_one hy] }
end

lemma exists_lt_norm (r : ℝ) : ∃ x : α, r < ∥x∥ :=
let ⟨w, hw⟩ := exists_one_lt_norm α in
let ⟨n, hn⟩ := pow_unbounded_of_one_lt r hw in
⟨w^n, by rwa norm_pow⟩

lemma exists_norm_lt {r : ℝ} (hr : 0 < r) : ∃ x : α, 0 < ∥x∥ ∧ ∥x∥ < r :=
let ⟨w, hw⟩ := exists_one_lt_norm α in
let ⟨n, hle, hlt⟩ := exists_int_pow_near' hr hw in
⟨w^n, by { rw norm_fpow; exact fpow_pos_of_pos (lt_trans zero_lt_one hw) _},
by rwa norm_fpow⟩

variable {α}

@[instance]
lemma punctured_nhds_ne_bot (x : α) : ne_bot (𝓝[{x}ᶜ] x) :=
begin
  rw [← mem_closure_iff_nhds_within_ne_bot, metric.mem_closure_iff],
  rintros ε ε0,
  rcases normed_field.exists_norm_lt α ε0 with ⟨b, hb0, hbε⟩,
  refine ⟨x + b, mt (set.mem_singleton_iff.trans add_right_eq_self).1 $ norm_pos_iff.1 hb0, _⟩,
  rwa [dist_comm, dist_eq_norm, add_sub_cancel'],
end

@[instance]
lemma nhds_within_is_unit_ne_bot : ne_bot (𝓝[{x : α | is_unit x}] 0) :=
by simpa only [is_unit_iff_ne_zero] using punctured_nhds_ne_bot (0:α)

end normed_field

instance : normed_field ℝ :=
{ norm_mul' := abs_mul,
  .. real.normed_group }

instance : nondiscrete_normed_field ℝ :=
{ non_trivial := ⟨2, by { unfold norm, rw abs_of_nonneg; norm_num }⟩ }

namespace real

lemma norm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ∥x∥ = x :=
abs_of_nonneg hx

lemma norm_of_nonpos {x : ℝ} (hx : x ≤ 0) : ∥x∥ = -x :=
abs_of_nonpos hx

@[simp] lemma norm_coe_nat (n : ℕ) : ∥(n : ℝ)∥ = n := abs_of_nonneg n.cast_nonneg

@[simp] lemma nnnorm_coe_nat (n : ℕ) : ∥(n : ℝ)∥₊ = n := nnreal.eq $ by simp

@[simp] lemma norm_two : ∥(2 : ℝ)∥ = 2 := abs_of_pos (@zero_lt_two ℝ _ _)

@[simp] lemma nnnorm_two : ∥(2 : ℝ)∥₊ = 2 := nnreal.eq $ by simp

lemma nnnorm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : ∥x∥₊ = ⟨x, hx⟩ :=
nnreal.eq $ norm_of_nonneg hx

lemma ennnorm_eq_of_real {x : ℝ} (hx : 0 ≤ x) : (∥x∥₊ : ℝ≥0∞) = ennreal.of_real x :=
by { rw [← of_real_norm_eq_coe_nnnorm, norm_of_nonneg hx] }

/-- If `E` is a nontrivial topological module over `ℝ`, then `E` has no isolated points.
This is a particular case of `module.punctured_nhds_ne_bot`. -/
instance punctured_nhds_module_ne_bot
  {E : Type*} [add_comm_group E] [topological_space E] [has_continuous_add E] [nontrivial E]
  [module ℝ E] [has_continuous_smul ℝ E] (x : E) :
  ne_bot (𝓝[{x}ᶜ] x) :=
module.punctured_nhds_ne_bot ℝ E x

end real

namespace nnreal

open_locale nnreal

@[simp] lemma norm_eq (x : ℝ≥0) : ∥(x : ℝ)∥ = x :=
by rw [real.norm_eq_abs, x.abs_eq]

@[simp] lemma nnnorm_eq (x : ℝ≥0) : ∥(x : ℝ)∥₊ = x :=
nnreal.eq $ real.norm_of_nonneg x.2

end nnreal

@[simp] lemma norm_norm [semi_normed_group α] (x : α) : ∥∥x∥∥ = ∥x∥ :=
real.norm_of_nonneg (norm_nonneg _)

@[simp] lemma nnnorm_norm [semi_normed_group α] (a : α) : ∥∥a∥∥₊ = ∥a∥₊ :=
by simpa [real.nnnorm_of_nonneg (norm_nonneg a)]

/-- A restatement of `metric_space.tendsto_at_top` in terms of the norm. -/
lemma normed_group.tendsto_at_top [nonempty α] [semilattice_sup α] {β : Type*} [semi_normed_group β]
  {f : α → β} {b : β} :
  tendsto f at_top (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N ≤ n → ∥f n - b∥ < ε :=
(at_top_basis.tendsto_iff metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

/--
A variant of `normed_group.tendsto_at_top` that
uses `∃ N, ∀ n > N, ...` rather than `∃ N, ∀ n ≥ N, ...`
-/
lemma normed_group.tendsto_at_top' [nonempty α] [semilattice_sup α] [no_top_order α]
  {β : Type*} [semi_normed_group β]
  {f : α → β} {b : β} :
  tendsto f at_top (𝓝 b) ↔ ∀ ε, 0 < ε → ∃ N, ∀ n, N < n → ∥f n - b∥ < ε :=
(at_top_basis_Ioi.tendsto_iff metric.nhds_basis_ball).trans (by simp [dist_eq_norm])

instance : normed_comm_ring ℤ :=
{ norm := λ n, ∥(n : ℝ)∥,
  norm_mul := λ m n, le_of_eq $ by simp only [norm, int.cast_mul, abs_mul],
  dist_eq := λ m n, by simp only [int.dist_eq, norm, int.cast_sub],
  mul_comm := mul_comm }

@[norm_cast] lemma int.norm_cast_real (m : ℤ) : ∥(m : ℝ)∥ = ∥m∥ := rfl

lemma int.norm_eq_abs (n : ℤ) : ∥n∥ = abs n := rfl

lemma nnreal.coe_nat_abs (n : ℤ) : (n.nat_abs : ℝ≥0) = ∥n∥₊ :=
nnreal.eq $ calc ((n.nat_abs : ℝ≥0) : ℝ)
               = (n.nat_abs : ℤ) : by simp only [int.cast_coe_nat, nnreal.coe_nat_cast]
           ... = abs n           : by simp only [← int.abs_eq_nat_abs, int.cast_abs]
           ... = ∥n∥              : rfl

instance : norm_one_class ℤ :=
⟨by simp [← int.norm_cast_real]⟩

instance : normed_field ℚ :=
{ norm := λ r, ∥(r : ℝ)∥,
  norm_mul' := λ r₁ r₂, by simp only [norm, rat.cast_mul, abs_mul],
  dist_eq := λ r₁ r₂, by simp only [rat.dist_eq, norm, rat.cast_sub] }

instance : nondiscrete_normed_field ℚ :=
{ non_trivial := ⟨2, by { unfold norm, rw abs_of_nonneg; norm_num }⟩ }

@[norm_cast, simp] lemma rat.norm_cast_real (r : ℚ) : ∥(r : ℝ)∥ = ∥r∥ := rfl

@[norm_cast, simp] lemma int.norm_cast_rat (m : ℤ) : ∥(m : ℚ)∥ = ∥m∥ :=
by rw [← rat.norm_cast_real, ← int.norm_cast_real]; congr' 1; norm_cast

-- Now that we've installed the norm on `ℤ`,
-- we can state some lemmas about `nsmul` and `gsmul`.
section
variables [semi_normed_group α]

lemma norm_nsmul_le (n : ℕ) (a : α) : ∥n • a∥ ≤ n * ∥a∥ :=
begin
  induction n with n ih,
  { simp only [norm_zero, nat.cast_zero, zero_mul, zero_smul] },
  simp only [nat.succ_eq_add_one, add_smul, add_mul, one_mul, nat.cast_add,
    nat.cast_one, one_nsmul],
  exact norm_add_le_of_le ih le_rfl
end

lemma norm_gsmul_le (n : ℤ) (a : α) : ∥n • a∥ ≤ ∥n∥ * ∥a∥ :=
begin
  induction n with n n,
  { simp only [int.of_nat_eq_coe, gsmul_coe_nat],
    convert norm_nsmul_le n a,
    exact nat.abs_cast n },
  { simp only [int.neg_succ_of_nat_coe, neg_smul, norm_neg, gsmul_coe_nat],
    convert norm_nsmul_le n.succ a,
    exact nat.abs_cast n.succ, }
end

lemma nnnorm_nsmul_le (n : ℕ) (a : α) : ∥n • a∥₊ ≤ n * ∥a∥₊ :=
by simpa only [←nnreal.coe_le_coe, nnreal.coe_mul, nnreal.coe_nat_cast]
  using norm_nsmul_le n a

lemma nnnorm_gsmul_le (n : ℤ) (a : α) : ∥n • a∥₊ ≤ ∥n∥₊ * ∥a∥₊ :=
by simpa only [←nnreal.coe_le_coe, nnreal.coe_mul] using norm_gsmul_le n a

end

section semi_normed_space

section prio
set_option extends_priority 920
-- Here, we set a rather high priority for the instance `[semi_normed_space α β] : module α β`
-- to take precedence over `semiring.to_module` as this leads to instance paths with better
-- unification properties.
/-- A seminormed space over a normed field is a vector space endowed with a seminorm which satisfies
the equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`. -/
class semi_normed_space (α : Type*) (β : Type*) [normed_field α] [semi_normed_group β]
  extends module α β :=
(norm_smul_le : ∀ (a:α) (b:β), ∥a • b∥ ≤ ∥a∥ * ∥b∥)

set_option extends_priority 920
-- Here, we set a rather high priority for the instance `[normed_space α β] : module α β`
-- to take precedence over `semiring.to_module` as this leads to instance paths with better
-- unification properties.
/-- A normed space over a normed field is a vector space endowed with a norm which satisfies the
equality `∥c • x∥ = ∥c∥ ∥x∥`. We require only `∥c • x∥ ≤ ∥c∥ ∥x∥` in the definition, then prove
`∥c • x∥ = ∥c∥ ∥x∥` in `norm_smul`. -/
class normed_space (α : Type*) (β : Type*) [normed_field α] [normed_group β]
  extends module α β :=
(norm_smul_le : ∀ (a:α) (b:β), ∥a • b∥ ≤ ∥a∥ * ∥b∥)

/-- A normed space is a seminormed space. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_space.to_semi_normed_space [normed_field α] [normed_group β]
  [γ : normed_space α β] : semi_normed_space α β := { ..γ }

end prio

variables [normed_field α] [semi_normed_group β]

@[priority 100] -- see Note [lower instance priority]
instance semi_normed_space.has_bounded_smul [semi_normed_space α β] : has_bounded_smul α β :=
{ dist_smul_pair' := λ x y₁ y₂,
    by simpa [dist_eq_norm, smul_sub] using semi_normed_space.norm_smul_le x (y₁ - y₂),
  dist_pair_smul' := λ x₁ x₂ y,
    by simpa [dist_eq_norm, sub_smul] using semi_normed_space.norm_smul_le (x₁ - x₂) y }

instance normed_field.to_normed_space : normed_space α α :=
{ norm_smul_le := λ a b, le_of_eq (normed_field.norm_mul a b) }

lemma norm_smul [semi_normed_space α β] (s : α) (x : β) : ∥s • x∥ = ∥s∥ * ∥x∥ :=
begin
  by_cases h : s = 0,
  { simp [h] },
  { refine le_antisymm (semi_normed_space.norm_smul_le s x) _,
    calc ∥s∥ * ∥x∥ = ∥s∥ * ∥s⁻¹ • s • x∥     : by rw [inv_smul_smul' h]
               ... ≤ ∥s∥ * (∥s⁻¹∥ * ∥s • x∥) :
      mul_le_mul_of_nonneg_left (semi_normed_space.norm_smul_le _ _) (norm_nonneg _)
               ... = ∥s • x∥                 :
      by rw [normed_field.norm_inv, ← mul_assoc, mul_inv_cancel (mt norm_eq_zero.1 h), one_mul] }
end

@[simp] lemma abs_norm_eq_norm (z : β) : abs ∥z∥ = ∥z∥ :=
  (abs_eq (norm_nonneg z)).mpr (or.inl rfl)

lemma dist_smul [semi_normed_space α β] (s : α) (x y : β) : dist (s • x) (s • y) = ∥s∥ * dist x y :=
by simp only [dist_eq_norm, (norm_smul _ _).symm, smul_sub]

lemma nnnorm_smul [semi_normed_space α β] (s : α) (x : β) : ∥s • x∥₊ = ∥s∥₊ * ∥x∥₊ :=
nnreal.eq $ norm_smul s x

lemma nndist_smul [semi_normed_space α β] (s : α) (x y : β) :
  nndist (s • x) (s • y) = ∥s∥₊ * nndist x y :=
nnreal.eq $ dist_smul s x y

lemma norm_smul_of_nonneg [semi_normed_space ℝ β] {t : ℝ} (ht : 0 ≤ t) (x : β) :
  ∥t • x∥ = t * ∥x∥ := by rw [norm_smul, real.norm_eq_abs, abs_of_nonneg ht]

variables {E : Type*} [semi_normed_group E] [semi_normed_space α E]
variables {F : Type*} [semi_normed_group F] [semi_normed_space α F]

theorem eventually_nhds_norm_smul_sub_lt (c : α) (x : E) {ε : ℝ} (h : 0 < ε) :
  ∀ᶠ y in 𝓝 x, ∥c • (y - x)∥ < ε :=
have tendsto (λ y, ∥c • (y - x)∥) (𝓝 x) (𝓝 0),
  from (continuous_const.smul (continuous_id.sub continuous_const)).norm.tendsto' _ _ (by simp),
this.eventually (gt_mem_nhds h)

theorem closure_ball [semi_normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
  closure (ball x r) = closed_ball x r :=
begin
  refine set.subset.antisymm closure_ball_subset_closed_ball (λ y hy, _),
  have : continuous_within_at (λ c : ℝ, c • (y - x) + x) (set.Ico 0 1) 1 :=
    ((continuous_id.smul continuous_const).add continuous_const).continuous_within_at,
  convert this.mem_closure _ _,
  { rw [one_smul, sub_add_cancel] },
  { simp [closure_Ico (@zero_lt_one ℝ _ _), zero_le_one] },
  { rintros c ⟨hc0, hc1⟩,
    rw [set.mem_preimage, mem_ball, dist_eq_norm, add_sub_cancel, norm_smul, real.norm_eq_abs,
      abs_of_nonneg hc0, mul_comm, ← mul_one r],
    rw [mem_closed_ball, dist_eq_norm] at hy,
    apply mul_lt_mul'; assumption }
end

theorem frontier_ball [semi_normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
  frontier (ball x r) = sphere x r :=
begin
  rw [frontier, closure_ball x hr, is_open_ball.interior_eq],
  ext x, exact (@eq_iff_le_not_lt ℝ _ _ _).symm
end

theorem interior_closed_ball [semi_normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
  interior (closed_ball x r) = ball x r :=
begin
  refine set.subset.antisymm _ ball_subset_interior_closed_ball,
  intros y hy,
  rcases le_iff_lt_or_eq.1 (mem_closed_ball.1 $ interior_subset hy) with hr|rfl, { exact hr },
  set f : ℝ → E := λ c : ℝ, c • (y - x) + x,
  suffices : f ⁻¹' closed_ball x (dist y x) ⊆ set.Icc (-1) 1,
  { have hfc : continuous f := (continuous_id.smul continuous_const).add continuous_const,
    have hf1 : (1:ℝ) ∈ f ⁻¹' (interior (closed_ball x $ dist y x)), by simpa [f],
    have h1 : (1:ℝ) ∈ interior (set.Icc (-1:ℝ) 1) :=
      interior_mono this (preimage_interior_subset_interior_preimage hfc hf1),
    contrapose h1,
    simp },
  intros c hc,
  rw [set.mem_Icc, ← abs_le, ← real.norm_eq_abs, ← mul_le_mul_right hr],
  simpa [f, dist_eq_norm, norm_smul] using hc
end

theorem frontier_closed_ball [semi_normed_space ℝ E] (x : E) {r : ℝ} (hr : 0 < r) :
  frontier (closed_ball x r) = sphere x r :=
by rw [frontier, closure_closed_ball, interior_closed_ball x hr,
  closed_ball_diff_ball]

variables (α)

lemma ne_neg_of_mem_sphere [char_zero α] {r : ℝ} (hr : 0 < r) (x : sphere (0:E) r) : x ≠ - x :=
λ h, nonzero_of_mem_sphere hr x (eq_zero_of_eq_neg α (by { conv_lhs {rw h}, simp }))

lemma ne_neg_of_mem_unit_sphere [char_zero α] (x : sphere (0:E) 1) : x ≠ - x :=
ne_neg_of_mem_sphere α  (by norm_num) x

variables {α}

open normed_field

/-- The product of two seminormed spaces is a seminormed space, with the sup norm. -/
instance prod.semi_normed_space : semi_normed_space α (E × F) :=
{ norm_smul_le := λ s x, le_of_eq $ by simp [prod.semi_norm_def, norm_smul, mul_max_of_nonneg],
  ..prod.normed_group,
  ..prod.module }

/-- The product of finitely many seminormed spaces is a seminormed space, with the sup norm. -/
instance pi.semi_normed_space {E : ι → Type*} [fintype ι] [∀i, semi_normed_group (E i)]
  [∀i, semi_normed_space α (E i)] : semi_normed_space α (Πi, E i) :=
{ norm_smul_le := λ a f, le_of_eq $
    show (↑(finset.sup finset.univ (λ (b : ι), ∥a • f b∥₊)) : ℝ) =
      ∥a∥₊ * ↑(finset.sup finset.univ (λ (b : ι), ∥f b∥₊)),
    by simp only [(nnreal.coe_mul _ _).symm, nnreal.mul_finset_sup, nnnorm_smul] }

/-- A subspace of a seminormed space is also a normed space, with the restriction of the norm. -/
instance submodule.semi_normed_space {𝕜 R : Type*} [has_scalar 𝕜 R] [normed_field 𝕜] [ring R]
  {E : Type*} [semi_normed_group E] [semi_normed_space 𝕜 E] [module R E]
  [is_scalar_tower 𝕜 R E] (s : submodule R E) :
  semi_normed_space 𝕜 s :=
{ norm_smul_le := λc x, le_of_eq $ norm_smul c (x : E) }

/-- If there is a scalar `c` with `∥c∥>1`, then any element of with norm different from `0` can be
moved by scalar multiplication to any shell of width `∥c∥`. Also recap information on the norm of
the rescaling element that shows up in applications. -/
lemma rescale_to_shell_semi_normed {c : α} (hc : 1 < ∥c∥) {ε : ℝ} (εpos : 0 < ε) {x : E}
  (hx : ∥x∥ ≠ 0) : ∃d:α, d ≠ 0 ∧ ∥d • x∥ < ε ∧ (ε/∥c∥ ≤ ∥d • x∥) ∧ (∥d∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥) :=
begin
  have xεpos : 0 < ∥x∥/ε := div_pos ((ne.symm hx).le_iff_lt.1 (norm_nonneg x)) εpos,
  rcases exists_int_pow_near xεpos hc with ⟨n, hn⟩,
  have cpos : 0 < ∥c∥ := lt_trans (zero_lt_one : (0 :ℝ) < 1) hc,
  have cnpos : 0 < ∥c^(n+1)∥ := by { rw norm_fpow, exact lt_trans xεpos hn.2 },
  refine ⟨(c^(n+1))⁻¹, _, _, _, _⟩,
  show (c ^ (n + 1))⁻¹  ≠ 0,
    by rwa [ne.def, inv_eq_zero, ← ne.def, ← norm_pos_iff],
  show ∥(c ^ (n + 1))⁻¹ • x∥ < ε,
  { rw [norm_smul, norm_inv, ← div_eq_inv_mul, div_lt_iff cnpos, mul_comm, norm_fpow],
    exact (div_lt_iff εpos).1 (hn.2) },
  show ε / ∥c∥ ≤ ∥(c ^ (n + 1))⁻¹ • x∥,
  { rw [div_le_iff cpos, norm_smul, norm_inv, norm_fpow, fpow_add (ne_of_gt cpos),
        gpow_one, mul_inv_rev', mul_comm, ← mul_assoc, ← mul_assoc, mul_inv_cancel (ne_of_gt cpos),
        one_mul, ← div_eq_inv_mul, le_div_iff (fpow_pos_of_pos cpos _), mul_comm],
    exact (le_div_iff εpos).1 hn.1 },
  show ∥(c ^ (n + 1))⁻¹∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥,
  { have : ε⁻¹ * ∥c∥ * ∥x∥ = ε⁻¹ * ∥x∥ * ∥c∥, by ring,
    rw [norm_inv, inv_inv', norm_fpow, fpow_add (ne_of_gt cpos), gpow_one, this, ← div_eq_inv_mul],
    exact mul_le_mul_of_nonneg_right hn.1 (norm_nonneg _) }
end

end semi_normed_space

section normed_space

variables [normed_field α]
variables {E : Type*} [normed_group E] [normed_space α E]
variables {F : Type*} [normed_group F] [normed_space α F]

open normed_field

theorem interior_closed_ball' [normed_space ℝ E] [nontrivial E] (x : E) (r : ℝ) :
  interior (closed_ball x r) = ball x r :=
begin
  rcases lt_trichotomy r 0 with hr|rfl|hr,
  { simp [closed_ball_eq_empty.2 hr, ball_eq_empty.2 hr.le] },
  { rw [closed_ball_zero, ball_zero, interior_singleton] },
  { exact interior_closed_ball x hr }
end

theorem frontier_closed_ball' [normed_space ℝ E] [nontrivial E] (x : E) (r : ℝ) :
  frontier (closed_ball x r) = sphere x r :=
by rw [frontier, closure_closed_ball, interior_closed_ball' x r, closed_ball_diff_ball]

variables {α}

/-- If there is a scalar `c` with `∥c∥>1`, then any element can be moved by scalar multiplication to
any shell of width `∥c∥`. Also recap information on the norm of the rescaling element that shows
up in applications. -/
lemma rescale_to_shell {c : α} (hc : 1 < ∥c∥) {ε : ℝ} (εpos : 0 < ε) {x : E} (hx : x ≠ 0) :
  ∃d:α, d ≠ 0 ∧ ∥d • x∥ < ε ∧ (ε/∥c∥ ≤ ∥d • x∥) ∧ (∥d∥⁻¹ ≤ ε⁻¹ * ∥c∥ * ∥x∥) :=
rescale_to_shell_semi_normed hc εpos (ne_of_lt (norm_pos_iff.2 hx)).symm

/-- The product of two normed spaces is a normed space, with the sup norm. -/
instance : normed_space α (E × F) := { ..prod.semi_normed_space }

/-- The product of finitely many normed spaces is a normed space, with the sup norm. -/
instance pi.normed_space {E : ι → Type*} [fintype ι] [∀i, normed_group (E i)]
  [∀i, normed_space α (E i)] : normed_space α (Πi, E i) :=
{ ..pi.semi_normed_space }

/-- A subspace of a normed space is also a normed space, with the restriction of the norm. -/
instance submodule.normed_space {𝕜 R : Type*} [has_scalar 𝕜 R] [normed_field 𝕜] [ring R]
  {E : Type*} [normed_group E] [normed_space 𝕜 E] [module R E]
  [is_scalar_tower 𝕜 R E] (s : submodule R E) :
  normed_space 𝕜 s :=
{ ..submodule.semi_normed_space s }

end normed_space

section normed_algebra

/-- A seminormed algebra `𝕜'` over `𝕜` is an algebra endowed with a seminorm for which the
embedding of `𝕜` in `𝕜'` is an isometry. -/
class semi_normed_algebra (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [semi_normed_ring 𝕜']
  extends algebra 𝕜 𝕜' :=
(norm_algebra_map_eq : ∀x:𝕜, ∥algebra_map 𝕜 𝕜' x∥ = ∥x∥)

/-- A normed algebra `𝕜'` over `𝕜` is an algebra endowed with a norm for which the embedding of
`𝕜` in `𝕜'` is an isometry. -/
class normed_algebra (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [normed_ring 𝕜']
  extends algebra 𝕜 𝕜' :=
(norm_algebra_map_eq : ∀x:𝕜, ∥algebra_map 𝕜 𝕜' x∥ = ∥x∥)

/-- A normed algebra is a seminormed algebra. -/
@[priority 100] -- see Note [lower instance priority]
instance normed_algebra.to_semi_normed_algebra (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜]
  [normed_ring 𝕜'] [normed_algebra 𝕜 𝕜'] : semi_normed_algebra 𝕜 𝕜' :=
{ norm_algebra_map_eq := normed_algebra.norm_algebra_map_eq }

@[simp] lemma norm_algebra_map_eq {𝕜 : Type*} (𝕜' : Type*) [normed_field 𝕜] [semi_normed_ring 𝕜']
  [h : semi_normed_algebra 𝕜 𝕜'] (x : 𝕜) : ∥algebra_map 𝕜 𝕜' x∥ = ∥x∥ :=
semi_normed_algebra.norm_algebra_map_eq _

/-- In a normed algebra, the inclusion of the base field in the extended field is an isometry. -/
lemma algebra_map_isometry (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [semi_normed_ring 𝕜']
  [semi_normed_algebra 𝕜 𝕜'] : isometry (algebra_map 𝕜 𝕜') :=
begin
  refine isometry_emetric_iff_metric.2 (λx y, _),
  rw [dist_eq_norm, dist_eq_norm, ← ring_hom.map_sub, norm_algebra_map_eq],
end

variables (𝕜 : Type*) [normed_field 𝕜]
variables (𝕜' : Type*) [semi_normed_ring 𝕜']

@[priority 100]
instance semi_normed_algebra.to_semi_normed_space [h : semi_normed_algebra 𝕜 𝕜'] :
  semi_normed_space 𝕜 𝕜' :=
{ norm_smul_le := λ s x, calc
    ∥s • x∥ = ∥((algebra_map 𝕜 𝕜') s) * x∥ : by { rw h.smul_def', refl }
    ... ≤ ∥algebra_map 𝕜 𝕜' s∥ * ∥x∥ : semi_normed_ring.norm_mul _ _
    ... = ∥s∥ * ∥x∥ : by rw norm_algebra_map_eq,
  ..h }

/-- While this may appear identical to `semi_normed_algebra.to_semi_normed_space`, it contains an
implicit argument involving `normed_ring.to_semi_normed_ring` that typeclass inference has trouble
inferring.

Specifically, the following instance cannot be found without this
`semi_normed_algebra.to_semi_normed_space'`:
```lean
example
  (𝕜 ι : Type*) (E : ι → Type*)
  [normed_field 𝕜] [Π i, normed_ring (E i)] [Π i, normed_algebra 𝕜 (E i)] :
  Π i, module 𝕜 (E i) := by apply_instance
```

See `semi_normed_space.to_module'` for a similar situation. -/
@[priority 100]
instance semi_normed_algebra.to_semi_normed_space' (𝕜 : Type*) [normed_field 𝕜] (𝕜' : Type*)
  [normed_ring 𝕜'] [semi_normed_algebra 𝕜 𝕜'] :
  semi_normed_space 𝕜 𝕜' := by apply_instance

@[priority 100]
instance normed_algebra.to_normed_space (𝕜 : Type*) [normed_field 𝕜] (𝕜' : Type*)
  [normed_ring 𝕜'] [h : normed_algebra 𝕜 𝕜'] : normed_space 𝕜 𝕜' :=
{ norm_smul_le := semi_normed_space.norm_smul_le,
  ..h }

instance normed_algebra.id : normed_algebra 𝕜 𝕜 :=
{ norm_algebra_map_eq := by simp,
.. algebra.id 𝕜}

variables (𝕜') [semi_normed_algebra 𝕜 𝕜']
include 𝕜

lemma normed_algebra.norm_one : ∥(1:𝕜')∥ = 1 :=
by simpa using (norm_algebra_map_eq 𝕜' (1:𝕜))

lemma normed_algebra.norm_one_class : norm_one_class 𝕜' :=
⟨normed_algebra.norm_one 𝕜 𝕜'⟩

lemma normed_algebra.zero_ne_one : (0:𝕜') ≠ 1 :=
begin
  refine (ne_zero_of_norm_pos _).symm,
  rw normed_algebra.norm_one 𝕜 𝕜', norm_num,
end

lemma normed_algebra.nontrivial : nontrivial 𝕜' :=
⟨⟨0, 1, normed_algebra.zero_ne_one 𝕜 𝕜'⟩⟩

end normed_algebra

section restrict_scalars

variables (𝕜 : Type*) (𝕜' : Type*) [normed_field 𝕜] [normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
(E : Type*) [normed_group E] [normed_space 𝕜' E]
(F : Type*) [semi_normed_group F] [semi_normed_space 𝕜' F]

/-- Warning: This declaration should be used judiciously.
Please consider using `is_scalar_tower` instead.

`𝕜`-seminormed space structure induced by a `𝕜'`-seminormed space structure when `𝕜'` is a
seminormed algebra over `𝕜`. Not registered as an instance as `𝕜'` can not be inferred.

The type synonym `module.restrict_scalars 𝕜 𝕜' E` will be endowed with this instance by default.
-/
def semi_normed_space.restrict_scalars : semi_normed_space 𝕜 F :=
{ norm_smul_le := λc x, le_of_eq $ begin
    change ∥(algebra_map 𝕜 𝕜' c) • x∥ = ∥c∥ * ∥x∥,
    simp [norm_smul]
  end,
  ..restrict_scalars.module 𝕜 𝕜' F }

/-- Warning: This declaration should be used judiciously.
Please consider using `is_scalar_tower` instead.

`𝕜`-normed space structure induced by a `𝕜'`-normed space structure when `𝕜'` is a
normed algebra over `𝕜`. Not registered as an instance as `𝕜'` can not be inferred.

The type synonym `restrict_scalars 𝕜 𝕜' E` will be endowed with this instance by default.
-/
def normed_space.restrict_scalars : normed_space 𝕜 E :=
{ norm_smul_le := λc x, le_of_eq $ begin
    change ∥(algebra_map 𝕜 𝕜' c) • x∥ = ∥c∥ * ∥x∥,
    simp [norm_smul]
  end,
  ..restrict_scalars.module 𝕜 𝕜' E }

instance {𝕜 : Type*} {𝕜' : Type*} {F : Type*} [I : semi_normed_group F] :
  semi_normed_group (restrict_scalars 𝕜 𝕜' F) := I

instance {𝕜 : Type*} {𝕜' : Type*} {E : Type*} [I : normed_group E] :
  normed_group (restrict_scalars 𝕜 𝕜' E) := I

instance module.restrict_scalars.semi_normed_space_orig {𝕜 : Type*} {𝕜' : Type*} {F : Type*}
  [normed_field 𝕜'] [semi_normed_group F] [I : semi_normed_space 𝕜' F] :
  semi_normed_space 𝕜' (restrict_scalars 𝕜 𝕜' F) := I

instance module.restrict_scalars.normed_space_orig {𝕜 : Type*} {𝕜' : Type*} {E : Type*}
  [normed_field 𝕜'] [normed_group E] [I : normed_space 𝕜' E] :
  normed_space 𝕜' (restrict_scalars 𝕜 𝕜' E) := I

instance : semi_normed_space 𝕜 (restrict_scalars 𝕜 𝕜' F) :=
(semi_normed_space.restrict_scalars 𝕜 𝕜' F : semi_normed_space 𝕜 F)

instance : normed_space 𝕜 (restrict_scalars 𝕜 𝕜' E) :=
(normed_space.restrict_scalars 𝕜 𝕜' E : normed_space 𝕜 E)

end restrict_scalars

section summable
open_locale classical
open finset filter
variables [semi_normed_group α] [semi_normed_group β]

lemma cauchy_seq_finset_iff_vanishing_norm {f : ι → α} :
  cauchy_seq (λ s : finset ι, ∑ i in s, f i) ↔
    ∀ε > (0 : ℝ), ∃s:finset ι, ∀t, disjoint t s → ∥ ∑ i in t, f i ∥ < ε :=
begin
  rw [cauchy_seq_finset_iff_vanishing, nhds_basis_ball.forall_iff],
  { simp only [ball_0_eq, set.mem_set_of_eq] },
  { rintros s t hst ⟨s', hs'⟩,
    exact ⟨s', λ t' ht', hst $ hs' _ ht'⟩ }
end

lemma summable_iff_vanishing_norm [complete_space α] {f : ι → α} :
  summable f ↔ ∀ε > (0 : ℝ), ∃s:finset ι, ∀t, disjoint t s → ∥ ∑ i in t, f i ∥ < ε :=
by rw [summable_iff_cauchy_seq_finset, cauchy_seq_finset_iff_vanishing_norm]

lemma cauchy_seq_finset_of_norm_bounded {f : ι → α} (g : ι → ℝ) (hg : summable g)
  (h : ∀i, ∥f i∥ ≤ g i) : cauchy_seq (λ s : finset ι, ∑ i in s, f i) :=
cauchy_seq_finset_iff_vanishing_norm.2 $ assume ε hε,
  let ⟨s, hs⟩ := summable_iff_vanishing_norm.1 hg ε hε in
  ⟨s, assume t ht,
    have ∥∑ i in t, g i∥ < ε := hs t ht,
    have nn : 0 ≤ ∑ i in t, g i := finset.sum_nonneg (assume a _, le_trans (norm_nonneg _) (h a)),
    lt_of_le_of_lt (norm_sum_le_of_le t (λ i _, h i)) $
      by rwa [real.norm_eq_abs, abs_of_nonneg nn] at this⟩

lemma cauchy_seq_finset_of_summable_norm {f : ι → α} (hf : summable (λa, ∥f a∥)) :
  cauchy_seq (λ s : finset ι, ∑ a in s, f a) :=
cauchy_seq_finset_of_norm_bounded _ hf (assume i, le_refl _)

/-- If a function `f` is summable in norm, and along some sequence of finsets exhausting the space
its sum is converging to a limit `a`, then this holds along all finsets, i.e., `f` is summable
with sum `a`. -/
lemma has_sum_of_subseq_of_summable {f : ι → α} (hf : summable (λa, ∥f a∥))
  {s : γ → finset ι} {p : filter γ} [ne_bot p]
  (hs : tendsto s p at_top) {a : α} (ha : tendsto (λ b, ∑ i in s b, f i) p (𝓝 a)) :
  has_sum f a :=
tendsto_nhds_of_cauchy_seq_of_subseq (cauchy_seq_finset_of_summable_norm hf) hs ha

lemma has_sum_iff_tendsto_nat_of_summable_norm {f : ℕ → α} {a : α} (hf : summable (λi, ∥f i∥)) :
  has_sum f a ↔ tendsto (λn:ℕ, ∑ i in range n, f i) at_top (𝓝 a) :=
⟨λ h, h.tendsto_sum_nat,
λ h, has_sum_of_subseq_of_summable hf tendsto_finset_range h⟩

/-- The direct comparison test for series:  if the norm of `f` is bounded by a real function `g`
which is summable, then `f` is summable. -/
lemma summable_of_norm_bounded
  [complete_space α] {f : ι → α} (g : ι → ℝ) (hg : summable g) (h : ∀i, ∥f i∥ ≤ g i) :
  summable f :=
by { rw summable_iff_cauchy_seq_finset, exact cauchy_seq_finset_of_norm_bounded g hg h }

lemma has_sum.norm_le_of_bounded {f : ι → α} {g : ι → ℝ} {a : α} {b : ℝ}
  (hf : has_sum f a) (hg : has_sum g b) (h : ∀ i, ∥f i∥ ≤ g i) :
  ∥a∥ ≤ b :=
le_of_tendsto_of_tendsto' hf.norm hg $ λ s, norm_sum_le_of_le _ $ λ i hi, h i

/-- Quantitative result associated to the direct comparison test for series:  If `∑' i, g i` is
summable, and for all `i`, `∥f i∥ ≤ g i`, then `∥∑' i, f i∥ ≤ ∑' i, g i`. Note that we do not
assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
lemma tsum_of_norm_bounded {f : ι → α} {g : ι → ℝ} {a : ℝ} (hg : has_sum g a)
  (h : ∀ i, ∥f i∥ ≤ g i) :
  ∥∑' i : ι, f i∥ ≤ a :=
begin
  by_cases hf : summable f,
  { exact hf.has_sum.norm_le_of_bounded hg h },
  { rw [tsum_eq_zero_of_not_summable hf, norm_zero],
    exact ge_of_tendsto' hg (λ s, sum_nonneg $ λ i hi, (norm_nonneg _).trans (h i)) }
end

/-- If `∑' i, ∥f i∥` is summable, then `∥∑' i, f i∥ ≤ (∑' i, ∥f i∥)`. Note that we do not assume
that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete space. -/
lemma norm_tsum_le_tsum_norm {f : ι → α} (hf : summable (λi, ∥f i∥)) :
  ∥∑' i, f i∥ ≤ ∑' i, ∥f i∥ :=
tsum_of_norm_bounded hf.has_sum $ λ i, le_rfl

/-- Quantitative result associated to the direct comparison test for series: If `∑' i, g i` is
summable, and for all `i`, `nnnorm (f i) ≤ g i`, then `nnnorm (∑' i, f i) ≤ ∑' i, g i`. Note that we
do not assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete
space. -/
lemma tsum_of_nnnorm_bounded {f : ι → α} {g : ι → ℝ≥0} {a : ℝ≥0} (hg : has_sum g a)
  (h : ∀ i, nnnorm (f i) ≤ g i) :
  nnnorm (∑' i : ι, f i) ≤ a :=
begin
  simp only [← nnreal.coe_le_coe, ← nnreal.has_sum_coe, coe_nnnorm] at *,
  exact tsum_of_norm_bounded hg h
end

/-- If `∑' i, nnnorm (f i)` is summable, then `nnnorm (∑' i, f i) ≤ ∑' i, nnnorm (f i)`. Note that
we do not assume that `∑' i, f i` is summable, and it might not be the case if `α` is not a complete
space. -/
lemma nnnorm_tsum_le {f : ι → α} (hf : summable (λi, nnnorm (f i))) :
  nnnorm (∑' i, f i) ≤ ∑' i, nnnorm (f i) :=
tsum_of_nnnorm_bounded hf.has_sum (λ i, le_rfl)

variable [complete_space α]

/-- Variant of the direct comparison test for series:  if the norm of `f` is eventually bounded by a
real function `g` which is summable, then `f` is summable. -/
lemma summable_of_norm_bounded_eventually {f : ι → α} (g : ι → ℝ) (hg : summable g)
  (h : ∀ᶠ i in cofinite, ∥f i∥ ≤ g i) : summable f :=
begin
  replace h := mem_cofinite.1 h,
  refine h.summable_compl_iff.mp _,
  refine summable_of_norm_bounded _ (h.summable_compl_iff.mpr hg) _,
  rintros ⟨a, h'⟩,
  simpa using h'
end

lemma summable_of_nnnorm_bounded {f : ι → α} (g : ι → ℝ≥0) (hg : summable g)
  (h : ∀i, ∥f i∥₊ ≤ g i) : summable f :=
summable_of_norm_bounded (λ i, (g i : ℝ)) (nnreal.summable_coe.2 hg) (λ i, by exact_mod_cast h i)

lemma summable_of_summable_norm {f : ι → α} (hf : summable (λa, ∥f a∥)) : summable f :=
summable_of_norm_bounded _ hf (assume i, le_refl _)

lemma summable_of_summable_nnnorm {f : ι → α} (hf : summable (λ a, ∥f a∥₊)) : summable f :=
summable_of_nnnorm_bounded _ hf (assume i, le_refl _)

end summable

section cauchy_product

/-! ## Multipliying two infinite sums in a normed ring

In this section, we prove various results about `(∑' x : ι, f x) * (∑' y : ι', g y)` in a normed
ring. There are similar results proven in `topology/algebra/infinite_sum` (e.g `tsum_mul_tsum`),
but in a normed ring we get summability results which aren't true in general.

We first establish results about arbitrary index types, `β` and `γ`, and then we specialize to
`β = γ = ℕ` to prove the Cauchy product formula
(see `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`).

### Arbitrary index types
-/

variables {ι' : Type*} [normed_ring α]

open finset
open_locale classical

lemma summable.mul_of_nonneg {f : ι → ℝ} {g : ι' → ℝ}
  (hf : summable f) (hg : summable g) (hf' : 0 ≤ f) (hg' : 0 ≤ g) :
  summable (λ (x : ι × ι'), f x.1 * g x.2) :=
let ⟨s, hf⟩ := hf in
let ⟨t, hg⟩ := hg in
suffices this : ∀ u : finset (ι × ι'), ∑ x in u, f x.1 * g x.2 ≤ s*t,
  from summable_of_sum_le (λ x, mul_nonneg (hf' _) (hg' _)) this,
assume u,
calc  ∑ x in u, f x.1 * g x.2
    ≤ ∑ x in (u.image prod.fst).product (u.image prod.snd), f x.1 * g x.2 :
      sum_mono_set_of_nonneg (λ x, mul_nonneg (hf' _) (hg' _)) subset_product
... = ∑ x in u.image prod.fst, ∑ y in u.image prod.snd, f x * g y : sum_product
... = ∑ x in u.image prod.fst, f x * ∑ y in u.image prod.snd, g y :
      sum_congr rfl (λ x _, mul_sum.symm)
... ≤ ∑ x in u.image prod.fst, f x * t :
      sum_le_sum
        (λ x _, mul_le_mul_of_nonneg_left (sum_le_has_sum _ (λ _ _, hg' _) hg) (hf' _))
... = (∑ x in u.image prod.fst, f x) * t : sum_mul.symm
... ≤ s * t :
      mul_le_mul_of_nonneg_right (sum_le_has_sum _ (λ _ _, hf' _) hf) (hg.nonneg $ λ _, hg' _)

lemma summable.mul_norm {f : ι → α} {g : ι' → α}
  (hf : summable (λ x, ∥f x∥)) (hg : summable (λ x, ∥g x∥)) :
  summable (λ (x : ι × ι'), ∥f x.1 * g x.2∥) :=
summable_of_nonneg_of_le (λ x, norm_nonneg (f x.1 * g x.2)) (λ x, norm_mul_le (f x.1) (g x.2))
  (hf.mul_of_nonneg hg (λ x, norm_nonneg $ f x) (λ x, norm_nonneg $ g x) : _)

lemma summable_mul_of_summable_norm [complete_space α] {f : ι → α} {g : ι' → α}
  (hf : summable (λ x, ∥f x∥)) (hg : summable (λ x, ∥g x∥)) :
  summable (λ (x : ι × ι'), f x.1 * g x.2) :=
summable_of_summable_norm (hf.mul_norm hg)

/-- Product of two infinites sums indexed by arbitrary types.
    See also `tsum_mul_tsum` if `f` and `g` are *not* absolutely summable. -/
lemma tsum_mul_tsum_of_summable_norm [complete_space α] {f : ι → α} {g : ι' → α}
  (hf : summable (λ x, ∥f x∥)) (hg : summable (λ x, ∥g x∥)) :
  (∑' x, f x) * (∑' y, g y) = (∑' z : ι × ι', f z.1 * g z.2) :=
tsum_mul_tsum (summable_of_summable_norm hf) (summable_of_summable_norm hg)
  (summable_mul_of_summable_norm hf hg)

/-! ### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm`, where the `n`-th term is a sum over
`finset.range (n+1)` involving `nat` substraction.
In order to avoid `nat` substraction, we also provide
`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`finset` `finset.nat.antidiagonal n`. -/

section nat

open finset.nat

lemma summable_norm_sum_mul_antidiagonal_of_summable_norm {f g : ℕ → α}
  (hf : summable (λ x, ∥f x∥)) (hg : summable (λ x, ∥g x∥)) :
  summable (λ n, ∥∑ kl in antidiagonal n, f kl.1 * g kl.2∥) :=
begin
  have := summable_sum_mul_antidiagonal_of_summable_mul
    (summable.mul_of_nonneg hf hg (λ _, norm_nonneg _) (λ _, norm_nonneg _)),
  refine summable_of_nonneg_of_le (λ _, norm_nonneg _) _ this,
  intros n,
  calc  ∥∑ kl in antidiagonal n, f kl.1 * g kl.2∥
      ≤ ∑ kl in antidiagonal n, ∥f kl.1 * g kl.2∥ : norm_sum_le _ _
  ... ≤ ∑ kl in antidiagonal n, ∥f kl.1∥ * ∥g kl.2∥ : sum_le_sum (λ i _, norm_mul_le _ _)
end

/-- The Cauchy product formula for the product of two infinites sums indexed by `ℕ`,
    expressed by summing on `finset.nat.antidiagonal`.
    See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal` if `f` and `g` are
    *not* absolutely summable. -/
lemma tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm [complete_space α] {f g : ℕ → α}
  (hf : summable (λ x, ∥f x∥)) (hg : summable (λ x, ∥g x∥)) :
  (∑' n, f n) * (∑' n, g n) = ∑' n, ∑ kl in antidiagonal n, f kl.1 * g kl.2 :=
tsum_mul_tsum_eq_tsum_sum_antidiagonal (summable_of_summable_norm hf) (summable_of_summable_norm hg)
  (summable_mul_of_summable_norm hf hg)

lemma summable_norm_sum_mul_range_of_summable_norm {f g : ℕ → α}
  (hf : summable (λ x, ∥f x∥)) (hg : summable (λ x, ∥g x∥)) :
  summable (λ n, ∥∑ k in range (n+1), f k * g (n - k)∥) :=
begin
  simp_rw ← sum_antidiagonal_eq_sum_range_succ (λ k l, f k * g l),
  exact summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg
end

/-- The Cauchy product formula for the product of two infinites sums indexed by `ℕ`,
    expressed by summing on `finset.range`.
    See also `tsum_mul_tsum_eq_tsum_sum_range` if `f` and `g` are
    *not* absolutely summable. -/
lemma tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm [complete_space α] {f g : ℕ → α}
  (hf : summable (λ x, ∥f x∥)) (hg : summable (λ x, ∥g x∥)) :
  (∑' n, f n) * (∑' n, g n) = ∑' n, ∑ k in range (n+1), f k * g (n - k) :=
begin
  simp_rw ← sum_antidiagonal_eq_sum_range_succ (λ k l, f k * g l),
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
end

end nat

end cauchy_product

namespace uniform_space
namespace completion

variables (V : Type*)

instance [uniform_space V] [has_norm V] :
  has_norm (completion V) :=
{ norm := completion.extension has_norm.norm }

@[simp] lemma norm_coe {V} [semi_normed_group V] (v : V) :
  ∥(v : completion V)∥ = ∥v∥ :=
completion.extension_coe uniform_continuous_norm v

instance [semi_normed_group V] : normed_group (completion V) :=
{ dist_eq :=
  begin
    intros x y,
    apply completion.induction_on₂ x y; clear x y,
    { refine is_closed_eq (completion.uniform_continuous_extension₂ _).continuous _,
      exact continuous.comp completion.continuous_extension continuous_sub },
    { intros x y,
      rw [← completion.coe_sub, norm_coe, metric.completion.dist_eq, dist_eq_norm] }
  end,
  .. (show add_comm_group (completion V), by apply_instance),
  .. (show metric_space (completion V), by apply_instance) }

end completion
end uniform_space

namespace locally_constant

variables {X Y : Type*} [topological_space X] [topological_space Y] (f : locally_constant X Y)

/-- The inclusion of locally-constant functions into continuous functions as a multiplicative
monoid hom. -/
@[to_additive "The inclusion of locally-constant functions into continuous functions as an
additive monoid hom.", simps]
def to_continuous_map_monoid_hom [monoid Y] [has_continuous_mul Y] :
  locally_constant X Y →* C(X, Y) :=
{ to_fun    := coe,
  map_one' := by { ext, simp, },
  map_mul'  := λ x y, by { ext, simp, }, }

/-- The inclusion of locally-constant functions into continuous functions as a linear map. -/
@[simps] def to_continuous_map_linear_map (R : Type*) [semiring R] [topological_space R]
  [add_comm_monoid Y] [module R Y] [has_continuous_add Y] [has_continuous_smul R Y] :
  locally_constant X Y →ₗ[R] C(X, Y) :=
{ to_fun    := coe,
  map_add'  := λ x y, by { ext, simp, },
  map_smul' := λ x y, by { ext, simp, }, }

/-- The inclusion of locally-constant functions into continuous functions as an algebra map. -/
@[simps] def to_continuous_map_alg_hom (R : Type*) [comm_semiring R] [topological_space R]
  [semiring Y] [algebra R Y] [topological_ring Y] [has_continuous_smul R Y] :
  locally_constant X Y →ₐ[R] C(X, Y) :=
{ to_fun    := coe,
  map_one'  := by { ext, simp, },
  map_mul'  := λ x y, by { ext, simp, },
  map_zero' := by { ext, simp, },
  map_add'  := λ x y, by { ext, simp, },
  commutes' := λ r, by { ext x, simp [algebra.smul_def], }, }

end locally_constant
