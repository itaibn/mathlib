/-
Copyright (c) 2021 Jordan Brown, Thomas Browning, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jordan Brown, Thomas Browning, Patrick Lutz
-/

import data.bracket
import group_theory.subgroup
import tactic.group

/-!
# General commutators.

If `G` is a group and `H₁ H₂ : subgroup G` then the general commutator `⁅H₁, H₂⁆ : subgroup G`
is the subgroup of `G` generated by the commutators `h₁ * h₂ * h₁⁻¹ * h₂⁻¹`.

## Main definitions

* `general_commutator H₁ H₂` : the commutator of the subgroups `H₁` and `H₂`
-/

open subgroup

variables {G G' : Type*} [group G] [group G'] {f : G →* G'}

/-- The commutator of two subgroups `H₁` and `H₂`. -/
instance general_commutator : has_bracket (subgroup G) (subgroup G) :=
⟨λ H₁ H₂, closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x}⟩

lemma general_commutator_def (H₁ H₂ : subgroup G) :
  ⁅H₁, H₂⁆ = closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x} := rfl

instance general_commutator_normal (H₁ H₂ : subgroup G) [h₁ : H₁.normal]
  [h₂ : H₂.normal] : normal ⁅H₁, H₂⁆ :=
begin
  let base : set G := {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x},
  suffices h_base : base = group.conjugates_of_set base,
  { dsimp only [general_commutator_def, ←base],
    rw h_base,
    exact subgroup.normal_closure_normal },
  apply set.subset.antisymm group.subset_conjugates_of_set,
  intros a h,
  simp_rw [group.mem_conjugates_of_set_iff, is_conj_iff] at h,
  rcases h with ⟨b, ⟨c, hc, e, he, rfl⟩, d, rfl⟩,
  exact ⟨d * c * d⁻¹, h₁.conj_mem c hc d, d * e * d⁻¹, h₂.conj_mem e he d, by group⟩,
end

lemma general_commutator_mono {H₁ H₂ K₁ K₂ : subgroup G} (h₁ : H₁ ≤ K₁) (h₂ : H₂ ≤ K₂) :
  ⁅H₁, H₂⁆ ≤ ⁅K₁, K₂⁆ :=
begin
  apply closure_mono,
  rintros x ⟨p, hp, q, hq, rfl⟩,
  exact ⟨p, h₁ hp, q, h₂ hq, rfl⟩,
end

lemma general_commutator_def' (H₁ H₂ : subgroup G) [H₁.normal] [H₂.normal] :
  ⁅H₁, H₂⁆ = normal_closure {x | ∃ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ = x} :=
by rw [← normal_closure_eq_self ⁅H₁, H₂⁆, general_commutator_def,
  normal_closure_closure_eq_normal_closure]

lemma general_commutator_le (H₁ H₂ : subgroup G) (K : subgroup G) :
  ⁅H₁, H₂⁆ ≤ K ↔ ∀ (p ∈ H₁) (q ∈ H₂), p * q * p⁻¹ * q⁻¹ ∈ K :=
begin
  rw [general_commutator, closure_le],
  split,
  { intros h p hp q hq,
    exact h ⟨p, hp, q, hq, rfl⟩, },
  { rintros h x ⟨p, hp, q, hq, rfl⟩,
    exact h p hp q hq, }
end

lemma general_commutator_containment (H₁ H₂ : subgroup G) {p q : G} (hp : p ∈ H₁) (hq : q ∈ H₂) :
  p * q * p⁻¹ * q⁻¹ ∈ ⁅H₁, H₂⁆ :=
(general_commutator_le H₁ H₂ ⁅H₁, H₂⁆).mp (le_refl ⁅H₁, H₂⁆) p hp q hq

lemma general_commutator_comm (H₁ H₂ : subgroup G) : ⁅H₁, H₂⁆ = ⁅H₂, H₁⁆ :=
begin
  suffices : ∀ H₁ H₂ : subgroup G, ⁅H₁, H₂⁆ ≤ ⁅H₂, H₁⁆, { exact le_antisymm (this _ _) (this _ _) },
  intros H₁ H₂,
  rw general_commutator_le,
  intros p hp q hq,
  have h : (p * q * p⁻¹ * q⁻¹)⁻¹ ∈ ⁅H₂, H₁⁆ := subset_closure ⟨q, hq, p, hp, by group⟩,
  convert inv_mem ⁅H₂, H₁⁆ h,
  group,
end

lemma general_commutator_le_right (H₁ H₂ : subgroup G) [h : normal H₂] :
  ⁅H₁, H₂⁆ ≤ H₂ :=
begin
  rw general_commutator_le,
  intros p hp q hq,
  exact mul_mem H₂ (h.conj_mem q hq p) (inv_mem H₂ hq),
end

lemma general_commutator_le_left (H₁ H₂ : subgroup G) [h : normal H₁] :
  ⁅H₁, H₂⁆ ≤ H₁ :=
begin
  rw general_commutator_comm,
  exact general_commutator_le_right H₂ H₁,
end

@[simp] lemma general_commutator_bot (H : subgroup G) : ⁅H, ⊥⁆ = (⊥ : subgroup G) :=
by { rw eq_bot_iff, exact general_commutator_le_right H ⊥ }

@[simp] lemma bot_general_commutator (H : subgroup G) : ⁅(⊥ : subgroup G), H⁆ = (⊥ : subgroup G) :=
by { rw eq_bot_iff, exact general_commutator_le_left ⊥ H }

lemma general_commutator_le_inf (H₁ H₂ : subgroup G) [normal H₁] [normal H₂] :
  ⁅H₁, H₂⁆ ≤ H₁ ⊓ H₂ :=
by simp only [general_commutator_le_left, general_commutator_le_right, le_inf_iff, and_self]
