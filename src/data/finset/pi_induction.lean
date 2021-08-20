import data.fintype.basic

open function

variables {ι : Type*} {α : ι → Type*} [fintype ι] [decidable_eq ι] [Π i, decidable_eq (α i)]

namespace finset

lemma induction_on_pi_of_choice (r : Π i, α i → finset (α i) → Prop)
  (H_ex : ∀ i (s : finset (α i)) (hs : s.nonempty), ∃ x ∈ s, r i x (s.erase x))
  {p : (Π i, finset (α i)) → Prop} (f : Π i, finset (α i)) (h0 : p (λ _, ∅))
  (step : ∀ (g : Π i, finset (α i)) (i : ι) (x : α i),
    r i x (g i) → p g → p (update g i (insert x (g i)))) :
  p f :=
begin
  induction hs : univ.sigma f using finset.strong_induction_on with s ihs generalizing f, subst s,
  cases eq_empty_or_nonempty (univ.sigma f) with he hne,
  { convert h0, simpa [funext_iff] using he },
  { rcases sigma_nonempty.1 hne with ⟨i, -, hi⟩,
    rcases H_ex i (f i) hi with ⟨x, x_mem, hr⟩,
    set g := update f i ((f i).erase x) with hg, clear_value g,
    have hx' : x ∉ g i, by { rw [hg, update_same], apply not_mem_erase },
    obtain rfl : f = update g i (insert x (g i)),
      by rw [hg, update_idem, update_same, insert_erase x_mem, update_eq_self],
    clear hg, rw [update_same, erase_insert hx'] at hr,
    refine step _ _ _ hr (ihs (univ.sigma g) _ _ rfl),
    rw ssubset_iff_of_subset (sigma_mono (subset.refl _) _),
    exacts [⟨⟨i, x⟩, mem_sigma.2 ⟨mem_univ _, by simp⟩, by simp [hx']⟩,
      (@le_update_iff _ _ _ _ g g i _).2 ⟨subset_insert _ _, λ _ _, le_rfl⟩] }
end

lemma induction_on_pi {p : (Π i, finset (α i)) → Prop} (f : Π i, finset (α i)) (h0 : p (λ _, ∅))
  (step : ∀ (g : Π i, finset (α i)) (i : ι) (x : α i) (hx : x ∉ g i),
    p g → p (update g i (insert x (g i)))) :
  p f :=
induction_on_pi_of_choice (λ i x s, x ∉ s) (λ i s ⟨x, hx⟩, ⟨x, hx, not_mem_erase x s⟩) f h0 step

lemma induction_on_pi_max [Π i, linear_order (α i)] {p : (Π i, finset (α i)) → Prop}
  (f : Π i, finset (α i)) (h0 : p (λ _, ∅))
  (step : ∀ (g : Π i, finset (α i)) (i : ι) (x : α i),
    (∀ y ∈ g i, y < x) → p g → p (update g i (insert x (g i)))) :
  p f :=
induction_on_pi_of_choice (λ i x s, ∀ y ∈ s, y < x)
  (λ i s hs, ⟨s.max' hs, s.max'_mem hs, λ y, s.lt_max'_of_mem_erase_max' _⟩) f h0 step

lemma induction_on_pi_min [Π i, linear_order (α i)] {p : (Π i, finset (α i)) → Prop}
  (f : Π i, finset (α i)) (h0 : p (λ _, ∅))
  (step : ∀ (g : Π i, finset (α i)) (i : ι) (x : α i),
    (∀ y ∈ g i, x < y) → p g → p (update g i (insert x (g i)))) :
  p f :=
@induction_on_pi_max ι (λ i, order_dual (α i)) _ _ _ _ _ _ h0 step

end finset
