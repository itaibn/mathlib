import data.finset.basic
import data.pfun

variables {α β : Type*}

namespace part

def to_finset (o : part α) [decidable o.dom] : finset α := o.to_option.to_finset

@[simp] lemma mem_to_finset {o : part α} [decidable o.dom] {x : α} :
  x ∈ o.to_finset ↔ x ∈ o :=
by simp [to_finset]

@[simp] theorem to_finset_none : none.to_finset = (∅ : finset α) := rfl

@[simp] theorem to_finset_some {a : α} : (some a).to_finset = {a} := rfl

end part

namespace finset

variables [decidable_eq β] {s : finset α} {f : α →. β} [∀ x, decidable (f x).dom] {b : β}

def pimage (s : finset α) (f : α →. β) [∀ x, decidable (f x).dom] : finset β :=
s.bUnion (λ x, (f x).to_finset)

@[simp] lemma mem_pimage : b ∈ s.pimage f ↔ ∃ (a ∈ s), b ∈ f a := by simp [pimage]

end finset
