/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton

Type of continuous maps and the compact-open topology on them.
-/
import topology.algebra.infinite_sum
import topology.continuous_function.algebra
import topology.subset_properties
import topology.continuous_function.basic
import topology.homeomorph
import tactic.tidy

/-!
# The compact-open topology

In this file, we define the compact-open topology on the set of continuous maps between two
topological spaces.

## Main definitions

* `compact_open` is the compact-open topology on `C(α, β)`. It is declared as an instance.
* `ev` is the evaluation map `C(α, β) × α → β`. It is continuous as long as `α` is locally compact.
* `coev` is the coevaluation map `β → C(α, β × α)`. It is always continuous.
* `continuous_map.curry` is the currying map `C(α × β, γ) → C(α, C(β, γ))`. This map always exists
  and it is continuous as long as `α × β` is locally compact.
* `continuous_map.uncurry` is the uncurrying map `C(α, C(β, γ)) → C(α × β, γ)`. For this map to
  exist, we need `β` to be locally compact. If `α` is also locally compact, then this map is
  continuous.
* `homeomorph.curry` combines the currying and uncurrying operations into a homeomorphism
  `C(α × β, γ) ≃ₜ C(α, C(β, γ))`. This homeomorphism exists if `α` and `β` are locally compact.


## Tags

compact-open, curry, function space
-/

open set
open_locale topological_space

namespace continuous_map

section compact_open
variables {α : Type*} {β : Type*} {γ : Type*}
variables [topological_space α] [topological_space β] [topological_space γ]

def compact_open.gen (s : set α) (u : set β) : set C(α,β) := {f | f '' s ⊆ u}

def compact_open'.gen (s : set α) (u : set β) : set (α → β) := {f | f '' s ⊆ u}

variables (β)
def uniform_on.gen (s : set α) : set (set C(α, β)) :=
{m | ∃ (u : set β) (hu : is_open u), m = compact_open.gen s u}

def uniform_on'.gen (s : set α) : set (set C(α, β)) :=
{m | ∃ (s' : set α) (hs' : is_compact s) (hss' : s' ⊂ s) (u : set β) (hu : is_open u),
  m = compact_open.gen s u}


/-- For a fixed `s : set α`, the topology on the space of continuous maps `α → β` of "uniform
convergence on `s`".  Not an instance because it varies with `s`. -/
def uniform_on (s : set α) : topological_space C(α, β) :=
topological_space.generate_from (uniform_on.gen β s)
variables {β}

lemma uniform_on_mono {s₁ s₂ : set α} (h : s₁ ⊆ s₂) : uniform_on β s₂ ≤ uniform_on β s₁ :=
begin
  dsimp [uniform_on],
  apply generate_from_mono,
  dsimp [uniform_on.gen],
  rintros s ⟨t, ht, hts⟩,
  refine ⟨t, ht, _⟩,
  ext f,
  simp [compact_open.gen],

end

private lemma is_open_uniform_on_gen (s : set α) {u : set β} (hu : is_open u) :
  (uniform_on β s).is_open (compact_open.gen s u) :=
topological_space.generate_open.basic _ (by dsimp [uniform_on.gen, mem_set_of_eq]; tauto)

/-- The compact-open topology on the space of continuous maps `α → β`. -/
instance compact_open' : topological_space (α → β) :=
topological_space.generate_from
  {m | ∃ (s : set α) (hs : is_compact s) (u : set β) (hu : is_open u), m = compact_open'.gen s u}

/-- The compact-open topology on the space of continuous maps `α → β`. -/
instance compact_open : topological_space C(α, β) :=
topological_space.generate_from
  {m | ∃ (s : set α) (hs : is_compact s) (u : set β) (hu : is_open u), m = compact_open.gen s u}

private lemma is_open_gen {s : set α} (hs : is_compact s) {u : set β} (hu : is_open u) :
  is_open (compact_open.gen s u) :=
topological_space.generate_open.basic _ (by dsimp [mem_set_of_eq]; tauto)

/-- The compact-open topology is equal to the infimum, as `s` varies over the compact subsets of
`α`, of the topologies of uniform convergence on `s`. -/
lemma compact_open_eq_Inf_uniform_on :
  continuous_map.compact_open = ⨅ (s : set α) (hs : is_compact s), uniform_on β s :=
begin
  transitivity
    topological_space.generate_from (⋃ (s : set α) (hs : is_compact s), uniform_on.gen β s),
  { rw continuous_map.compact_open,
    congr' 1,
    ext s,
    simp [uniform_on.gen] },
  simp [generate_from_Union, uniform_on]
end

lemma nhds_compact_open_eq_Inf (f : C(α, β)) :
  nhds f = ⨅ (s : set α) (hs : is_compact s), @nhds _ (uniform_on β s) f :=
by { rw [compact_open_eq_Inf_uniform_on], simp [nhds_infi] }

lemma nhds_uniform_on_mono {s₁ s₂ : set α} (hs : s₁ ⊆ s₂) (f : C(α, β)) :
  @nhds _ (uniform_on β s₂) f ≤ @nhds _ (uniform_on β s₁) f :=
nhds_mono (uniform_on_mono hs)

lemma tendsto_compact_open_iff_forall {ι : Type*} {l : filter ι} (F : ι → C(α, β)) (f : C(α, β)) :
  filter.tendsto F l (nhds f)
  ↔ ∀ (s : set α) (hs : is_compact s), filter.tendsto F l (@nhds _ (uniform_on β s) f) :=
by { rw [compact_open_eq_Inf_uniform_on], simp [nhds_infi] }

lemma tendsto_uniform_on_mono {ι : Type*} {l : filter ι} {F : ι → C(α, β)} {s₁ s₂ : set α}
  (hs : s₁ ⊆ s₂) {f : C(α, β)} (hFf : filter.tendsto F l (@nhds _ (uniform_on β s₂) f)) :
  filter.tendsto F l (@nhds _ (uniform_on β s₁) f) :=
hFf.mono_right (nhds_uniform_on_mono hs f)

lemma continuous_eval {s : set α} {a : α} (ha : a ∈ s) :
  @continuous _ _ (uniform_on β s) _ (λ f, f a) :=
sorry

lemma nhds_uniform_on_eq_nhds_uniform_on_iff [t2_space β] (s : set α) (f₁ f₂ : C(α, β)) :
  @nhds _ (uniform_on β s) f₁ = @nhds _ (uniform_on β s) f₂ ↔ eq_on f₁ f₂ s :=
sorry


noncomputable def continuous_glue {α : Type*} [topological_space α] {β : Type*}
  [topological_space β] {S : set (set α)}
  (hs : ∀ x : α, (S ∩ (nhds x).sets).nonempty) {F : Π s, s ∈ S → C(α, β)}
  (h : ∀ s (hs : s ∈ S) s' (hs' : s' ∈ S), eq_on (F s hs) (F s' hs') (s ∩ s')) :
  unique {f : C(α, β) // ∀ s (hs : S s), eq_on (F s hs) f s} :=
sorry

-- gluing lemma, probably can be made a bit more general
lemma gluing [locally_compact_space α] [t2_space β] {ι : Type*} {l : filter ι} [filter.ne_bot l]
  (F : ι → C(α, β)) :
  (∃ f, filter.tendsto F l (nhds f))
  ↔ ∀ (s : set α) (hs : is_compact s), ∃ f, filter.tendsto F l (@nhds _ (uniform_on β s) f) :=
begin
  split,
  { rintros ⟨f, hf⟩ s hs,
    rw tendsto_compact_open_iff_forall at hf,
    exact ⟨f, hf s hs⟩ },
  { intros h,
    choose f hf using h,
    -- By uniqueness of limits in a `t2_space`, since `λ i, F i x` tends to both `f s x` and
    -- `f s' x`, we have `f s x = f s' x`
    have h : ∀ s (hs : is_compact s) s' (hs' : is_compact s'), eq_on (f s hs) (f s' hs') (s ∩ s'),
    { rintros s hs s' hs' x ⟨hxs, hxs'⟩,
      have Hx := (continuous_eval hxs).continuous_at.tendsto,
      have Hx' := (continuous_eval hxs').continuous_at.tendsto,
      exact tendsto_nhds_unique (Hx.comp (hf s hs)) (Hx'.comp (hf s' hs')) },
    -- So glue the `f s hs` together and prove that this glued function `f₀` is a limit on each
    -- compact set `s`
    have hs : ∀ x, (is_compact ∩ (nhds x).sets : set (set α)).nonempty := exists_compact_mem_nhds,
    haveI := continuous_glue hs h,
    obtain ⟨f₀, hf₀⟩ := default {f₀ : C(α, β) // ∀ s (hs : is_compact s), eq_on (f s hs) f₀ s},
    refine ⟨f₀, _⟩,
    rw tendsto_compact_open_iff_forall,
    intros s hs,
    convert hf s hs using 1,
    -- For this it suffices to know that on `s` the glued function `f₀` equals `f s hs`
    rw nhds_uniform_on_eq_nhds_uniform_on_iff,
    exact (hf₀ s hs).symm }
end



section functorial

variables {g : β → γ} (hg : continuous g)

def induced (f : C(α, β)) : C(α, γ) := ⟨g ∘ f, hg.comp f.continuous⟩

private lemma preimage_gen {s : set α} (hs : is_compact s) {u : set γ} (hu : is_open u) :
  continuous_map.induced hg ⁻¹' (compact_open.gen s u) = compact_open.gen s (g ⁻¹' u) :=
begin
  ext ⟨f, _⟩,
  change g ∘ f '' s ⊆ u ↔ f '' s ⊆ g ⁻¹' u,
  rw [image_comp, image_subset_iff]
end

/-- C(α, -) is a functor. -/
lemma continuous_induced : continuous (continuous_map.induced hg : C(α, β) → C(α, γ)) :=
continuous_generated_from $ assume m ⟨s, hs, u, hu, hm⟩,
  by rw [hm, preimage_gen hg hs hu]; exact is_open_gen hs (hu.preimage hg)

end functorial

section ev

variables (α β)
def ev (p : C(α, β) × α) : β := p.1 p.2

variables {α β}

-- The evaluation map C(α, β) → β is continuous if α is locally compact.
lemma continuous_ev' [locally_compact_space α] : ∀ x, continuous (λ f : C(α, β), f x) :=
begin
  intros x,
  rw continuous_iff_continuous_at,
  rintros f n hn,
  obtain ⟨v, vn, vo, fxv⟩ := mem_nhds_iff.mp hn,
  have : v ∈ 𝓝 (f x) := is_open.mem_nhds vo fxv,
  obtain ⟨s, hs, sv, sc⟩ :=
    locally_compact_space.local_compact_nhds x (f ⁻¹' v)
      (f.continuous.tendsto x this),
  obtain ⟨u, us, uo, xu⟩ := mem_nhds_iff.mp hs,
  rw filter.mem_map,
  let w := compact_open.gen s v,
  have : w ⊆ (λ f : C(α, β), f x) ⁻¹' n,
  { rintros f' hf', calc
    f' x ∈ f' '' s  : mem_image_of_mem f' (us xu)
    ...       ⊆ v            : hf'
    ...       ⊆ n            : vn },
  have : is_open w, from is_open_gen sc vo,
  have : f ∈ w, from image_subset_iff.mpr sv,
  exact mem_nhds_iff.mpr ⟨w, by assumption, by assumption, by assumption⟩

  -- cases
end


-- The evaluation map C(α, β) × α → β is continuous if α is locally compact.
lemma continuous_ev [locally_compact_space α] : continuous (ev α β) :=
begin
  rw continuous_iff_continuous_at,
  rintros ⟨f, x⟩ n hn,
  obtain ⟨v, vn, vo, fxv⟩ := mem_nhds_iff.mp hn,
  have : v ∈ 𝓝 (f x) := is_open.mem_nhds vo fxv,
  obtain ⟨s, hs, sv, sc⟩ :=
    locally_compact_space.local_compact_nhds x (f ⁻¹' v)
      (f.continuous.tendsto x this),
  obtain ⟨u, us, uo, xu⟩ := mem_nhds_iff.mp hs,
  change (ev α β) ⁻¹' n ∈ 𝓝 (f, x),
  let w := set.prod (compact_open.gen s v) u,
  have : w ⊆ ev α β ⁻¹' n,
  { rintros ⟨f', x'⟩ ⟨hf', hx'⟩, calc
    f' x' ∈ f' '' s  : mem_image_of_mem f' (us hx')
    ...       ⊆ v            : hf'
    ...       ⊆ n            : vn },
  have : is_open w, from (is_open_gen sc vo).prod uo,
  have : (f, x) ∈ w, from ⟨image_subset_iff.mpr sv, xu⟩,
  exact mem_nhds_iff.mpr ⟨w, by assumption, by assumption, by assumption⟩

  -- cases
end
-- continuous_iff_continuous_at.mpr $ assume ⟨f, x⟩ n hn,
--   let ⟨v, vn, vo, fxv⟩ := mem_nhds_iff.mp hn in
--   have v ∈ 𝓝 (f x), from is_open.mem_nhds vo fxv,
--   let ⟨s, hs, sv, sc⟩ :=
--     locally_compact_space.local_compact_nhds x (f ⁻¹' v)
--       (f.continuous.tendsto x this) in
--   let ⟨u, us, uo, xu⟩ := mem_nhds_iff.mp hs in
--   show (ev α β) ⁻¹' n ∈ 𝓝 (f, x), from
--   let w := set.prod (compact_open.gen s v) u in
--   have w ⊆ ev α β ⁻¹' n, from assume ⟨f', x'⟩ ⟨hf', hx'⟩, calc
--     f' x' ∈ f' '' s  : mem_image_of_mem f' (us hx')
--     ...       ⊆ v            : hf'
--     ...       ⊆ n            : vn,
--   have is_open w, from (is_open_gen sc vo).prod uo,
--   have (f, x) ∈ w, from ⟨image_subset_iff.mpr sv, xu⟩,
--   mem_nhds_iff.mpr ⟨w, by assumption, by assumption, by assumption⟩

lemma continuous_eval' {s : set α} {x : α} (hs : s ∈ 𝓝 x) :
  @continuous _ _ (uniform_on β s) _ (λ f, f x) :=
begin
  rw continuous_iff_continuous_at,
  rintros f n (hn : n ∈ 𝓝 (f x)),
  rw filter.mem_map,
  rw mem_nhds_iff,
  obtain ⟨v, vn, vo, fxv⟩ := mem_nhds_iff.mp hn,
  have : v ∈ 𝓝 (f x) := is_open.mem_nhds vo fxv,
  -- have : (f x)
  refine ⟨compact_open.gen s v, _, is_open_uniform_on_gen s vo, _⟩,
  -- obtain ⟨v, vn, vo, fxv⟩ := mem_nhds_iff.mp hn,
  -- have : v ∈ 𝓝 (f x) := is_open.mem_nhds vo fxv,
  -- obtain ⟨u, us, uo, xu⟩ := mem_nhds_iff.mp hs,
  -- refine ⟨compact_open.gen s v, _, _, _⟩,
  rintros f' a,
  sorry,
  exact is_open_uniform_on_gen s vo,
  refine image_subset_iff.mpr _,
  -- rw subset_preimage
  -- change (λ f : C(α, β), f x) ⁻¹' n ∈ 𝓝 f,
  let w := set.prod (compact_open.gen s v) u,
  have : w ⊆ ev α β ⁻¹' n,
  { rintros ⟨f', x'⟩ ⟨hf', hx'⟩, calc
    f' x' ∈ f' '' s  : mem_image_of_mem f' (us hx')
    ...       ⊆ v            : hf'
    ...       ⊆ n            : vn },
  have : is_open w, from (is_open_uniform_on_gen vo).prod uo,
  have : (f, x) ∈ w, from ⟨image_subset_iff.mpr sv, xu⟩,
  exact mem_nhds_iff.mpr ⟨w, by assumption, by assumption, by assumption⟩
end

end ev

section coev

variables (α β)
def coev (b : β) : C(α, β × α) := ⟨λ a, (b, a), continuous.prod_mk continuous_const continuous_id⟩

variables {α β}
lemma image_coev {y : β} (s : set α) : (coev α β y) '' s = set.prod {y} s := by tidy

-- The coevaluation map β → C(α, β × α) is continuous (always).
lemma continuous_coev : continuous (coev α β) :=
continuous_generated_from $ begin
  rintros _ ⟨s, sc, u, uo, rfl⟩,
  rw is_open_iff_forall_mem_open,
  intros y hy,
  change (coev α β y) '' s ⊆ u at hy,
  rw image_coev s at hy,
  rcases generalized_tube_lemma is_compact_singleton sc uo hy
    with ⟨v, w, vo, wo, yv, sw, vwu⟩,
  refine ⟨v, _, vo, singleton_subset_iff.mp yv⟩,
  intros y' hy',
  change (coev α β y') '' s ⊆ u,
  rw image_coev s,
  exact subset.trans (prod_mono (singleton_subset_iff.mpr hy') sw) vwu
end

end coev

section curry

/-- Auxiliary definition, see `continuous_map.curry` and `homeomorph.curry`. -/
def curry' (f : C(α × β, γ)) (a : α) : C(β, γ) := ⟨function.curry f a⟩

/-- If a map `α × β → γ` is continuous, then its curried form `α → C(β, γ)` is continuous. -/
lemma continuous_curry' (f : C(α × β, γ)) : continuous (curry' f) :=
have hf : curry' f = continuous_map.induced f.continuous_to_fun ∘ coev _ _, by { ext, refl },
hf ▸ continuous.comp (continuous_induced f.continuous_to_fun) continuous_coev

/-- To show continuity of a map `α → C(β, γ)`, it suffices to show that its uncurried form
    `α × β → γ` is continuous. -/
lemma continuous_of_continuous_uncurry (f : α → C(β, γ))
  (h : continuous (function.uncurry (λ x y, f x y))) : continuous f :=
by { convert continuous_curry' ⟨_, h⟩, ext, refl }

/-- The curried form of a continuous map `α × β → γ` as a continuous map `α → C(β, γ)`.
    If `a × β` is locally compact, this is continuous. If `α` and `β` are both locally
    compact, then this is a homeomorphism, see `homeomorph.curry`. -/
def curry (f : C(α × β, γ)) : C(α, C(β, γ)) :=
⟨_, continuous_curry' f⟩

/-- The currying process is a continuous map between function spaces. -/
lemma continuous_curry [locally_compact_space (α × β)] :
  continuous (curry : C(α × β, γ) → C(α, C(β, γ))) :=
begin
  apply continuous_of_continuous_uncurry,
  apply continuous_of_continuous_uncurry,
  rw ←homeomorph.comp_continuous_iff' (homeomorph.prod_assoc _ _ _).symm,
  convert continuous_ev;
  tidy
end

/-- The uncurried form of a continuous map `α → C(β, γ)` is a continuous map `α × β → γ`. -/
lemma continuous_uncurry_of_continuous [locally_compact_space β] (f : C(α, C(β, γ))) :
  continuous (function.uncurry (λ x y, f x y)) :=
have hf : function.uncurry (λ x y, f x y) = ev β γ ∘ prod.map f id, by { ext, refl },
hf ▸ continuous.comp continuous_ev $ continuous.prod_map f.2 id.2

/-- The uncurried form of a continuous map `α → C(β, γ)` as a continuous map `α × β → γ` (if `β` is
    locally compact). If `α` is also locally compact, then this is a homeomorphism between the two
    function spaces, see `homeomorph.curry`. -/
def uncurry [locally_compact_space β] (f : C(α, C(β, γ))) : C(α × β, γ) :=
⟨_, continuous_uncurry_of_continuous f⟩

/-- The uncurrying process is a continuous map between function spaces. -/
lemma continuous_uncurry [locally_compact_space α] [locally_compact_space β] :
  continuous (uncurry : C(α, C(β, γ)) → C(α × β, γ)) :=
begin
  apply continuous_of_continuous_uncurry,
  rw ←homeomorph.comp_continuous_iff' (homeomorph.prod_assoc _ _ _),
  apply continuous.comp continuous_ev (continuous.prod_map continuous_ev id.2);
  apply_instance
end

/-- The family of constant maps: `β → C(α, β)` as a continuous map. -/
def const' : C(β, C(α, β)) := curry ⟨prod.fst, continuous_fst⟩

@[simp] lemma coe_const' : (const' : β → C(α, β)) = const := rfl

lemma continuous_const' : continuous (const : β → C(α, β)) := const'.continuous

end curry

end compact_open

end continuous_map

open continuous_map

namespace homeomorph
variables {α : Type*} {β : Type*} {γ : Type*}
variables [topological_space α] [topological_space β] [topological_space γ]

/-- Currying as a homeomorphism between the function spaces `C(α × β, γ)` and `C(α, C(β, γ))`. -/
def curry [locally_compact_space α] [locally_compact_space β] : C(α × β, γ) ≃ₜ C(α, C(β, γ)) :=
⟨⟨curry, uncurry, by tidy, by tidy⟩, continuous_curry, continuous_uncurry⟩

/-- If `α` has a single element, then `β` is homeomorphic to `C(α, β)`. -/
def continuous_map_of_unique [unique α] : β ≃ₜ C(α, β) :=
{ to_fun := continuous_map.induced continuous_fst ∘ coev α β,
  inv_fun := ev α β ∘ (λ f, (f, default α)),
  left_inv := λ a, rfl,
  right_inv := λ f, by { ext, rw unique.eq_default x, refl },
  continuous_to_fun := continuous.comp (continuous_induced _) continuous_coev,
  continuous_inv_fun :=
    continuous.comp continuous_ev (continuous.prod_mk continuous_id continuous_const) }

@[simp] lemma continuous_map_of_unique_apply [unique α] (b : β) (a : α) :
  continuous_map_of_unique b a = b :=
rfl

@[simp] lemma continuous_map_of_unique_symm_apply [unique α] (f : C(α, β)) :
  continuous_map_of_unique.symm f = f (default α) :=
rfl

end homeomorph

section tsum
variables {α : Type*} {β : Type*}
variables [topological_space α] [topological_space β] [add_comm_monoid β] [has_continuous_add β]

lemma has_sum_compact_open_iff_forall {ι : Type*} {l : filter ι} (F : ι → C(α, β)) (f : C(α, β)) :
  has_sum F f
  ↔ ∀ (s : set α) (hs : is_compact s), @has_sum _ _ _ (uniform_on β s) F f :=
tendsto_compact_open_iff_forall (λ a : finset ι, a.sum F) f

lemma summable_compact_open_iff_forall [locally_compact_space α] [t2_space β] {ι : Type*}
  [decidable_eq ι] [nonempty ι] {l : filter ι} (F : ι → C(α, β)) :
  summable F
  ↔ ∀ (s : set α) (hs : is_compact s), @summable _ _ _ (uniform_on β s) F :=
gluing (λ a : finset ι, a.sum F)

end tsum
