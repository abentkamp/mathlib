/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro

Linear independence and basis sets in a module or vector space.

This file is inspired by Isabelle/HOL's linear algebra, and hence indirectly by HOL Light.

We define the following concepts:

* `linear_independent α v s`: states that the elements indexed by `s` are linear independent

* `linear_independent.repr s b`: choose the linear combination representing `b` on the linear
  independent vectors `s`. `b` should be in `span α b` (uses classical choice)

* `is_basis α s`: if `s` is a basis, i.e. linear independent and spans the entire space

* `is_basis.repr s b`: like `linear_independent.repr` but as a `linear_map`

* `is_basis.constr s g`: constructs a `linear_map` by extending `g` from the basis `s`

-/
import linear_algebra.basic linear_algebra.finsupp order.zorn
noncomputable theory

open function lattice set submodule

variables {ι : Type*} {ι' : Type*} {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
          {v : ι → β}
variables [decidable_eq ι] [decidable_eq ι'] [decidable_eq α] [decidable_eq β] [decidable_eq γ] [decidable_eq δ]

section module
variables [ring α] [add_comm_group β] [add_comm_group γ] [add_comm_group δ]
variables [module α β] [module α γ] [module α δ]
variables {a b : α} {x y : β}
include α



section indexed
variables {s t : set ι}

variables (α) (v)
/-- Linearly independent set of vectors -/
def linear_independent (s : set ι) : Prop :=
disjoint (finsupp.supported α α s) (finsupp.total ι β α v).ker
variables {α} {v}

theorem linear_independent_iff : linear_independent α v s ↔
  ∀l ∈ finsupp.supported α α s, finsupp.total ι β α v l = 0 → l = 0 :=
by simp [linear_independent, linear_map.disjoint_ker]

theorem linear_independent_iff_total_on : linear_independent α v s ↔ (finsupp.total_on ι β α v s).ker = ⊥ :=
by rw [finsupp.total_on, linear_map.ker, linear_map.comap_cod_restrict, map_bot, comap_bot,
  linear_map.ker_comp, linear_independent, disjoint, ← map_comap_subtype, map_le_iff_le_comap,
  comap_bot, ker_subtype, le_bot_iff]

lemma linear_independent_empty : linear_independent α v (∅ : set ι) :=
by simp [linear_independent]

lemma linear_independent_empty_type (h : ¬ nonempty ι) : linear_independent α v univ :=
begin
 rw [linear_independent_iff],
 intros,
 ext i,
 exact false.elim (not_nonempty_iff_imp_false.1 h i)
end

lemma linear_independent.mono (h : t ⊆ s) : linear_independent α v s → linear_independent α v t :=
disjoint_mono_left (finsupp.supported_mono h)

lemma linear_independent.unique (hs : linear_independent α v s) {l₁ l₂ : ι  →₀ α} :
  l₁ ∈ finsupp.supported α α s → l₂ ∈ finsupp.supported α α s →
  finsupp.total ι β α v l₁ = finsupp.total ι β α v l₂ → l₁ = l₂ :=
linear_map.disjoint_ker'.1 hs _ _

lemma zero_not_mem_of_linear_independent
  {i : ι} (ne : 0 ≠ (1:α)) (hs : linear_independent α v s) (hi : v i = 0) :
    i ∉ s :=
λ h, ne $ eq.symm begin
  suffices : (finsupp.single i 1 : ι →₀ α) i = 0, {simpa},
  rw disjoint_def.1 hs _ (finsupp.single_mem_supported _ 1 h),
  {refl}, {simp [hi]}
end

lemma linear_independent_univ_iff :
  linear_independent α v univ ↔ (finsupp.total ι β α v).ker = ⊥ :=
by simp [linear_independent, disjoint_iff]

theorem linear_independent_univ_iff_inj : linear_independent α v univ ↔
  ∀l, finsupp.total ι β α v l = 0 → l = 0 :=
by simp [linear_independent_iff]




lemma linear_independent.comp_univ (f : ι' → ι) (hf : injective f)
  (h : linear_independent α v univ) : linear_independent α (v ∘ f) univ :=
begin
  rw [linear_independent_univ_iff_inj, finsupp.total_comp],
  intros l hl,
  have h_map_domain : ∀ x, (finsupp.map_domain f l) (f x) = 0,
    by rw linear_independent_univ_iff_inj.1 h (finsupp.map_domain f l) hl; simp,
  ext,
  simp,
  simp only [finsupp.map_domain_apply hf] at h_map_domain,
  apply h_map_domain
end

lemma linear_independent_union
  (hs : linear_independent α v s) (ht : linear_independent α v t)
  (hst : disjoint (span α (v '' s)) (span α (v '' t))) :
  linear_independent α v (s ∪ t) :=
begin
  rw [linear_independent, disjoint_def, finsupp.supported_union],
  intros l h₁ h₂, rw mem_sup at h₁,
  rcases h₁ with ⟨ls, hls, lt, hlt, rfl⟩,
  rw [finsupp.span_eq_map_total, finsupp.span_eq_map_total] at hst,
  have : finsupp.total ι β α v ls ∈ map (finsupp.total ι β α v) (finsupp.supported α α t),
  { apply (add_mem_iff_left (map _ _) (mem_image_of_mem _ hlt)).1,
    rw [← linear_map.map_add, linear_map.mem_ker.1 h₂],
    apply zero_mem },
  have ls0 := disjoint_def.1 hs _ hls (linear_map.mem_ker.2 $
    disjoint_def.1 hst _ (mem_image_of_mem _ hls) this),
  subst ls0, simp [-linear_map.mem_ker] at this h₂ ⊢,
  exact disjoint_def.1 ht _ hlt h₂
end

lemma linear_independent_of_finite
  (H : ∀ t ⊆ s, finite t → linear_independent α v t) :
  linear_independent α v s :=
linear_independent_iff.2 $ λ l hl,
linear_independent_iff.1 (H _ hl (finset.finite_to_set _)) l (subset.refl _)

lemma linear_independent_Union_of_directed {η : Type*}
  {s : η → set ι} (hs : directed (⊆) s)
  (h : ∀ i, linear_independent α v (s i)) : linear_independent α v (⋃ i, s i) :=
begin
  haveI := classical.dec (nonempty η),
  by_cases hη : nonempty η,
  { refine linear_independent_of_finite (λ t ht ft, _),
    rcases finite_subset_Union ft ht with ⟨I, fi, hI⟩,
    rcases hs.finset_le hη fi.to_finset with ⟨i, hi⟩,
    exact (h i).mono (subset.trans hI $ bUnion_subset $
      λ j hj, hi j (finite.mem_to_finset.2 hj)) },
  { refine linear_independent_empty.mono _,
    rintro _ ⟨_, ⟨i, _⟩, _⟩, exact hη ⟨i⟩ }
end

lemma linear_independent_sUnion_of_directed {s : set (set ι)}
  (hs : directed_on (⊆) s)
  (h : ∀ a ∈ s, linear_independent α v a) : linear_independent α v (⋃₀ s) :=
by rw sUnion_eq_Union; exact
linear_independent_Union_of_directed
  ((directed_on_iff_directed _).1 hs) (by simpa using h)

lemma linear_independent_bUnion_of_directed {η} {s : set η} {t : η → set ι}
  (hs : directed_on (t ⁻¹'o (⊆)) s) (h : ∀a∈s, linear_independent α v (t a)) :
  linear_independent α v (⋃a∈s, t a) :=
by rw bUnion_eq_Union; exact
linear_independent_Union_of_directed
  ((directed_comp _ _ _).2 $ (directed_on_iff_directed _).1 hs)
  (by simpa using h)

lemma linear_independent_Union_finite___ {η : Type*} {ιs : η → Type*}
  [decidable_eq η] [∀ j, decidable_eq (ιs j)]
  {f : Π j : η, ιs j → β}
  (hl : ∀j, linear_independent α (f j) univ)
  (hd : ∀i, ∀t:set η, finite t → i ∉ t →
  disjoint (span α (range (f i))) (⨆i∈t, span α (range (f i)))) :
  linear_independent α (λ ji : Σ j, ιs j, f ji.1 ji.2) univ :=
sorry

lemma linear_independent_Union_finite {η : Type*} {f : η → set ι}
  (hl : ∀i, linear_independent α v (f i))
  (hd : ∀i, ∀t:set η, finite t → i ∉ t →
  disjoint (span α (v '' (f i))) (⨆i∈t, span α (v '' (f i)))) :
  linear_independent α v (⋃i, f i) :=
begin
  haveI := classical.dec_eq η,
  rw [Union_eq_Union_finset f],
  refine linear_independent_Union_of_directed (directed_of_sup _) _,
  exact (assume t₁ t₂ ht, Union_subset_Union $ assume i, Union_subset_Union_const $ assume h, ht h),
  assume t, rw [set.Union, ← finset.sup_eq_supr],
  refine t.induction_on _ _,
  { exact linear_independent_empty },
  { rintros ⟨i⟩ s his ih,
    rw [finset.sup_insert],
    refine linear_independent_union (hl _) ih _,
    rw [finset.sup_eq_supr],
    refine disjoint_mono (le_refl _) _ (hd i _ _ his),
    { simp only [(span_Union _).symm, set.image_Union],
      refine span_mono (@supr_le_supr2 (set β) _ _ _ _ _ _),
      rintros ⟨i⟩, exact ⟨i, le_refl _⟩ },
    { change finite (plift.up ⁻¹' s.to_set),
      exact finite_preimage (assume i j, plift.up.inj) s.finite_to_set } }
end

section repr
variables (hs : linear_independent α v s)

lemma linear_independent.injective (zero_ne_one : (0 : α) ≠ 1)
  (hs : linear_independent α v s) (i j : ι) (hi : i ∈ s) (hi : j ∈ s)
  (hij: v i = v j) : i = j :=
begin
  let l : ι →₀ α := finsupp.single i (1 : α) - finsupp.single j 1,
  have h_supp : l ∈ finsupp.supported α α s,
  { dsimp only [l],
    rw [finsupp.mem_supported],
    intros k hk,
    apply or.elim (finset.mem_union.1 (finsupp.support_add (finset.mem_coe.1 hk))),
    { intro hk',
      rwa finset.mem_singleton.1 (finsupp.support_single_subset hk') },
    { intro hk',
      rw finsupp.support_neg at hk',
      rwa finset.mem_singleton.1 (finsupp.support_single_subset hk') } },
  have h_total : finsupp.total ι β α v l = 0,
  { rw finsupp.total_apply,
    rw finsupp.sum_sub_index,
    { simp [finsupp.sum_single_index, hij] },
    { intros, apply sub_smul } },
  have h_single_eq : finsupp.single i (1 : α) = finsupp.single j 1,
  { rw linear_independent_iff at hs,
    simp [eq_add_of_sub_eq' (hs l h_supp h_total)] },
  show i = j,
  { apply or.elim ((finsupp.single_eq_single_iff _ _ _ _).1 h_single_eq),
    simp,
    exact λ h, false.elim (zero_ne_one.symm h.1) }
end

lemma linear_independent.id_of_univ (zero_ne_one : (0 : α) ≠ 1)
  (h : linear_independent α v univ) : linear_independent α id (range v) :=
begin
  rw linear_independent_iff,
  intros l hl₁ hl₂,
  have h_bij : bij_on v (v ⁻¹' finset.to_set (l.support)) (finset.to_set (l.support)),
  {
    apply bij_on.mk,
    { rw maps_to',
      apply image_preimage_subset },
    { unfold inj_on,
      intros i₁ i₂ hi₁ hi₂ hi,
      apply linear_independent.injective zero_ne_one h _ _ (mem_univ _) (mem_univ _) hi,
     },
    { intros x hx,
      apply exists.elim (mem_range.1 ((finsupp.mem_supported α l).2 hl₁ hx)),
      intros x' hx',
      rw mem_image,
      use x',
      split,
      { rwa [mem_preimage_eq, hx'] },
      { exact hx' } },
  },
  rw linear_independent_univ_iff_inj at h,
  rw finsupp.total_apply at hl₂,
  rw finsupp.sum at hl₂,
  have := h (finsupp.comap_domain v l (set.inj_on_of_bij_on h_bij)),
  rw finsupp.total_comap_domain at this,
  rw finset.sum_preimage v l.support (set.inj_on_of_bij_on h_bij) (λ (x : β), l x • x) at this,
  have := this hl₂,
  apply finsupp.eq_zero_of_comap_domain_eq_zero _ _ h_bij this,
end

lemma linear_independent.univ_of_id (hv : injective v)
  (h : linear_independent α id (range v)) : linear_independent α v univ :=
begin
  rw linear_independent_iff at *,
  intros l hl₁ hl₂,
  apply finsupp.injective_map_domain hv,
  apply h (l.map_domain v),
  { rw finsupp.mem_supported,
    intros x hx,
    have := finset.mem_coe.2 (finsupp.map_domain_support hx),
    rw finset.coe_image at this,
    apply set.image_subset_range _ _ this },
  { rw finsupp.total_map_domain _ _ hv,
    rw left_id,
    exact hl₂ }
end

def linear_independent.total_equiv : finsupp.supported α α s ≃ₗ span α (v '' s) :=
linear_equiv.of_bijective (finsupp.total_on ι β α v s)
  (linear_independent_iff_total_on.1 hs) (finsupp.total_on_range _ _)

private def aux_linear_equiv_to_linear_map:
  has_coe (span α (v '' s) ≃ₗ[α] finsupp.supported α α s)
          (span α (v '' s) →ₗ[α] finsupp.supported α α s) :=
⟨linear_equiv.to_linear_map⟩
local attribute [instance] aux_linear_equiv_to_linear_map

def linear_independent.repr : span α (v '' s) →ₗ[α] ι →₀ α :=
(submodule.subtype _).comp (hs.total_equiv.symm : span α (v '' s) →ₗ[α] finsupp.supported α α s )

lemma linear_independent.total_repr (x) : finsupp.total ι β α v (hs.repr x) = x :=
subtype.ext.1 $ hs.total_equiv.right_inv x

lemma linear_independent.total_comp_repr : (finsupp.total ι β α v).comp hs.repr = submodule.subtype _ :=
linear_map.ext $ hs.total_repr

lemma linear_independent.repr_ker : hs.repr.ker = ⊥ :=
by rw [linear_independent.repr, linear_map.ker_comp, ker_subtype, comap_bot, linear_equiv.ker]

lemma linear_independent.repr_range : hs.repr.range = finsupp.supported α α s :=
by rw [linear_independent.repr, linear_map.range_comp, linear_equiv.range, map_top, range_subtype]

private def aux_linear_map_to_fun : has_coe_to_fun (finsupp.supported α α s →ₗ[α] span α (v '' s)) :=
  ⟨_, linear_map.to_fun⟩
local attribute [instance] aux_linear_map_to_fun

lemma linear_independent.repr_eq
  {l : ι →₀ α} (h : l ∈ finsupp.supported α α s) {x} (eq : finsupp.total ι β α v l = ↑x) :
  hs.repr x = l :=
by rw ← (subtype.eq' eq : (finsupp.total_on ι β α v s : finsupp.supported α α s →ₗ span α (v '' s)) ⟨l, h⟩ = x);
   exact subtype.ext.1 (hs.total_equiv.left_inv ⟨l, h⟩)

lemma linear_independent.repr_eq_single (i) (x) (hi : i ∈ s) (hx : ↑x = v i) : hs.repr x = finsupp.single i 1 :=
begin
  apply hs.repr_eq (finsupp.single_mem_supported _ _ hi),
  simp [finsupp.total_single, hx]
end

def aux_linear_map_to_fun : has_coe_to_fun (span α (v '' s) →ₗ[α] finsupp.supported α α s) :=
  ⟨_, linear_map.to_fun⟩
local attribute [instance] aux_linear_map_to_fun

lemma linear_independent.repr_supported (x) : hs.repr x ∈ finsupp.supported α α s :=
((hs.total_equiv.symm : span α (v '' s) →ₗ[α] finsupp.supported α α s) x).2

lemma linear_independent.repr_eq_repr_of_subset (h : t ⊆ s) (x y) (e : (↑x:β) = ↑y) :
  (hs.mono h).repr x = hs.repr y :=
eq.symm $ hs.repr_eq (finsupp.supported_mono h ((hs.mono h).repr_supported _) : _ ∈ ↑(finsupp.supported α α s))
  (by rw [← e, (hs.mono h).total_repr]).

lemma linear_independent_iff_not_smul_mem_span :
  linear_independent α v s ↔ (∀ (i ∈ s) (a : α), a • (v i) ∈ span α (v '' (s \ {i})) → a = 0) :=
⟨λ hs i hi a ha, begin
  rw [finsupp.span_eq_map_total, mem_map] at ha,
  rcases ha with ⟨l, hl, e⟩,
  have := (finsupp.supported α α s).sub_mem
    (finsupp.supported_mono (diff_subset _ _) hl : _ ∈ ↑(finsupp.supported α α s))
    (finsupp.single_mem_supported α a hi),
  rw [sub_eq_zero.1 (linear_independent_iff.1 hs _ this $ by simp [e])] at hl,
  by_contra hn,
  exact (not_mem_of_mem_diff (hl $ by simp [hn])) (mem_singleton _)
end, λ H, linear_independent_iff.2 $ λ l ls l0, begin
  ext x, simp,
  by_contra hn,
  have xs : x ∈ s := ls (finsupp.mem_support_iff.2 hn),
  refine hn (H _ xs _ _),
  refine (finsupp.mem_span_iff_total _).2 ⟨finsupp.single x (l x) - l, _, _⟩,
  { have : finsupp.single x (l x) - l ∈ finsupp.supported α α s :=
      sub_mem _ (finsupp.single_mem_supported _ _ xs) ls,
    refine λ y hy, ⟨this hy, λ e, _⟩,
    simp at e hy, apply hy, simp [e] },
  { simp [l0] }
end⟩

lemma linear_independent.restrict_univ (hs : linear_independent α v s) :
  linear_independent α (function.restrict v s) univ :=
begin
  have h_restrict : restrict v s = v ∘ (λ x, x.val),
    by refl,
  rw linear_independent_iff at *,
  rw h_restrict,
  rw finsupp.total_comp,
  intros l _ hl,
  simp at hl,
  have h_map_domain_subtype_eq_0 : l.map_domain subtype.val = 0,
  {
    apply hs (finsupp.lmap_domain α α (λ x : subtype s, x.val) l),
    {
      rw finsupp.mem_supported,
      simp,
      intros x hx,
      have := finset.mem_coe.2 (finsupp.map_domain_support (finset.mem_coe.1 hx)),
      rw finset.coe_image at this,
      exact subtype.val_image_subset _ _ this
    },
    {
      simpa
    },
  },
  apply @finsupp.injective_map_domain _ (subtype s) ι,
  { apply subtype.val_injective },
  { simpa },
end

end repr

lemma eq_of_linear_independent_of_span (nz : (1 : α) ≠ 0)
  (hs : linear_independent α v s) (h : t ⊆ s) (hst : v '' s ⊆ span α (v '' t)) : s = t :=
begin
  refine subset.antisymm (λ i hi, _) h,
  have : (hs.mono h).repr ⟨v i, hst (set.mem_image_of_mem _ hi)⟩ = finsupp.single i 1 :=
    (hs.repr_eq_repr_of_subset h ⟨v i, hst (set.mem_image_of_mem _ hi)⟩
      ⟨v i, subset_span (set.mem_image_of_mem _ hi)⟩ rfl).trans
      (hs.repr_eq_single i ⟨v i, _⟩ hi (by simp)),
  have ss := (hs.mono h).repr_supported _,
  rw this at ss, exact ss (by simp [nz]),
end

end indexed

section
variables {s t : set β} {f : β →ₗ[α] γ}
variables (hf_inj : ∀ x y ∈ t, f x = f y → x = y)
variables (ht : linear_independent α id (f '' t))
include hf_inj ht
open linear_map

lemma linear_independent.supported_disjoint_ker :
  disjoint (finsupp.supported α α t) (ker (f.comp (finsupp.total _ _ _ id))) :=
begin
  refine le_trans (le_inf inf_le_left _) (finsupp.lmap_domain_disjoint_ker _ _ f hf_inj),
  haveI : inhabited β := ⟨0⟩,
  rw [linear_independent, disjoint_iff, ← finsupp.lmap_domain_supported α α f t] at ht,
  rw [← @finsupp.lmap_domain_total _ _ α _ _ _ _ _ _ _ _ _ _ _ _ id id f f (by simp), le_ker_iff_map],
  refine eq_bot_mono (le_inf (map_mono inf_le_left) _) ht,
  rw [map_le_iff_le_comap, ← ker_comp], exact inf_le_right,
end

lemma linear_independent.of_image : linear_independent α (id : β → β) t :=
disjoint_mono_right (ker_le_ker_comp _ _) (ht.supported_disjoint_ker hf_inj)

lemma linear_independent.disjoint_ker : disjoint (span α t) f.ker :=
by rw [← set.image_id t, finsupp.span_eq_map_total, disjoint_iff, map_inf_eq_map_inf_comap,
  ← ker_comp, disjoint_iff.1 (ht.supported_disjoint_ker hf_inj), map_bot]

end

lemma linear_independent.inj_span_iff_inj
  {t : set β} {f : β →ₗ[α] γ}
  (ht : linear_independent α id (f '' t)) :
  disjoint (span α t) f.ker ↔ (∀ x y ∈ t, f x = f y → x = y) :=
⟨linear_map.inj_of_disjoint_ker subset_span, λ h, ht.disjoint_ker h⟩

open linear_map

lemma linear_independent.image {s : set β} {f : β →ₗ γ} (hs : linear_independent α id s)
  (hf_inj : disjoint (span α s) f.ker) : linear_independent α id (f '' s) :=
begin
  rw [disjoint, ← set.image_id s, finsupp.span_eq_map_total, map_inf_eq_map_inf_comap,
    map_le_iff_le_comap, comap_bot] at hf_inj,
  haveI : inhabited β := ⟨0⟩,
  rw [linear_independent, disjoint, ← finsupp.lmap_domain_supported _ _ f, map_inf_eq_map_inf_comap,
      map_le_iff_le_comap, ← ker_comp, @finsupp.lmap_domain_total _ _ α _ _ _ _ _ _ _ _ _ _ _ _ id id, ker_comp],
  { exact le_trans (le_inf inf_le_left hf_inj) (le_trans hs bot_le) },
  { simp }
end

lemma linear_map.linear_independent_image_iff {s : set β} {f : β →ₗ γ}
  (hf_inj : disjoint (span α s) f.ker) :
  linear_independent α id (f '' s) ↔ linear_independent α id s :=
⟨λ hs, hs.of_image (linear_map.inj_of_disjoint_ker subset_span hf_inj),
 λ hs, hs.image hf_inj⟩

lemma linear_independent_inl_union_inr {s : set β} {t : set γ}
  (hs : linear_independent α id s) (ht : linear_independent α id t) :
  linear_independent α id (inl α β γ '' s ∪ inr α β γ '' t) :=
linear_independent_union (hs.image $ by simp) (ht.image $ by simp) $
by rw [set.image_id, span_image, set.image_id, span_image];
    simp [disjoint_iff, prod_inf_prod]



variables (α) (v)
/-- A set of vectors is a basis if it is linearly independent and all vectors are in the span α -/
def is_basis := linear_independent α v univ ∧ span α (range v) = ⊤
variables {α} {v}

section is_basis
variables {s t : set β} (hv : is_basis α v)

lemma is_basis.mem_span (hv : is_basis α v) : ∀ x, x ∈ span α (range v) := eq_top_iff'.1 hv.2

def is_basis.repr : β →ₗ (ι →₀ α) :=
(hv.1.repr).comp (linear_map.id.cod_restrict _ (by rw [image_univ]; exact hv.mem_span))

lemma is_basis.total_repr (x) : finsupp.total ι β α v (hv.repr x) = x :=
hv.1.total_repr ⟨x, _⟩

lemma is_basis.total_comp_repr : (finsupp.total ι β α v).comp hv.repr = linear_map.id :=
linear_map.ext hv.total_repr

lemma is_basis.repr_ker : hv.repr.ker = ⊥ :=
linear_map.ker_eq_bot.2 $ injective_of_left_inverse hv.total_repr

lemma is_basis.repr_range : hv.repr.range = finsupp.supported α α univ :=
by  rw [is_basis.repr, linear_map.range, submodule.map_comp,
  linear_map.map_cod_restrict, submodule.map_id, comap_top, map_top, hv.1.repr_range]

-- TODO: remove because trivial?
--lemma is_basis.repr_supported (x : β) : hv.repr x ∈ (finsupp.supported α α univ : submodule α (ι →₀ α)) :=
--hv.1.repr_supported ⟨x, _⟩

lemma is_basis.repr_total (x : ι →₀ α) (hx : x ∈ finsupp.supported α α (univ : set ι)) :
  hv.repr (finsupp.total ι β α v x) = x :=
begin
  rw [← hv.repr_range, linear_map.mem_range] at hx,
  cases hx with w hw,
  rw [← hw, hv.total_repr],
end

lemma is_basis.repr_eq_single {i} : hv.repr (v i) = finsupp.single i 1 :=
by apply hv.1.repr_eq_single; simp

/-- Construct a linear map given the value at the basis. -/
def is_basis.constr (f : ι → γ) : β →ₗ[α] γ :=
(finsupp.total γ γ α id).comp $ (finsupp.lmap_domain α α f).comp hv.repr

theorem is_basis.constr_apply (f : ι → γ) (x : β) :
  (hv.constr f : β → γ) x = (hv.repr x).sum (λb a, a • f b) :=
by dsimp [is_basis.constr];
   rw [finsupp.total_apply, finsupp.sum_map_domain_index]; simp [add_smul]

lemma is_basis.ext {f g : β →ₗ[α] γ} (hv : is_basis α v) (h : ∀i, f (v i) = g (v i)) : f = g :=
begin
  apply linear_map.ext,
  intro x,
  apply linear_eq_on (range v) _ (hv.mem_span x),
  intros y hy,
  apply exists.elim (set.mem_range.1 hy),
  intros i hi, rw ←hi, exact h i,
end

lemma constr_congr {f g : ι → γ} (hv : is_basis α v) (h : ∀i, f i = g i) :
  hv.constr f = hv.constr g :=
by ext y; simp [is_basis.constr_apply]; exact
finset.sum_congr rfl (λ x hx, by simp [h x])

lemma constr_basis {f : ι → γ} {i : ι} (hv : is_basis α v) :
  (hv.constr f : β → γ) (v i) = f i :=
by simp [is_basis.constr_apply, hv.repr_eq_single, finsupp.sum_single_index]

lemma constr_eq {g : ι → γ} {f : β →ₗ[α] γ} (hv : is_basis α v)
  (h : ∀i, g i = f (v i)) : hv.constr g = f :=
hv.ext $ λ i, (constr_basis hv).trans (h i)

lemma constr_self (f : β →ₗ[α] γ) : hv.constr (λ i, f (v i)) = f :=
constr_eq hv $ λ x, rfl

lemma constr_zero (hv : is_basis α v) : hv.constr (λi, (0 : γ)) = 0 :=
constr_eq hv $ λ x, rfl

lemma constr_add {g f : ι → γ} (hv : is_basis α v) :
  hv.constr (λi, f i + g i) = hv.constr f + hv.constr g :=
constr_eq hv $ by simp [constr_basis hv] {contextual := tt}

lemma constr_neg {f : ι → γ} (hv : is_basis α v) : hv.constr (λi, - f i) = - hv.constr f :=
constr_eq hv $ by simp [constr_basis hv] {contextual := tt}

lemma constr_sub {g f : ι → γ} (hs : is_basis α v) :
  hv.constr (λi, f i - g i) = hs.constr f - hs.constr g :=
by simp [constr_add, constr_neg]

-- this only works on functions if `α` is a commutative ring
lemma constr_smul {ι α β γ} [decidable_eq ι] [decidable_eq α] [decidable_eq β] [decidable_eq γ] [comm_ring α]
  [add_comm_group β] [add_comm_group γ] [module α β] [module α γ]
  {v : ι → α} {f : ι → γ} {a : α} (hv : is_basis α v) {b : β} :
  hv.constr (λb, a • f b) = a • hv.constr f :=
constr_eq hv $ by simp [constr_basis hv] {contextual := tt}

lemma constr_range [inhabited ι] (hv : is_basis α v) {f : ι  → γ} :
  (hv.constr f).range = span α (range f) :=
by rw [is_basis.constr, linear_map.range_comp, linear_map.range_comp, is_basis.repr_range,
    finsupp.lmap_domain_supported, ←set.image_univ, ←finsupp.span_eq_map_total, image_id]

def module_equiv_finsupp (hv : is_basis α v) : β ≃ₗ[α] finsupp.supported α α (univ : set ι) :=
(hv.1.total_equiv.trans (linear_equiv.of_top _ (by rw set.image_univ; exact hv.2))).symm

def equiv_of_is_basis {v : ι → β} {v' : ι' → γ} {f : β → γ} {g : γ → β}
  (hv : is_basis α v) (hv' : is_basis α v') (hf : ∀i, f (v i) ∈ range v') (hg : ∀i, g (v' i) ∈ range v)
  (hgf : ∀i, g (f (v i)) = v i) (hfg : ∀i, f (g (v' i)) = v' i) :
  β ≃ₗ γ :=
{ inv_fun := hv'.constr (g ∘ v'),
  left_inv :=
    have (hv'.constr (g ∘ v')).comp (hv.constr (f ∘ v)) = linear_map.id,
    from hv.ext $ λ i, exists.elim (hf i) (λ i' hi', by simp [constr_basis, hi'.symm]; rw [hi', hgf]),
    λ x, congr_arg (λ h:β →ₗ[α] β, h x) this,
  right_inv :=
    have (hv.constr (f ∘ v)).comp (hv'.constr (g ∘ v')) = linear_map.id,
    from hv'.ext $ λ i', exists.elim (hg i') (λ i hi, by simp [constr_basis, hi.symm]; rw [hi, hfg]),
    λ y, congr_arg (λ h:γ →ₗ[α] γ, h y) this,
  ..hv.constr (f ∘ v) }

/- TODO
lemma is_basis_inl_union_inr {v : ι → β} {v' : ι' → γ}
  (hv : is_basis α v) (hv' : is_basis α v') : is_basis α (sum.map v v') :=
⟨linear_independent_inl_union_inr hs.1 ht.1,
  by rw [span_union, span_image, span_image]; simp [hs.2, ht.2]⟩
-/

end is_basis

-- TODO: move
lemma finsupp.unique_single [unique ι] (x : ι →₀ α) : x = finsupp.single (default ι) (x (default ι)) :=
by ext i; simp [unique.eq_default i]

lemma is_basis_singleton_one (α : Type*) [unique ι] [decidable_eq α] [ring α] [module α β] :
  is_basis α (λ (_ : ι), (1 : α)) :=
begin
  split,
  { intro i,
    simp [unique.eq_default],
    rw finsupp.unique_single i,
    simp,
    intro hi,
    simp [hi] },
  { apply top_unique,
    intros a h,
    simp [submodule.mem_span_singleton] }
end

/- TODO: needed nowhere, but may be useful
lemma linear_equiv.is_basis (hs : is_basis α v)
  (f : β ≃ₗ[α] γ) : is_basis α (f ∘ v) :=
--show is_basis α ((f : β →ₗ[α] γ) ∘ v), from
⟨hs.1.image $ by simp, sorry ⟩ --by rw [span_image, hs.2, map_top, f.range]⟩
-/

-- TODO: move up
lemma linear_independent_span (hs : linear_independent α v univ) :
  @linear_independent ι α (span α (range v))
      (λ i : ι, ⟨v i, subset_span (mem_range_self i)⟩) _ _ _ _ _ _ univ :=
begin
  rw linear_independent_iff at *,
  intros l hl₀ hl,
  apply hs l hl₀,
  simp [finsupp.total_apply] at *,
  unfold has_scalar.smul at hl,
  simp at hl,
  unfold finsupp.sum at *,
  have := congr_arg (submodule.subtype (span α (range v))) hl,
  rw linear_map.map_sum (submodule.subtype (span α (range v))) at this,
  simp at this,
  exact this,
end

-- TODO : move
lemma submodule.subtype_eq_val (p : submodule α β) :
  ((submodule.subtype p) : p → β) = subtype.val :=
by refl

lemma is_basis_span (hs : linear_independent α v univ) :
  @is_basis ι α (span α (range v)) (λ i : ι, ⟨v i, subset_span (mem_range_self _)⟩) _ _ _ _ _ _ :=
begin
split,
{ apply linear_independent_span hs },
{ simp only [image_univ.symm,finsupp.span_eq_map_total],
  simp [range_eq_top],
  intros x,
  have := x.property,
  simp only [image_univ.symm,finsupp.span_eq_map_total, finsupp.supported_univ, map] at this,
  apply exists.elim this,
  intros l hl,
  use l,
  apply subtype.ext.2,
  simp [finsupp.total_apply, finsupp.sum] at *,
  rw ←submodule.subtype_eq_val,
  rw linear_map.map_sum (submodule.subtype (span α (range v))),
  simp,
  exact hl }
end

lemma is_basis_empty (h : ∀x:β, x = 0) : is_basis α (λ x : empty, (0 : β)) :=
⟨ linear_independent_empty_type nonempty_empty,
  eq_top_iff'.2 $ assume x, (h x).symm ▸ submodule.zero_mem _ ⟩


--lemma is_basis_empty_bot : is_basis α ({x | false } : set (⊥ : submodule α β)) :=
--is_basis_empty $ assume ⟨x, hx⟩,
--  by change x ∈ (⊥ : submodule α β) at hx; simpa [subtype.ext] using hx

end module

section vector_space
variables [discrete_field α] [add_comm_group β] [add_comm_group γ]
  [vector_space α β] [vector_space α γ] {s t : set β} {x y z : β}
include α
open submodule

/- TODO: some of the following proofs can generalized with a zero_ne_one predicate type class
   (instead of a data containing type class) -/

set_option class.instance_max_depth 36

lemma mem_span_insert_exchange : x ∈ span α (insert y s) → x ∉ span α s → y ∈ span α (insert x s) :=
begin
  simp [mem_span_insert],
  rintro a z hz rfl h,
  refine ⟨a⁻¹, -a⁻¹ • z, smul_mem _ _ hz, _⟩,
  have a0 : a ≠ 0, {rintro rfl, simp * at *},
  simp [a0, smul_add, smul_smul]
end

set_option class.instance_max_depth 32

lemma linear_independent_iff_not_mem_span : linear_independent α id s ↔ (∀x∈s, x ∉ span α (s \ {x})) :=
linear_independent_iff_not_smul_mem_span.trans
⟨λ H x xs hx, one_ne_zero (H x xs 1 $ by rw set.image_id; simpa),
 λ H x xs a hx, classical.by_contradiction $ λ a0,
   H x xs (by rw [← set.image_id (s \ {x})]; exact (smul_mem_iff _ a0).1 hx)⟩

lemma linear_independent_singleton {x : β} (hx : x ≠ 0) : linear_independent α id ({x} : set β) :=
linear_independent_iff_not_mem_span.mpr $ by simp [hx] {contextual := tt}

lemma disjoint_span_singleton {p : submodule α β} {x : β} (x0 : x ≠ 0) :
  disjoint p (span α {x}) ↔ x ∉ p :=
⟨λ H xp, x0 (disjoint_def.1 H _ xp (singleton_subset_iff.1 subset_span:_)),
begin
  simp [disjoint_def, mem_span_singleton],
  rintro xp y yp a rfl,
  by_cases a0 : a = 0, {simp [a0]},
  exact xp.elim ((smul_mem_iff p a0).1 yp),
end⟩

lemma linear_independent.insert (hs : linear_independent α id s) (hx : x ∉ span α s) :
  linear_independent α id (insert x s) :=
begin
  rw ← union_singleton,
  have x0 : x ≠ 0 := mt (by rintro rfl; apply zero_mem _) hx,
  apply linear_independent_union hs (linear_independent_singleton x0),
  rwa [set.image_id, set.image_id, disjoint_span_singleton x0],
  exact classical.dec_eq α
end

lemma exists_linear_independent (hs : linear_independent α id s) (hst : s ⊆ t) :
  ∃b⊆t, s ⊆ b ∧ t ⊆ span α b ∧ linear_independent α id b :=
begin
  rcases zorn.zorn_subset₀ {b | b ⊆ t ∧ linear_independent α id b} _ _
    ⟨hst, hs⟩ with ⟨b, ⟨bt, bi⟩, sb, h⟩,
  { refine ⟨b, bt, sb, λ x xt, _, bi⟩,
    haveI := classical.dec (x ∈ span α b),
    by_contra hn,
    apply hn,
    rw ← h _ ⟨insert_subset.2 ⟨xt, bt⟩, bi.insert hn⟩ (subset_insert _ _),
    exact subset_span (mem_insert _ _) },
  { refine λ c hc cc c0, ⟨⋃₀ c, ⟨_, _⟩, λ x, _⟩,
    { exact sUnion_subset (λ x xc, (hc xc).1) },
    { exact linear_independent_sUnion_of_directed cc.directed_on (λ x xc, (hc xc).2) },
    { exact subset_sUnion_of_mem } }
end

lemma exists_subset_is_basis (hs : linear_independent α id s) :
  ∃b, s ⊆ b ∧ is_basis α (λ i : b, i.val) :=
let ⟨b, hb₀, hx, hb₂, hb₃⟩ := exists_linear_independent hs (@subset_univ _ _) in
⟨ b, hx,
  @linear_independent.restrict_univ _ _ _ id _ _ _ _ _ _ _ hb₃,
  by simp; exact eq_top_iff.2 hb₂⟩

variables (α β)
lemma exists_is_basis : ∃b : set β, is_basis α (λ i : b, i.val) :=
let ⟨b, _, hb⟩ := exists_subset_is_basis linear_independent_empty in ⟨b, hb⟩
variables {α β}

-- TODO(Mario): rewrite?
lemma exists_of_linear_independent_of_finite_span {t : finset β}
  (hs : linear_independent α id s) (hst : s ⊆ (span α ↑t : submodule α β)) :
  ∃t':finset β, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = t.card :=
have ∀t, ∀(s' : finset β), ↑s' ⊆ s → s ∩ ↑t = ∅ → s ⊆ (span α ↑(s' ∪ t) : submodule α β) →
  ∃t':finset β, ↑t' ⊆ s ∪ ↑t ∧ s ⊆ ↑t' ∧ t'.card = (s' ∪ t).card :=
assume t, finset.induction_on t
  (assume s' hs' _ hss',
    have s = ↑s',
      from eq_of_linear_independent_of_span (@one_ne_zero α _) hs hs' $
          by rw [set.image_id, set.image_id]; simpa using hss',
    ⟨s', by simp [this]⟩)
  (assume b₁ t hb₁t ih s' hs' hst hss',
    have hb₁s : b₁ ∉ s,
      from assume h,
      have b₁ ∈ s ∩ ↑(insert b₁ t), from ⟨h, finset.mem_insert_self _ _⟩,
      by rwa [hst] at this,
    have hb₁s' : b₁ ∉ s', from assume h, hb₁s $ hs' h,
    have hst : s ∩ ↑t = ∅,
      from eq_empty_of_subset_empty $ subset.trans
        (by simp [inter_subset_inter, subset.refl]) (le_of_eq hst),
    classical.by_cases
      (assume : s ⊆ (span α ↑(s' ∪ t) : submodule α β),
        let ⟨u, hust, hsu, eq⟩ := ih _ hs' hst this in
        have hb₁u : b₁ ∉ u, from assume h, (hust h).elim hb₁s hb₁t,
        ⟨insert b₁ u, by simp [insert_subset_insert hust],
          subset.trans hsu (by simp), by simp [eq, hb₁t, hb₁s', hb₁u]⟩)
      (assume : ¬ s ⊆ (span α ↑(s' ∪ t) : submodule α β),
        let ⟨b₂, hb₂s, hb₂t⟩ := not_subset.mp this in
        have hb₂t' : b₂ ∉ s' ∪ t, from assume h, hb₂t $ subset_span h,
        have s ⊆ (span α ↑(insert b₂ s' ∪ t) : submodule α β), from
          assume b₃ hb₃,
          have ↑(s' ∪ insert b₁ t) ⊆ insert b₁ (insert b₂ ↑(s' ∪ t) : set β),
            by simp [insert_eq, -singleton_union, -union_singleton, union_subset_union, subset.refl, subset_union_right],
          have hb₃ : b₃ ∈ span α (insert b₁ (insert b₂ ↑(s' ∪ t) : set β)),
            from span_mono this (hss' hb₃),
          have s ⊆ (span α (insert b₁ ↑(s' ∪ t)) : submodule α β),
            by simpa [insert_eq, -singleton_union, -union_singleton] using hss',
          have hb₁ : b₁ ∈ span α (insert b₂ ↑(s' ∪ t)),
            from mem_span_insert_exchange (this hb₂s) hb₂t,
          by rw [span_insert_eq_span hb₁] at hb₃; simpa using hb₃,
        let ⟨u, hust, hsu, eq⟩ := ih _ (by simp [insert_subset, hb₂s, hs']) hst this in
        ⟨u, subset.trans hust $ union_subset_union (subset.refl _) (by simp [subset_insert]),
          hsu, by rw [finset.union_comm] at hb₂t'; simp [eq, hb₂t', hb₁t, hb₁s']⟩)),
begin
  letI := classical.dec_pred (λx, x ∈ s),
  have eq : t.filter (λx, x ∈ s) ∪ t.filter (λx, x ∉ s) = t,
  { apply finset.ext.mpr,
    intro x,
    by_cases x ∈ s; simp *, finish },
  apply exists.elim (this (t.filter (λx, x ∉ s)) (t.filter (λx, x ∈ s))
    (by simp [set.subset_def]) (by simp [set.ext_iff] {contextual := tt}) (by rwa [eq])),
  intros u h,
  exact ⟨u, subset.trans h.1 (by simp [subset_def, and_imp, or_imp_distrib] {contextual:=tt}),
    h.2.1, by simp only [h.2.2, eq]⟩
end

lemma exists_finite_card_le_of_finite_of_linear_independent_of_span
  (ht : finite t) (hs : linear_independent α id s) (hst : s ⊆ span α t) :
  ∃h : finite s, h.to_finset.card ≤ ht.to_finset.card :=
have s ⊆ (span α ↑(ht.to_finset) : submodule α β), by simp; assumption,
let ⟨u, hust, hsu, eq⟩ := exists_of_linear_independent_of_finite_span hs this in
have finite s, from finite_subset u.finite_to_set hsu,
⟨this, by rw [←eq]; exact (finset.card_le_of_subset $ finset.coe_subset.mp $ by simp [hsu])⟩

lemma exists_left_inverse_linear_map_of_injective {f : β →ₗ[α] γ} (zero_ne_one : (0 : α) ≠ 1)
  (hf_inj : f.ker = ⊥) : ∃g:γ →ₗ β, g.comp f = linear_map.id :=
begin
  rcases exists_is_basis α β with ⟨B, hB⟩,
  have hB₀ : _ := linear_independent.id_of_univ zero_ne_one hB.1,
  have : linear_independent α id (f '' B),
  { have := hB₀.image (show disjoint (span α (range (λ i : B, i.val))) (linear_map.ker f), by simp [hf_inj]),
    simp at this,
    exact this },
  rcases exists_subset_is_basis this with ⟨C, BC, hC⟩,
  haveI : inhabited β := ⟨0⟩,
  use hC.constr (function.restrict (inv_fun f) C : C → β),
  apply @is_basis.ext _ _ _ _ _ _ _ _ (show decidable_eq β, by assumption) _ _ _ _ _ _ _ hB,
  intros b,
  rw image_subset_iff at BC,
  simp,
  have := BC (subtype.mem b),
  rw mem_preimage_eq at this,
  have : f (b.val) = (subtype.mk (f ↑b) (begin rw ←mem_preimage_eq, exact BC (subtype.mem b) end) : C).val,
    by simp; unfold_coes,
  rw this,
  rw [constr_basis hC],
  exact left_inverse_inv_fun (linear_map.ker_eq_bot.1 hf_inj) _,
end

lemma exists_right_inverse_linear_map_of_surjective {f : β →ₗ[α] γ}
  (hf_surj : f.range = ⊤) : ∃g:γ →ₗ β, f.comp g = linear_map.id :=
begin
  rcases exists_is_basis α γ with ⟨C, hC⟩,
  haveI : inhabited β := ⟨0⟩,
  use hC.constr (function.restrict (inv_fun f) C : C → β),
  apply @is_basis.ext _ _ _ _ _ _ _ _ (show decidable_eq γ, by assumption) _ _ _ _ _ _ _ hC,
  intros c,
  simp [constr_basis hC],
  exact right_inverse_inv_fun (linear_map.range_eq_top.1 hf_surj) _
end

set_option class.instance_max_depth 49
open submodule linear_map
theorem quotient_prod_linear_equiv (p : submodule α β) :
  nonempty ((p.quotient × p) ≃ₗ[α] β) :=
begin
  haveI := classical.dec_eq (quotient p),
  rcases exists_right_inverse_linear_map_of_surjective p.range_mkq with ⟨f, hf⟩,
  have mkf : ∀ x, submodule.quotient.mk (f x) = x := linear_map.ext_iff.1 hf,
  have fp : ∀ x, x - f (p.mkq x) ∈ p :=
    λ x, (submodule.quotient.eq p).1 (mkf (p.mkq x)).symm,
  refine ⟨linear_equiv.of_linear (f.copair p.subtype)
    (p.mkq.pair (cod_restrict p (linear_map.id - f.comp p.mkq) fp))
    (by ext; simp) _⟩,
  ext ⟨⟨x⟩, y, hy⟩; simp,
  { apply (submodule.quotient.eq p).2,
    simpa using sub_mem p hy (fp x) },
  { refine subtype.coe_ext.2 _,
    simp [mkf, (submodule.quotient.mk_eq_zero p).2 hy] }
end

open fintype
variables (h : is_basis α v)

local attribute [instance] submodule.module

noncomputable def equiv_fun_basis [fintype ι] : β ≃ (ι → α) :=
calc β ≃ finsupp.supported α α (univ : set ι) : (module_equiv_finsupp h).to_equiv
   ... ≃ ((univ : set ι) →₀ α)                : finsupp.restrict_support_equiv _
   ... ≃ (ι →₀ α)                             : finsupp.dom_congr (equiv.set.univ ι)
   ... ≃ (ι → α)                              : finsupp.equiv_fun_on_fintype

theorem vector_space.card_fintype [fintype ι] [fintype α] [fintype β] :
  card β = (card α) ^ (card ι) :=
calc card β = card (ι → α)    : card_congr (equiv_fun_basis h)
        ... = card α ^ card ι : card_fun

theorem vector_space.card_fintype' [fintype α] [fintype β] :
  ∃ n : ℕ, card β = (card α) ^ n :=
begin
  apply exists.elim (exists_is_basis α β),
  intros b hb,
  haveI := classical.dec_pred (λ x, x ∈ b),
  use card b,
  exact vector_space.card_fintype hb,
end

end vector_space

namespace pi
open set linear_map

section module
variables {η : Type*} {ιs : η → Type*} {φ : η → Type*}
variables [ring α] [∀i, add_comm_group (φ i)] [∀i, module α (φ i)] [fintype η] [decidable_eq η]



lemma linear_independent_std_basis [∀ j, decidable_eq (ιs j)]  [∀ i, decidable_eq (φ i)]
  (s : Πj, ιs j → (φ j)) (hs : ∀i, linear_independent α (s i) univ) :
  linear_independent α (λ (ji : Σ j, ιs j), std_basis α φ ji.1 (s ji.1 ji.2)) univ :=
begin

lemma linear_independent_std_basis [∀ i, decidable_eq (φ i)]
  (s : Πi, set (φ i)) (hs : ∀i, linear_independent α id (s i)) :
  linear_independent α id (⋃i, std_basis α φ i '' s i) :=
begin
  refine linear_independent_Union_finite _ _,
  { assume i,
    refine (linear_independent_image_iff _).2 (hs i),
    simp only [ker_std_basis, disjoint_bot_right] },
  { assume i J _ hiJ,
    simp only [set.image_id],
    simp [(set.Union.equations._eqn_1 _).symm, submodule.span_image, submodule.span_Union],
    have h₁ : map (std_basis α φ i) (span α (s i)) ≤ (⨆j∈({i} : set η), range (std_basis α φ j)),
    { exact (le_supr_of_le i $ le_supr_of_le (set.mem_singleton _) $ map_mono $ le_top) },
    have h₂ : (⨆j∈J, map (std_basis α φ j) (span α (s j))) ≤ (⨆j∈J, range (std_basis α φ j)),
    { exact supr_le_supr (assume i, supr_le_supr $ assume hi, map_mono $ le_top) },
    exact disjoint_mono h₁ h₂
      (disjoint_std_basis_std_basis _ _ _ _ $ set.disjoint_singleton_left.2 hiJ) }
end

lemma is_basis_std_basis [fintype ι] [∀ j, decidable_eq (ιs j)] [∀ j, decidable_eq (φ j)]
  (s : Πj, ιs j → (φ j)) (hs : ∀j, is_basis α (s j)) :
  is_basis α (λ (ji : Σ j, ιs j), std_basis α φ ji.1 (s ji.1 ji.2)) :=
begin
  split,
  apply linear_independent.univ_of_id,
  { sorry },
  --{ apply linear_independent_std_basis },
end
 -- is_basis α (λ (ji : Σ j, ιs j), (std_basis α φ ji.1).to_fun  (s ji.1 ji.2)) :=
--begin
--  refine ⟨linear_independent_std_basis _ (assume i, (hs i).1), _⟩,
--  simp only [submodule.span_Union, submodule.span_image, (assume i, (hs i).2), submodule.map_top,
--    supr_range_std_basis]
--end

section
variables (α ι)
lemma is_basis_fun [fintype ι] : is_basis α (⋃i, std_basis α (λi:ι, α) i '' {1}) :=
is_basis_std_basis _ (assume i, is_basis_singleton_one _)
end

end module

end pi
