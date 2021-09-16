import group_theory.free_group group_theory.subgroup

variables {α : Type*} {β : Type*} [decidable_eq α] (T : set α) (r : free_group α)

open group subgroup free_group




def blah (t : α) : free_group α →* free_group unit :=
to_group (λ a, if a = t then of () else 1)

instance {α : Type*} [subsingleton α] : comm_group (free_group α) :=
{ mul_comm := λ a b, sorry,
  ..free_group.group }

def ker_blah_free (t : α) (e : α ≃ option β) (he : e.symm none = t) :
  free_group (β × ℤ) ≃* (blah t).ker :=
{ to_fun := free_group.to_group
    (λ b : β × ℤ, (⟨of t ^ b.2 * of (e.symm (some b.1)) * of t ^ -b.2,
      monoid_hom.mem_ker.2 begin
        rw [monoid_hom.map_mul, monoid_hom.map_mul, mul_right_comm,
          ← monoid_hom.map_mul, ← gpow_add, add_neg_self],
        simp [blah, he.symm]
      end⟩ : (blah t).ker)),
  inv_fun := λ x, begin
    have := x.1,

  end,  }

@[elab_as_eliminator]
lemma normal_closure_induction {G : Type*} [group G] {P : G → Prop} {x : G} {s : set G}
  (h : x ∈ subgroup.normal_closure s)
  (hs : ∀ x ∈ s, P x)
  (h1 : P 1)
  (hmul : ∀ x ∈ s, ∀ y, P y → P (x * y))
  (hinv : ∀ x ∈ s, P x → P x⁻¹) : P x := sorry

theorem freiheitsatz (x : free_group α)
  (hxr : x ∈ subgroup.normal_closure ({r} : set (free_group α)))
  (hxT : x ∈ subgroup.normal_closure (free_group.of '' T)) (hx1 : x ≠ 1) :
  r ∈ subgroup.normal_closure (free_group.of '' T) :=
begin
  revert hxT hx1,
  refine normal_closure_induction hxr _ _ _ _,
  { assume x,
    simp {contextual := tt} },
  { simp },
  { simp only [set.mem_singleton_iff, forall_eq, ne.def] {contextual := tt},
    assume y hy hry, generalize hz : r * y = z, rw hz at hry, clear hxr, revert hz hy y r,
    refine normal_closure_induction hry _ _ _ _,
    { rintros _ ⟨a, haT, rfl⟩ r y ih, }
   },


end
-- begin
--   revert hxr hxT,
--   refine free_group.induction_on r _ _ _ _ x,
--   { intros,
--     exact is_submonoid.one_mem },
--   { assume r x hxr hxT,
--     sorry },
--   { assume y ih x hxr hxT, sorry,
--      },
--   { intros, }
-- end
