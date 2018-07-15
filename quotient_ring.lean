import ring_theory.ideals linear_algebra.quotient_module tactic.ring

open set function

universes u v w
variables {α : Type u} {β : Type v} [comm_ring α] [comm_ring β] {a b : α}

namespace is_ideal

lemma zero (S : set α) [is_ideal S] : (0 : α) ∈ S := is_submodule.zero_ α S

lemma add {S : set α} [is_ideal S] : a ∈ S → b ∈ S → a + b ∈ S := is_submodule.add_ α

lemma neg_iff {S : set α} [is_ideal S] : a ∈ S ↔ -a ∈ S := ⟨is_submodule.neg, λ h, neg_neg a ▸ is_submodule.neg h⟩

lemma sub {S : set α} [is_ideal S] : a ∈ S → b ∈ S → a - b ∈ S := is_submodule.sub

lemma mul_left {S : set α} [is_ideal S] : b ∈ S → a * b ∈ S := @is_submodule.smul α α _ _ _ _ a _

lemma mul_right {S : set α} [is_ideal S] : a ∈ S → a * b ∈ S := mul_comm b a ▸ mul_left

def quotient_rel (S : set α) [is_ideal S] := is_submodule.quotient_rel S

local attribute [instance] quotient_rel

def quotient (S : set α) [is_ideal S] := quotient (quotient_rel S)

instance (S : set α) [is_ideal S] : comm_ring (quotient S) :=
{ mul := λ a b, quotient.lift_on₂ a b (λ a b, ⟦a * b⟧) 
  (λ a₁ a₂ b₁ b₂ (h₁ : a₁ - b₁ ∈ S) (h₂ : a₂ - b₂ ∈ S), 
    quotient.sound
    (show a₁ * a₂ - b₁ * b₂ ∈ S, from
    have h : a₂ * (a₁ - b₁) + (a₂ - b₂) * b₁ =
      a₁ * a₂ - b₁ * b₂, by ring,
    h ▸ add (mul_left h₁) (mul_right h₂))),
  mul_assoc := λ a b c, quotient.induction_on₃ a b c $ 
    λ a b c, show ⟦_⟧ = ⟦_⟧, by rw mul_assoc,
  mul_comm := λ a b, quotient.induction_on₂ a b $
    λ a b, show ⟦_⟧ = ⟦_⟧, by rw mul_comm,
  one := ⟦1⟧,
  one_mul := λ a, quotient.induction_on a $
    λ a, show ⟦_⟧ = ⟦_⟧, by rw one_mul,
  mul_one := λ a, quotient.induction_on a $
    λ a, show ⟦_⟧ = ⟦_⟧, by rw mul_one,
  left_distrib := λ a b c, quotient.induction_on₃ a b c $ 
    λ a b c, show ⟦_⟧ = ⟦_⟧, by rw mul_add,
  right_distrib := λ a b c, quotient.induction_on₃ a b c $ 
    λ a b c, show ⟦_⟧ = ⟦_⟧, by rw add_mul,
  ..is_submodule.quotient.add_comm_group S }

lemma is_proper_ideal_iff_one_not_mem {S : set α} [hS : is_ideal S] : 
  is_proper_ideal S ↔ (1 : α) ∉ S :=
⟨λ h h1, by exactI is_proper_ideal.ne_univ S 
  (eq_univ_iff_forall.2 (λ a, mul_one a ▸ mul_left h1)), 
λ h, {ne_univ := mt eq_univ_iff_forall.1 (λ ha, h (ha _)), ..hS}⟩

lemma quotient_eq_zero_iff_mem {S : set α} [is_ideal S] : ⟦a⟧ = (0 : quotient S) ↔ a ∈ S :=
by conv {to_rhs, rw ← sub_zero a }; exact quotient.eq

instance (S : set α) [is_prime_ideal S] : integral_domain (quotient S) :=
{ zero_ne_one := ne.symm $ mt quotient_eq_zero_iff_mem.1 
    (is_proper_ideal_iff_one_not_mem.1 (by apply_instance)),
  eq_zero_or_eq_zero_of_mul_eq_zero := λ a b,
    quotient.induction_on₂ a b $ λ a b hab,
      (is_prime_ideal.mem_or_mem_of_mul_mem 
        (quotient_eq_zero_iff_mem.1 hab)).elim
      (or.inl ∘ quotient_eq_zero_iff_mem.2)
      (or.inr ∘ quotient_eq_zero_iff_mem.2),
  ..is_ideal.comm_ring S }

instance (S : set α) : is_ideal (span S) :=
{ ..show is_submodule (span S), by apply_instance }

lemma exists_inv {S : set α} [is_maximal_ideal S] {a : quotient S} : a ≠ 0 →
  ∃ b : quotient S, a * b = 1 :=
quotient.induction_on  a $ λ a ha,
classical.by_contradiction $ λ h,
have haS : a ∉ S := mt quotient_eq_zero_iff_mem.2 ha,
by haveI hS : is_proper_ideal (span (set.insert a S)) :=
  is_proper_ideal_iff_one_not_mem.2
  (mt mem_span_insert.1 $ λ ⟨b, hb⟩,
  h ⟨-⟦b⟧, quotient.sound (show a * -b - 1 ∈ S,
    from neg_iff.2 (begin
      rw [neg_sub, mul_neg_eq_neg_mul_symm, sub_eq_add_neg, neg_neg, mul_comm],
      rw span_eq_of_is_submodule (show is_submodule S, by apply_instance) at hb,
      exact hb
    end))⟩);
exact
  have span (set.insert a S) = S :=
    or.resolve_right (is_maximal_ideal.eq_or_univ_of_subset (span (set.insert a S))
    (subset.trans (subset_insert _ _) subset_span)) (is_proper_ideal.ne_univ _),
  haS (this ▸ subset_span (mem_insert _ _))

local attribute [instance] classical.prop_decidable

/-- quotient by maximal ideal is a field. A definition rather than an instance, since
it is noncomputable, and users may have a computable inverse in some applications-/
noncomputable def field (S : set α) [is_maximal_ideal S] : field (quotient S) :=
{ zero_ne_one := ne.symm $ mt quotient_eq_zero_iff_mem.1 
    (is_proper_ideal_iff_one_not_mem.1 (by apply_instance)),
  inv := λ a, if ha : a = 0 then 0 else classical.some (exists_inv ha),
  mul_inv_cancel := λ a (ha : a ≠ 0), show a * dite _ _ _ = _, 
    by rw dif_neg ha;
    exact classical.some_spec (exists_inv ha),
  inv_mul_cancel := λ a (ha : a ≠ 0), show dite _ _ _ * a = _, 
    by rw [mul_comm, dif_neg ha];
    exact classical.some_spec (exists_inv ha),
  ..is_ideal.comm_ring S }

instance is_ring_hom_quotient_mk (S : set α) [is_ideal S] : 
  @is_ring_hom _ (quotient S) _ _ quotient.mk :=
by refine {..}; intros; refl

end is_ideal