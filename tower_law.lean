import ring_theory.algebra_operations linear_algebra.dimension ring_theory.noetherian

universes u v w
section
variables {α : Type*} {β : Type*} [comm_ring α] [comm_ring β] [algebra α β]
variables {γ : Type w} [add_comm_group γ] [module α γ] [module β γ]
open submodule
#print nat.to_digits
lemma span_subset_span {s : set γ} : (span α s : set γ) ⊆ span β s :=
λ x hx, span_induction hx
  (λ _ h, subset_span h)
  (zero_mem (span β s))
  (λ _ _, add_mem (span β s))
  (λ x y h, begin
    have : algebra_map β x • y = x • y, from _,
    simp at this,
  end)

lemma span_subset_ideal_span {s : set β} : (span α s).carrier ⊆ (ideal.span s).carrier :=
λ x hx, span_induction hx
  (λ _ h, ideal.subset_span h)
  (ideal.zero_mem (ideal.span s))
  (λ _ _, ideal.add_mem (ideal.span s))
  (λ x y h, by rw algebra.smul_def;
    exact ideal.mul_mem_left (ideal.span s) h)




open vector_space submodule
-- set_option trace.class_instances true
-- set_option class.instance_max_depth 40
#print span_smul_span

lemma tower_law (s : set β) (t : set γ) (hs : span α s = ⊤) (ht : span β t = ⊤) :
  span α (⋃ (x ∈ s) (y ∈ t), {x • y} : set γ) = ⊤ :=
have h : ideal.span s = ⊤, from (ideal.eq_top_iff_one _).2
  (span_subset_ideal_span (eq_top_iff'.1 hs _)),
calc span α (⋃ (x ∈ s) (y ∈ t), {x • y} : set γ) =
  span α (span β (⋃ (x ∈ s) (y ∈ t), {x • y} : set γ)) :
le_antisymm (span_mono subset_span)
  (λ y hy, _)
... = span α
    ((ideal.span s • span β t) : submodule β γ) :
  by rw span_smul_span
... = _ : _

end
