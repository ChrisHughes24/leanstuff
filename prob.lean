import data.real.basic tactic.find
variables {Ω : Type*} {α : Type*}
open set
local attribute [instance] classical.prop_decidable
noncomputable theory

lemma union_diff_eq_union (s t : set α) 
    : s ∪ (t \ s) = s ∪ t := set.ext $ λ x, 
or.by_cases (classical.em (x ∈ s)) (λ h, by simp [h]) (λ h, by simp [h])

@[simp] lemma diff_disjoint (s t : set α) : disjoint (s \ t) t :=
show (s ∩ -t) ∩ t = ∅, from (inter_assoc s (-t) t).symm ▸ 
(compl_inter_self t).symm ▸ inter_empty s

@[simp] lemma disjoint_diff (s t : set α) : disjoint s (t \ s) :=
disjoint_symm (diff_disjoint _ _)

variables [iα : discrete_linear_ordered_field α] (P : set Ω → α) 
include iα

class prob : Prop :=
(prob_nonneg : ∀ E : set Ω, 0 ≤ P E)
(prob_univ : P univ = 1)
(prob_add : ∀ {E₁ E₂ : set Ω}, disjoint E₁ E₂ → P (E₁ ∪ E₂) = P E₁ + P E₂)

attribute [simp] prob.prob_univ

namespace prob
variables [hP : prob P] 
include hP

@[simp] lemma union_compl_self (E : set Ω) : P (E ∪ -E) = 1 := 
eq.symm (set.union_compl_self E) ▸ prob_univ _

@[simp] lemma compl_union_self (E : set Ω) : P (-E ∪ E) = 1 := 
(set.compl_union_self E).symm ▸ prob_univ _

lemma subset_le {E₁ E₂ : set Ω} (h : E₁ ⊆ E₂) : P E₁ ≤ P E₂ :=
union_diff_cancel h ▸ (prob_add P (disjoint_diff E₁ E₂)).symm ▸ 
le_add_of_nonneg_right (prob_nonneg _ _)

lemma le_union_left (E₁ E₂ : set Ω) : P E₁ ≤ P (E₁ ∪ E₂) :=
subset_le P (subset_union_left _ _)

lemma le_union_right (E₁ E₂ : set Ω) : P E₂ ≤ P (E₁ ∪ E₂) :=
subset_le P (subset_union_right _ _)

lemma le_one (E : set Ω) : P E ≤ 1 :=
prob_univ P ▸ subset_le P (subset_univ _)

lemma inter_le_left (E₁ E₂ : set Ω) : P (E₁ ∩ E₂) ≤ P E₁ :=
subset_le P (inter_subset_left _ _)

lemma inter_le_right (E₁ E₂ : set Ω) : P (E₁ ∩ E₂) ≤ P E₂ :=
subset_le P (inter_subset_right _ _)

@[simp] lemma empty : P ∅ = 0 := 
have h : P (univ ∪ ∅) = P univ + P ∅ := prob_add P (inter_empty univ),
by rwa [union_empty, prob_univ P, ← add_zero (1 : α), 
      add_assoc, add_left_cancel_iff, zero_add, eq_comm] at h

def given (E₁ E₂ : set Ω) := P (E₁ ∩ E₂) / P E₂


#print mul_comm
end