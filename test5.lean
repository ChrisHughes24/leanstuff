import data.real.cardinality group_theory.quotient_group

instance rat_cast_is_add_group_hom : is_add_group_hom (coe : ℚ → ℝ) :=
{ to_is_add_hom := { map_add := by simp } }

noncomputable lemma real_equiv_real_mod_rat : ℝ ≃ quotient_add_group.quotient
  (set.range (coe : ℚ → ℝ)) :=
calc ℝ ≃ quotient_add_group.quotient (set.range (coe : ℚ → ℝ)) ×
  (set.range (coe : ℚ → ℝ)) : is_add_subgroup.add_group_equiv_quotient_times_subgroup _
... ≃ _ : quotient_add_group.quotient (set.range (coe : ℚ → ℝ))
#exit