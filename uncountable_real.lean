import topology.separation topology.subset_properties tactic.push_neg data.real.basic
import analysis.complex.exponential

open function set finset

local attribute [instance] classical.dec
noncomputable theory

def set_nat_to_seq (s : set ℕ) (n : ℕ) : ℝ := if n ∈ s then (3⁻¹)^n else 0
--#print cauchy_seq
lemma is_cau_seq_set_nat_to_seq (s : set ℕ) : is_cau_seq abs
  (λ n, (range n).sum (set_nat_to_seq s)) :=
is_cau_series_of_abv_le_cau 0 (λ m hm, show abs (set_nat_to_seq s m) ≤ ((3 : ℝ)⁻¹) ^ m,
    from if h : m ∈ s then by simp [set_nat_to_seq, h,
      abs_of_nonneg (pow_nonneg (inv_nonneg.2 (show (3 : ℝ) ≥ 0, by norm_num)) _)]
    else by rw [set_nat_to_seq, if_neg h, abs_zero];
      exact pow_nonneg (inv_nonneg.2 (by norm_num)) _)
  (is_cau_geo_series (3⁻¹ : ℝ) (by rw [abs_of_nonneg]; norm_num))

def set_nat_to_cau_seq (s : set ℕ) : cau_seq ℝ abs := ⟨_, is_cau_seq_set_nat_to_seq s⟩

lemma lim_set_nat_to_seq_injective_mul_three_pow_eq (s : set ℕ) : ∀ (n : ℕ),
  ⌊cau_seq.lim (set_nat_to_cau_seq s) * 3^n⌋ = (range n).sum (λ m, if m ∈ s then 3^(n-m) else 0)
| 0     := by simp
| (n+1) := _
#print set.Inter
#print compact_elim_finite_subcover_image
variables {α : Type*} [topological_space α]

lemma cantor_intersection (c : ℕ → set α) (hc : ∀ n, compact (c n))
  (hn : ∀ n, c n ≠ ∅) (hmono : ∀ m n, m ≤ n → c n ⊆ c m) : (⋂ n, c n) ≠ ∅ :=
λ h,
let U : Π n:ℕ, set α := λ n, c 0 \ c n in
-- have hU : ∀ n : ℕ, (⋃ (m : ℕ) (hm : n ≤ m), U m) = c 0 \ ⋂ (m : ℕ) (hm : n ≤ m), c m,
--   from λ n, by simp only [diff_Inter_left, U],
have ∀ x : α, ∃ n, x ∉ c n, by simpa [set.ext_iff, classical.not_forall] using h,
have (⋃ (n : ℕ) (h : n ∈ @univ ℕ), U n) = c 0, by simp [set.ext_iff, this],
have hc : compact (⋂ n, c n), from sorry,
have hU : ∀ n, n ∈ @univ ℕ → is_open (U n), from λ _ _, is_open_diff _ _,
let ⟨s, hs⟩ := compact_elim_finite_subcover_image hc
  _ _ in
begin


end

local attribute [instance] classical.dec
--#print not_mem_closure

lemma exists_subset_not_mem_closure [t2_space α] (h : ∀ x : α, ¬ is_open ({x} : set α)) :
  ∀ x : α, ∀ U : set α, is_open U → U ≠ ∅ → ∃ V ⊆ U, x ∉ closure V ∧ V ≠ ∅ :=
λ x U hU hUn,
have hUxn : U \ {x} ≠ ∅, from mt diff_eq_empty.1 $
  λ hUx, if hxU : x ∈ U
    then h x $ by convert hU; exact set.subset.antisymm (by simpa) hUx
    else hUn $ eq_empty_iff_forall_not_mem.2
      (λ y hy, hxU $ by convert hy; simpa [eq_comm] using hUx hy),
let ⟨y, hy⟩ := set.exists_mem_of_ne_empty hUxn in
let ⟨W₁, W₂, hW₁o, hW₂o, hxW, hyW, hW⟩ := t2_space.t2 x y (by finish) in
⟨W₂ ∩ U, inter_subset_right _ _, begin
  rw mem_closure_iff,
  push_neg,
  exact ⟨W₁, hW₁o, hxW, by rw [← inter_assoc, hW, empty_inter]⟩,
end, set.ne_empty_of_mem ⟨hyW, hy.1⟩⟩

def uncountable_space_aux [t2_space α] [nonempty α] (h : ∀ x : α, ¬ is_open ({x} : set α)) (f : ℕ → α) :
  Π n : ℕ,  {s : set α // is_closed s ∧ f n ∉ s ∧ s ≠ ∅}
| 0     := have h : _ := exists_subset_not_mem_closure h (f 0)
    univ is_open_univ (by simp),
  ⟨closure (classical.some h), is_closed_closure, (classical.some_spec h).snd.1,
    λ hV, (classical.some_spec h).snd.2 (eq_empty_of_subset_empty $
      by convert subset_closure; exact hV.symm)⟩
| (n+1) := have h : _ := exists_subset_not_mem_closure h (f (n+1))
    (-uncountable_space_aux n) (is_open_compl_iff.2
    (uncountable_space_aux n).2.1)
    (set.ne_empty_of_mem (uncountable_space_aux n).2.2.1),
  ⟨closure (classical.some h), is_closed_closure, (classical.some_spec h).snd.1,
    λ hV, (classical.some_spec h).snd.2 (eq_empty_of_subset_empty $
      by convert subset_closure; exact hV.symm)⟩

lemma uncountable [compact_space α] [t2_space α]
  [n : nonempty α] (h : ∀ x : α, ¬ is_open ({x} : set α)) (f : ℕ → α) : ¬surjective f :=
let ⟨x⟩ := n in
λ h, let ⟨y, hy⟩ := _ in
