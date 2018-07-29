import group_theory.subgroup data.equiv.basic data.fintype algebra.big_operators
open equiv
variables {α : Type*}

def is_transposition (f : perm α) : Prop := 
∃ x y, f x = y ∧ f y = x ∧ ∀ a, a ≠ x → a ≠ y → f a = a

lemma is_transposition_inv {f : perm α} : is_transposition f → 
  is_transposition (f⁻¹) :=
λ ⟨x, y, h⟩, ⟨x, y, h.2.1 ▸ equiv.left_inv _ _, h.1 ▸ equiv.left_inv _ _,
  λ a hax hay, by conv {to_lhs, rw ← h.2.2 a hax hay}; 
    exact equiv.left_inv _ _⟩

variable [fintype α]

lemma product_of_transpositions (f : perm α) : ∃ s : list (perm α), 
  f = s.prod ∧ ∀ g ∈ s, is_transposition g := sorry

lemma sign_well_defined_aux : ∀ (n : ℕ) (f : perm α) (m l : list (perm α)),
  (∀ g ∈ l, is_transposition g) → l.prod = f → l.length = n →
  (∀ g ∈ m, is_transposition g) → m.prod = f → l.length % 2 = m.length % 2 
| 0 := λ f m,
  match m with
  | [] := by simp {contextual := tt}
  | (k :: m) := λ l hl hlf hl0, begin 
     
    end
  end
lemma sign_well_defined (f : perm α) : 
  (∀ l : list (perm α), (∀ g ∈ l, is_transposition g) → l.prod = f → l.length % 2 = 0) ∨
  (∀ l : list (perm α), (∀ g ∈ l, is_transposition g) → l.prod = f → l.length % 2 = 0) :=
have ∀ n : ℕ, ∀ l m : list (perm α), (∀ g ∈ l, is_transposition g) → l.prod = f → l.length = n
  (∀ g ∈ m, is_transposition g) → m.prod = f → l.length % 2 = m.length % 2 | 0 :=
begin




end