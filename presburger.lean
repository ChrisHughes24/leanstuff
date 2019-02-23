import data.set.basic

inductive presburger_equation : Type
|


inductive presburger : Π n, (set (fin n → ℕ)) → Prop
| empty (n : ℕ) : presburger n ∅
| union (n : ℕ) (s t : set (fin n → ℕ)) : presburger n s →
  presburger n t → presburger n (s ∪ t)
| inter (n : ℕ) (s t : set (fin n → ℕ)) : presburger n s →
  presburger n t → presburger n (s ∪ t)