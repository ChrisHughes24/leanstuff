import data.num.lemmas

inductive poly : Type
| const : znum → poly
| add   : poly → poly → poly
| mul   : poly → poly → poly
| pow   : poly → num → poly
| var   : ℕ → poly

instance : has_pow poly num := ⟨poly.pow⟩
instance : has_add poly     := ⟨poly.add⟩
instance : has_mul poly     := ⟨poly.mul⟩

inductive horner_poly : Type
| const          : znum → horner_poly
-- The poly (f * X_i^n + b)
| horner (i : ℕ) (f : horner_poly) (n : pos_num) (b : horner_poly) : horner_poly

open poly horner_poly

@[simp] def add : horner_poly → horner_poly → horner_poly
| (const m) (const n) := const (m + n)
| f (horner i g n b)  := horner i g n (add _ _)
