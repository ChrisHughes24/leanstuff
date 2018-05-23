import linear_algebra.multivariate_polynomial
open finsupp
def uv_polynomial (α : Type*) [comm_semiring α] := ℕ →₀ α

namespace uv_polynomial
variables {α : Type*} {a a' a₁ a₂ : α} {e : ℕ} {n : ℕ}
variables [decidable_eq α]

section comm_semiring
variables [comm_semiring α] {p q : uv_polynomial α}

instance : has_zero (uv_polynomial α) := finsupp.has_zero
instance : has_one (uv_polynomial α) := finsupp.has_one
instance : has_add (uv_polynomial α) := finsupp.has_add
instance : has_mul (uv_polynomial α) := finsupp.has_mul
instance : comm_semiring (uv_polynomial α) := finsupp.to_comm_semiring

def monomial (n : ℕ) (a : α) : uv_polynomial α := single n a

def C (a : α) : uv_polynomial α := monomial 0 a

def X : uv_polynomial α := monomial 1 1

@[simp] lemma C_0 : C 0 = (0 : uv_polynomial α) := by simp [C, monomial]; refl

@[simp] lemma C_1 : C 1 = (1 : uv_polynomial α) := rfl

@[simp] lemma C_mul_monomial : C a * monomial n a' = monomial n (a * a') :=
by simp [C, monomial, single_mul_single]

lemma X_pow_eq_single : X ^ e = monomial e (1 : α) :=
begin
  induction e,
  { simp [X], refl },
  { simp [pow_succ, e_ih],
    simp [X, monomial, single_mul_single, nat.succ_eq_add_one] }
end

lemma monomial_add_right : monomial (n + e) a = (monomial n a * X ^ e):=
by rw [X_pow_eq_single, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_add_left : monomial (e + n) a = (X ^ e * monomial n a):=
by rw [X_pow_eq_single, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_eq : monomial e a = C a * X ^ e :=
by rw [X_pow_eq_single, C_mul_monomial, mul_one]

lemma induction_on {M : uv_polynomial α → Prop} (p : uv_polynomial α)
  (h_C : ∀a, M (C a)) (h_add : ∀p q, M p → M q → M (p + q)) (h_X : ∀p, M p → M (p * X)) :
  M p :=
have ∀n a, M (monomial n a),
begin
  assume n a,
  induction n with n ih,
  { exact h_C _ },
  { rw [← nat.add_one, monomial_add_right, pow_one],
    exact h_X _ ih }
end,
finsupp.induction p (show M (0 : uv_polynomial α), by rw ← C_0; exact h_C 0) $ 
λ n a f hfn ha ih, (show M (monomial n a + f), from h_add _ _ (this _ _) ih)

section eval
variable {x : α}

def eval (p : uv_polynomial α) (x : α) : α :=
p.sum (λ e a, a * x ^ e)

@[simp] lemma eval_zero : (0 : uv_polynomial α).eval x = 0 :=
finsupp.sum_zero_index

lemma eval_add : (p + q).eval x = p.eval x + q.eval x :=
finsupp.sum_add_index (by simp) (by simp [add_mul])

lemma eval_monomial : (monomial n a).eval x = a * x ^ n :=
finsupp.sum_single_index (zero_mul _)

@[simp] lemma eval_C : (C a).eval x = a :=
by simp [eval_monomial, C, prod_zero_index]

@[simp] lemma eval_X : X.eval x = x :=
by simp [eval_monomial, X, prod_single_index, pow_one]

lemma eval_mul_monomial :
  ∀{n a}, (p * monomial n a).eval x = p.eval x * a * x ^ n :=
begin
  apply uv_polynomial.induction_on p,
  { assume a' s a, by simp [C_mul_monomial, eval_monomial] },
  { assume p q ih_p ih_q, simp [add_mul, eval_add, ih_p, ih_q] },
  { assume p ih n a,
    from calc eval (p * X * monomial n a) x = eval (p * monomial (1 + n) a) x :
        by simp [monomial_add_left, -add_comm, pow_one, mul_assoc]
      ... = eval (p * X) x * a * x ^ n :
        by simp [ih, X, pow_add, mul_assoc, mul_comm, mul_left_comm] }
end

lemma eval_mul : ∀{p}, (p * q).eval x = p.eval x * q.eval x :=
begin
  apply uv_polynomial.induction_on q,
  { simp [C, eval_monomial, eval_mul_monomial, prod_zero_index] },
  { simp [mul_add, eval_add] {contextual := tt} },
  { simp [X, eval_monomial, eval_mul_monomial, (mul_assoc _ _ _).symm] { contextual := tt} }
end

end eval

section degree_of
/-- `degree_of n p` gives the highest power of X_n that appears in `p` -/
def degree_of (p : uv_polynomial α) : ℕ := p.support.sup id

end degree_of

end comm_semiring

section comm_ring
variable [comm_ring α]
instance : ring (uv_polynomial α) := finsupp.to_ring
instance : has_scalar α (uv_polynomial α) := finsupp.to_has_scalar
instance : module α (uv_polynomial α) := finsupp.to_module

end comm_ring

end uv_polynomial
