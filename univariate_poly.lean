import linear_algebra.multivariate_polynomial data.set.finite
open finsupp finset

class is_nonzero (α : Type*) [has_one α] [has_zero α] : Prop :=
(zero_ne_one : (0 : α) ≠ 1)

class nonzero_comm_ring (α : Type*) extends comm_ring α, is_nonzero α

instance integral_domain.to_nonzero_ring (α : Type*) [hd : integral_domain α] : nonzero_comm_ring α :=
{ ..hd }

namespace finset

lemma sup_lt_nat : ∀ {s t : finset ℕ}, s ⊆ t → t.sup id ∉ s
  → 0 < t.sup id → s.sup id < t.sup id :=
λ s, finset.induction_on s (λ _ _ _, id) begin
  assume a s has ih t hst hsup hpos,
  rw finset.sup_insert,
  exact max_lt_iff.2 ⟨lt_of_le_of_ne (finset.le_sup (hst (finset.mem_insert_self _ _))) 
      (λ h, by simpa [h.symm] using hsup),
    ih (λ a ha, hst (finset.mem_insert_of_mem ha))
      (hsup ∘ finset.mem_insert_of_mem) hpos⟩,
end

lemma sup_mem_nat {s : finset ℕ} : s ≠ ∅ → s.sup id ∈ s :=
finset.induction_on s (by simp * at *) $
begin
  assume a s has ih _,
  by_cases h₁ : s = ∅,
  { simp * },
  { cases (le_total a (s.sup id)) with h₂ h₂,
    { simp [lattice.sup_of_le_right h₂, ih h₁] },
    { simp [lattice.sup_of_le_left h₂] } }
end

end finset

namespace set

@[simp] theorem card_insert_le {α : Type*} [decidable_eq α] {a : α} (s : set α) [fintype s] 
  [hf : fintype (insert a s : set α)] : fintype.card (insert a s : set α) ≤ fintype.card s + 1 :=
if h : a ∈ s then calc fintype.card ↥(insert a s) = fintype.card s 
          : by congr; exact set.insert_eq_of_mem h
  ... ≤ _ : nat.le_succ _
else calc @fintype.card ↥(insert a s) hf = 
      @fintype.card ↥(insert a s) (set.fintype_insert a s) : by congr
  ... = fintype.card s + 1 : set.card_insert _ h
  ... ≤ _ : le_refl _

end set

namespace finsupp

lemma erase_single {α β : Type*} [decidable_eq α] [decidable_eq β] [has_zero β]
  (a : α) (b : β) : (single a b).erase a = (0 : α →₀ β) := 
ext (λ x, begin 
  by_cases hxa : x = a,
  { simp [hxa, erase_same] },
  { simp [erase_ne hxa, single_apply, if_neg (ne.symm hxa)] },
end)

end finsupp

def polynomial (α : Type*) [comm_semiring α] := ℕ →₀ α

namespace polynomial
variables {α : Type*} {a b c d : α} {m n : ℕ} 
variables [decidable_eq α]

section comm_semiring
variables [comm_semiring α] {p q : polynomial α}

instance : has_coe_to_fun (polynomial α) := finsupp.has_coe_to_fun
instance : has_zero (polynomial α) := finsupp.has_zero
instance : has_one (polynomial α) := finsupp.has_one
instance : has_add (polynomial α) := finsupp.has_add
instance : has_mul (polynomial α) := finsupp.has_mul
instance : comm_semiring (polynomial α) := finsupp.to_comm_semiring

local attribute [instance] finsupp.to_comm_semiring

def monomial (n : ℕ) (a : α) : polynomial α := single n a

def C (a : α) : polynomial α := monomial 0 a

def X : polynomial α := monomial 1 1

@[simp] lemma C_0 : C 0 = (0 : polynomial α) := by simp [C, monomial]; refl

@[simp] lemma C_1 : C 1 = (1 : polynomial α) := rfl

@[simp] lemma C_mul_monomial : C a * monomial n b = monomial n (a * b) :=
by simp [C, monomial, single_mul_single]

@[simp] lemma C_mul_C : C a * C b = C (a * b) :=
by simp [C, monomial, single_mul_single]

@[simp] lemma monomial_mul_monomial : monomial n a * monomial m b = monomial (n + m) (a * b) :=
single_mul_single

@[simp] lemma monomial_zero_right (n : ℕ) : monomial n (0 : α) = 0 := 
by ext; simp [monomial]; refl

lemma X_pow_eq_monomial : X ^ n = monomial n (1 : α) :=
begin
  induction n,
  { simp [X], refl },
  { simp [pow_succ, n_ih],
    simp [X, monomial, single_mul_single, nat.succ_eq_add_one] }
end

lemma monomial_add_right : monomial (n + m) a = (monomial n a * X ^ m):=
by rw [X_pow_eq_monomial, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_add_left : monomial (m + n) a = (X ^ m * monomial n a):=
by rw [X_pow_eq_monomial, monomial, monomial, monomial, single_mul_single]; simp

lemma monomial_eq : monomial n a = C a * X ^ n :=
by rw [X_pow_eq_monomial, C_mul_monomial, mul_one]

lemma erase_monomial : (monomial n a).erase n = 0 := finsupp.erase_single _ _

@[elab_as_eliminator] lemma induction_on {M : polynomial α → Prop} (p : polynomial α)
  (h_C : ∀a, M (C a)) (h_add : ∀p q, M p → M q → M (p + q)) 
  (h_X : ∀(n : ℕ) (a : α), M (monomial n a) → M (monomial n a * X)) :
  M p :=
have ∀n a, M (monomial n a),
begin
  assume n a,
  induction n with n ih,
  { exact h_C _ },
  { rw [← nat.add_one, monomial_add_right, pow_one],
    exact h_X _ _ ih }
end,
finsupp.induction p (show M (0 : polynomial α), by rw ← C_0; exact h_C 0) $ 
λ n a f hfn ha ih, (show M (monomial n a + f), from h_add _ _ (this _ _) ih)

lemma monomial_apply : @coe_fn (polynomial α) polynomial.has_coe_to_fun (monomial n a) m = ite (n = m) a 0 :=
finsupp.single_apply

lemma C_apply : @coe_fn (polynomial α) polynomial.has_coe_to_fun (C a) n = ite (0 = n) a 0 := finsupp.single_apply

lemma add_apply (p q : polynomial α) (n : ℕ) : (p + q) n = p n + q n := add_apply

@[simp] lemma C_mul_apply (p : polynomial α) : (C a * p) n = a * p n :=
induction_on p (λ b, show (monomial 0 a * monomial 0 b) n = a * 
  @coe_fn (polynomial α) polynomial.has_coe_to_fun (monomial 0 b) n,
  begin 
    rw [monomial_mul_monomial, monomial_apply, monomial_apply],
    split_ifs; simp
  end) begin 
    intros, 
    rw [mul_add, add_apply, add_apply, mul_add], 
    simp *,
  end begin
    intros,
    rw [X, monomial_mul_monomial, C, monomial_mul_monomial, monomial_apply, monomial_apply],
    split_ifs;
    simp * at *,
  end

@[elab_as_eliminator] lemma induction_on' {M : polynomial α → Prop} (p : polynomial α)
  (h0 : M 0) 
  (h : ∀ (n : ℕ) (a : α) (p : polynomial α), p n = 0 → a ≠ 0 → M p → 
  M (monomial n a + p)) : M p :=
finsupp.induction p h0 (λ n a p hpn, h n a p (by rwa [mem_support_iff, ne.def, not_not] at hpn))

section eval
variable {x : α}

def eval (x : α) (p : polynomial α) : α :=
p.sum (λ e a, a * x ^ e)

@[simp] lemma eval_zero : (0 : polynomial α).eval x = 0 :=
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
  apply polynomial.induction_on p,
  { assume a' s a, by simp [C_mul_monomial, eval_monomial] },
  { assume p q ih_p ih_q, simp [add_mul, eval_add, ih_p, ih_q] },
  { assume m b ih n a,
    unfold X,
    rw [mul_assoc, ih, monomial_mul_monomial, ih, pow_add],
    simp [mul_assoc, mul_comm, mul_left_comm] }
end

lemma eval_mul : ∀{p}, (p * q).eval x = p.eval x * q.eval x :=
begin
  apply polynomial.induction_on q,
  { simp [C, eval_monomial, eval_mul_monomial, prod_zero_index] },
  { simp [mul_add, eval_add] {contextual := tt} },
  { simp [X, eval_monomial, eval_mul_monomial, (mul_assoc _ _ _).symm] { contextual := tt} }
end

def root (p : polynomial α) (a : α) : Prop := p.eval a = 0

lemma root.def : root p a ↔ p.eval a = 0 := iff.rfl

lemma root_mul_left_of_root (q : polynomial α) : root p a → root (q * p) a :=
by simp [root, eval_mul] {contextual := tt}

lemma root_mul_right_of_root (q : polynomial α) : root p a → root (p * q) a :=
by simp [root, eval_mul] {contextual := tt}

end eval
/-- `degree n p` gives the highest power of X that appears in `p` -/
def degree (p : polynomial α) : ℕ := p.support.sup id

def leading_coeff (p : polynomial α) : α := p (degree p)

def monic (p : polynomial α) := leading_coeff p = (1 : α)

@[simp] lemma degree_zero : degree (0 : polynomial α) = 0 := rfl

@[simp] lemma degree_C (a : α) : degree (C a) = 0 := 
begin
  unfold C single monomial degree finsupp.support,
  by_cases a = 0;
  simp *;
  refl
end

lemma degree_monomial_le (n : ℕ) (a : α) : degree (monomial n a) ≤ n :=
begin
  unfold single monomial degree finsupp.support,
  by_cases a = 0;
  simp [*, sup];
  refl
end

@[simp] lemma degree_monomial (n : ℕ) (ha : a ≠ 0) : degree (monomial n a) = n :=
begin
  unfold X single monomial degree finsupp.support,
  rw if_neg ha,
  simp [sup]
end

lemma le_degree_ne_zero (h : p n ≠ 0) : n ≤ degree p :=
show id n ≤ p.support.sup id,
from finset.le_sup ((finsupp.mem_support_iff _ _).2 h)

lemma eq_zero_of_degree_lt (h : degree p < n) : p n = 0 :=
not_not.1 (mt le_degree_ne_zero (not_le_of_gt h))

lemma eq_C_of_degree_eq_zero (h : degree p = 0) : p = C (p 0) := 
ext begin
  assume n,
  cases n,
  { refl },
  { have h : degree p < nat.succ n := h.symm ▸ nat.succ_pos _,
    rw [eq_zero_of_degree_lt h, C_apply, if_neg],
    exact λ h, nat.no_confusion h }
end

lemma degree_add_le (p q : polynomial α) : 
  degree (p + q) ≤ max (degree p) (degree q) :=
show _ ≤ (finset.sup (p.support) id) ⊔ (finset.sup (q.support) id),
by rw ← finset.sup_union;
  exact finset.sup_mono support_add

--stolen
lemma degree_sum_le {β : Type*} [decidable_eq β] (s : finset β) (f : β → polynomial α) :
  degree (s.sum f) ≤ s.sup (λi, degree (f i)) :=
finset.induction_on s (by simp; refl) $
  assume b s hbs ih,
  calc degree ((insert b s).sum f) = degree (f b + s.sum f) : by simp [hbs]
    ... ≤ degree (f b) ⊔ degree (s.sum f) : degree_add_le _ _
    ... ≤ degree (f b) ⊔ s.sup (λi, degree (f i)) : lattice.sup_le_sup (le_refl _) ih
    ... = (insert b s).sup (λi, degree (f i)) : by simp

--stolen
lemma degree_mul_le (f g : polynomial α) : degree (f * g) ≤ degree f + degree g :=
calc degree (f * g) ≤ _ : degree_sum_le _ _
  ... ≤ _ : finset.sup_mono_fun $ assume a ha, degree_sum_le _ _
  ... ≤ _ : finset.sup_le $ assume b₁ hb₁, finset.sup_le $ assume b₂ hb₂,
    calc _ ≤ b₁ + b₂ : degree_monomial_le _ _
      ... ≤ degree f + degree g : add_le_add (finset.le_sup hb₁) (finset.le_sup hb₂)

lemma degree_erase_le (p : polynomial α) (n : ℕ) : degree (p.erase n) ≤ degree p :=
sup_mono (erase_subset _ _)

lemma degree_erase_lt (h : 0 < degree p) : 
  degree (p.erase (degree p)) < degree p :=
finset.sup_lt_nat (erase_subset _ _) (not_mem_erase _ _) h

lemma monic.def : monic p ↔ leading_coeff p = 1 := iff.rfl

lemma leading_coeff_ne_zero (h : p ≠ 0) :
  leading_coeff p ≠ 0 :=
(mem_support_iff _ _).1 (finset.sup_mem_nat (mt support_eq_empty.1 h))

@[simp] lemma leading_coeff_zero : leading_coeff (0 : polynomial α) = 0 := rfl

@[simp] lemma leading_coeff_monomial : leading_coeff (monomial n a) = a :=
begin 
  by_cases ha : a = 0,
  { simp [ha] },
  { simp [leading_coeff, degree_monomial _ ha, monomial_apply] },
end

lemma degree_add_eq_of_degree_lt (h : degree p < degree q) : degree (p + q) = degree q :=
le_antisymm (max_eq_right_of_lt h ▸ degree_add_le _ _)
  (le_degree_ne_zero begin 
    rw [add_apply, eq_zero_of_degree_lt h, zero_add],
    exact leading_coeff_ne_zero (λ h₁, by simpa [h₁, nat.not_lt_zero] using h)
  end)

lemma leading_coeff_add_of_lt (h : degree p < degree q) :
  leading_coeff (p + q) = leading_coeff q :=
by unfold leading_coeff;
  rw [degree_add_eq_of_degree_lt h, add_apply, eq_zero_of_degree_lt h, zero_add]

@[simp] lemma mul_apply_degree_add_degree (p q : polynomial α) :
  (p * q) (degree p + degree q) = leading_coeff p * leading_coeff q :=
if hp : degree p = 0 then begin 
  rw [eq_C_of_degree_eq_zero hp],
  simp [leading_coeff, C_apply]
end
else
have h₁ : p * q = monomial (degree p + degree q) (p (degree p) * q (degree q)) +
  erase (degree p) p * monomial (degree q) (q (degree q)) +
  (erase (degree q) q * monomial (degree p) (p (degree p)) +
  erase (degree p) p * erase (degree q) q),
begin
  unfold monomial,
  conv {to_lhs, rw [← @single_add_erase _ _ _ _ _ _ (degree p) p, 
      ← @single_add_erase _ _ _ _ _ _ (degree q) q,
      mul_add, add_mul, add_mul, single_mul_single] },
  simp [mul_comm],
end,
have h₂ : ∀ {p q r : polynomial α}, degree r ≤ degree q →
  (erase (degree p) p * r) (degree p + degree q) = 0,
from λ p q r hr, if hp : degree p = 0 then
  by rw [hp, eq_C_of_degree_eq_zero hp, C, erase_monomial, zero_add, zero_mul, zero_apply]
else
eq_zero_of_degree_lt 
  (calc degree (erase (degree p) p * r)
      ≤ _ : degree_mul_le _ _
  ... < _ : add_lt_add_of_lt_of_le (degree_erase_lt (nat.pos_of_ne_zero hp)) hr),
begin
  rw [h₁, add_apply, add_apply, add_apply, monomial_apply, if_pos rfl],
  rw [h₂ (degree_monomial_le _ _), h₂ (degree_erase_le _ _),
    add_comm (degree p), h₂ (degree_monomial_le _ _), add_zero, add_zero, add_zero],
  refl,  
end

lemma degree_mul_eq' {p q : polynomial α} (h : leading_coeff p * leading_coeff q ≠ 0) :
  degree (p * q) = degree p + degree q := 
le_antisymm (degree_mul_le _ _) (le_degree_ne_zero (by rwa mul_apply_degree_add_degree))

end comm_semiring

section comm_ring
variables [comm_ring α] {p q : polynomial α}
instance : comm_ring (polynomial α) := finsupp.to_comm_ring
instance : has_scalar α (polynomial α) := finsupp.to_has_scalar
instance : module α (polynomial α) := finsupp.to_module
instance {x : α} : is_ring_hom (eval x) := ⟨λ x y, eval_add, λ x y, eval_mul, eval_C⟩

@[simp] lemma degree_neg (p : polynomial α) : degree (-p) = degree p :=
by unfold degree; rw support_neg

@[simp] lemma neg_apply (p : polynomial α) (n : ℕ) : (-p) n = - p n := neg_apply

lemma eval_neg (p : polynomial α) (x : α) : (-p).eval x = -p.eval x :=
is_ring_hom.map_neg _

lemma eval_sub (p q : polynomial α) (x : α) : (p - q).eval x = p.eval x - q.eval x :=
is_ring_hom.map_sub _

lemma degree_sub_lt (hd : degree p = degree q)
  (hpos : 0 < degree p) (hlc : leading_coeff p = leading_coeff q) :
  degree (p - q) < degree p :=
have hlc' : p (degree p) = q (degree q) := hlc,
have hp : single (degree p) (p (degree p)) + p.erase (degree p) = p :=
  finsupp.single_add_erase,
have hq : single (degree q) (q (degree q)) + q.erase (degree q) = q :=
  finsupp.single_add_erase,
begin
  conv { to_lhs, rw [← hp, ← hq, hlc', hd, add_sub_add_left_eq_sub] },
  exact calc degree (erase (degree q) p + -erase (degree q) q)
    ≤ max (degree (erase (degree q) p)) (degree (erase (degree q) q))
    : by rw ← degree_neg (erase (degree q) q);
      exact degree_add_le _ _
  ... < degree p : max_lt_iff.2
    ⟨hd ▸ degree_erase_lt hpos,
    hd.symm ▸ degree_erase_lt (hd ▸ hpos)⟩
end

lemma div_wf_lemma (h : degree q ≤ degree p ∧ 0 < degree p) (hq : monic q) :
  degree (p - monomial (degree p - degree q) (leading_coeff p) * q) < degree p := 
have hp : leading_coeff p ≠ 0, from leading_coeff_ne_zero (λ hp, by simpa [hp, nat.not_lt_zero] using h),
have hpq : leading_coeff (monomial (degree p - degree q) (leading_coeff p)) * leading_coeff q ≠ 0,
  by rwa [leading_coeff, degree_monomial _ hp, monomial_apply, if_pos rfl, monic.def.1 hq, mul_one],
have hzq : leading_coeff (monomial (degree p - degree q) (p (degree p))) * leading_coeff q ≠ 0 :=
  by rwa [monic.def.1 hq, leading_coeff_monomial, mul_one],
degree_sub_lt (by rw [degree_mul_eq' hpq, degree_monomial _ hp, nat.sub_add_cancel h.1]) 
  h.2
  (by rw [leading_coeff, leading_coeff, degree_mul_eq' hzq, mul_apply_degree_add_degree, 
      leading_coeff_monomial, monic.def.1 hq, mul_one])

def div_mod_by_monic_aux : Π (p : polynomial α) {q : polynomial α}, 
  monic q → polynomial α × polynomial α
| p := λ q hq, if h : degree q ≤ degree p ∧ 0 < degree p then
have h : _ := div_wf_lemma h hq,
let z := monomial (degree p - degree q) (leading_coeff p) in
let dm := div_mod_by_monic_aux (p - z * q) hq in
⟨z + dm.1, dm.2⟩
else if degree p = 0 ∧ degree q = 0
  then ⟨C (leading_coeff p), 0⟩
else ⟨0, p⟩
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf degree⟩]}

def div_by_monic (p : polynomial α) {q : polynomial α} (hq : monic q) : polynomial α :=
(div_mod_by_monic_aux p hq).1

def mod_by_monic (p : polynomial α) {q : polynomial α} (hq : monic q) : polynomial α :=
(div_mod_by_monic_aux p hq).2

lemma degree_mod_by_monic_lt : ∀ (p : polynomial α) {q : polynomial α} (hq :monic q) (hq0 : 0 < degree q),
  degree (mod_by_monic p hq) < degree q
| p := λ q hq hq0, if h : degree q ≤ degree p ∧ 0 < degree p then 
have wf : _ := div_wf_lemma h hq,
begin
  unfold mod_by_monic div_mod_by_monic_aux,
  rw if_pos h,
  exact degree_mod_by_monic_lt _ hq hq0,
end
else 
have h₁ : ¬ (degree p = 0 ∧ degree q = 0) := λ h₁, by simpa [h₁.2, lt_irrefl] using hq0,
begin
  unfold mod_by_monic div_mod_by_monic_aux,
  rw [if_neg h, if_neg h₁],
  cases not_and_distrib.1 h with h₂ h₂,
  { exact lt_of_not_ge h₂ },
  { simpa [nat.le_zero_iff.1 (le_of_not_gt h₂)] }
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf degree⟩]}

lemma mod_by_monic_eq_sub_mul_div : ∀ (p : polynomial α) {q : polynomial α} (hq :monic q),
  mod_by_monic p hq = p - q * div_by_monic p hq
| p := λ q hq, if h : degree q ≤ degree p ∧ 0 < degree p then
  have wf : _ := div_wf_lemma h hq,
  begin
  unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
  rw if_pos h,
  show mod_by_monic (p - (monomial (degree p - degree q) (leading_coeff p) * q)) hq = p -
    q * (monomial (degree p - degree q) (leading_coeff p) +
    div_by_monic (p - (monomial (degree p - degree q) (leading_coeff p) * q)) hq),
  rw mod_by_monic_eq_sub_mul_div,
  simp [mul_add, add_mul, mul_comm]
end
else if h₁ : degree p = 0 ∧ degree q = 0 then 
have hq0 : q 0 = 1 := h₁.2 ▸ hq,
begin
  unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
  rw [if_neg h, if_pos h₁, eq_C_of_degree_eq_zero h₁.2],
  conv {to_rhs, congr, rw eq_C_of_degree_eq_zero h₁.1},
  simp [hq0, leading_coeff, h₁.1]
end
else begin 
  unfold mod_by_monic div_by_monic div_mod_by_monic_aux,
  rw [if_neg h, if_neg h₁],
  simp
end
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf degree⟩]}

lemma mod_by_monic_add_div (p : polynomial α) {q : polynomial α} (hq :monic q) : 
  mod_by_monic p hq + q * div_by_monic p hq = p := eq_sub_iff_add_eq.1 (mod_by_monic_eq_sub_mul_div p hq)

lemma degree_div_by_monic_lt (p : polynomial α) {q : polynomial α} (hq : monic q) 
  (hq0 : 0 < degree q) (hp0 : 0 < degree p) : degree (div_by_monic p hq) < degree p :=
if hdp : div_by_monic p hq = 0 then by simpa [hdp] else
have h₁ : leading_coeff q * leading_coeff (div_by_monic p hq) ≠ 0 :=
by rw [monic.def.1 hq, one_mul];
  exact leading_coeff_ne_zero hdp,
have h₂ : degree (mod_by_monic p hq) < degree (q * div_by_monic p hq) :=
by rw degree_mul_eq' h₁;
  exact calc degree (mod_by_monic p hq) < degree q : degree_mod_by_monic_lt p hq hq0 
    ... ≤ degree q + _ : nat.le_add_right _ _,
begin
  conv {to_rhs, rw ← mod_by_monic_add_div p hq},
  rw [degree_add_eq_of_degree_lt h₂, degree_mul_eq' h₁],
  exact (lt_add_iff_pos_left _).2 hq0,
end

lemma dvd_of_mod_by_monic_eq_zero (hq : monic q): mod_by_monic p hq = 0 → q ∣ p :=
λ h, by rw [← mod_by_monic_add_div p hq, h, zero_add];
  exact dvd_mul_right _ _

end comm_ring

section nonzero_comm_ring
variables [nonzero_comm_ring α] {p q : polynomial α}

lemma degree_X : degree (X : polynomial α) = 1 := 
begin
  unfold X monomial degree single finsupp.support,
  rw if_neg (is_nonzero.zero_ne_one α).symm,
  simp [sup],
end

lemma degree_X_sub_C (a : α) : degree (X - C a) = 1 :=
begin 
  rw [sub_eq_add_neg, add_comm, ← @degree_X α],
  exact degree_add_eq_of_degree_lt (by simp [degree_X, degree_neg, degree_C, nat.succ_pos]) 
end

lemma monic_X_sub_C (a : α) : monic (X - C a) :=
begin
  unfold monic leading_coeff,
  rw [degree_X_sub_C, sub_eq_add_neg, add_apply, X, C, monomial_apply, neg_apply, monomial_apply],
  split_ifs; simp * at *
end

lemma root_X_sub_C : root (X - C a) b ↔ a = b := 
by rw [root, eval_sub, eval_X, eval_C, sub_eq_zero_iff_eq, eq_comm]

lemma mod_by_monic_X_sub_C_eq_C_eval (p : polynomial α) (a : α) : mod_by_monic p (monic_X_sub_C a) = C (p.eval a) :=
have h : (mod_by_monic p (monic_X_sub_C a)).eval a = p.eval a :=
  by rw [mod_by_monic_eq_sub_mul_div, eval_sub, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, sub_zero],
have degree (mod_by_monic p (monic_X_sub_C a)) < 1 := 
  degree_X_sub_C a ▸ degree_mod_by_monic_lt p (monic_X_sub_C a) ((degree_X_sub_C a).symm ▸ nat.succ_pos _),
have degree (mod_by_monic p (monic_X_sub_C a)) = 0 := nat.eq_zero_of_le_zero (nat.le_of_lt_succ this),
begin
  rw [eq_C_of_degree_eq_zero this, eval_C] at h,
  rw [eq_C_of_degree_eq_zero this, h]
end

lemma mul_div_eq_iff_root : (X - C a) * div_by_monic p (monic_X_sub_C a) = p ↔ root p a := 
⟨λ h, by rw [← h, root, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul],
λ h : p.eval a = 0, 
  by conv{to_rhs, rw ← mod_by_monic_add_div p (monic_X_sub_C a)};
    rw [mod_by_monic_X_sub_C_eq_C_eval, h, C_0, zero_add]⟩

end nonzero_comm_ring

section integral_domain
variables [integral_domain α] {p q : polynomial α}
open fintype

lemma degree_mul_eq (hp : p ≠ 0) (hq : q ≠ 0) : degree (p * q) = degree p + degree q :=
by rw degree_mul_eq';
  exact mul_ne_zero (leading_coeff_ne_zero hp) (leading_coeff_ne_zero hq)

lemma leading_coeff_mul (p q : polynomial α) : leading_coeff (p * q) = 
  leading_coeff p * leading_coeff q :=
begin
  by_cases hp : p = 0,
  { simp [hp] },
  by_cases hq : q = 0,
  { simp [hq] },
  rw [leading_coeff, degree_mul_eq hp hq, mul_apply_degree_add_degree],
end

lemma root_or_root_of_root_mul (h : root (p * q) a) : root p a ∨ root q a :=
by rw [root, eval_mul] at h;
  exact eq_zero_or_eq_zero_of_mul_eq_zero h

noncomputable def roots_aux : Π {p : polynomial α} (hp : p ≠ 0), 
  {s : finset α // s.card ≤ degree p ∧ ∀ x, root p x ↔ x ∈ s}
| p :=
λ hp, @dite (∃ x, root p x) (classical.prop_decidable _) 
  {s : finset α // s.card ≤ degree p ∧ ∀ x, root p x ↔ x ∈ s}
  (λ h, let ⟨x, hx⟩ := classical.indefinite_description _ h in
  have hpd : 0 < degree p := nat.pos_of_ne_zero 
    (λ h, begin 
      rw [eq_C_of_degree_eq_zero h, root, eval_C] at hx, 
      have h1 : p (degree p) ≠ 0 := leading_coeff_ne_zero hp,
      rw h at h1,
      contradiction,
    end),
  have hd0 : div_by_monic p (monic_X_sub_C x) ≠ 0 :=
    λ h, by have := mul_div_eq_iff_root.2 hx;
      simp * at *,
  have wf : degree (div_by_monic p _) < degree p := 
    degree_div_by_monic_lt _ (monic_X_sub_C x) 
    ((degree_X_sub_C x).symm ▸ nat.succ_pos _) hpd,
  let ⟨t, htd, htr⟩ := @roots_aux (div_by_monic p (monic_X_sub_C x)) hd0 in
  ⟨insert x t, calc (insert x t).card ≤ t.card + 1 : finset.card_insert_le _ _
    ... ≤ degree (div_by_monic p (monic_X_sub_C x)) + 1 : nat.succ_le_succ htd
    ... ≤ _ : nat.succ_le_of_lt wf,
  begin
    assume y,
    rw [mem_insert, ← htr, eq_comm, ← root_X_sub_C],
    conv {to_lhs, rw ← mul_div_eq_iff_root.2 hx},
    exact ⟨root_or_root_of_root_mul, λ h, or.cases_on h (root_mul_right_of_root _) (root_mul_left_of_root _)⟩  
  end⟩)
  (λ h, ⟨∅, nat.zero_le _, by finish⟩)
using_well_founded {rel_tac := λ _ _, `[exact ⟨_, measure_wf degree⟩]}

#print axioms roots_aux

end integral_domain

end polynomial