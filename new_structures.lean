variables

class monoid' (α : Type*) extends semigroup α, has_one α :=
(mul_one : ∀ a : α, a * 1 = a)
(one_mul : ∀ a : α, 1 * a = a)

class comm_monoid' (α : Type*) extends semigroup α, has_one α :=
(mul_one : ∀ a : α, a * 1 = 1)
(mul_comm : ∀ a b : α, a * b = b * a)

class group' (α : Type*) extends semigroup α, has_one α, has_inv α :=
(one_mul : ∀ a : α, 1 * a = a)
(mul_left_inv : ∀ a : α, a⁻¹ * a = 1)
(mul_right_inv : ∀ a : α, a * a⁻¹ = 1)

class comm_group' (α : Type*) extends semigroup α, has_one α :=
(mul_comm : ∀ a b : α, a * b = b * a)

variable {α : Type*}

instance group'.to_monoid' [group' α] : monoid' α :=
{ mul := (*),
  mul_one := λ a, by rw [← group'.mul_left_inv a, ← mul_assoc, group'.mul_right_inv, group'.one_mul],
  ..show group' α, by apply_instance }

instance comm_group'.to_comm_monoid' [comm_group' α] : comm_monoid' α :=
{ ..show comm_group' α, by apply_instance }

def pow [monoid' α] (a : α) : ℕ → α
| 0     := 1
| (n+1) := a * pow n

instance I1 [monoid' α] : has_pow α ℕ := ⟨pow⟩

def gpow [group' α] (a : α) : ℤ → α
| (n : ℕ) := a ^ n
| -[1+ n] := (a ^ (n + 1))⁻¹

instance I2 [group' α] : has_pow α ℤ := ⟨gpow⟩

lemma gpow_eq_pow [group' α] (a : α) (n : ℕ) : a ^ (n : ℕ) = a ^ (n : ℤ) := rfl

example {α : Type*} [comm_group' α] : @group'.to_monoid' _ (comm_group'.to_group' α) =
  @comm_monoid'.to_monoid' _ comm_group'.to_comm_monoid' := rfl

set_option pp.all true
example [comm_group' α] (a : α) (n : ℕ) : a ^ (n : ℕ) = a ^ (n : ℤ) :=
begin
  rw gpow_eq_pow,

end
