import data.equiv.basic algebra.field

universes u v
variables {α : Type u} {β : Type v} (e : α ≃ β)

namespace equiv

protected def has_zero [has_zero α] : has_zero β := ⟨e 0⟩
lemma zero_def [has_zero α] : @has_zero.zero _ (equiv.has_zero e) = e 0 := rfl

protected def has_one [has_one α] : has_one β := ⟨e 1⟩
lemma one_def [has_one α] : @has_one.one _ (equiv.has_one e) = e 1 := rfl

protected def has_mul [has_mul α] : has_mul β := ⟨λ x y, e (e.symm x * e.symm y)⟩
lemma mul_def [has_mul α] (x y : β) :
  @has_mul.mul _ (equiv.has_mul e) x y = e (e.symm x * e.symm y) := rfl

protected def has_add [has_add α] : has_add β := ⟨λ x y, e (e.symm x + e.symm y)⟩
lemma add_def [has_add α] (x y : β) :
  @has_add.add _ (equiv.has_add e) x y = e (e.symm x + e.symm y) := rfl

protected def has_inv [has_inv α] : has_inv β := ⟨λ x, e (e.symm x)⁻¹⟩
lemma inv_def [has_inv α] (x : β) : @has_inv.inv _ (equiv.has_inv e) x = e (e.symm x)⁻¹ := rfl

protected def has_neg [has_neg α] : has_neg β := ⟨λ x, e (- e.symm x)⟩
lemma neg_def [has_neg α] (x : β) : @has_neg.neg _ (equiv.has_neg e) x = e (-e.symm x) := rfl

protected def semigroup [semigroup α] : semigroup β :=
{ mul_assoc := by simp [mul_def, mul_assoc],
  ..equiv.has_mul e }

protected def comm_semigroup [comm_semigroup α] : comm_semigroup β :=
{ mul_comm := by simp [mul_def, mul_comm],
  ..equiv.semigroup e }

protected def monoid [monoid α] : monoid β :=
{ one_mul := by simp [mul_def, one_def],
  mul_one := by simp [mul_def, one_def],
  ..equiv.semigroup e,
  ..equiv.has_one e }

protected def comm_monoid [comm_monoid α] : comm_monoid β :=
{ ..equiv.comm_semigroup e,
  ..equiv.monoid e }

protected def group [group α] : group β :=
{ mul_left_inv := by simp [mul_def, inv_def, one_def],
  ..equiv.monoid e,
  ..equiv.has_inv e }

protected def comm_group [comm_group α] : comm_group β :=
{ ..equiv.group e,
  ..equiv.comm_semigroup e }

protected def add_semigroup [add_semigroup α] : add_semigroup β :=
@additive.add_semigroup _ (@equiv.semigroup _ _ e multiplicative.semigroup)

protected def add_comm_semigroup [add_comm_semigroup α] : add_comm_semigroup β :=
@additive.add_comm_semigroup _ (@equiv.comm_semigroup _ _ e multiplicative.comm_semigroup)

protected def add_monoid [add_monoid α] : add_monoid β :=
@additive.add_monoid _ (@equiv.monoid _ _ e multiplicative.monoid)

protected def add_comm_monoid [add_comm_monoid α] : add_comm_monoid β :=
@additive.add_comm_monoid _ (@equiv.comm_monoid _ _ e multiplicative.comm_monoid)

protected def add_group [add_group α] : add_group β :=
@additive.add_group _ (@equiv.group _ _ e multiplicative.group)

protected def add_comm_group [add_comm_group α] : add_comm_group β :=
@additive.add_comm_group _ (@equiv.comm_group _ _ e multiplicative.comm_group)

protected def ring [ring α] : ring β :=
{ right_distrib := by simp [mul_def, add_def, add_mul],
  left_distrib := by simp [mul_def, add_def, mul_add],
  ..equiv.has_mul e,
  ..equiv.has_add e,
  ..equiv.monoid e,
  ..equiv.add_comm_group e }

protected def comm_ring [comm_ring α] : comm_ring β :=
{ ..equiv.comm_monoid e,
  ..equiv.ring e }

protected def nonzero_comm_ring [nonzero_comm_ring α] : nonzero_comm_ring β :=
{ zero_ne_one := by simp [zero_def, one_def],
  ..equiv.has_zero e,
  ..equiv.has_one e,
  ..equiv.comm_ring e }

protected def integral_domain [integral_domain α] : integral_domain β :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := by simp [mul_def, zero_def, equiv.symm_apply_eq],
  ..equiv.has_zero e,
  ..equiv.has_mul e,
  ..equiv.nonzero_comm_ring e }

protected def division_ring [division_ring α] : division_ring β :=
{ zero_ne_one := by simp [zero_def, one_def],
  inv_mul_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact inv_mul_cancel,
  mul_inv_cancel := λ _,
    by simp [mul_def, inv_def, zero_def, one_def, (equiv.symm_apply_eq _).symm];
      exact mul_inv_cancel,
  ..equiv.has_zero e,
  ..equiv.has_one e,
  ..equiv.ring e,
  ..equiv.has_inv e }

protected def field [field α] : field β :=
{ ..equiv.comm_ring e,
  ..equiv.division_ring e }

protected def discrete_field [discrete_field α] : discrete_field β :=
{ has_decidable_eq := equiv.decidable_eq e.symm,
  inv_zero := by simp [mul_def, inv_def, zero_def],
  ..equiv.has_mul e,
  ..equiv.has_inv e,
  ..equiv.has_zero e,
  ..equiv.field e }

end equiv
