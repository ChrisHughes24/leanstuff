

-- let's define the real numbers to be a number system which satisfies
-- the basic properties of the real numbers which we will need.

noncomputable theory 
constant real : Type
@[instance] constant real_field : linear_ordered_field real

-- This piece of magic means that "real" now behaves a lot like
-- the real numbers. In particular we now have a bunch
-- of theorems:

example : ∀ x y : real, x * y = y * x := mul_comm


variable x : real
variable n : nat

-- We do _not_ have powers though. So we need to make them.

open nat 

definition natural_power : real → nat → real
| x 0 := 1
| x (succ n) := (natural_power x n) * x

theorem T : ∀ x:real, ∀ m n:nat, natural_power x (m+n) = natural_power x m *natural_power x n :=
begin
assume x m n,
induction n with n H,
unfold natural_power,
rw [add_zero, mul_one],
unfold natural_power,
rw [H, mul_assoc],
end

theorem T2 : ∀ x: real, ∀ m n : nat, natural_power (natural_power x m) n = natural_power x (m*n) :=
begin
assume x m n,
induction n with n H,
unfold natural_power,
rw [mul_zero, eq_comm],
unfold natural_power,
rw [succ_eq_add_one, mul_add, mul_one, add_one],
unfold natural_power,
rw[T, H],
end

theorem T3 : ∀ x y:real, ∀ n:nat, (natural_power x n) * (natural_power y n) = natural_power (x*y) n :=
begin
assume x y n,
induction n with n H,
unfold natural_power,
simp,
unfold natural_power,
cc,
end



constant nth_root (x : real) (n : nat) : (x>0) → (n>0) → real

axiom is_nth_root (x : real) (n : nat) (Hx : x>0) (Hn : n>0) : natural_power (nth_root x n Hx Hn) n = x 

definition rational_power_v0 (x : real) (n : nat) (d : nat) (Hx : x > 0) (Hd : d > 0) : real :=
natural_power (nth_root x d Hx Hd) n 

theorem T4 : ∀ x y:real,∀ Hx:x≥0,∀ Hy:y≥0,∀ n:nat,natural_power x (n+1) = natural_power y (n+1) → x = y:=
begin
assume x y Hx Hy n,
induction n with n H,
    rw[add_one],
    unfold natural_power,
    rw[mul_comm,mul_one,mul_comm,mul_one],
    assume H1,
    exact(H1),
    unfold natural_power,
    assume H2,
    calc
    natural_power x n * x * x = natural_power y n * y * y : H2
    ... =

        
        



end
/-
theorem T5 : ∀ x:real, ∀ n d k:nat, ∀ Hx: x > 0, 
∀ Hd: d >0, ∀ Hkd: (k*d) >0, 
rational_power_v0 x n d Hx Hd = rational_power_v0 x (k*n) (k*d) Hx Hkd:=
begin
assume x n d k Hx Hd Hkd,
unfold rational_power_v0,
rw[← T2],
have H1 :natural_power (rational_power_v0 x n d Hx Hd) d= natural_power x n :=
begin
unfold rational_power_v0,
rw[T2, mul_comm,← T2,is_nth_root],
end,
let y:real := x,
have H1 y=x,
begin

end
end
-/
