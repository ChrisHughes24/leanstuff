
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

theorem T1 : ∀ x:real, ∀ m n:nat, natural_power x (m+n) = natural_power x m *natural_power x n :=
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
        rw [succ_eq_add_one,mul_add,mul_one,add_one],
        unfold natural_power,
        rw [T1,H]
    end

theorem T3 : ∀ x y: real, ∀ n : nat, natural_power x n * natural_power y n = natural_power (x*y) n :=
    begin
        assume x y n,
        induction n with n H,
        unfold natural_power,
        exact mul_one 1,
        rw[succ_eq_add_one],
        rw[T1],
        unfold natural_power,
        rw[one_mul],
        cc,
    end


constant nth_root (x : real) (n : nat) : (x>0) → (n>0) → real

axiom is_nth_root (x : real) (n : nat) (Hx : x>0) (Hn : n>0) : natural_power (nth_root x n Hx Hn) n = x 

definition rational_power_v0 (x : real) (n : nat) (d : nat) (Hx : x > 0) (Hd : d > 0) : real :=
natural_power (nth_root x d Hx Hd) n 


theorem T4 (x:real) (n:ℕ) (Hx:x≥0): 0 ≤ natural_power x n:=
    begin
        induction n with n H,
        unfold natural_power,
        exact zero_le_one,
        unfold natural_power,
        exact calc 0 = 0*x:by rw[zero_mul]
            ... ≤ natural_power x n * x:mul_le_mul_of_nonneg_right H Hx,
    end


theorem T5 (x y:real) (n:ℕ) (Hx:x≥0) (Hy:y≥0) (Hn:n≥1): natural_power x n = natural_power y n → x = y :=
    begin
        have H1:  ∀ (s t:real), ∀ (Hs : s ≥ 0), ∀ (Ht : t ≥ 0) , s < t → natural_power s n < natural_power t n,
            assume s t Hs Ht Hslt,
            cases n with k,
            exfalso,
            have Htemp : 0 < 0,
            exact calc 0 < 1 : zero_lt_one
                ... ≤ 0 : Hn,
            have Htemp2 : ¬ (0=0),
            exact ne_of_lt Htemp,
            apply Htemp2,
            trivial,
            clear Hn,

            induction k with k Hk,
                unfold natural_power,
                rwa[one_mul,one_mul],
                unfold natural_power,
                exact calc natural_power s k * s * s = natural_power s (succ k) * s:rfl
                    ... ≤ natural_power s (succ k) * t:mul_le_mul_of_nonneg_left (le_of_lt Hslt) (T4 s (succ k) Hs) --  (sorry)
                    ... < natural_power t (succ k) * t: mul_lt_mul_of_pos_right Hk (calc 0≤s : Hs ... <t : Hslt)
                    ... = natural_power t k * t * t : rfl,

        intro Hnp,
        cases  lt_or_ge x y with H2 H3,
        exfalso,
        exact ne_of_lt (H1 x y Hx Hy H2) Hnp, 

        cases lt_or_eq_of_le H3 with H4 H5,
        tactic.swap,
        exact eq.symm H5,
        exfalso,
        exact ne_of_lt (H1 y x Hy Hx H4) (eq.symm Hnp),
    end

axiom positive_nth_root (x:real) (n:ℕ) (Hx:x>0) (Hn:n>0):0<nth_root x n Hx Hn

theorem T6 (x:real) (m n k l:ℕ) (Hx:x>0) (Hm:m≥0) (Hn:n>0) (Hk:k≥0) (Hl:l>0) (Hmnkl:m*l=k*n): rational_power_v0 x m n Hx Hn=rational_power_v0 x k l Hx Hl:=
begin
    have H2:natural_power (rational_power_v0 x m n Hx Hn) (n*l)=natural_power (rational_power_v0 x k l Hx Hl) (n*l):=
        begin
            have H2_1:natural_power (rational_power_v0 x k l Hx Hl) (n*l) = natural_power (rational_power_v0 x k l Hx Hl) (l*n):=
                begin rw[mul_comm] end,
            rw[H2_1], clear H2_1,
            rw[←T2,←T2],
            unfold rational_power_v0,
            rw[T2 (nth_root x l Hx Hl), mul_comm,←T2, is_nth_root],
            rw[T2 (nth_root x n Hx Hn), mul_comm,←T2, is_nth_root],
            rw[T2,T2,Hmnkl]
        end,
    have Hxmn:rational_power_v0 x m n Hx Hn≥0:=
        begin
            unfold rational_power_v0,
            have Hxmn_1:0≤nth_root x n Hx Hn:= le_of_lt (positive_nth_root x n Hx Hn),
            exact T4 (nth_root x n Hx Hn) m Hxmn_1,
        end,
    have Hxkl:rational_power_v0 x k l Hx Hl≥0:=
        begin
            unfold rational_power_v0,
            have Hxkl_1:0≤nth_root x l Hx Hl:= le_of_lt (positive_nth_root x l Hx Hl),
            exact T4 (nth_root x l Hx Hl) k Hxkl_1,
        end,
    have Hnl:n*l≥1:=
        begin
            have Hnl_1:0<n*l:=mul_pos Hn Hl,
            have Hnl_2:1<1+(n*l):=add_lt_add_left Hnl_1 1,
            have Hnl_3:1<succ(n*l):=
                begin
                    rw[succ_eq_add_one,add_comm],
                    exact Hnl_2,
                end,
            have Hnl_4:1≤(n*l):=le_of_lt_succ Hnl_3,
            exact(Hnl_4),
        end,

    exact T5 (rational_power_v0 x m n Hx Hn) (rational_power_v0 x k l Hx Hl) (n*l) Hxmn Hxkl Hnl H2,

end

theorem T7 (x:real) (m n k l:ℕ) (Hx:x>0) (Hm:m≥0) (Hn:n>0) (Hk:k≥0) (Hl:l>0) (Hmnkl:m*l=k*n): T6 x m n k l Hx Hm Hn Hk Hl Hmnkl = T6 x m n k l Hx Hm Hn Hk Hl Hmnkl :=
begin
unfold T6,
end