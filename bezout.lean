import init.meta.well_founded_tactics
import tactic.norm_num
open well_founded
open nat
def euclid_n : nat → nat → nat
| 0        b:= 0
| (succ c) b := have b % succ c < succ c, from mod_lt _ $ succ_pos _,
                succ (euclid_n (b % succ c) (succ c))
                --copied from mathlib gcd definition
def euclid_r: ℕ→ℕ→ℕ→ℕ
    | b c 0        := b
    | b c (succ n) := euclid_r b c n
theorem r_gcd: ∀ b c n:ℕ,euclid_n c b= succ n→euclid_r b c n = gcd c b:=begin
    assume b c n,
    induction c with c1 Hi,
    cases n with n1,unfold euclid_r,
end
theorem decreasingd: ∀ b c n:ℕ ,euclid_n c b =n → euclid_r b c n=gcd b c
| b 0 0                 :=by {unfold euclid_r euclid_n,simp}
| b (succ c) 0          :=by {unfold euclid_n,simp [succ_ne_zero]}
| b 0 (succ n)          :=by {unfold euclid_n,rw eq_comm,simp [succ_ne_zero]}
| b (succ c) (succ n)   :=by{unfold euclid_r euclid_n,intro, rw gcd exact decreasingd (succ c) (b%succ c) n (succ_inj a)}
def euclid_q: ℕ→ℕ→ℕ→ℕ
    | b c 0     := 0
    | b c (succ n) := euclid_r c (b%c) n / euclid_r b c n
def euclid_x: ℕ→ℕ→ℕ→ℤ
    | b c 0     := 0
    | b c (succ n) := euclid_x c (b%c) n - euclid_q b c (succ n) * euclid_x b c n

theorem bezout: ∀ b c:ℕ,∃x y:ℤ, ↑b*x+↑c*y = ↑(gcd b c):=begin
    assume b c,
    apply gcd.induction b c,
    unfold gcd,intro n,existsi (10909301:int),existsi (1:int),simp,
    assume m n Hm,assume Hmn,cases Hmn with x1 Hx,cases Hx with y1 Hxy,
    cases m with m,simp [lt_irrefl] at Hm,revert Hm,cc,
    unfold gcd,rw ←Hxy,existsi -↑(n/succ m)*x1+y1,existsi x1,
    have H: n%succ m=n-(succ m)*(n/(succ m)):=begin rw [eq_comm,nat.sub_eq_iff_eq_add,mod_add_div n (succ m)],rw mul_comm,exact div_mul_le_self n (succ m) end,
    rw H,rw [int.coe_nat_sub,mul_add,add_assoc,add_comm (↑(succ m) * y1) (↑n * x1),←add_assoc,add_right_cancel_iff,mul_sub_right_distrib,int.coe_nat_mul],norm_num,
    rw mul_comm,exact div_mul_le_self n (succ m),
end
#print gcd.induction