import data.nat.prime
import tactic.norm_num
import data.nat.gcd
open nat


definition is_prime : nat → Prop
| zero := false
| (succ zero) := false
| (succ(succ x)) := ¬∃b c:nat,2≤b ∧ 2≤c ∧ b*c=succ(succ x)
definition product : list nat → nat
| list.nil := 1
| (n::L) :=  n * product L



theorem product_append: ∀L M:list nat,product L*product M=product (L ++ M):=begin
    assume L,
    induction L with h L1 HiL,
        unfold product append list.append,
        assume M, rw one_mul,

        assume M1,
        have H2:product L1 * product (h::M1) = product (L1 ++ (h::M1)):=HiL (h::M1),
        clear HiL,revert H2,
        unfold product append list.append,
        rw[←mul_assoc, mul_comm (product L1) h],
        assume H,rw H,clear H,
        induction L1 with h1 L2 HiL1,
            unfold list.append product,

            unfold list.append product,
            rw [HiL1,←mul_assoc,←mul_assoc, mul_comm h h1],
end

theorem prime_eq :∀ p, is_prime p ↔ prime p:=begin
    intro, cases p with p,
    unfold is_prime prime,norm_num,
    cases p with p,
    unfold is_prime prime,norm_num,exact dec_trivial,
    unfold prime is_prime,
    apply iff.intro,
    assume H,apply and.intro,
    exact dec_trivial,
    assume p1 H3,
    have H4:=exists_eq_mul_right_of_dvd H3,
    apply exists.elim H4, assume c Hc,
    cases c with c,
    exfalso,revert Hc,exact dec_trivial,
    cases c with c,
    revert Hc,norm_num,rw eq_comm,cc,
    cases classical.em(p1=1),left,assumption,
    have H5:∃ (b c : ℕ), 2 ≤ b ∧ 2 ≤ c ∧ b * c = succ (succ p):=begin
        existsi (succ(succ c)),existsi p1,
        have H6:2 ≤ succ (succ c)↔true:=dec_trivial,
        rw H6,simp,rw Hc,simp,
        cases p1 with p1,
        revert Hc,norm_num,exact succ_ne_zero (succ p),
        cases p1 with p1,
        revert a,norm_num,exact dec_trivial,
    end,exfalso,exact H H5,
    assume Hp Hexists,
    apply exists.elim Hexists,assume b Hb,
    apply exists.elim Hb,assume c Hbc,clear Hb Hexists,
    apply and.elim Hbc,assume Hb Hc1,clear Hbc,
    apply and.elim Hc1, assume Hc Hbc,clear Hc1,apply and.elim Hp,clear Hp,
    assume H1 Hp,
    have H3:=Hp c,
    have H4:= dvd_of_mul_left_eq b Hbc,
    have H5:= H3 H4,
    have H6:c=1↔false:=begin
        apply iff.intro,
        assume Ht,revert Hc,rw Ht,norm_num,
    end,revert H5,rw H6,simp,
    assume Hc,rw Hc at Hbc,
    cases b with b,revert Hb,exact dec_trivial,
    cases b with b,revert Hb,exact dec_trivial,
    revert Hbc,simp,rw mul_succ,norm_num,rw[mul_comm,mul_succ],assume Hbc,
    have H7:succ (succ p) + (succ (succ p) * b + succ (succ p)) = succ (succ p)+0:=begin rw Hbc, end,
    have H8:(succ (succ p) * b + succ (succ p))=0:=add_left_cancel H7,
    revert H8,rw[add_comm,succ_add],apply succ_ne_zero,
end

theorem prime_product: ∀x:ℕ,1≤x→∃L:list ℕ,(∀p:ℕ,p ∈ L→prime p)∧product L=x:=begin
    have Hstrong:∀ x y:ℕ,x≤y→1≤x→∃L:list ℕ,(∀p:ℕ,p ∈ L→prime p)∧product L=x:=begin
        assume x y, revert x,
        induction y with y Hiy,
            assume x Hxy Hx1,
            have Hx:=eq_zero_of_le_zero Hxy,revert Hx1,rw Hx,norm_num,           
            assume x Hxy H1x,
            cases x with x,revert H1x,norm_num,
            cases x with x,
            existsi list.nil,
            unfold list.mem product,simp,
            cases classical.em(prime (succ(succ x))) with Hx Hx1,
                existsi ([succ(succ x)]),
                unfold list.mem product,simp,assumption,

                rw ←prime_eq at Hx1,unfold is_prime at Hx1,
                have A:∃ (b c : ℕ), 2 ≤ b ∧ 2 ≤ c ∧ b * c = succ (succ x):=begin
                    revert Hx1,cc,
                end,clear Hx1,
                apply exists.elim A, assume b Hb,clear A,
                apply exists.elim Hb, assume c Hbc1,clear Hb,
                have Hb:=and.elim_left Hbc1,
                have Hc:=and.elim_left(and.elim_right Hbc1),
                have Hbc:=and.elim_right(and.elim_right Hbc1),clear Hbc1,
                have Hbx:b<succ(succ x),{rw[←Hbc,mul_comm,lt_mul_iff_one_lt_left],exact lt_of_succ_le Hc,cases b,revert Hb,norm_num,exact dec_trivial},
                have Hcx:c<succ(succ x),{rw[←Hbc,lt_mul_iff_one_lt_left],exact lt_of_succ_le Hb,cases c,revert Hc,norm_num,exact dec_trivial},
                have Hxy1:succ x≤y:=by rwa ←succ_le_succ_iff,clear Hxy,
                have Hbx1:b≤succ x:=begin rw ←succ_le_succ_iff,apply succ_le_of_lt,assumption end,
                have Hcx1:c≤succ x:=begin rw ←succ_le_succ_iff,apply succ_le_of_lt,assumption end,
                have Hby:=le_trans Hbx1 Hxy1,
                have Hcy:=le_trans Hcx1 Hxy1,
                have H12:1≤2:=dec_trivial,
                have H1b:=le_trans H12 Hb,
                have H1c:=le_trans H12 Hc,
                clear H12 Hcx1 Hbx1 Hxy1 Hcx Hbx Hb Hc H1x,
                apply exists.elim (Hiy b Hby H1b),assume Lb HLb,
                apply exists.elim (Hiy c Hcy H1c),assume Lc HLc,clear Hiy H1b H1c Hby Hcy,
                have HLb1:=and.elim_left HLb,have HLb2:=and.elim_right HLb,clear HLb,
                have HLc1:=and.elim_left HLc,have HLc2:=and.elim_right HLc,clear HLc,
                existsi(Lb ++ Lc),
                apply and.intro,rw[←Hbc,←HLb2,←HLc2,eq_comm],
                exact product_append Lb Lc,
                norm_num,
                assume p H,
                cases H with A A,
                exact HLb1 p A,
                exact HLc1 p A,                              
    end,
    assume x,
    exact Hstrong x x (le_refl x),
end
def euclid_r: int→int→nat→int
| a b 0     := b
| a b 1     := a%b
| a b (n+2) := euclid_r a b n % euclid_r a b (succ n)
def euclid_q: int→int→nat→int
| a b 0     := 0
| a b 1     := -(a/b)
| a b (n+2) := euclid_r a b n / euclid_r a b (succ n)
def euclid_x: int→int→nat→int
| a b 0     := 0
| a b 1     := 1
| a b (n+2) := euclid_x a b n - euclid_q a b (succ (succ n)) * euclid_x a b (succ n)
def euclid_y: int→int→nat→int
| a b 0     := 1
| a b 1     := euclid_q a b 1
| a b (n+2) := euclid_y a b n - euclid_q a b (succ (succ n)) * euclid_y a b (succ n)
open int
theorem pos_mod:∀ a b:int,a%b≥ 0:=sorry


theorem int_mod_lt: ∀ b c:int, c≠ 0→ b%c<abs(c):=int.mod_lt
theorem decreasing_r: ∀ (b c:int) (n:ℕ),abs(euclid_r b c (n+1))<abs(euclid_r b c n) ∨ ∃m,m≤n+1∧euclid_r b c m = 0 :=begin
    assume b c n,
    induction n with n1 Hin,
        unfold euclid_r,
        cases classical.em(c=0) with A A,
        right,existsi 0,unfold euclid_r,
        rw A,simp,exact dec_trivial,left,
        
        rw abs_of_nonneg (pos_mod b c),

        exact int_mod_lt b c A,
        unfold euclid_r,rw ←add_one,
        cases classical.em (∃ (m : ℕ), m ≤ n1 + 1 ∧ euclid_r b c m = 0) with A A,
        right,apply exists.elim A,assume m Hm,existsi m,
        apply and.intro,
        exact le_trans (and.elim_left Hm) (le_add_right (n1+1) 1),
        exact and.elim_right Hm,
        cases classical.em(euclid_r b c (n1 + 1)=0) with A A,
        right, existsi n1+1,apply and.intro,norm_num,
        assumption,left,
        rw abs_of_nonneg (pos_mod(euclid_r b c n1)(euclid_r b c (n1 + 1))),
        apply int_mod_lt,exact A,
end
--use size_of not abs
theorem gcd_exists:∀ b c :int, ∃ n:nat, euclid_r b c (succ n) = 0:=begin
    assume b c ,
    have H:∀ n:nat,(∀ m:nat,m≤n→¬euclid_r b c m = 0)→abs (euclid_r b c n)≤abs c-n:=begin
        assume n Hn,
        induction n with n1 Hin,
        unfold euclid_r,norm_num,
        have Hn1:∀ (m : ℕ), m ≤ n1 → ¬euclid_r b c m = 0:=begin
            assume m Hm,
            have H:=le_trans Hm (le_succ n1),
            exact Hn m H,
        end,
        have Hin1:=Hin Hn1,clear Hin,
        have H1:=decreasing_r b c n1,
        have H3:∀ (m : ℕ),¬( m ≤succ n1 ∧ euclid_r b c m = 0):=begin
            assume m,rw not_and,exact Hn m,
        end,
        have H2:¬∃ (m : ℕ), m ≤ succ n1 ∧ euclid_r b c m = 0:=not_exists_of_forall_not H3,
        have H4:(∃ (m : ℕ), m ≤ succ n1 ∧ euclid_r b c m = 0)↔false:=begin 
            apply iff.intro,exact H2,trivial,
        end,rw H4 at H1,simp at H1,clear H4 H2 H3,
        have H2:= lt_of_lt_of_le H1 Hin1,
        have H3:= add_one_le_of_lt H2,
        have H4:abs c - ↑n1=(abs c -↑n1-1)+1:=begin rw sub_add_cancel, end,
        rw H4 at H3,
        have H5:=le_of_add_le_add_right H3,revert H5,norm_num,
    end,
    cases classical.em (∃m:nat,↑m≤abs c ∧ euclid_r b c m = 0) with A A,
    have H1

end
open nat
theorem quotients :∀(c b:int) n:nat, euclid_r c b n -euclid_q c b (succ(succ n)) * euclid_r c b (succ n) = euclid_r c b (succ (succ n)):=begin
    assume c b n,
    unfold euclid_q euclid_r,
    rw int.mod_def,norm_num,
end
theorem almost_bezout: ∀ (c b:int) n:nat, euclid_x c b n * c + euclid_y c b n * b = euclid_r c b n:=begin
    -- semi strong induction, need previous two cases
    have Hi:∀(c b:int) n:nat,euclid_x c b n * c + euclid_y c b n * b = euclid_r c b n ∧ euclid_x c b (succ n) * c + euclid_y c b (succ n) * b = euclid_r c b (succ n):=begin
        assume  c b n,
        induction n with n1 Hin2,
        apply and.intro,
        unfold euclid_x euclid_y euclid_r,simp,
        unfold euclid_x euclid_y euclid_r euclid_q,rw int.mod_def,simp,

        have Hin:=and.elim_left Hin2,
        have Hin1:=and.elim_right Hin2,clear Hin2,
        apply and.intro,assumption,

        unfold euclid_x euclid_y,

        rw ←quotients c b n1,
        have H1:(euclid_x c b n1 - euclid_q c b (succ (succ n1)) * euclid_x c b (succ n1)) * c=euclid_x c b n1 *c - euclid_q c b (succ (succ n1)) * euclid_x c b (succ n1)*c:=begin norm_num,rw mul_add,norm_num,end,
        have H2:(euclid_y c b n1 - euclid_q c b (succ (succ n1)) * euclid_y c b (succ n1)) * b=euclid_y c b n1 *b - euclid_q c b (succ (succ n1)) * euclid_y c b (succ n1)*b:=begin norm_num,rw mul_add,norm_num,end,
        rw [H1,H2],clear H1 H2,
        have H1:=calc euclid_x c b n1 * c - euclid_q c b (succ (succ n1)) * euclid_x c b (succ n1) * c +
      (euclid_y c b n1 * b - euclid_q c b (succ (succ n1)) * euclid_y c b (succ n1) * b)=euclid_x c b n1 * c - euclid_q c b (succ (succ n1)) * euclid_x c b (succ n1) * c +
      euclid_y c b n1 * b - euclid_q c b (succ (succ n1)) * euclid_y c b (succ n1) * b:by norm_num
      ...=euclid_x c b n1 * c + euclid_y c b n1 * b - euclid_q c b (succ (succ n1)) * euclid_y c b (succ n1) * b-euclid_q c b (succ (succ n1)) * euclid_x c b (succ n1)*c:by norm_num
      ...=euclid_r c b n1 -euclid_q c b (succ (succ n1)) * euclid_y c b (succ n1) * b-euclid_q c b (succ (succ n1)) * euclid_x c b (succ n1)*c:by rw ←Hin
      ...=euclid_r c b n1 + (-euclid_q c b (succ (succ n1)) * (euclid_y c b (succ n1) * b) + -euclid_q c b (succ (succ n1)) * (euclid_x c b (succ n1)*c)):by norm_num,
      rw H1,
      have H2:=mul_add (-euclid_q c b (succ (succ n1))) (euclid_y c b (succ n1) * b) (euclid_x c b (succ n1)*c),rw  ←H2,
      rw ←Hin1,norm_num,
    end,
    assume c b n,
    exact and.elim_left (Hi c b n),    
end


theorem int_dvd_mod_iff: ∀ (b c d:int), b ∣ d → (b ∣ (c % d) ↔ b ∣ c) :=begin
    assume b c d Hbd,
    apply iff.intro,
    rw int.mod_def,
    have H1:c=c-(d * (c / d))+(d * (c / d)):=by norm_num,
    intros,rw H1,
    exact dvd_add a (dvd_mul_of_dvd_left Hbd (c/d)),
    assume H1,
    rw int.mod_def,
    exact dvd_sub H1 (dvd_mul_of_dvd_left Hbd (c/d)),
end
theorem cd_dvd_r:∀ (b c x:int), x ∣ b → x∣c→∀ n:nat, x∣euclid_r b c n:=begin
    assume b c x Hb Hc n,
    have Hi:x ∣ euclid_r b c n∧x ∣ euclid_r b c (succ n):=begin
        induction n with n1 Hin,
        unfold euclid_r,apply and.intro,
        assumption,
        exact iff.elim_right (int_dvd_mod_iff x b c Hc) Hb,

        unfold euclid_r,

        exact and.intro (and.elim_right Hin) (iff.elim_right (int_dvd_mod_iff x (euclid_r b c n1) (euclid_r b c (succ n1)) (and.elim_right Hin)) (and.elim_left Hin)),
    end,
    exact and.elim_left Hi,
end
def gcd1: int→int→int→Prop
| a b n:= n∣a ∧ n ∣ b ∧ (∀ e : int,e∣a→ e∣b → e∣n)
theorem gcd_euclid: ∀ (b c:int) (n:nat), euclid_r b c (n+1)=0→gcd1 b c (euclid_r b c n):=begin
    have quotients_mod: ∀ (b c:int) (n:nat), euclid_r b c n= euclid_q b c (succ (succ n)) * euclid_r b c(succ n) +euclid_r b c (succ (succ n)):=begin
        assume b c n,
        rw ←quotients,norm_num,
    end,
    have Hi:∀ (b c:int) (n:nat), euclid_r b c (succ(succ n))=0→(∀ k:nat,k≤n→euclid_r b c (succ n) ∣ euclid_r b c (n-k)∧euclid_r b c (succ n) ∣ euclid_r b c (succ(n-k))):=begin       
        assume b c n H,
        unfold euclid_r at H,
        have H2:=int.dvd_of_mod_eq_zero H,
        assume k Hkn,
        induction k with k1 Hik,
        simp,assumption,
        have Hik3:=Hik ( le_trans (le_succ k1) Hkn),clear Hik,
        have Hik1:= and.elim_left Hik3,
        have Hik2:=and.elim_right Hik3,clear Hik3,
        have Hsucc:(nat.succ (n - succ k1))=n-k1:=sorry,
        apply and.intro,
        rw quotients_mod b c (n- succ k1),
        rw Hsucc,
        exact dvd_add (dvd_mul_of_dvd_right Hik1 (euclid_q b c (succ (n - k1)))) Hik2,
        rw Hsucc,assumption,
    end,
    assume b c n Hn,
    have H1:euclid_r b c n ∣ c:=begin
        cases n with n1,
        unfold euclid_r,exact dvd_refl c,rw add_one at Hn,
        have Hi1:= Hi b c n1 Hn n1 (le_refl n1),
        have H1:n1-n1=0:=nat.sub_self n1,
        rw H1 at Hi1,
        unfold euclid_r at Hi1,
        exact and.elim_left Hi1,
    end,
    have H2:euclid_r b c n ∣ (b%c):=begin
        cases n with n1,
        unfold euclid_r,unfold euclid_r at Hn,rw Hn,
        exact dvd_zero c,
        cases n1 with n2,
        unfold euclid_r,exact dvd_refl (b%c),
        have Hi1:= Hi b c (succ n2) Hn n2,
        have H1:nat.succ n2-n2=1:=begin rw ←zero_add 1,have H2:=nat.sub_self n2,rw[←H2,add_one],exact succ_sub (le_refl n2), end,
        rw H1 at Hi1,
        have H3: euclid_r b c 1 =b%c:=by unfold euclid_r,
        rw ←H3,exact and.elim_left (Hi1 (le_succ n2)),
    end,


    unfold gcd1,
    apply and.intro,
    exact iff.elim_left (int_dvd_mod_iff (euclid_r b c n) b c H1) H2,
    apply and.intro,assumption,
    assume x Hb Hc,
    exact cd_dvd_r b c x Hb Hc n,    
end

theorem bezout: ∀ b c d:int, gcd1 b c d→ ∃ x y:ℤ, x *b + y*c = d:=begin
    assume b c n Hn,
    apply exists.elim (gcd_exists b c),
    existsi euclid_x b c n,
    existsi euclid_y b c n,
    existsi euclid_r b c n,
    rw ←add_one at Hn,
    apply and.intro,
    exact almost_bezout b c n,
    exact gcd_euclid b c n Hn,
end
def int_prime : int→Prop
| p := abs p ≠ 1 ∧ ∀ x:int, x∣p → abs x=1 ∨ abs x = p
open int
#eval int.sizeof (0:int)
theorem gcdprime:∀ p x:int, int_prime p → ∀ d, gcd1 x p d → d=1 ∨ d=p:=sorry
theorem euclids_lemma: ∀b c p:int, int_prime p→p ∣ (b*c) → p ∣ b ∨ p ∣ c:=sorry
def product_int :list int → int
| list.nil := 1
| (p::L)   := p* product_int L
theorem int_prime_product: ∀ x:int,∃ L:list int,(∀ p:int,p ∈ L → int_prime p)∧product_int L = x:=sorry
def count: int → (list int) → nat
| n [] :=0
| n (a::l):= if abs a=abs n then (succ (count n l)) else (count n l)
theorem product_dvd: ∀ (p:int) (L:list int),p ∈ L→ p ∣ product_int L:=sorry 
theorem unique_prime_factorization: ∀ (x :int) (A : list int),((∀ p:int,p ∈ A → int_prime p)∧product_int A = x)→(∀ B:list int,((∀ p:int,p ∈ B → int_prime p)∧product_int B = x)→ ∀ p:int,count p A = count p B):=begin
    assume x A HA,revert x,
    
    induction A with pA A1 HiA,
    norm_num,unfold product_int count,assume B HB,
    admit,

    assume x1 HA1,
    have H2:∀ p,p ∈ pA :: A1↔p=pA∨p∈A1:=begin
        norm_num,
    end,
    have H1:(∀ (p : ℤ), p ∈ A1 → int_prime p):=begin
        assume p H1,
        have H:=and.elim_left HA1 p,rw (H2 p) at H,
        exact H (or.intro_right (p=pA) H1),
    end,
    have HiA3:=HiA (product_int A1) (and.intro H1 (by trivial)),clear HiA,
    assume B HB,
    cases B with pB B1,
    unfold product_int at HB,
    have Hx1:=and.elim_right HB,clear HB,
    have HA2:=and.elim_right HA1,exfalso,revert HA2,
    rw ←Hx1,unfold product_int,admit,

    
    have H2B:∀ p,p ∈ pB :: B1↔p=pB∨p∈B1:=begin
        norm_num,
    end,
    have H1B:(∀ (p : ℤ), p ∈ B1 → int_prime p):=begin
        assume p H1,
        have H:=and.elim_left HB p,rw (H2B p) at H,
        exact H (or.intro_right (p=pB) H1),
    end,
    cases classical.em (pA∣pB) with A A,
    have H1:abs(pA)=abs(pB):=sorry,
    unfold count,admit,




end
open nat
def nat_count: nat → (list nat) → nat
| n [] :=0
| n (a::l):= if a=n then (succ (nat_count n l)) else (nat_count n l)
theorem  unique_prime_factorization_nat: ∀ A B:list nat,product A=product B→(∀p:nat, p∈A→prime p)→(∀ p:nat,p∈ B→ prime p)→∀ p:nat,nat_count p A=nat_count p B:=begin
    assume A,
    induction A with pA A1 Hi,
    admit,

    assume B,
    cases B with pB B1,
    admit,

    cases classical.em(pA ∣ pB) with A B,
    have H1:pB = pA:=sorry,
    unfold product,
    have H2:product A1=product B1:=sorry,
    assume H3 H4 H5,
    have H6:(∀ (p : ℕ), p ∈ A1 → prime p):=sorry,
    have H7:(∀ (p : ℕ), p ∈ B1 → prime p):=sorry,
    have Hi2:=Hi B1 H2 H6 H7,rw H1,
    unfold nat_count,admit,

    unfold product,
    have H6:(∀ (p : ℕ), p ∈ A1 → prime p):=sorry,
    have H7:(∀ (p : ℕ), p ∈ B1 → prime p):=sorry,
    have H8:pA ∣ product B1:=sorry,
    have H9:pA ∈ B1:=sorry,
    have H10:∃ B2, pA :: B2 = pB :: B1:=sorry,intros,
    apply exists.elim H10,clear H10,
    assume B2 HB2,
    have H2:product A1=product B2:=sorry,
    have H3:∀p,p∈ B2→prime p:=sorry,
    have Hi2:= Hi B2 H2 H6 H3,
    rw ←HB2,unfold nat_count,
    cases classical.em (pA=p),
    rw a_3,norm_num,rw Hi2 p,
    have H2:pA=p↔false:=sorry,admit,

    
    
end