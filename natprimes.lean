import data.nat.prime
import tactic.norm_num
import data.list.basic
import analysis.real
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
        have H2:=HiL (h::M1),
        clear HiL,revert H2,
        unfold product append list.append,
        rw[←mul_assoc, mul_comm (product L1) h],
        assume H,rw H,clear H,
        induction L1 with h1 L2 HiL1,
            unfold list.append product,

            unfold list.append product,
            rw [HiL1,←mul_assoc,←mul_assoc, mul_comm h h1],
end

theorem prime_eq :∀ p, is_prime p ↔ prime p := begin

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
    cases H4 with c Hc,
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
    cases Hexists with b Hb,
    cases Hb with c Hbc,
    cases Hbc with Hb Hc1,
    cases Hc1 with Hc Hbc,
    cases Hp with H1 Hp,
    have H5:= (Hp c) (dvd_of_mul_left_eq b Hbc),
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
                have A:∃ (b c : ℕ), 2 ≤ b ∧ 2 ≤ c ∧ b * c = succ (succ x):=by{revert Hx1,cc},clear Hx1,
                cases A with b Hb,
                cases Hb with c Hbc1,
                cases Hbc1 with Hb Hc,
                cases Hc with Hc Hbc,
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
                cases (Hiy b Hby H1b) with Lb HLb,
                cases (Hiy c Hcy H1c) with Lc HLc,clear Hiy H1b H1c Hby Hcy,
                cases HLb with HLb1 HLb2,
                cases HLc with HLc1 HLc2,
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

def euclid_r: nat→nat→nat→nat
| b c 0     := c
| b c 1     := b%c
| b c (n+2) := euclid_r b c n % euclid_r b c (succ n)
def euclid_q: nat→nat→nat→nat
| b c 0     := 0
| b c 1     := b/c
| b c (n+2) := euclid_r b c n / euclid_r b c (succ n)
def euclid_x: nat→nat→nat→int
| b c 0     := 0
| b c 1     := 1
| b c (n+2) := euclid_x b c n - euclid_q b c (succ (succ n)) * euclid_x b c (succ n)
def euclid_y: nat→nat→nat→int
| b c 0     := 1
| b c 1     := -euclid_q b c 1
| b c (n+2) := euclid_y b c n - euclid_q b c (succ (succ n)) * euclid_y b c (succ n)
theorem sub_succ2: ∀ n k1 :nat,succ k1≤ n→ succ (n - succ k1)=n-k1:=begin
    intros,
    rw[← add_one,←add_one],
    suffices:n - (k1 + 1) + 1 +k1= n - k1+k1,
        revert this,simp,
    rw [add_comm k1 1, add_assoc,one_add],
    have H:=le_trans (le_succ k1) a,
    rw nat.sub_add_cancel a,
    rw nat.sub_add_cancel H,
end
theorem decreasing_r: ∀ (b c n:ℕ),euclid_r b c (n+1)<euclid_r b c n ∨ ∃m,m≤n+1∧euclid_r b c m = 0 :=begin
    assume b c n,
    induction n with n1 Hin,
        unfold euclid_r,
        cases classical.em(c=0) with A A,
        right,existsi 0,unfold euclid_r,
        rw A,simp,exact dec_trivial,left,
        cases c with c,exfalso,revert A,simp,
        exact mod_lt b (succ_pos c),
        
        unfold euclid_r,rw ←add_one,
        cases classical.em (∃ (m : ℕ), m ≤ n1 + 1 ∧ euclid_r b c m = 0) with A A,
        right,cases A with m Hm,existsi m,
        exact  and.intro (le_trans (and.left Hm) (le_add_right (n1+1) 1)) (and.right Hm),
        cases classical.em(euclid_r b c (n1 + 1)=0) with A A,
        right, existsi n1+1,apply and.intro,norm_num,
        assumption,left,
        cases (euclid_r b c (n1 + 1)) with r,
        exfalso, revert A_1,simp,
        exact mod_lt (euclid_r b c n1) (succ_pos r)
end

theorem gcd_exists: ∀ b c :nat, ∃ n:nat, euclid_r b c (succ n) = 0:=begin
    assume b c ,
    have H:∀ n:nat,n≤c→(∀ m:nat,m≤n→¬euclid_r b c m = 0)→euclid_r b c n≤c-n:=begin
        assume n Hnc Hn,
        induction n with n1 Hin,
        unfold euclid_r,norm_num,
        have Hn1:∀ (m : ℕ), m ≤ n1 → ¬euclid_r b c m = 0:=begin
            assume m Hm,
            have H:=le_trans Hm (le_succ n1),
            exact Hn m H,
        end,
        have Hin1:=Hin (le_trans (le_succ n1) Hnc) Hn1,clear Hin,
        have H1:=decreasing_r b c n1,
        have H3:∀ (m : ℕ),¬( m ≤succ n1 ∧ euclid_r b c m = 0):=begin
            assume m,rw not_and,exact Hn m,
        end,
        have H2:¬∃ (m : ℕ), m ≤ succ n1 ∧ euclid_r b c m = 0:=not_exists_of_forall_not H3,
        have H4:(∃ (m : ℕ), m ≤ succ n1 ∧ euclid_r b c m = 0)↔false:=begin 
            apply iff.intro,exact H2,trivial,
        end,rw H4 at H1,simp at H1,clear H4 H2 H3,
        have H2:= lt_of_lt_of_le H1 Hin1,
        have H3:= succ_le_of_lt H2,
        apply le_of_succ_le_succ,
        rwa sub_succ2 c n1 Hnc,
    end,
    cases classical.em (∃m:nat,m≤ c ∧ euclid_r b c m = 0) with A A,
    apply exists.elim A,assume m Hm,
    cases m with m,unfold euclid_r at Hm,
    existsi 1,unfold  euclid_r,rw and.right Hm,simp,
    existsi m,exact and.right Hm,
    have H1:∀ (m : ℕ),¬( m ≤ c ∧ euclid_r b c m = 0):=forall_not_of_not_exists A,
    clear A,
    have H2: ∀ (m : ℕ), m ≤ c →¬ euclid_r b c m = 0:=begin
        assume m,rw ←not_and,exact H1 m,
    end,
    clear H1,have H3:=H c (le_refl c) (H2),exfalso,revert H3,
    rw nat.sub_self c,
    assume H1,have H3:=eq_zero_of_le_zero H1,revert H3,
    exact H2 c (le_refl c),
end

theorem quotients :∀(b c n:nat), euclid_r b c n - euclid_q b c (succ(succ n)) * euclid_r b c (succ n) = euclid_r b c (succ (succ n)):=begin
    assume b c n,
    unfold euclid_q euclid_r,
    have H1:(euclid_r b c n - euclid_r b c n / euclid_r b c (succ n) * euclid_r b c (succ n))+euclid_r b c n / euclid_r b c (succ n) * euclid_r b c (succ n)= euclid_r b c n % euclid_r b c (succ n)+euclid_r b c n / euclid_r b c (succ n) * euclid_r b c (succ n):=begin
        rw [nat.sub_add_cancel,mul_comm,mod_add_div],
        exact div_mul_le_self (euclid_r b c n) (euclid_r b c (succ n)),
    end,
    apply add_right_cancel H1,
end

theorem almost_bezout: ∀ (c b n:nat), euclid_x c b n * c + euclid_y c b n * b = euclid_r c b n:=begin
    -- semi strong induction, need previous two cases
    have Hi:∀(c b n:nat),euclid_x c b n * c + euclid_y c b n * b = euclid_r c b n ∧ euclid_x c b (succ n) * c + euclid_y c b (succ n) * b = euclid_r c b (succ n):=begin
        assume  c b n,
        induction n with n1 Hin2,
        apply and.intro,
        unfold euclid_x euclid_y euclid_r,simp,
        unfold euclid_x euclid_y euclid_r euclid_q,simp,
        have H1:↑c + -(↑b * ↑(c / b)) + (↑b * ↑(c / b)) = ↑(c % b) +(↑b * ↑(c / b)):=begin
            rw [←int.coe_nat_mul,←int.coe_nat_add,mod_add_div],rw [add_assoc,add_comm (-↑(b * (c / b))) (↑(b * (c / b))),← add_assoc],rw add_neg_cancel_right,
        end,
        revert H1,norm_num,assume H1,rw H1,simp,


        have Hin:=and.left Hin2,
        have Hin1:=and.right Hin2,clear Hin2,
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
      have H2:=mul_add (-↑(euclid_q c b (succ (succ n1)))) (euclid_y c b (succ n1) * ↑b) (euclid_x c b (succ n1)*↑c),rw  ←H2,rw add_comm at Hin1,
      rw Hin1,rw [int.coe_nat_sub,int.coe_nat_mul],simp,
      unfold euclid_q,apply div_mul_le_self,
    end,
    assume c b n,
    exact and.left (Hi c b n),    
end
theorem cd_dvd_r:∀ (b c x:nat), x ∣ b → x∣c→∀ n:nat, x∣euclid_r b c n:=begin
    assume b c x Hb Hc n,
    have Hi:x ∣ euclid_r b c n∧x ∣ euclid_r b c (succ n):=begin
        induction n with n1 Hin,
        unfold euclid_r,
        exact and.intro Hc (iff.elim_right (dvd_mod_iff Hc) Hb),

        unfold euclid_r,
        exact and.intro (and.right Hin) (iff.elim_right (dvd_mod_iff  (and.right Hin)) (and.left Hin)),
    end,
    exact and.left Hi,
end
def is_gcd: nat→nat→nat→Prop
| b c n := n∣b ∧ n ∣ c ∧ (∀ e:nat,e∣b→ e∣c → e∣n)

theorem gcd_euclid: ∀ b c n:nat, euclid_r b c (n+1)=0→is_gcd b c (euclid_r b c n):=begin
    have quotients_mod: ∀ (b c n:nat),(euclid_r b c n)= (euclid_q b c (succ (succ n)))* (euclid_r b c(succ n)) +(euclid_r b c (succ (succ n))):=begin
        assume b c n,
        unfold euclid_q euclid_r,rw [mul_comm,add_comm,mod_add_div],
    end,
    have Hi:∀ (b c n:nat), euclid_r b c (succ(succ n))=0→(∀ k:nat,k≤n→euclid_r b c (succ n) ∣ euclid_r b c (n-k)∧euclid_r b c (succ n) ∣ euclid_r b c (succ(n-k))):=begin       
        assume b c n H,
        unfold euclid_r at H,
        have H2:=dvd_of_mod_eq_zero H,
        assume k Hkn,
        induction k with k1 Hik,
        simp,assumption,
        have Hik3:=Hik ( le_trans (le_succ k1) Hkn),clear Hik,
        have Hik1:= and.left Hik3,
        have Hik2:=and.right Hik3,clear Hik3,
        have Hsucc:(succ (n - succ k1))=n-k1:=sub_succ2 n k1 Hkn,
        apply and.intro,
        have Hup:↑(euclid_r b c (succ n)) ∣ ↑(euclid_r b c (n - succ k1)):=begin
            rw quotients_mod b c (n- succ k1),rw Hsucc,
            rw ←int.coe_nat_dvd at Hik2,
            rw← int.coe_nat_dvd at Hik1,
            exact dvd_add (dvd_mul_of_dvd_right Hik1 (euclid_q b c (succ (n - k1)))) Hik2,
        end,
        rwa ←int.coe_nat_dvd,
        rwa Hsucc,
    end,
    assume b c n Hn,
    have H1:euclid_r b c n ∣ c:=begin
        cases n with n1,
        unfold euclid_r,exact dvd_refl c,rw add_one at Hn,
        have Hi1:= Hi b c n1 Hn n1 (le_refl n1),
        have H1:=nat.sub_self n1,
        rw H1 at Hi1,
        unfold euclid_r at Hi1,
        exact and.left Hi1,
    end,
    have H2:euclid_r b c n ∣ (b%c):=begin
        cases n with n1,
        unfold euclid_r,unfold euclid_r at Hn,rw Hn,
        exact dvd_zero c,
        cases n1 with n2,
        unfold euclid_r,exact dvd_refl (b%c),
        have Hi1:= Hi b c (succ n2) Hn n2,
        have H1:succ n2-n2=1:=begin rw ←zero_add 1,have H2:=nat.sub_self n2,rw[←H2,add_one],exact succ_sub (le_refl n2), end,
        rw H1 at Hi1,
        have H3: euclid_r b c 1 =b%c:=by unfold euclid_r,
        rw ←H3,exact and.left (Hi1 (le_succ n2)),
    end,
    unfold is_gcd,rw ←dvd_mod_iff H1,
    exact and.intro H2 (and.intro H1 (λ e Heb Hec,cd_dvd_r b c e Heb Hec n)),
end
theorem bezout: ∀ b c:nat,  ∃ (x y:ℤ) (d:nat), x *↑b + y*↑c = ↑d∧is_gcd b c d:=
    λ b c,exists.elim (gcd_exists b c) (λ n Hn,exists.intro (euclid_x b c n) 
    (exists.intro (euclid_y b c n) (exists.intro (euclid_r b c n) 
    ⟨almost_bezout b c n,gcd_euclid b c n Hn⟩)))

theorem gcdprime:∀ p x:nat, prime p → ∀ d, is_gcd x p d → d=1 ∨ d=p:=begin
    unfold prime is_gcd,   
    assume p x Hp d Hd, exact (and.right Hp) d (and.left(and.right Hd)),
end

theorem euclids_lemma: ∀b c p:nat, prime p → p ∣ (b*c) → p ∣ b ∨ p ∣ c:=begin
    assume b c p Hp Hpbc,
    have Hgcdb:=gcdprime p b Hp,
    have H1:= bezout b p,
    cases H1 with x H,
    cases H with y H1,
    cases H1 with d Hxyd,
    cases Hxyd with Hbz Hd,
    cases (Hgcdb d Hd) with A A,
    rw A at Hbz,
    have Hbz2:↑ c*(x * ↑b) + ↑ c*(y * ↑p) = ↑ c*↑1:=by rw[←mul_add,Hbz],
    rw [mul_comm x ↑b,←mul_assoc,←mul_assoc,mul_comm ↑c ↑b] at Hbz2,right,
    rw [←int.coe_nat_dvd,int.coe_nat_mul ]at Hpbc,
    have H2:=dvd_add (dvd_mul_of_dvd_left Hpbc x)(dvd_mul_of_dvd_right (dvd_refl ↑p) (↑c*y)),
    rw Hbz2 at H2,simp at H2,
    rwa ←int.coe_nat_dvd,
    
    unfold is_gcd at Hd,rw A at Hd,left,
    exact and.left Hd,
end

theorem product_dvd: ∀ (p:nat) (L:list nat),p∈L→ p ∣ product L:=begin
    assume p L,revert p,
    induction L with p1 L1 HiL,
        norm_num,
        unfold product,norm_num,
        assume p2 Hp,
        have H:= HiL p2 Hp,
        exact dvd_mul_of_dvd_right H p1,
end
theorem listcount1:∀ B:list nat,∀ x y1 y2:nat, list.count x (y1::y2::B) = list.count x (y2::y1::B):=begin
    assume B x y1 y2,
    cases classical.em (x=y1) with H H,
    cases classical.em (x=y2) with H1 H1,
    rw [←H,← H1],rw ← H,
    rw list.count_cons_self,
    rw list.count_cons_of_ne H1,
    rw list.count_cons_of_ne H1,
    rw list.count_cons_self,
    cases classical.em(x=y2) with H1 H1,
    rw← H1,
    rw list.count_cons_of_ne H,
    rw list.count_cons_self,
    rw list.count_cons_self,
    rw list.count_cons_of_ne H,
    rw list.count_cons_of_ne H,
    rw list.count_cons_of_ne H1,
    rw list.count_cons_of_ne H1,
    rw list.count_cons_of_ne H,
end
theorem anti_cons_list:∀ (B1:list nat) (p:nat),p∈ B1→ (∀x:nat,x∈B1→prime x)→ ∃ B2:list nat,(product B1=product (p::B2)∧(∀x:nat,x∈ B2→ prime x)∧(∀ x:nat,list.count x B1 = list.count x (p::B2))):=begin
    assume B1,
    induction B1 with p1 B3 Hi,
    simp,
    assume p2 Hp,
    have H:p2 = p1 ∨ p2 ∈ B3:=by{revert Hp,norm_num},
    cases H with A A,
    assume H2,
    existsi B3,rw A,
    apply and.intro,trivial,
    revert H2,norm_num,

    assume H6 H7,
    have H1:=Hi p2 A H7,
    cases H1 with C HC,
    existsi p1::C,
    unfold product,unfold product at HC,
    rw and.left HC,
    apply and.intro,
    simp,

    apply and.intro,exact H6,
    exact and.left (and.right HC),
    apply and.intro,simp,
    norm_num,
    assume x,
    rw listcount1 C x p2 p1,
    cases classical.em (x=p1) with A A,
    rw A,
    rw list.count_cons_self,
    rw list.count_cons_self,
    rw and.right (and.right HC) p1,
    rw list.count_cons_of_ne A,
    rw list.count_cons_of_ne A,
    rw and.right (and.right HC) x,
end

theorem prime_product_dvd:∀ (B:list nat)(p:nat),prime p→(∀pB, pB ∈ B → prime pB)→p ∣ product B → p ∈ B:=begin
    assume B,
    induction B with p1 B1 Hi,
    unfold product,assume p Hp H H2,exfalso,revert H2,
    exact prime.not_dvd_one Hp,
    assume p2 Hp2 H H1,
    norm_num,
    unfold product at H1,
    have H2:=euclids_lemma p1 (product B1) p2 Hp2 H1,
    cases H2 with A A,
    left,
    have H3:=H p1,
    revert H3,norm_num,assume H4,
    unfold prime at H4,
    have H5:=and.right H4 p2 A,
    have H6:p2=1↔ false:=begin apply iff.intro,unfold prime at Hp2,intro,rw a at Hp2,simp at Hp2,revert Hp2,norm_num, end,
    rw H6 at H5, simp at H5,assumption,
    right,
    have H3:(∀ (pB : ℕ), pB ∈ B1 → prime pB):=begin revert H, norm_num,end,have H2:= Hi p2 Hp2 H3 A,assumption,
end
theorem eq_one_of_mul_eq_one:∀ x y :nat, x*y=1→x=1∧ y=1:=begin
    assume x y,
    cases x with x,
    norm_num,
    cases y with y,norm_num,
    rw [mul_succ,mul_comm,mul_succ,add_comm,succ_add],
    assume Hxy,
    have H:=succ_inj Hxy,
    have H2:=eq_zero_of_add_eq_zero H,apply and.intro,
    rw and.left H2,
    have H3:=eq_zero_of_add_eq_zero (and.right H2),
    rw and.right H3,
end
theorem  unique_prime_factorization: ∀ A B:list nat,product A=product B→(∀p:nat, p∈A→prime p)→(∀ p:nat,p∈ B→ prime p)→∀ p:nat,list.count p A=list.count p B:=begin
assume A,
    induction A with pA A1 Hi,
    unfold product,norm_num,
    assume B HP HA p,
    have H:p∈ B→ ¬p∈ B:=begin
        intro HpB,
        have H:= HA p HpB,
        have H1:=product_dvd p B HpB,
        rw ←HP at H1,
        exfalso,
        exact prime.not_dvd_one H H1,
    end,
    cases classical.em(list.count p B>0) with A A,
    have H1:=H (list.mem_of_count_pos A) (list.mem_of_count_pos A),exfalso,assumption,
    cases (eq_zero_or_pos (list.count p B)),rwa eq_comm, exfalso, exact A a,

    assume B,
    cases B with pB B1,clear Hi,norm_num,
    assume HP Hp Hb,
    exfalso,
    unfold product at HP,
    have H:=and.left (eq_one_of_mul_eq_one pA (product A1) HP),
    unfold prime at Hp, rw H at Hp,revert Hp,simp,norm_num,

    assume HP HppA H6 HppB H7,

    cases classical.em(pA ∣ pB) with A B,
    unfold prime at HppA HppB,
    have H:=and.right HppB pA A,
    have H1:pA=1↔ false:=begin apply iff.intro, assume H2,rw H2 at HppA,revert HppA,norm_num,end,
    rw H1 at H,clear H1,simp at H,
    unfold product at HP, rw H at HP,
    have HpB0: pB>0:=gt_of_ge_of_gt (and.left HppB) (begin norm_num,end),
    have H2:product A1=product B1:=iff.elim_left (nat.mul_left_inj HpB0) HP,


    have Hi2:=Hi B1 H2 H6 H7,assume p,rw H,
    rw ←H,
    cases classical.em(p=pA) with C C,
    rw [C,list.count_cons_self,list.count_cons_self],rw (Hi2 pA),
    rw[list.count_cons_of_ne C,list.count_cons_of_ne C],exact Hi2 p,


    unfold product at HP,
    have HA:(∀ (p : ℕ), p ∈pA:: A1 → prime p):=begin norm_num,exact and.intro HppA H6 end,
    have HB:(∀ (p : ℕ), p ∈ pB::B1 → prime p):=begin norm_num,exact and.intro HppB H7 end,
    have H8:pA ∣ product B1:=begin
        have H:=dvd_mul_right pA (product A1),rw HP at H,
        have H2:=euclids_lemma pB (product B1) pA HppA H,
        have H3:pA ∣ pB↔ false:=by{apply iff.intro, exact B,trivial},rw H3 at H2,simp at H2,assumption
    end,
    have H9:=prime_product_dvd B1 pA HppA H7 H8,
    have H11:pA ∈ pB :: B1:=by{revert H9,intro,right,assumption},
    have H10:=anti_cons_list (pB::B1) pA H11 HB,
    intros,
    cases H10 with B2 HB2,
    unfold product at HB2,rw ←HP at HB2,
    have HpA0:pA>0:=gt_of_ge_of_gt (and.left HppA) (by norm_num),
    have H2:=iff.elim_left (nat.mul_left_inj HpA0) (and.left HB2),
    have H3:=λ p Hp,and.left (and.right HB2) p Hp,
    have H4:=λ p,and.right (and.right HB2) p,
    have Hi2:= Hi B2 H2 H6 H3,
    rw H4,
    cases classical.em (p=pA) with D D,rw D,
    rw[list.count_cons_self,list.count_cons_self, Hi2 pA],
    rw[list.count_cons_of_ne D,list.count_cons_of_ne D, Hi2 p],
    
end
theorem fundamental_theorem_of_arithmetic: ∀ n:ℕ,1≤n→∃ L:list ℕ, (∀ p:ℕ, p ∈ L → prime p) ∧ product L = n ∧ ∀ M:list ℕ, ((∀ p:ℕ, p ∈ M → prime p) → product M = n → (∀ p:ℕ, list.count p L = list.count p M)):=begin
    assume n Hn,
    cases (prime_product n Hn) with L HL,
    existsi L,
    apply and.intro (and.left HL),
    apply and.intro (and.right HL),
    assume M H1 H2 p,
    rw[eq_comm,←and.right HL] at H2,
    exact (unique_prime_factorization L) M H2 (and.left HL) H1 p,
end
