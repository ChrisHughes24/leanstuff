

inductive xnat
| zero : xnat
| succ : xnat → xnat
open xnat
#print xnat.succ.inj
#print xnat.no_confusion
definition one := succ zero
definition two := succ one
definition add :xnat → xnat → xnat
| n zero := n
| n (succ p) := succ (add n p)
notation a + b := add a b
theorem one_add_one_equals_two : one + one = two :=
    begin
        unfold two,
        unfold one,
        unfold add,
    end
theorem add_zerox (n:xnat): n+zero=n:=
    begin
        unfold add,
    end
theorem zero_addx (n:xnat):zero+n=n:=
    begin
        induction n with k H,
        unfold add,
        unfold add,
        rw[H],
    end
theorem add_assocx (a b c:xnat):(a+b)+c=a+(b+c):=
    begin
        induction c with k H,
        unfold add,
        unfold add,
        rw[H],
    end
theorem zero_add_eq_add_zerox (n:xnat) : zero+n=n+zero:=
    begin 
        rw[zero_addx,add_zerox],
    end
theorem add_one_eq_succx (n:xnat) : n + one = succ n:=
    begin
        unfold one add,
    end
theorem one_add_eq_succx (n : xnat) : one+n=succ n:=
    begin
        induction n with k H,
        unfold one add,
        unfold one add,
        rw[←H],
        unfold one,
    end
theorem succ_addx (a b:xnat) : succ (a + b) = succ a + b:=begin
    induction b with b hi,
    trivial,
    unfold add,rw hi,
end
theorem add_commx (a b:xnat) : a+b = b+a:=
    begin
        induction b with k H,
        rw[zero_add_eq_add_zerox],
        unfold add,
        rw [H,succ_addx],
    end
theorem eq_iff_succ_eq_succ (a b : xnat) : succ a = succ b ↔ a = b :=
    begin
        split,
        exact succ.inj,
        assume H : a = b,
        rw [H],
    end
theorem add_cancel_right (a b t : xnat) :  a = b ↔ a+t = b+t :=
    begin
        split,
        assume H,
        rw[H],
        induction t with k H,
        rw[add_zerox,add_zerox],
        assume H1,
        exact H1,
        unfold add,
        rw[eq_iff_succ_eq_succ],
        exact H,
    end
definition mul:xnat→xnat→xnat
| n zero:=zero
| n (succ p):= mul n p + n
notation a * b := mul a b
theorem mul_zerox (a : xnat) : a * zero = zero :=
    begin
        trivial,
    end
theorem zero_mulx (a : xnat) : zero * a = zero :=
    begin
        induction a with k H,
        unfold mul,
        unfold mul add,
        rw[H],
    end
theorem mul_onex (a : xnat) : a * one = a :=
    begin
        unfold one mul,
        rw[zero_addx],
    end
theorem one_mulx (a : xnat) : one * a = a :=
    begin
        induction a with k H,
        unfold mul,
        unfold mul,
        rw[add_one_eq_succx, H],
    end
theorem right_distribx (a b c : xnat) : a * (b + c) = a* b + a * c :=
    begin
        induction c with k H,
        rw[mul_zerox,add_zerox,add_zerox],
        unfold add mul,
        rw[H, add_assocx],
    end
theorem left_distribx (a b c : xnat) : (a + b) * c = a * c + b * c :=
    begin
        induction c with n Hn,
        unfold mul,
        refl,
        rw [←add_one_eq_succx,right_distribx,Hn,right_distribx,right_distribx],
        rw [mul_onex,mul_onex,mul_onex],
        rw [add_assocx,←add_assocx (b*n),add_commx (b*n),←add_assocx,←add_assocx,←add_assocx],
    end
theorem mul_assocx (a b c : xnat) : (a * b) * c = a * (b * c) :=
    begin
        induction c with k H,
        rw[mul_zerox,mul_zerox,mul_zerox],
        unfold mul,
        rw[right_distribx,H]
    end
theorem mul_commx (a b : xnat) : a * b = b * a :=
    begin
        induction b with k H,
        rw[mul_zerox,zero_mulx],
        unfold mul,
        rw[H],
        exact calc k * a + a = k * a + one * a: by rw[one_mulx]
        ...=(k + one) * a: by rw[left_distribx]
        ...=succ k * a: by rw[add_one_eq_succx],
    end
definition lt : xnat → xnat → Prop 
    | zero zero := false
    | (succ m) zero := false
    | zero (succ p) := true 
    | (succ m) (succ p) := lt m p

notation b > a := lt a b 
notation a < b := lt a b

theorem inequality_A1 (a b t : xnat) : a < b → a + t < b + t :=
    begin
        induction t with n H,
        rw[add_zerox,add_zerox],
        assume H1,
        exact H1,
        unfold add lt, exact H,
    end
theorem blah: ∀a b c:xnat,a<b→b<c→a<c:=begin
    assume a,
    induction a with a1 Hia,
        assume b c,
        cases b with b1,
            unfold lt,cc,
            
            
            cases c with c1,
                unfold lt,cc,

                unfold lt,cc,
        assume b c,
        cases b with b1,
            unfold lt,cc,

            cases c with c1,
                unfold lt,cc,

                unfold lt,
                exact Hia b1 c1,
end
theorem blah1: ∀a b c:xnat,a<b→b<c→a<c:=begin
    assume a b, revert a,
    induction b with b1 Hib,
        assume a,
        cases a with a1,
            unfold lt,cc,

            unfold lt,cc,
        assume a c,
        cases c with c1,
            unfold lt,cc,

        cases a with a1,
            unfold lt,cc,

            unfold lt,exact Hib a1 c1,
end
theorem blah2: ∀a b c:xnat,a<b→b<c→a<c:=begin
    assume a b c,revert a b,
    induction c with c1 Hic,
        assume a b,
        cases b with b1,
            unfold lt,cc,

            unfold lt,cc,
        
        assume a b,
        cases a with a1,
            unfold lt,cc,

            cases b with b1,
                unfold lt,trivial,

                unfold lt,exact Hic a1 b1,
end
#check list.
#print blah2
theorem subtraction :∀ a b:xnat,a<b→∃c,c+a=b:=begin
    assume a,
    induction a with a1 Hia,
        assume b H1,
        existsi b, unfold add,
        
        assume b1,
        cases b1 with b2,
            unfold lt,trivial,

            unfold lt,
            assume H2,
            apply exists.elim (Hia b2 H2),
            assume c H3,
            existsi c,rw ←H3,unfold add,

end
theorem a_lt_a_add_succ_b (a b:xnat):a<a+succ b:=begin
    induction a with a1 Ha,
    rw zero_addx,unfold lt,
    unfold add lt,rwa[←add_one_eq_succx,add_assocx,one_add_eq_succx],
end
theorem blah3 (x y:xnat):zero<x→one<y→x<x*y:=begin
    cases x with x1,
        unfold lt,cc,

        cases y with y1,
            unfold one lt,cc,

            cases y1 with y2,
                unfold one lt,cc,

                unfold one lt mul,
                rw[add_commx,←one_add_eq_succx,add_assocx,one_add_eq_succx,one_add_eq_succx],
                unfold lt,
                have H1:x1 + (succ x1 * y2 + succ x1)=x1+succ (succ x1 * y2 + x1):=calc
                    x1 + (succ x1 * y2 + succ x1) = x1 + (succ x1 * y2 + (x1+one)):begin rw ←add_one_eq_succx end
                    ...=x1 + (succ x1 * y2 + x1+one):begin rw add_assocx, end
                    ...=x1 +succ (succ x1 * y2 + x1):begin rw add_one_eq_succx, end,
                rw H1,
                assume H2 H3,
                exact a_lt_a_add_succ_b x1 (succ x1 * y2 + x1),       
end
