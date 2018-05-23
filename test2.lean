open classical
variables (α : Type) (p q : α → Prop)
variable a : α
variable r : Prop
theorem c4_1 : r→(∃ x:α,r):=
    begin
        rw[exists_],
    end