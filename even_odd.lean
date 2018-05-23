
def even : nat → Prop :=
λ n, ∃ m, m * 2 = n

def odd : nat → Prop :=
λ n, ∃ m, nat.succ (m * 2) = n

lemma 