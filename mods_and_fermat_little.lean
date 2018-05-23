theorem test1 :∀ y:ℕ, ∃ x:ℕ, x-2=y:=λ y,exists.intro (y+2) rfl
#print classical.some
noncomputable def test2 : ℕ → ℕ :=λ y, classical.some (test1 y)
theorem test3 : ∀ y:ℕ,test2 y-2=y:=λ y,classical.some_spec (test1 y)
Sort hello 
#check test3 7