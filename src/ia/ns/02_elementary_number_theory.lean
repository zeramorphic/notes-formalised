import tactic

-- 2.2 Strong induction

-- Use nat.strong_induction_on
private theorem nat.strong_induction
  {p: ℕ → Prop}
  (h₀: p 0)
  (h: ∀ n, (∀ k < n, p k) → p n)
  : ∀ n, p n :=
begin
  let q := λ n, ∀ k ≤ n, p k,
  have : ∀ n, q n,
  { intro n,
    refine nat.rec_on n _ _; clear n,
    { change ∀ k ≤ 0, p k,
      intros k hk,
      convert h₀,
      linarith },
    { intros n hqn k k_le_succ_n,
      cases eq_or_lt_of_le k_le_succ_n with h₁ h₁,
      { rw h₁,
        refine h _ _,
        intros j j_lt_succ_n,
        exact hqn j (nat.le_of_lt_succ j_lt_succ_n) },
      { exact hqn _ (nat.le_of_lt_succ h₁) } } },
  intro n,
  refine this n n (rfl.le),
end
