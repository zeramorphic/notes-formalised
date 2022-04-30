import constructions.rat

-- For now, we just define Cauchy sequences on the rationals.
-- Once we construct the reals, we can use them to make metric spaces.
def real_cauchy_seq (u : ℕ → ℚ) : Prop :=
∀ ε > 0, ∃ N : ℕ, ∀ m n ≥ N, |u m - u n| < ε
