import tactic.basic
import constructions.rat

-- For now, we just define Cauchy sequences on the rationals.
-- Once we construct the reals, we can use them to make metric spaces.
def is_real_cauchy_seq (u : ℕ → ℚ) : Prop :=
∀ ε > 0, ∃ N : ℕ, ∀ m n ≥ N, |u m - u n| < ε

abbreviation real_cauchy_seq := {u : ℕ → ℚ // is_real_cauchy_seq u}

namespace real_cauchy_seq

abbreviation rcs := real_cauchy_seq

def add (u v : rcs) : rcs := ⟨
  λ n, u.1 n + v.1 n,
  begin
    intros ε hε,
    have : ε/2 > 0,
    obtain ⟨M, hM⟩ := u.2 ε hε,
    obtain ⟨N, hN⟩ := v.2 ε hε,
    refine ⟨(max M N), _⟩,
  end
⟩

def converges_to_zero (u : real_cauchy_seq) : Prop :=
∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, |u.1 n| < ε

-- r is satisfied if the difference between the two Cauchy sequences converges to zero.
def r (u v : real_cauchy_seq) : Prop := sorry

lemma r_refl : reflexive r := sorry

lemma r_symm : symmetric r := sorry

lemma r_trans : transitive r := sorry

instance setoid : setoid real_cauchy_seq := ⟨r, r_refl, r_symm, r_trans⟩

end real_cauchy_seq
