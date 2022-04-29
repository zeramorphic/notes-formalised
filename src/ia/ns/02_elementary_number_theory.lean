import tactic.basic

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
      cases (lt_or_eq_of_le hk) with h₁ h₂,
      { exfalso,
        have := lt_of_le_of_lt (nat.zero_le k) h₁,
        exact ne_of_lt this rfl },
      { assumption } },
    { intros n hqn k k_le_succ_n,
      cases nat.eq_or_lt_of_le k_le_succ_n with h₁ h₁,
      { rw h₁,
        refine h _ _,
        intros j j_lt_succ_n,
        exact hqn j (nat.le_of_lt_succ j_lt_succ_n) },
      { exact hqn _ (nat.le_of_lt_succ h₁) } } },
  intro n,
  refine this n n (le_refl n),
end

-- 2.4 The rationals

-- Useful utilities.
namespace nat

theorem mul_ne_zero {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) : a * b ≠ 0 :=
begin
  obtain ⟨a₂, ha₂⟩ := nat.exists_eq_succ_of_ne_zero ha,
  obtain ⟨b₂, hb₂⟩ := nat.exists_eq_succ_of_ne_zero hb,
  rw ha₂,
  rw hb₂,
  rw nat.succ_mul,
  rw nat.mul_succ,
  have b₂_ne_zero : b₂.succ ≠ 0 := nat.succ_ne_zero b₂,
  by_contradiction h,
  have b₂_eq_zero := nat.eq_zero_of_add_eq_zero_left h,
  exact b₂_ne_zero b₂_eq_zero
end

end nat

-- A representation of a rational.
structure rat_repr :=
(num : ℤ)
(denom : ℕ)
(pos : denom ≠ 0)

namespace rat_repr

-- Rational representations are equal if their cross-multiplication is equal.
def r (p q : rat_repr) : Prop :=
p.num * q.denom = q.num * p.denom

def r_refl : reflexive r :=
begin
  intro x,
  unfold r
end

def r_symm : symmetric r :=
begin
  intros x y h,
  unfold r at *,
  rw h,
end

def r_trans : transitive r :=
begin
  intros x y z h₁ h₂,
  unfold r at *,
  have : ↑y.denom ≠ (0 : ℤ),
  { rw ← int.coe_nat_zero,
    by_contradiction,
    exact y.pos (int.coe_nat_inj h) },
  refine int.eq_of_mul_eq_mul_left this _,
  rw [
    ← int.mul_assoc,
    int.mul_comm ↑y.denom,
    h₁,
    int.mul_assoc,
    ← int.mul_comm ↑z.denom,
    ← int.mul_assoc,
    h₂,
    int.mul_comm z.num,
    int.mul_assoc
  ]
end

instance setoid : setoid rat_repr := ⟨r, r_refl, r_symm, r_trans⟩

@[simp] lemma equiv_def (p q : rat_repr)
  : p ≈ q ↔ p.num * q.denom = q.num * p.denom
  := by refl

def add (p q : rat_repr) : rat_repr :=
⟨p.num * q.denom + q.num * p.denom, p.denom * q.denom, nat.mul_ne_zero p.pos q.pos⟩

instance : has_add rat_repr := ⟨add⟩

@[simp] lemma add_def (p q : rat_repr)
  : p + q = ⟨p.num * q.denom + q.num * p.denom, p.denom * q.denom, nat.mul_ne_zero p.pos q.pos⟩ :=
rfl

lemma add_respects_r {a₁ a₂ b₁ b₂ : rat_repr}
  (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂)
  : a₁ + a₂ ≈ b₁ + b₂ :=
begin
  simp at *,
  repeat { rw int.distrib_right },
  repeat { rw int.coe_nat_mul },
  have : a₁.num * ↑(a₂.denom) * (↑(b₁.denom) * ↑(b₂.denom)) = b₁.num * ↑(b₂.denom) * (↑(a₁.denom) * ↑(a₂.denom)),
  { rw int.mul_assoc,
    rw ← int.mul_assoc ↑a₂.denom,
    rw int.mul_comm ↑a₂.denom,
    rw int.mul_assoc ↑b₁.denom,
    rw ← int.mul_assoc,
    rw h₁,
    rw int.mul_assoc,
    rw int.mul_assoc,
    rw int.mul_comm ↑a₂.denom,
    rw ← int.mul_assoc ↑a₁.denom,
    rw int.mul_comm ↑a₁.denom,
    rw int.mul_assoc ↑b₂.denom },
  rw this,
  have : a₂.num * ↑(a₁.denom) * (↑(b₁.denom) * ↑(b₂.denom)) = b₂.num * ↑(b₁.denom) * (↑(a₁.denom) * ↑(a₂.denom)),
  { rw int.mul_comm ↑b₁.denom,
    rw int.mul_assoc,
    rw ← int.mul_assoc ↑a₁.denom,
    rw int.mul_comm ↑a₁.denom,
    rw int.mul_assoc ↑b₂.denom,
    rw ← int.mul_assoc,
    rw h₂,
    rw int.mul_assoc,
    rw int.mul_assoc,
    rw int.mul_comm ↑a₂.denom,
    rw ← int.mul_assoc ↑b₁.denom,
    rw int.mul_comm ↑a₁.denom },
  rw this
end

end rat_repr

def rat := quotient rat_repr.setoid
notation `ℚ` := rat

namespace rat

def of_int (n : ℤ) : ℚ := ⟦⟨n, 1, nat.one_ne_zero⟩⟧

instance : has_zero ℚ := ⟨of_int 0⟩
instance : has_one ℚ := ⟨of_int 1⟩

def add_aux (p q : rat_repr) : ℚ := ⟦p + q⟧

def add : ℚ → ℚ → ℚ := quotient.lift₂ add_aux
begin
  intros a₁ a₂ b₁ b₂ h₁ h₂,
  have := rat_repr.add_respects_r h₁ h₂,
  exact quotient.sound this
end

end rat
