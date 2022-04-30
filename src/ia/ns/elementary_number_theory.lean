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

def of_int (n : ℤ) : rat_repr := ⟨n, 1, nat.one_ne_zero⟩

instance : has_zero rat_repr := ⟨of_int 0⟩
instance : has_one rat_repr := ⟨of_int 1⟩
@[simp] lemma zero_def : (0 : rat_repr) = ⟨0, 1, nat.one_ne_zero⟩ := rfl -- works
@[simp] lemma one_def : (1 : rat_repr) = ⟨1, 1, nat.one_ne_zero⟩ := rfl

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

-- Negation

def neg (p : rat_repr) : rat_repr := ⟨-p.num, p.denom, p.pos⟩

instance : has_neg rat_repr := ⟨neg⟩

@[simp] lemma neg_def (p : rat_repr)
  : -p = ⟨-p.num, p.denom, p.pos⟩ := rfl

lemma neg_respects_r {a b : rat_repr} (h : a ≈ b) : -a ≈ -b :=
begin
  simp at *,
  rw ← int.neg_mul_eq_neg_mul,
  rw ← int.neg_mul_eq_neg_mul,
  rw h
end

-- Addition

def add (p q : rat_repr) : rat_repr :=
⟨p.num * q.denom + q.num * p.denom, p.denom * q.denom, nat.mul_ne_zero p.pos q.pos⟩

instance : has_add rat_repr := ⟨add⟩

@[simp] lemma add_def (p q : rat_repr)
  : p + q = ⟨p.num * q.denom + q.num * p.denom, p.denom * q.denom, nat.mul_ne_zero p.pos q.pos⟩
  := rfl

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

def add_comm : ∀ a b : rat_repr, a + b = b + a :=
begin
  rintros ⟨num₁, denom₁, h₁⟩ ⟨num₂, denom₂, h₂⟩,
  simp,
  split,
  rw int.add_comm,
  rw nat.mul_comm
end

def add_assoc : ∀ a b c : rat_repr, a + b + c ≈ a + (b + c) :=
begin
  intros a b c,
  simp,
  congr' 1,
  { rw int.distrib_right,
    rw int.distrib_right,
    rw int.add_assoc,
    congr' 1,
    { rw int.mul_assoc,
      rw int.coe_nat_mul },
    { congr' 1,
      { rw int.mul_assoc,
        rw int.mul_assoc,
        rw int.mul_comm ↑a.denom },
      { rw int.coe_nat_mul,
        rw int.mul_comm ↑a.denom,
        rw int.mul_assoc } } },
  { rw nat.mul_assoc }
end

lemma zero_add (a : rat_repr) : 0 + a = a :=
begin
  obtain ⟨num, denom, h⟩ := a,
  simp,
  split,
  { rw int.zero_mul,
    rw int.zero_add,
    change num * 1 = num,
    rw int.mul_one },
  { rw nat.one_mul }
end

lemma add_zero (a : rat_repr) : a + 0 = a :=
begin
  rw add_comm,
  exact zero_add a
end

lemma add_left_neg (a : rat_repr) : -a + a ≈ 0 :=
begin
  obtain ⟨num, denom, h⟩ := a,
  simp,
  rw int.zero_mul,
  change (-num * ↑denom + num * ↑denom) * 1 = 0,
  rw int.mul_one,
  rw ← int.distrib_right,
  rw int.add_left_neg,
  rw int.zero_mul
end

lemma add_right_neg (a : rat_repr) : a + -a ≈ 0 :=
begin
  rw add_comm,
  exact add_left_neg a
end

end rat_repr

def rat := quotient rat_repr.setoid
notation `ℚ` := rat

namespace rat

def of_int (n : ℤ) : ℚ := ⟦rat_repr.of_int n⟧

instance : has_zero ℚ := ⟨of_int 0⟩
instance : has_one ℚ := ⟨of_int 1⟩

def neg : ℚ → ℚ := quotient.lift (λ p, ⟦-p⟧)
  (λ a b h, quotient.sound (rat_repr.neg_respects_r h))
instance : has_neg ℚ := ⟨neg⟩

def add : ℚ → ℚ → ℚ := quotient.lift₂ (λ p q, ⟦p + q⟧)
  (λ a₁ a₂ b₁ b₂ h₁ h₂, quotient.sound (rat_repr.add_respects_r h₁ h₂))
instance : has_add ℚ := ⟨add⟩

def sub (p q : ℚ) : ℚ := p + -q
instance : has_sub ℚ := ⟨sub⟩

lemma add_comm : ∀ a b : ℚ, a + b = b + a :=
begin
  intros a b,
  apply quotient.induction_on₂ a b, clear a b,
  intros a b,
  change ⟦a + b⟧ = ⟦b + a⟧,
  rw rat_repr.add_comm
end

lemma add_assoc : ∀ a b c : ℚ, a + b + c = a + (b + c) :=
begin
  intros a b c,
  apply quotient.induction_on₃ a b c, clear a b c,
  intros a b c,
  exact quotient.sound (rat_repr.add_assoc a b c)
end

lemma zero_add (a : ℚ) : 0 + a = a :=
begin
  apply quotient.induction_on a, clear a,
  intro a,
  refine quotient.sound _,
  have : rat_repr.of_int 0 + a = a := rat_repr.zero_add a,
  rw this
end

lemma add_zero (a : ℚ) : a + 0 = a :=
begin
  rw add_comm,
  exact zero_add a
end

lemma add_left_neg (a : ℚ) : -a + a = 0 :=
begin
  apply quotient.induction_on a, clear a,
  intro a,
  refine quotient.sound _,
  change -a + a ≈ 0,
  exact rat_repr.add_left_neg a
end

lemma add_right_neg (a : ℚ) : a + -a = 0 :=
begin
  rw add_comm,
  exact add_left_neg a
end

end rat
