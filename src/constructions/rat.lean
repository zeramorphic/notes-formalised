import tactic.basic

-- Useful utilities.

class has_abs (α : Type*) := (abs : α → α)
export has_abs (abs)
notation `|`a`|` := abs a

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

namespace int

lemma nonpos_of_mul_pos {a b : ℤ} (hb : 0 < b) (h : a * b ≤ 0) : a ≤ 0 :=
begin
  obtain ⟨n, hn⟩ := int.exists_eq_neg_of_nat h,
  obtain ⟨c, hc⟩ := int.eq_succ_of_zero_lt hb,
  rw hc at hn,
  by_contradiction ha,
  push_neg at ha,
  obtain ⟨m, hm⟩ := int.eq_succ_of_zero_lt ha,
  rw hm at hn,
  rw ← int.coe_nat_mul at hn,
  have : ↑(m.succ * c.succ) + ↑n = -↑n + ↑n, { rw hn },
  rw int.add_left_neg at this,
  rw ← int.coe_nat_add at this,
  change ↑(m.succ * c.succ + n) = ↑0 at this,
  rw int.coe_nat_eq_coe_nat_iff at this,
  have := nat.eq_zero_of_add_eq_zero_right this,
  tauto
end

def abs (x : ℤ) : ℤ := if 0 ≤ x then x else -x
instance : has_abs ℤ := ⟨abs⟩

lemma abs_def (a : ℤ)
  : abs a = if 0 ≤ a then a else -a := rfl

end int

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

lemma denom_nonneg (p : rat_repr) : (0 : ℤ) ≤ ↑p.denom := int.zero_le_of_nat p.denom
lemma denom_pos (p : rat_repr) : 0 < p.denom :=
begin
  have := p.pos,
  cases p.denom,
  { exfalso, exact this rfl },
  exact nat.zero_lt_succ n
end

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

@[simp] lemma neg_num_def (p : rat_repr)
  : (-p).num = -p.num := rfl

@[simp] lemma neg_denom_def (p : rat_repr)
  : (-p).denom = p.denom := rfl

-- Addition

def add (p q : rat_repr) : rat_repr :=
⟨p.num * q.denom + q.num * p.denom, p.denom * q.denom, nat.mul_ne_zero p.pos q.pos⟩

instance : has_add rat_repr := ⟨add⟩

def sub (p q : rat_repr) : rat_repr := p + -q
instance : has_sub rat_repr := ⟨sub⟩

@[simp] lemma add_def (p q : rat_repr)
  : p + q = ⟨p.num * q.denom + q.num * p.denom, p.denom * q.denom, nat.mul_ne_zero p.pos q.pos⟩
  := rfl

@[simp] lemma sub_def (p q : rat_repr) : p - q = p + -q := rfl

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

lemma sub_respects_r {a₁ a₂ b₁ b₂ : rat_repr}
  (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂)
  : a₁ - a₂ ≈ b₁ - b₂ :=
begin
  apply add_respects_r,
  assumption,
  apply neg_respects_r,
  assumption
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

@[simp] lemma zero_add (a : rat_repr) : 0 + a = a :=
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

@[simp] lemma add_zero (a : rat_repr) : a + 0 = a :=
begin
  rw add_comm,
  exact zero_add a
end

@[simp] lemma add_left_neg (a : rat_repr) : -a + a ≈ 0 :=
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

@[simp] lemma add_right_neg (a : rat_repr) : a + -a ≈ 0 :=
begin
  rw add_comm,
  exact add_left_neg a
end

-- Comparison
def le (a b : rat_repr) : Prop := (a - b).num ≤ 0
instance : has_le rat_repr := ⟨le⟩

@[simp] lemma le_def (a b : rat_repr)
  : a ≤ b ↔ (a - b).num ≤ 0 := by refl

/-
lemma le_zero_iff (a b : rat_repr)
  : a ≤ b ↔ a - b ≤ 0 :=
begin
  simp,
  change
    a.num * ↑(b.denom) + -b.num * ↑(a.denom) ≤ 0 ↔
    (a.num * ↑(b.denom) + -b.num * ↑(a.denom)) * 1 + 0 * ↑(a.denom * b.denom) ≤ 0,
  rw int.zero_mul,
  rw int.add_zero,
  rwa int.mul_one
end
-/

lemma le_respects_r {a₁ a₂ b₁ b₂ : rat_repr}
  (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂)
  (hle : a₁ ≤ a₂) : b₁ ≤ b₂ :=
begin
  simp at *,
  have := int.mul_le_mul_of_nonneg_right (int.mul_le_mul_of_nonneg_right hle b₁.denom_nonneg) b₂.denom_nonneg,
  rw [int.mul_assoc 0,
  int.zero_mul,
  int.distrib_right,
  int.distrib_right,
  int.mul_assoc,
  int.mul_assoc,
  int.mul_comm ↑a₂.denom,
  ← int.mul_assoc,
  ← int.mul_assoc,
  h₁,
  int.mul_assoc (-a₂.num),
  int.mul_assoc (-a₂.num),
  int.mul_comm (↑a₁.denom * ↑b₁.denom),
  ← int.mul_assoc,
  ← int.neg_mul_eq_neg_mul,
  h₂,
  int.neg_mul_eq_neg_mul,
  int.mul_assoc,
  int.mul_assoc,
  int.mul_comm ↑a₁.denom,
  ← int.mul_assoc,
  ← int.mul_assoc,
  int.mul_comm ↑a₁.denom,
  ← int.mul_assoc,
  int.mul_assoc (-b₂.num),
  int.mul_comm ↑a₂.denom,
  ← int.mul_assoc,
  int.mul_assoc,
  int.mul_assoc (-b₂.num * ↑(b₁.denom)),
  ← int.distrib_right ] at this,
  have : (0 : ℤ) < ↑(a₂.denom) * ↑(a₁.denom),
  { refine int.mul_pos _ _,
    apply int.coe_nat_lt_coe_nat_of_lt,
    apply denom_pos,
    apply int.coe_nat_lt_coe_nat_of_lt,
    apply denom_pos },
  refine int.nonpos_of_mul_pos this _,
  assumption
end

def lt (a b : rat_repr) : Prop := a ≤ b ∧ ¬ a ≈ b
instance : has_lt rat_repr := ⟨lt⟩

@[simp] lemma lt_def (a b : rat_repr)
  : a < b ↔ a ≤ b ∧ ¬ a ≈ b := by refl

lemma lt_respects_r {a₁ a₂ b₁ b₂ : rat_repr}
  (h₁ : a₁ ≈ b₁) (h₂ : a₂ ≈ b₂)
  (hle : a₁ < a₂) : b₁ < b₂ :=
begin
  obtain ⟨hle₁, hle₂⟩ := hle,
  split,
  { exact le_respects_r h₁ h₂ hle₁ },
  { by_contradiction,
    exact hle₂ (r_trans (r_trans h₁ h) h₂.symm) }
end

def abs (a : rat_repr) : rat_repr := if 0 ≤ a.num then a else -a
instance : has_abs rat_repr := ⟨abs⟩

lemma abs_def (a : rat_repr)
  : abs a = if 0 ≤ a.num then a else -a := rfl

@[simp] lemma abs_num_def (a : rat_repr)
  : (abs a).num = (a.num).abs :=
begin
  rw abs_def,
  by_cases 0 ≤ a.num,
  { rw if_pos, rw int.abs_def, rw if_pos, assumption, assumption },
  { rw if_neg, rw int.abs_def, rw if_neg, simp, assumption, assumption }
end

@[simp] lemma abs_denom_def (a : rat_repr)
  : (abs a).denom = a.denom :=
begin
  rw abs_def,
  by_cases 0 ≤ a.num,
  { rwa if_pos },
  { rw if_neg, simp, assumption }
end

lemma r_respects_nonneg {a b : rat_repr}
  (h : a ≈ b) (hn : 0 ≤ a) : 0 ≤ b := le_respects_r rfl h hn

lemma r_respects_num_nonneg {a b : rat_repr}
  (h : a ≈ b) (hn : 0 ≤ a.num) : 0 ≤ b.num :=
begin
  have := r_respects_nonneg h _,
  { rw le_def at this,
    rw sub_def at this,
    rw zero_add at this,
    simp at this,
    exact int.nonneg_of_neg_nonpos this },
  rw le_def,
  rw sub_def,
  rw zero_add,
  simp,
  exact int.neg_nonpos_of_nonneg hn
end

lemma r_respects_num_neg {a b : rat_repr}
  (h : a ≈ b) (hn : a.num < 0) : b.num < 0 :=
begin
  revert hn,
  contrapose!,
  exact r_respects_num_nonneg h.symm
end

lemma abs_respects_r {a b : rat_repr}
  (h : a ≈ b) : abs a ≈ abs b :=
begin
  simp,
  by_cases hn : 0 ≤ a.num,
  { have := r_respects_num_nonneg h hn,
    rw int.abs_def,
    rw int.abs_def,
    rw if_pos,
    rw if_pos,
    repeat { assumption } },
  { push_neg at hn,
    have := r_respects_num_neg h hn,
    rw int.abs_def,
    rw int.abs_def,
    rw if_neg,
    rw if_neg,
    rw ← int.neg_mul_eq_neg_mul,
    rw ← int.neg_mul_eq_neg_mul,
    congr' 1,
    push_neg,
    assumption,
    push_neg,
    assumption }
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

def le : ℚ → ℚ → Prop := quotient.lift₂ (λ p q, p ≤ q)
  begin
    intros a₁ a₂ b₁ b₂ h₁ h₂,
    dsimp,
    ext,
    split,
    { intro h, exact rat_repr.le_respects_r h₁ h₂ h },
    { intro h, exact rat_repr.le_respects_r h₁.symm h₂.symm h }
  end
instance : has_le ℚ := ⟨le⟩

def lt : ℚ → ℚ → Prop := quotient.lift₂ (λ p q, p < q)
  begin
    intros a₁ a₂ b₁ b₂ h₁ h₂,
    dsimp,
    ext,
    split,
    { intro h, exact rat_repr.lt_respects_r h₁ h₂ h },
    { intro h, exact rat_repr.lt_respects_r h₁.symm h₂.symm h }
  end
instance : has_lt ℚ := ⟨lt⟩

def abs : ℚ → ℚ := quotient.lift (λ p, ⟦|p|⟧)
  (λ a b h, quotient.sound (rat_repr.abs_respects_r h))
instance : has_abs ℚ := ⟨abs⟩

end rat
