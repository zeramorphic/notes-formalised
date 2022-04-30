import tactic

-- Use the definition of an irreducible element.
def prime (n: ℕ) : Prop := 1 ≠ n ∧ ∀ a b, a * b = n → a = 1 ∨ b = 1
def composite (n : ℕ) : Prop := ¬ prime n

-- 3.1 Products of primes

def constructive_composite (n: ℕ) : Prop :=
  2 ≤ n → ∃ a b,
    a * b = n ∧
    a < n ∧ b < n ∧
    2 ≤ a ∧ 2 ≤ b

lemma constructive_composite_of_composite {n: ℕ} (hcomp: composite n)
  : constructive_composite n :=
begin
  intro two_le_n,
  unfold composite prime at hcomp,
  push_neg at hcomp,
  obtain ⟨a, b, ⟨prod, a_ne_1, b_ne_1⟩⟩ := hcomp (by linarith),
  have h₁ : 2 ≤ a,
  { cases a,
    { linarith },
    { cases a,
      { exfalso, exact a_ne_1 rfl },
      { refine nat.succ_le_succ _,
        refine nat.succ_le_succ _,
        linarith, } } },
  have h₂ : 2 ≤ b,
  { cases b,
    { linarith },
    { cases b,
      { exfalso, exact b_ne_1 rfl, },
      { refine nat.succ_le_succ _,
        refine nat.succ_le_succ _,
        linarith, } } },
  have a_lt_n : a < n,
  { rw ← prod,
    rw lt_mul_iff_one_lt_right; linarith },
  have b_lt_n : b < n,
  { rw ← prod,
    rw lt_mul_iff_one_lt_left; linarith },
  refine ⟨a, b, ⟨prod, a_lt_n, b_lt_n, h₁, h₂⟩⟩
end

lemma prod_primes (n: ℕ) (hn: 2 ≤ n) :
  ∃ ps: multiset ℕ,
  (∀ p ∈ ps, prime p) ∧ ps.prod = n :=
begin
  revert hn,
  refine nat.strong_induction_on n _,
  clear n,
  intros n hyp hn,
  by_cases hprime: prime n,
  { refine ⟨[n], _⟩,
    split,
    { intros p hp,
      simp at hp,
      rw hp,
      exact hprime, },
    { simp } },
  { obtain ⟨a, ⟨b, ⟨hprod, ha, hb, ha2, hb2⟩⟩⟩ :=
      (constructive_composite_of_composite hprime) hn,
    obtain ⟨ps₁, ⟨hps₁_prime, hps₁_prod⟩⟩ := hyp a ha ha2,
    obtain ⟨ps₂, ⟨hps₂_prime, hps₂_prod⟩⟩ := hyp b hb hb2,
    refine ⟨ps₁ + ps₂, _⟩,
    split,
    { intros p hp,
      simp at hp,
      cases hp,
      { exact hps₁_prime p hp },
      { exact hps₂_prime p hp } },
    { rw multiset.prod_add,
      rw hps₁_prod,
      rwa hps₂_prod } }
end

-- 3.2 Infinite primes

def primes : set ℕ := {x | prime x}

lemma zero_composite : composite 0 :=
begin
  intro h,
  have := (or_self _).1 (h.2 0 0 (by linarith)),
  exact nat.zero_ne_one this
end

lemma one_composite : composite 1 :=
begin
  intro h,
  exact h.1 rfl,
end

lemma two_prime : prime 2 :=
begin
  split,
  { simp },
  { intros a b h,
    cases a,
    { simp at h,
      contradiction, },
    cases b,
      { simp at h,
        contradiction },
    cases a,
    { left,
      refl },
    { right,
      rw nat.succ_mul at h,
      rw nat.succ_mul at h,
      rw nat.succ_eq_add_one at *,
      have : a * (b + 1) + b + b = 0 := by linarith,
      rw add_eq_zero_iff at this,
      rw this.right, } }
end

lemma two_le_prime {n: ℕ} (h: prime n) : 2 ≤ n :=
begin
  cases n,
  { exfalso,
    exact zero_composite h, },
  { cases n,
    { exfalso,
      exact one_composite h, },
    { refine nat.succ_le_succ _,
      refine nat.succ_le_succ _,
      exact zero_le _, } }
end

lemma infinite_primes : set.infinite primes :=
begin
  intro hfinite,
  obtain ⟨all_ps, h⟩ := hfinite.exists_finset,
  let P := all_ps.val.prod + 1,
  have two_le_P : 2 ≤ P,
  { refine nat.succ_le_succ _,
    rw nat.one_le_iff_ne_zero,
    by_contradiction hzero,
    rw multiset.prod_eq_zero_iff at hzero,
    have := (h 0).1 hzero,
    exact zero_composite this },
  obtain ⟨ps, all_prime, prod⟩ := prod_primes P two_le_P,
  have : ∀ p, prime p → p ∉ ps,
  { intros p,
    contrapose!,
    intro p_mem,
    exfalso,
    have := multiset.dvd_prod p_mem,
    rw prod at this,
    -- Technically we've not done division yet.
    -- This is a pretty elementary argument, however.
    have mod_eq_zero : P % p = 0,
    { rwa nat.mod_eq_zero_of_dvd },
    have : all_ps.val.prod % p = 0,
    { rw nat.mod_eq_zero_of_dvd,
      apply multiset.dvd_prod,
      exact (h p).2 (all_prime p p_mem), },
    have mod_eq_one : P % p = 1,
    { rw nat.add_mod,
      rw this,
      simp,
      obtain ⟨p₁, hp₁⟩ := nat.le.dest (two_le_prime (all_prime p p_mem)),
      rw ← hp₁,
      ring_nf },
    rw mod_eq_one at mod_eq_zero,
    exact one_ne_zero mod_eq_zero },
  have : ∃ p, p ∈ ps,
  { cases multiset.empty_or_exists_mem ps with hempty hmem,
    { exfalso,
      rw hempty at prod,
      simp at prod,
      change 2 ≤ all_ps.val.prod + 1 at two_le_P,
      rw prod at two_le_P,
      linarith },
    assumption },
  obtain ⟨p, hp⟩ := this,
  exact this p (all_prime p hp) hp,
end
