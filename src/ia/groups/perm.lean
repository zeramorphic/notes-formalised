import data.list.cycle
import ia.groups.hom

namespace notes

@[reducible] def sym (X : Type*) := X ≃ X

instance {X : Type*} : semigroup (sym X) := ⟨λ σ τ υ, rfl⟩
instance {X : Type*} : monoid (sym X) := ⟨λ σ, by simp, λ σ, by simp⟩
instance {X : Type*} : group (sym X) := ⟨λ σ, by simp, λ σ, by simp⟩

@[reducible] def sym_fin := sym ∘ fin

-- Cycles

structure cycle_perm (X : Type*) :=
(cy : cycle X)
(nodup : cy.nodup)

variables {X : Type*} [decidable_eq X]

def cycle_perm.next_if_mem (c : cycle_perm X) (x : X) :=
dite (x ∈ c.cy) (c.cy.next c.nodup x) (λ _, x)

lemma cycle_perm.next_if_mem_of_mem {c : cycle_perm X} {x : X} (h : x ∈ c.cy) :
cycle_perm.next_if_mem c x = c.cy.next c.nodup x h :=
begin
  unfold cycle_perm.next_if_mem,
  rw dite_eq_iff, simp, left, exact h
end

lemma cycle_perm.next_if_mem_of_not_mem {c : cycle_perm X} {x : X} (h : x ∉ c.cy) :
cycle_perm.next_if_mem c x = x :=
begin
  unfold cycle_perm.next_if_mem,
  rw dite_eq_iff, simp, right, exact h
end

def cycle_perm.prev_if_mem (c : cycle_perm X) (x : X) :=
dite (x ∈ c.cy) (c.cy.prev c.nodup x) (λ _, x)

lemma cycle_perm.prev_if_mem_of_mem {c : cycle_perm X} {x : X} (h : x ∈ c.cy) :
cycle_perm.prev_if_mem c x = c.cy.prev c.nodup x h :=
begin
  unfold cycle_perm.prev_if_mem,
  rw dite_eq_iff, simp, left, exact h
end

lemma cycle_perm.prev_if_mem_of_not_mem {c : cycle_perm X} {x : X} (h : x ∉ c.cy) :
cycle_perm.prev_if_mem c x = x :=
begin
  unfold cycle_perm.prev_if_mem,
  rw dite_eq_iff, simp, right, exact h
end

instance : has_coe (cycle_perm X) (sym X) := ⟨λ c, ⟨
  cycle_perm.next_if_mem c,
  cycle_perm.prev_if_mem c,
  begin
    intro x,
    by_cases x ∈ c.cy,
    { rw cycle_perm.next_if_mem_of_mem h,
      rw cycle_perm.prev_if_mem_of_mem (cycle.next_mem c.cy c.nodup x h),
      simp },
    { rw cycle_perm.next_if_mem_of_not_mem h,
      rw cycle_perm.prev_if_mem_of_not_mem h }
  end,
  begin
    intro x,
    by_cases x ∈ c.cy,
    { rw cycle_perm.prev_if_mem_of_mem h,
      rw cycle_perm.next_if_mem_of_mem (cycle.prev_mem c.cy c.nodup x h),
      simp },
    { rw cycle_perm.prev_if_mem_of_not_mem h,
      rw cycle_perm.next_if_mem_of_not_mem h }
  end
⟩⟩

lemma cycle_perm.act_def (c : cycle_perm X) (x : X) :
c x = cycle_perm.next_if_mem c x := rfl

@[simp]
lemma cycle_perm.act_of_not_mem {c : cycle_perm X} {x : X} (h : x ∉ c.cy) : c x = x :=
by rw [cycle_perm.act_def, cycle_perm.next_if_mem_of_not_mem h]

@[simp]
lemma cycle_perm.act_mem_of_mem {c : cycle_perm X} {x : X} (h : x ∈ c.cy) : c x ∈ c.cy :=
begin
  rw cycle_perm.act_def,
  rw cycle_perm.next_if_mem_of_mem h,
  simp
end

@[simp]
lemma cycle_perm.act_mem_iff_mem (c : cycle_perm X) (x : X) : x ∈ c.cy ↔ c x ∈ c.cy :=
begin
  split,
  { intro h, exact cycle_perm.act_mem_of_mem h },
  { intro h, by_contradiction g,
    rw cycle_perm.act_of_not_mem g at h,
    exact g h }
end

@[simp]
lemma cycle_perm.act_not_mem_of_not_mem {c : cycle_perm X} {x : X} (h : x ∉ c.cy) : c x ∉ c.cy :=
by { rw cycle_perm.act_of_not_mem h, exact h }

@[simp]
lemma cycle_perm.act_not_mem_iff_not_mem (c : cycle_perm X) (x : X) : x ∉ c.cy ↔ c x ∉ c.cy :=
by rw cycle_perm.act_mem_iff_mem

def cycle_perm.disjoint (c d : cycle_perm X) : Prop := ∀ (x : X), x ∈ c.cy → x ∉ d.cy

lemma cycle_perm.disjoint.symm {c d : cycle_perm X} :
c.disjoint d → d.disjoint c := λ h x hx hc, h x hc hx

lemma cycle_perm.disjoint.symm_iff (c d : cycle_perm X) :
c.disjoint d ↔ d.disjoint c := ⟨cycle_perm.disjoint.symm, cycle_perm.disjoint.symm⟩

lemma cycle_perm.comm_of_disjoint (c d : cycle_perm X) (hcd : cycle_perm.disjoint c d) :
(c : sym X) * d = d * c :=
begin
  ext x,
  change c (d x) = d (c x),
  by_cases x ∈ c.cy,
  { rw cycle_perm.act_of_not_mem (hcd x h),
    rw cycle_perm.act_of_not_mem (hcd _ (cycle_perm.act_mem_of_mem h)) },
  { rw cycle_perm.act_of_not_mem h,
    by_cases x ∈ d.cy,
    { rw cycle_perm.act_of_not_mem (hcd.symm _ (cycle_perm.act_mem_of_mem h) : d x ∉ c.cy) },
    { rw cycle_perm.act_of_not_mem,
      rw cycle_perm.act_of_not_mem,
      assumption, assumption } }
end

-- Cycle decomposition

variable {n : ℕ}

def sym_fin.order (σ : sym_fin n) (x : fin n) : ℕ :=
@nat.find (λ n, 0 < n ∧ (σ ^ n) x = x) _ begin
  obtain ⟨a, b, hne, hab⟩ := fintype.exists_ne_map_eq_of_infinite (λ (n : ℕ), (σ ^ n) x),
  wlog : a < b,
  { exact ne.lt_or_lt hne },
  dsimp at hab,
  refine ⟨b - a, _, _⟩,
  { exact lt_tsub_comm.mp case },
  have : σ ^ b = (σ ^ a) * (σ ^ (b - a)),
  { rw group.nat_pow_comm_pow_of_comm,
    rw group.sub_nat_pow_of_le,
    exact le_of_lt case,
    refl },
  rw this at hab,
  symmetry,
  exact equiv.injective _ hab
end

def sym_fin.orbit_of (σ : sym_fin n) (x : fin n) : list (fin n) :=
list.map (λ n, (σ ^ n) x) $ list.range (sym_fin.order σ x)

@[simp]
lemma sym_fin.orbit_of_nodup (σ : sym_fin n) (x : fin n) : (sym_fin.orbit_of σ x).nodup :=
begin
  unfold sym_fin.orbit_of,
  rw list.nodup_map_iff_inj_on,
  { intros a ha b hb hab,
    by_contradiction hne,
    wlog : a < b,
    { exact ne.lt_or_lt hne },
    have : (σ ^ (b - a)) x = x,
    { have : σ ^ b = (σ ^ a) * (σ ^ (b - a)),
      { rw group.nat_pow_comm_pow_of_comm,
        rw group.sub_nat_pow_of_le,
        exact le_of_lt case,
        refl },
      rw this at hab,
      symmetry,
      exact equiv.injective _ hab },
    have : b - a < σ.order x,
    { rw list.mem_range at ha hb,
      apply lt_of_le_of_lt _ hb,
      norm_num },
    unfold sym_fin.order at this,
    rw nat.lt_find_iff at this,
    refine this (b - a) (le_refl _) ⟨_, _⟩,
    { norm_num, exact case },
    { assumption } },
  { exact list.nodup_range _ }
end

def sym_fin.cycle_of (σ : sym_fin n) (x : fin n) : cycle (fin n) :=
↑(sym_fin.orbit_of σ x)

def sym_fin.cycle_perm_of (σ : sym_fin n) (x : fin n) : cycle_perm (fin n) :=
⟨sym_fin.cycle_of σ x, by { unfold sym_fin.cycle_of, simp }⟩

end notes
