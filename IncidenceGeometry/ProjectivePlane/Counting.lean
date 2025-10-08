import IncidenceGeometry.ProjectivePlane.Basic

namespace ProjectivePlane

universe u v
variable (P  : Type u) (L : Type v) [ProjectivePlane P L]

/-- The order of a projective plane is the number of points on each line, minus one. -/
def order : Cardinal :=
  let l₀ := Classical.choice (exists_line P L)
  let p₀ := Classical.choose (exists_point_on_line P l₀)
  Cardinal.mk {p : P | p 𝐈 l₀ ∧ p ≠ p₀}

--every line has at least 3 points...

/-- The order of an projective plane is the number of points on each line, minus one. -/
noncomputable def finorder : ℕ := Cardinal.toNat (order P L)

variable {P : Type u} {L : Type v} [ProjectivePlane P L]

theorem finorder_eq_of_order_eq {n : ℕ} (h : order P L = ↑n) : finorder P L = n := by
  simp [finorder, h]

variable (P) in
/-- In a projective plane of finite order `n`, every line has `n + 1` points. -/
theorem card_points_on_a_line {n : ℕ} (h : finorder P L = n) (l : L) (hfin : order P L < Cardinal.aleph0) :
    Nat.card {p : P | p 𝐈 l} = n + 1 := by
  let l₀ := Classical.choice (exists_line P L)
  let p₀ := Classical.choose (exists_point_on_line P l₀)
  let hp₀ := Classical.choose_spec (exists_point_on_line P l₀)
  have union_point : {p : P | p 𝐈 l₀} = {p : P | p 𝐈 l₀ ∧ p ≠ p₀} ∪ {p₀} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.union_singleton, Set.mem_insert_iff]
    constructor
    · intro hp
      by_cases hpp₀ : p = p₀
      · left
        exact hpp₀
      · right
        exact ⟨hp, hpp₀⟩
    · intro hp
      rcases hp with hp | hp
      · rw [hp]
        exact hp₀
      · exact hp.left
  have disj_point : Disjoint {p : P | p 𝐈 l₀ ∧ p ≠ p₀} {p₀} := by
    rw [Set.disjoint_singleton_right]
    simp
  unfold Nat.card
  rw [Cardinal.mk_congr (equiv_points_on_a_line P l l₀), union_point, Cardinal.mk_union_of_disjoint disj_point]
  simp only [Cardinal.mk_fintype, Fintype.card_unique, Nat.cast_one]
  change Cardinal.toNat ((order P L) + 1) = n + 1
  rw [Cardinal.toNat_add hfin (by simp)]
  simp only [map_one, Nat.add_right_cancel_iff]
  exact h

variable (P) in
/-- In a projective plane of infinite order, the order is the number of points on a line. -/
theorem card_points_on_a_line' (l : L) (hinf : order P L ≥ Cardinal.aleph0) :
    Cardinal.mk {p : P | p 𝐈 l} = order P L := by
  unfold order
  let l₀ := Classical.choice (exists_line P L)
  let p₀ := Classical.choose (exists_point_on_line P l₀)
  let hp₀ := Classical.choose_spec (exists_point_on_line P l₀)
  have union_point : {p : P | p 𝐈 l₀} = {p : P | p 𝐈 l₀ ∧ p ≠ p₀} ∪ {p₀} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.union_singleton, Set.mem_insert_iff]
    constructor
    · intro hp
      by_cases hpp₀ : p = p₀
      · left
        exact hpp₀
      · right
        exact ⟨hp, hpp₀⟩
    · intro hp
      rcases hp with hp | hp
      · rw [hp]
        exact hp₀
      · exact hp.left
  have disj_point : Disjoint {p : P | p 𝐈 l₀ ∧ p ≠ p₀} {p₀} := by
    rw [Set.disjoint_singleton_right]
    simp
  rw [Cardinal.mk_congr (equiv_points_on_a_line P l l₀), union_point, Cardinal.mk_union_of_disjoint disj_point]
  simp only [Cardinal.mk_fintype, Fintype.card_unique, Nat.cast_one]
  change order P L + 1 = order P L
  rw [Cardinal.add_one_of_aleph0_le hinf]

variable (L) in
/-- In a projective plane of finite order `n`, every point lies on `n + 1` lines. -/
theorem card_lines_through_a_point {n : ℕ} (h : finorder P L = n) (p : P) (hfin : order P L < Cardinal.aleph0) :
    Nat.card {l : L | p 𝐈 l} = n + 1 := by
  unfold Nat.card
  obtain ⟨l, hl⟩ := exists_line_not_through_point L p
  have e := (points_on_line_equiv_lines_through_point p l hl).symm
  rw [←Cardinal.toNat_lift, Cardinal.mk_congr_lift e, Cardinal.toNat_lift]
  exact card_points_on_a_line P h l hfin

theorem dual_finite (hfin : order P L < Cardinal.aleph0) : order L P < Cardinal.aleph0 := by
  let l₀ := Classical.choice (exists_line L P)
  let p₀ := Classical.choose (exists_point_on_line L l₀)
  unfold order
  have step₁ : Cardinal.mk {l : L | l 𝐈 l₀ ∧ l ≠ p₀} ≤ Cardinal.mk {l : L | l 𝐈 l₀} := by
    apply Cardinal.mk_le_mk_of_subset
    intro p hp
    exact hp.left
  have step₂ : Cardinal.mk {l : L | l 𝐈 l₀} < Cardinal.aleph0 := by
    rw [Cardinal.lt_aleph0_iff_set_finite]
    apply Nat.finite_of_card_ne_zero
    change Nat.card {l : L | l₀ 𝐈 l} ≠ 0
    rw [card_lines_through_a_point L rfl l₀ hfin]
    simp
  exact lt_of_le_of_lt step₁ step₂

variable (P L) in
theorem order_eq_order_dual :
    Cardinal.lift.{v, u} (order P L) = Cardinal.lift.{u, v} (order L P) := by
  let l₀ := Classical.choice (exists_line P L)
  let p₀ := Classical.choose (exists_point_on_line P l₀)
  let p₁ := Classical.choice (exists_line L P)
  let l₁ := Classical.choose (exists_point_on_line L p₁)
  by_cases hfin : order P L < Cardinal.aleph0
  · rw [← Cardinal.toNat_inj_of_lt_aleph0 ?fin ?fin']
    · simp only [Cardinal.toNat_lift]
      change finorder P L = finorder L P
      rw [← @Nat.add_right_cancel_iff _ _ 1]
      obtain ⟨p₀⟩ := exists_point P L
      obtain ⟨l₀⟩ := exists_line P L
      rw [← card_points_on_a_line L rfl p₀ (dual_finite hfin)]
      change _ = Nat.card {l : L | p₀ 𝐈 l}
      rw [card_lines_through_a_point L rfl p₀ hfin]
    · simp only [gt_iff_lt, Cardinal.lift_lt_aleph0]
      exact hfin
    · simp only [gt_iff_lt, Cardinal.lift_lt_aleph0]
      exact dual_finite hfin
  · have hfin' : Cardinal.aleph0 ≤ order L P := by
      rw [←not_lt]
      intro h
      exact hfin (dual_finite h)
    rw [not_lt] at hfin
    obtain ⟨p⟩ := exists_point P L
    obtain ⟨l, hl⟩ := exists_line_not_through_point L p
    rw [← card_points_on_a_line' P l hfin, ← card_points_on_a_line' L p hfin']
    rw [Cardinal.mk_congr_lift (points_on_line_equiv_lines_through_point p l hl)]
    rfl

variable (P L) in
theorem finorder_eq_finorder_dual :
    finorder P L = finorder L P := by
  unfold finorder
  rw [←Cardinal.toNat_lift, order_eq_order_dual P L, Cardinal.toNat_lift]
