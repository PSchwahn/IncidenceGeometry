import IncidenceGeometry.ProjectivePlane.Basic

namespace ProjectivePlane

variable (P L : Type*) [ProjectivePlane P L]

/-- The order of a projective plane is the number of points on each line, minus one. -/
def order : Cardinal :=
  let l₀ := Classical.choice (exists_line P L)
  let p₀ := Classical.choose (exists_point_on_line P l₀)
  Cardinal.mk {p : P | p 𝐈 l₀ ∧ p ≠ p₀}

--every line has at least 3 points...

/-- The order of an projective plane is the number of points on each line, minus one. -/
noncomputable def finorder : ℕ := Cardinal.toNat (order P L)

variable {P L : Type*} [ProjectivePlane P L]

theorem finorder_eq_of_order_eq {n : ℕ} (h : order P L = ↑n) : finorder P L = n := by
  simp [finorder, h]

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

/-- In a projective plane of infinite order, the order is the number of points on a line. -/
theorem card_points_on_a_line' (l : L) (hinf : order P L ≥ Cardinal.aleph0) :
    Cardinal.mk {p : P | p 𝐈 l} = order P L := by
  sorry
