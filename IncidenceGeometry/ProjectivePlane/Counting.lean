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

instance finite_points_on_a_line (hfin : order P L < Cardinal.aleph0) (l : L) : Finite {p : P | p 𝐈 l} := by
  have : Nat.card {p : P | p 𝐈 l} > 0 := by
    rw [card_points_on_a_line P rfl l hfin]
    simp
  exact (Nat.card_pos_iff.mp this).right

theorem card_points_on_a_line_except_one {n : ℕ} (h : finorder P L = n) (p : P) (l : L) (hp : p 𝐈 l) (hfin : order P L < Cardinal.aleph0) :
    Nat.card {q : P | q 𝐈 l ∧ q ≠ p} = n := by
  have union_point : {q : P | q 𝐈 l} = {q : P | q 𝐈 l ∧ q ≠ p} ∪ {p} := by
    ext q
    simp only [Set.mem_setOf_eq, Set.union_singleton, Set.mem_insert_iff]
    constructor
    · intro hq
      by_cases hqp : q = p
      · left
        exact hqp
      · right
        exact ⟨hq, hqp⟩
    · intro hq
      rcases hq with hq | hq
      · rw [hq]
        exact hp
      · exact hq.left
  have disj_point : Disjoint {q : P | q 𝐈 l ∧ q ≠ p} {p} := by
    rw [Set.disjoint_singleton_right]
    simp
  rw [← @Nat.add_right_cancel_iff _ _ 1, ← card_points_on_a_line P h l (hfin : order P L < Cardinal.aleph0), union_point]
  unfold Nat.card
  rw [Cardinal.mk_union_of_disjoint disj_point]
  simp only [Cardinal.mk_fintype, Fintype.card_unique, Nat.cast_one]
  rw [Cardinal.toNat_add ?fin (by simp)]
  · simp
  · have step₁ : Cardinal.mk {q : P | q 𝐈 l ∧ q ≠ p} ≤ Cardinal.mk {q : P | q 𝐈 l} := by
      apply Cardinal.mk_le_mk_of_subset
      intro p hp
      exact hp.left
    have step₂ : Cardinal.mk {q : P | q 𝐈 l} < Cardinal.aleph0 := by
      rw [Cardinal.lt_aleph0_iff_set_finite]
      apply Nat.finite_of_card_ne_zero
      rw [card_points_on_a_line P rfl l hfin]
      simp
    exact lt_of_le_of_lt step₁ step₂

variable (L) in
/-- In a projective plane of finite order `n`, every point lies on `n + 1` lines. -/
theorem card_lines_through_a_point {n : ℕ} (h : finorder P L = n) (p : P) (hfin : order P L < Cardinal.aleph0) :
    Nat.card {l : L | p 𝐈 l} = n + 1 := by
  unfold Nat.card
  obtain ⟨l, hl⟩ := exists_line_not_through_point L p
  have e := (points_on_line_equiv_lines_through_point p l hl).symm
  rw [←Cardinal.toNat_lift, Cardinal.mk_congr_lift e, Cardinal.toNat_lift]
  exact card_points_on_a_line P h l hfin

instance finite_lines_through_a_point (hfin : order P L < Cardinal.aleph0) (p : P) :
    Finite {l : L | p 𝐈 l} := by
  have : Nat.card {a : L | p 𝐈 a} > 0 := by
    rw [card_lines_through_a_point L rfl p hfin]
    simp
  exact (Nat.card_pos_iff.mp this).right

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

variable (P  : Type u) (L : Type v) [ProjectivePlane P L]

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

theorem finorder_eq_finorder_dual :
    finorder P L = finorder L P := by
  unfold finorder
  rw [←Cardinal.toNat_lift, order_eq_order_dual P L, Cardinal.toNat_lift]

/-- A projective plane of finite order `n` has `n ^ 2 + n + 1` points. -/
theorem card_points {n : ℕ} (h : finorder P L = n) (hfin : order P L < Cardinal.aleph0) :
    Nat.card P = n * n + n + 1 := by
  obtain ⟨p⟩ := exists_point P L
  let P' := (l : {l : L | p 𝐈 l}) × {q : P | q 𝐈 l.val ∧ q ≠ p}
  have finlines : Finite {l : L | p 𝐈 l} := by
    refine (Nat.card_pos_iff.mp ?_).right
    rw [card_lines_through_a_point L h p hfin]
    simp
  have finline : ∀ l : L, Finite {q | q 𝐈 l ∧ q ≠ p} := by
    intro l
    have : {q | q 𝐈 l ∧ q ≠ p} ⊆ {q | q 𝐈 l} := by
      intro q hq
      exact hq.left
    refine Set.Finite.subset ?_ this
    refine (Nat.card_pos_iff.mp ?_).right
    rw [card_points_on_a_line P h l hfin]
    simp
  have key₁ : Nat.card P' = (n + 1) * n := by
    unfold Nat.card
    rw [Cardinal.mk_sigma]
    have h₁ : ∀ l : L, p 𝐈 l → Cardinal.mk {q | q 𝐈 l ∧ q ≠ p} = n := by
      intro l hl
      rw [← Nat.cast_card, card_points_on_a_line_except_one h p l hl hfin]
    have h₂ : Cardinal.mk {l : L | p 𝐈 l} = (n + 1 : ℕ) := by
      rw [← Nat.cast_card, card_lines_through_a_point L h p hfin]
    conv =>
      lhs
      rhs
      congr
      intro a
      rw [h₁ a.val a.prop]
    simp only [Cardinal.sum_const, Cardinal.lift_natCast, h₂, map_mul, Cardinal.toNat_natCast]
  have key₂ : Nat.card P = Nat.card P' + 1 := by
    let f : P' → {q : P | q ≠ p} := fun ⟨_, ⟨q, hq⟩⟩ ↦ ⟨q, hq.right⟩
    have hf : Function.Bijective f := by
      rw [Function.bijective_iff_existsUnique]
      intro ⟨q, hqp⟩
      let l : L := join p q
      use ⟨⟨l, (join_incident p q hqp.symm).left⟩, ⟨q, (join_incident p q hqp.symm).right, hqp⟩⟩
      constructor <;> dsimp [f]
      intro ⟨⟨l', hpl'⟩, ⟨q', hq'l', hq'p⟩⟩ hq'q
      simp only [Subtype.mk.injEq] at hq'q
      subst hq'q
      ext <;> dsimp
      subst l
      exact unique_join _ _ _ hq'p.symm hpl' hq'l'
    have h₁ : insert p {q : P | q ≠ p} = ⊤ := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_setOf_eq, Set.top_eq_univ, Set.mem_univ, iff_true]
      by_cases hxp : x = p
      · exact Or.inl hxp
      · exact Or.inr hxp
    have h₂ := Cardinal.mk_insert (a := p) (s := {q : P | q ≠ p})
    simp only [ne_eq, Set.mem_setOf_eq, not_true_eq_false, not_false_eq_true, forall_const,
      h₁, Set.top_eq_univ, Cardinal.mk_univ] at h₂
    have he := Equiv.lift_cardinal_eq (Equiv.ofBijective f hf).symm
    rw [Cardinal.lift_umax, Cardinal.lift_id' (Cardinal.mk ↑P')] at he
    unfold Nat.card
    rw [← he, h₂, Cardinal.toNat_add ?finite (by simp)]
    · simp only [map_one, ne_eq, Cardinal.toNat_lift]
    · rw [←Cardinal.lift_lt, he, Cardinal.lift_aleph0, Cardinal.lt_aleph0_iff_finite]
      apply Finite.instSigma
  rw [key₂, key₁]
  linarith

instance finite_points (hfin : order P L < Cardinal.aleph0) : Finite P := by
  have hP := card_points P L rfl hfin
  have cardpos : Nat.card P > 0 := by
    rw [hP]
    simp
  exact (Nat.card_pos_iff.mp cardpos).right

/-- A projective plane of finite order `n` has `n ^ 2 + n + 1` lines. -/
theorem card_lines {n : ℕ} (h : finorder P L = n) (hfin : order P L < Cardinal.aleph0) :
    Nat.card L = n * n + n + 1 :=
  card_points L P (by rw [finorder_eq_finorder_dual, h]) (dual_finite hfin)

instance finite_lines (hfin : order P L < Cardinal.aleph0) : Finite L := by
  have hL := card_lines P L rfl hfin
  have cardpos : Nat.card L > 0 := by
    rw [hL]
    simp
  exact (Nat.card_pos_iff.mp cardpos).right
