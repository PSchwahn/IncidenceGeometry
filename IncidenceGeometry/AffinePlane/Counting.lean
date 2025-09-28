import IncidenceGeometry.AffinePlane.Basic

namespace AffinePlane

variable (P L : Type*) [AffinePlane P L]

/-- The order of an affine plane is the number of points on each line. -/
def order : Cardinal := Cardinal.mk {p : P | p 𝐈 Classical.choice (exists_line P L)}

/-- The order of an affine plane is the number of points on each line. -/
noncomputable def finorder : ℕ := Cardinal.toNat (order P L)

variable {P L : Type*} [AffinePlane P L]

theorem finorder_eq_of_order_eq {n : ℕ} (h : order P L = ↑n) : finorder P L = n := by
  simp [finorder, h]

variable (P) in
/-- In an affine plane of order `n`, every line has `n` points. -/
theorem card_points_on_a_line' (l : L) : Cardinal.mk {p : P | p 𝐈 l} = order P L := by
  apply Cardinal.mk_congr
  apply Nonempty.some
  apply equiv_points_on_a_line

/-- In an affine plane of finite order `n`, every line has `n` points. -/
theorem card_points_on_a_line {n : ℕ} (h : finorder P L = n) (l : L) :
    Nat.card {p : P | p 𝐈 l} = n := by
  unfold Nat.card
  rw [card_points_on_a_line' P l]
  exact h

variable (P L) in
theorem order_ge_2 (hfin : order P L < Cardinal.aleph0) : finorder P L ≥ 2 := by
  obtain ⟨p, pinj, _⟩ := nondeg P L
  unfold finorder
  let l : L := join (p 0) (p 1)
  rw [← card_points_on_a_line' P l] at *
  have lfin := Cardinal.lt_aleph0_iff_finite.mp hfin
  have := join_incident (p 0) (p 1) (Function.Injective.ne pinj (by simp)) (L := L)
  let f : Fin 2 → {q : P | q 𝐈 l} := ![⟨p 0, this.1⟩, ⟨p 1, this.2⟩]
  have finj : Function.Injective f := by
    intro i j hij
    unfold f at hij
    fin_cases i <;> fin_cases j
    · rfl
    · simp only [Set.coe_setOf, Set.mem_setOf_eq, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero,
      Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Subtype.mk.injEq] at hij
      absurd pinj hij
      exact zero_ne_one
    · simp only [Set.coe_setOf, Set.mem_setOf_eq, Fin.isValue, Fin.zero_eta, Matrix.cons_val_zero,
      Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Subtype.mk.injEq] at hij
      absurd pinj hij
      exact one_ne_zero
    · rfl
  have := Nat.card_le_card_of_injective f finj
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
  assumption

variable (L) in
/-- In an affine plane of finite order `n`, every point lies on `n + 1` lines. -/
theorem card_lines_through_a_point {n : ℕ} (h : finorder P L = n) (p : P) (hfin : order P L < Cardinal.aleph0) :
    Nat.card {l : L | p 𝐈 l} = n + 1 := by
  --take a line and a point not on it
  obtain ⟨f, hinj, hf⟩ := nondeg P L
  let p' : P := f 0
  let l : L := join (f 1) (f 2)
  have hpl : ¬ p' 𝐈 l := by
    intro h
    apply hf
    use l
    intro i
    fin_cases i
    · exact h
    · exact (join_incident (f 1) (f 2) (Function.Injective.ne hinj (by simp))).1
    · exact (join_incident (f 1) (f 2) (Function.Injective.ne hinj (by simp))).2
  --l has n points, so we can draw n distinct lines through p
  let j : {q : P | q 𝐈 l} → L := fun ⟨q, _⟩ ↦ join p' q
  have pisnt : ∀ q : P, q 𝐈 l → p' ≠ q := by
    intro q hq hpq
    apply hpl
    rw [hpq]
    assumption
  have jinj : Function.Injective j := by
    intro ⟨q₁, hq₁⟩ ⟨q₂, hq₂⟩ hjq
    --show that j q₁ = j q₂ = l, thus p 𝐈 l if q₁ ≠ q₂
    by_contra hq
    simp only [Subtype.mk.injEq] at hq
    have lisq₁q₂ : l = join q₁ q₂ := unique_join _ _ _ hq hq₁ hq₂
    have j₁isq₁q₂ : j ⟨q₁, hq₁⟩ = join q₁ q₂ := by
      apply unique_join _ _ _ hq
      · exact (join_incident p' q₁ (pisnt q₁ hq₁)).2
      · rw [hjq]
        exact (join_incident p' q₂ (pisnt q₂ hq₂)).2
    apply hpl
    rw [lisq₁q₂, ← j₁isq₁q₂]
    exact (join_incident p' q₁ (pisnt q₁ hq₁)).1
  --every line through p is either one of those lines or the parallel of l through p
  have key : {l' : L | p' 𝐈 l'} = {par l p'} ∪ Set.range j := by
    ext l'
    simp only [Set.mem_setOf_eq, Set.coe_setOf, Set.singleton_union, Set.mem_insert_iff,
      Set.mem_range, Subtype.exists]
    constructor
    · intro hpl'
      by_cases hll' : IsParallel P l l'
      · left
        symm
        exact parallel_unique hpl' hll'
      · right
        obtain ⟨q, ⟨hql, hql'⟩, hqunique⟩ := unique_intersection_of_not_parallel hll'
        use q, hql
        symm
        exact unique_join _ _ _ (pisnt q hql) hpl' hql'
    · intro hl'
      rcases hl' with rfl | ⟨q, hql, rfl⟩
      · exact par_incident l p'
      · exact (join_incident p' q (pisnt q hql)).1
  --also this union is disjoint
  have disj : Disjoint {par l p'} (Set.range j) := by
    rw [Set.disjoint_singleton_left]
    intro ⟨⟨q, hql⟩, jqpar⟩
    apply hpl
    have : par l p' = l := by
      apply parallel_prop p' l
      use q
      constructor
      · rw [← jqpar]
        exact (join_incident p' q (pisnt q hql)).2
      · exact hql
    rw [← this]
    exact par_incident l p'
  --now juggle cardinals. what is even the best formulation of the theorem?
  have cardj := Cardinal.mk_range_eq_of_injective jinj
  rw [card_points_on_a_line' P l] at cardj
  unfold Nat.card
  rw [← h, Cardinal.eq.mpr ⟨equiv_lines_through_a_point L p p'⟩, key, Cardinal.mk_union_of_disjoint disj,
    Cardinal.toNat_add (by simp) ?finite]
  · simp only [Cardinal.mk_fintype, Fintype.card_unique, Nat.cast_one, map_one]
    rw [←Cardinal.toNat_lift, cardj, Cardinal.toNat_lift, add_comm]
    rfl
  · rw [← Cardinal.lift_lt, cardj]
    simp only [Cardinal.lift_aleph0, Cardinal.lift_lt_aleph0]
    exact hfin

variable (P L : Type*) [AffinePlane P L]

/-- An affine plane of finite order `n` has `n ^ 2` points. -/
theorem card_points {n : ℕ} (h : finorder P L = n) (hfin : order P L < Cardinal.aleph0) :
    Nat.card P = n * n := by
  have nge2 := order_ge_2 P L hfin
  rw [h] at nge2
  obtain ⟨p⟩ := exists_point P L
  let P' := {(q, l) : P × L | p ≠ q ∧ p 𝐈 l ∧ q 𝐈 l}
  --we count the number of these pairs in two different ways.
  have key₁ : Nat.card P' = (n + 1) * (n - 1) := by
    --p lies on n + 1 lines, so there are n + 1 possibilities for l
    --each of these lines has n points, and q can be n - 1 of them
    --the set above is the disjoint union of {(q, l) | p ≠ q ∧ q 𝐈 l} where l runs through {l | p 𝐈 l}:
    let S : L → Set (P × L) := fun l ↦ {u : P × L | ∃ q, u = (q, l) ∧ p ≠ q ∧ q 𝐈 l}
    let T := (l : {a | p 𝐈 a}) × S l.val
    have hTP' : Nat.card P' = Nat.card T := by
      let f : P' → T := fun ⟨(q, l), ⟨hpq, hpl, hql⟩⟩ ↦ ⟨⟨l, hpl⟩, ⟨(q, l), ⟨q, rfl, hpq, hql⟩⟩⟩
      apply Nat.card_eq_of_bijective f
      rw [Function.bijective_iff_existsUnique]
      intro ⟨⟨l, hpl⟩, ⟨u, ⟨q, hu, hpq, hql⟩⟩⟩
      subst hu
      use ⟨(q, l), ⟨hpq, hpl, hql⟩⟩
      constructor
      · rfl
      · intro ⟨⟨q', l'⟩, ⟨hpq', hpl', hq'l⟩⟩
        dsimp [f]
        intro hq'
        rw [Sigma.ext_iff] at hq'
        simp_all only [Subtype.mk.injEq]
        simp only [Prod.mk.injEq, and_true]
        obtain ⟨hl'l, hq'q⟩ := hq'
        subst hl'l
        rw [heq_eq_eq, Subtype.mk.injEq, Prod.mk.injEq] at hq'q
        exact hq'q.1
    have hS : ∀ l ∈ {a | p 𝐈 a}, Cardinal.mk (S l) = (n - 1 : ℕ) := by
      intro l hpl
      let f : {q : P | p ≠ q ∧ q 𝐈 l} → S l := fun ⟨q, hpq, hql⟩ ↦ ⟨(q, l), ⟨q, rfl, hpq, hql⟩⟩
      have hf : Function.Bijective f := by
        rw [Function.bijective_iff_existsUnique]
        intro ⟨u, q, hu, hpq, hql⟩
        subst hu
        use ⟨q, hpq, hql⟩
        constructor
        · dsimp
        · intro ⟨q', hpq', hq'l⟩
          dsimp [f]
          intro hq'
          simp only [Subtype.mk.injEq, Prod.mk.injEq, and_true] at hq'
          simp only [hq']
      have he := Equiv.lift_cardinal_eq (Equiv.ofBijective f hf)
      have hS' : Cardinal.mk {q : P | p ≠ q ∧ q 𝐈 l} = (n - 1 : ℕ) := by
        have : Finite {q : P | q 𝐈 l} := by
          rw [← Cardinal.lt_aleph0_iff_finite]
          rwa [card_points_on_a_line' P l]
        have : Finite {q | p ≠ q ∧ q 𝐈 l} := by
          apply Finite.Set.subset {q | q 𝐈 l}
          simp only [Set.setOf_subset_setOf, and_imp, imp_self, implies_true]
        have h₁ : insert p {q : P | p ≠ q ∧ q 𝐈 l} = {q | q 𝐈 l} := by
          ext x
          rw [Set.mem_insert_iff]
          constructor
          · intro h
            rcases h with rfl | h
            · exact hpl
            · exact h.2
          · intro h
            by_cases hxp : x = p
            · exact Or.inl hxp
            · exact Or.inr ⟨Ne.symm hxp, h⟩
        have h₂ := Cardinal.mk_insert (a := p) (s := {q : P | p ≠ q ∧ q 𝐈 l})
        simp only [ne_eq, Set.mem_setOf_eq, not_true_eq_false, false_and, not_false_eq_true,
          forall_const, h₁, card_points_on_a_line' P l] at h₂
        apply congrArg Cardinal.toNat at h₂
        rw [Cardinal.toNat_add (by apply Cardinal.lt_aleph0_of_finite) (by simp), map_one] at h₂
        subst h
        unfold finorder
        rw [← Nat.cast_card]
        rw [h₂, add_tsub_cancel_right]
        rfl
      rw [Cardinal.lift_umax, Cardinal.lift_id' (Cardinal.mk ↑(S l))] at he
      rw [← he]
      simp only [Cardinal.lift_eq_nat_iff, hS']
    have hT : Cardinal.mk T = Cardinal.sum fun (l : {a | p 𝐈 a}) ↦ Cardinal.mk (S l.val) := by
      apply Cardinal.mk_sigma
    have hp : Cardinal.mk {a : L | p 𝐈 a} = (n + 1 : ℕ) := by
      have hp' := card_lines_through_a_point L h p hfin
      have hfin' : Nat.card {a : L | p 𝐈 a} > 0 := by
        rw [hp']
        simp
      have : Finite {a : L | p 𝐈 a} := (Nat.card_pos_iff.mp hfin').right
      rw [← Nat.cast_card, hp']
    conv at hT =>
      rhs
      congr
      intro l
      rw [hS l.val l.prop]
    rw [Cardinal.sum_const, hp] at hT
    have hT' : Nat.card T = (n + 1) * (n - 1) := by
      unfold Nat.card
      rw [hT]
      simp only [Cardinal.lift_natCast, map_mul, Cardinal.toNat_natCast]
    rw [hTP', hT']
  have key₂ : Nat.card P = Nat.card P' + 1 := by
    --there are Nat.card P - 1 possibilities for q, but then l = join p q is unique
    let f : {q : P | p ≠ q} → P' := fun ⟨q, hpq⟩ ↦ ⟨(q, join p q), ⟨hpq, join_incident p q hpq⟩⟩
    have hf : Function.Bijective f := by
      rw [Function.bijective_iff_existsUnique]
      intro ⟨(q, l), ⟨hpq, hpl, hql⟩⟩
      use ⟨q, hpq⟩
      constructor
      · simp only [Subtype.mk.injEq, Prod.mk.injEq, true_and, f]
        rw [unique_join _ _ _ hpq hpl hql]
      · intro ⟨q', hpq'⟩
        simp only [Subtype.mk.injEq, Prod.mk.injEq, and_imp, f]
        intro hq'q
        subst hq'q
        simp only [implies_true]
    have h₁ : insert p {q : P | p ≠ q} = ⊤ := by
      ext x
      simp only [Set.mem_insert_iff, Set.mem_setOf_eq, Set.top_eq_univ, Set.mem_univ, iff_true]
      by_cases hxp : x = p
      · exact Or.inl hxp
      · exact Or.inr (Ne.symm hxp)
    have h₂ := Cardinal.mk_insert (a := p) (s := {q : P | p ≠ q})
    simp only [ne_eq, Set.mem_setOf_eq, not_true_eq_false, not_false_eq_true, forall_const,
        h₁, Set.top_eq_univ, Cardinal.mk_univ] at h₂
    have he := Equiv.lift_cardinal_eq (Equiv.ofBijective f hf)
    rw [Cardinal.lift_umax, Cardinal.lift_id' (Cardinal.mk ↑P')] at he
    unfold Nat.card
    rw [← he, h₂, Cardinal.toNat_add ?finite (by simp)]
    simp only [map_one, ne_eq, Cardinal.toNat_lift]
    · rw [←Cardinal.lift_lt, he, Cardinal.lift_aleph0, Cardinal.lt_aleph0_iff_finite]
      have hfin' : Nat.card P' > 0 := by
        rw [key₁]
        simp only [gt_iff_lt, add_pos_iff, zero_lt_one, or_true, mul_pos_iff_of_pos_left,
          tsub_pos_iff_lt]
        linarith
      exact (Nat.card_pos_iff.mp hfin').right
  rw [key₂, key₁, ← mul_self_tsub_one, Nat.sub_add_cancel]
  rw [one_le_mul_self_iff]
  linarith

instance finite_of_order_lt_aleph0 (hfin : order P L < Cardinal.aleph0) : Finite P := by
  have hP := card_points P L rfl hfin
  have nge2 := order_ge_2 P L hfin
  have cardpos : Nat.card P > 0 := by
    rw [hP]
    apply Nat.zero_lt_of_ne_zero
    rw [mul_self_ne_zero]
    linarith
  exact (Nat.card_pos_iff.mp cardpos).right

/-- In an affine plane of finite order `n`, every direction has `n` lines. -/
theorem card_direction {n : ℕ} (h : finorder P L = n) {π : Set L} (hπ : π ∈ Direction P L) :
    Nat.card π = n := by
  obtain ⟨l, hl⟩ := line_of_direction hπ
  obtain ⟨l', hl', _⟩ := exists_line_not_parallel_to_two_lines P l l
  have : l' ∉ π := by
    intro h
    apply hl'
    rw [isparallel_iff_eq_directions l l' hπ hπ hl h]
  unfold Nat.card
  rw [← h, ← Cardinal.toNat_lift, Cardinal.lift_mk_eq'.mpr ⟨direction_equiv_points_on_a_line l' hπ this⟩,
    Cardinal.toNat_lift]
  apply card_points_on_a_line
  rfl

/-- An affine plane of finite order `n` has `n + 1` directions. -/
theorem card_directions {n : ℕ} (h : finorder P L = n) (hfin : order P L < Cardinal.aleph0) :
    Nat.card (Direction P L) = n + 1 := by
  obtain ⟨p⟩ := exists_point P L
  unfold Nat.card
  rw [← card_lines_through_a_point L h p hfin, Cardinal.eq.mpr ⟨directions_equiv_lines_through_a_point p⟩]
  rfl

/-- An affine plane of finite order `n` has `n ^ 2 + n` lines. -/
theorem card_lines {n : ℕ} (h : finorder P L = n) (hfin : order P L < Cardinal.aleph0) :
    Nat.card L = n * (n + 1) := by
  --there are n + 1 directions, each of which has n lines.
  sorry

end AffinePlane
