import IncidenceGeometry.Defs

open IncidenceGeometry
namespace ProjectivePlane

variable (P L : Type*) [instPlane : ProjectivePlane P L]

theorem nondeg : ∃ p : Fin 4 → P, Function.Injective p ∧
    ∀ (l : L) (i : Fin 4), ¬(p i 𝐈 l ∧ p (i + 1) 𝐈 l ∧ p (i + 2) 𝐈 l) :=
  ProjectivePlane.nondeg'

theorem dual_nondeg : ∃ l : Fin 4 → L, Function.Injective l ∧
    ∀ (p : P) (i : Fin 4), ¬(p 𝐈 l i ∧ p 𝐈 l (i + 1) ∧ p 𝐈 l (i + 2)) := by
  obtain ⟨p, pinj, h⟩ := nondeg P L
  let l : Fin 4 → L := fun i ↦ join (p i) (p (i + 1))
  have l₀left := fun i ↦ (instPlane.join_incident (p i) (p (i + 1)) (Function.Injective.ne pinj (by simp))).left
  have l₀right := fun i ↦ (instPlane.join_incident (p i) (p (i + 1)) (Function.Injective.ne pinj (by simp))).right
  have l₁left := fun i ↦ (instPlane.join_incident (p (i + 1)) (p (i + 2)) (Function.Injective.ne pinj (by simp))).left
  have aux₁ (i) : l (i + 1) = join (p (i + 1)) (p (i + 2)) := by
    unfold l
    rw [add_assoc]
    rfl
  simp_rw [←aux₁] at l₁left
  have l₁right := fun i ↦ (instPlane.join_incident (p (i + 1)) (p (i + 2)) (Function.Injective.ne pinj (by simp))).right
  simp_rw [←aux₁] at l₁right
  have l₂left := fun i ↦ (instPlane.join_incident (p (i + 2)) (p (i + 3)) (Function.Injective.ne pinj (by simp))).left
  have aux₂ (i) : l (i + 2) = join (p (i + 2)) (p (i + 3)) := by
    unfold l
    rw [add_assoc]
    rfl
  simp_rw [←aux₂] at l₂left
  have l₃left := fun i ↦ (instPlane.join_incident (p (i + 3)) (p i) (Function.Injective.ne pinj (by simp))).left
  have aux₃ (i) : l (i + 3) = join (p (i + 3)) (p i) := by
    unfold l
    rw [add_assoc]
    simp
  simp_rw [←aux₃] at l₃left
  have linj : Function.Injective l := by
    have diff : ∀ (i j : Fin 4), j = i ∨ j = i + 1 ∨ j = i + 2 ∨ j = i + 3 := by decide
    intro i j hij
    rcases diff i j with h₀ | h₁ | h₂ | h₃
    · exact h₀.symm
    · exfalso
      rw [h₁] at hij
      --p i, p (i + 1) and p (i + 2) lie on the same line
      apply h (l i) i
      use l₀left i, l₀right i
      rw [hij]
      use l₁right i
    · exfalso
      rw [h₂] at hij
      --p i, p (i + 1), p (i + 2) and p (i + 3) lie on the same line
      apply h (l i) i
      use l₀left i, l₀right i
      rw [hij]
      use l₂left i
    · exfalso
      rw [h₃] at hij
      --p i, p (i + 1), p (i + 3) lie on the same line
      apply h (l i) (i + 3)
      rw [hij]
      use l₃left i
      rw [←hij, add_assoc, add_assoc]
      simp only [Fin.reduceAdd, add_zero]
      use l₀left i, l₀right i
  use l, linj
  intro q i ⟨h₀, h₁, h₂⟩
  have hq := instPlane.unique_meet (l i) (l (i + 1)) q (Function.Injective.ne linj (by simp)) h₀ h₁
  have hq' := instPlane.unique_meet (l (i + 1)) (l (i + 2)) q (Function.Injective.ne linj (by simp)) h₁ h₂
  have hp₁ := instPlane.unique_meet (l i) (l (i + 1)) (p (i + 1)) (Function.Injective.ne linj (by simp))
    (l₀right i) (l₁left i)
  have hp₂ := instPlane.unique_meet (l (i + 1)) (l (i + 2)) (p (i + 2)) (Function.Injective.ne linj (by simp))
    (l₁right i) (l₂left i)
  have : p (i + 1) = p (i + 2) := by
    rw [hp₁, hp₂, ←hq, ←hq']
  apply pinj at this
  simp at this

instance Dual : ProjectivePlane L P where
  Incident := fun l p => p 𝐈 l
  join := instPlane.meet
  join_incident := instPlane.meet_incident
  unique_join := instPlane.unique_meet
  meet := instPlane.join
  meet_incident := instPlane.join_incident
  unique_meet := instPlane.unique_join
  nondeg' := dual_nondeg P L

variable {P L : Type*} [ProjectivePlane P L]

def points_on_line_equiv_lines_through_point (p : P) (l : L) (h : ¬ p 𝐈 l) : {q : P | q 𝐈 l} ≃ {l' : L | p 𝐈 l'} where
  toFun := fun ⟨q, hq⟩ ↦ ⟨join p q, (join_incident _ _ (by intro hpq; subst hpq; exact h hq)).left⟩
  invFun := fun ⟨l', hl'⟩ ↦ ⟨meet l l', (meet_incident _ _ (by intro hll'; subst hll'; exact h hl')).left⟩
  left_inv := by
    intro ⟨q, hq⟩
    simp only [Subtype.mk.injEq]
    symm
    apply unique_meet
    · intro hl
      apply h
      rw [hl]
      exact (join_incident _ _ (by intro hpq; subst hpq; exact h hq)).left
    · exact hq
    · exact (join_incident _ _ (by intro hpq; subst hpq; exact h hq)).right
  right_inv := by
    intro ⟨l', hl'⟩
    simp only [Subtype.mk.injEq]
    symm
    apply unique_join
    · intro hp
      apply h
      rw [hp]
      exact (meet_incident _ _ (by intro hll'; subst hll'; exact h hl')).left
    · exact hl'
    · exact (meet_incident _ _ (by intro hll'; subst hll'; exact h hl')).right

theorem join_symm (p q : P) : join p q = (join q p : L) :=  by
  by_cases h : p = q
  · rw [h]
  apply unique_join
  · exact Ne.symm h
  · exact (join_incident p q h).right
  · exact (join_incident p q h).left

--application of duality
theorem meet_symm (l₁ l₂ : L) : meet l₁ l₂ = (meet l₂ l₁ : P) :=
  join_symm l₁ l₂

theorem meet_join (p q r : P) (h₁ : p ≠ q) (h₂ : ¬ r 𝐈 (join p q : L)) : meet (L := L) (join p q) (join p r) = p := by
  have hpr : p ≠ r := by
    intro hpr
    apply h₂
    rw [← hpr]
    exact (join_incident p q h₁).left
  symm
  apply unique_meet
  · intro h
    apply h₂
    rw [h]
    exact (join_incident p r hpr).right
  · exact (join_incident p q h₁).left
  · exact (join_incident p r hpr).left

theorem join_cancel {p q r s : P} (h₁ : p 𝐈 (join q r : L)) (h₂ : p 𝐈 (join q s : L)) (h₃ : q ≠ r) (h₄ : ¬ s 𝐈 (join q r : L)) : p = q := by
  have hqs : q ≠ s := by
    intro hqs
    apply h₄
    rw [← hqs]
    exact (join_incident q r h₃).left
  rw [← meet_join q r s (L := L) h₃ h₄]
  · apply unique_meet
    · intro h
      apply h₄
      rw [h]
      exact (join_incident q s hqs).right
    · exact h₁
    · exact h₂

variable (L) in
theorem exists_line_not_through_two_points (p₁ p₂ : P) : ∃ l : L, ¬ p₁ 𝐈 l ∧ ¬ p₂ 𝐈 l := by
  obtain ⟨p, pinj, hp⟩ := nondeg P L
  have middle_case : ∀ q : P, q ≠ p 0 → ∃ l : L, ¬p 0 𝐈 l ∧ ¬q 𝐈 l := by
    intro q hq
    by_cases h : q 𝐈 join (L := L) (p 1) (p 2)
    · by_cases hq : q = p 1
      · subst hq
        use join (p 2) (p 3)
        have h₀ := hp (join (p 2) (p 3)) 2
        have h₁ := hp (join (p 2) (p 3)) 1
        simp only [Fin.isValue, Fin.reduceAdd, not_and] at h₀
        simp only [Fin.isValue, Fin.reduceAdd, not_and] at h₁
        constructor
        · apply h₀
          · exact (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).left
          · exact (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).right
        · intro hp1
          apply h₁ hp1
          · exact (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).left
          · exact (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).right
      · use join (p 1) (p 3)
        constructor
        · intro hp0
          specialize hp (join (p 1) (p 3)) 3
          simp only [Fin.isValue, Fin.reduceAdd, not_and] at hp
          specialize hp (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).right hp0
          exact hp (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).left
        · intro hq'
          apply hq
          apply join_cancel h hq' (by intro hne; have := pinj hne; simp at this)
          specialize hp (join (p 1) (p 2)) 1
          simp only [Fin.isValue, Fin.reduceAdd, not_and] at hp
          exact hp (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).left
            (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).right
    · use join (p 1) (p 2)
      constructor
      · intro hp0
        specialize hp (join (p 1) (p 2)) 0
        simp only [Fin.isValue, zero_add, not_and] at hp
        specialize hp hp0 (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).left
        exact hp (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).right
      · exact h
  by_cases h₁ : p₁ = p 0 <;> by_cases h₂ : p₂ = p 0
  · use join (p 1) (p 2)
    specialize hp (join (p 1) (p 2)) 0
    subst h₁ h₂
    simp only [zero_add, not_and] at hp
    simp only [and_self]
    intro h
    apply hp h (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).left
    exact (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).right
  · --at least one of join (p 1) (p 2), join (p 2) (p 3), join (p 1) (p 3)
    subst h₁
    apply middle_case
    exact h₂
  · --at least one of join (p 1) (p 2), join (p 2) (p 3), join (p 1) (p 3)
    subst h₂
    conv =>
      congr
      intro
      rw [and_comm]
    apply middle_case
    exact h₁
  · --at least one of join (p 0) (p 1), join (p 0) (p 2), join (p 0) (p 3)
    --if p₁ lies on join (p 0) (p 1):
    ---if p₂ lies on join (p 0) (p 2)): use join (p 0) (p 3)
    ---if p₂ does not lie join (p 0) (p 2)): use join (p 0) (p 2)
    --cycle through (1,2,3)
    by_cases hp₁₁ : p₁ 𝐈 (join (p 0) (p 1) : L)
    · by_cases hp₂₂ : p₂ 𝐈 (join (p 0) (p 2) : L)
      · use join (p 0) (p 3)
        constructor
        · intro hp₁₃
          apply h₁
          apply join_cancel hp₁₁ hp₁₃ (by intro hne; have := pinj hne; simp at this)
          specialize hp (join (p 0) (p 1)) 3
          simp only [Fin.isValue, Fin.reduceAdd, not_and] at hp
          intro h
          specialize hp h (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).left
          exact hp (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).right
        · intro hp₂₃
          apply h₂
          apply join_cancel hp₂₂ hp₂₃ (by intro hne; have := pinj hne; simp at this)
          specialize hp (join (p 0) (p 2)) 2
          simp only [Fin.isValue, Fin.reduceAdd, not_and] at hp
          intro h
          apply hp (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).right h
          exact (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).left
      · use join (p 0) (p 2)
        constructor
        · intro h
          apply h₁
          apply join_cancel hp₁₁ h (by intro hne; have := pinj hne; simp at this)
          specialize hp (join (p 0) (p 1)) 0
          simp only [Fin.isValue, zero_add, not_and] at hp
          exact hp (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).left
            (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).right
        · exact hp₂₂
    · by_cases hp₁₂ : p₁ 𝐈 (join (p 0) (p 2) : L)
      · by_cases hp₂₃ : p₂ 𝐈 (join (p 0) (p 3) : L)
        · use join (p 0) (p 1)
          constructor
          · exact hp₁₁
          · intro h
            apply h₂
            apply join_cancel h hp₂₃ (by intro hne; have := pinj hne; simp at this)
            specialize hp (join (p 0) (p 1)) 3
            simp only [Fin.isValue, Fin.reduceAdd, not_and] at hp
            intro h
            apply hp h (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).left
              (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).right
        · use join (p 0) (p 3)
          constructor
          · intro h
            apply h₁
            apply join_cancel hp₁₂ h (by intro hne; have := pinj hne; simp at this)
            specialize hp (join (p 0) (p 2)) 2
            simp only [Fin.isValue, Fin.reduceAdd, not_and] at hp
            intro h
            exact hp (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).right h
              (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).left
          · exact hp₂₃
      · by_cases hp₂₁ : p₂ 𝐈 (join (p 0) (p 1) : L)
        · use join (p 0) (p 2)
          constructor
          · exact hp₁₂
          · intro h
            apply h₂
            apply join_cancel hp₂₁ h (by intro hne; have := pinj hne; simp at this)
            specialize hp (join (p 0) (p 1)) 0
            simp only [Fin.isValue, zero_add, not_and] at hp
            exact hp (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).left
              (join_incident _ _ (by intro hne; have := pinj hne; simp at this)).right
        · use join (p 0) (p 1)

variable (L) in
theorem exists_line_not_through_point (p : P) : ∃ l : L, ¬ p 𝐈 l := by
  obtain ⟨l, hl, _⟩ := exists_line_not_through_two_points L p p
  exact ⟨l, hl⟩

variable (L) in
noncomputable def equiv_lines_through_a_point (p₁ p₂ : P) : {l : L | p₁ 𝐈 l} ≃ {l : L | p₂ 𝐈 l} :=
  let l₀ := Classical.choose (exists_line_not_through_two_points L p₁ p₂)
  let ⟨h₁, h₂⟩ := Classical.choose_spec (exists_line_not_through_two_points L p₁ p₂)
  (points_on_line_equiv_lines_through_point p₁ l₀ h₁).symm.trans (points_on_line_equiv_lines_through_point p₂ l₀ h₂)

--Applications of duality:

variable (P) in
theorem exists_point_not_on_two_lines (l₁ l₂ : L) : ∃ p : P, ¬ p 𝐈 l₁ ∧ ¬ p 𝐈 l₂ :=
  exists_line_not_through_two_points P l₁ l₂

variable (P) in
theorem exists_point_not_on_line (l : L) : ∃ p : P, ¬ p 𝐈 l :=
  exists_line_not_through_point P l

variable (P) in
noncomputable def equiv_points_on_a_line (l₁ l₂ : L) : {p : P | p 𝐈 l₁} ≃ {p : P | p 𝐈 l₂} :=
  equiv_lines_through_a_point P l₁ l₂

end ProjectivePlane
