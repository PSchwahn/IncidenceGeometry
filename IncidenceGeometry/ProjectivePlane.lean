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
  let l₀₁ := instPlane.join (p 0) (p 1)
  let l₀₂ := instPlane.join (p 0) (p 2)
  let l₁₃ := instPlane.join (p 1) (p 3)
  let l₂₃ := instPlane.join (p 2) (p 3)
  let l := ![l₀₁, l₀₂, l₁₃, l₂₃]
  have linj : Function.Injective l := by
    intro i j hij
    --can we golf this? or is this doomed because the definition of l is not so nice?
    fin_cases i <;> fin_cases j <;> dsimp at *
    · exfalso
      apply h (l 0) 0
      use (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).left
      use (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).right
      rw [hij]
      use (instPlane.join_incident (p 0) (p 2) (Function.Injective.ne pinj (by decide))).right
    · exfalso
      apply h (l 0) 3
      rw [hij]
      use (instPlane.join_incident (p 1) (p 3) (Function.Injective.ne pinj (by decide))).right
      rw [←hij]
      use (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).left
      use (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).right
    · exfalso
      apply h (l 0) 0
      use (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).left
      use (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).right
      rw [hij]
      use (instPlane.join_incident (p 2) (p 3) (Function.Injective.ne pinj (by decide))).left
    · exfalso
      apply h (l 0) 0
      use (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).left
      use (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).right
      rw [←hij]
      use (instPlane.join_incident (p 0) (p 2) (Function.Injective.ne pinj (by decide))).right
    · exfalso
      apply h (l 1) 0
      use (instPlane.join_incident (p 0) (p 2) (Function.Injective.ne pinj (by decide))).left
      symm
      use (instPlane.join_incident (p 0) (p 2) (Function.Injective.ne pinj (by decide))).right
      rw [hij]
      use (instPlane.join_incident (p 1) (p 3) (Function.Injective.ne pinj (by decide))).left
    · exfalso
      apply h (l 1) 2
      use (instPlane.join_incident (p 0) (p 2) (Function.Injective.ne pinj (by decide))).right
      rw [hij]
      use (instPlane.join_incident (p 2) (p 3) (Function.Injective.ne pinj (by decide))).right
      rw [←hij]
      use (instPlane.join_incident (p 0) (p 2) (Function.Injective.ne pinj (by decide))).left
    · exfalso
      apply h (l 0) 3
      rw [←hij]
      use (instPlane.join_incident (p 1) (p 3) (Function.Injective.ne pinj (by decide))).right
      rw [hij]
      use (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).left
      use (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).right
    · exfalso
      apply h (l 1) 0
      use (instPlane.join_incident (p 0) (p 2) (Function.Injective.ne pinj (by decide))).left
      symm
      use (instPlane.join_incident (p 0) (p 2) (Function.Injective.ne pinj (by decide))).right
      rw [←hij]
      use (instPlane.join_incident (p 1) (p 3) (Function.Injective.ne pinj (by decide))).left
    · exfalso
      apply h (l 2) 1
      use (instPlane.join_incident (p 1) (p 3) (Function.Injective.ne pinj (by decide))).left
      symm
      use (instPlane.join_incident (p 1) (p 3) (Function.Injective.ne pinj (by decide))).right
      rw [hij]
      use (instPlane.join_incident (p 2) (p 3) (Function.Injective.ne pinj (by decide))).left
    · exfalso
      apply h (l 0) 0
      use (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).left
      use (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).right
      rw [←hij]
      use (instPlane.join_incident (p 2) (p 3) (Function.Injective.ne pinj (by decide))).left
    · exfalso
      apply h (l 1) 2
      use (instPlane.join_incident (p 0) (p 2) (Function.Injective.ne pinj (by decide))).right
      rw [←hij]
      use (instPlane.join_incident (p 2) (p 3) (Function.Injective.ne pinj (by decide))).right
      rw [hij]
      use (instPlane.join_incident (p 0) (p 2) (Function.Injective.ne pinj (by decide))).left
    · exfalso
      apply h (l 2) 1
      use (instPlane.join_incident (p 1) (p 3) (Function.Injective.ne pinj (by decide))).left
      symm
      use (instPlane.join_incident (p 1) (p 3) (Function.Injective.ne pinj (by decide))).right
      rw [←hij]
      use (instPlane.join_incident (p 2) (p 3) (Function.Injective.ne pinj (by decide))).left
  use l, linj
  --show that no point lies on any three of the four lines
  intro q i
  fin_cases i <;> dsimp
  · intro ⟨hq₀, hq₁, hq₂⟩
    --show q = p 0 = p 1
    have hq' := instPlane.unique_meet (l 0) (l 1) q (Function.Injective.ne linj (by decide)) hq₀ hq₁
    have hq'' := instPlane.unique_meet (l 0) (l 2) q (Function.Injective.ne linj (by decide)) hq₀ hq₂
    have hp₀ := instPlane.unique_meet (l 0) (l 1) (p 0) (Function.Injective.ne linj (by decide))
      (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).left
      (instPlane.join_incident (p 0) (p 2) (Function.Injective.ne pinj (by decide))).left
    have hp₁ := instPlane.unique_meet (l 0) (l 2) (p 1) (Function.Injective.ne linj (by decide))
      (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).right
      (instPlane.join_incident (p 1) (p 3) (Function.Injective.ne pinj (by decide))).left
    have : p 0 = p 1 := by
      rw [hp₀, hp₁, ←hq', ←hq'']
    apply pinj at this
    simp at this
  · intro ⟨hq₁, hq₂, hq₃⟩
    --show q = p 2 = p 3
    have hq' := instPlane.unique_meet (l 1) (l 3) q (Function.Injective.ne linj (by decide)) hq₁ hq₃
    have hq'' := instPlane.unique_meet (l 2) (l 3) q (Function.Injective.ne linj (by decide)) hq₂ hq₃
    have hp₂ := instPlane.unique_meet (l 1) (l 3) (p 2) (Function.Injective.ne linj (by decide))
      (instPlane.join_incident (p 0) (p 2) (Function.Injective.ne pinj (by decide))).right
      (instPlane.join_incident (p 2) (p 3) (Function.Injective.ne pinj (by decide))).left
    have hp₃ := instPlane.unique_meet (l 2) (l 3) (p 3) (Function.Injective.ne linj (by decide))
      (instPlane.join_incident (p 1) (p 3) (Function.Injective.ne pinj (by decide))).right
      (instPlane.join_incident (p 2) (p 3) (Function.Injective.ne pinj (by decide))).right
    have : p 2 = p 3 := by
      rw [hp₂, hp₃, ←hq', ←hq'']
    apply pinj at this
    simp at this
  · intro ⟨hq₂, hq₃, hq₀⟩
    --show q = p 1 = p 3
    have hq' := instPlane.unique_meet (l 0) (l 2) q (Function.Injective.ne linj (by decide)) hq₀ hq₂
    have hq'' := instPlane.unique_meet (l 2) (l 3) q (Function.Injective.ne linj (by decide)) hq₂ hq₃
    have hp₁ := instPlane.unique_meet (l 0) (l 2) (p 1) (Function.Injective.ne linj (by decide))
      (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).right
      (instPlane.join_incident (p 1) (p 3) (Function.Injective.ne pinj (by decide))).left
    have hp₃ := instPlane.unique_meet (l 2) (l 3) (p 3) (Function.Injective.ne linj (by decide))
      (instPlane.join_incident (p 1) (p 3) (Function.Injective.ne pinj (by decide))).right
      (instPlane.join_incident (p 2) (p 3) (Function.Injective.ne pinj (by decide))).right
    have : p 1 = p 3 := by
      rw [hp₁, hp₃, ←hq', ←hq'']
    apply pinj at this
    simp at this
  · intro ⟨hq₃, hq₀, hq₁⟩
    --show q = p 0 = p 2
    have hq' := instPlane.unique_meet (l 0) (l 1) q (Function.Injective.ne linj (by decide)) hq₀ hq₁
    have hq'' := instPlane.unique_meet (l 1) (l 3) q (Function.Injective.ne linj (by decide)) hq₁ hq₃
    have hp₀ := instPlane.unique_meet (l 0) (l 1) (p 0) (Function.Injective.ne linj (by decide))
      (instPlane.join_incident (p 0) (p 1) (Function.Injective.ne pinj (by decide))).left
      (instPlane.join_incident (p 0) (p 2) (Function.Injective.ne pinj (by decide))).left
    have hp₂ := instPlane.unique_meet (l 1) (l 3) (p 2) (Function.Injective.ne linj (by decide))
      (instPlane.join_incident (p 0) (p 2) (Function.Injective.ne pinj (by decide))).right
      (instPlane.join_incident (p 2) (p 3) (Function.Injective.ne pinj (by decide))).left
    have : p 0 = p 2 := by
      rw [hp₀, hp₂, ←hq', ←hq'']
    apply pinj at this
    simp at this

theorem dual_nondeg' : ∃ l : Fin 4 → L, Function.Injective l ∧
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

--is this formulation correct? where do we have to assume inequality?
def IsDesarguesian : Prop :=
  ∀ (p p' : Fin 3 → P) (ne : (i : Fin 3) →  p i ≠ p' i)
    (ne' : (i : Fin 3) → (join (p i) (p (i + 1)) : L) ≠ (join (p' i) (p' (i + 1)) : L))
    (o : P) (central : (i : Fin 3) → o 𝐈 (join (p i) (p' i) : L)),
  ∃ l : L, ∀ i : Fin 3, (meet (join (p i) (p (i + 1)) : L) (join (p' i) (p' (i + 1)) : L) : P) 𝐈 l

theorem dual_desarguesian (h : IsDesarguesian P L) : IsDesarguesian L P := by
  unfold IsDesarguesian at *
  intro l l' ne ne' m central
  let p : Fin 3 → P := fun i ↦ meet (l i) (l (i + 1))
  let p' : Fin 3 → P := fun i ↦ meet (l' i) (l' (i + 1))
  have ne'' : ∀ i : Fin 3, join (p i) (p (i + 1)) ≠ (join (p' i) (p' (i + 1)) : L) := by
    sorry
  specialize h p p' ne' ne''
  sorry

theorem desarguesian_iff_dual : IsDesarguesian P L ↔ IsDesarguesian L P :=
  ⟨dual_desarguesian P L, dual_desarguesian L P⟩

end ProjectivePlane
