import IncidenceGeometry.AffinePlane.Basic

open IncidenceGeometry

namespace AffinePlane

inductive ProjectiveClosure.Point (P L : Type*) [AffinePlane P L] where
  | point_of_affine : P → Point P L
  | point_at_infty : (π : Set L) → π ∈ Direction P L → Point P L

inductive ProjectiveClosure.Line (P L : Type*) [AffinePlane P L] where
  | line_of_affine : L → Line P L
  | line_at_infty : Line P L

open ProjectiveClosure.Point
open ProjectiveClosure.Line

instance (P L : Type*) [AffinePlane P L] :
    IncidenceGeometry (ProjectiveClosure.Point P L) (ProjectiveClosure.Line P L) where
  Incident := fun p l => match p, l with
    | point_of_affine p', line_of_affine l' => p' 𝐈 l'
    | point_of_affine _, line_at_infty => False
    | point_at_infty π _, line_of_affine l' => l' ∈ π
    | point_at_infty _ _, line_at_infty => True

noncomputable instance (P L : Type*) [AffinePlane P L] :
    ProjectivePlane (ProjectiveClosure.Point P L) (ProjectiveClosure.Line P L) where
  join := fun p q ↦ match p, q with
    | point_of_affine p', point_of_affine q' => line_of_affine (join p' q')
    | point_of_affine p', point_at_infty π hπ => line_of_affine (directions_equiv_lines_through_a_point p' ⟨π, hπ⟩)
    | point_at_infty π hπ, point_of_affine q' => line_of_affine (directions_equiv_lines_through_a_point q' ⟨π, hπ⟩)
    | point_at_infty π₁ hπ₁, point_at_infty π₂ hπ₂ => line_at_infty
  join_incident := by
    intro p q hne
    match p, q with
    | point_of_affine p', point_of_affine q' =>
      apply join_incident p' q' (fun h ↦ hne (by rw [h]))
    | point_of_affine p', point_at_infty π hπ =>
      constructor
      · exact (directions_equiv_lines_through_a_point p' ⟨π, hπ⟩).prop
      · exact line_of_point_of_direction_mem_direction p' hπ
    | point_at_infty π hπ, point_of_affine q' =>
      constructor
      · exact line_of_point_of_direction_mem_direction q' hπ
      · exact (directions_equiv_lines_through_a_point q' ⟨π, hπ⟩).prop
    | point_at_infty π₁ hπ₁, point_at_infty π₂ hπ₂ => trivial
  unique_join := by
    intro p₁ p₂ l hne hp₁l hp₂l
    match p₁, p₂, l with
    | point_of_affine p₁', point_of_affine p₂', line_of_affine l' =>
      rw [unique_join p₁' p₂' l' (fun h ↦ hne (by rw [h])) hp₁l hp₂l]
    | point_of_affine p₁', point_of_affine p₂', line_at_infty => exact False.elim hp₁l
    | point_of_affine p₁', point_at_infty π hπ, line_of_affine l' =>
      simp only [unique_line_of_point_of_direction p₁' hπ l' hp₁l hp₂l]
    | point_of_affine p₁', point_at_infty π hπ, line_at_infty => exact False.elim hp₁l
    | point_at_infty π hπ, point_of_affine p₂', line_of_affine l' =>
      simp only [unique_line_of_point_of_direction p₂' hπ l' hp₂l hp₁l]
    | point_at_infty π hπ, point_of_affine p₂', line_at_infty => exact False.elim hp₂l
    | point_at_infty π₁ hπ₁, point_at_infty π₂ hπ₂, line_of_affine l' =>
      absurd hne
      congr
      rw [← isparallel_iff_eq_directions (P := P) l' l' hπ₁ hπ₂ hp₁l hp₂l]
      exact Setoid.refl l'
    | point_at_infty π₁ hπ₁, point_at_infty π₂ hπ₂, line_at_infty => rfl
  meet := fun l₁ l₂ ↦ match l₁, l₂ with
    | line_of_affine l₁', line_of_affine l₂' => by
      by_cases h : (IsParallel P l₁' l₂')
      · let ⟨π, hπ⟩ := direction_of_line P l₁'
        exact point_at_infty π hπ
      · exact point_of_affine (meet l₁' l₂' h)
    | line_of_affine l', line_at_infty => let ⟨π, hπ⟩ := direction_of_line P l'; point_at_infty π hπ
    | line_at_infty, line_of_affine l' => let ⟨π, hπ⟩ := direction_of_line P l'; point_at_infty π hπ
    | line_at_infty, line_at_infty => point_of_affine (Nonempty.some (exists_point P L))
  meet_incident := by
    intro l₁ l₂ hne
    match l₁, l₂ with
    | line_of_affine l₁', line_of_affine l₂' =>
      by_cases h : (IsParallel P l₁' l₂') <;> simp only [h, reduceDIte]
      · constructor
        · exact mem_direction_of_self P l₁'
        · have := (isparallel_iff_eq_directions l₁' l₂' (direction_of_line P l₁').prop (direction_of_line P l₂').prop
            (mem_direction_of_self P l₁') (mem_direction_of_self P l₂')).mp h
          conv =>
            lhs
            congr
            rw [this]
          exact mem_direction_of_self P l₂'
      · exact meet_incident l₁' l₂' h
    | line_of_affine l', line_at_infty =>
      constructor
      · exact mem_direction_of_self P l'
      · trivial
    | line_at_infty, line_of_affine l' =>
      constructor
      · trivial
      · exact mem_direction_of_self P l'
    | line_at_infty, line_at_infty => exact False.elim (hne rfl)
  unique_meet := by
    intro l₁ l₂ p hne hpl₁ hpl₂
    match l₁, l₂, p with
    | line_of_affine l₁', line_of_affine l₂', point_of_affine p' =>
      by_cases h : IsParallel P l₁' l₂'
      · absurd hne
        congr
        apply h
        use p'
        exact ⟨hpl₁, hpl₂⟩
      · simp only [h, reduceDIte]
        congr
        apply unique_meet l₁' l₂'
        exact ⟨hpl₁, hpl₂⟩
    | line_of_affine l₁', line_of_affine l₂', point_at_infty π hπ =>
      by_cases h : IsParallel P l₁' l₂'
      · simp only [h, reduceDIte]
        congr
        exact unique_direction_of_line l₁' hπ hpl₁
      · rw [isparallel_iff_eq_directions l₁' l₂' hπ hπ hpl₁ hpl₂] at h
        exact False.elim (h rfl)
    | line_of_affine l', line_at_infty, point_of_affine p' => exact False.elim hpl₂
    | line_of_affine l', line_at_infty, point_at_infty π hπ =>
      congr
      exact unique_direction_of_line l' hπ hpl₁
    | line_at_infty, line_of_affine l', point_of_affine p' => exact False.elim hpl₁
    | line_at_infty, line_of_affine l', point_at_infty π hπ =>
      congr
      exact unique_direction_of_line l' hπ hpl₂
    | line_at_infty, line_at_infty, point_of_affine p' => exact False.elim hpl₁
    | line_at_infty, line_at_infty, point_at_infty π hπ => exact False.elim (hne rfl)
  nondeg' := by
    obtain ⟨d, dinj⟩ := ge_3_directions P L
    obtain ⟨l₀, hl₀⟩ := line_of_direction (d 0).prop
    obtain ⟨p', p'inj⟩ := two_points_of_line P l₀
    have l₀join : l₀ = join (p' 0).val (p' 1).val := by
      apply unique_join
      · intro h
        apply Subtype.val_injective at h
        apply p'inj at h
        exact zero_ne_one h
      · exact (p' 0).prop
      · exact (p' 1).prop
    let p : Fin 4 → ProjectiveClosure.Point P L := fun i ↦ match i with
      | 0 => point_of_affine (p' 0)
      | 1 => point_of_affine (p' 1)
      | 2 => point_at_infty (d 1).val (d 1).prop
      | 3 => point_at_infty (d 2).val (d 2).prop
    use p
    constructor
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp only [reduceCtorEq, p, point_of_affine.injEq, point_at_infty.injEq, Subtype.val_inj] at *
      · apply p'inj at hij
        simp at hij
      · apply p'inj at hij
        simp at hij
      · apply dinj at hij
        simp at hij
      · apply dinj at hij
        simp at hij
    · intro l i
      match l with
      | line_of_affine l' =>
        fin_cases i <;> unfold p <;> dsimp <;> simp only [not_and]
        · intro h₀ h₁
          have l'join : l' = join (p' 0).val (p' 1).val := by
            apply unique_join
            · intro h
              apply Subtype.val_injective at h
              apply p'inj at h
              exact zero_ne_one h
            · exact h₀
            · exact h₁
          rw [l'join, ←l₀join]
          intro h₀₁
          have := (isparallel_iff_eq_directions l₀ l₀ (d 0).prop (d 1).prop hl₀ h₀₁).mp (Setoid.refl l₀)
          apply Subtype.val_injective at this
          apply dinj at this
          simp at this
        · intro _ h₁ h₂
          have := (isparallel_iff_eq_directions l' l' (d 1).prop (d 2).prop h₁ h₂).mp (Setoid.refl l')
          apply Subtype.val_injective at this
          apply dinj at this
          simp at this
        · intro h₁ h₂ _
          have := (isparallel_iff_eq_directions l' l' (d 1).prop (d 2).prop h₁ h₂).mp (Setoid.refl l')
          apply Subtype.val_injective at this
          apply dinj at this
          simp at this
        · intro h₂ h₀ h₁
          have l'join : l' = join (p' 0).val (p' 1).val := by
            apply unique_join
            · intro h
              apply Subtype.val_injective at h
              apply p'inj at h
              exact zero_ne_one h
            · exact h₀
            · exact h₁
          revert h₂
          rw [l'join, ←l₀join]
          intro h₀₂
          have := (isparallel_iff_eq_directions l₀ l₀ (d 0).prop (d 2).prop hl₀ h₀₂).mp (Setoid.refl l₀)
          apply Subtype.val_injective at this
          apply dinj at this
          simp at this
      | line_at_infty =>
        fin_cases i <;> unfold p <;> dsimp <;> simp only [not_and]
        · intro h _ _
          exact h
        · intro h _ _
          exact h
        · intro _ _ h
          exact h
        · intro _ h _
          exact h
