import Mathlib

variable (P L : semiOutParam Type*)

class IncidenceGeometry where
  Incident : P → L → Prop

/-- Notation for incidence relation. -/
infix:50 " 𝐈 " => IncidenceGeometry.Incident

variable [IncidenceGeometry P L]

namespace IncidenceGeometry

variable {L} in
/-- Notation for "two lines meet somewhere". -/
abbrev Intersect (l₁ l₂ : L) : Prop := ∃ q : P, q 𝐈 l₁ ∧ q 𝐈 l₂

theorem intersect_symm (l₁ l₂ : L) : Intersect P l₁ l₂ → Intersect P l₂ l₁ :=
  fun ⟨q, h₁, h₂⟩ ↦ ⟨q, h₂, h₁⟩

theorem intersect_symm_iff (l₁ l₂ : L) : Intersect P l₁ l₂ ↔ Intersect P l₂ l₁ := by
  constructor
  apply intersect_symm
  apply intersect_symm

variable {P} in
abbrev Collinear {ι : Type*} (p : ι → P) : Prop := ∃ l : L, ∀ i : ι, p i 𝐈 l

variable {P} in
abbrev Collinear' (s : Set P) : Prop := ∃ l : L, ∀ p ∈ s, p 𝐈 l

variable {L} in
abbrev Concurrent {ι : Type*} (l : ι → L) : Prop := ∃ p : P, ∀ i : ι, p 𝐈 l i

variable {L} in
abbrev Concurrent' (s : Set L) : Prop := ∃ p : P, ∀ l ∈ s, p 𝐈 l

end IncidenceGeometry

structure IncidenceEquiv (P L P' L' : Type*) [IncidenceGeometry P L] [IncidenceGeometry P' L'] where
  onPoints : P ≃ P'
  onLines : L ≃ L'
  preserves_incidence : ∀ (p : P) (l : L), p 𝐈 l ↔ onPoints p 𝐈 onLines l

--ext theorem?

abbrev Collineation := IncidenceEquiv P L P L

instance : Group (Collineation P L) where
  mul := fun ⟨pe, le, h⟩ ⟨pe', le', h'⟩ ↦ ⟨pe'.trans pe, le'.trans le, by
    intro p l
    trans pe' p 𝐈 le' l
    apply h'
    apply h⟩
  mul_assoc := fun _ _ _ ↦ rfl
  one := ⟨Equiv.refl P, Equiv.refl L, fun _ _ ↦ by simp⟩
  one_mul := fun _ ↦ rfl
  mul_one := fun _ ↦ rfl
  inv := fun ⟨pe, le, h⟩ ↦ ⟨pe.symm, le.symm, by
    intro p l
    rw [h (pe.symm p)]
    simp⟩
  inv_mul_cancel := fun ⟨pe, le, h⟩ ↦ by
    dsimp
    change IncidenceEquiv.mk (pe.trans pe.symm) (le.trans le.symm) _ = _
    simp
    rfl
--EquivLike or something like that?
--API like collineation_apply ...

open IncidenceGeometry

class ProjectivePlane extends IncidenceGeometry P L where
  join : P → P → L
  join_incident : ∀ (p₁ p₂ : P), p₁ ≠ p₂ →
    p₁ 𝐈 (join p₁ p₂) ∧ p₂ 𝐈 (join p₁ p₂)
  unique_join : ∀ (p₁ p₂ : P) (l : L), p₁ ≠ p₂ →
    p₁ 𝐈 l → p₂ 𝐈 l → l = join p₁ p₂
  meet : L → L → P
  meet_incident : ∀ (l₁ l₂ : L), l₁ ≠ l₂ →
    (meet l₁ l₂) 𝐈 l₁ ∧ (meet l₁ l₂) 𝐈 l₂
  unique_meet : ∀ (l₁ l₂ : L) (p : P), l₁ ≠ l₂ →
    p 𝐈 l₁ → p 𝐈 l₂ → p = meet l₁ l₂
  nondeg' : ∃ p : Fin 4 → P, Function.Injective p ∧
    ∀ (l : L) (i : Fin 4), ¬(p i 𝐈 l ∧ p (i + 1) 𝐈 l ∧ p (i + 2) 𝐈 l)

class ProjectiveSpace extends IncidenceGeometry P L where
  join : P → P → L
  join_incident : ∀ (p₁ p₂ : P), p₁ ≠ p₂ →
    p₁ 𝐈 (join p₁ p₂) ∧ p₂ 𝐈 (join p₁ p₂)
  unique_join : ∀ (p₁ p₂ : P) (l : L), p₁ ≠ p₂ →
    p₁ 𝐈 l → p₂ 𝐈 l → l = join p₁ p₂
  veblen' : ∀ (p : Fin 4 → P) (q : P), Function.Injective p →
    (q 𝐈 (join (p 0) (p 1)) ∧ q 𝐈 (join (p 2) (p 3)) → ∃ r : P,
    r 𝐈 (join (p 0) (p 2)) ∧ r 𝐈 (join (p 1) (p 3)))
  nondeg' : ∀ (l : L), ∃ (p : Fin 3 → P),
    Function.Injective p ∧ (p 0) 𝐈 l ∧ (p 1) 𝐈 l ∧ (p 2) 𝐈 l

class AffinePlane extends IncidenceGeometry P L where
  join : P → P → L
  join_incident : ∀ (p₁ p₂ : P), p₁ ≠ p₂ →
    p₁ 𝐈 (join p₁ p₂) ∧ p₂ 𝐈 (join p₁ p₂)
  unique_join : ∀ (p₁ p₂ : P) (l : L), p₁ ≠ p₂ →
    p₁ 𝐈 l → p₂ 𝐈 l → l = join p₁ p₂
  par : L → P → L
  par_incident : ∀ (l : L) (p : P), p 𝐈 (par l p)
  par_not_intersect : ∀ (l : L) (p : P), ¬ p 𝐈 l →
    ¬Intersect P (par l p) l
  par_unique : ∀ (l : L) (p : P), ¬ p 𝐈 l →
    ∀ (l₁ l₂ : L), p 𝐈 l₁ → p 𝐈 l₂ →
    ¬Intersect P l l₁ → ¬Intersect P l l₂ →
    l₁ = l₂
  nondeg' : ∃ p : Fin 3 → P, Function.Injective p ∧ ¬ Collinear L p
  par_id : ∀ (l : L) (p : P), p 𝐈 l → par l p = l
