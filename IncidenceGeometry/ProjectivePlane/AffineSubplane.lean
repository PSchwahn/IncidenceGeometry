import IncidenceGeometry.Defs
import IncidenceGeometry.ProjectivePlane.Basic
import IncidenceGeometry.ProjectivePlane.Counting
import IncidenceGeometry.AffinePlane.ProjectiveClosure
import IncidenceGeometry.AffinePlane.Counting

open IncidenceGeometry
namespace ProjectivePlane

--set_option trace.Meta.synthInstance true

abbrev WithLineRemoved.Point (P L : Type*) [ProjectivePlane P L] (l₀ : L) :=
  { p : P // ¬ p 𝐈 l₀ }

abbrev WithLineRemoved.Line (P L : Type*) [ProjectivePlane P L] (l₀ : L) :=
  { l : L // l ≠ l₀ }

namespace WithLineRemoved

variable (P L : Type*) [ProjectivePlane P L] (l₀ : L)

/- instance does not provide concrete values for (semi-)out-params
   AffinePlane (WithLineRemoved.Point P L ?l₀) (WithLineRemoved.Line P L ?l₀) -/
def instPlane : AffinePlane (WithLineRemoved.Point P L l₀) (WithLineRemoved.Line P L l₀) where
  Incident := fun ⟨p, _⟩ ⟨l, _⟩ ↦ p 𝐈 l
  join := sorry
  join_incident := sorry
  unique_join := sorry
  par := sorry
  par_incident := sorry
  par_not_intersect := sorry
  par_unique := sorry
  nondeg' := sorry
  par_id := sorry

theorem order_eq :
    @AffinePlane.order (WithLineRemoved.Point P L l₀) (WithLineRemoved.Line P L l₀) (instPlane _ _ _) =
    ProjectivePlane.order P L := by
  obtain ⟨l, hl⟩ := @AffinePlane.exists_line (WithLineRemoved.Point P L l₀) (WithLineRemoved.Line P L l₀) (instPlane _ _ _)
  rw [← @AffinePlane.card_points_on_a_line' _ _ (instPlane _ _ _) ⟨l, hl⟩]
  rw [← card_points_on_a_line_except_one' (meet l l₀) l (meet_incident _ _ hl).left]
  apply Cardinal.mk_congr
  apply Equiv.ofBijective ?f ?bij
  · intro ⟨⟨p, hp₁⟩, hp₂⟩
    use p, hp₂
    intro h
    apply hp₁
    rw [h]
    exact (meet_incident  _ _ hl).right
  · rw [Function.bijective_iff_existsUnique]
    intro ⟨p, hp₁, hp₂⟩
    have hp₃ : ¬ p 𝐈 l₀ := by
      intro h
      apply hp₂
      apply unique_meet _ _ _ hl hp₁ h
    use ⟨⟨p, hp₃⟩, hp₁⟩
    constructor <;> dsimp
    intro ⟨⟨q, hq₁⟩, hq₂⟩ hpq
    simp only [Subtype.mk.injEq]
    simp only [Subtype.mk.injEq] at hpq
    assumption

/-- For any projective plane `P`, the projective closure of (`P` minus a line) is isomorphic to `P`. -/
def closure_equiv_self : IncidenceEquiv
    (@AffinePlane.ProjectiveClosure.Point (WithLineRemoved.Point P L l₀) (WithLineRemoved.Line P L l₀) (instPlane _ _ _))
    (@AffinePlane.ProjectiveClosure.Line (WithLineRemoved.Point P L l₀) (WithLineRemoved.Line P L l₀) (instPlane _ _ _))
    P L where
  onPoints := sorry
  onLines := sorry
  preserves_incidence := sorry

/-
TODO: for linear spaces/unique join geometries where every line has at least two points,
an ext theorem for lines: (∀ p, p 𝐈 l ↔ p 𝐈 l') → l = l'
Then we can define incidence morphisms/equivs simply by their action on points.
-/
