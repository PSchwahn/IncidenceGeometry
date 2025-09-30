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
  join_incident := sorry
  unique_join := sorry
  meet := sorry
  meet_incident := sorry
  unique_meet := sorry
  nondeg' := sorry
