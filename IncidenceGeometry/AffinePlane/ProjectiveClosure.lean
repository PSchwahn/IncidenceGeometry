import IncidenceGeometry.AffinePlane.Basic

open IncidenceGeometry

namespace AffinePlane

inductive ProjectiveClosure.Point (P L : Type*) [AffinePlane P L] where
  | ofAffine : P → Point P L
  | point_at_infty : (π : Set L) → π ∈ Direction P L → Point P L

inductive ProjectiveClosure.Line (P L : Type*) [AffinePlane P L] where
  | ofAffine : L → Line P L
  | line_at_infty : Line P L

instance (P L : Type*) [AffinePlane P L] :
    IncidenceGeometry (ProjectiveClosure.Point P L) (ProjectiveClosure.Line P L) where
  Incident := fun p l => by
    cases p with
    | ofAffine p =>
      cases l with
      | ofAffine l => exact p 𝐈 l
      | line_at_infty => exact False
    | point_at_infty π hπ =>
      cases l with
      | ofAffine l => exact l ∈ π
      | line_at_infty => exact True

instance (P L : Type*) [AffinePlane P L] :
    ProjectivePlane (ProjectiveClosure.Point P L) (ProjectiveClosure.Line P L) where
  join := sorry
  join_incident := sorry
  unique_join := sorry
  meet := sorry
  meet_incident := sorry
  unique_meet := sorry
  nondeg' := sorry
