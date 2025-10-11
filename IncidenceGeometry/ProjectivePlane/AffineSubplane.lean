import IncidenceGeometry.Defs
import IncidenceGeometry.ProjectivePlane.Basic

open IncidenceGeometry
namespace ProjectivePlane

--set_option trace.Meta.synthInstance true

def WithLineRemoved.Point (P L : Type*) [ProjectivePlane P L] (l₀ : L) :=
  { p : P // ¬ p 𝐈 l₀ }

def WithLineRemoved.Line (P L : Type*) [ProjectivePlane P L] (l₀ : L) :=
  { l : L // l ≠ l₀ }

variable (P L : Type*) [ProjectivePlane P L] (l₀ : L)

/- instance does not provide concrete values for (semi-)out-params
   IncidenceGeometry (WithLineRemoved.Point P L ?l₀) (WithLineRemoved.Line P L ?l₀) -/
def WithLineRemoved.instIncidence : IncidenceGeometry (WithLineRemoved.Point P L l₀) (WithLineRemoved.Line P L l₀) where
  Incident := fun ⟨p, _⟩ ⟨l, _⟩ ↦ p 𝐈 l

def WithLineRemoved.instPlane : AffinePlane (WithLineRemoved.Point P L l₀) (WithLineRemoved.Line P L l₀) where
  Incident := sorry
  join := sorry
  join_incident := sorry
  unique_join := sorry
  par := sorry
  par_incident := sorry
  par_not_intersect := sorry
  par_unique := sorry
  nondeg' := sorry
  par_id := sorry
