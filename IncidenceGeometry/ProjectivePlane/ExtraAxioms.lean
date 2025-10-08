import IncidenceGeometry.Defs
import IncidenceGeometry.ProjectivePlane.Basic

open IncidenceGeometry
namespace ProjectivePlane

variable (P L : Type*) [instPlane : ProjectivePlane P L]

variable {P} in
/-- Two triangles are axially perspective if the joins of their corresponding vertices
    are collinear. -/
def CentrallyPerspective (p q : Fin 3 → P) : Prop :=
  ∀ i, p i ≠ q i ∧ Concurrent P fun i ↦ (join (p i) (q i) : L)

variable {P} in
/-- Two triangles are axially perspective if the meets of their corresponding sides
    are collinear. -/
def AxiallyPerspective (p q : Fin 3 → P) : Prop :=
  Collinear L fun i ↦ meet (P := P)
    (join (p i) (p (i + 1)) : L)
    (join (q i) (q (i + 1)) : L)

variable {P} in
def CentrallyPerspectiveFrom (p q : Fin 3 → P) (c : P) : Prop :=
  ∀ i, p i ≠ q i ∧ c 𝐈 (join (p i) (q i) : L)

variable {P L} in
def AxiallyPerspectiveFrom (p q : Fin 3 → P) (a : L) : Prop :=
  ∀ i, meet (P := P) (join (p i) (p (i + 1)) : L) (join (q i) (q (i + 1)) : L) 𝐈 a

--is this formulation the right one? or do we want iff for self-duality?
def IsDesarguesian : Prop :=
  ∀ p q : Fin 3 → P, Function.Injective p → Function.Injective q →
    CentrallyPerspective L p q → AxiallyPerspective L p q

def IsPappian : Prop :=
  ∀ p q : Fin 3 → P, Function.Injective p → Function.Injective q →
    Collinear L p → Collinear L q → Collinear L fun (i : Fin 3) ↦ meet (P := P)
    (join (p i) (q (i + 1)) : L)
    (join (q i) (p (i + 1)) : L)

--taken from Wikipedia. Is this the right formulation?
def IsLittleDesargian : Prop :=
  ∀ p q : Fin 3 → P, ∀ c : P, ∀ a : L, Function.Injective p → Function.Injective q →
  c 𝐈 a → CentrallyPerspectiveFrom L p q c →
  meet (P := P) ((join (p 0) (p 1)) : L) ((join (q 0) (q 1)) : L) 𝐈 a →
  meet (P := P) ((join (p 1) (p 2)) : L) ((join (q 1) (q 2)) : L) 𝐈 a →
  meet (P := P) ((join (p 2) (p 0)) : L) ((join (q 2) (q 0)) : L) 𝐈 a

--TODO: test whether the point ≠ point assumptions make sense where they are.
