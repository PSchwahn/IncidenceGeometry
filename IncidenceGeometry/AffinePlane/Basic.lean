import IncidenceGeometry.Defs

open IncidenceGeometry

namespace AffinePlane

variable (P L : Type*) [AffinePlane P L]

theorem nondeg : ∃ p : Fin 3 → P, Function.Injective p ∧ ¬ Collinear L p :=
  AffinePlane.nondeg'

instance exists_point : Nonempty P := by
  obtain ⟨p, _⟩ := nondeg P L
  use p 0

instance exists_line : Nonempty L := by
  obtain ⟨p⟩ := exists_point P L
  use join p p

variable (P : Type*) {L : Type*} [instPlane : AffinePlane P L]

/-- Every line has a point. -/
theorem exists_point_on_line (l : L) : ∃ p : P, p 𝐈 l := by
  obtain ⟨p, pinj, hp⟩ := nondeg P L
  by_cases h₀ : p 0 𝐈 l
  · use p 0
  let l₀₁ : L := join (p 0) (p 1)
  let l₀₂ : L := join (p 0) (p 2)
  have hp₀₁ : p 0 𝐈 l₀₁ := (join_incident (p 0) (p 1) (Function.Injective.ne pinj (by simp))).1
  have hp₀₂ : p 0 𝐈 l₀₂ := (join_incident (p 0) (p 2) (Function.Injective.ne pinj (by simp))).1
  by_cases h₁ : Intersect P l l₀₁
  · obtain ⟨q, _, _⟩ := h₁
    use q
  by_cases h₂ : Intersect P l l₀₂
  · obtain ⟨q, _, _⟩ := h₂
    use q
  absurd hp
  use l₀₁
  intro i
  fin_cases i
  · exact hp₀₁
  · exact (join_incident (p 0) (p 1) (Function.Injective.ne pinj (by simp))).2
  · rw [par_unique l (p 0) h₀ l₀₁ l₀₂ hp₀₁ hp₀₂ h₁ h₂]
    exact (join_incident (p 0) (p 2) (Function.Injective.ne pinj (by simp))).2

/-- Two lines are parallel if they are equal or do not intersect. -/
def IsParallel (l₁ l₂ : L) : Prop := Intersect P l₁ l₂ → l₁ = l₂

--infix:50 " ∥ " => IsParallel
--can we fix this (using outParam) such that P does not need to be given explicitly?

variable {P L : Type*} [instPlane : AffinePlane P L]

theorem parallel_prop (p : P) (l : L) : IsParallel P (par l p) l := by
  intro h
  by_cases hp : p 𝐈 l
  · apply par_id
    assumption
  · exfalso
    apply par_not_intersect l p hp h

/-- There exists exactly one line through `p` parallel to `l`. -/
theorem parallel_unique {p : P} {l l' : L} (hI : p 𝐈 l') (hpar : IsParallel P l l') : par l p = l' := by
  by_cases hp : p 𝐈 l
  · rw [par_id l p hp]
    apply hpar
    use p
  · apply par_unique l p hp (par l p) l' (par_incident l p) hI
    · rw [intersect_symm_iff]
      apply par_not_intersect
      exact hp
    · intro h
      rw [hpar h] at hp
      exact hp hI

theorem isparallel_symm {l₁ l₂ : L} : IsParallel P l₁ l₂ → IsParallel P l₂ l₁ := by
    intro h ⟨p, h'⟩
    symm
    apply h
    use p, h'.2, h'.1

theorem isparallel_equivalence : Equivalence (@IsParallel P L _) where
  refl := fun _ _ ↦ rfl
  symm := isparallel_symm
  trans := by
    intro l₁ l₂ l₃ h₁₂ h₂₃ ⟨p, h'⟩
    rw [← parallel_unique h'.1 (isparallel_symm h₁₂), parallel_unique h'.2 h₂₃]

variable (P L) in
/-- Two lines are parallel if they are equal or do not intersect. -/
instance parallelSetoid : Setoid L where
  r := IsParallel P
  iseqv := isparallel_equivalence

/-- If two lines are not parallel, they intersect in a unique point. -/
theorem unique_meet_of_not_parallel {l₁ l₂ : L} (h : ¬ IsParallel P l₁ l₂) : ∃! p : P, p 𝐈 l₁ ∧ p 𝐈 l₂ := by
  unfold IsParallel at h
  push_neg at h
  obtain ⟨⟨p, h₁, h₂⟩, hne⟩ := h
  use p, ⟨h₁, h₂⟩
  intro p' ⟨h₁', h₂'⟩
  symm
  by_contra hpne
  rw [unique_join p p' l₁ hpne h₁ h₁', unique_join p p' l₂ hpne h₂ h₂'] at hne
  apply hne
  rfl

/-- The (unique) meet of two non-parallel lines. -/
noncomputable def meet (l₁ l₂ : L) (h : ¬ IsParallel P l₁ l₂) : P :=
  Classical.choose (unique_meet_of_not_parallel h)

theorem meet_incident (l₁ l₂ : L) (h : ¬ IsParallel P l₁ l₂) : meet l₁ l₂ h 𝐈 l₁ ∧ meet l₁ l₂ h 𝐈 l₂ :=
  (Classical.choose_spec (unique_meet_of_not_parallel h)).left

theorem unique_meet (l₁ l₂ : L) (h : ¬ IsParallel P l₁ l₂) (p : P) (hp : p 𝐈 l₁ ∧ p 𝐈 l₂) :
    p = meet l₁ l₂ h :=
  (Classical.choose_spec (unique_meet_of_not_parallel h)).right p hp

variable (P L) in
/-- The set of directions, i.e. equivalence classes of the parallel lines. -/
def Direction := Setoid.classes (parallelSetoid P L : Setoid L)

--rather use quotient type?

--todo: use this API more widely in proofs, instead of the implementation of Direction?
variable (P) in
/-- The direction in which the line `l` lies. -/
def direction_of_line (l : L) : Direction P L := ⟨{l' | IsParallel P l' l}, Setoid.mem_classes _ _⟩

variable (P) in
theorem mem_direction_of_self (l : L) : l ∈ (direction_of_line P l).val := Setoid.refl l

theorem direction_eq_class (l : L) {π : Set L} (hπ : π ∈ Direction P L) (h : l ∈ π) : π = {l' | IsParallel P l' l} := by
  obtain ⟨l'', rfl⟩ := hπ
  ext l
  constructor
  · intro hl
    exact isparallel_equivalence.trans hl (isparallel_equivalence.symm h)
  · intro hl
    exact isparallel_equivalence.trans hl h

/-- Two lines are parallel if and only if the directions they belong to are equal. -/
theorem isparallel_iff_eq_directions (l₁ l₂ : L) {π₁ π₂ : Set L} (hπ₁ : π₁ ∈ Direction P L) (hπ₂ : π₂ ∈ Direction P L)
      (h₁ : l₁ ∈ π₁) (h₂ : l₂ ∈ π₂) :
    IsParallel P l₁ l₂ ↔ π₁ = π₂ := by
  constructor
  · intro h
    rw [direction_eq_class l₁ hπ₁ h₁, direction_eq_class l₂ hπ₂ h₂]
    ext l
    constructor
    · intro hl
      exact isparallel_equivalence.trans hl h
    · intro hl
      exact isparallel_equivalence.trans hl (isparallel_equivalence.symm h)
  · intro h
    change parallelSetoid P L l₁ l₂
    rw [Setoid.rel_iff_exists_classes]
    use π₁, hπ₁, h₁
    rw [h]
    exact h₂

--use the two theorems above to golf a few of the proofs below?

/-- Every direction contains a line. -/
theorem line_of_direction {π : Set L} (hπ : π ∈ Direction P L) : ∃ l : L, l ∈ π := by
  have hpart : Setoid.IsPartition (Direction P L) := by
    apply Setoid.isPartition_classes
  have π_nempty : π ≠ ∅ := by
    intro h
    rw [h] at hπ
    exact hpart.1 hπ
  by_contra!
  apply π_nempty
  rw [← Set.subset_empty_iff]
  intro l hl
  rw [Set.mem_empty_iff_false]
  apply this l hl

/-- If `π` is a direction, then every point lies on exactly one line of `π`.-/
theorem direction_partitions {π : Set L} (hπ : π ∈ Direction P L) (p : P) : ∃! l : L, p 𝐈 l ∧ l ∈ π := by
  obtain ⟨l', hl'⟩ := line_of_direction hπ
  use par l' p
  simp
  constructor
  · use par_incident l' p
    have : parallelSetoid P L (par l' p) l' := parallel_prop p l'
    rw [Setoid.rel_iff_exists_classes] at this
    obtain ⟨π', hπ'⟩ := this
    obtain ⟨π'', hπ''⟩ := (Setoid.isPartition_classes _).2 l'
    simp at hπ''
    have hππ'' : π = π'' := hπ''.2 π hπ hl'
    have hπ'π'' : π' = π'' := hπ''.2 π' hπ'.1 hπ'.2.2
    rw [hππ'', ←hπ'π'']
    exact hπ'.2.1
  · intro l hpl hl
    symm
    apply parallel_unique hpl
    change parallelSetoid P L l' l
    rw [Setoid.rel_iff_exists_classes]
    use π, hπ

/-- If `π` is a direction, then the lines of `π` partition the points. -/
theorem direction_partitions' {π : Set L} (hπ : π ∈ Direction P L) : Setoid.IsPartition {{p : P | p 𝐈 l} | l ∈ π} := by
  constructor
  · intro ⟨l, hl₁, hl₂⟩
    rw [←Set.subset_empty_iff] at hl₂
    obtain ⟨p, hp⟩ := exists_point_on_line P l
    apply hl₂ at hp
    rw [Set.mem_empty_iff_false] at hp
    assumption
  · intro p
    obtain ⟨l, ⟨hpl, hl⟩, hlu⟩ := direction_partitions hπ p
    use {p | p 𝐈 l}
    simp at *
    constructor
    · exact ⟨⟨l, hl, rfl⟩, hpl⟩
    · intro l' hl' hpl'
      rw [hlu l' hpl' hl']

variable (P L) in
theorem ge_3_directions : ∃ π : Fin 3 → Direction P L, Function.Injective π := by
  obtain ⟨p, hinj, hp⟩ := nondeg P L
  let l : Fin 3 → L := fun i ↦ join (p i) (p (i + 1))
  have diff : ∀ (i j : Fin 3), j = i ∨ j = i + 1 ∨ j = i + 2 := by decide
  let π : Fin 3 → Direction P L := fun i ↦ ⟨{ l' | IsParallel P l' (l i) }, ⟨l i, rfl⟩⟩
  use π
  intro i j hij
  unfold π at hij
  rw [Subtype.mk.injEq] at hij
  have hij : IsParallel P (l i) (l j) := by
    change parallelSetoid P L _ _
    rw [Setoid.rel_iff_exists_classes]
    use {l' | IsParallel P l' (l i)}
    constructor
    · apply Setoid.mem_classes
    · constructor
      · apply isparallel_equivalence.refl
      · rw [hij]
        apply isparallel_equivalence.refl
  rcases diff i j with rfl | rfl | rfl
  · rfl
  · absurd hp
    use l i
    intro j
    rcases diff i j with rfl | rfl | rfl
    · exact (join_incident (p j) (p (j + 1)) (Function.Injective.ne hinj (by simp))).1
    · exact (join_incident (p i) (p (i + 1)) (Function.Injective.ne hinj (by simp))).2
    · have : l i = l (i + 1) := by
        apply hij
        use p (i + 1)
        use (join_incident (p i) (p (i + 1)) (Function.Injective.ne hinj (by simp))).2
        use (join_incident (p (i + 1)) (p (i + 1 + 1)) (Function.Injective.ne hinj (by simp))).1
      rw [this]
      have : l (i + 1) = join (p (i + 1)) (p (i + 2)) := by
          unfold l
          simp [add_assoc]
      rw [this]
      exact (join_incident (p (i + 1)) (p (i + 2)) (Function.Injective.ne hinj (by simp))).2
  · absurd hp
    use l i
    intro j
    rcases diff i j with rfl | rfl | rfl
    · exact (join_incident (p j) (p (j + 1)) (Function.Injective.ne hinj (by simp))).1
    · exact (join_incident (p i) (p (i + 1)) (Function.Injective.ne hinj (by simp))).2
    · have : l (i + 2) = join (p (i + 2)) (p i) := by
          unfold l
          simp [add_assoc]
      have : l i = l (i + 2) := by
        apply hij
        use p i
        use (join_incident (p i) (p (i + 1)) (Function.Injective.ne hinj (by simp))).1
        rw [this]
        use (join_incident (p (i + 2)) (p i) (Function.Injective.ne hinj (by simp))).2
      rw [this]
      exact (join_incident (p (i + 2)) (p (i + 2 + 1)) (Function.Injective.ne hinj (by simp))).1

variable (P) in
/-- For any two lines, there exists a third line not parallel to either of them. -/
theorem exists_line_not_parallel_to_two_lines (l₁ l₂ : L) : ∃ l : L, ¬ IsParallel P l₁ l ∧ ¬ IsParallel P l₂ l := by
  obtain ⟨f, finj⟩ := ge_3_directions P L
  let π₁ : Direction P L := ⟨{ l' | IsParallel P l' l₁ }, Setoid.mem_classes _ _⟩
  let π₂ : Direction P L := ⟨{ l' | IsParallel P l' l₂ }, Setoid.mem_classes _ _⟩
  have : ∃ π : Direction P L, π ≠ π₁ ∧ π ≠ π₂ := by
    by_cases h : π₁ = f 0
    · rw [h]
      by_cases h' : π₂ = f 1
      · use f 2
        rw [h']
        exact ⟨Function.Injective.ne finj (by decide), Function.Injective.ne finj (by decide)⟩
      · use f 1, Function.Injective.ne finj (by decide), Ne.symm h'
    · by_cases h' : π₂ = f 1
      · use f 0
        rw [h']
        exact ⟨Ne.symm h, Function.Injective.ne finj (by decide)⟩
      · by_cases h'' : π₁ = f 2
        · use f 1
          rw [h'']
          exact ⟨Function.Injective.ne finj (by decide), Ne.symm h'⟩
        · by_cases h''' : π₂ = f 0
          · use f 2
            rw [h''']
            exact ⟨Ne.symm h'', Function.Injective.ne finj (by decide)⟩
          · use f 0
            exact ⟨Ne.symm h, Ne.symm h'''⟩
  obtain ⟨⟨π, hπ⟩, h₁, h₂⟩ := this
  obtain ⟨l, hlπ⟩ := line_of_direction hπ
  use l
  constructor
  · intro h
    apply h₁
    unfold π₁
    simp only [Subtype.mk.injEq]
    rw [←isparallel_iff_eq_directions l l₁ hπ π₁.prop hlπ (isparallel_equivalence.refl _)]
    exact isparallel_equivalence.symm h
  · intro h
    apply h₂
    unfold π₂
    simp only [Subtype.mk.injEq]
    rw [←isparallel_iff_eq_directions l l₂ hπ π₂.prop hlπ (isparallel_equivalence.refl _)]
    exact isparallel_equivalence.symm h

noncomputable def lines_through_a_point_equiv_directions (p : P) : {l : L | p 𝐈 l} ≃ Direction P L :=
  Equiv.ofBijective (fun ⟨l, _ ⟩ ↦ direction_of_line P l) <| by
  constructor
  · intro ⟨l₁, hl₁⟩ ⟨l₂, hl₂⟩ hl₁₂
    simp only [Subtype.mk.injEq] at *
    simp only [Set.mem_setOf_eq] at *
    have hπ : { l' | IsParallel P l' l₁ } ∈ Direction P L := Setoid.mem_classes _ _
    obtain ⟨l₃, ⟨hl₃, hl₃π⟩, l₃unique⟩ := direction_partitions (direction_of_line P l₁).prop p
    rw [l₃unique l₁ ⟨hl₁, isparallel_equivalence.refl _⟩]
    rw [l₃unique l₂ ⟨hl₂, by rw [hl₁₂]; exact isparallel_equivalence.refl _⟩]
  · intro ⟨π, hπ⟩
    simp only [Set.coe_setOf, Subtype.exists, exists_prop]
    obtain ⟨l, ⟨hl, hlπ⟩, l₃unique⟩ := direction_partitions hπ p
    use l, hl
    obtain ⟨l₁, rfl⟩ := hπ
    ext l₂
    constructor <;> simp at *
    · intro hl₂
      exact isparallel_equivalence.trans hl₂ hlπ
    · intro hl₂
      exact isparallel_equivalence.trans hl₂ (isparallel_symm hlπ)

/-- Given a point `p`, the canonical correspondence between directions and lines through `p`. -/
noncomputable def directions_equiv_lines_through_a_point (p : P) : Direction P L ≃ {l : L | p 𝐈 l} :=
  (lines_through_a_point_equiv_directions p).symm

theorem mem_direction_of_self' (p : P) (l : L) (hl : p 𝐈 l) : l ∈ (lines_through_a_point_equiv_directions p ⟨l, hl⟩).val := mem_direction_of_self P l

theorem line_of_point_of_direction_mem_direction (p : P) {π : Set L} (hπ : π ∈ Direction P L) :
    (directions_equiv_lines_through_a_point p ⟨π, hπ⟩).val ∈ π := by
  have h₁ : lines_through_a_point_equiv_directions p (directions_equiv_lines_through_a_point p ⟨π, hπ⟩) = ⟨π, hπ⟩ := Equiv.apply_symm_apply _ _
  have h₂ : (⟨π, hπ⟩ : Direction P L).val = π := rfl
  conv =>
    lhs
    rw [← h₂, ←h₁]
  apply mem_direction_of_self'

theorem unique_line_of_point_of_direction (p : P) {π : Set L} (hπ : π ∈ Direction P L) (l : L) (h₁ : p 𝐈 l) (h₂ : l ∈ π) :
    l = (directions_equiv_lines_through_a_point p ⟨π, hπ⟩).val := by
  have : l = (directions_equiv_lines_through_a_point p (lines_through_a_point_equiv_directions p ⟨l, h₁⟩)).val := by
    unfold directions_equiv_lines_through_a_point
    simp only [Equiv.symm_apply_apply]
  rw [this]
  congr
  unfold lines_through_a_point_equiv_directions
  simp only [Equiv.ofBijective_apply]
  simp only [← (isparallel_iff_eq_directions (P := P) l l (direction_of_line P l).prop hπ (mem_direction_of_self P l) h₂).mp (Setoid.refl l),
    Subtype.coe_eta]

--more API for the above definitions?

variable (L) in
/-- Any two points lie on the same number of lines. -/
noncomputable def equiv_lines_through_a_point (p₁ p₂ : P) : {l : L | p₁ 𝐈 l} ≃ {l : L | p₂ 𝐈 l} :=
  (directions_equiv_lines_through_a_point p₁).symm.trans (directions_equiv_lines_through_a_point p₂)

--auxiliary theorem to define a function π → {p : P | p 𝐈 l}
theorem unique_intersection_of_direction_of_line (l l' : L) {π : Set L} (hπ : π ∈ Direction P L)
      (hl : ¬ l ∈ π) (hl' : l' ∈ π) :
    ∃! p : P, p 𝐈 l ∧ p 𝐈 l' := by
  apply unique_meet_of_not_parallel
  obtain ⟨l'', rfl⟩ := hπ
  simp only [Set.mem_setOf_eq] at *
  intro h
  apply hl
  exact isparallel_equivalence.trans h hl'

noncomputable def direction_equiv_points_on_a_line_aux₁ (l : L) {π : Set L} (hπ : π ∈ Direction P L) (h : ¬ l ∈ π) :
    π → {p : P | p 𝐈 l} := by
  intro ⟨l₁, hl₁⟩
  have := ExistsUnique.exists (unique_intersection_of_direction_of_line l l₁ hπ h hl₁)
  exact ⟨Classical.choose this, (Classical.choose_spec this).1⟩

theorem direction_equiv_points_on_a_line_aux₂ (l l' : L) {π : Set L} (hπ : π ∈ Direction P L) (hl : ¬ l ∈ π) (hl' : l' ∈ π) :
    (direction_equiv_points_on_a_line_aux₁ l hπ hl ⟨l', hl'⟩).val 𝐈 l' := by
  have := ExistsUnique.exists (unique_intersection_of_direction_of_line l l' hπ hl hl')
  exact (Classical.choose_spec this).2

/-- Given a line `l` and a direction `π` not containing `l`, the canonical correspondence between
    lines in `π` and points on `l`. -/
noncomputable def direction_equiv_points_on_a_line (l : L) {π : Set L} (hπ : π ∈ Direction P L) (h : ¬ l ∈ π) :
    π ≃ {p : P | p 𝐈 l} :=
  Equiv.ofBijective (direction_equiv_points_on_a_line_aux₁ l hπ h) <| by
  constructor
  · intro ⟨l₁, h₁⟩ ⟨l₂, h₂⟩ h₁₂
    have : IsParallel P l₁ l₂ := by
      change parallelSetoid P L l₁ l₂
      rw [Setoid.rel_iff_exists_classes]
      use π, hπ
    simp only [Subtype.mk.injEq]
    apply this
    use direction_equiv_points_on_a_line_aux₁ l hπ h ⟨l₁, h₁⟩
    constructor
    · apply direction_equiv_points_on_a_line_aux₂
    · rw [h₁₂]
      apply direction_equiv_points_on_a_line_aux₂
  · intro ⟨p, hp⟩
    obtain ⟨l', ⟨hpl', hl'π⟩, hl'unique⟩ := direction_partitions hπ p
    use ⟨l', hl'π⟩
    obtain ⟨q, ⟨hql, hql'⟩, hqunique⟩ := unique_intersection_of_direction_of_line l l' hπ h hl'π
    have h₁ : (direction_equiv_points_on_a_line_aux₁ l hπ h ⟨l', hl'π⟩).val = q := by
      apply hqunique
      exact ⟨(direction_equiv_points_on_a_line_aux₁ l hπ h ⟨l', hl'π⟩).prop,
        direction_equiv_points_on_a_line_aux₂ l l' hπ h hl'π⟩
    have h₂ : p = q := by
      apply hqunique
      exact ⟨hp, hpl'⟩
    ext
    dsimp
    rw [h₁, h₂]

variable (P) in
/-- Any two lines have the same number of points. -/
theorem equiv_points_on_a_line (l₁ l₂ : L) : Nonempty ({p : P | p 𝐈 l₁} ≃ {p : P | p 𝐈 l₂}) := by
  obtain ⟨l, h₁, h₂⟩ := exists_line_not_parallel_to_two_lines P l₁ l₂
  have hπ : {l' | IsParallel P l' l} ∈ Direction P L := Setoid.mem_classes _ _
  exact ⟨(direction_equiv_points_on_a_line l₁ hπ h₁).symm.trans (direction_equiv_points_on_a_line l₂ hπ h₂)⟩

/-- Any two directions have the same number of lines. -/
theorem equiv_directions {π₁ π₂ : Set L} (hπ₁ : π₁ ∈ Direction P L) (hπ₂ : π₂ ∈ Direction P L) : Nonempty (π₁ ≃ π₂) := by
  obtain ⟨l₁, hl₁⟩ := line_of_direction hπ₁
  obtain ⟨l₂, hl₂⟩ := line_of_direction hπ₂
  obtain ⟨l, h₁, h₂⟩ := exists_line_not_parallel_to_two_lines P l₁ l₂
  have h₁ : ¬ l ∈ π₁ := by
    obtain ⟨l₁', rfl⟩ := hπ₁
    intro h
    exact h₁ (isparallel_equivalence.trans hl₁ (isparallel_equivalence.symm h))
  have h₂ : ¬ l ∈ π₂ := by
    obtain ⟨l₂', rfl⟩ := hπ₂
    simp at *
    intro h
    exact h₂ (isparallel_equivalence.trans hl₂ (isparallel_equivalence.symm h))
  exact ⟨(direction_equiv_points_on_a_line l hπ₁ h₁).trans (direction_equiv_points_on_a_line l hπ₂ h₂).symm⟩

end AffinePlane
