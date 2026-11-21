import YangMills.Construction.InfiniteLattice.CoveringOfTheTorusLatticeAtOneSpacingProof
import YangMills.Construction.PassageToTheLimit.TransportedLatticeFunctionalsAreBoundedFormsProof
import YangMills.Construction.Towers.IsometriesAreOrthogonalMotionsProof
import YangMills.Construction.Towers.IsometriesOfATowerAreHypercubicMotions
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set Matrix
open InfiniteLattice (AmbientSpace)
open TorusMetric (torusProj)
namespace Tower.HypercubicMotions
open OrthogonalMotions (IsIntegerMatrix)
structure IntegralOrthogonal (R : Matrix (Fin 4) (Fin 4) ℝ) : Prop where
  mem_orthogonal : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ
  isInteger : IsIntegerMatrix R
section Orthogonal
variable {R : Matrix (Fin 4) (Fin 4) ℝ}
theorem transpose_mul_self_of_mem (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : Rᵀ * R = 1 := by apply _root_.YangMills.Construction.ConfigSpace.orth_transpose_mul_self <;> assumption
theorem mul_transpose_self_of_mem (hR : R ∈ Matrix.orthogonalGroup (Fin 4) ℝ) : R * Rᵀ = 1 := by apply _root_.YangMills.Construction.Tower.OrthogonalMotions.orth_mul_transpose_self <;> assumption
theorem IntegralOrthogonal.transpose (hR : IntegralOrthogonal R) : IntegralOrthogonal Rᵀ where
  mem_orthogonal := by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
    exact transpose_mul_self_of_mem hR.mem_orthogonal
  isInteger := fun μ ν => hR.isInteger ν μ
theorem IntegralOrthogonal.apply_symm (hR : IntegralOrthogonal R) (x : AmbientSpace) :
    R *ᵥ (Rᵀ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, mul_transpose_self_of_mem hR.mem_orthogonal, Matrix.one_mulVec]
theorem IntegralOrthogonal.symm_apply (hR : IntegralOrthogonal R) (x : AmbientSpace) :
    Rᵀ *ᵥ (R *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, transpose_mul_self_of_mem hR.mem_orthogonal, Matrix.one_mulVec]
theorem dotProduct_mulVec_mulVec (hR : IntegralOrthogonal R) (w u : AmbientSpace) :
    (R *ᵥ w) ⬝ᵥ (R *ᵥ u) = w ⬝ᵥ u := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec,
    transpose_mul_self_of_mem hR.mem_orthogonal, Matrix.one_mulVec]
theorem exists_single_of_sum_sq_eq_one (m : Fin 4 → ℤ) (hm : ∑ κ, m κ ^ 2 = 1) :
    ∃ κ, (m κ = 1 ∨ m κ = -1) ∧ ∀ κ', κ' ≠ κ → m κ' = 0 := by apply _root_.YangMills.Construction.AffineTorusIsometries.exists_unit_of_sum_sq_eq_one <;> assumption
theorem mulVec_single (hR : IntegralOrthogonal R) (μ : Fin 4) :
    ∃ κ, ∃ e : ℝ, (e = 1 ∨ e = -1) ∧
      ∀ t : ℝ, R *ᵥ (Pi.single μ t : AmbientSpace) = Pi.single κ (e * t) := by
  have hint := hR.isInteger
  choose m hm using hint
  have hcol : ∀ (t : ℝ) (κ' : Fin 4),
      (R *ᵥ (Pi.single μ t : AmbientSpace)) κ' = (m κ' μ : ℝ) * t := by
    intro t κ'
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, hm]
  have hsum : ∑ κ', (m κ' μ) ^ 2 = 1 := by
    have h := dotProduct_mulVec_mulVec hR (Pi.single μ 1) (Pi.single μ 1)
    have hd : (Pi.single μ (1 : ℝ) : AmbientSpace) ⬝ᵥ (Pi.single μ (1 : ℝ) : AmbientSpace) = 1 := by
      simp [dotProduct, Pi.single_apply]
    rw [hd] at h
    have h2 : ∑ κ', ((m κ' μ : ℝ)) ^ 2 = 1 := by
      simpa [dotProduct, hcol, sq] using h
    exact_mod_cast h2
  obtain ⟨κ, hu, hz⟩ := exists_single_of_sum_sq_eq_one (fun κ' => m κ' μ) hsum
  refine ⟨κ, (m κ μ : ℝ), ?_, fun t => funext fun κ' => ?_⟩
  · rcases hu with h | h
    · left; simp [h]
    · right; simp [h]
  · rw [hcol]
    by_cases hk : κ' = κ
    · subst hk; simp
    · have h0 : m κ' μ = 0 := hz κ' hk
      simp [Pi.single_eq_of_ne hk, h0]
theorem axis_ne_of_ne (hR : IntegralOrthogonal R) {μ ν κ κ' : Fin 4} (hne : μ ≠ ν) {e e' : ℝ}
    (he : e = 1 ∨ e = -1) (he' : e' = 1 ∨ e' = -1)
    (h : ∀ t : ℝ, R *ᵥ (Pi.single μ t : AmbientSpace) = Pi.single κ (e * t))
    (h' : ∀ t : ℝ, R *ᵥ (Pi.single ν t : AmbientSpace) = Pi.single κ' (e' * t)) : κ ≠ κ' := by
  rintro rfl
  have h1 := dotProduct_mulVec_mulVec hR (Pi.single μ 1) (Pi.single ν 1)
  rw [h, h'] at h1
  have h2 : (Pi.single μ (1 : ℝ) : AmbientSpace) ⬝ᵥ (Pi.single ν (1 : ℝ) : AmbientSpace) = 0 := by
    simp [dotProduct, Pi.single_apply, Ne.symm hne]
  have h3 : (Pi.single κ (e * 1) : AmbientSpace) ⬝ᵥ (Pi.single κ (e' * 1) : AmbientSpace) =
      e * e' := by
    simp [dotProduct, Pi.single_apply]
  rw [h2, h3] at h1
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl <;> norm_num at h1
theorem mulVec_mem_latticeSubgroup (hR : IntegralOrthogonal R) {a : ℝ} {x : AmbientSpace}
    (hx : x ∈ InfiniteLattice.latticeSubgroup a) :
    R *ᵥ x ∈ InfiniteLattice.latticeSubgroup a := by
  have hint := hR.isInteger
  choose m hm using hint
  obtain ⟨N, hN⟩ := hx
  refine ⟨fun μ => ∑ ν, m μ ν * N ν, fun μ => ?_⟩
  simp only [Matrix.mulVec, dotProduct, hm, hN]
  push_cast
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun ν _ => by ring
theorem isIntegerMatrix_of_mulVec_single {a : ℝ} (ha : a ≠ 0)
    (hR : ∀ ν, R *ᵥ (Pi.single ν a : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a) :
    IsIntegerMatrix R := by
  intro μ ν
  obtain ⟨N, hN⟩ := hR ν
  have h : (R *ᵥ (Pi.single ν a : AmbientSpace)) μ = R μ ν * a := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  exact ⟨N μ, mul_right_cancel₀ ha (h.symm.trans (hN μ))⟩
theorem exists_mem_hyperoctahedral (hR : IntegralOrthogonal R) :
    ∃ w ∈ InfiniteLattice.hyperoctahedralLinearGroup, ∀ x : AmbientSpace, w x = R *ᵥ x := by
  have hmaps : ∀ {S : Matrix (Fin 4) (Fin 4) ℝ}, IntegralOrthogonal S →
      ∀ x ∈ InfiniteLattice.signedUnitVectors, S *ᵥ x ∈ InfiniteLattice.signedUnitVectors := by
    intro S hS x hx
    have hcol : ∀ μ : Fin 4,
        S *ᵥ (Pi.single μ (1 : ℝ) : AmbientSpace) ∈ InfiniteLattice.signedUnitVectors := by
      intro μ
      obtain ⟨κ, e, he, h⟩ := mulVec_single hS μ
      rw [h]
      rcases he with rfl | rfl
      · exact ⟨κ, Or.inl (by simp)⟩
      · exact ⟨κ, Or.inr (by rw [show (-1 : ℝ) * 1 = -1 by norm_num, Pi.single_neg])⟩
    obtain ⟨μ, rfl | rfl⟩ := hx
    · exact hcol μ
    · rw [Matrix.mulVec_neg]
      obtain ⟨κ, h | h⟩ := hcol μ
      · exact ⟨κ, Or.inr (by rw [h])⟩
      · exact ⟨κ, Or.inl (by rw [h, neg_neg])⟩
  have hbij : BijOn R.mulVecLin InfiniteLattice.signedUnitVectors
      InfiniteLattice.signedUnitVectors := by
    refine ⟨fun x hx => hmaps hR x hx, fun x _ y _ hxy => ?_, fun y hy => ?_⟩
    · have h : R *ᵥ x = R *ᵥ y := hxy
      rw [← hR.symm_apply x, h, hR.symm_apply]
    · exact ⟨Rᵀ *ᵥ y, hmaps hR.transpose y hy, hR.apply_symm y⟩
  obtain ⟨w, hw, hwf⟩ := InfiniteLattice.exists_mem_hyperoctahedralLinearGroup R.mulVecLin hbij
  exact ⟨w, hw, fun x => by rw [hwf]; rfl⟩
end Orthogonal
section Squares
variable {R : Matrix (Fin 4) (Fin 4) ℝ}
def quad (x u w : AmbientSpace) : Set AmbientSpace := {x, x + u, x + u + w, x + w}
theorem quad_comm (x u w : AmbientSpace) : quad x u w = quad x w u := by
  have h : x + w + u = x + u + w := by abel
  simp only [quad, h]
  ext z
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto
theorem quad_neg_left (x u w : AmbientSpace) : quad x (-u) w = quad (x - u) u w := by
  have h1 : x + -u = x - u := by abel
  have h2 : x - u + u = x := by abel
  simp only [quad, h1, h2]
  ext z
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto
theorem quad_neg_right (x u w : AmbientSpace) : quad x u (-w) = quad (x - w) u w := by
  rw [quad_comm, quad_neg_left, quad_comm]
theorem image_quad (v x u w : AmbientSpace) :
    (fun y : AmbientSpace => R *ᵥ y + v) '' quad x u w =
      quad (R *ᵥ x + v) (R *ᵥ u) (R *ᵥ w) := by
  have h1 : R *ᵥ x + R *ᵥ u + v = R *ᵥ x + v + R *ᵥ u := by abel
  have h2 : R *ᵥ x + R *ᵥ u + R *ᵥ w + v = R *ᵥ x + v + R *ᵥ u + R *ᵥ w := by abel
  have h3 : R *ᵥ x + R *ᵥ w + v = R *ᵥ x + v + R *ᵥ w := by abel
  simp only [quad, image_insert_eq, image_singleton, Matrix.mulVec_add, h1, h2, h3]
theorem image_latticeSubgroup (hR : IntegralOrthogonal R) {a : ℝ} {v : AmbientSpace}
    (hv : v ∈ InfiniteLattice.latticeSubgroup a) :
    (fun y : AmbientSpace => R *ᵥ y + v) '' (InfiniteLattice.latticeSubgroup a : Set AmbientSpace) =
      InfiniteLattice.latticeSubgroup a := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact add_mem (mulVec_mem_latticeSubgroup hR hx) hv
  · intro hz
    refine ⟨Rᵀ *ᵥ (z - v), mulVec_mem_latticeSubgroup hR.transpose (sub_mem hz hv), ?_⟩
    simp only [hR.apply_symm, sub_add_cancel]
theorem single_mem_latticeSubgroup {a e : ℝ} (he : e = 1 ∨ e = -1) (κ : Fin 4) :
    (Pi.single κ (e * a) : AmbientSpace) ∈ InfiniteLattice.latticeSubgroup a := by
  rcases he with rfl | rfl
  · refine ⟨Pi.single κ 1, fun μ => ?_⟩
    by_cases h : μ = κ
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  · refine ⟨-Pi.single κ 1, fun μ => ?_⟩
    by_cases h : μ = κ
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
end Squares
structure LatticeChart (a : ℝ) {T B P : Type} (π : AmbientSpace → T) (src tgt : B → T)
    (cs : P → Set T) : Prop where
  edge_of_point : ∀ x ∈ InfiniteLattice.latticeSubgroup a, ∀ (κ : Fin 4) (e : ℝ),
    (e = 1 ∨ e = -1) → ∃ b, src b = π x ∧ tgt b = π (x + Pi.single κ (e * a))
  point_of_edge : ∀ b, ∃ x ∈ InfiniteLattice.latticeSubgroup a, ∃ (κ : Fin 4) (e : ℝ),
    (e = 1 ∨ e = -1) ∧ src b = π x ∧ tgt b = π (x + Pi.single κ (e * a))
  face_of_point : ∀ x ∈ InfiniteLattice.latticeSubgroup a, ∀ α β : Fin 4, α < β →
    ∃ p, cs p = π '' quad x (Pi.single α a) (Pi.single β a)
  point_of_face : ∀ p, ∃ x ∈ InfiniteLattice.latticeSubgroup a, ∃ α β : Fin 4, α < β ∧
    cs p = π '' quad x (Pi.single α a) (Pi.single β a)
section ChartFacts
variable {a : ℝ} {T B P : Type} {π : AmbientSpace → T} {src tgt : B → T} {cs : P → Set T}
variable {R : Matrix (Fin 4) (Fin 4) ℝ} {v : AmbientSpace} {f : T → T}
theorem image_image_of_semiconj (hf : ∀ x, f (π x) = π (R *ᵥ x + v)) (S : Set AmbientSpace) :
    f '' (π '' S) = π '' ((fun y : AmbientSpace => R *ᵥ y + v) '' S) := by
  simp only [image_image, hf]
theorem LatticeChart.exists_face_lt (F : LatticeChart a π src tgt cs) {x : AmbientSpace}
    (hx : x ∈ InfiniteLattice.latticeSubgroup a) {α β : Fin 4} (h : α < β) {e e' : ℝ}
    (he : e = 1 ∨ e = -1) (he' : e' = 1 ∨ e' = -1) :
    ∃ p, cs p = π '' quad x (Pi.single α (e * a)) (Pi.single β (e' * a)) := by
  have hα := single_mem_latticeSubgroup (a := a) (e := 1) (Or.inl rfl) α
  have hβ := single_mem_latticeSubgroup (a := a) (e := 1) (Or.inl rfl) β
  rw [one_mul] at hα hβ
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl <;>
    simp only [one_mul, neg_mul, Pi.single_neg]
  · exact F.face_of_point x hx α β h
  · rw [quad_neg_right]
    exact F.face_of_point _ (sub_mem hx hβ) α β h
  · rw [quad_neg_left]
    exact F.face_of_point _ (sub_mem hx hα) α β h
  · rw [quad_neg_left, quad_neg_right]
    exact F.face_of_point _ (sub_mem (sub_mem hx hα) hβ) α β h
theorem LatticeChart.exists_face_ne (F : LatticeChart a π src tgt cs) {x : AmbientSpace}
    (hx : x ∈ InfiniteLattice.latticeSubgroup a) {α β : Fin 4} (h : α ≠ β) {e e' : ℝ}
    (he : e = 1 ∨ e = -1) (he' : e' = 1 ∨ e' = -1) :
    ∃ p, cs p = π '' quad x (Pi.single α (e * a)) (Pi.single β (e' * a)) := by
  rcases lt_or_gt_of_ne h with h' | h'
  · exact F.exists_face_lt hx h' he he'
  · rw [quad_comm]
    exact F.exists_face_lt hx h' he' he
theorem sign_mul_sign {e e' : ℝ} (he : e = 1 ∨ e = -1) (he' : e' = 1 ∨ e' = -1) :
    e * e' = 1 ∨ e * e' = -1 := by
  rcases he with rfl | rfl <;> rcases he' with rfl | rfl <;> norm_num
theorem LatticeChart.edges_onto (F : LatticeChart a π src tgt cs) (hR : IntegralOrthogonal R)
    (hv : v ∈ InfiniteLattice.latticeSubgroup a) (hf : ∀ x, f (π x) = π (R *ᵥ x + v)) :
    (∀ b, ∃ b', src b' = f (src b) ∧ tgt b' = f (tgt b)) ∧
      ∀ b', ∃ b, src b' = f (src b) ∧ tgt b' = f (tgt b) := by
  constructor
  · intro b
    obtain ⟨x, hx, κ, e, he, ht, hh⟩ := F.point_of_edge b
    obtain ⟨κ', e', he', hc⟩ := mulVec_single hR κ
    obtain ⟨b', h1, h2⟩ := F.edge_of_point (R *ᵥ x + v)
      (add_mem (mulVec_mem_latticeSubgroup hR hx) hv) κ' (e' * e) (sign_mul_sign he' he)
    refine ⟨b', ?_, ?_⟩
    · rw [h1, ht, hf]
    · rw [h2, hh, hf, Matrix.mulVec_add, hc, mul_assoc]
      congr 1
      abel
  · intro b'
    obtain ⟨y, hy, κ, e, he, ht, hh⟩ := F.point_of_edge b'
    obtain ⟨κ', e', he', hc⟩ := mulVec_single hR.transpose κ
    have hx : Rᵀ *ᵥ (y - v) ∈ InfiniteLattice.latticeSubgroup a :=
      mulVec_mem_latticeSubgroup hR.transpose (sub_mem hy hv)
    have hxy : R *ᵥ (Rᵀ *ᵥ (y - v)) + v = y := by
      rw [hR.apply_symm, sub_add_cancel]
    obtain ⟨b, h1, h2⟩ := F.edge_of_point _ hx κ' (e' * e) (sign_mul_sign he' he)
    have hstep : R *ᵥ (Pi.single κ' (e' * e * a) : AmbientSpace) = Pi.single κ (e * a) := by
      rw [mul_assoc, ← hc, hR.apply_symm]
    refine ⟨b, ?_, ?_⟩
    · rw [ht, h1, hf, hxy]
    · rw [hh, h2, hf, Matrix.mulVec_add, hstep]
      congr 1
      rw [← hxy]
      simp only [hR.apply_symm, sub_add_cancel]
      abel
theorem LatticeChart.faces_onto (F : LatticeChart a π src tgt cs) (hR : IntegralOrthogonal R)
    (hv : v ∈ InfiniteLattice.latticeSubgroup a) (hf : ∀ x, f (π x) = π (R *ᵥ x + v)) :
    (∀ p, ∃ p', cs p' = f '' cs p) ∧ ∀ p', ∃ p, cs p' = f '' cs p := by
  constructor
  · intro p
    obtain ⟨x, hx, α, β, h, hc⟩ := F.point_of_face p
    obtain ⟨κ, e, he, h1⟩ := mulVec_single hR α
    obtain ⟨κ', e', he', h2⟩ := mulVec_single hR β
    obtain ⟨p', hp'⟩ := F.exists_face_ne (add_mem (mulVec_mem_latticeSubgroup hR hx) hv)
      (axis_ne_of_ne hR h.ne he he' h1 h2) he he'
    refine ⟨p', ?_⟩
    rw [hp', hc, image_image_of_semiconj hf, image_quad, h1, h2]
  · intro p'
    obtain ⟨y, hy, α, β, h, hc⟩ := F.point_of_face p'
    obtain ⟨κ, e, he, h1⟩ := mulVec_single hR.transpose α
    obtain ⟨κ', e', he', h2⟩ := mulVec_single hR.transpose β
    have hx : Rᵀ *ᵥ (y - v) ∈ InfiniteLattice.latticeSubgroup a :=
      mulVec_mem_latticeSubgroup hR.transpose (sub_mem hy hv)
    have hxy : R *ᵥ (Rᵀ *ᵥ (y - v)) + v = y := by
      rw [hR.apply_symm, sub_add_cancel]
    obtain ⟨p, hp⟩ := F.exists_face_ne hx (axis_ne_of_ne hR.transpose h.ne he he' h1 h2) he he'
    refine ⟨p, ?_⟩
    rw [hp, image_image_of_semiconj hf, image_quad, hxy, hc, ← h1, ← h2, hR.apply_symm,
      hR.apply_symm]
end ChartFacts
theorem chart_ambient (a : ℝ) :
    LatticeChart a (id : AmbientSpace → AmbientSpace)
      (fun b : InfiniteLattice.Link a => (b.initial : AmbientSpace))
      (fun b : InfiniteLattice.Link a => (b.terminal : AmbientSpace))
      (fun p : InfiniteLattice.ElementaryPlaquette a => Subtype.val '' FullSpace.faceCorners p) where
  edge_of_point x hx κ e he := by
    refine ⟨⟨⟨x, hx⟩, ⟨x + Pi.single κ (e * a), add_mem hx (single_mem_latticeSubgroup he κ)⟩,
      κ, ?_⟩, rfl, rfl⟩
    rcases he with rfl | rfl
    · left
      apply Subtype.ext
      change x + Pi.single κ (1 * a) - x = Pi.single κ a
      simp
    · right
      apply Subtype.ext
      change x + Pi.single κ (-1 * a) - x = -Pi.single κ a
      simp [Pi.single_neg]
  point_of_edge b := by
    obtain ⟨μ, h | h⟩ := b.isAdjacent
    · refine ⟨b.initial, b.initial.2, μ, 1, Or.inl rfl, rfl, ?_⟩
      have h' : (b.terminal : AmbientSpace) - (b.initial : AmbientSpace) =
          (Pi.single μ a : AmbientSpace) := congrArg Subtype.val h
      change (b.terminal : AmbientSpace) = (b.initial : AmbientSpace) + Pi.single μ (1 * a)
      rw [one_mul, ← h']
      abel
    · refine ⟨b.initial, b.initial.2, μ, -1, Or.inr rfl, rfl, ?_⟩
      have h' : (b.terminal : AmbientSpace) - (b.initial : AmbientSpace) =
          -(Pi.single μ a : AmbientSpace) := congrArg Subtype.val h
      change (b.terminal : AmbientSpace) = (b.initial : AmbientSpace) + Pi.single μ (-1 * a)
      rw [neg_one_mul, Pi.single_neg, ← h']
      abel
  face_of_point x hx α β h := by
    refine ⟨⟨⟨x, hx⟩, α, β, h⟩, ?_⟩
    simp only [FullSpace.faceCorners, quad, image_insert_eq, image_singleton]
    rfl
  point_of_face p := by
    refine ⟨p.corner, p.corner.2, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis, ?_⟩
    simp only [FullSpace.faceCorners, quad, image_insert_eq, image_singleton]
    rfl
section TorusChart
variable {L n : ℕ}
theorem torusProj_add (S : ℝ) (x y : AmbientSpace) :
    torusProj S (x + y) = torusProj S x + torusProj S y := by apply _root_.YangMills.Construction.AffineTorusIsometries.torusProj_add' <;> assumption
theorem torusProj_zero (S : ℝ) : torusProj S 0 = 0 := by apply _root_.YangMills.Construction.LimitSpaces.PeriodizeOnSmallSets.torusProj_zero <;> assumption
theorem torusProj_single (κ : Fin 4) (t : ℝ) :
    torusProj (PeriodicLattice.torusSide L n) (Pi.single κ t) =
      PeriodicLattice.pointOnAxis L n κ t := by apply _root_.YangMills.Construction.InfiniteLattice.TorusCovering.torusProj_single <;> assumption
theorem pointOnAxis_neg (κ : Fin 4) (t : ℝ) :
    PeriodicLattice.pointOnAxis L n κ (-t) = -PeriodicLattice.pointOnAxis L n κ t := by apply _root_.YangMills.Construction.CellGrid.pointOnAxis_neg <;> assumption
theorem sublattice_eq_image (j : ℤ) :
    (PeriodicLattice.sublattice L n j : Set (PeriodicLattice.FourTorus L n)) =
      torusProj (PeriodicLattice.torusSide L n) ''
        (InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L j) : Set AmbientSpace) := by
  ext x
  constructor
  · rintro ⟨N, hN⟩
    exact ⟨fun μ => (N μ : ℝ) * PeriodicLattice.meshSize L j, ⟨N, fun _ => rfl⟩,
      funext fun μ => (hN μ).symm⟩
  · rintro ⟨y, ⟨N, hN⟩, rfl⟩
    refine ⟨N, fun μ => ?_⟩
    change ((y μ : ℝ) : AddCircle (PeriodicLattice.torusSide L n)) = _
    rw [hN]
theorem torusProj_mem_sublattice {j : ℤ} {x : AmbientSpace}
    (hx : x ∈ InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L j)) :
    torusProj (PeriodicLattice.torusSide L n) x ∈ PeriodicLattice.sublattice L n j := by
  exact show torusProj (PeriodicLattice.torusSide L n) x ∈
      (PeriodicLattice.sublattice L n j : Set (PeriodicLattice.FourTorus L n)) from by
    rw [sublattice_eq_image]
    exact mem_image_of_mem _ hx
theorem exists_lift_of_site {j : ℤ} (y : PeriodicLattice.Site L n j) :
    ∃ x ∈ InfiniteLattice.latticeSubgroup (PeriodicLattice.meshSize L j),
      torusProj (PeriodicLattice.torusSide L n) x = (y : PeriodicLattice.FourTorus L n) := by
  have h : (y : PeriodicLattice.FourTorus L n) ∈
      (PeriodicLattice.sublattice L n j : Set (PeriodicLattice.FourTorus L n)) := y.2
  rw [sublattice_eq_image] at h
  exact h
theorem chart_torus (L n : ℕ) (j : ℤ) :
    LatticeChart (PeriodicLattice.meshSize L j) (torusProj (PeriodicLattice.torusSide L n))
      (fun b : PeriodicLattice.Bond L n j => (b.source : PeriodicLattice.FourTorus L n))
      (fun b : PeriodicLattice.Bond L n j => (b.target : PeriodicLattice.FourTorus L n))
      (fun p : PeriodicLattice.Plaquette L n j => Subtype.val '' p.vertices) where
  edge_of_point x hx κ e he := by
    refine ⟨⟨⟨_, torusProj_mem_sublattice hx⟩,
      ⟨_, torusProj_mem_sublattice (add_mem hx (single_mem_latticeSubgroup he κ))⟩, κ, ?_⟩,
      rfl, rfl⟩
    rcases he with rfl | rfl
    · left
      apply Subtype.ext
      change torusProj (PeriodicLattice.torusSide L n)
          (x + Pi.single κ (1 * PeriodicLattice.meshSize L j)) -
        torusProj (PeriodicLattice.torusSide L n) x =
          PeriodicLattice.pointOnAxis L n κ (PeriodicLattice.meshSize L j)
      rw [torusProj_add, torusProj_single, one_mul, add_sub_cancel_left]
    · right
      apply Subtype.ext
      change torusProj (PeriodicLattice.torusSide L n)
          (x + Pi.single κ (-1 * PeriodicLattice.meshSize L j)) -
        torusProj (PeriodicLattice.torusSide L n) x =
          -PeriodicLattice.pointOnAxis L n κ (PeriodicLattice.meshSize L j)
      rw [torusProj_add, torusProj_single, neg_one_mul, add_sub_cancel_left, pointOnAxis_neg]
  point_of_edge b := by
    obtain ⟨x, hx, hxt⟩ := exists_lift_of_site b.source
    obtain ⟨μ, h | h⟩ := b.isNeighbour
    · refine ⟨x, hx, μ, 1, Or.inl rfl, hxt.symm, ?_⟩
      have h' : (b.target : PeriodicLattice.FourTorus L n) -
          (b.source : PeriodicLattice.FourTorus L n) =
          PeriodicLattice.pointOnAxis L n μ (PeriodicLattice.meshSize L j) :=
        congrArg Subtype.val h
      change (b.target : PeriodicLattice.FourTorus L n) = _
      rw [torusProj_add, torusProj_single, one_mul, ← h', hxt]
      abel
    · refine ⟨x, hx, μ, -1, Or.inr rfl, hxt.symm, ?_⟩
      have h' : (b.target : PeriodicLattice.FourTorus L n) -
          (b.source : PeriodicLattice.FourTorus L n) =
          -PeriodicLattice.pointOnAxis L n μ (PeriodicLattice.meshSize L j) :=
        congrArg Subtype.val h
      change (b.target : PeriodicLattice.FourTorus L n) = _
      rw [torusProj_add, torusProj_single, neg_one_mul, pointOnAxis_neg, ← h', hxt]
      abel
  face_of_point x hx α β h := by
    refine ⟨⟨⟨_, torusProj_mem_sublattice hx⟩, α, β, h⟩, ?_⟩
    simp only [PeriodicLattice.Plaquette.vertices, quad, image_insert_eq, image_singleton,
      torusProj_add, torusProj_single]
    rfl
  point_of_face p := by
    obtain ⟨x, hx, hb⟩ := exists_lift_of_site p.origin
    refine ⟨x, hx, p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis, ?_⟩
    simp only [PeriodicLattice.Plaquette.vertices, quad, image_insert_eq, image_singleton,
      torusProj_add, torusProj_single, hb]
    rfl
end TorusChart
theorem meshAt_ne_zero {L : ℕ} (hL : 0 < L) (k j : ℕ) : meshAt L k j ≠ 0 :=
  zpow_ne_zero _ (by exact_mod_cast hL.ne')
theorem latticeSubgroup_le_of_le {L : ℕ} (hL : 0 < L) {k i j : ℕ} (h : i ≤ j) :
    InfiniteLattice.latticeSubgroup (meshAt L k j) ≤
      InfiniteLattice.latticeSubgroup (meshAt L k i) := by
  rintro x ⟨N, hN⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  refine ⟨fun μ => N μ * (L : ℤ) ^ d, fun μ => ?_⟩
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  have hs : meshAt L k (i + d) = (L : ℝ) ^ d * meshAt L k i := by
    simp only [meshAt]
    rw [← zpow_natCast, ← zpow_add₀ hL']
    congr 1
    push_cast
    ring
  rw [hN μ, hs]
  push_cast
  ring
section Motions
variable {L n k : ℕ} {R : Matrix (Fin 4) (Fin 4) ℝ} {v : AmbientSpace}
theorem torus_mapsSublatticeOnto (hR : IntegralOrthogonal R) {i : ℕ}
    (hv : v ∈ InfiniteLattice.latticeSubgroup (meshAt L k i))
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hf : ∀ x, f (torusProj (PeriodicLattice.torusSide L n) x) =
      torusProj (PeriodicLattice.torusSide L n) (R *ᵥ x + v)) :
    MapsSublatticeOnto k i f := by
  have hv' : v ∈ InfiniteLattice.latticeSubgroup
      (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k i)) := by
    rw [meshSize_levelDepth]
    exact hv
  change f '' (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i) :
      Set (PeriodicLattice.FourTorus L n)) =
    PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k i)
  rw [sublattice_eq_image, image_image_of_semiconj hf, image_latticeSubgroup hR hv']
theorem torus_maps_all_levels (hL : 0 < L) (hR : IntegralOrthogonal R) {j : ℕ}
    (hv : v ∈ InfiniteLattice.latticeSubgroup (meshAt L k j))
    {f : PeriodicLattice.FourTorus L n → PeriodicLattice.FourTorus L n}
    (hf : ∀ x, f (torusProj (PeriodicLattice.torusSide L n) x) =
      torusProj (PeriodicLattice.torusSide L n) (R *ᵥ x + v)) :
    ∀ i ≤ j, MapsSublatticeOnto k i f ∧ MapsEdgesOnto k i f ∧ MapsFacesOnto k i f := by
  intro i hi
  have hvi := latticeSubgroup_le_of_le hL hi hv
  have hvi' : v ∈ InfiniteLattice.latticeSubgroup
      (PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k i)) := by
    rw [meshSize_levelDepth]
    exact hvi
  have F := chart_torus L n (PeriodicLattice.levelDepth k i)
  exact ⟨torus_mapsSublatticeOnto hR hvi hf, F.edges_onto hR hvi' hf, F.faces_onto hR hvi' hf⟩
end Motions
theorem symmetriesAreHypercubicMotions_of_classification (h : OrthogonalMotions.Classification) :
    SymmetriesAreHypercubicMotions := by
  obtain ⟨-, hmot, -, htor⟩ := h
  intro L hL0 hL k
  refine ⟨fun n hn j _ f hiso hon => ?_, fun j _ f hiso hon => ?_⟩
  · obtain ⟨-, -, hlift, -⟩ := htor L n hL hn
    obtain ⟨R, hR, himg, v₀, hform⟩ := hlift f hiso
    have hside : PeriodicLattice.torusSide L n ≠ 0 := by
      have : (L : ℝ) ≠ 0 := by exact_mod_cast hL0.ne'
      simp [PeriodicLattice.torusSide, this]
    have hint : IsIntegerMatrix R := isIntegerMatrix_of_mulVec_single hside fun ν => by
      have h1 := single_mem_latticeSubgroup (a := PeriodicLattice.torusSide L n) (e := 1)
        (Or.inl rfl) ν
      rw [one_mul] at h1
      exact show R *ᵥ (Pi.single ν (PeriodicLattice.torusSide L n) : AmbientSpace) ∈
          (InfiniteLattice.latticeSubgroup (PeriodicLattice.torusSide L n) : Set AmbientSpace) from by
        rw [← himg]
        exact ⟨_, h1, rfl⟩
    have hRo : IntegralOrthogonal R := ⟨hR, hint⟩
    have h0 : f 0 ∈ (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) :
        Set (PeriodicLattice.FourTorus L n)) := by
      have hon' : f '' (PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) :
          Set (PeriodicLattice.FourTorus L n)) =
          PeriodicLattice.sublattice L n (PeriodicLattice.levelDepth k j) := hon
      rw [← hon']
      exact mem_image_of_mem f (zero_mem _)
    rw [sublattice_eq_image, meshSize_levelDepth] at h0
    obtain ⟨v, hv, hvc⟩ := h0
    have hf0 : torusProj (PeriodicLattice.torusSide L n) v₀ = f 0 := by
      have h1 := hform 0
      rw [torusProj_zero, Matrix.mulVec_zero, zero_add] at h1
      exact h1.symm
    have hf : ∀ x, f (torusProj (PeriodicLattice.torusSide L n) x) =
        torusProj (PeriodicLattice.torusSide L n) (R *ᵥ x + v) := fun x => by
      rw [hform, torusProj_add, torusProj_add, hvc, hf0]
    obtain ⟨w, hw, hwx⟩ := exists_mem_hyperoctahedral hRo
    exact ⟨⟨w, hw, v, hv, fun x => by rw [hwx]; exact hf x⟩, torus_maps_all_levels hL0 hRo hv hf⟩
  · obtain ⟨R, hR, v, hform⟩ := hmot f hiso
    have hon' : f '' (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) =
      InfiniteLattice.latticeSubgroup (meshAt L k j) := hon
    have hmem : ∀ x ∈ InfiniteLattice.latticeSubgroup (meshAt L k j),
        f x ∈ InfiniteLattice.latticeSubgroup (meshAt L k j) := fun x hx => by
      exact show f x ∈ (InfiniteLattice.latticeSubgroup (meshAt L k j) : Set AmbientSpace) from by
        rw [← hon']
        exact mem_image_of_mem f hx
    have hv : v ∈ InfiniteLattice.latticeSubgroup (meshAt L k j) := by
      have h1 := hmem 0 (zero_mem _)
      rw [hform, Matrix.mulVec_zero, zero_add] at h1
      exact h1
    have hint : IsIntegerMatrix R :=
      isIntegerMatrix_of_mulVec_single (meshAt_ne_zero hL0 k j) fun ν => by
        have h1 := single_mem_latticeSubgroup (a := meshAt L k j) (e := 1) (Or.inl rfl) ν
        rw [one_mul] at h1
        have h2 := hmem _ h1
        rw [hform] at h2
        have h3 := sub_mem h2 hv
        rwa [add_sub_cancel_right] at h3
    have hRo : IntegralOrthogonal R := ⟨hR, hint⟩
    obtain ⟨w, hw, hwx⟩ := exists_mem_hyperoctahedral hRo
    refine ⟨⟨w, hw, v, hv, fun x => by rw [hwx]; exact hform x⟩, fun i hi => ?_, fun n hn => ?_⟩
    · have hvi := latticeSubgroup_le_of_le hL0 hi hv
      have F := chart_ambient (meshAt L k i)
      have hf' : ∀ x, f (id x) = id (R *ᵥ x + v) := hform
      have hfe : f = fun y : AmbientSpace => R *ᵥ y + v := funext hform
      refine ⟨?_, F.edges_onto hRo hvi hf', F.faces_onto hRo hvi hf'⟩
      change f '' (InfiniteLattice.latticeSubgroup (meshAt L k i) : Set AmbientSpace) = _
      rw [hfe]
      exact image_latticeSubgroup hRo hvi
    · obtain ⟨-, -, -, hind⟩ := htor L n hL hn
      obtain ⟨g, hg, hgi⟩ := hind R hR hint v
      exact ⟨g, fun x => by rw [hg, hform], hgi, torus_mapsSublatticeOnto hRo hv hg⟩
end Tower.HypercubicMotions
end YangMills.Construction
