import YangMills.Construction.Lattice.CovariantAdjointsBySummationByParts
import YangMills.Construction.Towers.GaugeDirectionsInTheLeftChartProof
import YangMills.Construction.Averaging.MeanInTheComplexGroupProof
import YangMills.Construction.Lattice.CovarianceOfComplexPlaquetteVariables
import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActionsProof
import Mathlib
set_option autoImplicit false
open Set
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open YangMills.Construction.Matrices
namespace PlaquetteCovariance
variable {L m : ℕ} {j : ℤ}
theorem bond_ext_coe {b b' : Bond L m j} (hs : (b.source : FourTorus L m) = b'.source)
    (ht : (b.target : FourTorus L m) = b'.target) : b = b' :=
  Bond.ext (Subtype.ext hs) (Subtype.ext ht)
section Bonds
variable {σ : FourTorus L m ≃ FourTorus L m}
theorem bondPreimage_source (h : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    ((bondPreimage σ b).source : FourTorus L m) = σ.symm b.source := (h.2.2.2.1 b).1
theorem bondPreimage_target (h : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    ((bondPreimage σ b).target : FourTorus L m) = σ.symm b.target := (h.2.2.2.1 b).2
end Bonds
theorem apply_add_pointOnAxis {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame}
    {v : Fin 4 → ℝ} (hind : IsInducedByAffine σ r v) (y : FourTorus L m) (μ : Fin 4) (t : ℝ) :
    σ (y + pointOnAxis L m μ t) =
      σ y + (r.2 (r.1.symm μ) : ℤ) • pointOnAxis L m (r.1.symm μ) t := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.apply_add_pointOnAxis <;> assumption
theorem axis_eq_of_half_offsets (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {b x : FourTorus L m}
    (hb : b ∈ sublattice L m j) (hx : x ∈ sublattice L m j) {f' g' f g : Fin 4} (hfg' : f' ≠ g')
    (c₁ c₂ : ℤˣ)
    (h : b + pointOnAxis L m f' (meshSize L j / 2) + pointOnAxis L m g' (meshSize L j / 2) =
      x + (c₁ : ℤ) • pointOnAxis L m f (meshSize L j / 2) +
        (c₂ : ℤ) • pointOnAxis L m g (meshSize L j / 2)) :
    f' = f ∨ f' = g := by exact _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.axis_eq_of_half_shift hL hj hb hx hfg' c₁ c₂ h
def parallelogramVertex {T : Type*} [Add T] (x A B : T) (k : Fin 4) : T :=
  ![x, x + A, x + A + B, x + B] k
def vertexAt (p : Plaquette L m j) : Fin 4 → FourTorus L m :=
  parallelogramVertex (p.origin : FourTorus L m) (pointOnAxis L m p.firstAxis (meshSize L j))
    (pointOnAxis L m p.secondAxis (meshSize L j))
def boundaryEdge (p : Plaquette L m j) (k : Fin 4) : Bond L m j :=
  ![Bond.forwardFrom p.origin p.firstAxis,
    Bond.forwardFrom (p.origin + unitStep L m j p.firstAxis) p.secondAxis,
    (Bond.forwardFrom (p.origin + unitStep L m j p.secondAxis) p.firstAxis).opposite,
    (Bond.forwardFrom p.origin p.secondAxis).opposite] k
theorem boundaryBonds_eq (p : Plaquette L m j) :
    p.boundaryBonds = [boundaryEdge p 0, boundaryEdge p 1, boundaryEdge p 2, boundaryEdge p 3] :=
  rfl
theorem boundaryEdge_source (p : Plaquette L m j) (k : Fin 4) :
    ((boundaryEdge p k).source : FourTorus L m) = vertexAt p k := by
  fin_cases k
  · rfl
  · rfl
  · change (p.origin : FourTorus L m) + pointOnAxis L m p.secondAxis (meshSize L j) +
      pointOnAxis L m p.firstAxis (meshSize L j) = _
    simp only [vertexAt, parallelogramVertex]
    change _ = (p.origin : FourTorus L m) + pointOnAxis L m p.firstAxis (meshSize L j) +
      pointOnAxis L m p.secondAxis (meshSize L j)
    abel
  · rfl
theorem boundaryEdge_target (p : Plaquette L m j) (k : Fin 4) :
    ((boundaryEdge p k).target : FourTorus L m) = vertexAt p (k + 1) := by
  fin_cases k
  · rfl
  · rfl
  · rfl
  · rfl
theorem vertices_of_signs {T : Type*} [AddCommGroup T] (x h₁ h₂ b : T) (c₁ c₂ : ℤˣ)
    (hb : b + h₁ + h₂ = x + (c₁ : ℤ) • h₁ + (c₂ : ℤ) • h₂) :
    ∃ q : Fin 4,
      (c₁ * c₂ = 1 ∧ ∀ k, parallelogramVertex b (h₁ + h₁) (h₂ + h₂) k =
        parallelogramVertex x ((c₁ : ℤ) • (h₁ + h₁)) ((c₂ : ℤ) • (h₂ + h₂)) (k + q)) ∨
      (c₁ * c₂ = -1 ∧ ∀ k, parallelogramVertex b (h₁ + h₁) (h₂ + h₂) k =
        parallelogramVertex x ((c₁ : ℤ) • (h₁ + h₁)) ((c₂ : ℤ) • (h₂ + h₂)) (q - k)) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.parallelogram_vertices_of_signs <;> assumption
theorem vertices_of_signs_swapped {T : Type*} [AddCommGroup T] (x h₁ h₂ b : T) (c₁ c₂ : ℤˣ)
    (hb : b + h₂ + h₁ = x + (c₁ : ℤ) • h₁ + (c₂ : ℤ) • h₂) :
    ∃ q : Fin 4,
      (c₁ * c₂ = -1 ∧ ∀ k, parallelogramVertex b (h₂ + h₂) (h₁ + h₁) k =
        parallelogramVertex x ((c₁ : ℤ) • (h₁ + h₁)) ((c₂ : ℤ) • (h₂ + h₂)) (k + q)) ∨
      (c₁ * c₂ = 1 ∧ ∀ k, parallelogramVertex b (h₂ + h₂) (h₁ + h₁) k =
        parallelogramVertex x ((c₁ : ℤ) • (h₁ + h₁)) ((c₂ : ℤ) • (h₂ + h₂)) (q - k)) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.parallelogram_vertices_of_signs_swap <;> assumption
def orientationSign (r : SignedFrame) (μ ν : Fin 4) : ℤˣ :=
  r.2 (r.1.symm μ) * r.2 (r.1.symm ν) * (if r.1.symm μ < r.1.symm ν then 1 else -1)
theorem pointOnAxis_meshSize_eq_halves (μ : Fin 4) : pointOnAxis L m μ (meshSize L j) =
    pointOnAxis L m μ (meshSize L j / 2) + pointOnAxis L m μ (meshSize L j / 2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.pointOnAxis_meshSize_eq_add <;> assumption
theorem vertices_of_barycenter (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {x : FourTorus L m}
    (hx : x ∈ sublattice L m j) (p' : Plaquette L m j) {f g : Fin 4} (c₁ c₂ : ℤˣ)
    (hbar : p'.barycenter = x + (c₁ : ℤ) • pointOnAxis L m f (meshSize L j / 2) +
      (c₂ : ℤ) • pointOnAxis L m g (meshSize L j / 2)) :
    (f < g → ∃ q : Fin 4,
      (c₁ * c₂ = 1 ∧ ∀ k, vertexAt p' k =
        parallelogramVertex x ((c₁ : ℤ) • (pointOnAxis L m f (meshSize L j / 2) +
            pointOnAxis L m f (meshSize L j / 2)))
          ((c₂ : ℤ) • (pointOnAxis L m g (meshSize L j / 2) +
            pointOnAxis L m g (meshSize L j / 2))) (k + q)) ∨
      (c₁ * c₂ = -1 ∧ ∀ k, vertexAt p' k =
        parallelogramVertex x ((c₁ : ℤ) • (pointOnAxis L m f (meshSize L j / 2) +
            pointOnAxis L m f (meshSize L j / 2)))
          ((c₂ : ℤ) • (pointOnAxis L m g (meshSize L j / 2) +
            pointOnAxis L m g (meshSize L j / 2))) (q - k))) ∧
    (g < f → ∃ q : Fin 4,
      (c₁ * c₂ = -1 ∧ ∀ k, vertexAt p' k =
        parallelogramVertex x ((c₁ : ℤ) • (pointOnAxis L m f (meshSize L j / 2) +
            pointOnAxis L m f (meshSize L j / 2)))
          ((c₂ : ℤ) • (pointOnAxis L m g (meshSize L j / 2) +
            pointOnAxis L m g (meshSize L j / 2))) (k + q)) ∨
      (c₁ * c₂ = 1 ∧ ∀ k, vertexAt p' k =
        parallelogramVertex x ((c₁ : ℤ) • (pointOnAxis L m f (meshSize L j / 2) +
            pointOnAxis L m f (meshSize L j / 2)))
          ((c₂ : ℤ) • (pointOnAxis L m g (meshSize L j / 2) +
            pointOnAxis L m g (meshSize L j / 2))) (q - k))) := by
  have h' : (p'.origin : FourTorus L m) + pointOnAxis L m p'.firstAxis (meshSize L j / 2) +
      pointOnAxis L m p'.secondAxis (meshSize L j / 2) = _ := hbar
  have h'' : (p'.origin : FourTorus L m) + pointOnAxis L m p'.secondAxis (meshSize L j / 2) +
      pointOnAxis L m p'.firstAxis (meshSize L j / 2) =
      x + (c₁ : ℤ) • pointOnAxis L m f (meshSize L j / 2) +
        (c₂ : ℤ) • pointOnAxis L m g (meshSize L j / 2) := by
    rw [add_right_comm]
    exact h'
  have d₁ := axis_eq_of_half_offsets hL hj p'.origin.2 hx p'.firstAxis_lt_secondAxis.ne c₁ c₂ h'
  have d₂ := axis_eq_of_half_offsets hL hj p'.origin.2 hx p'.firstAxis_lt_secondAxis.ne' c₁ c₂ h''
  have l := p'.firstAxis_lt_secondAxis
  constructor
  · intro hlt
    have e₁ : p'.firstAxis = f := by
      rcases d₁ with d₁ | d₁
      · exact d₁
      · rcases d₂ with d₂ | d₂
        · rw [d₁, d₂] at l
          exact absurd l (not_lt.2 hlt.le)
        · rw [d₁, d₂] at l
          exact absurd l (lt_irrefl _)
    have e₂ : p'.secondAxis = g := by
      rcases d₂ with d₂ | d₂
      · rw [e₁, d₂] at l
        exact absurd l (lt_irrefl _)
      · exact d₂
    rw [e₁, e₂] at h'
    obtain ⟨q, hq⟩ := vertices_of_signs x _ _ (p'.origin : FourTorus L m) c₁ c₂ h'
    refine ⟨q, ?_⟩
    simpa only [vertexAt, e₁, e₂, ← pointOnAxis_meshSize_eq_halves] using hq
  · intro hgt
    have e₁ : p'.firstAxis = g := by
      rcases d₁ with d₁ | d₁
      · rcases d₂ with d₂ | d₂
        · rw [d₁, d₂] at l
          exact absurd l (lt_irrefl _)
        · rw [d₁, d₂] at l
          exact absurd l (not_lt.2 hgt.le)
      · exact d₁
    have e₂ : p'.secondAxis = f := by
      rcases d₂ with d₂ | d₂
      · exact d₂
      · rw [e₁, d₂] at l
        exact absurd l (lt_irrefl _)
    rw [e₁, e₂] at h'
    obtain ⟨q, hq⟩ := vertices_of_signs_swapped x _ _ (p'.origin : FourTorus L m) c₁ c₂ h'
    refine ⟨q, ?_⟩
    simpa only [vertexAt, e₁, e₂, ← pointOnAxis_meshSize_eq_halves] using hq
section Image
variable {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame} {v : Fin 4 → ℝ}
theorem apply_vertexAt (hind : IsInducedByAffine σ r v) (p : Plaquette L m j) (k : Fin 4) :
    σ (vertexAt p k) = parallelogramVertex (σ p.origin)
      ((r.2 (r.1.symm p.firstAxis) : ℤ) • (pointOnAxis L m (r.1.symm p.firstAxis) (meshSize L j / 2) +
        pointOnAxis L m (r.1.symm p.firstAxis) (meshSize L j / 2)))
      ((r.2 (r.1.symm p.secondAxis) : ℤ) • (pointOnAxis L m (r.1.symm p.secondAxis) (meshSize L j / 2) +
        pointOnAxis L m (r.1.symm p.secondAxis) (meshSize L j / 2))) k := by
  fin_cases k
  · rfl
  · change σ ((p.origin : FourTorus L m) + pointOnAxis L m p.firstAxis (meshSize L j)) = (σ p.origin) + _
    rw [apply_add_pointOnAxis hind, pointOnAxis_meshSize_eq_halves (r.1.symm p.firstAxis)]
  · change σ ((p.origin : FourTorus L m) + pointOnAxis L m p.firstAxis (meshSize L j) +
      pointOnAxis L m p.secondAxis (meshSize L j)) = (σ p.origin) + _ + _
    rw [apply_add_pointOnAxis hind, apply_add_pointOnAxis hind,
      pointOnAxis_meshSize_eq_halves (r.1.symm p.firstAxis),
      pointOnAxis_meshSize_eq_halves (r.1.symm p.secondAxis)]
  · change σ ((p.origin : FourTorus L m) + pointOnAxis L m p.secondAxis (meshSize L j)) = (σ p.origin) + _
    rw [apply_add_pointOnAxis hind, pointOnAxis_meshSize_eq_halves (r.1.symm p.secondAxis)]
theorem apply_barycenter (hind : IsInducedByAffine σ r v) (p : Plaquette L m j) :
    σ p.barycenter = σ p.origin +
      (r.2 (r.1.symm p.firstAxis) : ℤ) • pointOnAxis L m (r.1.symm p.firstAxis) (meshSize L j / 2) +
      (r.2 (r.1.symm p.secondAxis) : ℤ) • pointOnAxis L m (r.1.symm p.secondAxis) (meshSize L j / 2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.apply_barycenter <;> assumption
theorem plaquetteImage_barycenter (h : MapsCellsAndCubes σ j) (p : Plaquette L m j) :
    (plaquetteImage σ p).barycenter = σ p.barycenter := h.2.2.2.2.2.2.2.1 p
theorem plaquetteImage_vertices (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (h : MapsCellsAndCubes σ j) (hind : IsInducedByAffine σ r v)
    (p : Plaquette L m j) :
    ∃ q : Fin 4,
      (orientationSign r p.firstAxis p.secondAxis = 1 ∧
        ∀ k, vertexAt (plaquetteImage σ p) k = σ (vertexAt p (k + q))) ∨
      (orientationSign r p.firstAxis p.secondAxis = -1 ∧
        ∀ k, vertexAt (plaquetteImage σ p) k = σ (vertexAt p (q - k))) := by
  have hx : σ p.origin ∈ sublattice L m j := by
    have e : σ p.origin ∈ σ '' (sublattice L m j : Set (FourTorus L m)) :=
      mem_image_of_mem σ p.origin.2
    rw [h.1] at e
    exact e
  have hfg : r.1.symm p.firstAxis ≠ r.1.symm p.secondAxis :=
    fun e => p.firstAxis_lt_secondAxis.ne (r.1.symm.injective e)
  have hb := plaquetteImage_barycenter h p
  rw [apply_barycenter hind] at hb
  obtain ⟨c₁, c₂⟩ := vertices_of_barycenter hL hj hx (plaquetteImage σ p) _ _ hb
  rcases lt_or_gt_of_ne hfg with hlt | hgt
  · have he : orientationSign r p.firstAxis p.secondAxis =
        r.2 (r.1.symm p.firstAxis) * r.2 (r.1.symm p.secondAxis) := by
      simp [orientationSign, hlt]
    obtain ⟨q, hq⟩ := c₁ hlt
    refine ⟨q, ?_⟩
    rcases hq with ⟨hc, hk⟩ | ⟨hc, hk⟩
    · exact Or.inl ⟨he.trans hc, fun k => by rw [apply_vertexAt hind]; exact hk k⟩
    · exact Or.inr ⟨he.trans hc, fun k => by rw [apply_vertexAt hind]; exact hk k⟩
  · have he : orientationSign r p.firstAxis p.secondAxis =
        -(r.2 (r.1.symm p.firstAxis) * r.2 (r.1.symm p.secondAxis)) := by
      simp [orientationSign, not_lt.2 hgt.le]
    obtain ⟨q, hq⟩ := c₂ hgt
    refine ⟨q, ?_⟩
    rcases hq with ⟨hc, hk⟩ | ⟨hc, hk⟩
    · exact Or.inl ⟨by rw [he, hc, neg_neg], fun k => by rw [apply_vertexAt hind]; exact hk k⟩
    · exact Or.inr ⟨by rw [he, hc], fun k => by rw [apply_vertexAt hind]; exact hk k⟩
theorem bondPreimage_boundaryEdge_of_rotation (h' : MapsCellsAndCubes σ.symm j)
    {p p' : Plaquette L m j} {q : Fin 4}
    (hc : ∀ k, vertexAt p' k = σ (vertexAt p (k + q))) (k : Fin 4) :
    bondPreimage σ (boundaryEdge p' k) = boundaryEdge p (k + q) :=
  bond_ext_coe
    (by rw [bondPreimage_source h', boundaryEdge_source, hc, Equiv.symm_apply_apply,
      boundaryEdge_source])
    (by rw [bondPreimage_target h', boundaryEdge_target, hc, Equiv.symm_apply_apply,
      boundaryEdge_target, add_right_comm])
theorem bondPreimage_boundaryEdge_of_reflection (h' : MapsCellsAndCubes σ.symm j)
    {p p' : Plaquette L m j} {q : Fin 4}
    (hc : ∀ k, vertexAt p' k = σ (vertexAt p (q - k))) (k : Fin 4) :
    bondPreimage σ (boundaryEdge p' k) = (boundaryEdge p (q - k - 1)).opposite :=
  bond_ext_coe
    (by
      rw [bondPreimage_source h', boundaryEdge_source, hc, Equiv.symm_apply_apply]
      change _ = (((boundaryEdge p (q - k - 1)).target : Site L m j) : FourTorus L m)
      rw [boundaryEdge_target, sub_add_cancel])
    (by
      rw [bondPreimage_target h', boundaryEdge_target, hc, Equiv.symm_apply_apply]
      change _ = (((boundaryEdge p (q - k - 1)).source : Site L m j) : FourTorus L m)
      rw [boundaryEdge_source, sub_sub])
end Image
theorem fin_four_eq (q : Fin 4) : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by apply _root_.YangMills.Construction.GaugeFixing.fin_four_cases <;> assumption
theorem prod_rotated_eq_conj {β : Type*} (U : β → ComplexMatrix2) (e : Fin 4 → β)
    (hu : ∀ k, IsUnit (U (e k))) (q : Fin 4) :
    U (e (0 + q)) * (U (e (1 + q)) * (U (e (2 + q)) * U (e (3 + q)))) =
      (([e 0, e 1, e 2, e 3].drop q).map U).prod * ([e 0, e 1, e 2, e 3].map U).prod *
        ((([e 0, e 1, e 2, e 3].drop q).map U).prod)⁻¹ := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.rotated_product_eq_conj <;> assumption
theorem prod_reflected_eq_conj {β : Type*} (U : β → ComplexMatrix2) (e : Fin 4 → β)
    (hu : ∀ k, IsUnit (U (e k))) (q : Fin 4) :
    (U (e (q - 0 - 1)))⁻¹ * ((U (e (q - 1 - 1)))⁻¹ * ((U (e (q - 2 - 1)))⁻¹ *
        (U (e (q - 3 - 1)))⁻¹)) =
      (([e 0, e 1, e 2, e 3].drop q).map U).prod * (([e 0, e 1, e 2, e 3].map U).prod)⁻¹ *
        ((([e 0, e 1, e 2, e 3].drop q).map U).prod)⁻¹ := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.reflected_product_eq_conj <;> assumption
theorem boundaryEdge_mem (p : Plaquette L m j) (k : Fin 4) : boundaryEdge p k ∈ p.boundaryBonds := by
  rw [boundaryBonds_eq]
  rcases fin_four_eq k with rfl | rfl | rfl | rfl <;> simp
theorem plaquetteHolonomy_eq_prod (U : Bond L m j → ComplexMatrix2) (p : Plaquette L m j) :
    plaquetteHolonomy U p =
      U (boundaryEdge p 0) * (U (boundaryEdge p 1) * (U (boundaryEdge p 2) * U (boundaryEdge p 3))) := by
  simp only [plaquetteHolonomy, pathHolonomy, boundaryBonds_eq, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one]
theorem det_eq_one_of_mem {X : ComplexMatrix2} (h : X ∈ complexGaugeGroup) : X.det = 1 := h
theorem isUnit_of_mem_complexGaugeGroup {X : ComplexMatrix2} (h : X ∈ complexGaugeGroup) : IsUnit X := by apply _root_.YangMills.Construction.Averaging.ComplexLogMean.isUnit_of_mem_complexGaugeGroup <;> assumption
theorem det_pathHolonomy {B : Set (Bond L m j)} {U : Bond L m j → ComplexMatrix2}
    (hU : IsGaugeField complexGaugeGroup B U) {Γ : List (Bond L m j)} (hΓ : ∀ b ∈ Γ, b ∈ B) :
    (pathHolonomy U Γ).det = 1 := by
  induction Γ with
  | nil => simp [pathHolonomy]
  | cons b Γ ih =>
    have h₁ := det_eq_one_of_mem (hU.1 b (hΓ b List.mem_cons_self))
    have h₂ := ih fun c hc => hΓ c (List.mem_cons_of_mem b hc)
    simp only [pathHolonomy, List.map_cons, List.prod_cons, Matrix.det_mul] at h₂ ⊢
    rw [h₁, h₂, one_mul]
section Variables
variable {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame} {v : Fin 4 → ℝ}
theorem plaquetteHolonomy_transport (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (h : MapsCellsAndCubes σ j) (h' : MapsCellsAndCubes σ.symm j)
    (hind : IsInducedByAffine σ r v) (p : Plaquette L m j) :
    ∃ Γ : List (Bond L m j), Γ <:+: p.boundaryBonds ∧
      ∀ (B : Set (Bond L m j)) (U : Bond L m j → ComplexMatrix2), IsGaugeField complexGaugeGroup B U →
        (∀ b ∈ p.boundaryBonds, b ∈ B) →
        plaquetteHolonomy (transportGaugeField σ U) (plaquetteImage σ p) =
          pathHolonomy U Γ *
            plaquetteHolonomy U p ^ ((orientationSign r p.firstAxis p.secondAxis : ℤˣ) : ℤ) *
            (pathHolonomy U Γ)⁻¹ := by
  obtain ⟨q, ⟨he, hc⟩ | ⟨he, hc⟩⟩ := plaquetteImage_vertices hL hj h hind p
  · refine ⟨p.boundaryBonds.drop q, (List.drop_suffix _ _).isInfix, fun B U hU hp => ?_⟩
    have hu : ∀ k, IsUnit (U (boundaryEdge p k)) :=
      fun k => isUnit_of_mem_complexGaugeGroup (hU.1 _ (hp _ (boundaryEdge_mem p k)))
    rw [he, plaquetteHolonomy_eq_prod]
    simp only [transportGaugeField, bondPreimage_boundaryEdge_of_rotation h' hc, Units.val_one,
      zpow_one]
    exact prod_rotated_eq_conj U (boundaryEdge p) hu q
  · refine ⟨p.boundaryBonds.drop q, (List.drop_suffix _ _).isInfix, fun B U hU hp => ?_⟩
    have hu : ∀ k, IsUnit (U (boundaryEdge p k)) :=
      fun k => isUnit_of_mem_complexGaugeGroup (hU.1 _ (hp _ (boundaryEdge_mem p k)))
    rw [he, plaquetteHolonomy_eq_prod]
    simp only [transportGaugeField, bondPreimage_boundaryEdge_of_reflection h' hc, Units.val_neg,
      Units.val_one, Int.reduceNeg, zpow_neg_one]
    simp only [hU.2 _ (hp _ (boundaryEdge_mem p _))]
    exact prod_reflected_eq_conj U (boundaryEdge p) hu q
end Variables
theorem fullTrace_conj {Q : ComplexMatrix2} (hQ : Q.det = 1) (Y : ComplexMatrix2) :
    ComplexMatrix2.fullTrace (Q * Y * Q⁻¹) = ComplexMatrix2.fullTrace Y := by apply _root_.YangMills.DeltaSharedProofs.p68910 <;> assumption
theorem fullTrace_inv {X : ComplexMatrix2} (hX : X.det = 1) :
    ComplexMatrix2.fullTrace X⁻¹ = ComplexMatrix2.fullTrace X := by apply _root_.YangMills.DeltaSharedProofs.p7762 <;> assumption
theorem fullTrace_zpow_units {X : ComplexMatrix2} (hX : X.det = 1) (c : ℤˣ) :
    ComplexMatrix2.fullTrace (X ^ (c : ℤ)) = ComplexMatrix2.fullTrace X := by
  rcases Int.units_eq_one_or c with rfl | rfl
  · simp
  · simpa using fullTrace_inv hX
theorem analyticAt_fullTrace (X : ComplexMatrix2) :
    AnalyticAt ℂ (fun Y : ComplexMatrix2 => ComplexMatrix2.fullTrace Y) X := by
  have h : (fun Y : ComplexMatrix2 => ComplexMatrix2.fullTrace Y) =
      ⇑(LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)) := by
    funext Y
    rfl
  rw [h]
  exact ContinuousLinearMap.analyticAt _ _
theorem analyticAt_conj_zpow {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {H P : W → ComplexMatrix2} {w : W} (hH : AnalyticAt ℂ H w) (hP : AnalyticAt ℂ P w)
    (dH : (H w).det ≠ 0) (dP : (P w).det ≠ 0) (c : ℤˣ) :
    AnalyticAt ℂ (fun x => H x * P x ^ (c : ℤ) * (H x)⁻¹) w := by
  have iH : AnalyticAt ℂ (fun x => (H x)⁻¹) w :=
    AnalyticAt.comp (g := fun Y : ComplexMatrix2 => Y⁻¹) (analyticAt_inv_of_det_ne_zero dH) hH
  have iP : AnalyticAt ℂ (fun x => (P x)⁻¹) w :=
    AnalyticAt.comp (g := fun Y : ComplexMatrix2 => Y⁻¹) (analyticAt_inv_of_det_ne_zero dP) hP
  rcases Int.units_eq_one_or c with rfl | rfl
  · simpa [Pi.mul_def] using (hH.mul hP).mul iH
  · simpa [Pi.mul_def] using (hH.mul iP).mul iH
theorem holomorphicEquation_of_formula {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {σ : FourTorus L m ≃ FourTorus L m} {B : Set (Bond L m j)} [Fintype ↥B]
    {f₁ f₂ : (Bond L m j → ComplexMatrix2) → E} (F : (↥B → ComplexMatrix2) → E)
    (hF : ∀ U ∈ complexGaugeFields B, AnalyticAt ℂ F (restrictToBonds B U))
    (h₂ : ∀ U ∈ complexGaugeFields B, f₂ U = F (restrictToBonds B U))
    (h₁₂ : ∀ U ∈ complexGaugeFields B, f₁ U = f₂ U) :
    IsHolomorphicEquationOnComplexFields σ B f₁ f₂ := by
  unfold IsHolomorphicEquationOnComplexFields IsHolomorphicEquation
  simp only [inter_self]
  exact ⟨IsHolomorphicOnFields.of_analytic_formula F subset_rfl (isRelativelyOpen_self _) hF
      fun U hU => (h₁₂ U hU).trans (h₂ U hU),
    IsHolomorphicOnFields.of_analytic_formula F subset_rfl (isRelativelyOpen_self _) hF h₂, h₁₂,
    fun _ => trivial⟩
end PlaquetteCovariance
open PlaquetteCovariance in
theorem plaquetteVariablesCovarianceStatement_holds
    (h₁ : LatticeIsometryGroupActionStatement) :
    PlaquetteVariablesCovarianceStatement := by
  refine ⟨orientationSign, fun L m i σ hL hm hi hσ => ?_⟩
  have hpos : 0 < L := by
    have := hL.2
    omega
  have hg := h₁ L m i hL hm hi
  have hσ' : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨⟨H, hH⟩, -⟩ := hg.1
    have t : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
    have t' := H.inv_mem t
    rw [← hH]
    exact t'
  obtain ⟨v, hind⟩ : HasLinearPart σ (linearComponent σ) := by
    obtain ⟨r, v, -, hrv⟩ := hσ
    have hex : ∃ r : SignedFrame, HasLinearPart σ r := ⟨r, v, hrv⟩
    unfold linearComponent
    rw [dif_pos hex]
    exact hex.choose_spec
  intro j hj p
  have hcar : MapsCellsAndCubes σ j := (hg.2.2.2.2 σ hσ j hj).1
  have hcar' : MapsCellsAndCubes σ.symm j := (hg.2.2.2.2 σ.symm hσ' j hj).1
  obtain ⟨Γ, hΓ, hid⟩ := plaquetteHolonomy_transport hpos (hi.trans hj) hcar hcar' hind p
  refine ⟨Γ, hΓ, fun B _ hp => ?_⟩
  have hfin : Finite (Bond L m j) := by
    have : Finite (Site L m j) := SeparatedSequences.BaseParameters.site_finite hpos m j
    refine Finite.of_injective (fun b : Bond L m j => (b.source, b.target)) ?_
    intro b b' hb
    exact Bond.ext (congrArg Prod.fst hb) (congrArg Prod.snd hb)
  let : Fintype ↥B := Fintype.ofFinite _
  have hpb : ∀ b ∈ p.boundaryBonds, b ∈ B := hp
  have hΓB : ∀ b ∈ Γ, b ∈ B := fun b hb => hpb b (hΓ.subset hb)
  have hvalΓ : ∀ U : Bond L m j → ComplexMatrix2,
      pathHolonomy (extendWithIdentity B (restrictToBonds B U)) Γ = pathHolonomy U Γ :=
    fun U => pathHolonomy_extendByOne U hΓB
  have hvalP : ∀ U : Bond L m j → ComplexMatrix2,
      plaquetteHolonomy (extendWithIdentity B (restrictToBonds B U)) p = plaquetteHolonomy U p :=
    fun U => pathHolonomy_extendByOne U hpb
  have aΓ : ∀ w, AnalyticAt ℂ
      (fun w : ↥B → ComplexMatrix2 => pathHolonomy (extendWithIdentity B w) Γ) w :=
    analyticAt_pathHolonomy_extendByOne hΓB
  have aP : ∀ w, AnalyticAt ℂ
      (fun w : ↥B → ComplexMatrix2 => plaquetteHolonomy (extendWithIdentity B w) p) w :=
    analyticAt_pathHolonomy_extendByOne hpb
  have dΓ : ∀ U ∈ complexGaugeFields B, (pathHolonomy U Γ).det = 1 :=
    fun U hU => det_pathHolonomy hU hΓB
  have dP : ∀ U ∈ complexGaugeFields B, (plaquetteHolonomy U p).det = 1 :=
    fun U hU => det_pathHolonomy hU hpb
  refine ⟨holomorphicEquation_of_formula
    (fun w => pathHolonomy (extendWithIdentity B w) Γ *
      plaquetteHolonomy (extendWithIdentity B w) p ^
        ((orientationSign (linearComponent σ) p.firstAxis p.secondAxis : ℤˣ) : ℤ) *
        (pathHolonomy (extendWithIdentity B w) Γ)⁻¹) ?_ ?_ ?_,
    holomorphicEquation_of_formula (fun w => plaquetteEnergy (extendWithIdentity B w) p) ?_ ?_ ?_⟩
  · intro U hU
    refine analyticAt_conj_zpow (aΓ _) (aP _) ?_ ?_ _
    · rw [hvalΓ, dΓ U hU]
      exact one_ne_zero
    · rw [hvalP, dP U hU]
      exact one_ne_zero
  · intro U _
    simp only [hvalΓ, hvalP]
  · exact fun U hU => hid B U hU hpb
  · intro U _
    unfold plaquetteEnergy
    exact analyticAt_const.sub (analyticAt_const.mul
      (AnalyticAt.comp (g := fun Y : ComplexMatrix2 => ComplexMatrix2.fullTrace Y)
        (analyticAt_fullTrace _) (aP _)))
  · intro U _
    simp only [plaquetteEnergy, hvalP]
  · intro U hU
    simp only [plaquetteEnergy]
    rw [hid B U hU hpb, fullTrace_conj (dΓ U hU), fullTrace_zpow_units (dP U hU)]
end YangMills.Construction.PeriodicLattice
