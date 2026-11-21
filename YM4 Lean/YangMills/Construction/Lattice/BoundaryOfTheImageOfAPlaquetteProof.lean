import YangMills.Construction.Lattice.IsometryCovarianceOfHolonomiesAndActionsProof
import YangMills.Construction.Lattice.BoundaryOfTheImageOfAPlaquette
import YangMills.Construction.Lattice.CovarianceOfComplexAveragesProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.PlaquetteImageBoundaryProof
variable {L m : ℕ} {j : ℤ}
theorem bond_ext_coe {b b' : Bond L m j} (hs : (b.source : FourTorus L m) = b'.source)
    (ht : (b.target : FourTorus L m) = b'.target) : b = b' :=
  Bond.ext (Subtype.ext hs) (Subtype.ext ht)
section Bonds
variable {σ : FourTorus L m ≃ FourTorus L m}
theorem bondPreimage_source (hσ : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    ((bondPreimage σ b).source : FourTorus L m) = σ.symm b.source := (hσ.2.2.2.1 b).1
theorem bondPreimage_target (hσ : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    ((bondPreimage σ b).target : FourTorus L m) = σ.symm b.target := (hσ.2.2.2.1 b).2
theorem bondImage_opposite (hσ : MapsCellsAndCubes σ j) (b : Bond L m j) :
    bondImage σ b.opposite = (bondImage σ b).opposite := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.bondImage_opposite <;> assumption
end Bonds
theorem map_add_pointOnAxis {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame}
    {v : Fin 4 → ℝ} (haff : IsInducedByAffine σ r v) (y : FourTorus L m) (μ : Fin 4) (t : ℝ) :
    σ (y + pointOnAxis L m μ t) =
      σ y + (r.2 (r.1.symm μ) : ℤ) • pointOnAxis L m (r.1.symm μ) t := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.apply_add_pointOnAxis <;> assumption
theorem axis_eq_of_half_shift (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {b x : FourTorus L m}
    (hb : b ∈ sublattice L m j) (hx : x ∈ sublattice L m j) {f' g' f g : Fin 4} (hfg' : f' ≠ g')
    (c₁ c₂ : ℤˣ)
    (h : b + pointOnAxis L m f' (meshSize L j / 2) + pointOnAxis L m g' (meshSize L j / 2) =
      x + (c₁ : ℤ) • pointOnAxis L m f (meshSize L j / 2) +
        (c₂ : ℤ) • pointOnAxis L m g (meshSize L j / 2)) :
    f' = f ∨ f' = g := by exact _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.axis_eq_of_half_shift hL hj hb hx hfg' c₁ c₂ h
def parallelogramVertex {T : Type*} [Add T] (x A B : T) (k : Fin 4) : T :=
  ![x, x + A, x + A + B, x + B] k
def plaquetteVertex (p : Plaquette L m j) : Fin 4 → FourTorus L m :=
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
    ((boundaryEdge p k).source : FourTorus L m) = plaquetteVertex p k := by
  fin_cases k
  · rfl
  · rfl
  · change (p.origin : FourTorus L m) + pointOnAxis L m p.secondAxis (meshSize L j) +
      pointOnAxis L m p.firstAxis (meshSize L j) = _
    simp only [plaquetteVertex, parallelogramVertex]
    change _ = (p.origin : FourTorus L m) + pointOnAxis L m p.firstAxis (meshSize L j) +
      pointOnAxis L m p.secondAxis (meshSize L j)
    abel
  · rfl
theorem boundaryEdge_target (p : Plaquette L m j) (k : Fin 4) :
    ((boundaryEdge p k).target : FourTorus L m) = plaquetteVertex p (k + 1) := by
  fin_cases k
  · rfl
  · rfl
  · rfl
  · rfl
theorem parallelogramVertex_of_signs {T : Type*} [AddCommGroup T] (x h₁ h₂ b : T) (c₁ c₂ : ℤˣ)
    (hb : b + h₁ + h₂ = x + (c₁ : ℤ) • h₁ + (c₂ : ℤ) • h₂) :
    ∃ q : Fin 4,
      (c₁ * c₂ = 1 ∧ ∀ k, parallelogramVertex b (h₁ + h₁) (h₂ + h₂) k =
        parallelogramVertex x ((c₁ : ℤ) • (h₁ + h₁)) ((c₂ : ℤ) • (h₂ + h₂)) (k + q)) ∨
      (c₁ * c₂ = -1 ∧ ∀ k, parallelogramVertex b (h₁ + h₁) (h₂ + h₂) k =
        parallelogramVertex x ((c₁ : ℤ) • (h₁ + h₁)) ((c₂ : ℤ) • (h₂ + h₂)) (q - k)) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.parallelogram_vertices_of_signs <;> assumption
theorem parallelogramVertex_of_signs_swap {T : Type*} [AddCommGroup T] (x h₁ h₂ b : T)
    (c₁ c₂ : ℤˣ) (hb : b + h₂ + h₁ = x + (c₁ : ℤ) • h₁ + (c₂ : ℤ) • h₂) :
    ∃ q : Fin 4,
      (c₁ * c₂ = -1 ∧ ∀ k, parallelogramVertex b (h₂ + h₂) (h₁ + h₁) k =
        parallelogramVertex x ((c₁ : ℤ) • (h₁ + h₁)) ((c₂ : ℤ) • (h₂ + h₂)) (k + q)) ∨
      (c₁ * c₂ = 1 ∧ ∀ k, parallelogramVertex b (h₂ + h₂) (h₁ + h₁) k =
        parallelogramVertex x ((c₁ : ℤ) • (h₁ + h₁)) ((c₂ : ℤ) • (h₂ + h₂)) (q - k)) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.parallelogram_vertices_of_signs_swap <;> assumption
def orientationSign (r : SignedFrame) (μ ν : Fin 4) : ℤˣ :=
  r.2 (r.1.symm μ) * r.2 (r.1.symm ν) * (if r.1.symm μ < r.1.symm ν then 1 else -1)
theorem pointOnAxis_meshSize_eq_add (μ : Fin 4) : pointOnAxis L m μ (meshSize L j) =
    pointOnAxis L m μ (meshSize L j / 2) + pointOnAxis L m μ (meshSize L j / 2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.pointOnAxis_meshSize_eq_add <;> assumption
theorem plaquetteVertex_of_barycenter (hL : 0 < L) (hj : -(m : ℤ) ≤ j) {x : FourTorus L m}
    (hx : x ∈ sublattice L m j) (p' : Plaquette L m j) {f g : Fin 4} (c₁ c₂ : ℤˣ)
    (hbar : p'.barycenter = x + (c₁ : ℤ) • pointOnAxis L m f (meshSize L j / 2) +
      (c₂ : ℤ) • pointOnAxis L m g (meshSize L j / 2)) :
    (f < g → ∃ q : Fin 4,
      (c₁ * c₂ = 1 ∧ ∀ k, plaquetteVertex p' k =
        parallelogramVertex x ((c₁ : ℤ) • (pointOnAxis L m f (meshSize L j / 2) +
            pointOnAxis L m f (meshSize L j / 2)))
          ((c₂ : ℤ) • (pointOnAxis L m g (meshSize L j / 2) +
            pointOnAxis L m g (meshSize L j / 2))) (k + q)) ∨
      (c₁ * c₂ = -1 ∧ ∀ k, plaquetteVertex p' k =
        parallelogramVertex x ((c₁ : ℤ) • (pointOnAxis L m f (meshSize L j / 2) +
            pointOnAxis L m f (meshSize L j / 2)))
          ((c₂ : ℤ) • (pointOnAxis L m g (meshSize L j / 2) +
            pointOnAxis L m g (meshSize L j / 2))) (q - k))) ∧
    (g < f → ∃ q : Fin 4,
      (c₁ * c₂ = -1 ∧ ∀ k, plaquetteVertex p' k =
        parallelogramVertex x ((c₁ : ℤ) • (pointOnAxis L m f (meshSize L j / 2) +
            pointOnAxis L m f (meshSize L j / 2)))
          ((c₂ : ℤ) • (pointOnAxis L m g (meshSize L j / 2) +
            pointOnAxis L m g (meshSize L j / 2))) (k + q)) ∨
      (c₁ * c₂ = 1 ∧ ∀ k, plaquetteVertex p' k =
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
  have d₁ := axis_eq_of_half_shift hL hj p'.origin.2 hx p'.firstAxis_lt_secondAxis.ne c₁ c₂ h'
  have d₂ := axis_eq_of_half_shift hL hj p'.origin.2 hx p'.firstAxis_lt_secondAxis.ne' c₁ c₂ h''
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
    obtain ⟨q, hq⟩ := parallelogramVertex_of_signs x _ _ (p'.origin : FourTorus L m) c₁ c₂ h'
    refine ⟨q, ?_⟩
    simpa only [plaquetteVertex, e₁, e₂, ← pointOnAxis_meshSize_eq_add] using hq
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
    obtain ⟨q, hq⟩ :=
      parallelogramVertex_of_signs_swap x _ _ (p'.origin : FourTorus L m) c₁ c₂ h'
    refine ⟨q, ?_⟩
    simpa only [plaquetteVertex, e₁, e₂, ← pointOnAxis_meshSize_eq_add] using hq
section Image
variable {σ : FourTorus L m ≃ FourTorus L m} {r : SignedFrame} {v : Fin 4 → ℝ}
theorem map_plaquetteVertex (haff : IsInducedByAffine σ r v) (p : Plaquette L m j) (k : Fin 4) :
    σ (plaquetteVertex p k) = parallelogramVertex (σ p.origin)
      ((r.2 (r.1.symm p.firstAxis) : ℤ) •
        (pointOnAxis L m (r.1.symm p.firstAxis) (meshSize L j / 2) +
          pointOnAxis L m (r.1.symm p.firstAxis) (meshSize L j / 2)))
      ((r.2 (r.1.symm p.secondAxis) : ℤ) •
        (pointOnAxis L m (r.1.symm p.secondAxis) (meshSize L j / 2) +
          pointOnAxis L m (r.1.symm p.secondAxis) (meshSize L j / 2))) k := by
  fin_cases k
  · rfl
  · change σ ((p.origin : FourTorus L m) + pointOnAxis L m p.firstAxis (meshSize L j)) =
      (σ p.origin) + _
    rw [map_add_pointOnAxis haff, pointOnAxis_meshSize_eq_add (r.1.symm p.firstAxis)]
  · change σ ((p.origin : FourTorus L m) + pointOnAxis L m p.firstAxis (meshSize L j) +
      pointOnAxis L m p.secondAxis (meshSize L j)) = (σ p.origin) + _ + _
    rw [map_add_pointOnAxis haff, map_add_pointOnAxis haff,
      pointOnAxis_meshSize_eq_add (r.1.symm p.firstAxis),
      pointOnAxis_meshSize_eq_add (r.1.symm p.secondAxis)]
  · change σ ((p.origin : FourTorus L m) + pointOnAxis L m p.secondAxis (meshSize L j)) =
      (σ p.origin) + _
    rw [map_add_pointOnAxis haff, pointOnAxis_meshSize_eq_add (r.1.symm p.secondAxis)]
theorem map_barycenter (haff : IsInducedByAffine σ r v) (p : Plaquette L m j) :
    σ p.barycenter = σ p.origin +
      (r.2 (r.1.symm p.firstAxis) : ℤ) •
        pointOnAxis L m (r.1.symm p.firstAxis) (meshSize L j / 2) +
      (r.2 (r.1.symm p.secondAxis) : ℤ) •
        pointOnAxis L m (r.1.symm p.secondAxis) (meshSize L j / 2) := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryCovariance.apply_barycenter <;> assumption
theorem plaquetteImage_barycenter (hσ : MapsCellsAndCubes σ j) (p : Plaquette L m j) :
    (plaquetteImage σ p).barycenter = σ p.barycenter := hσ.2.2.2.2.2.2.2.1 p
theorem plaquetteImage_vertices (hL : 0 < L) (hj : -(m : ℤ) ≤ j)
    (hσ : MapsCellsAndCubes σ j) (haff : IsInducedByAffine σ r v)
    (p : Plaquette L m j) :
    ∃ q : Fin 4,
      (orientationSign r p.firstAxis p.secondAxis = 1 ∧
        ∀ k, plaquetteVertex (plaquetteImage σ p) k = σ (plaquetteVertex p (k + q))) ∨
      (orientationSign r p.firstAxis p.secondAxis = -1 ∧
        ∀ k, plaquetteVertex (plaquetteImage σ p) k = σ (plaquetteVertex p (q - k))) := by
  have hx : σ p.origin ∈ sublattice L m j := by
    have e : σ p.origin ∈ σ '' (sublattice L m j : Set (FourTorus L m)) :=
      mem_image_of_mem σ p.origin.2
    rw [hσ.1] at e
    exact e
  have hfg : r.1.symm p.firstAxis ≠ r.1.symm p.secondAxis :=
    fun e => p.firstAxis_lt_secondAxis.ne (r.1.symm.injective e)
  have hb := plaquetteImage_barycenter hσ p
  rw [map_barycenter haff] at hb
  obtain ⟨c₁, c₂⟩ := plaquetteVertex_of_barycenter hL hj hx (plaquetteImage σ p) _ _ hb
  rcases lt_or_gt_of_ne hfg with hlt | hgt
  · have he : orientationSign r p.firstAxis p.secondAxis =
        r.2 (r.1.symm p.firstAxis) * r.2 (r.1.symm p.secondAxis) := by
      simp [orientationSign, hlt]
    obtain ⟨q, hq⟩ := c₁ hlt
    refine ⟨q, ?_⟩
    rcases hq with ⟨hc, hk⟩ | ⟨hc, hk⟩
    · exact Or.inl ⟨he.trans hc, fun k => by rw [map_plaquetteVertex haff]; exact hk k⟩
    · exact Or.inr ⟨he.trans hc, fun k => by rw [map_plaquetteVertex haff]; exact hk k⟩
  · have he : orientationSign r p.firstAxis p.secondAxis =
        -(r.2 (r.1.symm p.firstAxis) * r.2 (r.1.symm p.secondAxis)) := by
      simp [orientationSign, not_lt.2 hgt.le]
    obtain ⟨q, hq⟩ := c₂ hgt
    refine ⟨q, ?_⟩
    rcases hq with ⟨hc, hk⟩ | ⟨hc, hk⟩
    · exact Or.inl ⟨by rw [he, hc, neg_neg], fun k => by rw [map_plaquetteVertex haff]; exact hk k⟩
    · exact Or.inr ⟨by rw [he, hc], fun k => by rw [map_plaquetteVertex haff]; exact hk k⟩
theorem bondPreimage_boundaryEdge_of_add (hσ' : MapsCellsAndCubes σ.symm j)
    {p p' : Plaquette L m j} {q : Fin 4}
    (hc : ∀ k, plaquetteVertex p' k = σ (plaquetteVertex p (k + q))) (k : Fin 4) :
    bondPreimage σ (boundaryEdge p' k) = boundaryEdge p (k + q) :=
  bond_ext_coe
    (by rw [bondPreimage_source hσ', boundaryEdge_source, hc, Equiv.symm_apply_apply,
      boundaryEdge_source])
    (by rw [bondPreimage_target hσ', boundaryEdge_target, hc, Equiv.symm_apply_apply,
      boundaryEdge_target, add_right_comm])
theorem bondPreimage_boundaryEdge_of_sub (hσ' : MapsCellsAndCubes σ.symm j)
    {p p' : Plaquette L m j} {q : Fin 4}
    (hc : ∀ k, plaquetteVertex p' k = σ (plaquetteVertex p (q - k))) (k : Fin 4) :
    bondPreimage σ (boundaryEdge p' k) = (boundaryEdge p (q - k - 1)).opposite :=
  bond_ext_coe
    (by
      rw [bondPreimage_source hσ', boundaryEdge_source, hc, Equiv.symm_apply_apply]
      change _ = (((boundaryEdge p (q - k - 1)).target : Site L m j) : FourTorus L m)
      rw [boundaryEdge_target, sub_add_cancel])
    (by
      rw [bondPreimage_target hσ', boundaryEdge_target, hc, Equiv.symm_apply_apply]
      change _ = (((boundaryEdge p (q - k - 1)).source : Site L m j) : FourTorus L m)
      rw [boundaryEdge_source, sub_sub])
end Image
theorem exists_boundaryEdge_eq {p : Plaquette L m j} {b : Bond L m j}
    (hb : b ∈ p.boundaryBonds) : ∃ k, b = boundaryEdge p k := by
  rw [boundaryBonds_eq] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with hb | hb | hb | hb
  · exact ⟨0, hb⟩
  · exact ⟨1, hb⟩
  · exact ⟨2, hb⟩
  · exact ⟨3, hb⟩
theorem boundaryEdge_mem (p : Plaquette L m j) (k : Fin 4) :
    boundaryEdge p k ∈ p.boundaryBonds := by
  rw [boundaryBonds_eq]
  fin_cases k <;> simp
theorem bondImage_bondPreimage {σ : FourTorus L m ≃ FourTorus L m}
    (hσ : MapsCellsAndCubes σ j) (hσ' : MapsCellsAndCubes σ.symm j) (b : Bond L m j) :
    bondImage σ (bondPreimage σ b) = b := by apply _root_.YangMills.Construction.PeriodicLattice.ComplexAveragesCommuteWithIsometries.bondImage_bondPreimage <;> assumption
theorem plaquetteImageBoundary_holds (hgroup : LatticeIsometryGroupActionStatement) :
    PlaquetteImageBoundary := by
  intro L m i j σ hL hm hi hσ hij p
  have hpos : 0 < L := by
    have := hL.2
    omega
  have hg := hgroup L m i hL hm hi
  have hσ' : σ.symm ∈ latticeIsometries L m i := by
    obtain ⟨⟨H, hH⟩, -⟩ := hg.1
    have t : σ ∈ (H : Set (Equiv.Perm (FourTorus L m))) := by rw [hH]; exact hσ
    have t' := H.inv_mem t
    rw [← hH]
    exact t'
  have hmap := (hg.2.2.2.2 σ hσ j hij).1
  have hmap' := (hg.2.2.2.2 σ.symm hσ' j hij).1
  obtain ⟨r, v, -, haff⟩ := hσ
  obtain ⟨q, ⟨-, hc⟩ | ⟨-, hc⟩⟩ := plaquetteImage_vertices hpos (by omega) hmap haff p
  · have e := bondPreimage_boundaryEdge_of_add hmap' hc
    constructor
    · intro b hb
      obtain ⟨k, rfl⟩ := exists_boundaryEdge_eq hb
      exact ⟨boundaryEdge p (k + q), boundaryEdge_mem p _,
        Or.inl (by rw [← e, bondImage_bondPreimage hmap hmap'])⟩
    · intro c hc'
      obtain ⟨l, rfl⟩ := exists_boundaryEdge_eq hc'
      refine ⟨boundaryEdge (plaquetteImage σ p) (l - q), boundaryEdge_mem _ _, Or.inl ?_⟩
      have e' := e (l - q)
      rw [sub_add_cancel] at e'
      rw [← e', bondImage_bondPreimage hmap hmap']
  · have e := bondPreimage_boundaryEdge_of_sub hmap' hc
    constructor
    · intro b hb
      obtain ⟨k, rfl⟩ := exists_boundaryEdge_eq hb
      refine ⟨boundaryEdge p (q - k - 1), boundaryEdge_mem p _, Or.inr ?_⟩
      rw [← bondImage_opposite hmap, ← e, bondImage_bondPreimage hmap hmap']
    · intro c hc'
      obtain ⟨l, rfl⟩ := exists_boundaryEdge_eq hc'
      refine ⟨boundaryEdge (plaquetteImage σ p) (q - l - 1), boundaryEdge_mem _ _, Or.inr ?_⟩
      have e' := e (q - l - 1)
      have a : q - (q - l - 1) - 1 = l := by abel
      rw [a] at e'
      rw [← bondImage_opposite hmap, ← e', bondImage_bondPreimage hmap hmap']
end YangMills.Construction.PeriodicLattice.PlaquetteImageBoundaryProof
