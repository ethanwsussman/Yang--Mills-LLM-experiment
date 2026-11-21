import YangMills.Construction.Towers.TowersOfLattices
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace Tower
section Transport
variable {X Y X' Y' V W : Type*}
def transportList (e : X ≃ Y) (Γ : List X) : List Y := Γ.map e
def transportFun (e : X ≃ Y) (S : Set X) : (S → V) ≃ (e '' S → V) :=
  (e.image S).arrowCongr (Equiv.refl V)
theorem transportFun_apply_image (e : X ≃ Y) (S : Set X) (f : S → V) (σ : S) :
    transportFun e S f (e.image S σ) = f σ := by
  simp [transportFun]
def conjMap (e : X ≃ Y) (s : X → X) : Y → Y := e ∘ s ∘ e.symm
def transportTotal (e : X ≃ Y) (f : X → V) : Y → V := f ∘ e.symm
theorem transportTotal_apply (e : X ≃ Y) (f : X → V) (σ : X) :
    transportTotal e f (e σ) = f σ := by
  simp [transportTotal]
def transportTotalFunValued (e : X ≃ Y) (e' : X' ≃ Y') (Φ : (X → V) → X' → W) :
    (Y → V) → Y' → W :=
  fun F => transportTotal e' (Φ (F ∘ e))
theorem transportTotalFunValued_transportTotal (e : X ≃ Y) (e' : X' ≃ Y')
    (Φ : (X → V) → X' → W) (f : X → V) :
    transportTotalFunValued e e' Φ (transportTotal e f) = transportTotal e' (Φ f) := by
  have h : transportTotal e f ∘ e = f := by
    funext σ
    exact transportTotal_apply e f σ
  simp only [transportTotalFunValued, h]
def transportTotalScalar (e : X ≃ Y) (Φ : (X → V) → W) : (Y → V) → W := fun F => Φ (F ∘ e)
theorem transportTotalScalar_transportTotal (e : X ≃ Y) (Φ : (X → V) → W) (f : X → V) :
    transportTotalScalar e Φ (transportTotal e f) = Φ f := by
  have h : transportTotal e f ∘ e = f := by
    funext σ
    exact transportTotal_apply e f σ
  simp only [transportTotalScalar, h]
end Transport
section EdgesOfVertices
variable {L m m' : ℕ} {d d' : ℤ}
def edgeEquivOfVertexEquiv (s : PeriodicLattice.Site L m d ≃+ PeriodicLattice.Site L m' d')
    (hs : ∀ μ, s (PeriodicLattice.unitStep L m d μ) = PeriodicLattice.unitStep L m' d' μ) :
    PeriodicLattice.Bond L m d ≃ PeriodicLattice.Bond L m' d' where
  toFun b := ⟨s b.source, s b.target, by
    obtain ⟨μ, h | h⟩ := b.isNeighbour
    · exact ⟨μ, Or.inl (by rw [← map_sub, h, hs])⟩
    · exact ⟨μ, Or.inr (by rw [← map_sub, h, map_neg, hs])⟩⟩
  invFun b := ⟨s.symm b.source, s.symm b.target, by
    have hs' : ∀ μ, s.symm (PeriodicLattice.unitStep L m' d' μ) =
        PeriodicLattice.unitStep L m d μ := fun μ => by
      rw [← hs, s.symm_apply_apply]
    obtain ⟨μ, h | h⟩ := b.isNeighbour
    · exact ⟨μ, Or.inl (by rw [← map_sub, h, hs'])⟩
    · exact ⟨μ, Or.inr (by rw [← map_sub, h, map_neg, hs'])⟩⟩
  left_inv b := PeriodicLattice.Bond.ext (by simp) (by simp)
  right_inv b := PeriodicLattice.Bond.ext (by simp) (by simp)
def faceEquivOfVertexEquiv (s : PeriodicLattice.Site L m d ≃ PeriodicLattice.Site L m' d') :
    PeriodicLattice.Plaquette L m d ≃ PeriodicLattice.Plaquette L m' d' where
  toFun p := ⟨s p.origin, p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
  invFun p := ⟨s.symm p.origin, p.firstAxis, p.secondAxis, p.firstAxis_lt_secondAxis⟩
  left_inv p := PeriodicLattice.Plaquette.ext (by simp) rfl rfl
  right_inv p := PeriodicLattice.Plaquette.ext (by simp) rfl rfl
end EdgesOfVertices
theorem pow_mul_meshAt {L k j : ℕ} (hL : 0 < L) (hj : j ≤ k) (i : ℕ) :
    (L : ℝ) ^ (k - j) * meshAt L k i = meshAt L j i := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  rw [meshAt, meshAt, ← zpow_natCast, ← zpow_add₀ hL', Nat.cast_sub hj]
  congr 1
  ring
section PeriodicCase
variable {L n k j : ℕ}
abbrev scaledExponent (n k j : ℕ) : ℕ := n + (k - j)
theorem torusSide_ne_zero (hL : 0 < L) (m : ℕ) : PeriodicLattice.torusSide L m ≠ 0 := by
  have hL' : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
  simp [PeriodicLattice.torusSide, hL']
theorem torusSide_scaledExponent (L n k j : ℕ) :
    PeriodicLattice.torusSide L (scaledExponent n k j) =
      (L : ℝ) ^ (k - j) * PeriodicLattice.torusSide L n := by
  simp only [PeriodicLattice.torusSide, scaledExponent, pow_add]
  ring
def scaling (hL : 0 < L) (n k j : ℕ) :
    PeriodicLattice.FourTorus L n ≃+ PeriodicLattice.FourTorus L (scaledExponent n k j) :=
  AddEquiv.piCongrRight fun _ =>
    AddCircle.equivAddCircle _ _ (torusSide_ne_zero hL n) (torusSide_ne_zero hL _)
theorem scaling_apply (hL : 0 < L) (x : PeriodicLattice.FourTorus L n) (μ : Fin 4) (t : ℝ)
    (h : x μ = (t : AddCircle (PeriodicLattice.torusSide L n))) :
    scaling hL n k j x μ =
      (((L : ℝ) ^ (k - j) * t : ℝ) :
        AddCircle (PeriodicLattice.torusSide L (scaledExponent n k j))) := by
  have e : scaling hL n k j x μ = AddCircle.equivAddCircle _ _ (torusSide_ne_zero hL n)
      (torusSide_ne_zero hL (scaledExponent n k j)) (x μ) := rfl
  have hs := torusSide_ne_zero hL n
  rw [e, h, AddCircle.equivAddCircle_apply_mk, torusSide_scaledExponent]
  congr 1
  field_simp
theorem scaling_mk (hL : 0 < L) (x : Fin 4 → ℝ) :
    scaling hL n k j (fun μ => (x μ : AddCircle (PeriodicLattice.torusSide L n))) =
      fun μ => (((L : ℝ) ^ (k - j) * x μ : ℝ) :
        AddCircle (PeriodicLattice.torusSide L (scaledExponent n k j))) :=
  funext fun μ => scaling_apply hL _ μ (x μ) rfl
theorem scaling_pointOnAxis (hL : 0 < L) (μ : Fin 4) (t : ℝ) :
    scaling hL n k j (PeriodicLattice.pointOnAxis L n μ t) =
      PeriodicLattice.pointOnAxis L (scaledExponent n k j) μ ((L : ℝ) ^ (k - j) * t) := by
  funext ν
  by_cases h : ν = μ
  · subst h
    rw [scaling_apply hL _ ν t (by simp [PeriodicLattice.pointOnAxis])]
    simp [PeriodicLattice.pointOnAxis]
  · rw [scaling_apply hL _ ν 0 (by simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h])]
    simp [PeriodicLattice.pointOnAxis, Pi.single_eq_of_ne h]
theorem pow_mul_meshSize_levelDepth (hL : 0 < L) (hj : j ≤ k) (i : ℕ) :
    (L : ℝ) ^ (k - j) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k i) =
      PeriodicLattice.meshSize L (PeriodicLattice.levelDepth j i) := by
  rw [meshSize_levelDepth, meshSize_levelDepth, pow_mul_meshAt hL hj]
theorem scaling_gridPoint (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (a : Fin 4 → ℤ) :
    scaling hL n k j (fun μ =>
        (((a μ : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth k i) : ℝ) :
          AddCircle (PeriodicLattice.torusSide L n))) =
      fun μ => (((a μ : ℝ) * PeriodicLattice.meshSize L (PeriodicLattice.levelDepth j i) : ℝ) :
        AddCircle (PeriodicLattice.torusSide L (scaledExponent n k j))) := by
  funext μ
  rw [scaling_apply hL _ μ _ rfl, ← pow_mul_meshSize_levelDepth hL hj i]
  congr 1
  ring
def scaleVertex (hL : 0 < L) (hj : j ≤ k) (i : ℕ) :
    Vertex L n k i ≃+ Vertex L (scaledExponent n k j) j i where
  toFun x := ⟨scaling hL n k j x.1, by
    obtain ⟨a, ha⟩ := x.2
    have hx : (x.1 : PeriodicLattice.FourTorus L n) = _ := funext ha
    exact ⟨a, fun μ => by rw [hx, scaling_gridPoint hL hj i a]⟩⟩
  invFun y := ⟨(scaling hL n k j).symm y.1, by
    obtain ⟨a, ha⟩ := y.2
    refine ⟨a, fun μ => ?_⟩
    have hy : (y.1 : PeriodicLattice.FourTorus L (scaledExponent n k j)) = _ := funext ha
    rw [hy, ← scaling_gridPoint hL hj i a, AddEquiv.symm_apply_apply]⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
theorem coe_scaleVertex (hL : 0 < L) (hj : j ≤ k) {i : ℕ} (x : Vertex L n k i) :
    (scaleVertex hL hj i x : PeriodicLattice.FourTorus L (scaledExponent n k j)) =
      scaling hL n k j x := rfl
theorem scaleVertex_unitStep (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (μ : Fin 4) :
    scaleVertex hL hj i (PeriodicLattice.unitStep L n (PeriodicLattice.levelDepth k i) μ) =
      PeriodicLattice.unitStep L (scaledExponent n k j) (PeriodicLattice.levelDepth j i) μ :=
  Subtype.ext (by
    rw [coe_scaleVertex]
    simp only [PeriodicLattice.unitStep]
    rw [scaling_pointOnAxis, pow_mul_meshSize_levelDepth hL hj])
def scaleVertexPair (hL : 0 < L) (hj : j ≤ k) (i i' : ℕ) :
    Vertex L n k i × Vertex L n k i' ≃
      Vertex L (scaledExponent n k j) j i × Vertex L (scaledExponent n k j) j i' :=
  (scaleVertex hL hj i).toEquiv.prodCongr (scaleVertex hL hj i').toEquiv
def scaleEdge (hL : 0 < L) (hj : j ≤ k) (i : ℕ) :
    Edge L n k i ≃ Edge L (scaledExponent n k j) j i :=
  edgeEquivOfVertexEquiv (scaleVertex hL hj i) (scaleVertex_unitStep hL hj i)
def scaleFace (hL : 0 < L) (hj : j ≤ k) (i : ℕ) :
    Face L n k i ≃ Face L (scaledExponent n k j) j i :=
  faceEquivOfVertexEquiv (scaleVertex hL hj i).toEquiv
def scalePath (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (Γ : List (Edge L n k i)) :
    List (Edge L (scaledExponent n k j) j i) :=
  transportList (scaleEdge hL hj i) Γ
def scaleEdges (hL : 0 < L) (hj : j ≤ k) :
    (Σ i : Fin (j + 1), Edge L n k i) ≃ Σ i : Fin (j + 1), Edge L (scaledExponent n k j) j i :=
  Equiv.sigmaCongrRight fun i => scaleEdge hL hj i
def scaleFaces (hL : 0 < L) (hj : j ≤ k) :
    (Σ i : Fin (j + 1), Face L n k i) ≃
      Σ i : Fin (j + 1), Face L (scaledExponent n k j) j i :=
  Equiv.sigmaCongrRight fun i => scaleFace hL hj i
end PeriodicCase
namespace FullSpace
open InfiniteLattice (AmbientSpace)
section EdgesOfVertices
variable {a a' : ℝ}
def edgeEquivOfVertexEquiv
    (s : InfiniteLattice.LatticePoint a ≃+ InfiniteLattice.LatticePoint a')
    (hs : ∀ μ, s (InfiniteLattice.axisStep a μ) = InfiniteLattice.axisStep a' μ) :
    InfiniteLattice.Link a ≃ InfiniteLattice.Link a' where
  toFun b := ⟨s b.initial, s b.terminal, by
    obtain ⟨μ, h | h⟩ := b.isAdjacent
    · exact ⟨μ, Or.inl (by rw [← map_sub, h, hs])⟩
    · exact ⟨μ, Or.inr (by rw [← map_sub, h, map_neg, hs])⟩⟩
  invFun b := ⟨s.symm b.initial, s.symm b.terminal, by
    have hs' : ∀ μ, s.symm (InfiniteLattice.axisStep a' μ) = InfiniteLattice.axisStep a μ :=
      fun μ => by
        rw [← hs, s.symm_apply_apply]
    obtain ⟨μ, h | h⟩ := b.isAdjacent
    · exact ⟨μ, Or.inl (by rw [← map_sub, h, hs'])⟩
    · exact ⟨μ, Or.inr (by rw [← map_sub, h, map_neg, hs'])⟩⟩
  left_inv b := InfiniteLattice.Link.ext (by simp) (by simp)
  right_inv b := InfiniteLattice.Link.ext (by simp) (by simp)
def faceEquivOfVertexEquiv
    (s : InfiniteLattice.LatticePoint a ≃ InfiniteLattice.LatticePoint a') :
    InfiniteLattice.ElementaryPlaquette a ≃ InfiniteLattice.ElementaryPlaquette a' where
  toFun p := ⟨s p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
  invFun p := ⟨s.symm p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
  left_inv p := InfiniteLattice.ElementaryPlaquette.ext (by simp) rfl rfl
  right_inv p := InfiniteLattice.ElementaryPlaquette.ext (by simp) rfl rfl
end EdgesOfVertices
variable {L k j : ℕ}
def scaling (hL : 0 < L) (k j : ℕ) : AmbientSpace ≃+ AmbientSpace :=
  (LinearEquiv.smulOfNeZero ℝ AmbientSpace ((L : ℝ) ^ (k - j))
    (pow_ne_zero _ (by exact_mod_cast hL.ne'))).toAddEquiv
theorem scaling_apply (hL : 0 < L) (x : AmbientSpace) :
    scaling hL k j x = (L : ℝ) ^ (k - j) • x := rfl
def scaleVertex (hL : 0 < L) (hj : j ≤ k) (i : ℕ) : Vertex L k i ≃+ Vertex L j i where
  toFun x := ⟨scaling hL k j x.1, by
    obtain ⟨c, hc⟩ := x.2
    refine ⟨c, fun μ => ?_⟩
    rw [scaling_apply, Pi.smul_apply, hc μ, ← pow_mul_meshAt hL hj i, smul_eq_mul]
    ring⟩
  invFun y := ⟨(scaling hL k j).symm y.1, by
    obtain ⟨c, hc⟩ := y.2
    refine ⟨c, fun μ => ?_⟩
    have h : y.1 = scaling hL k j fun ν => (c ν : ℝ) * meshAt L k i := by
      funext ν
      rw [scaling_apply, Pi.smul_apply, hc ν, ← pow_mul_meshAt hL hj i, smul_eq_mul]
      ring
    rw [h, AddEquiv.symm_apply_apply]⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
theorem coe_scaleVertex (hL : 0 < L) (hj : j ≤ k) {i : ℕ} (x : Vertex L k i) :
    (scaleVertex hL hj i x : AmbientSpace) = scaling hL k j x := rfl
theorem scaleVertex_axisStep (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (μ : Fin 4) :
    scaleVertex hL hj i (InfiniteLattice.axisStep (meshAt L k i) μ) =
      InfiniteLattice.axisStep (meshAt L j i) μ :=
  Subtype.ext (by
    rw [coe_scaleVertex, scaling_apply]
    funext ν
    by_cases h : ν = μ
    · subst h
      simp [InfiniteLattice.axisStep, pow_mul_meshAt hL hj i]
    · simp [InfiniteLattice.axisStep, Pi.single_eq_of_ne h])
def scaleVertexPair (hL : 0 < L) (hj : j ≤ k) (i i' : ℕ) :
    Vertex L k i × Vertex L k i' ≃ Vertex L j i × Vertex L j i' :=
  (scaleVertex hL hj i).toEquiv.prodCongr (scaleVertex hL hj i').toEquiv
def scaleEdge (hL : 0 < L) (hj : j ≤ k) (i : ℕ) : Edge L k i ≃ Edge L j i :=
  edgeEquivOfVertexEquiv (scaleVertex hL hj i) (scaleVertex_axisStep hL hj i)
def scaleFace (hL : 0 < L) (hj : j ≤ k) (i : ℕ) : Face L k i ≃ Face L j i :=
  faceEquivOfVertexEquiv (scaleVertex hL hj i).toEquiv
def scalePath (hL : 0 < L) (hj : j ≤ k) (i : ℕ) (Γ : List (Edge L k i)) :
    List (Edge L j i) :=
  transportList (scaleEdge hL hj i) Γ
def scaleEdges (hL : 0 < L) (hj : j ≤ k) :
    (Σ i : Fin (j + 1), Edge L k i) ≃ Σ i : Fin (j + 1), Edge L j i :=
  Equiv.sigmaCongrRight fun i => scaleEdge hL hj i
def scaleFaces (hL : 0 < L) (hj : j ≤ k) :
    (Σ i : Fin (j + 1), Face L k i) ≃ Σ i : Fin (j + 1), Face L j i :=
  Equiv.sigmaCongrRight fun i => scaleFace hL hj i
end FullSpace
end Tower
end YangMills.Construction
