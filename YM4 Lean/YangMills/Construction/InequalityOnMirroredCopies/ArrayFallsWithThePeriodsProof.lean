import YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivityProof
import YangMills.Construction.InequalityOnMirroredCopies.ArrayFallsWithThePeriods
import YangMills.Construction.InequalityOnMirroredCopies.SimilarityCarriesTheArray
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies
open YangMills.Construction.ChessboardTori
namespace TiledIntegralFalls
private theorem indexVector_ext {u v : EvenIndexVector} (h : u.coord = v.coord) : u = v := by apply _root_.YangMills.Construction.ChessboardTori.ChessboardEstimateAndSubadditivity.evenIndexVector_ext <;> assumption
private def halfCoord (u : EvenIndexVector) (μ : Fin 4) : ℕ := (u.coord μ / 2).toNat
private theorem two_mul_halfCoord (u : EvenIndexVector) (μ : Fin 4) :
    2 * (halfCoord u μ : ℤ) = u.coord μ := by
  obtain ⟨r, hr⟩ := u.even μ
  have h2 := u.two_le μ
  have hdiv : u.coord μ / 2 = r := by omega
  unfold halfCoord
  rw [hdiv, Int.toNat_of_nonneg (by omega)]
  omega
private theorem one_le_halfCoord (u : EvenIndexVector) (μ : Fin 4) : 1 ≤ halfCoord u μ := by
  have h := two_mul_halfCoord u μ
  have h2 := u.two_le μ
  omega
private theorem stretch_setTwo (u : EvenIndexVector) (μ : Fin 4) :
    (setTwo u μ).stretch μ (one_le_halfCoord u μ) = u := by
  apply indexVector_ext
  funext κ
  by_cases h : κ = μ
  · subst h
    simp only [EvenIndexVector.stretch, scaleCoord, setTwo, Function.update_self]
    have := two_mul_halfCoord u κ
    linarith
  · simp [EvenIndexVector.stretch, scaleCoord, setTwo, Function.update_of_ne h]
private theorem eq_minimalCounts {D : ChessboardSetup} (u : EvenIndexVector)
    (h : ∀ κ, u.coord κ = 2) : u = minimalCounts D := by
  apply indexVector_ext
  funext κ
  simp [h κ, minimalCounts, cubicCounts]
private theorem cellCount_eq_prod (u : EvenIndexVector) :
    cellCount u = ∏ κ, (u.coord κ).toNat := by
  simp [cellCount, EvenIndexVector.indexBox, Fintype.card_piFinset]
private theorem toNat_coord (u : EvenIndexVector) (κ : Fin 4) :
    (u.coord κ).toNat = 2 * halfCoord u κ := by
  have := two_mul_halfCoord u κ
  omega
private theorem cellCount_div_sixteen (u : EvenIndexVector) :
    cellCount u / 16 = halfCoord u 0 * halfCoord u 1 * halfCoord u 2 * halfCoord u 3 := by
  rw [cellCount_eq_prod, Fin.prod_univ_four, toNat_coord u 0, toNat_coord u 1, toNat_coord u 2,
    toNat_coord u 3]
  have : 2 * halfCoord u 0 * (2 * halfCoord u 1) * (2 * halfCoord u 2) * (2 * halfCoord u 3) =
      16 * (halfCoord u 0 * halfCoord u 1 * halfCoord u 2 * halfCoord u 3) := by ring
  rw [this]
  exact Nat.mul_div_cancel_left _ (by norm_num)
private theorem bounds_of_stretchStep {D : ChessboardSetup} (z : EvenIndexVector → ℂ)
    (step : ∀ (u : EvenIndexVector) (μ : Fin 4), (z u).im = 0 ∧ 0 ≤ (z u).re ∧
      (z u).re ≤ (z (setTwo u μ)).re ^ halfCoord u μ) (u : EvenIndexVector) :
    (z u).im = 0 ∧ 0 ≤ (z u).re ∧
      (∀ μ : Fin 4, (z u).re ≤ (z (setTwo u μ)).re ^ (u.coord μ / 2).toNat) ∧
      (z u).re ≤ (z (minimalCounts D)).re ^ (cellCount u / 16) := by
  refine ⟨(step u 0).1, (step u 0).2.1, fun μ => (step u μ).2.2, ?_⟩
  set u₁ := setTwo u 0 with hu₁
  set u₂ := setTwo u₁ 1 with hu₂
  set u₃ := setTwo u₂ 2 with hu₃
  set u₄ := setTwo u₃ 3 with hu₄
  have hlast : u₄ = minimalCounts D := by
    apply eq_minimalCounts
    intro κ
    fin_cases κ <;> simp [hu₄, hu₃, hu₂, hu₁, setTwo, Function.update]
  have e₁ : halfCoord u₁ 1 = halfCoord u 1 := by simp [halfCoord, hu₁, setTwo, Function.update]
  have e₂ : halfCoord u₂ 2 = halfCoord u 2 := by
    simp [halfCoord, hu₂, hu₁, setTwo, Function.update]
  have e₃ : halfCoord u₃ 3 = halfCoord u 3 := by
    simp [halfCoord, hu₃, hu₂, hu₁, setTwo, Function.update]
  have s₀ := (step u 0).2.2
  have s₁ := (step u₁ 1).2.2
  have s₂ := (step u₂ 2).2.2
  have s₃ := (step u₃ 3).2.2
  rw [← hu₁] at s₀
  rw [← hu₂, e₁] at s₁
  rw [← hu₃, e₂] at s₂
  rw [← hu₄, e₃, hlast] at s₃
  have p₁ := (step u₁ 1).2.1
  have p₂ := (step u₂ 2).2.1
  have p₃ := (step u₃ 3).2.1
  rw [cellCount_div_sixteen]
  calc (z u).re ≤ (z u₁).re ^ halfCoord u 0 := s₀
    _ ≤ ((z u₂).re ^ halfCoord u 1) ^ halfCoord u 0 := pow_le_pow_left₀ p₁ s₁ _
    _ ≤ (((z u₃).re ^ halfCoord u 2) ^ halfCoord u 1) ^ halfCoord u 0 :=
        pow_le_pow_left₀ (pow_nonneg p₂ _) (pow_le_pow_left₀ p₂ s₂ _) _
    _ ≤ ((((z (minimalCounts D)).re ^ halfCoord u 3) ^ halfCoord u 2) ^ halfCoord u 1) ^
          halfCoord u 0 :=
        pow_le_pow_left₀ (pow_nonneg (pow_nonneg p₃ _) _)
          (pow_le_pow_left₀ (pow_nonneg p₃ _) (pow_le_pow_left₀ p₃ s₃ _) _) _
    _ = (z (minimalCounts D)).re ^
          (halfCoord u 0 * halfCoord u 1 * halfCoord u 2 * halfCoord u 3) := by
        simp only [← pow_mul]
        congr 1
        ring
private theorem stretchStep_of_coarse (hl : TorusStretchBound.Statement) {D : ChessboardSetup}
    (g : ReflectionGrid D) (hg : g.IsCoarse) {S : Set InfiniteLattice.AmbientSpace}
    (hS : S ∈ g.cellSet) {F : D.GaugeField → ℂ}
    (hF : F ∈ ReflectionGrid.cellObservables (D := D) S) (u : EvenIndexVector) (μ : Fin 4) :
    (tiledIntegral g u S F).im = 0 ∧ 0 ≤ (tiledIntegral g u S F).re ∧
      (tiledIntegral g u S F).re ≤ (tiledIntegral g (setTwo u μ) S F).re ^ halfCoord u μ := by
  have h := (hl ⟨D, g, hg⟩ (setTwo u μ) μ (halfCoord u μ) (one_le_halfCoord u μ)).2 S hS F hF
  rw [stretch_setTwo] at h
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩
end TiledIntegralFalls
open TiledIntegralFalls in
theorem tiledIntegralFallsWithPeriods_of_stretch (hl : TorusStretchBound.Statement)
    (hs : SimilarityPreservesTiledIntegral) : TiledIntegralFallsWithPeriods := by
  intro D g hside S hS F hF u
  by_cases hq : g.q < 0
  · obtain ⟨D', g', -, -, hg', -, -, hcells⟩ := hs D g hside hq
    obtain ⟨S', hS', Φ, hΦ⟩ := hcells S hS
    obtain ⟨hΦF, hkeep⟩ := hΦ F hF
    have hmin : minimalCounts D = minimalCounts D' := eq_minimalCounts _ (by
      intro κ
      simp [minimalCounts, cubicCounts])
    have key := bounds_of_stretchStep (D := D') (fun v => tiledIntegral g' v S' (Φ F))
      (fun v μ => stretchStep_of_coarse hl g' hg' hS' hΦF v μ) u
    simp only [hkeep, hmin]
    simpa only [← hkeep] using key
  · exact bounds_of_stretchStep (D := D) (fun v => tiledIntegral g v S F)
      (fun v μ => stretchStep_of_coarse hl g (not_lt.mp hq) hS hF v μ) u
end YangMills.Construction.ReflectedCopies
end
