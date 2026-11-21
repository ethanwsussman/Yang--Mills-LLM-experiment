import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.HullsOfHotLumps
import YangMills.Construction.ClusterExpansionOfAStep.SitesOfTheTopOfAStep
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section
namespace YangMills.Construction.StepSettings
open BlockAverages LumpContours TorusFields TorusLumps TopLevelSites StepCosts
variable {m : ℕ} [NeZero m]
theorem mem_hotLumpsOn_iff (p : StepParameters) (hp : p.Admissible) (hdvd : p.side ∣ m)
    (S : Finset (TorusSite m)) (W : TorusField m) (l : Finset (TorusSite m)) :
    l ∈ hotLumpsOn p S W ↔ ∃ x μ ν, μ < ν ∧ p.threshold ≤ curvature W x μ ν ∧
      (∀ z ∈ plaquetteVertices x μ ν, z ∈ S) ∧
      ∃ z ∈ plaquetteVertices x μ ν, l = torusLumpOf p z := by
  classical
  have hper : ∀ i, (stepBlockFrame p.side (m / p.side)).period 0 i = m := period_stepBlockFrame hdvd
  unfold hotLumpsOn hotLumps
  simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_filter]
  constructor
  · rintro ⟨l₀, ⟨⟨x, μ, ν⟩, ⟨hmem, hcurv⟩, hl⟩, rfl⟩
    obtain ⟨z₀, hz₀, rfl⟩ := hl
    have hlt : μ < ν := (Finset.mem_filter.mp hmem).2.1
    have hcorners := (Finset.mem_filter.mp hmem).2.2
    refine ⟨toTorusSite m x, μ, ν, hlt, ?_, ?_, toTorusSite m z₀,
      (mem_plaquetteVertices_iff hdvd x μ ν _).mpr ⟨z₀, hz₀, rfl⟩, ?_⟩
    · rw [← plaquetteDefect_readAtLevel hdvd]
      exact hcurv
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := (mem_plaquetteVertices_iff hdvd x μ ν _).mp hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hcorners hy)
      rw [toTorusSite_torusSiteInFrame hper]
      exact hw
    · exact image_lumpOf hp hdvd z₀
  · rintro ⟨x', μ, ν, hlt, hcurv, hS, z', hz', rfl⟩
    obtain ⟨x, rfl⟩ := toTorusSite_surjective (ℓ := p) hdvd x'
    obtain ⟨z₀, hz₀, rfl⟩ := (mem_plaquetteVertices_iff hdvd x μ ν _).mp hz'
    have hin : ∀ y ∈ plaquetteCorners ((x, μ, ν) : (stepBlockFrame p.side (m / p.side)).Site 0 × Fin 4 × Fin 4),
        y ∈ S.image (torusSiteInFrame (stepBlockFrame p.side (m / p.side)) 0) := by
      intro y hy
      refine Finset.mem_image.mpr ⟨toTorusSite m y,
        hS _ ((mem_plaquetteVertices_iff hdvd x μ ν _).mpr ⟨y, hy, rfl⟩), ?_⟩
      exact torusSiteInFrame_toTorusSite hper y
    refine ⟨lumpOf p.grid z₀, ⟨(x, μ, ν), ⟨?_, ?_⟩, z₀, hz₀, rfl⟩, image_lumpOf hp hdvd z₀⟩
    · unfold cutPlaquettes
      refine Finset.mem_filter.mpr ⟨?_, hlt, fun y hy => hin y hy⟩
      have hx : x ∈ plaquetteCorners ((x, μ, ν) : (stepBlockFrame p.side (m / p.side)).Site 0 × Fin 4 × Fin 4) := by
        simp [plaquetteCorners]
      simp [hin x hx]
    · rw [plaquetteDefect_readAtLevel hdvd]
      exact hcurv
variable {p : StepParameters}
theorem hotLumpsOn_subset_torusHotLumps (hp : p.Admissible) (hdvd : p.side ∣ m)
    (S : Finset (TorusSite m)) (W : TorusField m) :
    hotLumpsOn p S W ⊆ torusHotLumps p W := by
  intro l hl
  obtain ⟨x, μ, ν, h1, h2, -, z, hz, rfl⟩ := (mem_hotLumpsOn_iff p hp hdvd S W l).mp hl
  exact (mem_torusHotLumps_iff p hp hdvd W _).mpr ⟨x, μ, ν, h1, h2, z, hz, rfl⟩
theorem mem_hotLumpsOn_of_mem_chainComponents (hp : p.Admissible) (hdvd : p.side ∣ m) {r : ℕ}
    (hr : 2 ^ 16 ≤ r) {Y X : Finset (TorusSite m)} {W : TorusField m}
    (hsub : thickening (2 * r) (torusHotSites p W) ⊆ Y) (hX : X ∈ chainComponents r Y)
    {l : Finset (TorusSite m)} (hl : l ∈ torusHotLumps p W)
    {x : TorusSite m} (hxl : x ∈ l) (hxX : x ∈ X) : l ∈ hotLumpsOn p X W := by
  classical
  obtain ⟨x₀, μ, ν, h1, h2, z, hz, rfl⟩ := (mem_torusHotLumps_iff p hp hdvd W _).mp hl
  have hzl : z ∈ torusLumpOf p z := mem_torusLumpOf_self z
  refine (mem_hotLumpsOn_iff p hp hdvd X W _).mpr ⟨x₀, μ, ν, h1, h2, fun w hw => ?_, z, hz, rfl⟩
  have hin := thickening_subset_of_mem_chainComponents hp hdvd hr hsub hX hl hxl hxX
  refine hin ((mem_thickening _ _ _).mpr ⟨z, hzl, ?_⟩)
  have := supDist_le_four_of_mem_plaquetteVertices (x₀, μ, ν) hw hz
  omega
theorem mem_hotNeighbourhoodOn_iff (R : StepSetup) {n : ℕ} [NeZero n] (hp : R.params.Admissible)
    (hdvd : R.params.side ∣ n) (hr : 2 ^ 16 ≤ R.nextRange)
    {Y X : Finset (TorusSite n)} {V : TorusField n}
    (hsub : thickening (2 * R.nextRange) (torusHotSites R.params V) ⊆ Y)
    (hX : X ∈ chainComponents R.nextRange Y) {z : TorusSite n} (hz : z ∈ X) :
    z ∈ hotNeighbourhoodOn R X V ↔ z ∈ hotCoreSites R V := by
  classical
  constructor
  · intro h
    obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp h
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hx
    exact (mem_thickening _ _ _).mpr
      ⟨x, (show x ∈ (torusHotLumps R.params V).biUnion id from
        Finset.mem_biUnion.mpr ⟨l, hotLumpsOn_subset_torusHotLumps hp hdvd X V hl, hxl⟩), hzx⟩
  · intro h
    obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp h
    have hx' : x ∈ (torusHotLumps R.params V).biUnion id := hx
    obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hx'
    have hxY : x ∈ Y := hsub ((mem_thickening _ _ _).mpr ⟨x, hx, by rw [supDist_self]; omega⟩)
    have hxX : x ∈ X := mem_of_chainConnected_of_mem_chainComponents hX hz hxY
      (chainConnected_symm (chainConnected_of_supDist_le_two_mul hsub hx hzx))
    exact (mem_thickening _ _ _).mpr ⟨x, Finset.mem_biUnion.mpr
      ⟨l, mem_hotLumpsOn_of_mem_chainComponents hp hdvd hr hsub hX hl hxl hxX, hxl⟩, hzx⟩
theorem hotNeighbourhoodOn_subset (R : StepSetup) {n : ℕ} [NeZero n] (hp : R.params.Admissible)
    (hdvd : R.params.side ∣ n) (hr : 2 ^ 16 ≤ R.nextRange)
    {Y X : Finset (TorusSite n)} {V : TorusField n}
    (hsub : thickening (2 * R.nextRange) (torusHotSites R.params V) ⊆ Y)
    (hX : X ∈ chainComponents R.nextRange Y) : hotNeighbourhoodOn R X V ⊆ X := by
  classical
  intro z h
  obtain ⟨x, hx, hzx⟩ := (mem_thickening _ _ _).mp h
  obtain ⟨l, hl, hxl⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨x₀, μ, ν, h1, h2, hS, c, hc, rfl⟩ := (mem_hotLumpsOn_iff R.params hp hdvd X V l).mp hl
  have hhot : torusLumpOf R.params c ∈ torusHotLumps R.params V :=
    hotLumpsOn_subset_torusHotLumps hp hdvd X V hl
  have hcX : c ∈ X := hS c hc
  exact thickening_subset_of_mem_chainComponents hp hdvd hr hsub hX hhot (mem_torusLumpOf_self c) hcX
    ((mem_thickening _ _ _).mpr ⟨x, hxl, hzx⟩)
end YangMills.Construction.StepSettings
end
