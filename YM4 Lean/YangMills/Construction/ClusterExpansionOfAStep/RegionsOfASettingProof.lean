import YangMills.Construction.ClusterExpansionOfAStep.AttachedClustersOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.PriceOfTheHotLumps
import YangMills.Construction.ClusterExpansionOfAStep.RegionsOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.TopFieldOffTheHull
import YangMills.Construction.ClusterExpansionOfAStep.TopFrameOfATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages LumpContours TopLevelSites TorusFields TorusLumps TorusShares TorusFrame TorusBalls
  StepSettings RenormalizationStepParameters StepMarks StepCosts ColdChain
namespace SettingRegionFacts
section OnTheTorus
variable {L t m : ℕ} [NeZero m]
theorem isLocallyOrthantClosed_of_torusFrame {X : Finset (TorusSite m)} {k : ℕ}
    (h : IsOrthantRegular (cellsOfSites (torusFrame L t m) X) k) :
    IsLocallyOrthantClosed X k := by
  intro z
  obtain ⟨eps, he, hX⟩ := h (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top z)
  refine ⟨eps, he, fun q hq hd v hv hb => ?_⟩
  have hq' : torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top q ∈ cellsOfSites (torusFrame L t m) X :=
    mem_cellsOfSites_torusFrame.mpr (by rw [siteOfCell_torusSiteInFrame]; exact hq)
  have hd' : cellSupDist (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top q)
      (torusSiteInFrame (torusFrame L t m) (torusFrame L t m).top z) ≤ k := by
    rw [cellSupDist_torusFrame, siteOfCell_torusSiteInFrame, siteOfCell_torusSiteInFrame]
    exact hd
  have := mem_cellsOfSites_torusFrame.mp (hX _ hq' hd' v hv hb)
  rwa [siteOfCell_add, siteOfCell_torusSiteInFrame, siteOfCell_siteOfCoords] at this
omit [NeZero m] in
theorem isLocallyOrthantClosed_mono {X : Finset (TorusSite m)} {k k' : ℕ} (hk : k' ≤ k)
    (h : IsLocallyOrthantClosed X k) : IsLocallyOrthantClosed X k' := by
  intro z
  obtain ⟨eps, he, hX⟩ := h z
  refine ⟨eps, he, fun q hq hd v hv hb => hX q hq (hd.trans hk) v hv fun i => (hb i).trans ?_⟩
  exact_mod_cast hk
end OnTheTorus
section FinerLevel
variable {n L : ℕ} [NeZero n] [NeZero L]
theorem mem_sitesInBlocks_iff (S : Finset (TorusSite n)) (x : TorusSite (n * L)) :
    x ∈ sitesInBlocks L S ↔ parentBlock L x ∈ S := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.mem_sitesInBlocks <;> assumption
omit [NeZero n] in
theorem parentBlock_add_siteOfInt (q : TorusSite (n * L)) (h : Fin 4 → ℤ) :
    parentBlock L (q + siteOfInt h) = parentBlock L q + siteOfInt fun i =>
      (((q i).cast : ℤ) + ((L : ℤ) - 1) / 2 + h i) / (L : ℤ) - (((q i).cast : ℤ) + ((L : ℤ) - 1) / 2) / (L : ℤ) := by
  have hL : (0 : ℤ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  funext i
  simp only [parentBlock, siteOfInt, Pi.add_apply]
  set A : ℤ := ((q i).cast : ℤ) + ((L : ℤ) - 1) / 2 with hA
  have hdv : ((n * L : ℕ) : ℤ) ∣ (((q i + (h i : ZMod (n * L))).cast : ℤ)) - (((q i).cast : ℤ) + h i) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    push_cast
    simp
  obtain ⟨k, hk⟩ := hdv
  have e1 : (((q i + (h i : ZMod (n * L))).cast : ℤ)) + ((L : ℤ) - 1) / 2 = (A + h i) + (L : ℤ) * ((n : ℤ) * k) := by
    push_cast at hk
    have : (((q i + (h i : ZMod (n * L))).cast : ℤ)) = ((q i).cast : ℤ) + h i + (n : ℤ) * L * k := by linarith
    rw [this, hA]
    ring
  rw [e1, Int.add_mul_ediv_left _ _ hL.ne']
  push_cast
  simp
theorem isLocallyOrthantClosed_sitesInBlocks {S : Finset (TorusSite n)} {k : ℕ} (hk : 2 ≤ k) (hL : 2 ≤ L)
    (h : IsLocallyOrthantClosed S k) : IsLocallyOrthantClosed (sitesInBlocks L S) k := by
  intro z
  obtain ⟨eps, he, hS⟩ := h (parentBlock L z)
  refine ⟨eps, he, fun q hq hd v hv hb => ?_⟩
  rw [mem_sitesInBlocks_iff, parentBlock_add_siteOfInt]
  have hLz : (0 : ℤ) < L := by exact_mod_cast (by omega : 0 < L)
  have hdiv : k / L + 1 ≤ k := by
    have : k / L ≤ k / 2 := Nat.div_le_div_left hL (by norm_num)
    omega
  have h1 : supDist (parentBlock L q) (parentBlock L z) ≤ k := by
    have := supDist_parentBlock_le_div_add_one (n := n) L q z
    have h2 : supDist q z / L ≤ k / L := Nat.div_le_div_right hd
    omega
  refine hS _ ((mem_sitesInBlocks_iff _ _).mp hq) h1 _ (fun i => ?_) (fun i => ?_)
  · set A : ℤ := ((q i).cast : ℤ) + ((L : ℤ) - 1) / 2 with hA
    rcases he i with e | e
    · rw [e, one_mul]
      have hvi : 0 ≤ v i := by simpa [e] using hv i
      have := Int.ediv_le_ediv hLz (by omega : A ≤ A + v i)
      omega
    · have hvi : v i ≤ 0 := by
        have := hv i
        rw [e] at this
        omega
      have := Int.ediv_le_ediv hLz (by omega : A + v i ≤ A)
      rw [e]
      omega
  · set A : ℤ := ((q i).cast : ℤ) + ((L : ℤ) - 1) / 2 with hA
    have h3 := natAbs_ediv_sub_ediv_add_le L (by omega) A (v i)
    have h4 : (v i).natAbs ≤ k := by
      have := hb i
      have h5 : |v i| = ((v i).natAbs : ℤ) := Int.abs_eq_natAbs _
      rw [h5] at this
      exact_mod_cast this
    have h6 : (v i).natAbs / L ≤ k / L := Nat.div_le_div_right h4
    have h7 : |(A + v i) / (L : ℤ) - A / (L : ℤ)| = ((A / (L : ℤ) - (A + v i) / (L : ℤ)).natAbs : ℤ) := by
      rw [abs_sub_comm]
      exact Int.abs_eq_natAbs _
    rw [h7]
    have : (A / (L : ℤ) - (A + v i) / (L : ℤ)).natAbs ≤ k := by omega
    exact_mod_cast this
end FinerLevel
variable {n : ℕ} [NeZero n]
section AtTheTop
variable {L t : ℕ} [NeZero L]
omit [NeZero n] [NeZero L] in
theorem period_depth_torusFrame (i : Fin 4) : (torusFrame L t n).period (torusFrame L t n).depth i = n * L := by
  rw [period_depth]
  rfl
theorem readAtLevel_minimizingField (a ρ : ℝ) (S : Finset (TorusSite n)) (V : TorusField n) :
    readAtLevel (torusFrame L t n) (torusFrame L t n).depth (minimizingField a ρ L t S V) =
      chartedField (minimizingCoordinates a (cellsOfSites (torusFrame L t n) S)
          (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) := by
  funext x i
  show minimizingField a ρ L t S V (toTorusSite (n * L) x) i = _
  unfold minimizingField
  rw [torusSiteInFrame_toTorusSite period_depth_torusFrame]
theorem minimizingCoordinates_spec {a δ lam ρ σA cg : ℝ} {N : ℕ → ℝ} {L t : ℕ} [NeZero L]
    (hch : ColdChainConstants a δ L lam ρ σA cg N) (hodd : Odd L) (hn : 64 ≤ n) {S : Finset (TorusSite n)}
    {V : TorusField n} {s₁ : ℝ} (hs : 0 < s₁) (hsσ : s₁ ≤ σA)
    (hreg : IsOrthantRegular (cellsOfSites (torusFrame L t n) S) 2047)
    (hcold : IsCold (cellsOfSites (torusFrame L t n) S) (torusFrame L t n).top s₁
      (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)) :
    IsMinimizingChart a (cellsOfSites (torusFrame L t n) S) (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)
        (min ρ (N 0 * s₁))
      (minimizingCoordinates a (cellsOfSites (torusFrame L t n) S)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ) ∧
    IsCold (cellsOfSites (torusFrame L t n) S) (torusFrame L t n).depth (s₁ / 8)
      (chartedField (minimizingCoordinates a (cellsOfSites (torusFrame L t n) S)
          (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V)) := by
  obtain ⟨-, -, -, hρ, hρ1, -, -, -, main⟩ := hch
  have hone := (main (torusFrame L t n) 2047 _ rfl (isAdmissibleAmbient_torusFrame hn) (by norm_num) hreg s₁ _ hs hsσ
    hcold).1
  have hπ : ρ < Real.pi := lt_of_le_of_lt hρ1 (by linarith [Real.pi_gt_three])
  obtain ⟨w, h1, h2, h3⟩ := minimizingCoordinates_eq (F := torusFrame L t n) hodd (fun _ => by
    show 2 ≤ n
    omega) hπ le_rfl hone
  rw [h3]
  exact ⟨h1, h2⟩
theorem isColdOn_minimizingField {a ρ : ℝ} {L t : ℕ} [NeZero L] (hodd : Odd L) (hn : 2 ≤ n)
    {S : Finset (TorusSite n)} {V : TorusField n} {q : ℝ}
    (hcold : IsCold (cellsOfSites (torusFrame L t n) S) (torusFrame L t n).depth q
      (chartedField (minimizingCoordinates a (cellsOfSites (torusFrame L t n) S)
          (readAtLevel (torusFrame L t n) (torusFrame L t n).top V) ρ)
        (readAtLevel (torusFrame L t n) (torusFrame L t n).top V))) :
    IsColdOn (sitesInBlocks L S) q (minimizingField a ρ L t S V) := by
  classical
  have hnn : ∀ i, (torusFrame L t n).extent i = n := fun _ => rfl
  have hNE : NeZero (n * (torusFrame L t n).blockSide) := inferInstanceAs (NeZero (n * L))
  have hNL : NeZero (torusFrame L t n).blockSide := inferInstanceAs (NeZero L)
  intro x μ ν hμν hall
  have e1 : curvature (minimizingField a ρ L t S V) x μ ν =
      plaquetteDefect (readAtLevel (torusFrame L t n) (torusFrame L t n).depth (minimizingField a ρ L t S V))
        (torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth x, μ, ν) := by
    rw [plaquetteDefect_readAtLevel_eq period_depth_torusFrame, toTorusSite_torusSiteInFrame period_depth_torusFrame]
  rw [e1, readAtLevel_minimizingField]
  refine hcold _ ?_
  have hsite : ∀ z ∈ plaquetteVertices x μ ν, torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth z ∈
      sitesOfCells (cellsOfSites (torusFrame L t n) S) (torusFrame L t n).depth := fun z hz =>
    torusSiteInFrame_mem_sitesOfCells hnn hodd hn z ((mem_sitesInBlocks_iff _ _).mp (hall z hz))
  have hunit : ∀ i, torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth (x + TorusFields.unitStep (n * L) i) =
      torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth x + BlockAverages.unitStep _ i := by
    intro i
    apply toTorusSite_injective period_depth_torusFrame
    rw [toTorusSite_torusSiteInFrame period_depth_torusFrame, toTorusSite_add period_depth_torusFrame,
      toTorusSite_torusSiteInFrame period_depth_torusFrame, toTorusSite_unitStep period_depth_torusFrame]
  refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hsite x (by simp [plaquetteVertices]), by simp⟩, hμν, ?_⟩
  intro u hu
  simp only [plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl | rfl | rfl
  · exact hsite x (by simp [plaquetteVertices])
  · rw [← hunit]
    exact hsite _ (by simp [plaquetteVertices])
  · rw [← hunit]
    exact hsite _ (by simp [plaquetteVertices])
  · have e2 : torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth
          (x + TorusFields.unitStep (n * L) μ + TorusFields.unitStep (n * L) ν) =
        torusSiteInFrame (torusFrame L t n) (torusFrame L t n).depth x + BlockAverages.unitStep _ μ +
          BlockAverages.unitStep _ ν := by
      apply toTorusSite_injective period_depth_torusFrame
      rw [toTorusSite_torusSiteInFrame period_depth_torusFrame, toTorusSite_add period_depth_torusFrame,
        toTorusSite_add period_depth_torusFrame, toTorusSite_torusSiteInFrame period_depth_torusFrame,
        toTorusSite_unitStep period_depth_torusFrame, toTorusSite_unitStep period_depth_torusFrame]
    rw [← e2]
    exact hsite _ (by simp [plaquetteVertices])
end AtTheTop
end SettingRegionFacts
open SettingRegionFacts in
theorem settingRegionsRegular_of_complement (hc : ComplementOfThickenedLumpsRegular) : SettingRegionsRegular := by
  intro T hT
  refine ⟨T.floorMin, fun y hy R hR n _ hn s hs => ?_⟩
  have hfit : R.params.Admissible := by
    rw [hR.params_eq]
    exact hT.fits y hy
  have hLe : R.params.side = T.side := by rw [hR.params_eq]; rfl
  have haR : R.params.coupling = T.coupling := by rw [hR.params_eq]; rfl
  have hσe : R.params.threshold = T.threshold := by rw [hR.params_eq]; rfl
  have hn₀e : R.params.n₀ = T.n₀ := by rw [hR.params_eq]; rfl
  have hchain : ColdChainConstants R.params.coupling T.δ₁ R.params.side T.lam R.anchorRadius T.σA T.cg T.N := by
    rw [haR, hLe, hR.anchorRadius_eq]
    exact hT.chain
  have hσ0 : 0 < T.threshold := hT.σ_pos
  have hσA : 2 * T.threshold ≤ T.σA := hT.σ_le
  have hodd : Odd R.params.side := hfit.L_odd
  have hL2 : 2 ≤ R.params.side := by
    have := hfit.L_ge
    omega
  have key : ∀ (C : Finset (TorusSite n)) (s₂ : ℝ),
      IsStepSituation R.params (clusterRange R.nextCoupling) s.coarse s.region C s₂ →
      IsColdOn s.region (9 / 8 * T.threshold) s.coarse →
      IsLocallyOrthantClosed s.region 1024 ∧ IsColdOn s.region (9 / 8 * T.threshold) s.coarse ∧
      IsLocallyOrthantClosed (sitesInBlocks R.params.side s.region) 1024 ∧
      IsColdOn (sitesInBlocks R.params.side s.region) (9 / 8 * T.threshold)
        (minimizingField R.params.coupling R.anchorRadius R.params.side R.depth s.region s.coarse) := by
    intro C s₂ hsit hcoldS
    obtain ⟨hs0, hs2, h4096, hall⟩ := stepSituation_regular_and_cold hc hfit hsit
    obtain ⟨hreg, hcold⟩ := hall (torusFrame R.params.side R.depth n) (fun _ => rfl)
    have hrS : IsLocallyOrthantClosed s.region 1024 :=
      isLocallyOrthantClosed_mono (by norm_num) (isLocallyOrthantClosed_of_torusFrame hreg)
    have hs2' : s₂ ≤ 2 * T.threshold := by rw [← hσe]; exact hs2
    have hch := (minimizingCoordinates_spec (t := R.depth) hchain hodd (by omega) hs0 (hs2'.trans hσA) hreg hcold).2
    have hcl := isColdOn_minimizingField (a := R.params.coupling) (ρ := R.anchorRadius) (t := R.depth) hodd
      (by omega) hch
    refine ⟨hrS, hcoldS, isLocallyOrthantClosed_sitesInBlocks (by norm_num) hL2 hrS, fun x μ ν hμν hcor => ?_⟩
    have := hcl x μ ν hμν hcor
    nlinarith
  have hwhole : ∀ W : TorusField (n * R.params.side),
      IsLocallyOrthantClosed (Finset.univ \ thickening lumpRange (torusHotSites R.params W)) 1024 := by
    intro W
    have hLn : R.params.side ∣ n * R.params.side := Dvd.intro_left _ rfl
    have h1 := isOrthantRegular_cellsOfSites_compl_thickening (F := torusFrame R.params.side 0 (n * R.params.side))
      (n := n * R.params.side) hc hfit hLn (fun _ => rfl) W
    exact isLocallyOrthantClosed_mono (by norm_num) (isLocallyOrthantClosed_of_torusFrame h1)
  rcases hs.region_spec with ⟨htop, hcold⟩ | ⟨hblk, htop, -⟩
  · obtain ⟨a, b, c, d⟩ := key ∅ (9 / 8 * R.params.threshold) (Or.inr ⟨by omega, hcold, htop, rfl, rfl⟩) (by
      intro x μ ν hμν _
      have := hcold x μ ν hμν
      rwa [hσe] at this)
    exact ⟨a, b, c, d, hwhole⟩
  · obtain ⟨a, b, c, d⟩ := key (minimalHull R.params (clusterRange R.nextCoupling) s.coarse) R.params.threshold
      (Or.inl ⟨hblk, htop, rfl, rfl⟩) (by
      intro x μ ν hμν hcor
      by_contra hlt
      have h1 : T.threshold ≤ curvature s.coarse x μ ν := by
        have := not_lt.mp hlt
        linarith
      have h2 := mem_torusHotSites_of_mem_plaquetteVertices hfit hblk.1 hμν (by rw [hσe]; exact h1)
        (base_mem_plaquetteVertices x μ ν)
      have h3 := hcor x (base_mem_plaquetteVertices x μ ν)
      rw [htop] at h3
      exact (Finset.mem_sdiff.mp h3).2
        ((mem_thickening _ _ _).mpr ⟨x, h2, by rw [supDist_self]; exact Nat.zero_le _⟩))
    exact ⟨a, b, c, d, hwhole⟩
end YangMills.Construction.ClusterExpansionOfAStep
end
