import YangMills.Construction.ColdChainAtEveryLevel.PathsOnTheLattice
import YangMills.Construction.ColdChainAtEveryLevel.PowerWeightsThroughTheKernelProof
import YangMills.Construction.LawInAState.SumsOverTheBondsOfALattice
import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormOfTheCubeProof
import YangMills.Construction.RunningCouplingSlope.CompositionKeepsTheCoefficientProof
import YangMills.Construction.FormsOnATorus.ActionOnTwoToriProof
import YangMills.Construction.FormsOnATorus.LimitFormIsASumOfShares
import YangMills.Construction.FormsOnATorus.SharesOnTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped Quaternion
namespace YangMills.Construction.LimitForms
open YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.LevelAction YangMills.Construction.BlockAverages
section SiteCoordinates
variable {n : ℕ} [NeZero n]
private theorem valMinAbs_intCast_of_two_mul_abs_lt {u : ℤ} (h : 2 * |u| < (n : ℤ)) :
    ((u : ZMod n)).valMinAbs = u := by apply _root_.YangMills.SharedProofs.p9640 <;> assumption
private def centered (x : TorusSite n) : Fin 4 → ℤ := fun i => (x i).valMinAbs
private theorem siteOfInt_centered (x : TorusSite n) : siteOfInt (centered x) = x := by apply _root_.YangMills.Construction.SlopeCoefficient.Pullback.siteOfInt_minimalCoords <;> assumption
private theorem centered_siteOfInt {u : Fin 4 → ℤ} {p : ℕ} (hu : OffsetInBox p u) (hp : 2 * p < n) :
    centered (siteOfInt u : TorusSite n) = u := by apply _root_.YangMills.DeltaSharedProofs.p501837 <;> assumption
private theorem add_siteOfInt_mem_supBall (o : TorusSite n) {u : Fin 4 → ℤ} {r : ℕ} (hu : OffsetInBox r u) :
    o + siteOfInt u ∈ ResponseInTheExpansion.supBall o (r : ℝ) := by apply _root_.YangMills.SharedProofs.p7847 <;> assumption
private theorem supBall_isRegularRegion (o : TorusSite n) {r : ℕ} (hr : 2048 ≤ r) (hn : 4 * r < n) :
    IsRegularRegion (ResponseInTheExpansion.supBall o (r : ℝ)) 1024 := by apply _root_.YangMills.SharedProofs.p31712 <;> assumption
private theorem univ_isRegularRegion : IsRegularRegion (Finset.univ : Finset (TorusSite n)) 1024 :=
  fun _ => ⟨fun _ => 1, fun _ => Or.inl rfl, fun _ _ _ _ _ _ => Finset.mem_univ _⟩
private theorem exists_offsetInBox (u : Fin 4 → ℤ) : ∃ f : ℕ, OffsetInBox f u := by apply _root_.YangMills.SharedProofs.p5953 <;> assumption
private theorem offsetInBox_mono {e : Fin 4 → ℤ} {p p' : ℕ} (hp : p ≤ p') (he : OffsetInBox p e) :
    OffsetInBox p' e :=
  fun i => (he i).trans (by exact_mod_cast hp)
end SiteCoordinates
section Entries
private def offDiagEntry (a : ℝ) (L k : ℕ) {n : ℕ} [NeZero n] (o : TorusSite n) (X : Finset (TorusSite n))
    (b b' : IntBond) : ℝ :=
  mixedDeriv (actionAtLevel a L k X) (trivialField n) ![bondFrom o b, bondFrom o b']
    ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI]
private theorem areUnitVectors_imaginaryUnitI_pair :
    AreUnitVectors ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI] := by apply _root_.YangMills.SharedProofs.p1192 <;> assumption
private def TwoTorusBound (a δ : ℝ) (L : ℕ) (C : ℝ) : Prop :=
  ∀ (t n n' : ℕ) [NeZero n] [NeZero n'] (X : Finset (TorusSite n)) (X' : Finset (TorusSite n'))
    (z : TorusSite n) (z' : TorusSite n') (m r : ℕ), 64 ≤ n → 64 ≤ n' → IsRegularRegion X 1024 →
    IsRegularRegion X' 1024 → 4 * m + 2 < n → 4 * m + 2 < n' → 4 * r + 4 ≤ m →
    (∀ h, OffsetInBox (2 * m) h → (z + siteOfInt h ∈ X ↔ z' + siteOfInt h ∈ X')) →
    ∀ (k : ℕ) (c : Fin k → (Fin 4 → ℤ) × Fin 4) (Xs : Fin k → imaginaryQuaternions), 1 ≤ k → k ≤ 2 →
      AreUnitVectors Xs → (∀ l, OffsetInBox r (c l).1) →
      |mixedDeriv (actionAtLevel a L t X) (trivialField n) (fun l => bondFrom z (c l)) Xs -
          mixedDeriv (actionAtLevel a L t X') (trivialField n') (fun l => bondFrom z' (c l)) Xs| ≤
        C * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8)
private theorem offDiagEntry_sub_le {a δ C : ℝ} {L : ℕ} (hB : TwoTorusBound a δ L C) (k : ℕ) {n n' : ℕ}
    [NeZero n] [NeZero n'] (o : TorusSite n) (o' : TorusSite n') (X : Finset (TorusSite n))
    (X' : Finset (TorusSite n')) (e : Fin 4 → ℤ) (m f : ℕ) (b b' : IntBond) (hn : 64 ≤ n) (hn' : 64 ≤ n')
    (hX : IsRegularRegion X 1024) (hX' : IsRegularRegion X' 1024)
    (hm : 4 * m + 2 < n) (hm' : 4 * m + 2 < n') (hf : 4 * f + 4 ≤ m)
    (hag : ∀ h, OffsetInBox (2 * m) h →
      (o + siteOfInt e + siteOfInt h ∈ X ↔ o' + siteOfInt e + siteOfInt h ∈ X'))
    (hb : OffsetInBox f (b.1 - e)) (hb' : OffsetInBox f (b'.1 - e)) :
    |offDiagEntry a L k o X b b' - offDiagEntry a L k o' X' b b'| ≤
      C * ((m : ℝ) + 1) ^ 4 * Real.exp (-δ * m / 8) := by
  have key := hB k n n' X X' (o + siteOfInt e) (o' + siteOfInt e) m f hn hn' hX hX' hm hm' hf hag 2
    ![(b.1 - e, b.2), (b'.1 - e, b'.2)] ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI]
    (by norm_num) (by norm_num) areUnitVectors_imaginaryUnitI_pair (by
      intro l
      fin_cases l
      · exact hb
      · exact hb')
  have hfun : ∀ (p : ℕ) [NeZero p] (w : TorusSite p),
      (fun l => bondFrom (w + siteOfInt e) ((![(b.1 - e, b.2), (b'.1 - e, b'.2)] :
        Fin 2 → (Fin 4 → ℤ) × Fin 4) l)) = ![bondFrom w b, bondFrom w b'] := by
    intro p _ w
    funext l
    fin_cases l
    · show (w + siteOfInt e + siteOfInt (b.1 - e), b.2) = (w + siteOfInt b.1, b.2)
      rw [add_assoc, ← siteOfInt_add, add_sub_cancel]
    · show (w + siteOfInt e + siteOfInt (b'.1 - e), b'.2) = (w + siteOfInt b'.1, b'.2)
      rw [add_assoc, ← siteOfInt_add, add_sub_cancel]
  rw [hfun, hfun] at key
  exact key
private theorem tendsto_poly_mul_exp (C β : ℝ) (hβ : 0 < β) :
    Tendsto (fun m : ℕ => C * ((m : ℝ) + 1) ^ 4 * Real.exp (-β * m)) atTop (𝓝 0) := by apply _root_.YangMills.SharedProofs.p40441 <;> assumption
private theorem exists_poly_mul_exp_lt (C β : ℝ) (hβ : 0 < β) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m, M ≤ m → C * ((m : ℝ) + 1) ^ 4 * Real.exp (-β * m) < ε := by apply _root_.YangMills.SharedProofs.p56559 <;> assumption
private instance cubeSide_neZero (N : ℕ) : NeZero (16 * (N + 1)) := ⟨by omega⟩
private theorem cubeEntry_eq (a : ℝ) (L k N : ℕ) (b b' : IntBond) :
    cubeEntry a L k N b b' =
      offDiagEntry a L k (0 : TorusSite (16 * (N + 1))) (ResponseInTheExpansion.supBall 0 (N : ℝ)) b b' := rfl
private theorem cube_isRegularRegion {N : ℕ} (hN : 2048 ≤ N) :
    IsRegularRegion (ResponseInTheExpansion.supBall (0 : TorusSite (16 * (N + 1))) (N : ℝ)) 1024 :=
  supBall_isRegularRegion 0 hN (by omega)
private theorem add_siteOfInt_zero_add {p : ℕ} (w : TorusSite p) (h : Fin 4 → ℤ) :
    w + siteOfInt (0 : Fin 4 → ℤ) + siteOfInt h = w + siteOfInt h := by
  funext i
  simp [siteOfInt]
private theorem tendsto_offDiagEntry_univ {a δ C : ℝ} {L : ℕ} (hδ : 0 < δ) (hB : TwoTorusBound a δ L C) (k : ℕ)
    {b b' : IntBond} {q : ℝ} (hq : Tendsto (fun N => cubeEntry a L k N b b') atTop (𝓝 q)) :
    Tendsto (fun N => offDiagEntry a L k (0 : TorusSite (16 * (N + 1))) Finset.univ b b') atTop (𝓝 q) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨f₁, h₁⟩ := exists_offsetInBox b.1
  obtain ⟨f₂, h₂⟩ := exists_offsetInBox b'.1
  obtain ⟨M, hM⟩ := exists_poly_mul_exp_lt C (δ / 8) (by linarith) (half_pos hε)
  obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hq (ε / 2) (half_pos hε)
  obtain ⟨m, hm⟩ : ∃ m, m = M + 4 * (f₁ + f₂) + 4 := ⟨_, rfl⟩
  refine ⟨N₁ + 2 * m + 2048, fun N hN => ?_⟩
  have h1 := hN₁ N (by omega)
  rw [cubeEntry_eq] at h1
  have hc := offDiagEntry_sub_le hB k (0 : TorusSite (16 * (N + 1))) (0 : TorusSite (16 * (N + 1)))
    (ResponseInTheExpansion.supBall 0 (N : ℝ)) Finset.univ 0 m (f₁ + f₂) b b' (by omega) (by omega)
    (cube_isRegularRegion (by omega)) univ_isRegularRegion
    (by omega) (by omega) (by omega) (fun h hh => ?_) (by simpa using offsetInBox_mono (by omega) h₁)
    (by simpa using offsetInBox_mono (by omega) h₂)
  · have h2 := hM m (by omega)
    have e : -(δ / 8) * (m : ℝ) = -δ * m / 8 := by ring
    rw [e] at h2
    have h3 := lt_of_le_of_lt hc h2
    rw [Real.dist_eq] at h1 ⊢
    have h4 := abs_sub_lt_iff.mp h1
    have h5 := abs_sub_lt_iff.mp h3
    rw [abs_sub_lt_iff]
    constructor <;> linarith [h4.1, h4.2, h5.1, h5.2]
  · rw [add_siteOfInt_zero_add]
    exact ⟨fun _ => Finset.mem_univ _, fun _ => add_siteOfInt_mem_supBall 0 (offsetInBox_mono (by omega) hh)⟩
end Entries
section SumsOfDerivatives
variable {n : ℕ} [NeZero n]
private theorem mixedDeriv_finset_sum {k : ℕ} {sh : TorusSite n → TorusField n → ℝ} {W : TorusField n}
    (hs : ∀ y, ContDiffThreeAt (sh y) W) (hk : k ≤ 3) (c : Fin k → TorusBond n)
    (Xs : Fin k → imaginaryQuaternions) :
    mixedDeriv (fun W'' => ∑ y, sh y W'') W c Xs = ∑ y, mixedDeriv (sh y) W c Xs := by apply _root_.YangMills.SharedProofs.p19279 <;> assumption
end SumsOfDerivatives
section TranslateSum
private def supNorm (u : Fin 4 → ℤ) : ℕ := Finset.univ.sup fun i => (u i).natAbs
private theorem offsetInBox_supNorm (u : Fin 4 → ℤ) : OffsetInBox (supNorm u) u := by apply _root_.YangMills.Construction.LatticeFractionalIntegration.PowerWeightKernel.abs_apply_le_supNorm <;> assumption
private theorem supDist_zero_eq_supNorm {n : ℕ} [NeZero n] (y : TorusSite n) :
    supDist y 0 = supNorm (centered y) := by
  unfold supDist supNorm centered
  simp
private theorem supNorm_neg (u : Fin 4 → ℤ) : supNorm (-u) = supNorm u := by apply _root_.YangMills.Construction.LatticePaths.supNorm_neg <;> assumption
private theorem summable_exp_neg_supNorm {δ : ℝ} (hδ : 0 < δ) :
    Summable fun u : Fin 4 → ℤ => Real.exp (-δ * supNorm u) := by apply _root_.YangMills.Construction.LatticeSums.summable_exp_neg_offsetSupNorm <;> assumption
private theorem bondFrom_comp_pair {n : ℕ} (z : TorusSite n) (b b' : IntBond) :
    (fun l => bondFrom z ((![b, b'] : Fin 2 → IntBond) l)) = ![bondFrom z b, bondFrom z b'] := by
  funext l
  fin_cases l <;> rfl
private theorem levelShareFamily_zero_eq (a : ℝ) (L k n : ℕ) [NeZero n] :
    ShareFamilies.levelShareFamily a L k n 0 =
      StepCosts.levelShare a L k (Finset.univ : Finset (TorusSite n)) 0 := by
  funext V
  unfold ShareFamilies.levelShareFamily
  rw [dif_neg (NeZero.ne n)]
private theorem exists_mul_exp_lt {D δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m, M ≤ m → D * Real.exp (-δ * m) < ε := by
  have h : Tendsto (fun m : ℕ => D * Real.exp (-δ * m)) atTop (𝓝 0) := by
    exact show Tendsto (fun m : ℕ => D * Real.exp (-δ * m)) atTop (𝓝 0) from by
      have h3 : Tendsto (fun m : ℕ => Real.exp (-δ * m)) atTop (𝓝 0) := by
        have := Real.tendsto_exp_atBot.comp
          ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop_of_neg (neg_lt_zero.mpr hδ))
        exact this
      simpa using h3.const_mul D
  obtain ⟨M, hM⟩ := eventually_atTop.mp (h.eventually (Iio_mem_nhds hε))
  exact ⟨M, hM⟩
theorem limitFormTranslateSumStatement_holds (hS1 : TorusComparison.FlatSharesOnTwoTori)
    (hT : TorusComparison.FlatActionDerivativesAgree) : limitFormTranslateSumStatement := by
  intro Tb hD c C k Q _ hIs
  have hδ := hD.δ₁_pos
  have ha : 0 < Tb.coupling := by linarith [hD.a_ge]
  obtain ⟨D, hD0, hFacts, hNear⟩ :=
    hS1 Tb.coupling Tb.δ₁ Tb.side Tb.lam Tb.ρA Tb.σA Tb.cg Tb.N ha hD.L_odd hD.chain
  obtain ⟨C₁, hC₁, hB⟩ := hT Tb.coupling Tb.δ₁ Tb.side Tb.lam Tb.ρA Tb.σA Tb.cg Tb.N ha hD.L_odd hD.chain
  have hB' : TwoTorusBound Tb.coupling Tb.δ₁ Tb.side C₁ := fun t n n' _ _ => hB t n n'
  set δ := Tb.δ₁ with hδdef
  set a := Tb.coupling with hadef
  set L := Tb.side with hLdef
  have hnear : ∀ (n n' : ℕ) [NeZero n] [NeZero n'] (z : TorusSite n) (z' : TorusSite n') (m r : ℕ)
      (B B' : IntBond), 64 ≤ n → 64 ≤ n' → 2 * m + 2 < n → 2 * m + 2 < n' → 4 * r + 4 ≤ m →
      OffsetInBox r B.1 → OffsetInBox r B'.1 →
      |mixedDeriv (StepCosts.levelShare a L k Finset.univ z) (trivialField n) ![bondFrom z B, bondFrom z B']
          ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI] -
        mixedDeriv (StepCosts.levelShare a L k Finset.univ z') (trivialField n') ![bondFrom z' B, bondFrom z' B']
          ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI]| ≤
        D * Real.exp (-δ * m) := by
    intro n n' _ _ z z' m r B B' h1 h2 h3 h4 h5 h6 h7
    have := hNear k n n' z z' m r h1 h2 h3 h4 h5 2 ![B, B']
      ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI] (by norm_num) (by norm_num)
      areUnitVectors_imaginaryUnitI_pair
      (by
        intro l
        fin_cases l
        · exact h6
        · exact h7)
    rwa [bondFrom_comp_pair, bondFrom_comp_pair] at this
  have hlim : ∀ b b' : IntBond, ∃ q, Tendsto (fun n => mixedDeriv (ShareFamilies.levelShareFamily a L k n 0)
      (trivialField n) ![bondFrom 0 b, bondFrom 0 b']
      ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI]) atTop (𝓝 q) := by
    intro b b'
    have hcau : CauchySeq fun n => mixedDeriv (ShareFamilies.levelShareFamily a L k n 0) (trivialField n)
        ![bondFrom 0 b, bondFrom 0 b'] ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI] := by
      rw [Metric.cauchySeq_iff']
      intro ε hε
      obtain ⟨M, hM⟩ := exists_mul_exp_lt (D := D) hδ hε
      obtain ⟨m, hm⟩ : ∃ m, m = M + 4 * (supNorm b.1 + supNorm b'.1) + 4 := ⟨_, rfl⟩
      obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = 2 * m + 64 := ⟨_, rfl⟩
      refine ⟨n₀, fun n hn => ?_⟩
      haveI : NeZero n := ⟨by omega⟩
      haveI : NeZero n₀ := ⟨by omega⟩
      rw [Real.dist_eq, levelShareFamily_zero_eq, levelShareFamily_zero_eq]
      refine lt_of_le_of_lt (hnear n n₀ 0 0 m (supNorm b.1 + supNorm b'.1) b b' (by omega) (by omega) (by omega)
        (by omega) (by omega) (offsetInBox_mono (by omega) (offsetInBox_supNorm _))
        (offsetInBox_mono (by omega) (offsetInBox_supNorm _))) (hM m (by omega))
    exact cauchySeq_tendsto_of_complete hcau
  choose q hq using hlim
  refine ⟨q, hq, fun b b' => ?_⟩
  classical
  set Dn : (N : ℕ) → Finset (Fin 4 → ℤ) := fun N =>
    Finset.univ.image fun y : TorusSite (16 * (N + 1)) => -centered y with hDn
  set f : ℕ → (Fin 4 → ℤ) → ℝ := fun N u => if u ∈ Dn N then
    mixedDeriv (StepCosts.levelShare a L k (Finset.univ : Finset (TorusSite (16 * (N + 1)))) (siteOfInt (-u)))
      (trivialField (16 * (N + 1))) ![bondFrom 0 b, bondFrom 0 b']
      ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI] else 0 with hf
  set g : (Fin 4 → ℤ) → ℝ := fun u => q (b.1 + u, b.2) (b'.1 + u, b'.2) with hg
  set bnd : (Fin 4 → ℤ) → ℝ := fun u => D * Real.exp (δ * supNorm b.1) * Real.exp (-δ * supNorm u) with hbnd
  have hbsum : Summable bnd := (summable_exp_neg_supNorm hδ).mul_left _
  have hsumf : ∀ N, 4 ≤ N → ∑' u, f N u = offDiagEntry a L k (0 : TorusSite (16 * (N + 1))) Finset.univ b b' := by
    intro N hN
    obtain ⟨s1, s2, -⟩ := hFacts k (16 * (N + 1)) (by omega)
    have e1 : ∑' u, f N u = ∑ u ∈ Dn N, f N u := tsum_eq_sum fun u hu => by simp only [hf, if_neg hu]
    have hinj : Set.InjOn (fun y : TorusSite (16 * (N + 1)) => -centered y)
        (Finset.univ : Finset (TorusSite (16 * (N + 1)))) := by
      intro y _ y' _ he
      have h1 : centered y = centered y' := neg_injective he
      rw [← siteOfInt_centered y, ← siteOfInt_centered y', h1]
    rw [e1, Finset.sum_image hinj]
    unfold offDiagEntry
    rw [s1, mixedDeriv_finset_sum s2 (by norm_num)]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [hf]
    rw [if_pos (Finset.mem_image_of_mem _ (Finset.mem_univ y)), neg_neg, siteOfInt_centered]
  have hbound : ∀ N, 4 ≤ N → ∀ u, ‖f N u‖ ≤ bnd u := by
    intro N hN u
    by_cases hu : u ∈ Dn N
    · obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨-, -, s3⟩ := hFacts k (16 * (N + 1)) (by omega)
      simp only [hf]
      rw [if_pos hu, neg_neg, siteOfInt_centered, Real.norm_eq_abs]
      refine (s3 2 ![bondFrom 0 b, bondFrom 0 b'] ![BoxGaussian.imaginaryUnitI, BoxGaussian.imaginaryUnitI] 0 y
        (by norm_num) (by norm_num) areUnitVectors_imaginaryUnitI_pair).trans ?_
      simp only [hbnd]
      rw [mul_assoc, ← Real.exp_add, supNorm_neg]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hD0.le
      have h1 := supDist_triangle y (bondFrom (0 : TorusSite (16 * (N + 1))) b).1 0
      have h2 : supDist (bondFrom (0 : TorusSite (16 * (N + 1))) b).1 0 ≤ supNorm b.1 := by
        have h3 := supDist_add_siteOfInt_le (0 : TorusSite (16 * (N + 1))) b.1 (supNorm b.1) fun i => by
          have := offsetInBox_supNorm b.1 i
          rw [Int.abs_eq_natAbs] at this
          omega
        rw [supDist_comm]
        exact h3
      rw [supDist_zero_eq_supNorm] at h1
      have h4 : (supNorm (centered y) : ℝ) ≤
          supDist y (bondFrom (0 : TorusSite (16 * (N + 1))) b).1 + supNorm b.1 := by
        have : supNorm (centered y) ≤ supDist y (bondFrom (0 : TorusSite (16 * (N + 1))) b).1 + supNorm b.1 := by
          omega
        exact_mod_cast this
      show -δ * (supDist y (![bondFrom (0 : TorusSite (16 * (N + 1))) b, bondFrom 0 b'] 0).1 : ℝ) ≤ _
      have e : (![bondFrom (0 : TorusSite (16 * (N + 1))) b, bondFrom 0 b'] 0).1 =
          (bondFrom (0 : TorusSite (16 * (N + 1))) b).1 := rfl
      rw [e]
      nlinarith
    · simp only [hf]
      rw [if_neg hu, norm_zero]
      positivity
  have hpoint : ∀ u, Tendsto (fun N => f N u) atTop (𝓝 (g u)) := by
    intro u
    have hmain := (hq (b.1 + u, b.2) (b'.1 + u, b'.2)).comp
      (tendsto_atTop_mono (fun N => (by omega : N ≤ 16 * (N + 1))) tendsto_id)
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hmain (ε / 2) (half_pos hε)
    obtain ⟨M, hM⟩ := exists_mul_exp_lt (D := D) hδ (half_pos hε)
    obtain ⟨r, hr⟩ : ∃ r, r = supNorm (b.1 + u) + supNorm (b'.1 + u) := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m, m = M + 4 * r + 4 + supNorm u := ⟨_, rfl⟩
    refine ⟨N₁ + m + 4, fun N hN => ?_⟩
    have h1 := hN₁ N (by omega)
    simp only [Function.comp] at h1
    rw [levelShareFamily_zero_eq] at h1
    have hcenu : centered (siteOfInt (-u) : TorusSite (16 * (N + 1))) = -u :=
      centered_siteOfInt (p := supNorm u) (fun i => by
        have := offsetInBox_supNorm u i
        simpa using this) (by omega)
    have hmem : u ∈ Dn N := by
      refine Finset.mem_image.mpr ⟨siteOfInt (-u), Finset.mem_univ _, ?_⟩
      rw [hcenu, neg_neg]
    have hbA : ∀ B : IntBond,
        bondFrom (siteOfInt (-u) : TorusSite (16 * (N + 1))) (B.1 + u, B.2) = bondFrom 0 B := by
      intro B
      refine Prod.ext ?_ rfl
      show (siteOfInt (-u) : TorusSite (16 * (N + 1))) + siteOfInt (B.1 + u) = 0 + siteOfInt B.1
      rw [← siteOfInt_add, zero_add]
      congr 1
      abel
    have h2 := hnear (16 * (N + 1)) (16 * (N + 1)) (siteOfInt (-u)) 0 m r (b.1 + u, b.2) (b'.1 + u, b'.2)
      (by omega) (by omega) (by omega) (by omega) (by omega)
      (offsetInBox_mono (by omega) (offsetInBox_supNorm (b.1 + u)))
      (offsetInBox_mono (by omega) (offsetInBox_supNorm (b'.1 + u)))
    rw [hbA, hbA] at h2
    have h3 := lt_of_le_of_lt h2 (hM m (by omega))
    simp only [hf]
    rw [if_pos hmem]
    rw [Real.dist_eq] at h1 ⊢
    have h4 := abs_sub_lt_iff.mp h1
    have h5 := abs_sub_lt_iff.mp h3
    rw [abs_sub_lt_iff]
    constructor <;> linarith [h4.1, h4.2, h5.1, h5.2]
  have hgb : ∀ u, ‖g u‖ ≤ bnd u := by
    intro u
    refine le_of_tendsto (hpoint u).norm ?_
    filter_upwards [eventually_ge_atTop 4] with N hN
    exact hbound N hN u
  have hgs : Summable g := Summable.of_norm_bounded hbsum hgb
  have hdct := tendsto_tsum_of_dominated_convergence hbsum hpoint
    (by filter_upwards [eventually_ge_atTop 4] with N hN
        exact hbound N hN)
  have hW := tendsto_offDiagEntry_univ hδ hB' k (hIs.tendsto b b')
  have heq : Tendsto (fun N => offDiagEntry a L k (0 : TorusSite (16 * (N + 1))) Finset.univ b b') atTop
      (𝓝 (∑' u, g u)) := by
    refine hdct.congr' ?_
    filter_upwards [eventually_ge_atTop 4] with N hN
    exact hsumf N hN
  have hQ : Q b b' = ∑' u, g u := tendsto_nhds_unique hW heq
  rw [hQ]
  exact hgs.hasSum
end TranslateSum
end YangMills.Construction.LimitForms
end
