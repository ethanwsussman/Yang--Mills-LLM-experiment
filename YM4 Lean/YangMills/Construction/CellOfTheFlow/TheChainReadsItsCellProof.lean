import YangMills.Construction.CellOfTheFlow.TheChainReadsItsCell
import YangMills.Construction.ClusterExpansionOfAStep.NearPotentialAgainstTheCostProof
import YangMills.Construction.ClusterExpansionOfAStep.ShiftsOfTwoSettings
import YangMills.Construction.ClusterExpansionOfAStep.ZonesOfAGround
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
namespace ChainLocality
section Interior
variable {n : ℕ} [NeZero n]
private theorem mem_interior {m : ℕ} {c : Finset (TorusFields.TorusSite n)} {v : TorusFields.TorusSite n} :
    v ∈ interiorAtDepth m c ↔ v ∈ c ∧ ∀ w, w ∉ c → m ≤ TorusFields.supDist v w := by
  unfold interiorAtDepth
  exact Finset.mem_filter
private theorem interior_mono {A B : ℕ} (h : A ≤ B) {c : Finset (TorusFields.TorusSite n)}
    {v : TorusFields.TorusSite n} (hv : v ∈ interiorAtDepth B c) : v ∈ interiorAtDepth A c :=
  mem_interior.2 ⟨(mem_interior.1 hv).1, fun w hw => h.trans ((mem_interior.1 hv).2 w hw)⟩
abbrev _root_.YangMills.SharedProofs.p110460 := @interior_mono
private theorem interior_of_near {A d : ℕ} (hA : 0 < A) {c : Finset (TorusFields.TorusSite n)}
    {z u : TorusFields.TorusSite n} (hz : z ∈ interiorAtDepth (A + d) c) (h : TorusFields.supDist u z ≤ d) :
    u ∈ interiorAtDepth A c := by
  have key : ∀ w, w ∉ c → A ≤ TorusFields.supDist u w := by
    intro w hw
    have h1 := (mem_interior.1 hz).2 w hw
    have h2 := TorusFields.supDist_triangle z u w
    have h3 : TorusFields.supDist z u = TorusFields.supDist u z := TorusFields.supDist_comm _ _
    omega
  refine mem_interior.2 ⟨?_, key⟩
  by_contra hu
  have := key u hu
  rw [TorusFields.supDist_self] at this
  omega
private theorem mem_thickening_iff {m : ℕ} {X : Finset (TorusFields.TorusSite n)} {z : TorusFields.TorusSite n} :
    z ∈ TorusLumps.thickening m X ↔ ∃ x ∈ X, TorusFields.supDist z x ≤ m := by apply _root_.YangMills.Construction.TorusFields.mem_thickening <;> assumption
private def AgreeInInterior (c : Finset (TorusFields.TorusSite n)) (W W' : TorusFields.TorusField n) : Prop :=
  ∀ b : TorusFields.TorusBond n, b.1 ∈ interiorAtDepth 8 c →
    b.1 + TorusFields.unitStep n b.2 ∈ interiorAtDepth 8 c → W b.1 b.2 = W' b.1 b.2
private theorem AgreeInInterior.symm {c : Finset (TorusFields.TorusSite n)} {W W' : TorusFields.TorusField n}
    (h : AgreeInInterior c W W') : AgreeInInterior c W' W := fun b h1 h2 => (h b h1 h2).symm
private theorem AgreeInInterior.of_agreeOn {c : Finset (TorusFields.TorusSite n)}
    {W W' : TorusFields.TorusField n} (h : FieldsAgreeOn c W W') : AgreeInInterior c W W' :=
  fun b h1 h2 => h b (mem_interior.1 h1).1 (mem_interior.1 h2).1
private theorem step_interior {c : Finset (TorusFields.TorusSite n)} {u : TorusFields.TorusSite n}
    (hu : u ∈ interiorAtDepth 9 c) (i : Fin 4) :
    u ∈ interiorAtDepth 8 c ∧ u + TorusFields.unitStep n i ∈ interiorAtDepth 8 c := by
  refine ⟨interior_mono (by norm_num) hu, interior_of_near (A := 8) (d := 1) (by norm_num) hu ?_⟩
  rw [TorusFields.supDist_comm]
  exact TorusFields.supDist_add_unitStep_le u i
end Interior
section Blocks
variable {n L : ℕ} [NeZero n] [NeZero L]
private theorem mem_sitesInBlocks {S : Finset (TorusFields.TorusSite n)} {x : TorusFields.TorusSite (n * L)} :
    x ∈ TorusLumps.sitesInBlocks L S ↔ TorusLumps.parentBlock L x ∈ S := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.mem_sitesInBlocks <;> assumption
private theorem interior_of_parentBlock (hL : 8 ≤ L) {A : ℕ} (hA : 2 ≤ A) {c : Finset (TorusFields.TorusSite n)}
    {v : TorusFields.TorusSite (n * L)} (h : TorusLumps.parentBlock L v ∈ interiorAtDepth A c) :
    v ∈ interiorAtDepth 8 (TorusLumps.sitesInBlocks L c) := by
  refine mem_interior.2 ⟨mem_sitesInBlocks.2 (mem_interior.1 h).1, fun w hw => ?_⟩
  have h1 := (mem_interior.1 h).2 _ (fun hc => hw (mem_sitesInBlocks.2 hc))
  have h2 := TorusBalls.supDist_parentBlock_le_div_add_one L v w
  have h3 : 1 ≤ TorusFields.supDist v w / L := by omega
  have h4 := (Nat.le_div_iff_mul_le (by omega)).1 h3
  omega
private theorem agreeOn_threeNeighbourhood (hL : 8 ≤ L) {c : Finset (TorusFields.TorusSite n)}
    {W W' : TorusFields.TorusField (n * L)} (h : AgreeInInterior (TorusLumps.sitesInBlocks L c) W W')
    {Y : Finset (TorusFields.TorusSite n)} (hY : ∀ y ∈ Y, y ∈ interiorAtDepth 8 c) :
    FieldsAgreeOn (TorusLumps.sitesInBlocks L (TorusLumps.thickening 3 Y)) W W' := by
  have key : ∀ v, v ∈ TorusLumps.sitesInBlocks L (TorusLumps.thickening 3 Y) →
      v ∈ interiorAtDepth 8 (TorusLumps.sitesInBlocks L c) := by
    intro v hv
    obtain ⟨y, hy, hd⟩ := mem_thickening_iff.1 (mem_sitesInBlocks.1 hv)
    exact interior_of_parentBlock hL (A := 5) (by norm_num) (interior_of_near (d := 3) (by norm_num) (hY y hy) hd)
  intro b h1 h2
  exact h b (key _ h1) (key _ h2)
end Blocks
section Field
private theorem sampledBases_torusSiteInFrame {R : StepSettings.StepSetup} (S : StepSampler R) {n : ℕ} [NeZero n]
    (W : TorusFields.TorusField (n * R.params.side)) (ξ : StepNoise R.params n) (x : TorusFields.TorusSite n) :
    S.sampledBases W ξ (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 x) =
      S.sampleBase n W x (ξ.1 x) := by
  have e : TorusLumps.toTorusSite n
      (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 x) = x :=
    TopLevelSites.toTorusSite_torusSiteInFrame (fun i => BlockOffsets.period_one i) x
  have key : ∀ y, y = x → S.sampleBase n W y (ξ.1 y) = S.sampleBase n W x (ξ.1 x) := by
    rintro _ rfl
    rfl
  exact key _ e
private theorem sampledField_agree {ℓ : TorusLumps.StepParameters} (T : WeightedResponses.StageTower ℓ)
    (S : ChainSampler T) (hS : ∀ s, (S s).IsFaithful) (hL : 8 ≤ ℓ.side) :
    ∀ (s n : ℕ) [NeZero n] (c : Finset (TorusFields.TorusSite n))
      (U U' : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side s n)) (ξ ξ' : ChainNoise ℓ s n),
      FieldsAgreeOn (cellBelow ℓ.side s n c) U U' → NoiseAgreesOn ℓ s n c ξ ξ' →
      AgreeInInterior c (WeightedResponses.topField ℓ s n (sampleChain T S s n U ξ))
        (WeightedResponses.topField ℓ s n (sampleChain T S s n U' ξ')) := by
  intro s
  induction s with
  | zero =>
    intro n _ c U U' ξ ξ' hU _
    exact AgreeInInterior.of_agreeOn hU
  | succ s ih =>
    intro n _ c U U' ξ ξ' hU hξ b h1 h2
    obtain ⟨hξ0, hξb, hξc, -⟩ := hξ
    have hW := ih (n * ℓ.side) (TorusLumps.sitesInBlocks ℓ.side c) U U' ξ.1 ξ'.1 hU hξ0
    set W := WeightedResponses.topField ℓ s (n * ℓ.side) (sampleChain T S s (n * ℓ.side) U ξ.1) with hWdef
    set W' := WeightedResponses.topField ℓ s (n * ℓ.side) (sampleChain T S s (n * ℓ.side) U' ξ'.1) with hWdef'
    have hbase : ∀ y ∈ interiorAtDepth 8 c,
        (S s).sampledBases W ξ.2 (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 y) =
        (S s).sampledBases W' ξ'.2 (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 y) := by
      intro y hy
      rw [sampledBases_torusSiteInFrame, sampledBases_torusSiteInFrame, hξb y (mem_interior.1 hy).1]
      refine (hS s).base_local n W W' y _ (agreeOn_threeNeighbourhood hL hW ?_)
      intro y' h'
      rw [Finset.mem_singleton.1 h']
      exact hy
    have hn : ξ.2.2.1 b = ξ'.2.2.1 b := hξc b (mem_interior.1 h1).1 (mem_interior.1 h2).1
    show (S s).sampleLink n W ((S s).sampledBases W ξ.2) (b.1, b.2) (ξ.2.2.1 (b.1, b.2)) =
      (S s).sampleLink n W' ((S s).sampledBases W' ξ'.2) (b.1, b.2) (ξ'.2.2.1 (b.1, b.2))
    have hn' : ξ.2.2.1 (b.1, b.2) = ξ'.2.2.1 (b.1, b.2) := hn
    rw [hn']
    have hunder : ∀ y : TorusFields.TorusSite n,
        (S s).sampledBases W ξ.2 (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 y) ∈
        LumpContours.sitesBelow 0 (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 y) := by
      intro y
      rw [sampledBases_torusSiteInFrame]
      exact (hS s).base_mem_sitesBelow n W y _
    refine (hS s).link_local n W W' _ _ (b.1, b.2) _ (agreeOn_threeNeighbourhood hL hW ?_) (hunder _) (hunder _)
      (hbase _ h1) (hbase _ h2)
    intro y' h'
    rcases Finset.mem_insert.1 h' with rfl | h''
    · exact h1
    · rw [Finset.mem_singleton.1 h'']
      exact h2
end Field
section Seam
private theorem natAbs_cast_sub_le {P m L : ℕ} [NeZero m] (hP : 0 < P) (h1 : P ≤ m) (h2 : m ≤ P + L)
    (a b : ZMod P) (e : ℤ) (h : a - b = (e : ZMod P)) :
    ((((ZMod.cast a : ℤ) : ZMod m) - ((ZMod.cast b : ℤ) : ZMod m)).valMinAbs).natAbs ≤ e.natAbs + L := by
  have : NeZero P := ⟨hP.ne'⟩
  set d : ℤ := (a - b).valMinAbs with hd
  have hde : d.natAbs ≤ e.natAbs := by
    rw [hd, h]
    exact TorusFields.natAbs_valMinAbs_intCast_le e
  have hdP : d.natAbs ≤ P / 2 := ZMod.natAbs_valMinAbs_le _
  have hdc : ((d : ℤ) : ZMod P) = a - b := ZMod.coe_valMinAbs _
  set A : ℤ := (ZMod.cast a : ℤ) with hA
  set B : ℤ := (ZMod.cast b : ℤ) with hB
  have hAc : ((A : ℤ) : ZMod P) = a := ZMod.intCast_zmod_cast a
  have hBc : ((B : ℤ) : ZMod P) = b := ZMod.intCast_zmod_cast b
  have hA0 : 0 ≤ A ∧ A < P := by
    have e1 : A = ((a.val : ℕ) : ℤ) := ZMod.cast_eq_val a
    have e2 := ZMod.val_lt a
    omega
  have hB0 : 0 ≤ B ∧ B < P := by
    have e1 : B = ((b.val : ℕ) : ℤ) := ZMod.cast_eq_val b
    have e2 := ZMod.val_lt b
    omega
  have hdvd : (P : ℤ) ∣ d - (A - B) := by
    rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
    push_cast
    rw [hAc, hBc, hdc]
  obtain ⟨t, ht⟩ := hdvd
  have hd2 : 2 * d ≤ P ∧ -(P : ℤ) ≤ 2 * d := by omega
  have ht1 : t = -1 ∨ t = 0 ∨ t = 1 := by
    have u1 : t < 2 := by
      by_contra hc
      have : (2 : ℤ) ≤ t := by omega
      nlinarith
    have u2 : -2 < t := by
      by_contra hc
      have : t ≤ -2 := by omega
      nlinarith
    omega
  have hcast : ((A : ℤ) : ZMod m) - ((B : ℤ) : ZMod m) = ((d + ((m : ℤ) - P) * t : ℤ) : ZMod m) := by
    rw [← Int.cast_sub, ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨t, ?_⟩
    linarith
  rw [hcast]
  refine (TorusFields.natAbs_valMinAbs_intCast_le _).trans ?_
  rcases ht1 with rfl | rfl | rfl <;> simp only [mul_neg, mul_one, mul_zero] <;> omega
private theorem supDist_toTorusSite_le {F : BlockAverages.BlockFrame} {j m L : ℕ} [NeZero m]
    (hpos : ∀ i, 0 < F.period j i) (h1 : ∀ i, F.period j i ≤ m) (h2 : ∀ i, m ≤ F.period j i + L)
    (x y : F.Site j) (E : ℕ)
    (h : ∀ i, ∃ e : ℤ, x i - y i = (e : ZMod (F.period j i)) ∧ e.natAbs ≤ E) :
    TorusFields.supDist (TorusLumps.toTorusSite m x) (TorusLumps.toTorusSite m y) ≤ E + L := by
  rw [TorusFields.supDist_le_iff]
  intro i
  obtain ⟨e, he, hE⟩ := h i
  exact (natAbs_cast_sub_le (hpos i) (h1 i) (h2 i) _ _ e he).trans (by omega)
private theorem plaquetteHolonomy_eq {F : BlockAverages.BlockFrame} {j : ℕ} (X : F.GaugeField j) (a : F.Site j)
    (μ ν : Fin 4) :
    BlockAverages.plaquetteHolonomy X (a, μ, ν) =
      X a μ * (X (a + BlockAverages.unitStep j μ) ν *
        ((X (a + BlockAverages.unitStep j ν) μ)⁻¹ * (X a ν)⁻¹)) := by
  have a1 : a + BlockAverages.unitStep j μ + BlockAverages.unitStep j ν - BlockAverages.unitStep j μ =
      a + BlockAverages.unitStep j ν := by abel
  have a2 : a + BlockAverages.unitStep j μ + BlockAverages.unitStep j ν + -BlockAverages.unitStep j μ -
      BlockAverages.unitStep j ν = a := by abel
  simp only [BlockAverages.plaquetteHolonomy, BlockAverages.pathHolonomy, BlockAverages.linkValue,
    BlockAverages.stepDisplacement, if_true, Bool.false_eq_true, if_false, mul_one, a1, a2]
private theorem single_bounds (μ i : Fin 4) :
    0 ≤ (Pi.single μ 1 : Fin 4 → ℤ) i ∧ (Pi.single μ 1 : Fin 4 → ℤ) i ≤ 1 := by apply _root_.YangMills.Construction.PeriodicLattice.IsometryInvariance.single_one_bounds <;> assumption
private theorem corner_eq {F : BlockAverages.BlockFrame} {j : ℕ} {a q : F.Site j} {μ ν : Fin 4}
    (h : q ∈ BlockAverages.plaquetteCorners (a, μ, ν)) :
    ∃ A : Fin 4 → ℤ, q = a + BlockAverages.siteOfCoords j A ∧ ∀ i, 0 ≤ A i ∧ A i ≤ 2 := by
  simp only [BlockAverages.plaquetteCorners, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with rfl | rfl | rfl | rfl
  · exact ⟨0, by funext i; simp [BlockAverages.siteOfCoords], fun i => by simp⟩
  · exact ⟨Pi.single μ 1, rfl, fun i => by have := single_bounds μ i; omega⟩
  · exact ⟨Pi.single ν 1, rfl, fun i => by have := single_bounds ν i; omega⟩
  · refine ⟨Pi.single μ 1 + Pi.single ν 1, ?_, fun i => ?_⟩
    · funext i
      simp [BlockAverages.siteOfCoords, BlockAverages.unitStep, add_assoc]
    · have := single_bounds μ i
      have := single_bounds ν i
      simp only [Pi.add_apply]
      omega
private theorem lump_offsets {L : ℕ} (hL : Odd L) (g : LumpContours.LumpGrid L) {F : BlockAverages.BlockFrame}
    {j : ℕ} {x y : F.Site j} (hy : y ∈ LumpContours.lumpOf g x) :
    ∀ i, ∃ e : ℤ, y i - x i = (e : ZMod (F.period j i)) ∧ e.natAbs ≤ 2 ^ 15 := by
  unfold LumpContours.lumpOf LumpContours.boxSites at hy
  obtain ⟨H, hH, rfl⟩ := Finset.mem_image.1 hy
  intro i
  have hi : BlockAverages.siteCoords x i - LumpContours.offsetFromCentre L (BlockAverages.siteCoords x i) +
        g.lower (LumpContours.offsetFromCentre L (BlockAverages.siteCoords x i)) ≤ H i ∧
      H i ≤ BlockAverages.siteCoords x i - LumpContours.offsetFromCentre L (BlockAverages.siteCoords x i) +
        g.upper (LumpContours.offsetFromCentre L (BlockAverages.siteCoords x i)) :=
    Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hH i)
  refine ⟨H i - BlockAverages.siteCoords x i, ?_, ?_⟩
  · have e1 : ((BlockAverages.siteCoords x i : ℤ) : ZMod (F.period j i)) = x i := ZMod.intCast_zmod_cast (x i)
    simp only [BlockAverages.siteOfCoords]
    push_cast
    rw [e1]
  · obtain ⟨h, hh⟩ := hL
    have hLz : (L : ℤ) = 2 * h + 1 := by subst hh; push_cast; ring
    have hhalf : ((L : ℤ) - 1) / 2 = h := by rw [hLz]; omega
    set c := BlockAverages.siteCoords x i with hc
    have hoff : LumpContours.offsetFromCentre L c = (c + h) % (L : ℤ) - h := by
      unfold LumpContours.offsetFromCentre
      rw [hhalf]
    set o := LumpContours.offsetFromCentre L c with ho
    have hm0 := Int.emod_nonneg (c + h) (show (L : ℤ) ≠ 0 by omega)
    have hm1 := Int.emod_lt_of_pos (c + h) (show (0 : ℤ) < L by omega)
    have hobd : |o| ≤ ((L : ℤ) - 1) / 2 := by
      rw [hhalf, abs_le]
      constructor <;> omega
    obtain ⟨-, b2, b3, -⟩ := g.mem_interval o hobd
    obtain ⟨-, s2⟩ := g.interval_length o hobd
    norm_num at s2 ⊢
    omega
end Seam
section Hot
private theorem hot_of_agree (ℓ : TorusLumps.StepParameters) (hL : Odd ℓ.side) {m : ℕ} [NeZero m]
    (W W' : TorusFields.TorusField m) (z : TorusFields.TorusSite m)
    (hag : ∀ u i, TorusFields.supDist u z ≤ 2 ^ 15 + 2 + ℓ.side → W u i = W' u i)
    (hz : z ∈ TorusLumps.torusHotSites ℓ W) : z ∈ TorusLumps.torusHotSites ℓ W' := by
  classical
  simp only [TorusLumps.torusHotSites, TorusLumps.torusHotLumps, LumpContours.hotLumps, Finset.mem_biUnion,
    Finset.mem_image, Finset.mem_filter, id_eq] at hz ⊢
  obtain ⟨l, ⟨l₀, ⟨⟨a, μ, ν⟩, ⟨hp, hs⟩, x, hx, rfl⟩, rfl⟩, hzl⟩ := hz
  obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hzl
  refine ⟨_, ⟨_, ⟨(a, μ, ν), ⟨hp, ?_⟩, x, hx, rfl⟩, rfl⟩, Finset.mem_image.2 ⟨y, hy, rfl⟩⟩
  have hLpos : 0 < ℓ.side := hL.pos
  have hposi : ∀ i, 0 < (TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)).period 0 i := by
    have ha : a ∈ TorusLumps.levelSites (TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)) 0 := by
      unfold LumpContours.cutPlaquettes at hp
      exact (Finset.mem_product.1 (Finset.mem_filter.1 hp).1).1
    unfold TorusLumps.levelSites LumpContours.boxSites at ha
    obtain ⟨H, hH, -⟩ := Finset.mem_image.1 ha
    intro i
    have hi : (0 : ℤ) ≤ H i ∧ H i ≤ ((TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)).period 0 i : ℤ) - 1 :=
      Finset.mem_Icc.1 (Fintype.mem_piFinset.1 hH i)
    omega
  have hp1 : ∀ i, (TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)).period 0 i ≤ m := fun i => by
    rw [BlockOffsets.period_zero]
    exact Nat.div_mul_le_self m ℓ.side
  have hp2 : ∀ i, m ≤ (TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)).period 0 i + ℓ.side := fun i => by
    rw [BlockOffsets.period_zero]
    have e1 := Nat.div_add_mod m ℓ.side
    have e2 := Nat.mod_lt m hLpos
    rw [mul_comm] at e1
    omega
  have hr : ∀ q ∈ BlockAverages.plaquetteCorners
      ((a, μ, ν) : (TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)).Site 0 × Fin 4 × Fin 4), ∀ i,
      TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)) 0 W q i =
        TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)) 0 W' q i := by
    intro q hq i
    show W (TorusLumps.toTorusSite m q) i = W' (TorusLumps.toTorusSite m q) i
    refine hag _ i ?_
    obtain ⟨A, hqA, hA⟩ := corner_eq hq
    obtain ⟨A', hxA, hA'⟩ := corner_eq hx
    refine supDist_toTorusSite_le hposi hp1 hp2 q y (2 ^ 15 + 2) fun k => ?_
    obtain ⟨e, he, hE⟩ := lump_offsets hL ℓ.grid hy k
    refine ⟨A k - A' k - e, ?_, ?_⟩
    · rw [hxA] at he
      rw [hqA]
      simp only [Pi.add_apply, BlockAverages.siteOfCoords] at he ⊢
      push_cast
      rw [← he]
      ring
    · have b1 := hA k
      have b2 := hA' k
      norm_num at hE ⊢
      omega
  have hsame : BlockAverages.plaquetteHolonomy
        (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)) 0 W) (a, μ, ν) =
      BlockAverages.plaquetteHolonomy
        (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)) 0 W') (a, μ, ν) := by
    have c1 : a ∈ BlockAverages.plaquetteCorners
        ((a, μ, ν) : (TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)).Site 0 × Fin 4 × Fin 4) := by
      simp [BlockAverages.plaquetteCorners]
    have c2 : a + BlockAverages.unitStep 0 μ ∈ BlockAverages.plaquetteCorners
        ((a, μ, ν) : (TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)).Site 0 × Fin 4 × Fin 4) := by
      simp [BlockAverages.plaquetteCorners]
    have c3 : a + BlockAverages.unitStep 0 ν ∈ BlockAverages.plaquetteCorners
        ((a, μ, ν) : (TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)).Site 0 × Fin 4 × Fin 4) := by
      simp [BlockAverages.plaquetteCorners]
    rw [plaquetteHolonomy_eq, plaquetteHolonomy_eq, hr a c1 μ, hr a c1 ν, hr _ c2 ν, hr _ c3 μ]
  have hc : BlockAverages.plaquetteDefect
        (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)) 0 W) (a, μ, ν) =
      BlockAverages.plaquetteDefect
        (TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side (m / ℓ.side)) 0 W') (a, μ, ν) := by
    unfold BlockAverages.plaquetteDefect
    rw [hsame]
  rw [← hc]
  exact hs
abbrev _root_.YangMills.SharedProofs.p17017 := @hot_of_agree
private theorem hot_iff_of_agree (ℓ : TorusLumps.StepParameters) (hL : Odd ℓ.side) {m : ℕ} [NeZero m]
    {c : Finset (TorusFields.TorusSite m)} {W W' : TorusFields.TorusField m} (h : AgreeInInterior c W W') {r : ℕ}
    (hr : 2 ^ 15 + 2 + ℓ.side + 9 ≤ r) {z : TorusFields.TorusSite m} (hz : z ∈ interiorAtDepth r c) :
    z ∈ TorusLumps.torusHotSites ℓ W ↔ z ∈ TorusLumps.torusHotSites ℓ W' := by
  have one : ∀ {W W' : TorusFields.TorusField m}, AgreeInInterior c W W' →
      z ∈ TorusLumps.torusHotSites ℓ W → z ∈ TorusLumps.torusHotSites ℓ W' := by
    intro W W' h
    refine hot_of_agree ℓ hL W W' z fun u i hu => ?_
    have hu9 : u ∈ interiorAtDepth 9 c := interior_of_near (by norm_num) (interior_mono (by omega) hz) hu
    have h2 := step_interior hu9 i
    exact h (u, i) h2.1 h2.2
  exact ⟨one h, one h.symm⟩
private theorem hull_iff_of_agree (ℓ : TorusLumps.StepParameters) (hL : Odd ℓ.side) {m : ℕ} [NeZero m]
    {c : Finset (TorusFields.TorusSite m)} {W W' : TorusFields.TorusField m} (h : AgreeInInterior c W W') {r : ℕ}
    (hr : 2 ^ 15 + 2 + ℓ.side + 9 ≤ r) {z : TorusFields.TorusSite m} (hz : z ∈ interiorAtDepth (4 * r) c) :
    z ∈ TorusLumps.thickening (2 * r) (TorusLumps.torusHotSites ℓ W) ↔
      z ∈ TorusLumps.thickening (2 * r) (TorusLumps.torusHotSites ℓ W') := by
  have one : ∀ {W W' : TorusFields.TorusField m}, AgreeInInterior c W W' →
      z ∈ TorusLumps.thickening (2 * r) (TorusLumps.torusHotSites ℓ W) →
        z ∈ TorusLumps.thickening (2 * r) (TorusLumps.torusHotSites ℓ W') := by
    intro W W' h hz'
    obtain ⟨x, hx, hd⟩ := mem_thickening_iff.1 hz'
    have hx' : x ∈ interiorAtDepth (2 * r) c :=
      interior_of_near (d := 2 * r) (by omega) (interior_mono (by omega) hz)
        (by rw [TorusFields.supDist_comm]; exact hd)
    exact mem_thickening_iff.2 ⟨x, (hot_iff_of_agree ℓ hL h hr (interior_mono (by omega) hx')).1 hx, hd⟩
  exact ⟨one h, one h.symm⟩
end Hot
section Marks
private theorem siteAtOffset_eq {F : BlockAverages.BlockFrame} (c : F.Cell) (a b : Fin 4 → ℤ) :
    (TorusLumps.siteAtOffset c a : F.Site F.depth) =
      TorusLumps.siteAtOffset c b + BlockAverages.siteOfCoords F.depth (a - b) := by apply _root_.YangMills.Construction.CoarseFactorLocality.siteAtOffset_eq_add <;> assumption
private theorem chartCoord_eq (hblocks : TorusLumps.BlockDataIsLocal) {ℓ : TorusLumps.StepParameters}
    (hfit : ℓ.Admissible) {n : ℕ} [NeZero n] {V V' : TorusFields.TorusField n}
    {W W' : TorusFields.TorusField (n * ℓ.side)} (b : TorusFields.TorusBond (n * ℓ.side)) (h16 : 16 ≤ n)
    (hV1 : V (TorusLumps.parentBlock ℓ.side b.1) b.2 = V' (TorusLumps.parentBlock ℓ.side b.1) b.2)
    (hW : ∀ (e : Fin 4 → ℤ) (k : Fin 4), (∀ j, (e j).natAbs ≤ 4 * ℓ.side) →
      W (b.1 + TorusFields.siteOfInt e) k = W' (b.1 + TorusFields.siteOfInt e) k) :
    StepCosts.chartCoord ℓ V W b = StepCosts.chartCoord ℓ V' W' b := by
  set w := TorusLumps.parentBlock ℓ.side b.1 with hw
  set o := StepSettings.siteOffset (L := ℓ.side) b.1 with ho
  have hb : StepSettings.blockSite w o = b.1 := BlockZones.blockSite_parentBlock_siteOffset b.1
  have c₁ : StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 0 b.1 =
      TorusLumps.siteAtOffset (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 w)
        (CongruentBoxes.refinedOffset ℓ.side 0 o) := by
    have e := CongruentAdmission.torusSiteInFrame_blockSite (n := n) (L := ℓ.side) 0 w o
    rw [hb] at e
    exact e
  have hp : ∀ i, (TorusLumps.stepBlockFrame ℓ.side n).period 0 i = n * ℓ.side :=
    fun i => BlockOffsets.period_zero i
  have on_near : ∀ u : Fin 4 → ℤ,
      TorusLumps.toTorusSite (n * ℓ.side)
        (TorusLumps.siteAtOffset (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 w) u :
          (TorusLumps.stepBlockFrame ℓ.side n).Site 0) =
        b.1 + TorusFields.siteOfInt (u - CongruentBoxes.refinedOffset ℓ.side 0 o) := by
    intro u
    have a1 : TorusLumps.toTorusSite (n * ℓ.side)
        (TorusLumps.siteAtOffset (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 w)
          (CongruentBoxes.refinedOffset ℓ.side 0 o) : (TorusLumps.stepBlockFrame ℓ.side n).Site 0) = b.1 :=
      (congrArg (TorusLumps.toTorusSite (n * ℓ.side)) c₁).symm.trans
        (TopLevelSites.toTorusSite_torusSiteInFrame hp b.1)
    have a2 := TopLevelSites.toTorusSite_siteOfCoords (F := TorusLumps.stepBlockFrame ℓ.side n) (j := 0) hp
      (u - CongruentBoxes.refinedOffset ℓ.side 0 o)
    have a3 := TopLevelSites.toTorusSite_add (F := TorusLumps.stepBlockFrame ℓ.side n) (j := 0) hp
      (TorusLumps.siteAtOffset (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 w)
        (CongruentBoxes.refinedOffset ℓ.side 0 o))
      (BlockAverages.siteOfCoords 0 (u - CongruentBoxes.refinedOffset ℓ.side 0 o))
    exact (congrArg (TorusLumps.toTorusSite (n * ℓ.side))
        (siteAtOffset_eq (F := TorusLumps.stepBlockFrame ℓ.side n) _ u (CongruentBoxes.refinedOffset ℓ.side 0 o))).trans
      (a3.trans (congrArg₂ (· + ·) a1 a2))
  have hag : ∀ (u : Fin 4 → ℤ) (k : Fin 4), TorusFields.OffsetInBox (3 * ℓ.side) u →
      TorusFields.OffsetInBox (3 * ℓ.side) (u + Pi.single k 1) →
      TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0 W
          (TorusLumps.siteAtOffset (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 w) u) k =
        TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 0 W'
          (TorusLumps.siteAtOffset (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 w) u) k := by
    intro u k hu _
    show W (TorusLumps.toTorusSite (n * ℓ.side)
        (TorusLumps.siteAtOffset (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 w) u :
          (TorusLumps.stepBlockFrame ℓ.side n).Site 0)) k =
      W' (TorusLumps.toTorusSite (n * ℓ.side)
        (TorusLumps.siteAtOffset (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 w) u :
          (TorusLumps.stepBlockFrame ℓ.side n).Site 0)) k
    rw [on_near]
    refine hW _ k fun j => ?_
    have h1 := abs_le.1 (hu j)
    have h2 := (BlockOffsets.mem_centredCube_iff _).1 (CongruentAdmission.refinedOffset_mem_centredCube hfit.L_odd o) j
    push_cast at h1
    simp only [Pi.sub_apply]
    omega
  have hVr : TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 V
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 w) b.2 =
      TorusFields.readAtLevel (TorusLumps.stepBlockFrame ℓ.side n) 1 V'
        (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame ℓ.side n) 1 w) b.2 := by
    rw [TopLevelSites.readAtLevel_torusSiteInFrame (fun i => BlockOffsets.period_one i),
      TopLevelSites.readAtLevel_torusSiteInFrame (fun i => BlockOffsets.period_one i)]
    exact hV1
  have key := (hblocks ℓ hfit n n h16 h16 _ _ _ _ hag).2 _ _ _ b.2
    (CongruentAdmission.refinedOffset_mem_centredCube hfit.L_odd o) hVr
  unfold StepCosts.chartCoord
  rw [c₁]
  exact key
private theorem bondMark_eq (hframe : FrameLocality.FrameCoordLocal) (hblocks : TorusLumps.BlockDataIsLocal)
    {R : StepSettings.StepSetup} (hfit : R.params.Admissible) {n : ℕ} [NeZero n] {V V' : TorusFields.TorusField n}
    {W W' : TorusFields.TorusField (n * R.params.side)} (b : TorusFields.TorusBond (n * R.params.side))
    (h16 : 16 ≤ n) (hm : 0 < R.frameReach) (hm2 : 4 * R.frameReach + 5 < n)
    (hV : TorusLumps.FieldsAgreeNear V V' (TorusLumps.parentBlock R.params.side b.1)
      (TorusLumps.parentBlock R.params.side b.1) R.frameReach)
    (hV1 : V (TorusLumps.parentBlock R.params.side b.1) b.2 = V' (TorusLumps.parentBlock R.params.side b.1) b.2)
    (hW : ∀ (e : Fin 4 → ℤ) (k : Fin 4), (∀ j, (e j).natAbs ≤ 4 * R.params.side) →
      W (b.1 + TorusFields.siteOfInt e) k = W' (b.1 + TorusFields.siteOfInt e) k) :
    StepSettings.bondMark R V W b = StepSettings.bondMark R V' W' b := by
  have hf := hframe R.params R.anchorRadius R.depth R.frameReach n n V V' b b hfit hm hm2 hm2 rfl rfl hV
  have hc := chartCoord_eq hblocks hfit b h16 hV1 hW
  unfold StepSettings.bondMark
  rw [hc, hf]
abbrev _root_.YangMills.SharedProofs.p1768 := @bondMark_eq
private def markedSet (R : StepSettings.StepSetup) {n : ℕ} [NeZero n] (W : TorusFields.TorusField (n * R.params.side))
    (V : TorusFields.TorusField n) (ξ : StepNoise R.params n) : Finset (TorusFields.TorusBond (n * R.params.side)) :=
  markedBadBonds R W V ξ
private theorem mem_markedSet_iff (hframe : FrameLocality.FrameCoordLocal) (hblocks : TorusLumps.BlockDataIsLocal)
    {R : StepSettings.StepSetup} (hfit : R.params.Admissible) {n : ℕ} [NeZero n]
    {c : Finset (TorusFields.TorusSite n)} {V V' : TorusFields.TorusField n}
    {W W' : TorusFields.TorusField (n * R.params.side)} {ξ ξ' : StepNoise R.params n}
    (b : TorusFields.TorusBond (n * R.params.side))
    (hw : AgreeInInterior (TorusLumps.sitesInBlocks R.params.side c) W W') (hv : AgreeInInterior c V V')
    (h16 : 16 ≤ n) (hm : 0 < R.frameReach) (hm2 : 4 * R.frameReach + 5 < n) {D : ℕ} (hD : R.frameReach + 9 ≤ D)
    (hy : TorusLumps.parentBlock R.params.side b.1 ∈ interiorAtDepth D c)
    (hhull : TorusLumps.parentBlock R.params.side b.1 ∈ StepSettings.hotCoreSites R V ↔
      TorusLumps.parentBlock R.params.side b.1 ∈ StepSettings.hotCoreSites R V')
    (hξ : ξ.2.2 b = ξ'.2.2 b) :
    b ∈ markedSet R W V ξ ↔ b ∈ markedSet R W' V' ξ' := by
  classical
  have hL : 8 ≤ R.params.side := by
    have := hfit.L_ge
    omega
  have hmark : StepSettings.bondMark R V W b = StepSettings.bondMark R V' W' b := by
    refine bondMark_eq hframe hblocks hfit b h16 hm hm2 ?_ ?_ ?_
    · intro e he
      have h1 : TorusFields.supDist (TorusLumps.parentBlock R.params.side b.1 + TorusFields.siteOfInt e.1)
          (TorusLumps.parentBlock R.params.side b.1) ≤ R.frameReach := by
        rw [TorusFields.supDist_comm]
        refine TorusFields.supDist_add_siteOfInt_le _ _ _ fun i => ?_
        have := abs_le.1 (he.1 i)
        omega
      have hu9 : TorusLumps.parentBlock R.params.side b.1 + TorusFields.siteOfInt e.1 ∈ interiorAtDepth 9 c :=
        interior_of_near (d := R.frameReach) (by norm_num) (interior_mono (by omega) hy) h1
      have h2 := step_interior hu9 e.2
      exact hv (TorusLumps.parentBlock R.params.side b.1 + TorusFields.siteOfInt e.1, e.2) h2.1 h2.2
    · have hy9 : TorusLumps.parentBlock R.params.side b.1 ∈ interiorAtDepth 9 c := interior_mono (by omega) hy
      have h2 := step_interior hy9 b.2
      exact hv (TorusLumps.parentBlock R.params.side b.1, b.2) h2.1 h2.2
    · intro e k he
      have hv0 : TorusFields.supDist (b.1 + TorusFields.siteOfInt e) b.1 ≤ 4 * R.params.side := by
        rw [TorusFields.supDist_comm]
        exact TorusFields.supDist_add_siteOfInt_le _ _ _ he
      have hbl : ∀ u : TorusFields.TorusSite (n * R.params.side), TorusFields.supDist u b.1 ≤ 4 * R.params.side + 1 →
          TorusLumps.parentBlock R.params.side u ∈ interiorAtDepth 2 c := by
        intro u hu
        have h1 := TorusBalls.supDist_parentBlock_le_div_add_one R.params.side u b.1
        have h2 : TorusFields.supDist u b.1 / R.params.side ≤ 4 := by
          apply Nat.lt_succ_iff.1
          rw [Nat.div_lt_iff_lt_mul (by omega)]
          omega
        exact interior_of_near (d := 5) (by norm_num) (interior_mono (by omega) hy) (by omega)
      have hv1 : TorusFields.supDist (b.1 + TorusFields.siteOfInt e + TorusFields.unitStep _ k) b.1 ≤
          4 * R.params.side + 1 := by
        have e1 := TorusFields.supDist_triangle (b.1 + TorusFields.siteOfInt e + TorusFields.unitStep _ k)
          (b.1 + TorusFields.siteOfInt e) b.1
        have e2 := TorusFields.supDist_add_unitStep_le (b.1 + TorusFields.siteOfInt e) k
        rw [TorusFields.supDist_comm] at e2
        omega
      exact hw (b.1 + TorusFields.siteOfInt e, k)
        (interior_of_parentBlock hL le_rfl (hbl (b.1 + TorusFields.siteOfInt e) (by omega)))
        (interior_of_parentBlock hL le_rfl (hbl _ hv1))
  unfold markedSet markedBadBonds
  simp only [Finset.mem_filter, StepSettings.markedBonds, hmark, hξ, hhull]
private theorem exists_not_mem_cell (G : CellGrid) {m : ℕ} [NeZero m] (hG : G.Compatible m) (κ : Fin 4 → ℤ) :
    ∃ w, w ∉ G.cell m κ := by
  classical
  refine ⟨TorusFields.siteOfInt fun i => G.offset i + (G.side : ℤ) * κ i + G.side, fun hw => ?_⟩
  unfold CellGrid.cell at hw
  obtain ⟨h, hb, he⟩ := (Finset.mem_filter.1 hw).2
  have h0 := congrFun he 0
  simp only [TorusFields.siteOfInt] at h0
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h0
  have e1 : (G.offset 0 + (G.side : ℤ) * κ 0 + h 0) - (G.offset 0 + (G.side : ℤ) * κ 0 + G.side) =
      -((G.side : ℤ) - h 0) := by ring
  rw [e1, dvd_neg] at h0
  have hb0 := hb 0
  have hle := Int.le_of_dvd (by omega) h0
  have hdvd := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne m)) hG.two_mul_side_dvd
  have := hG.side_pos
  omega
private theorem le_clusterRange {x : ℝ} {N : ℕ} (h : (N : ℝ) ^ 100 ≤ x) : N ≤ TorusLumps.clusterRange x := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.NearPotentialBound.le_clusterRange_of_pow_le <;> assumption
end Marks
end ChainLocality
open ChainLocality in
theorem chainLocalityStatement_holds (hframe : FrameLocality.FrameCoordLocal)
    (hblocks : TorusLumps.BlockDataIsLocal) : chainLocalityStatement := by
  intro a _
  refine ⟨0, fun _ => 1, fun _ => one_pos, ?_⟩
  intro L _ _ Tb _ _ hdrawn _
  refine ⟨max Tb.floorMin (((2 ^ 16 + Tb.side : ℕ) : ℝ) ^ 100), ?_⟩
  intro y hy _ _ T S β k hrun hS
  have hfit := hdrawn.fits y ((le_max_left _ _).trans hy)
  have hyL := (le_max_right _ _).trans hy
  have hfloor : ∀ s, s ≤ k → 2 ^ 16 + (Tb.stepParameters y).side ≤ stageRange T s := fun s hs =>
    le_clusterRange (hyL.trans (hrun.onFamily.onFamily s hs).le_coupling)
  have hL8 : 8 ≤ (Tb.stepParameters y).side := by
    have := hfit.L_ge
    omega
  have hodd := hfit.L_odd
  have hfl : ∀ s, s ≤ k → 2 ^ 15 + 2 + (Tb.stepParameters y).side + 9 ≤ stageRange T s := fun s hs => by
    have := hfloor s hs
    omega
  refine ⟨?_, ?_, ?_⟩
  · intro s hs m _ G κ _ U U' ξ ξ' hU hξ
    have hf := sampledField_agree T S hS hL8 s m (G.cell m κ) U U' ξ ξ' hU hξ
    exact ⟨hf, fun z hz => hot_iff_of_agree _ hodd hf (hfl s hs) hz⟩
  · intro m _ G κ _ U U' hU z hz
    exact hull_iff_of_agree _ hodd (AgreeInInterior.of_agreeOn hU) (hfl 0 (Nat.zero_le _)) hz
  · intro s hs m _ G κ hG U U' ξ ξ' hU hξ
    have hV := sampledField_agree T S hS hL8 (s + 1) m (G.cell m κ) U U' ξ ξ' hU hξ
    have hW := sampledField_agree T S hS hL8 s (m * (Tb.stepParameters y).side)
      (TorusLumps.sitesInBlocks (Tb.stepParameters y).side (G.cell m κ)) U U' ξ.1 ξ'.1 hU hξ.1
    have hhull : ∀ z ∈ interiorAtDepth (4 * stageRange T (s + 1)) (G.cell m κ),
        (z ∈ StepSettings.hotCoreSites (T.stage s).toStepSetup (sampleChain T S (s + 1) m U ξ).2.2.1 ↔
          z ∈ StepSettings.hotCoreSites (T.stage s).toStepSetup (sampleChain T S (s + 1) m U' ξ').2.2.1) :=
      fun z hz => hull_iff_of_agree _ hodd hV (hfl (s + 1) hs) hz
    refine ⟨hhull, fun b hb => ?_⟩
    have hy' : TorusLumps.parentBlock (Tb.stepParameters y).side b.1 ∈
        interiorAtDepth (blockDepth T k s) (G.cell m κ) := mem_sitesInBlocks.1 hb
    have hy4 : TorusLumps.parentBlock (Tb.stepParameters y).side b.1 ∈
        interiorAtDepth (4 * stageRange T (s + 1)) (G.cell m κ) :=
      interior_mono (le_max_left _ _) hy'
    obtain ⟨w, hw⟩ := exists_not_mem_cell G hG κ
    have h1 := (ChainLocality.mem_interior.1 hy4).2 w hw
    have h2 := SettingShifts.two_mul_supDist_le (TorusLumps.parentBlock (Tb.stepParameters y).side b.1) w
    have hst := (hrun.onFamily.onFamily s hs.le).isStep.2.2
    have hrs := hfloor s hs.le
    have hrs' := hfloor (s + 1) hs
    have e0 : (T.stage s).toStepSetup.range = stageRange T s := rfl
    have e1 : (T.stage s).toStepSetup.nextRange = stageRange T (s + 1) := rfl
    have e2 : (T.stage s).toStepSetup.frameReach = stageRange T s / 2 ^ 11 := rfl
    rw [e0, e1] at hst
    have hm0 : 0 < (T.stage s).toStepSetup.frameReach := by
      rw [e2]
      omega
    have hm2 : 4 * (T.stage s).toStepSetup.frameReach + 5 < m := by
      rw [e2]
      omega
    have h16 : 16 ≤ m := by omega
    have hD : (T.stage s).toStepSetup.frameReach + 9 ≤ 4 * stageRange T (s + 1) := by
      rw [e2]
      omega
    have hnext : TorusLumps.parentBlock (Tb.stepParameters y).side (b.1 + TorusFields.unitStep _ b.2) ∈
        G.cell m κ := by
      have d1 := TorusBalls.supDist_parentBlock_le_div_add_one (Tb.stepParameters y).side
        (b.1 + TorusFields.unitStep _ b.2) b.1
      have d2 := TorusFields.supDist_add_unitStep_le b.1 b.2
      rw [TorusFields.supDist_comm] at d2
      have d3 : TorusFields.supDist (b.1 + TorusFields.unitStep _ b.2) b.1 / (Tb.stepParameters y).side = 0 :=
        Nat.div_eq_of_lt (by omega)
      exact (ChainLocality.mem_interior.1 (interior_of_near (A := 1) (d := 1) (by norm_num)
        (interior_mono (by omega) hy4) (by omega))).1
    have hξ' := hξ.2.2.2 b (mem_sitesInBlocks.2 (ChainLocality.mem_interior.1 hy').1) (mem_sitesInBlocks.2 hnext)
    exact mem_markedSet_iff hframe hblocks (R := (T.stage s).toStepSetup) hfit
      (V := (sampleChain T S (s + 1) m U ξ).2.2.1) (V' := (sampleChain T S (s + 1) m U' ξ').2.2.1)
      (ξ := ξ.2) (ξ' := ξ'.2) b hW hV h16 hm0 hm2 hD hy4 (hhull _ hy4) hξ'
end YangMills.Construction.CellWindows
end
