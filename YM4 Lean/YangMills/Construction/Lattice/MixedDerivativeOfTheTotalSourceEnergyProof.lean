import YangMills.Construction.ComplexAnalysis.HolomorphicFunctionsOfSeveralVariables
import YangMills.Construction.Functions.CauchyInequalityForTheMixedDerivativeAlongCoordinates
import YangMills.Construction.Lattice.LocalisationDomainsThroughACube
import YangMills.Construction.Lattice.MixedDerivativeOfTheTotalSourceEnergy
import YangMills.Construction.Lattice.SidesOfTheCubesAndTheLinearSize
import YangMills.Construction.Lattice.SourceDiscAndSourceClass
import YangMills.Construction.Lattice.SublevelSetsAndSourceDiscs
import YangMills.Construction.Lattice.TreeOfALocalisationDomain
import YangMills.Construction.Lattice.WhatADomainOfTheTorusBoundSees
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.TotalEnergyDerivative.Estimates
open Set TorusBound PolymerActivities.DomainCounting ComplexVariables TorusBoundNotation
open scoped ENNReal
noncomputable section
variable {n : ℕ}
theorem isHolomorphicScalar_const_zero {O : Set (Coordinates.ComplexCoordinates n)} (hO : IsOpen O) :
    IsHolomorphicScalar O fun _ => (0 : ℂ) :=
  ⟨hO, continuousOn_const, fun _ _ _ =>
    Filter.Eventually.of_forall fun _ => differentiableAt_const _⟩
theorem isHolomorphicScalar_finset_sum
    (hH : SeveralComplexVariables.HolomorphicCalculusRules) (hn : 1 ≤ n)
    {O : Set (Coordinates.ComplexCoordinates n)} (hO : IsOpen O) {ι : Type*} (s : Finset ι)
    (F : ι → Coordinates.ComplexCoordinates n → ℂ) (hF : ∀ a ∈ s, IsHolomorphicScalar O (F a)) :
    IsHolomorphicScalar O fun z => ∑ a ∈ s, F a z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isHolomorphicScalar_const_zero hO
  | insert a s ha ih =>
    have hs := ih fun b hb => hF b (Finset.mem_insert_of_mem hb)
    have ha' := hF a (Finset.mem_insert_self a s)
    obtain ⟨⟨h1, -, -⟩, -⟩ := hH n hn O hO (F a) _ ha' hs
    have h2 := h1 1
    simpa [Finset.sum_insert ha] using h2
theorem mixedDeriv_finset_sum (hH : SeveralComplexVariables.HolomorphicCalculusRules) (hn : 1 ≤ n)
    {O : Set (Coordinates.ComplexCoordinates n)} (hO : IsOpen O) {ι : Type*} (s : Finset ι)
    (F : ι → Coordinates.ComplexCoordinates n → ℂ) (hF : ∀ a ∈ s, IsHolomorphicScalar O (F a)) :
    EqOn (mixedDeriv fun z => ∑ a ∈ s, F a z) (fun z => ∑ a ∈ s, mixedDeriv (F a) z) O := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro z hz
    have h0 := isHolomorphicScalar_const_zero hO
    obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := hH n hn O hO _ _ h0 h0
    have := (h9 ⟨0, hn⟩ fun _ _ _ _ _ => rfl).2 hz
    simpa using this
  | insert a s ha ih =>
    have hs' := fun b hb => hF b (Finset.mem_insert_of_mem hb)
    have hs := isHolomorphicScalar_finset_sum hH hn hO s F hs'
    have ha' := hF a (Finset.mem_insert_self a s)
    obtain ⟨-, -, -, -, -, -, -, ⟨h8, -⟩, -, -⟩ := hH n hn O hO (F a) _ ha' hs
    intro z hz
    have hfun : (fun z => ∑ b ∈ insert a s, F b z) = fun z => F a z + 1 * ∑ b ∈ s, F b z := by
      funext z
      rw [Finset.sum_insert ha, one_mul]
    have h := h8 1 hz
    rw [hfun, h]
    beta_reduce
    rw [ih hs' hz, Finset.sum_insert ha, one_mul]
variable {D : Setup} {ϱ : ℝ} {hϱ : 0 < ϱ}
abbrev regionTerm (e : D.RadiusFamily ϱ hϱ) (f : Fin n → D.Torus → ℝ) (hf : D.IsRealFamily f)
    (j : (D.energyDataAt ϱ hϱ).levelSet) (X : (D.energyDataAt ϱ hϱ).domainsAt j) :
    Coordinates.ComplexCoordinates n → ℂ :=
  LocalizedEnergies.EnergyData.EnergyFamily.localEnergyAlong e j X f hf
theorem le_K_of_mem_levelSet (j : (D.energyDataAt ϱ hϱ).levelSet) : (j : ℕ) ≤ (D.K : ℕ) :=
  (D.mem_levelSet_energyDataAt_iff ϱ hϱ j).1 j.2
theorem domainsAt_energyDataAt_eq (j : ℕ) :
    (D.energyDataAt ϱ hϱ).domainsAt j = D.regionsAt j :=
  (Setup.regionsAt_ofEnergyData (D.energyDataAt ϱ hϱ) j).symm
theorem regionsAt_finite (hP : CubeSidesAndLinearSize) {j : ℕ}
    (hj : j ≤ (D.K : ℕ)) : (D.regionsAt j).Finite := by
  by_cases h : D.LevelFits j
  · exact ((hP D j hj).2 h).1.2.2.2.2 .wallConnected
  · rw [Setup.regionsAt, Setup.regionsBy_eq_empty _ h]
    exact finite_empty
theorem regionTerm_isHolomorphicScalar (e : D.RadiusFamily ϱ hϱ) (hA : e.Analytic)
    (f : Fin n → D.Torus → ℝ) (hf : D.IsRealFamily f) (j : (D.energyDataAt ϱ hϱ).levelSet)
    (X : (D.energyDataAt ϱ hϱ).domainsAt j) :
    IsHolomorphicScalar (D.disc ϱ f) (regionTerm e f hf j X) := by
  have h := hA j X n f hf
  have hfun : ((Equiv.funUnique (Fin 1) ℂ).symm ∘ regionTerm e f hf j X) =
      fun ζ _ => LocalizedEnergies.EnergyData.EnergyFamily.localEnergyAlong e j X f hf ζ := by
    funext z i
    simp
  unfold IsHolomorphicScalar
  rw [hfun]
  exact h
theorem regionTerm_of_mem_disc (e : D.RadiusFamily ϱ hϱ) (f : Fin n → D.Torus → ℝ)
    (hf : D.IsRealFamily f)
    (j : (D.energyDataAt ϱ hϱ).levelSet) (X : (D.energyDataAt ϱ hϱ).domainsAt j)
    {z : Coordinates.ComplexCoordinates n} (hz : z ∈ D.disc ϱ f) :
    regionTerm e f hf j X z =
      LocalizedEnergies.EnergyData.EnergyFamily.localEnergy e j X
        ⟨D.smear z f, (D.energyDataAt ϱ hϱ).complexSource_mem_sourceClass hf hz⟩ :=
  dif_pos hz
theorem diskEnergy_eq_sum (e : D.RadiusFamily ϱ hϱ) (f : Fin n → D.Torus → ℝ)
    (hf : D.IsRealFamily f)
    [∀ j : (D.energyDataAt ϱ hϱ).levelSet, Fintype ((D.energyDataAt ϱ hϱ).domainsAt j)] :
    diskEnergy e f hf = fun z =>
      ∑ j : (D.energyDataAt ϱ hϱ).levelSet, ∑ X : (D.energyDataAt ϱ hϱ).domainsAt j,
        regionTerm e f hf j X z := by
  funext z
  by_cases hz : z ∈ D.disc ϱ f
  · rw [diskEnergy_of_mem e f hf hz]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun X _ => ?_
    exact (regionTerm_of_mem_disc e f hf j X hz).symm
  · have h0 : diskEnergy e f hf z = 0 := dif_neg hz
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun X _ => ?_
    exact dif_neg hz
theorem regionTerm_mixedDeriv_eq_zero_of_not_sees
    (hH : SeveralComplexVariables.HolomorphicCalculusRules)
    (hS : SourceDiskAndClass.Statement) (e : D.RadiusFamily ϱ hϱ) (hL : e.Local)
    (hA : e.Analytic) (f : Fin n → D.Torus → ℝ) (hf : D.IsRealFamily f)
    (j : (D.energyDataAt ϱ hϱ).levelSet) (X : (D.energyDataAt ϱ hϱ).domainsAt j) (l : Fin n)
    (hsee : ¬D.SeesSupport j X.1 (f l)) :
    mixedDeriv (regionTerm e f hf j X) 0 = 0 := by
  obtain ⟨-, -, hO, -, -, h0, -, -⟩ := hS D f ϱ hf hϱ
  have hol := regionTerm_isHolomorphicScalar e hA f hf j X
  obtain ⟨-, -, -, -, -, -, -, -, h9, -⟩ := hH n hf.1 _ hO _ _ hol hol
  refine (h9 l fun z hz z' hz' hzz => ?_).2 h0
  rw [regionTerm_of_mem_disc e f hf j X hz, regionTerm_of_mem_disc e f hf j X hz']
  refine (hL j X).1 _ _ fun p hp => ?_
  have hzero : f l p.barycenter = 0 := by
    by_contra hne
    exact hsee ⟨p, hp, hne⟩
  change (∑ i, z i * (f i p.barycenter : ℂ)) = ∑ i, z' i * (f i p.barycenter : ℂ)
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i = l
  · subst hi
    simp [hzero]
  · rw [hzz i hi]
theorem norm_regionTerm_mixedDeriv_le (hC : CauchyEstimates.MixedDerivCauchyBound)
    (hD : SublevelSets.SublevelAndDiskStatement) (hS : SourceDiskAndClass.Statement)
    (e : D.RadiusFamily ϱ hϱ) (hA : e.Analytic) {Ce κe : ℝ} (hCe : 0 ≤ Ce)
    (hB : e.ExpBounded Ce κe) (f : Fin n → D.Torus → ℝ) (hf : D.IsRealFamily f)
    (j : (D.energyDataAt ϱ hϱ).levelSet) (X : (D.energyDataAt ϱ hϱ).domainsAt j)
    (hsee : ∀ l, D.SeesSupport j X.1 (f l)) :
    ‖mixedDeriv (regionTerm e f hf j X) 0‖ ≤
      Ce * Real.exp (-κe * D.extent j X.1) * sharpNormFactor D ϱ f := by
  have hpos : ∀ l, 0 < D.sharpNorm (f l) := by
    intro l
    obtain ⟨p, -, hp⟩ := hsee l
    obtain ⟨-, -, -, hnn, hz⟩ := (hS D f ϱ hf hϱ).1 l
    exact lt_of_le_of_ne hnn fun h => hp (hz h.symm _)
  obtain ⟨a, -, hdisc, -, hprod⟩ := hD.2 D n f ϱ hf hpos hϱ
  have hol := regionTerm_isHolomorphicScalar e hA f hf j X
  rw [hdisc] at hol
  have h := hC.2 n a (regionTerm e f hf j X) (Ce * Real.exp (-κe * D.extent j X.1)) hol
    (mul_nonneg hCe (Real.exp_pos _).le) fun z hz => by
      have hz' : z ∈ D.disc ϱ f := hdisc ▸ hz
      rw [regionTerm_of_mem_disc e f hf j X hz']
      exact hB.2.2 j X _
  rw [mul_assoc, hprod] at h
  exact h
theorem physicalCubeSide_eq (D : Setup) {j : ℕ} (hj : j ≤ (D.K : ℕ)) :
    D.physicalCubeSide j = (D.cubeSide : ℝ) / (D.L : ℝ) ^ ((D.K : ℕ) - j) := by
  have hdepth : D.depthOf j = (((D.K : ℕ) - j : ℕ) : ℤ) := by
    simp only [Setup.depthOf, PeriodicLattice.levelDepth]
    omega
  rw [Setup.physicalCubeSide, hdepth, PeriodicLattice.meshSize, zpow_neg, zpow_natCast,
    div_eq_mul_inv]
theorem L_cast_pos (D : Setup) : (0 : ℝ) < (D.L : ℝ) := by
  have := D.isAdmissible.2
  exact_mod_cast (by omega : 0 < D.L)
theorem cubeSide_cast_pos (D : Setup) : (0 : ℝ) < (D.cubeSide : ℝ) := by
  have := L_cast_pos D
  simp only [Setup.cubeSide, Nat.cast_pow]
  positivity
theorem extent_nonneg (D : Setup) (j : ℕ) (X : Set D.Torus) : 0 ≤ D.extent j X := by
  unfold Setup.extent PeriodicLattice.linearExtent
  positivity
def extentFloor (D : Setup) (d : ℝ) (j : ℕ) : ℝ :=
  plusPart (d * (D.L : ℝ) ^ ((D.K : ℕ) - j) / (D.cubeSide : ℝ) - 10)
theorem extentFloor_le (hT : LocalisationDomainTreeClaim) {f : Fin n → D.Torus → ℝ}
    {d : ℝ} (hd : TestFunctions.HasSeparatedSupportsTorus f d) (hn : 2 ≤ n) {j : ℕ}
    (hj : j ≤ (D.K : ℕ)) (h : D.LevelFits j) {X : Set D.Torus} (hX : X ∈ D.regionsAt j)
    (hsee : ∀ l, D.SeesSupport j X (f l)) : extentFloor D d j ≤ D.extent j X := by
  obtain ⟨p₁, hp₁, hx₁⟩ := hsee ⟨0, by omega⟩
  obtain ⟨p₂, hp₂, hx₂⟩ := hsee ⟨1, by omega⟩
  have hlt := (hT D j hj h .wallConnected X hX).2.1 p₁ hp₁ p₂ hp₂
  have hsep := hd.2 ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])
  have hinf : TorusMetric.setEuclidDist (tsupport (f ⟨0, by omega⟩)) (tsupport (f ⟨1, by omega⟩)) ≤
      ENNReal.ofReal (TorusMetric.torusEuclidNorm (p₁.barycenter - p₂.barycenter)) :=
    iInf₂_le_of_le _ (subset_tsupport _ hx₁) (iInf₂_le_of_le _ (subset_tsupport _ hx₂) le_rfl)
  have hdle : d ≤ TorusMetric.torusEuclidNorm (p₁.barycenter - p₂.barycenter) := by
    rcases ENNReal.ofReal_le_ofReal_iff'.1 (hsep.trans hinf) with h' | h'
    · exact h'
    · exact absurd hd.1 (not_lt.2 h')
  have hL := L_cast_pos D
  have hM := cubeSide_cast_pos D
  have hLs : 0 < (D.L : ℝ) ^ ((D.K : ℕ) - j) := pow_pos hL _
  rw [physicalCubeSide_eq D hj] at hlt
  have hlt' : d < (D.extent j X + 10) * ((D.cubeSide : ℝ) / (D.L : ℝ) ^ ((D.K : ℕ) - j)) :=
    lt_of_le_of_lt hdle hlt
  have hq : d * (D.L : ℝ) ^ ((D.K : ℕ) - j) / (D.cubeSide : ℝ) < D.extent j X + 10 := by
    rw [div_lt_iff₀ hM]
    rw [mul_div_assoc', lt_div_iff₀ hLs] at hlt'
    exact hlt'
  exact max_le (by linarith) (extent_nonneg D j X)
theorem sum_norm_mixedDeriv_level_le (hC : CauchyEstimates.MixedDerivCauchyBound)
    (hDisc : SublevelSets.SublevelAndDiskStatement) (hS : SourceDiskAndClass.Statement)
    (hH : SeveralComplexVariables.HolomorphicCalculusRules)
    (hP : CubeSidesAndLinearSize) (hN : RegionsThroughCube.CountAndTailBound)
    (hT : LocalisationDomainTreeClaim) (e : D.RadiusFamily ϱ hϱ) (hL : e.Local)
    (hA : e.Analytic) {Ce κe : ℝ} (hCe : 0 ≤ Ce) (hκe : countingRate < κe)
    (hB : e.ExpBounded Ce κe) (f : Fin n → D.Torus → ℝ) (hf : D.IsRealFamily f)
    {d : ℝ} (hd : TestFunctions.HasSeparatedSupportsTorus f d) (hn : 2 ≤ n)
    (hBF : 0 ≤ sharpNormFactor D ϱ f)
    (j : (D.energyDataAt ϱ hϱ).levelSet) (h : D.LevelFits j)
    [Fintype ((D.energyDataAt ϱ hϱ).domainsAt j)]
    (N : Set (Set D.Torus)) (hNfin : N.Finite) (hNsub : N ⊆ D.cubesAt j)
    (hcover : ∀ X ∈ D.regionsAt j, (∀ l, D.SeesSupport j X (f l)) → ∃ Q ∈ N, Q ⊆ X) :
    ∑ X : (D.energyDataAt ϱ hϱ).domainsAt j,
        ‖mixedDeriv (regionTerm e f hf j X) 0‖ ≤
      (N.ncard : ℝ) * rateSum κe * Real.exp (-(κe - countingRate) * extentFloor D d j) *
        (Ce * sharpNormFactor D ϱ f) := by
  classical
  have hj := le_K_of_mem_levelSet j
  have hfin : (D.regionsAt j).Finite := regionsAt_finite hP hj
  set g : Set D.Torus → ℝ := fun Y => Real.exp (-κe * D.extent j Y) with hg
  have hg0 : ∀ Y, 0 ≤ g Y := fun Y => (Real.exp_pos _).le
  set Dj := extentFloor D d j with hDj
  have hDj0 : 0 ≤ Dj := le_max_right _ _
  let AllSee : Set D.Torus → Prop := fun Y => ∀ l, D.SeesSupport j Y (f l)
  let T : Set D.Torus → Set (Set D.Torus) := fun Q =>
    {X | X ∈ D.regionsContaining .wallConnected j Q ∧ Dj ≤ D.extent j X}
  have hTsub : ∀ Q, T Q ⊆ D.regionsAt j := fun Q X hX => hX.1.1
  have hTfin : ∀ Q, (T Q).Finite := fun Q => hfin.subset (hTsub Q)
  have hmem : ∀ Y, Y ∈ hfin.toFinset ↔ Y ∈ (D.energyDataAt ϱ hϱ).domainsAt j := by
    intro Y
    rw [Set.Finite.mem_toFinset, domainsAt_energyDataAt_eq]
  have hterm : ∀ X : (D.energyDataAt ϱ hϱ).domainsAt j,
      ‖mixedDeriv (regionTerm e f hf j X) 0‖ ≤
        Ce * sharpNormFactor D ϱ f * (if AllSee X.1 then g X.1 else 0) := by
    intro X
    by_cases hs : AllSee X.1
    · rw [if_pos hs]
      have := norm_regionTerm_mixedDeriv_le hC hDisc hS e hA hCe hB f hf j X hs
      calc _ ≤ _ := this
        _ = _ := by simp only [hg]; ring
    · rw [if_neg hs, mul_zero]
      obtain ⟨l, hl⟩ := not_forall.1 hs
      rw [regionTerm_mixedDeriv_eq_zero_of_not_sees hH hS e hL hA f hf j X l hl, norm_zero]
  have hsum₁ : ∑ X : (D.energyDataAt ϱ hϱ).domainsAt j,
      ‖mixedDeriv (regionTerm e f hf j X) 0‖ ≤
        Ce * sharpNormFactor D ϱ f * ∑ Y ∈ hfin.toFinset, if AllSee Y then g Y else 0 := by
    rw [Finset.sum_subtype hfin.toFinset hmem (fun Y => if AllSee Y then g Y else 0),
      Finset.mul_sum]
    exact Finset.sum_le_sum fun X _ => hterm X
  have hsum₂ : ∑ Y ∈ hfin.toFinset, (if AllSee Y then g Y else 0) ≤
      ∑ Y ∈ hfin.toFinset, ∑ Q ∈ hNfin.toFinset, if Y ∈ T Q then g Y else 0 := by
    refine Finset.sum_le_sum fun Y hY => ?_
    have hY' : Y ∈ D.regionsAt j := by simpa using hY
    by_cases hs : AllSee Y
    · rw [if_pos hs]
      obtain ⟨Q, hQ, hQY⟩ := hcover Y hY' hs
      have hYT : Y ∈ T Q := ⟨⟨hY', hQY⟩, extentFloor_le hT hd hn hj h hY' hs⟩
      have hle := Finset.single_le_sum (f := fun Q => if Y ∈ T Q then g Y else 0)
        (fun Q _ => by
          split_ifs
          · exact hg0 Y
          · exact le_rfl) (hNfin.mem_toFinset.2 hQ)
      simpa [hYT] using hle
    · rw [if_neg hs]
      refine Finset.sum_nonneg fun Q _ => ?_
      split_ifs
      · exact hg0 Y
      · exact le_rfl
  have hQ : ∀ Q ∈ hNfin.toFinset,
      ∑ Y ∈ hfin.toFinset, (if Y ∈ T Q then g Y else 0) ≤
        rateSum κe * Real.exp (-(κe - countingRate) * Dj) := by
    intro Q hQ
    have hQ' : Q ∈ D.cubesAt j := hNsub (hNfin.mem_toFinset.1 hQ)
    have hcount := ((hN D .wallConnected j hj h Q hQ').2 κe Dj hκe hDj0)
    rw [finsum_mem_eq_finite_toFinset_sum _ (hTfin Q)] at hcount
    have heq : ∑ Y ∈ hfin.toFinset, (if Y ∈ T Q then g Y else 0) =
        ∑ Y ∈ (hTfin Q).toFinset, g Y := by
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext Y
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨fun hY => hY.2, fun hY => ⟨hTsub Q hY, hY⟩⟩
    rw [heq]
    exact hcount
  have hsum₃ : ∑ Y ∈ hfin.toFinset, (if AllSee Y then g Y else 0) ≤
      (N.ncard : ℝ) * (rateSum κe * Real.exp (-(κe - countingRate) * Dj)) := by
    refine hsum₂.trans ?_
    rw [Finset.sum_comm]
    refine (Finset.sum_le_sum hQ).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card N hNfin]
  have hCB : 0 ≤ Ce * sharpNormFactor D ϱ f := mul_nonneg hCe hBF
  calc _ ≤ _ := hsum₁
    _ ≤ Ce * sharpNormFactor D ϱ f *
        ((N.ncard : ℝ) * (rateSum κe * Real.exp (-(κe - countingRate) * Dj))) :=
      mul_le_mul_of_nonneg_left hsum₃ hCB
    _ = _ := by ring
theorem ofReal_norm_mixedDeriv_le_tsum (hH : SeveralComplexVariables.HolomorphicCalculusRules)
    (hS : SourceDiskAndClass.Statement)
    (e : D.RadiusFamily ϱ hϱ) (hA : e.Analytic) (f : Fin n → D.Torus → ℝ)
    (hf : D.IsRealFamily f)
    [∀ j : (D.energyDataAt ϱ hϱ).levelSet, Fintype ((D.energyDataAt ϱ hϱ).domainsAt j)]
    (P : ℝ) (hP0 : 0 ≤ P) (W : ℕ → ℝ) (hW : ∀ s, 0 ≤ W s)
    (hlevel : ∀ j : (D.energyDataAt ϱ hϱ).levelSet, D.LevelFits j →
      ∑ X : (D.energyDataAt ϱ hϱ).domainsAt j,
          ‖mixedDeriv (regionTerm e f hf j X) 0‖ ≤ P * W ((D.K : ℕ) - j)) :
    ENNReal.ofReal ‖mixedDeriv (diskEnergy e f hf) 0‖ ≤
      ENNReal.ofReal P * ∑' s : ℕ, ENNReal.ofReal (W s) := by
  obtain ⟨-, -, hO, -, -, h0, -, -⟩ := hS D f ϱ hf hϱ
  have hn : 1 ≤ n := hf.1
  have hterm := regionTerm_isHolomorphicScalar e hA f hf
  have hG : ∀ j : (D.energyDataAt ϱ hϱ).levelSet,
      IsHolomorphicScalar (D.disc ϱ f) fun z =>
        ∑ X : (D.energyDataAt ϱ hϱ).domainsAt j, regionTerm e f hf j X z := fun j =>
    isHolomorphicScalar_finset_sum hH hn hO Finset.univ _ fun X _ => hterm j X
  have hm : mixedDeriv (diskEnergy e f hf) 0 =
      ∑ j : (D.energyDataAt ϱ hϱ).levelSet, ∑ X : (D.energyDataAt ϱ hϱ).domainsAt j,
        mixedDeriv (regionTerm e f hf j X) 0 := by
    rw [diskEnergy_eq_sum e f hf,
      mixedDeriv_finset_sum hH hn hO Finset.univ _ (fun j _ => hG j) h0]
    exact Finset.sum_congr rfl fun j _ =>
      mixedDeriv_finset_sum hH hn hO Finset.univ _ (fun X _ => hterm j X) h0
  have hreal : ‖mixedDeriv (diskEnergy e f hf) 0‖ ≤
      ∑ j : (D.energyDataAt ϱ hϱ).levelSet, P * W ((D.K : ℕ) - j) := by
    rw [hm]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (norm_sum_le _ _).trans ?_
    by_cases h : D.LevelFits j
    · exact hlevel j h
    · have hempty : IsEmpty ((D.energyDataAt ϱ hϱ).domainsAt j) := by
        rw [domainsAt_energyDataAt_eq, Setup.regionsAt, Setup.regionsBy_eq_empty _ h]
        exact Set.isEmpty_coe_sort.2 rfl
      rw [Finset.univ_eq_empty, Finset.sum_empty]
      exact mul_nonneg hP0 (hW _)
  have hinj : Function.Injective fun j : (D.energyDataAt ϱ hϱ).levelSet => (D.K : ℕ) - j := by
    intro a b hab
    have ha := le_K_of_mem_levelSet a
    have hb := le_K_of_mem_levelSet b
    have hab' : (D.K : ℕ) - a = (D.K : ℕ) - b := hab
    exact Subtype.ext (by omega)
  calc ENNReal.ofReal ‖mixedDeriv (diskEnergy e f hf) 0‖
      ≤ ENNReal.ofReal (∑ j : (D.energyDataAt ϱ hϱ).levelSet, P * W ((D.K : ℕ) - j)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ∑ j : (D.energyDataAt ϱ hϱ).levelSet,
        ENNReal.ofReal P * ENNReal.ofReal (W ((D.K : ℕ) - j)) := by
        rw [ENNReal.ofReal_sum_of_nonneg fun j _ => mul_nonneg hP0 (hW _)]
        exact Finset.sum_congr rfl fun j _ => ENNReal.ofReal_mul hP0
    _ = ENNReal.ofReal P *
        ∑ j : (D.energyDataAt ϱ hϱ).levelSet, ENNReal.ofReal (W ((D.K : ℕ) - j)) :=
        Finset.mul_sum _ _ _ |>.symm
    _ ≤ ENNReal.ofReal P * ∑' s : ℕ, ENNReal.ofReal (W s) := by
        gcongr
        have h1 := ENNReal.tsum_comp_le_tsum_of_injective hinj fun s => ENNReal.ofReal (W s)
        exact le_trans (le_of_eq (tsum_fintype _).symm) h1
theorem exists_cube_subset_of_seesSupport (hP : CubeSidesAndLinearSize) {j : ℕ}
    (hj : j ≤ (D.K : ℕ)) (h : D.LevelFits j) {X : Set D.Torus} (hX : X ∈ D.regionsAt j)
    {g : D.Torus → ℝ} (hsee : D.SeesSupport j X g) : ∃ Q ∈ D.cubesAt j, Q ⊆ X := by
  obtain ⟨p, hp, -⟩ := hsee
  obtain ⟨Q, hQ⟩ := (((hP D j hj).2 h).2 .wallConnected X hX).2 ⟨p, hp⟩
  exact ⟨Q, hQ.1, hQ.2⟩
theorem mixedDerivBound_holds (hH : SeveralComplexVariables.HolomorphicCalculusRules)
    (hS : SourceDiskAndClass.Statement) (hDisc : SublevelSets.SublevelAndDiskStatement)
    (hC : CauchyEstimates.MixedDerivCauchyBound)
    (hP : CubeSidesAndLinearSize) (hN : RegionsThroughCube.CountAndTailBound)
    (hT : LocalisationDomainTreeClaim) : MixedDerivBound := by
  classical
  intro D ϱ hϱ Ce κe hCe hκe e hL hA hB n f hf
  have hfinite : ∀ j : (D.energyDataAt ϱ hϱ).levelSet,
      Finite ((D.energyDataAt ϱ hϱ).domainsAt j) := by
    intro j
    rw [domainsAt_energyDataAt_eq]
    exact (regionsAt_finite hP (le_K_of_mem_levelSet j)).to_subtype
  let _ : ∀ j : (D.energyDataAt ϱ hϱ).levelSet,
      Fintype ((D.energyDataAt ϱ hϱ).domainsAt j) := fun j =>
    haveI := hfinite j
    Fintype.ofFinite _
  obtain ⟨hnorm, -, hO, -, -, h0, -, -⟩ := hS D f ϱ hf hϱ
  have hn1 : 1 ≤ n := hf.1
  have hBF : 0 ≤ sharpNormFactor D ϱ f :=
    mul_nonneg (pow_nonneg (div_nonneg (Nat.cast_nonneg _) hϱ.le) _)
      (Finset.prod_nonneg fun i _ => (hnorm i).2.2.2.1)
  have hside : 0 ≤ D.side ^ 4 := Even.pow_nonneg (by decide) _
  set c := ConstantParameters.ofSetup D Ce κe 0 0 hCe hκe with hc
  have hSpos : 0 < rateSum κe := c.rateSum_pos
  refine ⟨?_, ?_, fun hn d hd => ⟨?_, fun R hR hball => ?_⟩⟩
  · rw [diskEnergy_eq_sum e f hf]
    exact isHolomorphicScalar_finset_sum hH hn1 hO Finset.univ _ fun j _ =>
      isHolomorphicScalar_finset_sum hH hn1 hO Finset.univ _ fun X _ =>
        regionTerm_isHolomorphicScalar e hA f hf j X
  · rw [diskEnergy_eq_sum e f hf]
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun X _ => ?_
    rw [regionTerm_of_mem_disc e f hf j X h0]
    have hzero : (⟨D.smear 0 f, (D.energyDataAt ϱ hϱ).complexSource_mem_sourceClass hf h0⟩ :
        (D.energyDataAt ϱ hϱ).sourceClass) = (D.energyDataAt ϱ hϱ).zeroSource := by
      refine Subtype.ext ?_
      funext x
      simp [PeriodicLattice.complexSource, LocalizedEnergies.EnergyData.zeroSource]
    rw [hzero]
    exact (hL j X).2
  · have hlevel : ∀ j : (D.energyDataAt ϱ hϱ).levelSet, D.LevelFits j →
        ∑ X : (D.energyDataAt ϱ hϱ).domainsAt j,
            ‖mixedDeriv (regionTerm e f hf j X) 0‖ ≤
          D.side ^ 4 * c.prefactor * sharpNormFactor D ϱ f * c.volumeTerm d ((D.K : ℕ) - j) := by
      intro j h
      have hj := le_K_of_mem_levelSet j
      obtain ⟨-, -, hpfin, hcard, -⟩ := ((hP D j hj).2 h).1
      have hb := sum_norm_mixedDeriv_level_le hC hDisc hS hH hP hN hT e hL hA hCe hκe hB f hf
        hd hn hBF j h (D.cubesAt j) hpfin subset_rfl fun X hX hs =>
          exists_cube_subset_of_seesSupport hP hj h hX (hs ⟨0, by omega⟩)
      refine hb.trans ?_
      have hdec : Real.exp (-(κe - countingRate) * extentFloor D d j) =
          c.decayFactor d ((D.K : ℕ) - j) := rfl
      have hM := cubeSide_cast_pos D
      have hLs : 0 < (D.L : ℝ) ^ ((D.K : ℕ) - j) := pow_pos (L_cast_pos D) _
      have hcard' : ((D.cubesAt j).ncard : ℝ) =
          D.side ^ 4 * ((D.L : ℝ) ^ ((D.K : ℕ) - j) / (D.cubeSide : ℝ)) ^ 4 := by
        rw [hcard]
        change (D.side / D.physicalCubeSide j) ^ 4 = _
        rw [physicalCubeSide_eq D hj, ← mul_pow]
        congr 1
        field_simp
      have hvol : c.volumeTerm d ((D.K : ℕ) - j) =
          ((D.L : ℝ) ^ ((D.K : ℕ) - j) / (D.cubeSide : ℝ)) ^ 4 *
            c.decayFactor d ((D.K : ℕ) - j) := rfl
      have hpre : c.prefactor = (Ce + 1) * rateSum κe := rfl
      rw [hdec, hcard', hvol, hpre]
      have hdec0 : 0 ≤ c.decayFactor d ((D.K : ℕ) - j) := (Real.exp_pos _).le
      have hX0 : 0 ≤ D.side ^ 4 * ((D.L : ℝ) ^ ((D.K : ℕ) - j) / (D.cubeSide : ℝ)) ^ 4 *
          rateSum κe * c.decayFactor d ((D.K : ℕ) - j) * sharpNormFactor D ϱ f := by
        have h4 : 0 ≤ ((D.L : ℝ) ^ ((D.K : ℕ) - j) / (D.cubeSide : ℝ)) ^ 4 :=
          Even.pow_nonneg (by decide) _
        exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hside h4) hSpos.le) hdec0) hBF
      nlinarith [hX0]
    have htotal := ofReal_norm_mixedDeriv_le_tsum hH hS e hA f hf _
      (mul_nonneg (mul_nonneg hside c.prefactor_pos.le) hBF) (c.volumeTerm d)
      (c.volumeTerm_nonneg d) hlevel
    refine htotal.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (mul_nonneg hside c.prefactor_pos.le), ENNReal.ofReal_mul hside,
      ConstantParameters.uvConstant]
    ring
  · obtain ⟨Bl, ⟨y₀, rfl⟩, hvan⟩ := hball
    have hlevel : ∀ j : (D.energyDataAt ϱ hϱ).levelSet, D.LevelFits j →
        ∑ X : (D.energyDataAt ϱ hϱ).domainsAt j,
            ‖mixedDeriv (regionTerm e f hf j X) 0‖ ≤
          Ce * rateSum κe * sharpNormFactor D ϱ f * c.ballTerm d R ((D.K : ℕ) - j) := by
      intro j h
      have hj := le_K_of_mem_levelSet j
      have hBT := c.ballTerm_nonneg d R ((D.K : ℕ) - j)
      rcases isEmpty_or_nonempty ((D.energyDataAt ϱ hϱ).domainsAt j) with hemp | ⟨⟨X₀, hX₀⟩⟩
      · rw [Finset.univ_eq_empty, Finset.sum_empty]
        exact mul_nonneg (mul_nonneg (mul_nonneg hCe hSpos.le) hBF) hBT
      have hX₀' : X₀ ∈ D.regionsAt j := by rwa [domainsAt_energyDataAt_eq] at hX₀
      obtain ⟨-, hNfin, hNcard⟩ :=
        (hT D j hj h .wallConnected X₀ hX₀').2.2 y₀ R hR
      have hNcard' := hNcard c rfl rfl
      have hb := sum_norm_mixedDeriv_level_le hC hDisc hS hH hP hN hT e hL hA hCe hκe hB f hf
        hd hn hBF j h (D.cubesCentredNear j y₀ (D.ballReach j R)) hNfin
        (by
          rintro Q ⟨a, rfl, -⟩
          exact ⟨a, rfl⟩)
        (fun X hX hs => by
          obtain ⟨p, hp, hx⟩ := hs ⟨0, by omega⟩
          have hin : p.barycenter ∈ D.ball y₀ R := by
            by_contra hout
            exact hx (hvan _ hout)
          obtain ⟨a, ha, hsup⟩ :=
            ((hT D j hj h .wallConnected X hX).2.2 y₀ R hR).1 ⟨p, hp, hin⟩
          exact ⟨D.cubeCentredAt a, ⟨a, rfl, hsup⟩, ha.2⟩)
      refine hb.trans ?_
      have hdec : Real.exp (-(κe - countingRate) * extentFloor D d j) =
          c.decayFactor d ((D.K : ℕ) - j) := rfl
      have hball' : c.ballTerm d R ((D.K : ℕ) - j) =
          c.ballCubeCount R ((D.K : ℕ) - j) * c.decayFactor d ((D.K : ℕ) - j) := rfl
      rw [hdec, hball']
      have hdec0 : 0 ≤ c.decayFactor d ((D.K : ℕ) - j) := (Real.exp_pos _).le
      have hY0 : 0 ≤ rateSum κe * c.decayFactor d ((D.K : ℕ) - j) *
          (Ce * sharpNormFactor D ϱ f) :=
        mul_nonneg (mul_nonneg hSpos.le hdec0) (mul_nonneg hCe hBF)
      have := mul_le_mul_of_nonneg_right hNcard' hY0
      calc _ = _ := by ring
        _ ≤ _ := this
        _ = _ := by ring
    have htotal := ofReal_norm_mixedDeriv_le_tsum hH hS e hA f hf _
      (mul_nonneg (mul_nonneg hCe hSpos.le) hBF) (c.ballTerm d R)
      (c.ballTerm_nonneg d R) hlevel
    refine htotal.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (mul_nonneg hCe hSpos.le), ConstantParameters.uvConstantInBall]
    change _ = ENNReal.ofReal (Ce * rateSum κe) * _ * _
    ring
end
end YangMills.Construction.TotalEnergyDerivative.Estimates
