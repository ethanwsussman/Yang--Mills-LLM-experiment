import YangMills.Construction.Lattice.BondOrientationDichotomy
import YangMills.Construction.Lattice.WilsonWeightGaugeInvariance
import YangMills.Construction.Matrices.HaarExpChartDensity
import YangMills.Construction.SourcesAndGluing.LinksUnderLatticeSimilaritiesOfToriForm
import YangMills.Construction.SourcesAndGluing.MeasuresUnderLatticeSimilaritiesForm
import YangMills.Construction.SourcesAndGluing.WilsonActionUnderLatticeSimilarities
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SourcesAndGluing.ScaledMotionMeasures
open Matrices
open Matrices.ComplexMatrix2
open PeriodicLattice
theorem haarPi_map_reindex_of_inv
    (hinv : Measure.map (fun U : specialUnitary => U⁻¹) haarProb = haarProb)
    {ι ι' : Type} [Countable ι] [Countable ι'] (e : ι ≃ ι')
    (g : ι → specialUnitary → specialUnitary)
    (hg : ∀ i, g i = id ∨ g i = Inv.inv) :
    (haarPi ι').map (fun v i => g i (v (e i))) = haarPi ι := by
  have hgm : ∀ i, Measurable (g i) := fun i => by
    rcases hg i with h | h <;> rw [h]
    · exact measurable_id
    · exact continuous_inv.measurable
  have hgh : ∀ i, haarProb.map (g i) = haarProb := fun i => by
    rcases hg i with h | h <;> rw [h]
    · exact Measure.map_id
    · exact hinv
  have hR : (fun (v : ι' → specialUnitary) i => v (e i)) =
      MeasurableEquiv.piCongrLeft (fun _ : ι => specialUnitary) e.symm := by
    funext v i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have h₁ : (haarPi ι').map (fun (v : ι' → specialUnitary) i => v (e i)) = haarPi ι := by
    rw [hR]
    exact Measure.infinitePi_map_piCongrLeft (μ := fun _ : ι => haarProb) e.symm
  have hRm : Measurable fun (v : ι' → specialUnitary) i => v (e i) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hGm : Measurable fun (v : ι → specialUnitary) i => g i (v i) :=
    measurable_pi_iff.2 fun i => (hgm i).comp (measurable_pi_apply i)
  have h₂ : (haarPi ι).map (fun (v : ι → specialUnitary) i => g i (v i)) = haarPi ι := by
    have h := Measure.infinitePi_map_pi (fun _ : ι => haarProb) hgm
    simp only [hgh] at h
    exact h
  have e₃ : (fun (v : ι' → specialUnitary) i => g i (v (e i))) =
      (fun (v : ι → specialUnitary) i => g i (v i)) ∘
        fun (v : ι' → specialUnitary) i => v (e i) := rfl
  rw [e₃, ← Measure.map_map hGm hRm, h₁, h₂]
section Links
variable {L m L' m' : ℕ} {j j' : ℤ}
theorem coe_specialUnitary_inv (g : specialUnitary) :
    ((g⁻¹ : specialUnitary) : ComplexMatrix2) = (g : ComplexMatrix2)⁻¹ := by apply _root_.YangMills.Construction.InfiniteLattice.specialUnitary_coe_inv <;> assumption
theorem gaugeFieldOfPositive_apply_of_pos (v : PositivelyOrientedBond L m j → specialUnitary)
    {b : Bond L m j} (h : b.IsPositivelyOriented) :
    gaugeFieldOfPositive v b = (v ⟨b, h⟩ : ComplexMatrix2) := by
  simp [gaugeFieldOfPositive, h]
theorem gaugeFieldOfPositive_apply_of_not_pos
    (v : PositivelyOrientedBond L m j → specialUnitary)
    {b : Bond L m j} (h : ¬ b.IsPositivelyOriented) (h' : b.opposite.IsPositivelyOriented) :
    gaugeFieldOfPositive v b = ((v ⟨b.opposite, h'⟩ : ComplexMatrix2))⁻¹ := by
  simp [gaugeFieldOfPositive, h, h']
theorem gaugeFieldOfPositive_opposite
    (hpos : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (v : PositivelyOrientedBond L m j → specialUnitary) (b : Bond L m j) :
    gaugeFieldOfPositive v b.opposite = (gaugeFieldOfPositive v b)⁻¹ := by
  rcases hpos b with ⟨h, h'⟩ | ⟨h', h⟩
  · have h₂ : b.opposite.opposite.IsPositivelyOriented := h
    rw [gaugeFieldOfPositive_apply_of_not_pos v h' h₂, gaugeFieldOfPositive_apply_of_pos v h]
    rfl
  · rw [gaugeFieldOfPositive_apply_of_pos v h', gaugeFieldOfPositive_apply_of_not_pos v h h',
      ← coe_specialUnitary_inv, ← coe_specialUnitary_inv, inv_inv]
theorem measurable_gaugeFieldOfPositive
    (hpos : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented) :
    Measurable (gaugeFieldOfPositive :
      (PositivelyOrientedBond L m j → specialUnitary) → Bond L m j → ComplexMatrix2) := by
  refine measurable_pi_iff.2 fun b => ?_
  have hval : Measurable fun g : specialUnitary => (g : ComplexMatrix2) :=
    continuous_subtype_val.measurable
  have hinv : Measurable fun g : specialUnitary => ((g⁻¹ : specialUnitary) : ComplexMatrix2) :=
    hval.comp continuous_inv.measurable
  rcases hpos b with ⟨h, -⟩ | ⟨h', h⟩
  · simp only [gaugeFieldOfPositive_apply_of_pos _ h]
    exact hval.comp (measurable_pi_apply _)
  · simp only [gaugeFieldOfPositive_apply_of_not_pos _ h h', ← coe_specialUnitary_inv]
    exact hinv.comp (measurable_pi_apply _)
theorem exists_reindex_of_bijective_commute_opposite
    (hpos : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hpos' : ∀ c : Bond L' m' j', Xor c.IsPositivelyOriented c.opposite.IsPositivelyOriented)
    (f : Bond L m j → Bond L' m' j') (hf : Function.Bijective f)
    (hrev : ∀ c, f c.opposite = (f c).opposite) :
    ∃ (e : PositivelyOrientedBond L m j ≃ PositivelyOrientedBond L' m' j')
      (g : PositivelyOrientedBond L m j → specialUnitary → specialUnitary),
      (∀ i, g i = id ∨ g i = Inv.inv) ∧
      ∀ v : PositivelyOrientedBond L' m' j' → specialUnitary,
        (fun c => gaugeFieldOfPositive v (f c)) =
          gaugeFieldOfPositive fun b => g b (v (e b)) := by
  classical
  have hor : ∀ b : Bond L m j, ¬ b.IsPositivelyOriented → b.opposite.IsPositivelyOriented :=
    fun b h => (hpos b).elim (fun h₁ => absurd h₁.1 h) (fun h₁ => h₁.1)
  have hor' : ∀ c : Bond L' m' j', ¬ c.IsPositivelyOriented → c.opposite.IsPositivelyOriented :=
    fun c h => (hpos' c).elim (fun h₁ => absurd h₁.1 h) (fun h₁ => h₁.1)
  have hnot : ∀ b : Bond L m j, b.IsPositivelyOriented → ¬ b.opposite.IsPositivelyOriented :=
    fun b h => (hpos b).elim (fun h₁ => h₁.2) (fun h₁ => absurd h h₁.2)
  have hnot' : ∀ c : Bond L' m' j', c.IsPositivelyOriented → ¬ c.opposite.IsPositivelyOriented :=
    fun c h => (hpos' c).elim (fun h₁ => h₁.2) (fun h₁ => absurd h h₁.2)
  let ρ : PositivelyOrientedBond L m j → PositivelyOrientedBond L' m' j' := fun b =>
    if h : (f b.1).IsPositivelyOriented then ⟨f b.1, h⟩ else ⟨(f b.1).opposite, hor' _ h⟩
  have ρ_pos : ∀ (b : PositivelyOrientedBond L m j) (h : (f b.1).IsPositivelyOriented),
      ρ b = ⟨f b.1, h⟩ := fun b h => dif_pos h
  have ρ_neg : ∀ (b : PositivelyOrientedBond L m j) (h : ¬ (f b.1).IsPositivelyOriented),
      ρ b = ⟨(f b.1).opposite, hor' _ h⟩ := fun b h => dif_neg h
  have hρ : Function.Bijective ρ := by
    constructor
    · rintro ⟨b₁, h₁⟩ ⟨b₂, h₂⟩ h
      have hval : b₁ = b₂ := by
        by_cases p₁ : (f b₁).IsPositivelyOriented <;> by_cases p₂ : (f b₂).IsPositivelyOriented
        · rw [ρ_pos ⟨b₁, h₁⟩ p₁, ρ_pos ⟨b₂, h₂⟩ p₂] at h
          exact hf.1 (congrArg Subtype.val h)
        · rw [ρ_pos ⟨b₁, h₁⟩ p₁, ρ_neg ⟨b₂, h₂⟩ p₂] at h
          have e : f b₁ = f b₂.opposite := by
            rw [hrev]
            exact congrArg Subtype.val h
          have e' := hf.1 e
          subst e'
          exact absurd h₁ (hnot b₂ h₂)
        · rw [ρ_neg ⟨b₁, h₁⟩ p₁, ρ_pos ⟨b₂, h₂⟩ p₂] at h
          have e : f b₁.opposite = f b₂ := by
            rw [hrev]
            exact congrArg Subtype.val h
          have e' := hf.1 e
          subst e'
          exact absurd h₂ (hnot b₁ h₁)
        · rw [ρ_neg ⟨b₁, h₁⟩ p₁, ρ_neg ⟨b₂, h₂⟩ p₂] at h
          have e : f b₁.opposite = f b₂.opposite := by
            rw [hrev, hrev]
            exact congrArg Subtype.val h
          exact congrArg Bond.opposite (hf.1 e)
      exact Subtype.ext hval
    · rintro ⟨c, hc⟩
      obtain ⟨b, rfl⟩ := hf.2 c
      by_cases hb : b.IsPositivelyOriented
      · exact ⟨⟨b, hb⟩, ρ_pos ⟨b, hb⟩ hc⟩
      · have hb' : b.opposite.IsPositivelyOriented := hor b hb
        have hn : ¬ (f b.opposite).IsPositivelyOriented := by
          rw [hrev]
          exact hnot' _ hc
        refine ⟨⟨b.opposite, hb'⟩, ?_⟩
        rw [ρ_neg ⟨b.opposite, hb'⟩ hn]
        refine Subtype.ext ?_
        change (f b.opposite).opposite = f b
        rw [hrev]
        rfl
  refine ⟨Equiv.ofBijective ρ hρ,
    fun b => if (f b.1).IsPositivelyOriented then id else Inv.inv, fun b => ?_, fun v => ?_⟩
  · by_cases h : (f b.1).IsPositivelyOriented
    · exact Or.inl (if_pos h)
    · exact Or.inr (if_neg h)
  · set w : PositivelyOrientedBond L m j → specialUnitary := fun b =>
      (if (f b.1).IsPositivelyOriented then id else Inv.inv) (v (Equiv.ofBijective ρ hρ b))
      with hw
    have key : ∀ (b : Bond L m j), b.IsPositivelyOriented →
        gaugeFieldOfPositive v (f b) = gaugeFieldOfPositive w b := by
      intro b hb
      rw [gaugeFieldOfPositive_apply_of_pos w hb]
      by_cases h : (f b).IsPositivelyOriented
      · have e : w ⟨b, hb⟩ = v ⟨f b, h⟩ := by
          simp only [hw, Equiv.ofBijective_apply, if_pos h, id]
          rw [ρ_pos ⟨b, hb⟩ h]
        rw [gaugeFieldOfPositive_apply_of_pos v h, e]
      · have e : w ⟨b, hb⟩ = (v ⟨(f b).opposite, hor' _ h⟩)⁻¹ := by
          simp only [hw, Equiv.ofBijective_apply, if_neg h]
          rw [ρ_neg ⟨b, hb⟩ h]
        rw [gaugeFieldOfPositive_apply_of_not_pos v h (hor' _ h), e, coe_specialUnitary_inv]
    funext b
    by_cases hb : b.IsPositivelyOriented
    · exact key b hb
    · have hb' := hor b hb
      calc gaugeFieldOfPositive v (f b)
          = gaugeFieldOfPositive v (f b.opposite).opposite := by
            rw [hrev]
            rfl
        _ = (gaugeFieldOfPositive v (f b.opposite))⁻¹ :=
            gaugeFieldOfPositive_opposite hpos' v _
        _ = (gaugeFieldOfPositive w b.opposite)⁻¹ := by rw [key _ hb']
        _ = gaugeFieldOfPositive w b.opposite.opposite :=
            (gaugeFieldOfPositive_opposite hpos w _).symm
        _ = gaugeFieldOfPositive w b := rfl
theorem productHaarMeasure_map_comp
    (hinv : Measure.map (fun U : specialUnitary => U⁻¹) haarProb = haarProb)
    (hpos : ∀ b : Bond L m j, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented)
    (hpos' : ∀ c : Bond L' m' j', Xor c.IsPositivelyOriented c.opposite.IsPositivelyOriented)
    (f : Bond L m j → Bond L' m' j') (hf : Function.Bijective f)
    (hrev : ∀ c, f c.opposite = (f c).opposite) :
    (productHaarMeasure L' m' j').map (fun U c => U (f c)) = productHaarMeasure L m j := by
  obtain ⟨e, g, hg, hv⟩ := exists_reindex_of_bijective_commute_opposite hpos hpos' f hf hrev
  have hgm : ∀ i, Measurable (g i) := fun i => by
    rcases hg i with h | h <;> rw [h]
    · exact measurable_id
    · exact continuous_inv.measurable
  have hΦ : Measurable fun (v : PositivelyOrientedBond L' m' j' → specialUnitary) b =>
      g b (v (e b)) :=
    measurable_pi_iff.2 fun i => (hgm i).comp (measurable_pi_apply _)
  have hT : Measurable fun (U : Bond L' m' j' → ComplexMatrix2) c => U (f c) :=
    measurable_pi_iff.2 fun _ => measurable_pi_apply _
  unfold productHaarMeasure gaugeFieldHaar
  rw [Measure.map_map hT (measurable_gaugeFieldOfPositive hpos')]
  have hc : (fun (U : Bond L' m' j' → ComplexMatrix2) c => U (f c)) ∘ gaugeFieldOfPositive =
      (gaugeFieldOfPositive :
        (PositivelyOrientedBond L m j → specialUnitary) → Bond L m j → ComplexMatrix2) ∘
        (fun v b => g b (v (e b))) := funext hv
  rw [hc, ← Measure.map_map (measurable_gaugeFieldOfPositive hpos) hΦ,
    haarPi_map_reindex_of_inv hinv e g hg]
end Links
theorem map_withDensity_of_ae_eq {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {μ' : Measure α} {T : α → γ} (hT : Measurable T) {d' : α → ℝ≥0∞} {d : γ → ℝ≥0∞}
    (hd : AEMeasurable d (μ'.map T)) (h : ∀ᵐ x ∂μ', d (T x) = d' x) :
    (μ'.withDensity d').map T = (μ'.map T).withDensity d := by
  ext s hs
  have hds : AEMeasurable d ((μ'.restrict (T ⁻¹' s)).map T) := by
    rw [← Measure.restrict_map hT hs]
    exact hd.restrict
  rw [Measure.map_apply hT hs, withDensity_apply _ (hT hs), withDensity_apply _ hs,
    Measure.restrict_map hT hs, lintegral_map' hds hT.aemeasurable]
  exact lintegral_congr_ae (ae_restrict_of_ae (h.mono fun x hx => hx.symm))
theorem wilsonGibbsMeasure_map {L m K L' m' K' : ℕ} {β : ℝ}
    {T : (Bond L' m' (K' : ℤ) → ComplexMatrix2) → Bond L m (K : ℤ) → ComplexMatrix2}
    (hT : Measurable T)
    (hμ : (productHaarMeasure L' m' (K' : ℤ)).map T = productHaarMeasure L m (K : ℤ))
    (hint : Integrable (boltzmannWeight β) (productHaarMeasure L m (K : ℤ)))
    (hact : ∀ᵐ U ∂productHaarMeasure L' m' (K' : ℤ), wilsonAction (T U) = wilsonAction U) :
    (wilsonGibbsMeasure L' m' K' β).map T = wilsonGibbsMeasure L m K β := by
  have hden : ∀ᵐ U ∂productHaarMeasure L' m' (K' : ℤ),
      boltzmannWeight β (T U) = boltzmannWeight β U := hact.mono fun U h => by
    unfold boltzmannWeight
    rw [h]
  have hZ : partitionFunction L' m' K' β = partitionFunction L m K β := by
    have h := integral_map (μ := productHaarMeasure L' m' (K' : ℤ)) hT.aemeasurable
      (f := boltzmannWeight β) (by rw [hμ]; exact hint.aestronglyMeasurable)
    rw [hμ] at h
    unfold partitionFunction
    rw [h]
    exact (integral_congr_ae hden).symm
  have hd : AEMeasurable (fun U => ENNReal.ofReal (boltzmannWeight β U))
      ((productHaarMeasure L' m' (K' : ℤ)).map T) := by
    rw [hμ]
    exact ENNReal.measurable_ofReal.comp_aemeasurable hint.aestronglyMeasurable.aemeasurable
  have hw := map_withDensity_of_ae_eq hT hd (d' := fun U => ENNReal.ofReal (boltzmannWeight β U))
    (hden.mono fun U h => by simp only [h])
  rw [hμ] at hw
  unfold wilsonGibbsMeasure
  rw [Measure.map_smul, hZ, hw]
theorem scaledMotionMeasuresClaim_holds (hLinks : ScaledMotionLinksOfToriClaim)
    (hAction : ActionUnderScaledMotions.Statement)
    (hOrientation : PeriodicLattice.BondOrientationDichotomy)
    (hHaar : Matrices.ComplexMatrix2.HaarExpChartProperties)
    (hWeight : PeriodicLattice.WilsonWeightGaugeInvariance.statement) :
    ScaledMotionMeasuresClaim := by
  intro D e Φ F hF β _
  have hK := D.K.pos
  have hm := D.m.pos
  have hK' := e.target.K.pos
  have hm' := e.target.m.pos
  have hpos : ∀ b : D.PeriodicLink, Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    hOrientation D.L D.m D.isAdmissible hm _ (by omega)
  have hpos' : ∀ b : e.target.PeriodicLink,
      Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented :=
    hOrientation e.target.L e.target.m e.target.isAdmissible hm' _ (by omega)
  obtain ⟨hbij, hrev, -⟩ := hLinks D e Φ
  have hT : Measurable Φ.pullTorusField := measurable_pi_iff.2 fun _ => measurable_pi_apply _
  have hμ : (productHaarMeasure e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ)).map
      Φ.pullTorusField = productHaarMeasure D.L (D.m : ℕ) ((D.K : ℕ) : ℤ) :=
    productHaarMeasure_map_comp hHaar.2.2.2 hpos hpos' Φ.onTorusLink hbij hrev
  have hL : 1 < D.L := by
    have := D.isAdmissible.2
    omega
  have hL' : 1 < e.target.L := by
    have := e.target.isAdmissible.2
    omega
  obtain ⟨-, -, -, hint, -⟩ := hWeight D.L D.m D.K β hL hm hK
  obtain ⟨-, -, -, -, -, -, hnull, -⟩ := hWeight e.target.L e.target.m e.target.K β hL' hm' hK'
  have hreal : ∀ᵐ U ∂productHaarMeasure e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ),
      U ∈ compactGaugeFields e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ) :=
    mem_ae_iff.mpr hnull
  have hact : ∀ᵐ U ∂productHaarMeasure e.target.L (e.target.m : ℕ) ((e.target.K : ℕ) : ℤ),
      wilsonAction (Φ.pullTorusField U) = wilsonAction U :=
    hreal.mono fun U hU => hAction D e Φ U hU
  have hW := wilsonGibbsMeasure_map hT hμ hint hact
  refine ⟨?_, ?_⟩
  · have h := integral_map (μ := productHaarMeasure e.target.L (e.target.m : ℕ)
      ((e.target.K : ℕ) : ℤ)) hT.aemeasurable (f := F) hF.1.aestronglyMeasurable
    rw [hμ] at h
    exact h.symm
  · have h := integral_map (μ := wilsonGibbsMeasure e.target.L (e.target.m : ℕ)
      (e.target.K : ℕ) β) hT.aemeasurable (f := F) hF.1.aestronglyMeasurable
    rw [hW] at h
    exact h.symm
end YangMills.Construction.SourcesAndGluing.ScaledMotionMeasures
end
