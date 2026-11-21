import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctionsProof
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.JetOfALocalOperatorFunctionIsEntire
import YangMills.Construction.Towers.PropertiesOfTheBackgrounds
import YangMills.Construction.Towers.TheMassiveFunctionIsContinuousOnTheRealPolydisc
import YangMills.Construction.Towers.TheMassiveJets
import YangMills.Construction.Towers.TheOperatorFunctionsOfTheMassiveFunctionalAreLocal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Tower.MassiveOpFunctions.ContinuousOnRealPolydisc
open Set
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.Tower.FullSpace.BackgroundJets
open YangMills.Construction.Tower.FullSpace.BackgroundProperties (axisAmplitude axisField axisField_of_mem)
theorem continuous_toComplexVec : Continuous toComplexVec := by apply _root_.YangMills.Construction.PeriodicOperators.EntriesDets.continuous_toComplexVec <;> assumption
theorem continuousOn_logNumber
    (hArgs : JetArgumentsAndEqualJets)
    (hEntire : LocalJetEntire.Claim)
    (hLogDet : LogDetSecondDerivs.Claim)
    {L k : ℕ} {P : PeriodicData} (hR : IsPeriodic (remainderIndex L k))
    (hP : IsPeriodic P)
    {A : ((remainderIndex L k).Carrier → ℂ) → P.Carrier → P.Carrier → ℂ}
    (hA : IsLocalOpFun (remainderIndex L k) P P A)
    (hUnit : ∀ ξ : InfiniteLattice.AmbientSpace,
      IsUnit (symbolHom P P (coeffZero (remainderIndex L k) P P A) (toComplexVec ξ) :
        Module.End ℂ (P.UnitQuot → ℂ)))
    {ν₁ ν₂ : Fin 4} {K : Set InfiniteLattice.AmbientSpace} {r : ℝ}
    (hpos : ∀ c, ContinuousOn (fun ξ => scaledResponseField L k (toComplexVec ξ) ν₁ c) K)
    (hneg : ∀ c, ContinuousOn (fun ξ => scaledResponseField L k (-toComplexVec ξ) ν₂ c) K)
    (Q : (Fin 4 → ℂ) → JetQuad P P)
    (hQinv : ∀ ξ ∈ K, JetQuad.IsInvertibleJet r (toComplexVec ξ) (Q (toComplexVec ξ)))
    (hQeq : ∀ ξ ∈ K, JetQuad.EqAsJet r (toComplexVec ξ)
      (jetAlongResponse L k A (toComplexVec ξ) ν₁ ν₂) (Q (toComplexVec ξ))) :
    ContinuousOn (fun ξ => JetQuad.logNumber (toComplexVec ξ) (Q (toComplexVec ξ))) K := by
  obtain ⟨δ, hδ, -, -, ⟨U, -, hUsub, f, hf, hexpand⟩, -⟩ := hLogDet _ P hR hP A hA hUnit
  have hfin : Finite (remainderIndex L k).UnitQuot := hR.finite_quot
  cases nonempty_fintype (remainderIndex L k).UnitQuot
  have hinStrip : ∀ ξ : InfiniteLattice.AmbientSpace, toComplexVec ξ ∈ imStrip δ := fun ξ μ => by
    simpa [toComplexVec] using hδ.le
  have hagree : EqOn
      (fun ξ => ∑ c, ∑ c', f c c' (toComplexVec ξ) * scaledResponseField L k (toComplexVec ξ) ν₁ c *
        scaledResponseField L k (-toComplexVec ξ) ν₂ c')
      (fun ξ => JetQuad.logNumber (toComplexVec ξ) (Q (toComplexVec ξ))) K := by
    intro ξ hξ
    have hinvξ := hQinv ξ hξ
    have hjetξ : JetQuad.IsJet r (toComplexVec ξ)
        (jetAlongResponse L k A (toComplexVec ξ) ν₁ ν₂) :=
      (hEntire _ P P hR hP hP A hA).2.2.2 r hinvξ.isJet.pos_width (toComplexVec ξ)
        hinvξ.isJet.mem_imStrip _ _
    have heqξ := hQeq ξ hξ
    have hsymmξ : JetQuad.EqAsJet r (toComplexVec ξ) (Q (toComplexVec ξ))
        (jetAlongResponse L k A (toComplexVec ξ) ν₁ ν₂) :=
      ⟨heqξ.1.symm, heqξ.2.1.symm, heqξ.2.2.1.symm, heqξ.2.2.2.symm⟩
    have hlog := ((hArgs.2.2 r (toComplexVec ξ) P hP _ _ hinvξ.isJet hjetξ hsymmξ).2 hinvξ).2.2.2
    have hser := hexpand (toComplexVec ξ) (hinStrip ξ) (scaledResponseField L k (toComplexVec ξ) ν₁)
      (scaledResponseField L k (-toComplexVec ξ) ν₂)
    simp only [tsum_fintype] at hser
    show _ = JetQuad.logNumber (toComplexVec ξ) (Q (toComplexVec ξ))
    rw [hlog]
    exact hser.symm
  refine ContinuousOn.congr ?_ hagree.symm
  refine continuousOn_finsetSum _ fun c _ => continuousOn_finsetSum _ fun c' _ => ?_
  have hU : ContinuousOn (f c c') U :=
    (continuous_apply (0 : Fin 1)).comp_continuousOn (hf c c').2.1
  have hK : ContinuousOn (fun ξ => f c c' (toComplexVec ξ)) K :=
    hU.comp continuous_toComplexVec.continuousOn fun ξ _ => hUsub (hinStrip ξ)
  exact (hK.mul (hpos c)).mul (hneg c')
theorem claim_of_parts (hTower : TowerIndexSets.Claim)
    (hArgs : JetArgumentsAndEqualJets)
    (hEntire : LocalJetEntire.Claim)
    (hLogDet : LogDetSecondDerivs.Claim)
    (hBack : FullSpace.BackgroundProperties.BackgroundPropertiesHold)
    (hMass : MassJets.MassJetsClaim)
    (hLocal : Locality.OpFunsLocal) : Claim := by
  intro L hL k hk z hz ν₁ ν₂
  obtain ⟨hVert, hEdge, -⟩ := hTower L hL k 0 (Nat.zero_le k)
  obtain ⟨U, -, hUsub, hNb⟩ := (hBack L hL k hk).exists_nhds ν₁ ν₂
  obtain ⟨hv, he, huv, hue, hjets⟩ := (hLocal L hL z hz).2 k hk
  have hin : ∀ ξ ∈ {ξ | toComplexVec ξ ∈ momentumPolydisc (massWidth z)},
      toComplexVec ξ ∈ momentumPolydisc stripHalfWidth := fun ξ hξ μ =>
    (hξ μ).trans (min_le_left _ _)
  have hinNeg : ∀ ξ ∈ {ξ | toComplexVec ξ ∈ momentumPolydisc (massWidth z)},
      -toComplexVec ξ ∈ momentumPolydisc stripHalfWidth := fun ξ hξ μ => by
    simpa using hin ξ hξ μ
  have hscaled : ∀ q ∈ momentumPolydisc stripHalfWidth, ∀ (μ : Fin 4) (c : (remainderIndex L k).UnitQuot),
      scaledResponseField L k q μ c = ((finestMesh L k : ℝ) : ℂ) * axisAmplitude L k q μ c := by
    intro q hq μ c
    rw [← axisField_of_mem hq]
    rfl
  have hpos : ∀ c, ContinuousOn (fun ξ => scaledResponseField L k (toComplexVec ξ) ν₁ c)
      {ξ | toComplexVec ξ ∈ momentumPolydisc (massWidth z)} := by
    intro c
    have hU : ContinuousOn (fun x => axisAmplitude L k x ν₁ c) U :=
      (continuous_apply (0 : Fin 1)).comp_continuousOn (hNb.amplitude_pos.2.2 c).2.1
    have hK : ContinuousOn (fun ξ => axisAmplitude L k (toComplexVec ξ) ν₁ c)
        {ξ | toComplexVec ξ ∈ momentumPolydisc (massWidth z)} :=
      hU.comp continuous_toComplexVec.continuousOn fun ξ hξ => hUsub (hin ξ hξ)
    exact (continuousOn_const (c := ((finestMesh L k : ℝ) : ℂ))).mul hK |>.congr fun ξ hξ =>
      hscaled _ (hin ξ hξ) ν₁ c
  have hneg : ∀ c, ContinuousOn (fun ξ => scaledResponseField L k (-toComplexVec ξ) ν₂ c)
      {ξ | toComplexVec ξ ∈ momentumPolydisc (massWidth z)} := by
    intro c
    have hU : ContinuousOn (fun x => axisAmplitude L k (-x) ν₂ c) U :=
      (continuous_apply (0 : Fin 1)).comp_continuousOn (hNb.amplitude_neg.2.2 c).2.1
    have hK : ContinuousOn (fun ξ => axisAmplitude L k (-toComplexVec ξ) ν₂ c)
        {ξ | toComplexVec ξ ∈ momentumPolydisc (massWidth z)} :=
      hU.comp continuous_toComplexVec.continuousOn fun ξ hξ => hUsub (hin ξ hξ)
    exact (continuousOn_const (c := ((finestMesh L k : ℝ) : ℂ))).mul hK |>.congr fun ξ hξ =>
      hscaled _ (hinNeg ξ hξ) ν₂ c
  have hvert := continuousOn_logNumber hArgs hEntire hLogDet hEdge hVert hv huv hpos hneg
    (fun q => addScalarJet (vertexOperatorJet L k q ν₁ ν₂) z)
    (fun ξ hξ => (((hMass L hL k hk).1 z hz).2 (toComplexVec ξ) hξ ν₁ ν₂).1.1)
    (fun ξ hξ => (hjets ξ hξ ν₁ ν₂).1)
  have hedge := continuousOn_logNumber hArgs hEntire hLogDet hEdge hEdge he hue hpos hneg
    (fun q => addScalarJet (edgeOperatorJet L k q ν₁ ν₂) z)
    (fun ξ hξ => (((hMass L hL k hk).1 z hz).2 (toComplexVec ξ) hξ ν₁ ν₂).2.1)
    (fun ξ hξ => (hjets ξ hξ ν₁ ν₂).2)
  exact hvert.sub (continuousOn_const.mul hedge)
end YangMills.Construction.Tower.MassiveOpFunctions.ContinuousOnRealPolydisc
end
