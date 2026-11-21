import Mathlib
import YangMills.ContinuumLimit.TopWithTuning
import YangMills.ContinuumLimit.LimitsOfATunedSequence
import YangMills.Construction.QuaternionicWilsonModel.TheLimitsOfTheTopAreRealAndNotZeroProof
import YangMills.Construction.TheStatementsProvedTogether.FromHeatSumOnALatticeProof
import YangMills.Construction.TheStatementsProvedTogether.FromMeansAtABondProof
import YangMills.Construction.TheStatementsProvedTogether.FromZetaOfAGroundIsBorelProof
import YangMills.Construction.TheStatementsProvedTogether.FromConcentrationInOneBoxProof
set_option autoImplicit false

open Filter Set
open scoped Topology

noncomputable section

namespace YangMills.ContinuumLimit

open YangMills.Construction YangMills.Construction.TotalDensities
  YangMills.Construction.RenormalizationStepParameters YangMills.Construction.TrajectoryData
  YangMills.Construction.CouplingFlow YangMills.Construction.TopAux
open YangMills.Construction.TheStatementsProvedTogether
open TorusMetric TestFunctions PeriodicLattice FourPointBounds SchwingerFunctions Conventions

def TunedTop.DilatedTopLimits (ℓ : TorusLumps.StepParameters) (T : ParameterAssignment)
    (y lam cr Bs g : ℝ) : Prop :=
  ∀ s : StandingParameters, s.L = ℓ.side →
    ∀ (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ), Tendsto K atTop atTop →
    (∀ j, runDepth lam cr ≤ (K j : ℕ)) →
    (∀ j, IsTunedAt T y (SequencePassage.passageThreshold Bs g) (K j) (β j)) →
    ∃ r < runDepth lam cr, ∃ (φ : ℕ+ → ℕ+) (K' : ℕ+ → ℕ+)
      (S' : AmbientPoints.TupleMapFamily (shiftSide s r) .torus),
      StrictMono φ ∧ (∀ j, (K' j : ℕ) + r = (K (φ j) : ℕ)) ∧
      (∀ j, TotalDensitySystem.IsFirstPassagePair ℓ Bs g (K' j) (β (φ j))) ∧
      TotalDensitySystem.IsTorusLimit ℓ Bs g (shiftSide s r) S' ∧
      (∀ (n : ℕ) (hn : 2 ≤ n) (X' : AmbientPoints.separatedTuples (shiftSide s r) .torus n),
        Tendsto (fun j => connectedSchwinger s.L ((s.m : ℕ) + r) (K' j : ℕ) (β (φ j)) X'.1) atTop
          (𝓝 ((S' n hn X' : ℝ) : ℂ))) ∧
      (∀ (n : ℕ) (hn : 2 ≤ n) (X : AmbientPoints.separatedTuples s .torus n),
        Tendsto (fun j => connectedSchwinger s.L s.m (K (φ j) : ℕ) (β (φ j)) X.1) atTop
          (𝓝 ((S' n hn ⟨fun i => dilateToSide s.L s.m ((s.m : ℕ) + r) (X.1 i),
            dilate_up_mem s r X.2⟩ : ℝ) : ℂ))) ∧
      (∀ (n : ℕ) (hn : 2 ≤ n) (X' : AmbientPoints.separatedTuples (shiftSide s r) .torus n),
        Tendsto (fun j => connectedSchwinger s.L s.m (K (φ j) : ℕ) (β (φ j))
          (fun i => dilateToSide s.L ((s.m : ℕ) + r) s.m (X'.1 i))) atTop
          (𝓝 ((S' n hn X' : ℝ) : ℂ)))

def TunedTop.Statement (Q' : ParameterAssignment → ℝ → Prop) : Prop :=
  ∃ ϑ₀ ∈ Ioc (0 : ℝ) 1, ∃ J Lstar : ℕ, 1 ≤ J ∧ ∀ L : ℕ, Odd L → Lstar ≤ L →
    ∃ (ℓ : TorusLumps.StepParameters) (Bs c₅ γ : ℝ) (Nw : ℕ) (CT : ℝ)
      (T : ParameterAssignment) (y c M Cr : ℝ) (Kr : WeightedResponses.ResponseParameters) (lam cr : ℝ),
    ℓ.side = L ∧ ℓ.baseDepth = J ∧ TotalDensitySystem.IsUnitMeshStepParameters ℓ ∧ 2 ≤ Bs ∧ 0 ≤ c₅ ∧
      γ ∈ Ioo (0 : ℝ) 1 ∧ 0 < CT ∧ 1 ≤ Nw ∧
      T.Admissible ∧ T.stepParameters y = ℓ ∧ 0 ≤ Cr ∧
      HasAverageSlope (ReferenceDensity.oneLoopCoefficient T.coupling T.ρA T.lam T.side)
        (slopeConst L) c ∧
      (∀ t, |ScaledVariables.secondStepCoefficient T.coupling T.ρA T.lam T.side t| ≤ M) ∧
      Bs = 2 * T.B ∧ RunTable T y Kr lam cr ∧ Q' T y ∧ TunedAtEveryCutoff T y ∧
      ∀ g ∈ Ioc 0 γ,
        TotalDensitySystem.CouplingConditions ℓ Bs c₅ (3 / 4 * TotalDensitySystem.oneLoopShift L) Nw CT g ∧
        ReferenceFlowBound ℓ Bs T.coupling T.ρA T.lam Cr g ∧
        runFloor T y cr < SequencePassage.passageThreshold Bs g ∧
        QuaternionicWilsonModel.TopLimitsRealNonzero.LimitsRealAt ℓ Bs g ∧
        (∀ ϑ ∈ Ioc (0 : ℝ) ϑ₀, ∃ d₁ ∈ Ioc (0 : ℝ) (1 / 40), ∀ d ∈ Ioc (0 : ℝ) d₁,
          QuaternionicWilsonModel.TopLimitsRealNonzero.ValuesPositiveAt ℓ Bs g ϑ d) ∧
        (∀ K : ℕ, ∃! β : ℝ, IsTunedAt T y (SequencePassage.passageThreshold Bs g) K β) ∧
        TunedTop.DilatedTopLimits ℓ T y lam cr Bs g

theorem tuned_top {Q' : ParameterAssignment → ℝ → Prop} (hQ' : HoldsAtAdmissibleParameters Q') :
    TunedTop.Statement Q' := by
  obtain ⟨hside, ϑ₀, hϑ₀, hmem⟩ := testClasses_nonempty_all_scales
  obtain ⟨J, Ls, hJ, h⟩ := top_with_tuning hQ'
  refine ⟨ϑ₀, hϑ₀, J, Ls, hJ, fun L hodd hge => ?_⟩
  obtain ⟨ℓ, Bs, c₅, γ, Nw, CT, T, y, c, M, Cr, Kr, lam, cr, hL, hJ₀, hdat, hBs2, hc₅, hγ, hCT, hNw,
    hT, hℓ, hCr, hS, hM, hBs, hRun, hQT, hTuned, hall, hfloor, huniq⟩ := h L hodd hge
  have h40 := hdat.side_ge
  have hL2 : 2 ≤ ℓ.side := by
    have h2 : (2 : ℕ) ≤ 2 ^ 40 := by norm_num
    omega
  have hB : IsAdmissibleBlockingFactor ℓ.side := by
    have h13 : (13 : ℕ) ≤ 2 ^ 40 := by norm_num
    exact ⟨hdat.side_odd, by omega⟩
  refine ⟨ℓ, Bs, c₅, γ, Nw, CT, T, y, c, M, Cr, Kr, lam, cr, hL, hJ₀, hdat, hBs2, hc₅, hγ, hCT, hNw,
    hT, hℓ, hCr, hS, hM, hBs, hRun, hQT, hTuned, fun g hg => ?_⟩
  have hLR := QuaternionicWilsonModel.TopLimitsRealNonzero.limitsRealAt_holds
    torus_lipschitz_tuple_props torusCumulant_multilinear hB hL2 (hall g hg).1
  refine ⟨(hall g hg).1, (hall g hg).2, hfloor g hg, hLR, fun ϑ hϑ => ?_, huniq g hg, ?_⟩
  · have hϑ1 : ϑ ∈ Ioc (0 : ℝ) 1 := ⟨hϑ.1, hϑ.2.trans hϑ₀.2⟩
    obtain ⟨cV, Cn, C, hC, -, -, -, -, hnum⟩ := (hall g hg).1.constants
    obtain ⟨-, hroom⟩ := hnum ϑ hϑ1
    obtain ⟨d₀, ηBar, εBar, ζ, K₀, d₄, hcl⟩ :=
      hroom QuaternionicWilsonModel.TopLimitsRealNonzero.linearGauge
        QuaternionicWilsonModel.TopLimitsRealNonzero.linearGauge_isSubexpGrowth
    exact ⟨d₄, ⟨hcl.d₄_mem.1, hcl.d₄_mem.2.trans hcl.twoPointLaw.cutoff_mem.2⟩, fun d hd =>
      QuaternionicWilsonModel.TopLimitsRealNonzero.valuesPositiveAt_holds torusCumulant_multilinear
        test_pair_transport_lift_dilation hside hϑ1 hcl (hmem ϑ hϑ d hd.1) hd⟩
  · subst hℓ
    exact fun s hs K β hK hdepth hβ =>
      tuned_limit_is_dilated_top_limit expansion_gives_total_flow total_density_flow_unique
        four_point_cutoff_rescaling_invariant hRun hLR.family_onTorus rfl s hs K β hK hdepth hβ

theorem tuned_limit_not_zero {ℓ : TorusLumps.StepParameters} {T : ParameterAssignment}
    {y lam cr Bs g ϑ d : ℝ} (hlim : TunedTop.DilatedTopLimits ℓ T y lam cr Bs g)
    (hpos : QuaternionicWilsonModel.TopLimitsRealNonzero.ValuesPositiveAt ℓ Bs g ϑ d)
    (s : StandingParameters) (hs : s.L = ℓ.side) (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ)
    (hK : Tendsto K atTop atTop) (hdepth : ∀ j, runDepth lam cr ≤ (K j : ℕ))
    (hβ : ∀ j, IsTunedAt T y (SequencePassage.passageThreshold Bs g) (K j) (β j)) :
    ∃ φ : ℕ+ → ℕ+, StrictMono φ ∧
      (∃ (X : AmbientPoints.separatedTuples s .torus 2) (t : ℝ), 0 < t ∧
        Tendsto (fun j => connectedSchwinger s.L s.m (K (φ j) : ℕ) (β (φ j)) X.1) atTop
          (𝓝 (t : ℂ))) ∧
      ∃ (X : AmbientPoints.separatedTuples s .torus 4) (t : ℝ), 0 < t ∧
        Tendsto (fun j => connectedSchwinger s.L s.m (K (φ j) : ℕ) (β (φ j)) X.1) atTop
          (𝓝 (t : ℂ)) := by
  obtain ⟨r, -, φ, K', S', hφ, -, -, hS', -, -, hdown⟩ := hlim s hs K β hK hdepth hβ
  have hs' : (shiftSide s r).L = ℓ.side := hs
  obtain ⟨⟨X₂, hX₂, -⟩, X₄, hX₄, -⟩ := hpos.nonempty_torus (shiftSide s r) hs'
  exact ⟨φ, hφ,
    ⟨⟨fun i => dilateToSide s.L ((s.m : ℕ) + r) s.m (X₂.1 i), dilate_down_mem s r X₂.2⟩,
      S' 2 le_rfl X₂, hpos.pair_pos_torus (shiftSide s r) S' hs' hS' X₂ hX₂, hdown 2 le_rfl X₂⟩,
    ⟨fun i => dilateToSide s.L ((s.m : ℕ) + r) s.m (X₄.1 i), dilate_down_mem s r X₄.2⟩,
      S' 4 (by norm_num) X₄, hpos.quad_pos_torus (shiftSide s r) S' hs' hS' X₄ hX₄,
      hdown 4 (by norm_num) X₄⟩

theorem tuned_top_limit_not_zero {Q' : ParameterAssignment → ℝ → Prop}
    (hQ' : HoldsAtAdmissibleParameters Q') :
    ∃ J Lstar : ℕ, 1 ≤ J ∧ ∀ L : ℕ, Odd L → Lstar ≤ L →
      ∃ (ℓ : TorusLumps.StepParameters) (Bs γ : ℝ) (T : ParameterAssignment) (y lam cr : ℝ),
        ℓ.side = L ∧ T.stepParameters y = ℓ ∧ Q' T y ∧ γ ∈ Ioo (0 : ℝ) 1 ∧
        ∀ g ∈ Ioc 0 γ, ∀ s : StandingParameters, s.L = L →
          ∀ (K : ℕ+ → ℕ+) (β : ℕ+ → ℝ), Tendsto K atTop atTop →
          (∀ j, runDepth lam cr ≤ (K j : ℕ)) →
          (∀ j, IsTunedAt T y (SequencePassage.passageThreshold Bs g) (K j) (β j)) →
          ∃ φ : ℕ+ → ℕ+, StrictMono φ ∧
            (∃ (X : AmbientPoints.separatedTuples s .torus 2) (t : ℝ), 0 < t ∧
              Tendsto (fun j => connectedSchwinger s.L s.m (K (φ j) : ℕ) (β (φ j)) X.1) atTop
                (𝓝 (t : ℂ))) ∧
            ∃ (X : AmbientPoints.separatedTuples s .torus 4) (t : ℝ), 0 < t ∧
              Tendsto (fun j => connectedSchwinger s.L s.m (K (φ j) : ℕ) (β (φ j)) X.1) atTop
                (𝓝 (t : ℂ)) := by
  obtain ⟨ϑ₀, hϑ₀, J, Ls, hJ, h⟩ := tuned_top hQ'
  refine ⟨J, Ls, hJ, fun L hodd hge => ?_⟩
  obtain ⟨ℓ, Bs, c₅, γ, Nw, CT, T, y, c, M, Cr, Kr, lam, cr, hL, -, -, -, -, hγ, -, -, -, hℓ,
    -, -, -, -, -, hQT, -, hall⟩ := h L hodd hge
  refine ⟨ℓ, Bs, γ, T, y, lam, cr, hL, hℓ, hQT, hγ, fun g hg s hs K β hK hdepth hβ => ?_⟩
  obtain ⟨-, -, -, -, hpos, -, hlim⟩ := hall g hg
  obtain ⟨d₁, hd₁, hd⟩ := hpos ϑ₀ ⟨hϑ₀.1, le_rfl⟩
  exact tuned_limit_not_zero hlim (hd d₁ ⟨hd₁.1, le_rfl⟩) s (hs.trans hL.symm) K β hK hdepth hβ

end YangMills.ContinuumLimit

end
