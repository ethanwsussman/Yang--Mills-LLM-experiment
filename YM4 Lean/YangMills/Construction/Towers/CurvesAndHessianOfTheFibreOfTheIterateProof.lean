import YangMills.Construction.Towers.ConfigurationsOnFiniteBondSets
import YangMills.Construction.Towers.CurvesAndHessianOfTheFibreOfTheIterate
import YangMills.Construction.Towers.FibresOfARealAnalyticSubmersion
import YangMills.Construction.Towers.HessianOfARestriction
import YangMills.Construction.Towers.HessianOfTheLastPartialSum
import YangMills.Construction.Towers.RealAnalyticFunctionsAreOfClassTwoOnSubsets
import YangMills.Construction.Towers.SmallNeighbourhoodsForThePartialSums
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Tower
namespace FibreCurves
theorem isHessianFormAt_chosen {X T S : Type} [AddCommGroup T] [Module ℝ T] [AddCommGroup S]
    [Module ℝ S] (R : Geometry.CurveData X T) {N : Set X} {F : X → ℝ} {x : X}
    (e : S →ₗ[ℝ] R.tangentSpan N x) (ι : S → T) (he : ∀ v, (e v : T) = ι v)
    (h : R.HasUniqueHessianAt N F x) : R.IsHessianFormAt ι N F x (R.hessianForm ι N F x) := by
  obtain ⟨Q, hQ, -⟩ := h
  have hex : ∃ Q' : QuadraticForm ℝ S, R.IsHessianFormAt ι N F x Q' :=
    ⟨Q.comp e, fun I γ v h1 h2 h3 h4 => hQ I γ (e v) h1 h2 h3 (by rw [he]; exact h4)⟩
  exact Classical.epsilon_spec hex
theorem exists_subinterval_mapsTo {X : Type} [TopologicalSpace X] {γ : ℝ → X} {I : Set ℝ}
    {O : Set X} (hI : IsOpenIntervalAroundZero I) (hγ : ContinuousAt γ 0) (hO : IsOpen O)
    (h0 : γ 0 ∈ O) :
    ∃ J : Set ℝ, IsOpenIntervalAroundZero J ∧ J ⊆ I ∧ ∀ t ∈ J, γ t ∈ O := by
  have h : I ∩ γ ⁻¹' O ∈ 𝓝 (0 : ℝ) :=
    inter_mem (hI.1.mem_nhds hI.2.2) (hγ.preimage_mem_nhds (hO.mem_nhds h0))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.1 h
  rw [Real.ball_eq_Ioo] at hsub
  refine ⟨Ioo (0 - ε) (0 + ε), ⟨isOpen_Ioo, ordConnected_Ioo, by simp [hε]⟩,
    fun t ht => (hsub ht).1, fun t ht => (hsub ht).2⟩
end FibreCurves
theorem fibreCurvesAndHessian_holds
    (hLast : LastPartialHessianFormula)
    (hCo : ProlongCompositesAndVertexLayers.Statement)
    (hE : BondSetFields.ProductStructureHolds)
    (hSub : SubmersionFibresAreSubmanifolds)
    (hY : RestrictionHessian.Statement) (hNb : FibreNeighbourhoodsOfSteps)
    (hC2 : AnalyticIsC2OnSubsetsStatement)
    (hNear : SmallNhdsForPartialGaugedActions) :
    FibreCurvesAndHessian := by
  intro L n k hL hn hk
  have hN : IsSmoothingFibreNhd L n k (smoothingFibreNhd L n k) :=
    (hLast L n k hL hn hk).1
  have hop : ∀ 𝒰 : Set (Edge L n k 0 → Matrices.ComplexMatrix2),
      IsOpenFieldSet PeriodicLattice.compactGaugeGroup 𝒰 ↔
      𝒰 ⊆ fieldSpace L n k 0 ∧ Matrices.ComplexMatrix2.IsRelativelyOpen (fieldSpace L n k 0) 𝒰 := by
    intro 𝒰
    have A := ((hE L hL k 0 (Nat.zero_le k)).1 n hn).2.2.2.2.2.2.2.2.1
    exact ⟨fun h => ⟨h.1, (A 𝒰 h.1).2 h.2⟩, fun h => ⟨h.1, (A 𝒰 h.1).1 h.2⟩⟩
  obtain ⟨hFrom, hObj, -⟩ := hCo.1 L n k hL hn hk
  obtain ⟨𝒲, h𝒲, hsub, hAn, hMan, hOnto⟩ :=
    hNear L n k hL hn hk _ hN.isOpenNhd
  obtain ⟨hc𝒲, O, hO, e𝒲⟩ := (hop 𝒲).1 h𝒲.1
  have h1O : (fun _ => (1 : Matrices.ComplexMatrix2)) ∈ O := by
    have h2 := h𝒲.2
    rw [e𝒲] at h2
    exact h2.1
  have h𝒲near : EventuallyNearIdentity (fieldSpace L n k 0) fun V => V ∈ 𝒲 := by
    refine mem_nhdsWithin.2 ⟨O, hO, h1O, fun V hV => ?_⟩
    show V ∈ 𝒲
    rw [e𝒲]
    exact hV
  have hQ : EventuallyNearIdentity (fieldSpace L n k 0) fun U => U ∈ 𝒲 ∧
      ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k, ∀ B : edgeFormSpace L n k 0,
        (T B : Edge L n k k → Matrices.ComplexMatrix2) =
          leftDifferential (smoothingIter L n k k) U (B : Edge L n k 0 → Matrices.ComplexMatrix2) :=
    Filter.Eventually.and h𝒲near (hObj.iterDifferential_linear k le_rfl)
  have hBase : EventuallyNearIdentity (fieldSpace L n k k) fun W => chainBottom W ∈ 𝒲 ∧
      ∃ T : edgeFormSpace L n k 0 →ₗ[ℝ] edgeFormSpace L n k k, ∀ B : edgeFormSpace L n k 0,
        (T B : Edge L n k k → Matrices.ComplexMatrix2) =
          leftDifferential (smoothingIter L n k k) (chainBottom W)
            (B : Edge L n k 0 → Matrices.ComplexMatrix2) := by
    refine (((hFrom.tendsto 0 (Nat.zero_le k)).eventually hQ).and hFrom.comp_zero_eq).mono ?_
    rintro W ⟨h, e⟩
    rw [e, ← chainBottom_eq W] at h
    exact h
  refine ((hBase.and hN.fibre_structure).and hN.critical_bottom).mono ?_
  rintro W ⟨⟨⟨hU𝒲, hlin⟩, hfib⟩, hcrit⟩
  have hspec := Classical.epsilon_spec hlin
  have hsubFibre : ∀ V, V ∈ fibreWithin 𝒲 (smoothingIter L n k k) W →
      V ∈ smoothingIterFibre (smoothingFibreNhd L n k) W :=
    fun V hV => ⟨hsub hV.1, hV.2⟩
  have hopen : Matrices.ComplexMatrix2.IsRelativelyOpen (smoothingIterFibre (smoothingFibreNhd L n k) W)
      (fibreWithin 𝒲 (smoothingIter L n k k) W) := by
    refine ⟨O, hO, ?_⟩
    ext U
    constructor
    · intro h
      have h3 := h.1
      rw [e𝒲] at h3
      exact ⟨h3.1, hsub h.1, h.2⟩
    · rintro ⟨h1, h2, h3⟩
      refine ⟨?_, h3⟩
      rw [e𝒲]
      exact ⟨h1, hN.isOpenNhd.1.1 h2⟩
  have hloc := hNb.2.2.1 L n k 0
  have key := hNb.1 _ _ (fieldCurveData L n k 0) hloc _ _ (plaquetteAction L n k) hopen (chainBottom W)
  have hcA : (fieldCurveData L n k 0).IsCriticalOn
      (fibreWithin 𝒲 (smoothingIter L n k k) W) (plaquetteAction L n k) (chainBottom W) :=
    key.1.2 ⟨⟨hU𝒲, hcrit.1.2⟩, hcrit⟩
  have hsubm := hSub L n k 0 k hL hn (Nat.zero_le k) le_rfl 𝒲 (smoothingIter L n k k) hMan
    (fun V hV => hOnto V hV) W
  have hsm : IsFieldSubmanifold (fibreWithin 𝒲 (smoothingIter L n k k) W) := hsubm.1.1
  obtain ⟨-, fin, -⟩ := id hsm
  let := fin
  have hYA := hY.2 L n k 0 _ _ (plaquetteAction L n k) hsm hsm subset_rfl
    (hC2 L n k 0 hL hn (Nat.zero_le k) 𝒲 _ _ (hAn 0 (Nat.zero_le k)) fun V hV => hV.1)
  obtain ⟨hparA, hlocA, hhessA, -⟩ := hYA
  have hmem : ∀ v : LinearMap.ker (topConstraintMap L n k W),
      (edgeFormSpace L n k 0).subtype ((LinearMap.ker (topConstraintMap L n k W)).subtype v) ∈
        (fieldCurveData L n k 0).tangentSpan
          (fibreWithin 𝒲 (smoothingIter L n k k) W) (chainBottom W) := by
    intro v
    refine (hsubm.2 _ hU𝒲 hcrit.1.2 _).2 ⟨v.1.2, ?_⟩
    have h1 : (topConstraintMap L n k W v.1 : Edge L n k k → Matrices.ComplexMatrix2) = 0 := by
      rw [LinearMap.mem_ker.1 v.2]
      rfl
    exact (hspec v.1).symm.trans h1
  let e : LinearMap.ker (topConstraintMap L n k W) →ₗ[ℝ] (fieldCurveData L n k 0).tangentSpan
      (fibreWithin 𝒲 (smoothingIter L n k k) W) (chainBottom W) :=
    LinearMap.codRestrict _ ((edgeFormSpace L n k 0).subtype ∘ₗ
      (LinearMap.ker (topConstraintMap L n k W)).subtype) hmem
  have hIA := FibreCurves.isHessianFormAt_chosen (fieldCurveData L n k 0) e
    (fun v : LinearMap.ker (topConstraintMap L n k W) =>
      (v.1.1 : Edge L n k 0 → Matrices.ComplexMatrix2))
    (fun _ => rfl) (hhessA _ hcA)
  have eH := (key.2 hcA).2 (LinearMap.ker (topConstraintMap L n k W))
    (fun v : LinearMap.ker (topConstraintMap L n k W) =>
      (v.1.1 : Edge L n k 0 → Matrices.ComplexMatrix2))
  refine ⟨hN.isOpenNhd.1.1 hcrit.1.1, hcrit, ?_, ?_, ?_⟩
  · intro I γ v hγ hγN hγ0 hγt
    obtain ⟨hI, hcont, hcut⟩ := hloc.isTwiceDiffCurve_local I γ hγ
    have h0 : γ 0 ∈ O := by
      have h3 := hU𝒲
      rw [e𝒲] at h3
      rw [hγ0]
      exact h3.1
    obtain ⟨J, hJ, hJI, hJO⟩ := FibreCurves.exists_subinterval_mapsTo hI hcont hO h0
    have hγJ : MapsTo γ J (fibreWithin 𝒲 (smoothingIter L n k k) W) := by
      intro t ht
      have hF := hγN (hJI ht)
      refine ⟨?_, hF.2⟩
      rw [e𝒲]
      exact ⟨hJO t ht, hN.isOpenNhd.1.1 hF.1⟩
    have := hIA J γ v (hcut J hJ hJI) hγJ hγ0 hγt
    rw [← this, eH]
    rfl
  · intro B
    obtain ⟨d, Oφ, φ, z, hφ, hz, hφz⟩ := hlocA _ hcA.1
    obtain ⟨D, -, hread⟩ := hparA (Fin d → ℝ) Oφ φ z hφ hz
    obtain ⟨I, γ, hγ, hγN, hγ0, hγt⟩ := hread.exists_curve (by rw [hφz]; exact hcA) B.1.1
      (by rw [hφz]; exact hmem B)
    rw [hφz] at hγ0
    exact ⟨I, γ, hγ, fun t ht => hsubFibre _ (hγN ht), hγ0, hγt⟩
  · intro I γ hγ hγN hγ0
    have htan : (fieldCurveData L n k 0).tangent γ ∈ (fieldCurveData L n k 0).tangentSpan
        (smoothingIterFibre (smoothingFibreNhd L n k) W) (chainBottom W) :=
      Submodule.subset_span ⟨I, γ, hγ.1, hγN, hγ0, rfl⟩
    obtain ⟨hf, h0⟩ := (hfib.2 _ hcrit.1 _).1 htan
    refine ⟨⟨⟨_, hf⟩, LinearMap.mem_ker.2 (Subtype.ext ?_)⟩, rfl⟩
    exact (hspec ⟨_, hf⟩).trans h0
end YangMills.Construction.Tower
end
