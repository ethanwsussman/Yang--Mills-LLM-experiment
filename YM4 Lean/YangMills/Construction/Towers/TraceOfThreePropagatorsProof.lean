import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.CalculusOfJets
import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.RiemannSumsAndShiftsProof
import YangMills.Construction.PeriodicOperators.TraceOfAProductOfSixJets
import YangMills.Construction.Towers.IntegralOfTheThirdPowersOfTheFreeSymbols
import YangMills.Construction.Towers.TheNumbersOfTheStripOfTheFreeOperatorsAreAdmitted
import YangMills.Construction.Towers.ThirdPowerNormOfAMatrixThatMultipliesTheCoefficients
import YangMills.Construction.Towers.TraceOfThreePropagators
import Mathlib
set_option autoImplicit false
open Set MeasureTheory
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.BackgroundJets.ResolventTrace
open PeriodicOperators
open PeriodicOperators.JetQuad
open PeriodicOperators.StripSymbols (openStripInterior)
open PeriodicOperators.JetDomains (JetAlgebra SymbolHolomorphicNear)
open TraceBound (schattenThreeNorm)
open RealPower (rpowPos)
section Bracketings
variable {I : PeriodicData}
def rightNestedMul (p : Fin 4 → ℂ) (T : JetQuad I I) : List (JetQuad I I) → JetQuad I I
  | [] => T
  | S :: l => mul p T (rightNestedMul p S l)
theorem eqAsJet_refl (δ : ℝ) (p : Fin 4 → ℂ) (T : JetQuad I I) : EqAsJet δ p T T :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
theorem eqAsJet_trans {δ : ℝ} {p : Fin 4 → ℂ} {T S R : JetQuad I I} (h : EqAsJet δ p T S)
    (h' : EqAsJet δ p S R) : EqAsJet δ p T R :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.trans h'.2.2.2⟩
theorem isJet_rightNestedMul {δ : ℝ} {p : Fin 4 → ℂ} (F : JetAlgebra I I I δ p) :
    ∀ (l : List (JetQuad I I)) (T : JetQuad I I), IsJet δ p T → (∀ S ∈ l, IsJet δ p S) →
      IsJet δ p (rightNestedMul p T l)
  | [], _, hT, _ => hT
  | S :: l, _, hT, hl =>
    F.mul_isJet _ _ hT (isJet_rightNestedMul F l S (hl S (by simp))
      fun R hR => hl R (by simp [hR]))
theorem mul_rightNestedMul_eqAsJet {δ : ℝ} {p : Fin 4 → ℂ} (F : JetAlgebra I I I δ p)
    (hA : ∀ T S R : JetQuad I I, IsJet δ p T → IsJet δ p S → IsJet δ p R →
      EqAsJet δ p (mul p (mul p T S) R) (mul p T (mul p S R)))
    (hE : ∀ T T' S S' : JetQuad I I, IsJet δ p T → IsJet δ p T' → EqAsJet δ p T T' →
      IsJet δ p S → IsJet δ p S' → EqAsJet δ p S S' → EqAsJet δ p (mul p T S) (mul p T' S'))
    (T₂ : JetQuad I I) (l₂ : List (JetQuad I I)) (h₂ : IsJet δ p T₂)
    (hl₂ : ∀ S ∈ l₂, IsJet δ p S) :
    ∀ (l₁ : List (JetQuad I I)) (T₁ : JetQuad I I), IsJet δ p T₁ → (∀ S ∈ l₁, IsJet δ p S) →
      EqAsJet δ p (mul p (rightNestedMul p T₁ l₁) (rightNestedMul p T₂ l₂))
        (rightNestedMul p T₁ (l₁ ++ T₂ :: l₂))
  | [], _, _, _ => eqAsJet_refl _ _ _
  | S :: l, T₁, h₁, hl => by
    have hS : IsJet δ p S := hl S (by simp)
    have hl' : ∀ R ∈ l, IsJet δ p R := fun R hR => hl R (by simp [hR])
    have hR₂ := isJet_rightNestedMul F l₂ T₂ h₂ hl₂
    have hR₁ := isJet_rightNestedMul F l S hS hl'
    have ih := mul_rightNestedMul_eqAsJet F hA hE T₂ l₂ h₂ hl₂ l S hS hl'
    have hall : ∀ R ∈ l ++ T₂ :: l₂, IsJet δ p R := by
      intro R hR
      rcases List.mem_append.1 hR with h | h
      · exact hl' R h
      · rcases List.mem_cons.1 h with rfl | h
        · exact h₂
        · exact hl₂ R h
    exact eqAsJet_trans (hA T₁ _ _ h₁ hR₁ hR₂)
      (hE _ _ _ _ h₁ h₁ (eqAsJet_refl _ _ _) (F.mul_isJet _ _ hR₁ hR₂)
        (isJet_rightNestedMul F _ S hS hall) ih)
theorem exists_eqAsJet_rightNestedMul {δ : ℝ} {p : Fin 4 → ℂ} (F : JetAlgebra I I I δ p)
    (hA : ∀ T S R : JetQuad I I, IsJet δ p T → IsJet δ p S → IsJet δ p R →
      EqAsJet δ p (mul p (mul p T S) R) (mul p T (mul p S R)))
    (hE : ∀ T T' S S' : JetQuad I I, IsJet δ p T → IsJet δ p T' → EqAsJet δ p T T' →
      IsJet δ p S → IsJet δ p S' → EqAsJet δ p S S' → EqAsJet δ p (mul p T S) (mul p T' S'))
    {l : List (JetQuad I I)} {X : JetQuad I I} (h : IsBracketedProductOf p l X) :
    (∀ S ∈ l, IsJet δ p S) →
      ∃ T l', l = T :: l' ∧ IsJet δ p X ∧ EqAsJet δ p X (rightNestedMul p T l') := by
  induction h with
  | leaf T =>
    intro hl
    exact ⟨T, [], rfl, hl T (by simp), eqAsJet_refl _ _ _⟩
  | @node l l' T S _ _ ihT ihS =>
    intro hl
    obtain ⟨T₁, l₁, rfl, hT, eT⟩ := ihT fun R hR => hl R (List.mem_append_left _ hR)
    obtain ⟨T₂, l₂, rfl, hS, eS⟩ := ihS fun R hR => hl R (List.mem_append_right _ hR)
    have h₁ : IsJet δ p T₁ := hl T₁ (by simp)
    have h₂ : IsJet δ p T₂ := hl T₂ (by simp)
    have hl₁ : ∀ R ∈ l₁, IsJet δ p R := fun R hR => hl R (by simp [hR])
    have hl₂ : ∀ R ∈ l₂, IsJet δ p R := fun R hR => hl R (by simp [hR])
    refine ⟨T₁, l₁ ++ T₂ :: l₂, rfl, F.mul_isJet _ _ hT hS, ?_⟩
    exact eqAsJet_trans
      (hE _ _ _ _ hT (isJet_rightNestedMul F l₁ T₁ h₁ hl₁) eT hS
        (isJet_rightNestedMul F l₂ T₂ h₂ hl₂) eS)
      (mul_rightNestedMul_eqAsJet F hA hE T₂ l₂ h₂ hl₂ l₁ T₁ h₁ hl₁)
end Bracketings
theorem isHolomorphicIn_congr {N N' : ℕ} {O : Set (Coordinates.ComplexCoordinates N)}
    {f g : Coordinates.ComplexCoordinates N → Coordinates.ComplexCoordinates N'}
    (h : Coordinates.ComplexCoordinates.IsHolomorphicIn O g)
    (e : EqOn f g O) : Coordinates.ComplexCoordinates.IsHolomorphicIn O f := by
  refine ⟨h.1, h.2.1.congr e, fun a ha j => ?_⟩
  have hcont : Continuous fun ζ : ℂ => a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j := by
    fun_prop
  have hmem : ∀ᶠ ζ in nhds (0 : ℂ), a + ζ • Coordinates.ComplexCoordinates.stdBasisVector j ∈ O :=
    hcont.continuousAt.eventually (by simpa using h.1.mem_nhds ha)
  filter_upwards [h.2.2 a ha j, hmem.eventually_nhds] with ζ hd hz
  exact hd.congr_of_eventuallyEq (hz.mono fun ζ' h' => e h')
theorem toComplexVec_add_mem_imStrip {ς : ℝ} {ϑ : Fin 4 → ℂ} (h : ϑ ∈ imStrip ς)
    (κ : InfiniteLattice.AmbientSpace) : toComplexVec κ + ϑ ∈ imStrip ς := by apply _root_.YangMills.Construction.PeriodicOperators.RiemannSums.toComplexVec_add_mem_imStrip <;> assumption
theorem imStrip_mono {a b : ℝ} (h : a ≤ b) : imStrip a ⊆ imStrip b :=
  fun _ hκ μ => (hκ μ).trans h
theorem traceBoundOn_of_matFunKernel (hLocal : JetDomains.OpFunJetTheory)
    (hJets : JetCalculus.Claim) (hW2 : JetArgumentsAndEqualJets)
    (hQ2 : StripSymbols.Claim) (hD : SixJetTrace.Bound)
    (hδ : 0 < stripHalfWidth) (hδ' : 2 * stripHalfWidth < 1 / 8)
    {I : PeriodicData} (hI : IsPeriodic I) [Finite I.UnitQuot] (hne : Nonempty I.UnitQuot)
    (M : (Fin 4 → ℂ) → QuotHom I I) (P : I.Carrier → I.Carrier → ℂ)
    (hP : P = matFunKernel I I M)
    (hol : QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior (1 / 8)) M)
    (bdd : QuotHomFamilyBoundedOn (openStripInterior (1 / 8)) M)
    (qp : IsQuasiPeriodic (imStrip (1 / 8)) M) (γ : ℝ) (hγ : 0 ≤ γ)
    (third : ∀ ϑ ∈ imStrip stripHalfWidth,
      Continuous (fun κ : InfiniteLattice.AmbientSpace =>
        rpowPos (schattenThreeNorm (wInner (I.quotWeight 1)) (M (toComplexVec κ + ϑ))) 3) ∧
      ((2 * Real.pi) ^ 4)⁻¹ * ∫ κ in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi),
        rpowPos (schattenThreeNorm (wInner (I.quotWeight 1)) (M (toComplexVec κ + ϑ))) 3
        ≤ γ) :
    TraceBoundOn γ I P := by
  have hint := hQ2.1 (1 / 8) (by norm_num)
  obtain ⟨hinteq, hopen, hsub, hcontains⟩ := hint
  have hin : ∀ υ' : ℝ, 0 < υ' → υ' < 1 / 8 → imStrip υ' ⊆ openStripInterior (1 / 8) :=
    fun υ' h h' => by
      rw [hinteq]; exact hcontains υ' h h'
  have hinS : openStripInterior (1 / 8) ⊆ imStrip (1 / 8) := by rw [hinteq]; exact hsub
  have hopenI : IsOpen (openStripInterior (1 / 8)) := by rw [hinteq]; exact hopen
  obtain ⟨-, -, -, hper, hformed, hsym⟩ :=
    (hQ2.2.1 I I hI hI).2.2.1 (1 / 8) (by norm_num) M hol
      (fun υ' h h' e => by
        obtain ⟨C, hC⟩ := bdd e
        exact ⟨C, fun x hx => hC x (hin υ' h h' hx)⟩)
      (fun e κ hκ => qp e κ (hinS hκ))
  subst hP
  set P := matFunKernel I I M with hPdef
  have hstrip2 : imStrip (2 * stripHalfWidth) ⊆ openStripInterior (1 / 8) :=
    hin _ (by positivity) hδ'
  have hstrip1 : imStrip stripHalfWidth ⊆ openStripInterior (1 / 8) :=
    (imStrip_mono (by linarith)).trans hstrip2
  have hsymhol : QuotHomFamilyHolomorphicOn (n := 4) (openStripInterior (1 / 8)) (symbolHom I I P) :=
    ⟨hol.1, hol.2.1, fun e => isHolomorphicIn_congr (hol.2.2 e) fun x hx => by
      funext _
      rw [hsym x hx]⟩
  have hnear : SymbolHolomorphicNear I I (imStrip (2 * stripHalfWidth)) P :=
    ⟨openStripInterior (1 / 8), hopenI, hstrip2, hformed, fun c' c => hsymhol.2.2 (c', c)⟩
  have facts : ∀ p ∈ imStrip stripHalfWidth, JetAlgebra I I I stripHalfWidth p := fun p hp =>
    hLocal.2.2 I I I hI hI hI stripHalfWidth p hδ hp
  have isjet : ∀ p ∈ imStrip stripHalfWidth, IsJet stripHalfWidth p (ofKernel I I P) :=
    fun p hp => (facts p hp).ofKernel_isJet P hper hnear
  have prodjet : ∀ p ∈ imStrip stripHalfWidth, ∀ B₁ B₂ B₃ : JetQuad I I,
      IsJet stripHalfWidth p B₁ → IsJet stripHalfWidth p B₂ → IsJet stripHalfWidth p B₃ →
        IsJet stripHalfWidth p (sixfoldProduct p P B₁ B₂ B₃) := fun p hp B₁ B₂ B₃ h₁ h₂ h₃ => by
    have F := facts p hp
    have hG := isjet p hp
    exact F.mul_isJet _ _ hG (F.mul_isJet _ _ h₁ (F.mul_isJet _ _ hG
      (F.mul_isJet _ _ h₂ (F.mul_isJet _ _ hG h₃))))
  refine ⟨hper, ⟨hformed, hsymhol⟩, hstrip2, isjet, prodjet, ?_, ?_⟩
  · intro p hp B₁ B₂ B₃ h₁ h₂ h₃ X hX
    have F := facts p hp
    have hG := isjet p hp
    have hA : ∀ T S R : JetQuad I I, IsJet stripHalfWidth p T → IsJet stripHalfWidth p S →
        IsJet stripHalfWidth p R →
        EqAsJet stripHalfWidth p (mul p (mul p T S) R) (mul p T (mul p S R)) :=
      fun T S R hT hS hR =>
        ((hJets stripHalfWidth p hδ hp).1 I I I I hI hI hI hI T S R hT hS hR).1
    have hE : ∀ T T' S S' : JetQuad I I, IsJet stripHalfWidth p T → IsJet stripHalfWidth p T' →
        EqAsJet stripHalfWidth p T T' → IsJet stripHalfWidth p S → IsJet stripHalfWidth p S' →
        EqAsJet stripHalfWidth p S S' → EqAsJet stripHalfWidth p (mul p T S) (mul p T' S') :=
      fun T T' S S' hT hT' e hS hS' e' =>
        (hW2.2.1 stripHalfWidth p I I hI hI T T' hT hT' e).2.2.2.2 I hI S S' hS hS' e'
    obtain ⟨T, l, hl, hXj, hXe⟩ := exists_eqAsJet_rightNestedMul F hA hE hX (by
      intro S hS
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hS
      rcases hS with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
    obtain ⟨rfl, rfl⟩ := List.cons.inj hl
    exact ⟨hXj, hXe⟩
  · intro p hp B₁ B₂ B₃ h₁ h₂ h₃
    refine hD I hI hne stripHalfWidth p (symbolHom I I P) γ hδ hp (isjet p hp) hγ ?_
      B₁ B₂ B₃ h₁ h₂ h₃
    intro ϑ hϑ
    have hϑs : ϑ ∈ imStrip stripHalfWidth := by
      rcases hϑ with rfl | rfl | rfl
      · intro μ; simpa using hδ.le
      · exact hp
      · intro μ; simpa using hp μ
    have heq : (fun κ : InfiniteLattice.AmbientSpace => symbolHom I I P (toComplexVec κ + ϑ)) =
        fun κ => M (toComplexVec κ + ϑ) := by
      funext κ
      exact hsym _ (hstrip1 (toComplexVec_add_mem_imStrip hϑs κ))
    have := third ϑ hϑs
    simp only [← congrFun heq] at this
    exact this
theorem cubicBound_nonneg : 0 ≤ FreeResolvents.CubicSumIntegral.cubicBound := by
  unfold FreeResolvents.CubicSumIntegral.cubicBound
  refine mul_nonneg (by positivity) (integral_nonneg fun q => ?_)
  unfold FreeResolvents.CubicSumIntegral.decayMajorant
  positivity
theorem threeResolventTraceBound_holds (hT3 : TowerIndexSets.Claim)
    (hLocal : JetDomains.OpFunJetTheory)
    (hJets : JetCalculus.Claim) (hW2 : JetArgumentsAndEqualJets)
    (hG : FreeResolvents.FreeResolventRoots) (hQ2 : StripSymbols.Claim)
    (hN : FreeStrip.ConstantsAdmissible.ConstantsAreAdmissible)
    (hD : SixJetTrace.Bound)
    (hB : PlaneWaves.ScalingMatrixSchattenCube)
    (hC : FreeResolvents.CubicSumIntegral.Claim) : ThreeResolventTraceBound := by
  obtain ⟨-, -, δ₀, hδ₀, C₀, -, hδ₀', -, -⟩ := hN
  have hw : stripHalfWidth = δ₀ := Part.mem_unique
    (stripHalfWidth_mem (Part.dom_iff_mem.2 ⟨δ₀, hδ₀⟩)) hδ₀
  have hδ : 0 < stripHalfWidth := hw ▸ hδ₀'.1
  have hδ' : 2 * stripHalfWidth < 1 / 8 := by
    rw [hw]; linarith [hδ₀'.2]
  have hδ8 : stripHalfWidth ≤ 1 / 8 := by linarith
  have hb := cubicBound_nonneg
  have key : IsThreeResolventTraceBound (12 * FreeResolvents.CubicSumIntegral.cubicBound) := by
    refine ⟨by positivity, fun L hL k hk => ?_⟩
    obtain ⟨-, hedges, hvertices⟩ : _ ∧ IsPeriodic (colourEdges L k 0) ∧
        IsPeriodic (colourVertices L k 0) := by
      have := hT3 L hL k 0 (Nat.zero_le k)
      exact ⟨trivial, this.2.1, this.1⟩
    have := hedges.finite_quot
    have := hvertices.finite_quot
    obtain ⟨-, -, -, fe, fv, -, -⟩ := hG L hL k hk
    have hm1 : (-1 : ℝ) ∈ FreeResolvents.resolventExponents := by
      simp [FreeResolvents.resolventExponents]
    have hrew : ∀ (c : ℝ) (ϑ : Fin 4 → ℂ) (f : InfiniteLattice.AmbientSpace → ℝ),
        (∀ κ, f κ = c * FreeResolvents.CubicSumIntegral.cubicResolventSum L k ϑ κ) →
        0 ≤ c → c ≤ 12 → ϑ ∈ imStrip stripHalfWidth → Continuous f ∧
          ((2 * Real.pi) ^ 4)⁻¹ * ∫ κ in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi), f κ
            ≤ 12 * FreeResolvents.CubicSumIntegral.cubicBound := by
      intro c ϑ f hf hc hc' hϑ
      obtain ⟨hcont, hle⟩ := hC.2 L hL k hk ϑ (imStrip_mono hδ8 hϑ)
      have hfe : f = fun κ =>
          c * FreeResolvents.CubicSumIntegral.cubicResolventSum L k ϑ κ := funext hf
      subst hfe
      refine ⟨continuous_const.mul hcont, ?_⟩
      rw [integral_const_mul]
      calc _ = c * (((2 * Real.pi) ^ 4)⁻¹ *
            ∫ κ in Icc (fun _ : Fin 4 => -Real.pi) (fun _ => Real.pi),
              FreeResolvents.CubicSumIntegral.cubicResolventSum L k ϑ κ) := by ring
        _ ≤ c * FreeResolvents.CubicSumIntegral.cubicBound :=
            mul_le_mul_of_nonneg_left hle hc
        _ ≤ _ := mul_le_mul_of_nonneg_right hc' hb
    constructor
    · refine traceBoundOn_of_matFunKernel hLocal hJets hW2 hQ2 hD hδ hδ' hedges
        ⟨(colourEdges L k 0).mkQuot 1 (0, Classical.arbitrary _)⟩
        (FreeResolvents.edgePowMatrix L k (-1)) _ fe.inverse_eq (fe.holomorphicOn _ hm1)
        (fe.boundedOn _ hm1) (fe.quasiPeriodic _ hm1) _ (by positivity) fun ϑ hϑ => ?_
      refine hrew 12 ϑ _ (fun κ => ?_) (by norm_num) le_rfl hϑ
      exact ((hB L hL k hk _ _).1 _
        (fe.scales_unique _ hm1 _ (imStrip_mono hδ8 (toComplexVec_add_mem_imStrip hϑ κ))).1)
    · refine traceBoundOn_of_matFunKernel hLocal hJets hW2 hQ2 hD hδ hδ' hvertices
        ⟨(colourVertices L k 0).mkQuot 1 (0, Classical.arbitrary _)⟩
        (FreeResolvents.vertexPowMatrix L k (-1)) _ fv.inverse_eq (fv.holomorphicOn _ hm1)
        (fv.boundedOn _ hm1) (fv.quasiPeriodic _ hm1) _ (by positivity) fun ϑ hϑ => ?_
      refine hrew 3 ϑ _ (fun κ => ?_) (by norm_num) (by norm_num) hϑ
      exact ((hB L hL k hk _ _).2 _
        (fv.scales_unique _ hm1 _ (imStrip_mono hδ8 (toComplexVec_add_mem_imStrip hϑ κ))).1)
  exact Classical.epsilon_spec (⟨_, key⟩ : ∃ γ, IsThreeResolventTraceBound γ)
end YangMills.Construction.Tower.FullSpace.BackgroundJets.ResolventTrace
end
