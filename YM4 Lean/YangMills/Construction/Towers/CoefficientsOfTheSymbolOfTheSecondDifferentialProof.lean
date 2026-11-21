import YangMills.Construction.PeriodicOperators.IndexSetsOfATower
import YangMills.Construction.PeriodicOperators.WidthsAtWhichJetsAreInvertible
import YangMills.Construction.Towers.CoefficientsOfTheSymbolOfTheSecondDifferential
import YangMills.Construction.Towers.IndexSetsArePeriodic
import YangMills.Construction.Towers.TheTwoOperatorFunctionsAreLocal
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.SymbolCoefficients
open YangMills.Construction.PeriodicOperators
open YangMills.Construction.PeriodicOperators.StripBound (logDetForm)
open YangMills.Construction.Coordinates.ComplexCoordinates.LogDetSecondDeriv (IsHolomorphicScalarIn)
theorem disjSum_isPeriodic {I J : PeriodicData} (hI : IsPeriodic I)
    (hJ : IsPeriodic J) : IsPeriodic (I.disjSum J) where
  translate_zero x := by
    cases x with
    | inl i => exact congrArg Sum.inl (hI.translate_zero i)
    | inr i => exact congrArg Sum.inr (hJ.translate_zero i)
  translate_add a b x := by
    cases x with
    | inl i => exact congrArg Sum.inl (hI.translate_add a b i)
    | inr i => exact congrArg Sum.inr (hJ.translate_add a b i)
  free a x hx := by
    cases x with
    | inl i => exact hI.free a i (Sum.inl.inj hx)
    | inr i => exact hJ.free a i (Sum.inr.inj hx)
  finite_quot := by
    have := hI.finite_quot
    have := hJ.finite_quot
    let f : I.UnitQuot ⊕ J.UnitQuot → (I.disjSum J).UnitQuot := Sum.elim
      (Quot.lift (fun i => (I.disjSum J).mkQuot 1 (Sum.inl i)) (by
        rintro i _ ⟨a, rfl⟩
        exact Quot.sound ⟨a, rfl⟩))
      (Quot.lift (fun i => (I.disjSum J).mkQuot 1 (Sum.inr i)) (by
        rintro i _ ⟨a, rfl⟩
        exact Quot.sound ⟨a, rfl⟩))
    refine Finite.of_surjective f fun q => ?_
    induction q using Quot.ind with
    | mk x =>
      cases x with
      | inl i => exact ⟨Sum.inl (I.mkQuot 1 i), rfl⟩
      | inr i => exact ⟨Sum.inr (J.mkQuot 1 i), rfl⟩
  pos_translate a x := by
    cases x with
    | inl i => exact hI.pos_translate a i
    | inr i => exact hJ.pos_translate a i
  finite_components := by
    have := hI.finite_components
    have := hJ.finite_components
    exact inferInstanceAs (Finite (I.Component ⊕ J.Component))
  componentOf_translate a x := by
    cases x with
    | inl i => exact congrArg Sum.inl (hI.componentOf_translate a i)
    | inr i => exact congrArg Sum.inr (hJ.componentOf_translate a i)
  weight_pos c := by
    cases c with
    | inl d => exact hI.weight_pos d
    | inr d => exact hJ.weight_pos d
theorem imStrip_mono {a b : ℝ} (hab : a ≤ b) : imStrip a ⊆ imStrip b :=
  fun _ hz μ => (hz μ).trans hab
theorem isHolomorphicScalarIn_mono {U V : Set (Fin 4 → ℂ)} {f : (Fin 4 → ℂ) → ℂ} (hV : IsOpen V)
    (hVU : V ⊆ U) (hf : IsHolomorphicScalarIn U f) : IsHolomorphicScalarIn V f :=
  ⟨hV, hf.2.1.mono hVU, fun z hz i => hf.2.2 z (hVU hz) i⟩
theorem isHolomorphicScalarIn_neg_half_add {U : Set (Fin 4 → ℂ)} {f g : (Fin 4 → ℂ) → ℂ}
    (hf : IsHolomorphicScalarIn U f) (hg : IsHolomorphicScalarIn U g) :
    IsHolomorphicScalarIn U fun z => -(1 / 2) * f z + g z := by
  refine ⟨hf.1, (hf.2.1.const_smul (-(1 / 2) : ℂ)).add hg.2.1, fun z hz i => ?_⟩
  filter_upwards [hf.2.2 z hz i, hg.2.2 z hz i] with w hfw hgw
  exact (hfw.const_smul (-(1 / 2) : ℂ)).add hgw
theorem bilinear_eq_sum_coeffs {ι : Type} [Fintype ι] [DecidableEq ι]
    (B : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) →ₗ[ℂ] ℂ) (u v : ι → ℂ) :
    B u v = ∑ i, ∑ j, B (Pi.single i 1) (Pi.single j 1) * u i * v j := by
  have hsum : ∀ w : ι → ℂ, ∑ i, w i • (Pi.single i 1 : ι → ℂ) = w := by
    intro w
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  calc B u v = B (∑ i, u i • Pi.single i 1) (∑ j, v j • Pi.single j 1) := by rw [hsum, hsum]
    _ = _ := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
open Classical in
theorem exists_coeffs_of_invertibleJets (hJet : InvertibleJetWidths.Claim)
    (hBd : StripBound.Claim) {F I : PeriodicData}
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} (hT : IsLocalOpFun F I I T) {δ : ℝ}
    (hδ : HasInvertibleJetsAtWidth F I T δ) :
    ∃ a : F.UnitQuot → F.UnitQuot → (Fin 4 → ℂ) → ℂ,
      (∀ i j, IsHolomorphicScalarIn (interior (imStrip δ)) (a i j) ∧
        ∃ C : ℝ, ∀ z ∈ imStrip δ, ‖a i j z‖ ≤ C) ∧
      ∀ z ∈ imStrip δ, ∀ u v : F.UnitQuot → ℂ,
        logDetForm F I T z u v =
          ∑ᶠ i, ∑ᶠ j, a i j z * u i * v j := by
  obtain ⟨-, hwid⟩ := hJet F I hF hI T hT
  obtain ⟨-, -, hre, hfm, hco, -⟩ := hwid δ hδ
  obtain ⟨-, -, ⟨C, hC⟩, -, -⟩ := hBd F I hF hI T hT hre δ hδ.1 hfm
  choose a ha hav using hco.2
  have := hF.finite_quot
  let := Fintype.ofFinite F.UnitQuot
  refine ⟨a, fun i j => ⟨?_, ?_⟩, fun z hz u v => ?_⟩
  · exact isHolomorphicScalarIn_mono isOpen_interior
      (interior_mono (imStrip_mono (by linarith [hδ.1]))) (ha i j)
  · refine ⟨C * wNorm (F.quotWeight 1) (Pi.single i 1) *
      wNorm (F.quotWeight 1) (Pi.single j 1), fun z hz => ?_⟩
    rw [hav i j z hz]
    exact hC z hz _ _
  · obtain ⟨B, hBz⟩ := hfm.bilinear z hz
    rw [hBz, bilinear_eq_sum_coeffs B u v]
    simp only [finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hav i j z hz, hBz]
theorem exists_larger_invertibleJets_width (hJet : InvertibleJetWidths.Claim) {F I : PeriodicData}
    (hF : IsPeriodic F) (hI : IsPeriodic I)
    {T : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ} (hT : IsLocalOpFun F I I T) {δ : ℝ}
    (hδ : HasInvertibleJetsAtWidth F I T δ) :
    ∃ η : ℝ, δ < η ∧ ∀ ε : ℝ, 0 < ε → ε ≤ η → HasInvertibleJetsAtWidth F I T ε := by
  obtain ⟨-, hwid⟩ := hJet F I hF hI T hT
  obtain ⟨η, hδη, hη⟩ := (hwid δ hδ).1.2
  exact ⟨η, hδη, (hwid η hη).1.1⟩
theorem symbolCoefficientsExist_holds (hJet : InvertibleJetWidths.Claim)
    (hBd : StripBound.Claim)
    (hLoc : OperatorFunctionsAreLocal)
    (hPer : LocalKernels.IndexSetPeriodicity.Statement)
    (hIdx : TowerIndexSets.Claim) : SymbolCoefficientsExist := by
  intro L hL hs n hn δ hδ
  obtain ⟨hv, hg⟩ := hLoc L hL hs n hn
  have hF : IsPeriodic (fieldPeriodicData L n hL) :=
    ((hPer L hs n).2 (LocalKernels.fieldIndices L n hL)).1
  have hV : IsPeriodic (vectorIndices L n) :=
    disjSum_isPeriodic (hIdx L hs n 0 (Nat.zero_le n)).2.1 (hIdx L hs n n le_rfl).2.1
  have hG : IsPeriodic (ghostIndices L n) :=
    disjSum_isPeriodic (hIdx L hs n 0 (Nat.zero_le n)).1 (hIdx L hs n n le_rfl).1
  obtain ⟨ηv, hδv, hwv⟩ := exists_larger_invertibleJets_width hJet hF hV hv hδ.1
  obtain ⟨ηg, hδg, hwg⟩ := exists_larger_invertibleJets_width hJet hF hG hg hδ.2
  have hlt : δ < min ηv ηg := lt_min hδv hδg
  have hpos : 0 < min ηv ηg := hδ.1.1.trans hlt
  have hjoint : IsJointInvertibilityWidth L n hL (min ηv ηg) :=
    ⟨hwv _ hpos (min_le_left _ _), hwg _ hpos (min_le_right _ _)⟩
  obtain ⟨av, hav, hsv⟩ := exists_coeffs_of_invertibleJets hJet hBd hF hV hv hjoint.1
  obtain ⟨ag, hag, hsg⟩ := exists_coeffs_of_invertibleJets hJet hBd hF hG hg hjoint.2
  refine ⟨min ηv ηg, hlt, hjoint, fun i j z => -(1 / 2) * av i j z + ag i j z,
    fun i j => ⟨isHolomorphicScalarIn_neg_half_add (hav i j).1 (hag i j).1, ?_⟩,
    fun z hz u v => ?_⟩
  · obtain ⟨Cv, hCv⟩ := (hav i j).2
    obtain ⟨Cg, hCg⟩ := (hag i j).2
    refine ⟨‖(-(1 / 2) : ℂ)‖ * Cv + Cg, fun z hz => ?_⟩
    calc ‖-(1 / 2) * av i j z + ag i j z‖
        ≤ ‖(-(1 / 2) : ℂ) * av i j z‖ + ‖ag i j z‖ := norm_add_le _ _
      _ = ‖(-(1 / 2) : ℂ)‖ * ‖av i j z‖ + ‖ag i j z‖ := by rw [norm_mul]
      _ ≤ ‖(-(1 / 2) : ℂ)‖ * Cv + Cg :=
        add_le_add (mul_le_mul_of_nonneg_left (hCv z hz) (norm_nonneg _)) (hCg z hz)
  · have hz' : z ∈ imStrip (min ηv ηg) := imStrip_mono hlt.le hz
    have := hF.finite_quot
    let := Fintype.ofFinite (fieldPeriodicData L n hL).UnitQuot
    have hev := hsv z hz' u v
    have heg := hsg z hz' u v
    have hdef : secondVariationSymbol L n hL z u v =
        -(1 / 2) * logDetForm _ _ (vectorOpFn L n hL) z u v +
          logDetForm _ _ (ghostOpFn L n hL) z u v := rfl
    rw [hdef, hev, heg]
    simp only [finsum_eq_sum_of_fintype, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
end YangMills.Construction.Tower.FullSpace.SymbolCoefficients
end
