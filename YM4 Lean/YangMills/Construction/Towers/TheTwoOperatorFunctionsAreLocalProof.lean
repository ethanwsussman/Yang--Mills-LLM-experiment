import YangMills.Construction.PeriodicOperators.MultiplesOfLocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.ProductOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.SumOfLocalOperatorFunctions
import YangMills.Construction.PeriodicOperators.TransposeOfALocalOperatorFunction
import YangMills.Construction.Towers.AveragesOfTheScaledPictureAreLocalProof
import YangMills.Construction.Towers.ConfigurationsNearOneHaveSmallIterates
import YangMills.Construction.Towers.FieldsAndTheirValues
import YangMills.Construction.Towers.IndexSetsArePeriodic
import YangMills.Construction.Towers.TheBackgroundKernelAndTheCovariantLaplacianAreFormed
import YangMills.Construction.Towers.TheThreeKernelsAsFunctionsOfValuesAreLocal
import YangMills.Construction.Towers.TheTwoOperatorFunctionsAreLocal
import YangMills.Construction.Towers.TheUnsymmetrisedBackgroundKernelIsLocal
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.OperatorLocality
open PeriodicOperators
open FieldValueFunctions
section Generic
variable {F I J : PeriodicData}
theorem isSupBelow_of_le {ζ : F.Carrier → ℂ} {ρ ρ' : ℝ} (h : IsSupBelow F ζ ρ') (hle : ρ' ≤ ρ) :
    IsSupBelow F ζ ρ := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.isSupBelow_mono <;> assumption
theorem isSupBelow_shiftField {ζ : F.Carrier → ℂ} {ρ : ℝ} (h : IsSupBelow F ζ ρ) (n : Fin 4 → ℤ) :
    IsSupBelow F (shiftField F n ζ) ρ := by apply _root_.YangMills.Construction.Tower.FullSpace.ScaledMeansLocality.isSupBelow_shiftField <;> assumption
theorem isLocalWith_congr {I' : PeriodicData} {T T' : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
    {ρ R : ℝ} (hT : IsLocalWith F I I' T ρ R) (hc : ∀ ζ, IsSupBelow F ζ ρ → T' ζ = T ζ) :
    IsLocalWith F I I' T' ρ R where
  radius_pos := hT.radius_pos
  vanish_far := fun ζ hζ ι' ι hn => by
    rw [hc ζ hζ]
    exact hT.vanish_far ζ hζ ι' ι hn
  holo_entry := fun ι' ι => by
    obtain ⟨l, e, h, hh, he⟩ := hT.holo_entry ι' ι
    exact ⟨l, e, h, hh, fun ζ hζ => by rw [hc ζ hζ]; exact he ζ hζ⟩
  shift_covariant := fun ζ hζ n ι' ι => by
    rw [hc _ (isSupBelow_shiftField hζ n), hc ζ hζ]
    exact hT.shift_covariant ζ hζ n ι' ι
theorem isHolomorphicIn_zero (l : ℕ) (ρ : ℝ) :
    Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1)
      (Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk
        (0 : Coordinates.ComplexCoordinates l) ρ)
      (fun z _ => (fun _ : Coordinates.ComplexCoordinates l => (0 : ℂ)) z) := by
  refine ⟨?_, continuousOn_const, fun a _ j => Filter.Eventually.of_forall fun ζ => ?_⟩
  · simp only [Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk, ofPred_forall]
    exact isOpen_iInter_of_finite fun j => isOpen_lt (by fun_prop) continuous_const
  · exact differentiableAt_const _
theorem isLocalWith_saddleMatrix [Nonempty I.Carrier] {X : (F.Carrier → ℂ) → I.Carrier → I.Carrier → ℂ}
    {Mt : (F.Carrier → ℂ) → I.Carrier → J.Carrier → ℂ} {M : (F.Carrier → ℂ) → J.Carrier → I.Carrier → ℂ}
    {ρ R : ℝ} (hX : IsLocalWith F I I X ρ R) (hMt : IsLocalWith F J I Mt ρ R)
    (hM : IsLocalWith F I J M ρ R) :
    IsLocalWith F (I.disjSum J) (I.disjSum J)
      (fun ζ => saddleMatrix (X ζ) (Mt ζ) (M ζ)) ρ R where
  radius_pos := hX.radius_pos
  vanish_far := fun ζ hζ ι' ι hn => by
    rcases ι' with a | a <;> rcases ι with b | b
    · exact hX.vanish_far ζ hζ a b hn
    · exact hMt.vanish_far ζ hζ a b hn
    · exact hM.vanish_far ζ hζ a b hn
    · rfl
  holo_entry := fun ι' ι => by
    rcases ι' with a | a <;> rcases ι with b | b
    · exact hX.holo_entry a b
    · exact hMt.holo_entry a b
    · exact hM.holo_entry a b
    · obtain ⟨l, e, -, -, -⟩ := hM.holo_entry a (Classical.arbitrary I.Carrier)
      exact ⟨l, e, fun _ => 0, isHolomorphicIn_zero l ρ, fun ζ _ => rfl⟩
  shift_covariant := fun ζ hζ n ι' ι => by
    rcases ι' with a | a <;> rcases ι with b | b
    · exact hX.shift_covariant ζ hζ n a b
    · exact hMt.shift_covariant ζ hζ n a b
    · exact hM.shift_covariant ζ hζ n a b
    · rfl
end Generic
theorem isLocalOpFun_smul (hMult : OpFunMultiples.Claim)
    {F I I' : PeriodicData} (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {S : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ}
    (hS : IsLocalOpFun F I I' S) (c : ℂ) :
    IsLocalOpFun F I I' (fun ζ => c • S ζ) :=
  (hMult F hF 1 0 one_pos (fun μ => by simp) 0 0 I I' hI hI' S hS c).1
theorem isLocalOpFun_swapKernel (hMult : OpFunMultiples.Claim)
    (hTr : OpFunTransposeLocal.Claim)
    {F I I' : PeriodicData} (hF : IsPeriodic F) (hI : IsPeriodic I)
    (hI' : IsPeriodic I') {w w' : ℝ} (hw : 0 < w) (hw' : 0 < w')
    (hwI : ∀ ι, I.weightOf ι = w) (hwI' : ∀ ι, I'.weightOf ι = w')
    {T : (F.Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} (hT : IsLocalOpFun F I I' T) :
    IsLocalOpFun F I' I (fun ζ => swapKernel (T ζ)) := by
  have h := isLocalOpFun_smul hMult hF hI' hI (hTr F I I' hF hI hI' T hT) ((w / w' : ℝ) : ℂ)
  have e : (fun ζ => swapKernel (T ζ)) =
      fun ζ => ((w / w' : ℝ) : ℂ) • opFunTranspose T ζ := by
    funext ζ ι ι'
    have hne : ((w / w' : ℝ) : ℂ) * ((w' / w : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, div_mul_div_comm, mul_comm w w',
        div_self (mul_ne_zero hw'.ne' hw.ne'), Complex.ofReal_one]
    simp only [Pi.smul_apply, smul_eq_mul, opFunTranspose, wTranspose, hwI, hwI', swapKernel]
    rw [← mul_assoc, hne, one_mul]
  rw [e]
  exact h
theorem operatorFunctionsAreLocal_holds (hValues : FieldValues.FieldsAndValuesClaim)
    (hSmall : SmallIterates.SmallIteratesNearOne)
    (hFormed : HessianLaplacian.HessianKernelAndLaplacianExist)
    (hY : RawHessianLocality.Claim)
    (hThree : LocalKernelFunctions.ThreeKernelsLocal)
    (hSum : PeriodicOperators.OpFunAdd.LocalClosed)
    (hProduct : PeriodicOperators.OpFunComp.LocalClosed)
    (hTr : OpFunTransposeLocal.Claim)
    (hMult : OpFunMultiples.Claim)
    (hNumbers : PeriodicOperators.ParameterIndependence.Claim)
    (hSets : PeriodicOperators.TowerIndexSets.Claim)
    (hTower : LocalKernels.IndexSetPeriodicity.Statement) : OperatorFunctionsAreLocal := by
  intro L hL hS k hk
  have hF : IsPeriodic (fieldPeriodicData L k hL) :=
    ((hTower L hS k).2 (LocalKernels.fieldIndices L k hL)).1
  obtain ⟨hS0, hB0, -⟩ := hSets L hS k 0 (Nat.zero_le k)
  obtain ⟨hSk, hBk, -⟩ := hSets L hS k k le_rfl
  have hpos : ∀ j : ℕ, (0 : ℝ) < meshAt L k j ^ 4 := fun j =>
    pow_pos (zpow_pos (Nat.cast_pos.2 hL) _) 4
  obtain ⟨ρ₁, hD, hA, hQ⟩ := hThree L hL hS k hk
  obtain ⟨ρ₂, hYm⟩ := hY L hL hS k hk
  obtain ⟨ρ₃, hρ₃, hsmall⟩ := (hSmall L hL hS k hk).2
  have shrink : ∀ {I I' : PeriodicData}, IsPeriodic I → IsPeriodic I' →
      ∀ {T : ((fieldPeriodicData L k hL).Carrier → ℂ) → I'.Carrier → I.Carrier → ℂ} {ρ R ρ'' R'' : ℝ},
        IsLocalWith (fieldPeriodicData L k hL) I I' T ρ R → 0 < ρ'' → ρ'' ≤ ρ → R ≤ R'' →
          IsLocalWith (fieldPeriodicData L k hL) I I' T ρ'' R'' :=
    fun hI hI' _ _ _ _ _ h h₁ h₂ h₃ =>
      (hNumbers _ _ _ hF hI hI' _ _ _ _ _ h h).1.1 _ _ h₁ h₂ h₃
  have : Nonempty (colourEdges L k 0).Carrier :=
    ⟨((0 : Fin 3), Classical.arbitrary (PeriodicOperators.PosEdge L k 0))⟩
  have : Nonempty (colourVertices L k 0).Carrier :=
    ⟨((0 : Fin 3), (Classical.arbitrary (PeriodicOperators.PosEdge L k 0)).1.initial)⟩
  refine ⟨?_, ?_⟩
  · have hYl : IsLocalOpFun (fieldPeriodicData L k hL) (colourEdges L k 0)
        (colourEdges L k 0) (rawHessianFn L k hL) := ⟨ρ₂, 19, hYm⟩
    have hYt := isLocalOpFun_swapKernel hMult hTr hF hB0 hB0 (hpos 0) (hpos 0) (fun _ => rfl)
      (fun _ => rfl) hYl
    obtain ⟨a, b, hXm⟩ := isLocalOpFun_smul hMult hF hB0 hB0
      (hSum _ _ _ hF hB0 hB0 _ _ hYl hYt) (1 / 2 : ℂ)
    obtain ⟨c, d, hQt⟩ := isLocalOpFun_swapKernel hMult hTr hF hB0 hBk (hpos 0) (hpos k) (fun _ => rfl)
      (fun _ => rfl) (⟨ρ₁, 19, hQ⟩ : IsLocalOpFun (fieldPeriodicData L k hL)
        (colourEdges L k 0) (colourEdges L k k) (covariantAverageFn L k hL))
    have hρ : 0 < min (min a c) (min ρ₁ ρ₃) :=
      lt_min (lt_min hXm.radius_pos hQt.radius_pos) (lt_min hQ.radius_pos hρ₃)
    refine ⟨min (min a c) (min ρ₁ ρ₃), max (max b d) 19, isLocalWith_congr
      (isLocalWith_saddleMatrix
        (shrink hB0 hB0 hXm hρ ((min_le_left _ _).trans (min_le_left _ _))
          ((le_max_left _ _).trans (le_max_left _ _)))
        (shrink hBk hB0 hQt hρ ((min_le_left _ _).trans (min_le_right _ _))
          ((le_max_right _ _).trans (le_max_left _ _)))
        (shrink hB0 hBk hQ hρ ((min_le_right _ _).trans (min_le_left _ _)) (le_max_right _ _)))
      fun f hf => ?_⟩
    have hU := hsmall f (isSupBelow_of_le hf ((min_le_right _ _).trans (min_le_right _ _)))
    obtain ⟨ζ, rfl⟩ := (hValues L hL k).2.1 f
    obtain ⟨-, hJ, hμ, -⟩ := (hValues L hL k).1 ζ
    have hform := ((hFormed L hS k hk _ hU).1 (sourceOfCoeffs hL (ζ.pauliCoeffs hL))
      (hJ ▸ ζ.2.1.2) (coarseOfCoeffs hL (ζ.pauliCoeffs hL)) (hμ ▸ ζ.2.2.2)).2.2.2.2
    change saddleMatrix
      (hessianKernel (FieldValueFunctions.gaugeFieldOfCoeffs hL (ζ.pauliCoeffs hL)) _ _) _ _ = _
    rw [hform]
    rfl
  · have hDl : IsLocalOpFun (fieldPeriodicData L k hL) (colourVertices L k 0)
        (colourEdges L k 0) (covDiffFn L k hL) := ⟨ρ₁, 19, hD⟩
    have hDt := isLocalOpFun_swapKernel hMult hTr hF hS0 hB0 (hpos 0) (hpos 0) (fun _ => rfl)
      (fun _ => rfl) hDl
    obtain ⟨a, b, hLap⟩ := hProduct _ _ _ _ hF hB0 hS0 hS0 _ _ hDt hDl
    obtain ⟨c, d, hAt⟩ := isLocalOpFun_swapKernel hMult hTr hF hS0 hSk (hpos 0) (hpos k) (fun _ => rfl)
      (fun _ => rfl) (⟨ρ₁, 19, hA⟩ : IsLocalOpFun (fieldPeriodicData L k hL)
        (colourVertices L k 0) (colourVertices L k k) (averageKernelFn L k hL))
    have hρ : 0 < min (min a c) ρ₁ :=
      lt_min (lt_min hLap.radius_pos hAt.radius_pos) hA.radius_pos
    exact ⟨min (min a c) ρ₁, max (max b d) 19, isLocalWith_congr
      (isLocalWith_saddleMatrix
        (shrink hS0 hS0 hLap hρ ((min_le_left _ _).trans (min_le_left _ _))
          ((le_max_left _ _).trans (le_max_left _ _)))
        (shrink hSk hS0 hAt hρ ((min_le_left _ _).trans (min_le_right _ _))
          ((le_max_right _ _).trans (le_max_left _ _)))
        (shrink hS0 hSk hA hρ (min_le_right _ _) (le_max_right _ _)))
      fun f _ => rfl⟩
end YangMills.Construction.Tower.FullSpace.OperatorLocality
end
