import YangMills.Construction.PeriodicOperators.BlockMatricesOfLocalOperatorFunctionsAreLocal
import YangMills.Construction.PeriodicOperators.CalculusOfSymbolsProof
import YangMills.Construction.PeriodicOperators.KernelsOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.NumbersOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.SymbolOnClassesAndPlaneWaves
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.BlockLocality
open OpFunKernels (IsComponentKernel)
theorem linearMapEntry_linearMapOfEntries {C C' : Type} [Finite C] (K : C' → C → ℂ) :
    linearMapEntry (linearMapOfEntries K) = K := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolCalculus.linearMapEntry_linearMapOfEntries <;> assumption
section Blocks
variable {J : Fin 2 → PeriodicData}
theorem symbolHom_blockKernel (H : SymbolOnQuotients.Claim)
    (hJ : ∀ b, IsPeriodic (J b)) {Z : ∀ i j, (J i).Carrier → (J j).Carrier → ℂ}
    (hZ : ∀ i j, IsFiniteRangeAllRates (J j) (J i) (Z i j))
    (hB : IsFiniteRangeAllRates (PeriodicData.sigma J) (PeriodicData.sigma J)
      (blockKernel J Z)) (κ : Fin 4 → ℂ) :
    symbolHom (PeriodicData.sigma J) (PeriodicData.sigma J) (blockKernel J Z) κ =
      blockQuotHom J fun i j => symbolHom (J j) (J i) (Z i j) κ := by
  have hU : IsPeriodic (PeriodicData.sigma J) := IsPeriodic.sigma hJ
  have e : descendMatrix (PeriodicData.sigma J) (PeriodicData.sigma J) 1
        (fourierSymbol (PeriodicData.sigma J) (PeriodicData.sigma J) (blockKernel J Z) κ) =
      fun c' c => blockQuotKernel J
        (fun i j => linearMapEntry (symbolHom (J j) (J i) (Z i j) κ))
        (sigmaQuotPlace J c') (sigmaQuotPlace J c) := by
    funext c' c
    obtain ⟨⟨i, a⟩, rfl⟩ : ∃ x', (PeriodicData.sigma J).mkQuot 1 x' = c' := Quot.exists_rep c'
    obtain ⟨⟨j, b⟩, rfl⟩ : ∃ x, (PeriodicData.sigma J).mkQuot 1 x = c := Quot.exists_rep c
    have := (hJ j).finite_quot
    have hBig := (H _ _ hU hU _ hB.periodic).quotSymbol_mkQuot κ
      (hB.summable κ (mem_univ κ)) ⟨i, a⟩ ⟨j, b⟩
    have hSmall := (H _ _ (hJ j) (hJ i) _ (hZ i j).periodic).quotSymbol_mkQuot κ
      ((hZ i j).summable κ (mem_univ κ)) a b
    simp only [quotSymbol] at hBig hSmall
    rw [hBig]
    show _ = linearMapEntry (symbolHom (J j) (J i) (Z i j) κ) ((J i).mkQuot 1 a) ((J j).mkQuot 1 b)
    rw [symbolHom, linearMapEntry_linearMapOfEntries, hSmall]
    rfl
  exact congrArg linearMapOfEntries e
theorem componentKernel_block (H : SymbolOnQuotients.Claim)
    (hJ : ∀ b, IsPeriodic (J b)) {q : Fin 4 → ℂ}
    {Y : ∀ i j, (J i).Carrier → (J j).Carrier → ℂ}
    {A : ∀ i j, (Fin 4 → ℂ) → QuotHom (J j) (J i)}
    {B : (Fin 4 → ℂ) → QuotHom (PeriodicData.sigma J) (PeriodicData.sigma J)}
    (hY : ∀ i j, IsComponentKernel (J j) (J i) q (Y i j) (A i j))
    (hB : IsComponentKernel (PeriodicData.sigma J) (PeriodicData.sigma J) q (blockKernel J Y) B)
    (κ : Fin 4 → ℂ) :
    B κ = blockQuotHom J fun i j => A i j κ := by
  have e : dephasedKernel (PeriodicData.sigma J) (PeriodicData.sigma J) q (blockKernel J Y) =
      blockKernel J fun i j => dephasedKernel (J j) (J i) q (Y i j) := rfl
  have hB' := hB.2.1
  rw [e] at hB'
  rw [hB.2.2, e, symbolHom_blockKernel H hJ (fun i j => (hY i j).2.1) hB' κ]
  exact congrArg (blockQuotHom J) (funext fun i => funext fun j => (congrFun (hY i j).2.2 κ).symm)
variable {F : PeriodicData} {T : ∀ i j, (F.Carrier → ℂ) → (J i).Carrier → (J j).Carrier → ℂ}
theorem isLocalWith_blockKernelFun {ρ R : ℝ} (hm : ∀ i j, IsLocalWith F (J j) (J i) (T i j) ρ R) :
    IsLocalWith F (PeriodicData.sigma J) (PeriodicData.sigma J) (blockKernelFun J T) ρ R where
  radius_pos := (hm 0 0).radius_pos
  vanish_far := fun ζ hζ x' x hr => (hm x'.1 x.1).vanish_far ζ hζ x'.2 x.2 hr
  holo_entry := fun x' x => (hm x'.1 x.1).holo_entry x'.2 x.2
  shift_covariant := fun ζ hζ k x' x => (hm x'.1 x.1).shift_covariant ζ hζ k x'.2 x.2
theorem exists_common_parameters (hN : ParameterIndependence.Claim)
    (hF : IsPeriodic F) (hJ : ∀ b, IsPeriodic (J b))
    (hT : ∀ i j, IsLocalOpFun F (J j) (J i) (T i j)) :
    ∃ ρ R : ℝ, ∀ i j, IsLocalWith F (J j) (J i) (T i j) ρ R := by
  choose ρ R hm using hT
  have hρ : ∀ i j, min (min (ρ 0 0) (ρ 0 1)) (min (ρ 1 0) (ρ 1 1)) ≤ ρ i j :=
    Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2
        ⟨(min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _)⟩,
      Fin.forall_fin_two.2
        ⟨(min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩⟩
  have hR : ∀ i j, R i j ≤ max (max (R 0 0) (R 0 1)) (max (R 1 0) (R 1 1)) :=
    Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2
        ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _)⟩,
      Fin.forall_fin_two.2
        ⟨(le_max_left _ _).trans (le_max_right _ _), (le_max_right _ _).trans (le_max_right _ _)⟩⟩
  have hpos : 0 < min (min (ρ 0 0) (ρ 0 1)) (min (ρ 1 0) (ρ 1 1)) :=
    lt_min (lt_min (hm 0 0).radius_pos (hm 0 1).radius_pos)
      (lt_min (hm 1 0).radius_pos (hm 1 1).radius_pos)
  exact ⟨_, _, fun i j =>
    (hN F (J j) (J i) hF (hJ j) (hJ i) (T i j) _ _ _ _ (hm i j) (hm i j)).1.1 _ _ hpos (hρ i j)
      (hR i j)⟩
theorem coeffOne_blockKernelFun (hN : ParameterIndependence.Claim)
    (hF : IsPeriodic F) (hJ : ∀ b, IsPeriodic (J b)) {ρ R : ℝ}
    (hm : ∀ i j, IsLocalWith F (J j) (J i) (T i j) ρ R) (ζ : F.Carrier → ℂ) :
    coeffOne F (PeriodicData.sigma J) (PeriodicData.sigma J) (blockKernelFun J T) ζ =
      blockKernel J fun i j => coeffOne F (J j) (J i) (T i j) ζ := by
  have hU : IsPeriodic (PeriodicData.sigma J) := IsPeriodic.sigma hJ
  have mb := isLocalWith_blockKernelFun hm
  funext x' x
  obtain ⟨i, a⟩ := x'
  obtain ⟨j, b⟩ := x
  have hT := (hN F (J j) (J i) hF (hJ j) (hJ i) (T i j) ρ R ρ R (hm i j) (hm i j)).2.1.1 ζ ζ a b
  have hB := (hN F _ _ hF hU hU (blockKernelFun J T) ρ R ρ R mb mb).2.1.1 ζ ζ ⟨i, a⟩ ⟨j, b⟩
  obtain ⟨-, l, e, φ, β, hx, ht⟩ := (hT.1.1 _).2 rfl
  exact ((hB.1.1 _).1 ⟨mb, l, e, φ, β, hx, ht⟩).symm
theorem coeffTwo_blockKernelFun (hN : ParameterIndependence.Claim)
    (hF : IsPeriodic F) (hJ : ∀ b, IsPeriodic (J b)) {ρ R : ℝ}
    (hm : ∀ i j, IsLocalWith F (J j) (J i) (T i j) ρ R) (ζ ζ' : F.Carrier → ℂ) :
    coeffTwo F (PeriodicData.sigma J) (PeriodicData.sigma J) (blockKernelFun J T) ζ ζ' =
      blockKernel J fun i j => coeffTwo F (J j) (J i) (T i j) ζ ζ' := by
  have hU : IsPeriodic (PeriodicData.sigma J) := IsPeriodic.sigma hJ
  have mb := isLocalWith_blockKernelFun hm
  funext x' x
  obtain ⟨i, a⟩ := x'
  obtain ⟨j, b⟩ := x
  have hT := (hN F (J j) (J i) hF (hJ j) (hJ i) (T i j) ρ R ρ R (hm i j) (hm i j)).2.1.1 ζ ζ' a b
  have hB := (hN F _ _ hF hU hU (blockKernelFun J T) ρ R ρ R mb mb).2.1.1 ζ ζ' ⟨i, a⟩ ⟨j, b⟩
  obtain ⟨-, l, e, φ, β, hx, ht⟩ := (hT.2.1 _).2 rfl
  exact ((hB.2.1 _).1 ⟨mb, l, e, φ, β, hx, ht⟩).symm
end Blocks
theorem claim_holds (hN : ParameterIndependence.Claim)
    (hK : OpFunKernels.Claim)
    (hS : SymbolOnQuotients.Claim) : Claim := by
  intro F hF δ p _ _ εPlus εMinus J hJ T hT
  have hU : IsPeriodic (PeriodicData.sigma J) := IsPeriodic.sigma hJ
  obtain ⟨ρ, R, hm⟩ := exists_common_parameters hN hF hJ hT
  have hL : IsLocalOpFun F (PeriodicData.sigma J) (PeriodicData.sigma J)
      (blockKernelFun J T) := ⟨ρ, R, isLocalWith_blockKernelFun hm⟩
  refine ⟨hL, ?_⟩
  obtain ⟨h0, h1⟩ := hK F _ _ hF hU hU _ hL
  obtain ⟨-, c10, c01, c11⟩ := h1 p εPlus εMinus
  have hi := fun i j => hK F (J j) (J i) hF (hJ j) (hJ i) (T i j) (hT i j)
  rw [coeffOne_blockKernelFun hN hF hJ hm] at c10 c01
  rw [coeffTwo_blockKernelFun hN hF hJ hm] at c11
  refine ⟨fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_, fun κ _ => ?_⟩
  · exact symbolHom_blockKernel hS hJ (fun i j => (hi i j).1) h0 κ
  · exact componentKernel_block hS hJ (fun i j => ((hi i j).2 p εPlus εMinus).2.1) c10 κ
  · exact componentKernel_block hS hJ (fun i j => ((hi i j).2 p εPlus εMinus).2.2.1) c01 κ
  · exact componentKernel_block hS hJ (fun i j => ((hi i j).2 p εPlus εMinus).2.2.2) c11 κ
end YangMills.Construction.PeriodicOperators.BlockLocality
end
