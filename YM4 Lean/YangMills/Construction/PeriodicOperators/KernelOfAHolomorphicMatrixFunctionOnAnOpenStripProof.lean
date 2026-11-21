import YangMills.Construction.PeriodicOperators.CalculusOfSymbols
import YangMills.Construction.PeriodicOperators.EntriesDeterminantsAndHolomorphicFunctions
import YangMills.Construction.PeriodicOperators.KernelOfAHolomorphicMatrixFunctionOnAnOpenStrip
import YangMills.Construction.PeriodicOperators.SymbolOnClassesAndPlaneWaves
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.OpenStripHolomorphicKernel
theorem imStrip_subset_openImStrip {a b : ℝ} (hab : a < b) :
    imStrip a ⊆ openImStrip b :=
  fun _ hz μ => lt_of_le_of_lt (hz μ) hab
theorem exists_lt_mem_openImStrip {b : ℝ} (hb : 0 < b) {z : Fin 4 → ℂ}
    (hz : z ∈ openImStrip b) :
    ∃ a : ℝ, 0 < a ∧ a < b ∧ z ∈ openImStrip a := by
  obtain ⟨ν, hν⟩ := Finite.exists_max fun μ => |(z μ).im|
  have hlt : |(z ν).im| < b := hz ν
  have hnn : 0 ≤ |(z ν).im| := abs_nonneg _
  refine ⟨(|(z ν).im| + b) / 2, by linarith, by linarith, fun μ => ?_⟩
  have := hν μ
  linarith
theorem quotHom_ext_of_carrierEntry {P Q : PeriodicData}
    (hApply : ∀ (L : QuotHom P Q) (f : P.UnitQuot → ℂ) (y : Q.UnitQuot),
      L f y = ∑ᶠ x, linearMapEntry L y x * f x)
    {A B : QuotHom P Q} (h : ∀ j i, carrierEntry A j i = carrierEntry B j i) : A = B := by
  have hent : ∀ (y : Q.UnitQuot) (x : P.UnitQuot), linearMapEntry A y x = linearMapEntry B y x := by
    intro y x
    induction y using Quot.ind with | mk j => ?_
    induction x using Quot.ind with | mk i => ?_
    exact h j i
  refine LinearMap.ext fun f => funext fun y => ?_
  rw [hApply A f y, hApply B f y]
  simp only [hent]
theorem claim_of (hCalc : SymbolCalculus.Claim)
    (hEnt : EntriesDets.Claim)
    (hQuot : SymbolOnQuotients.Claim) : Claim := by
  intro P Q hP hQ b hb M hHol hBdd hQuasi
  have hOpen : IsOpen (openImStrip b) := hHol.2.1
  have hCont : QuotHomFamilyContinuousOn (n := 4) (openImStrip b) M :=
    (hEnt.2.2.2.2.2.2.1 4 (openImStrip b) (by norm_num) hOpen).2.1 P Q hP hQ M hHol
  have hReal : realDualPoints ⊆ openImStrip b := by
    intro z hz μ
    rw [show (z μ).im = 0 from hz μ, abs_zero]
    exact hb
  have hKer : ∀ a : ℝ, 0 < a → a < b → SymbolCalculus.MatFunKernelProperties P Q a M := by
    intro a ha hab
    refine (hCalc P Q hP hQ).2.2.2.2.2.2.1 a ha |>.2.1 M ⟨?_, hBdd a ha hab, ?_⟩
    · exact ⟨openImStrip b, hOpen, imStrip_subset_openImStrip hab,
        fun y x => hHol.2.2 (y, x)⟩
    · exact fun e z hz => hQuasi e z (imStrip_subset_openImStrip hab hz)
  have hPt : ∀ z ∈ openImStrip b,
      SymbolSummableAt P Q (matFunKernel P Q M) z ∧
        ∀ j i, fourierSymbol P Q (matFunKernel P Q M) z j i =
          carrierEntry (M z) j i := by
    intro z hz
    obtain ⟨a, ha, hab, hza⟩ := exists_lt_mem_openImStrip hb hz
    exact (hKer a ha hab).summable_openImStrip z hza
  have hPer : IsPeriodicKernel P Q (matFunKernel P Q M) :=
    (hKer (b / 2) (by linarith) (by linarith)).isPeriodicKernel.1
  have hEq : ∀ z ∈ openImStrip b,
      symbolHom P Q (matFunKernel P Q M) z = M z := by
    intro z hz
    refine quotHom_ext_of_carrierEntry (hEnt.1 P Q P hP hQ hP).1 fun j i => ?_
    rw [← (hPt z hz).2 j i,
      ← (hQuot P Q hP hQ _ hPer).quotSymbol_mkQuot z (hPt z hz).1 j i]
    exact ((hEnt.2.1 P Q hP hQ).1 _).2 _ _
  exact ⟨hReal, hCont, ⟨hCont.1, fun e => (hCont.2 e).mono hReal⟩, hPer,
    fun z hz => (hPt z hz).1, hEq⟩
end YangMills.Construction.PeriodicOperators.OpenStripHolomorphicKernel
end
