import YangMills.Construction.ConfigSpace.FlatSchwartzDensity
import YangMills.Construction.Continuum.ConstantOfTheExtensionIsOfFactorialType
import YangMills.Construction.Continuum.ExtensionOfAFormToTheFlatFunctions
import YangMills.Construction.Continuum.FiniteSeminormsOfRapidlyDecreasingFunctions
import YangMills.Construction.Continuum.FirstFactsOnSmoothTestFunctionsAndTuples
import YangMills.Construction.Continuum.LocalFunctionalsLinearBoundedAndValueOnTensors
import YangMills.Construction.Continuum.PiecesOfATensorAddUpToTheForm
import YangMills.Construction.Continuum.SumOfTheLocalFunctionalsOverThePieces
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FlatExtension
open ExtensionConstants ConfigSpace PieceProducts ShellPieces SmoothMaps
variable {n : ℕ}
def pieceValue (T : smoothRealTupleSet n → ℝ) (φ : Config n → ℂ) (p : activeIndices n) : ℂ :=
  localPairing T (pieceBoxSystem p) (pieceMul p.1.1 p.1.2 φ)
def sumOverActivePieces (T : smoothRealTupleSet n → ℝ) (φ : flatSchwartzSet n) : ℂ :=
  ∑' p, pieceValue T φ.1 p
theorem pieceMul_add (j : ℕ) (z : LatticePt n) (φ ψ : Config n → ℂ) :
    pieceMul j z (φ + ψ) = pieceMul j z φ + pieceMul j z ψ := by
  funext x
  simp [pieceMul, mul_add]
theorem pieceMul_smul (j : ℕ) (z : LatticePt n) (lam : ℂ) (φ : Config n → ℂ) :
    pieceMul j z (lam • φ) = lam • pieceMul j z φ := by
  funext x
  simp only [pieceMul, Pi.smul_apply, smul_eq_mul]
  ring
theorem flatExtensionClaim_holds
    (hSum : PieceLocalSum.PieceLocalSumBound)
    (hAgree : PieceTensorSum.SumOverPiecesEqForm)
    (hDensity : TensorSpanDenseInFlatSchwartz)
    (hFacts : TupleFacts.BasicFacts)
    (hNorm : SchwartzSeminormsFinite)
    (hFlat : ProductBounds)
    (hLocal : LocalPairingProps.LocalPairingProperties)
    (hFactorial : FactorialTypeBounds) :
    FlatExtensionClaim := by
  intro n c a G T hn hc hG hT
  have hsys : ∀ p : activeIndices n, (pieceBoxSystem p).IsSeparated ∧
      ∀ φ ∈ smoothSet (Config n), pieceMul p.1.1 p.1.2 φ ∈ (pieceBoxSystem p).supportedClass := by
    intro p
    have h := (hFlat n hn p.1.1 p.1.2 p.2).1
    exact ⟨h.1, fun φ hφ => (h.2.2.2.2.2 φ hφ).2.2⟩
  have hlin : ∀ p : activeIndices n, LocalPairingProps.PairingIsComplexLinear
      T (pieceBoxSystem p) := fun p =>
    (hLocal n c a G T (pieceBoxSystem p) hT (hsys p).1).2.1
  have hsmooth : ∀ φ : flatSchwartzSet n, φ.1 ∈ smoothSet (Config n) := fun φ => φ.2.1.1
  have hfin : ∀ φ : flatSchwartzSet n,
      decaySeminorm (4 * n + 2) (10 * n + a - 2) φ.1 < ⊤ := fun φ =>
    ((hNorm n (by omega) (4 * n + 2) (10 * n + a - 2) 0).1 φ.1 φ.2.1).1
  have hsumm : ∀ φ : flatSchwartzSet n, Summable fun p => ‖pieceValue T φ.1 p‖ := by
    intro φ
    have hne : ∑' p : activeIndices n, ENNReal.ofReal ‖pieceValue T φ.1 p‖ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin φ).ne)
        (hSum n c a G T hT φ.1 φ.2)
    have h := ENNReal.summable_toReal hne
    simpa [ENNReal.toReal_ofReal, norm_nonneg] using h
  have hsummable : ∀ φ : flatSchwartzSet n, Summable (pieceValue T φ.1) := fun φ =>
    (hsumm φ).of_norm
  have hbound : ExtensionBound c a G (sumOverActivePieces T) := by
    intro φ
    calc ENNReal.ofReal ‖sumOverActivePieces T φ‖
        ≤ ENNReal.ofReal (∑' p, ‖pieceValue T φ.1 p‖) :=
          ENNReal.ofReal_le_ofReal (norm_tsum_le_tsum_norm (hsumm φ))
      _ = ∑' p, ENNReal.ofReal ‖pieceValue T φ.1 p‖ :=
          ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsumm φ)
      _ ≤ _ := hSum n c a G T hT φ.1 φ.2
  have hlinear : IsLinearOnFlat (sumOverActivePieces T) := by
    constructor
    · intro φ ψ χ hχ
      have hterm : ∀ p, pieceValue T χ.1 p = pieceValue T φ.1 p + pieceValue T ψ.1 p := by
        intro p
        simp only [pieceValue, hχ, pieceMul_add]
        exact (hlin p).1 _ ((hsys p).2 _ (hsmooth φ)) _ ((hsys p).2 _ (hsmooth ψ))
      simp only [sumOverActivePieces, hterm]
      exact (hsummable φ).tsum_add (hsummable ψ)
    · intro lam φ χ hχ
      have hterm : ∀ p, pieceValue T χ.1 p = lam * pieceValue T φ.1 p := by
        intro p
        simp only [pieceValue, hχ, pieceMul_smul]
        exact (hlin p).2 lam _ ((hsys p).2 _ (hsmooth φ))
      simp only [sumOverActivePieces, hterm]
      exact tsum_mul_left
  have hdual : sumOverActivePieces T ∈ flatDualSet n := by
    refine ⟨hlinear, 4 * n + 2, 10 * n + a - 2,
      |extConst n a * max 1 c ^ n * G|, abs_nonneg _, fun φ => ?_⟩
    exact (hbound φ).trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal (le_abs_self _)) _)
  obtain ⟨-, ⟨-, hten, W, hW, hWflat⟩, -⟩ := hFacts n hn
  have htensor : ∀ f : smoothRealTupleSet n, tensorProd f.1 ∈ flatSchwartzSet n := by
    intro f
    apply hWflat
    rw [hW]
    exact (hten f.1 f.2).1
  have hext : IsFlatExtension T (sumOverActivePieces T) :=
    ⟨hdual, fun f => ⟨⟨tensorProd f.1, htensor f⟩, rfl, hAgree n c a G T hT f⟩⟩
  have hunique : ∀ S, IsFlatExtension T S → S = sumOverActivePieces T := by
    intro S hS
    refine (hDensity n hn).2.2 S hS.1 _ hdual ?_
    rintro φ ⟨f, hf, hφ⟩
    obtain ⟨χ, hχ, hval⟩ := hS.2 ⟨f, hf⟩
    obtain ⟨χ', hχ', hval'⟩ := hext.2 ⟨f, hf⟩
    have e₁ : χ = φ := Subtype.ext (hχ.trans hφ.symm)
    have e₂ : χ' = φ := Subtype.ext (hχ'.trans hφ.symm)
    rw [← e₁, hval, ← hval', e₂, e₁]
  refine ⟨⟨sumOverActivePieces T, hext, hunique⟩, fun S hS => ?_, hFactorial.2.2.2.1 n a hn⟩
  rw [hunique S hS]
  exact hbound
end YangMills.Construction.FlatExtension
