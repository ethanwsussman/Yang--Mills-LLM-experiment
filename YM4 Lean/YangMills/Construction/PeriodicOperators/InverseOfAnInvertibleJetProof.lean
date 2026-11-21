import YangMills.Construction.PeriodicOperators.AlgebraOfQuadruples
import YangMills.Construction.PeriodicOperators.ArgumentsInProductsOfJetsAndEqualJets
import YangMills.Construction.PeriodicOperators.AssociativityAndNormOfProductsOfJets
import YangMills.Construction.PeriodicOperators.InverseOfAnInvertibleJet
import YangMills.Construction.PeriodicOperators.LocalOperatorFunctionsAndTheirJets
import YangMills.Construction.PeriodicOperators.NormsAndTracesOfMatricesOnTheClasses
import YangMills.Construction.PeriodicOperators.VanishingProductsOfThreeJets
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetInverse
open JetQuad
variable {I I' : PeriodicData} {δ : ℝ} {p : Fin 4 → ℂ}
theorem refl_eqAsJet (T : JetQuad I I') : EqAsJet δ p T T :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
theorem symm_eqAsJet {T S : JetQuad I I'} (h : EqAsJet δ p T S) : EqAsJet δ p S T :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
theorem trans_eqAsJet {T S R : JetQuad I I'} (h : EqAsJet δ p T S) (h' : EqAsJet δ p S R) :
    EqAsJet δ p T R :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.trans h'.2.2.2⟩
theorem add_eqAsJet_of_eqAsJet_zero (Y X : JetQuad I I') (h : EqAsJet δ p X (zeroJet I I')) :
    EqAsJet δ p (add Y X) Y := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨fun κ hκ => ?_, fun κ hκ => ?_, fun κ hκ => ?_, fun κ hκ => ?_⟩
  · change Y.f00 κ + X.f00 κ = Y.f00 κ
    rw [h0 hκ]
    exact add_zero _
  · change Y.f10 κ + X.f10 κ = Y.f10 κ
    rw [h1 hκ]
    exact add_zero _
  · change Y.f01 κ + X.f01 κ = Y.f01 κ
    rw [h2 hκ]
    exact add_zero _
  · change Y.f11 κ + X.f11 κ = Y.f11 κ
    rw [h3 hκ]
    exact add_zero _
theorem one_add_normalize (p : Fin 4 → ℂ) (T : JetQuad I I) :
    add (one I) (normalize p T) = mul p (zeroPartInv T) T := by
  apply JetQuad.ext <;> funext κ <;>
    simp only [add, smul, JetQuad.normalize, Pi.add_apply, Pi.smul_apply] <;> module
theorem geomSum_mul_one_add (N : JetQuad I I)
    (h : QuadAlgebra.MulBilinearUnital p I I I) :
    mul p (add (add (one I) (smul (-1) N)) (mul p N N)) (add (one I) N) =
      add (one I) (mul p (mul p N N) N) := by
  obtain ⟨hl, hr, hsl, -, hu⟩ := h
  have hu1 : ∀ X : JetQuad I I, mul p (one I) X = X := fun X => (hu X).1
  have hu2 : ∀ X : JetQuad I I, mul p X (one I) = X := fun X => (hu X).2
  simp only [hl, hr, hsl, hu1, hu2]
  apply JetQuad.ext <;> funext κ <;>
    simp only [add, smul, Pi.add_apply, Pi.smul_apply] <;> module
theorem one_add_mul_geomSum (N : JetQuad I I)
    (h : QuadAlgebra.MulBilinearUnital p I I I) :
    mul p (add (one I) N) (add (add (one I) (smul (-1) N)) (mul p N N)) =
      add (one I) (mul p N (mul p N N)) := by
  obtain ⟨hl, hr, -, hsr, hu⟩ := h
  have hu1 : ∀ X : JetQuad I I, mul p (one I) X = X := fun X => (hu X).1
  have hu2 : ∀ X : JetQuad I I, mul p X (one I) = X := fun X => (hu X).2
  simp only [hl, hr, hsr, hu1, hu2]
  apply JetQuad.ext <;> funext κ <;>
    simp only [add, smul, Pi.add_apply, Pi.smul_apply] <;> module
theorem claim_holds (hProduct : JetProductsAssocAndNormLe)
    (hThree : TripleJets.VanishOnStrip)
    (hAlgebra : QuadAlgebra.Claim)
    (hNorms : QuotMatrixNorms.Claim)
    (hLocal : JetDomains.OpFunJetTheory)
    (hEqual : JetArgumentsAndEqualJets) :
    JetInverse.Claim := by
  intro δ p hδ hp I hI T hT
  have F := hLocal.2.2 I I I hI hI hI δ p hδ hp
  have hProd : JetCalculus.MulAssocNormLe δ p := hProduct δ p hδ hp
  have hTj : IsJet δ p T := hT.isJet
  obtain ⟨hT0, hA⟩ := F.zeroPart_isJet T hT
  obtain ⟨-, hN, hNN, -⟩ := F.invertible_derived_isJet T hT
  have hOne : IsJet δ p (one I) := F.one_isJet
  have hBil := hAlgebra.1 p I I I
  obtain ⟨hAddN, hSmulN, hOneN, -, -⟩ := hAlgebra.2 δ p hδ hp I I hI hI
  have hZero : quotHomNorm (0 : QuotHom I I) = 0 := (hNorms I I I hI hI hI).1.2.2.2.1
  have assoc : ∀ X Y Z : JetQuad I I, IsJet δ p X → IsJet δ p Y → IsJet δ p Z →
      EqAsJet δ p (mul p (mul p X Y) Z) (mul p X (mul p Y Z)) :=
    fun X Y Z hX hY hZ => (hProd I I I I hI hI hI hI X Y Z hX hY hZ).1
  have hNormMul : ∀ X Y : JetQuad I I, IsJet δ p X → IsJet δ p Y →
      jetNorm δ p (mul p X Y) ≤ jetNorm δ p X * jetNorm δ p Y :=
    fun X Y hX hY => (hProd I I I I hI hI hI hI X Y X hX hY hX).2
  have cong : ∀ X X' Y Y' : JetQuad I I, IsJet δ p X → IsJet δ p X' → IsJet δ p Y →
      IsJet δ p Y' → EqAsJet δ p X X' → EqAsJet δ p Y Y' → EqAsJet δ p (mul p X Y) (mul p X' Y') :=
    fun X X' Y Y' hX hX' hY hY' hXX hYY =>
      (hEqual.2.1 δ p I I hI hI X X' hX hX' hXX).2.2.2.2 I hI Y Y' hY hY' hYY
  have hInvConst := F.zeroPart_inv T hT
  set A := zeroPartInv T with hAdef
  set N := normalize p T with hNdef
  set Q := add (add (one I) (smul (-1) N)) (mul p N N) with hQdef
  have hP : IsJet δ p (add (one I) N) := F.add_isJet _ _ hOne hN
  have hNeg : IsJet δ p (smul (-1) N) := F.smul_isJet _ _ hN
  have hOneNeg : IsJet δ p (add (one I) (smul (-1) N)) := F.add_isJet _ _ hOne hNeg
  have hQ : IsJet δ p Q := F.add_isJet _ _ hOneNeg hNN
  have hInvJet : IsJet δ p (mul p Q A) := F.mul_isJet _ _ hQ hA
  have hN00 : EqOn N.f00 0 (imStrip (2 * δ)) := by
    intro κ hκ
    have h1 : (quotHomInverse (T.f00 κ)).comp (T.f00 κ) = LinearMap.id :=
      Ring.inverse_mul_cancel _ (hT.isUnit_f00 κ hκ)
    change (quotHomInverse (T.f00 κ)).comp (T.f00 κ) + (-1 : ℂ) • (LinearMap.id : QuotHom I I) = 0
    rw [h1]
    module
  have hNNN : EqAsJet δ p (mul p (mul p N N) N) (zeroJet I I) :=
    hThree δ p hδ hp I I I I hI hI hI hI N N N hN hN hN hN00 hN00 hN00
  have hNNN' : EqAsJet δ p (mul p N (mul p N N)) (zeroJet I I) :=
    trans_eqAsJet (symm_eqAsJet (assoc N N N hN hN hN)) hNNN
  have hQP : EqAsJet δ p (mul p Q (add (one I) N)) (one I) := by
    rw [hQdef, geomSum_mul_one_add N hBil]
    exact add_eqAsJet_of_eqAsJet_zero _ _ hNNN
  have hPQ : EqAsJet δ p (mul p (add (one I) N) Q) (one I) := by
    rw [hQdef, one_add_mul_geomSum N hBil]
    exact add_eqAsJet_of_eqAsJet_zero _ _ hNNN'
  have hAT : add (one I) N = mul p A T := one_add_normalize p T
  have hLeft : EqAsJet δ p (mul p (mul p Q A) T) (one I) := by
    refine trans_eqAsJet (assoc Q A T hQ hA hTj) ?_
    rw [← hAT]
    exact hQP
  have hTeq : EqAsJet δ p (mul p (zeroPart T) (add (one I) N)) T := by
    rw [hAT]
    refine trans_eqAsJet (symm_eqAsJet (assoc _ _ _ hT0 hA hTj)) ?_
    have h1 := cong _ _ T T (F.mul_isJet _ _ hT0 hA) hOne hTj hTj hInvConst.2 (refl_eqAsJet T)
    rw [(hBil.2.2.2.2 T).1] at h1
    exact h1
  have hT0P : IsJet δ p (mul p (zeroPart T) (add (one I) N)) := F.mul_isJet _ _ hT0 hP
  have hRight : EqAsJet δ p (mul p T (mul p Q A)) (one I) := by
    have h1 := cong T _ (mul p Q A) (mul p Q A) hTj hT0P hInvJet hInvJet (symm_eqAsJet hTeq)
      (refl_eqAsJet _)
    have h2 := assoc _ _ (mul p Q A) hT0 hP hInvJet
    have h3 : EqAsJet δ p (mul p (add (one I) N) (mul p Q A)) A := by
      have h := symm_eqAsJet (assoc _ Q A hP hQ hA)
      have h' := cong _ (one I) A A (F.mul_isJet _ _ hP hQ) hOne hA hA hPQ (refl_eqAsJet A)
      rw [(hBil.2.2.2.2 A).1] at h'
      exact trans_eqAsJet h h'
    have h4 := cong (zeroPart T) (zeroPart T) _ A hT0 hT0
      (F.mul_isJet _ _ hP hInvJet) hA (refl_eqAsJet _) h3
    exact trans_eqAsJet h1 (trans_eqAsJet h2 (trans_eqAsJet h4 hInvConst.2))
  have hNormN : jetNorm δ p N ≤ jetNorm δ p A * jetNorm δ p T := by
    refine le_trans ?_ (hNormMul A T hA hTj)
    have h10 : ∀ κ, N.f10 κ = (mul p A T).f10 κ := fun κ => by
      change (mul p A T).f10 κ + (-1 : ℂ) • (0 : QuotHom I I) = _
      simp
    have h01 : ∀ κ, N.f01 κ = (mul p A T).f01 κ := fun κ => by
      change (mul p A T).f01 κ + (-1 : ℂ) • (0 : QuotHom I I) = _
      simp
    have h11 : ∀ κ, N.f11 κ = (mul p A T).f11 κ := fun κ => by
      change (mul p A T).f11 κ + (-1 : ℂ) • (0 : QuotHom I I) = _
      simp
    unfold jetNorm
    simp only [h10, h01, h11]
    refine add_le_add (add_le_add (add_le_add ?_ le_rfl) le_rfl) le_rfl
    refine iSup₂_le fun κ hκ => ?_
    have h0 : N.f00 κ = 0 := hN00 hκ
    rw [h0, hZero]
    exact zero_le
  have hNegNorm : jetNorm δ p (smul (-1) N) ≤ jetNorm δ p N := by
    simpa using hSmulN (-1) N hN
  have hQn : jetNorm δ p Q ≤ (1 + jetNorm δ p N) ^ 2 := by
    calc jetNorm δ p Q
        ≤ jetNorm δ p (add (one I) (smul (-1) N)) + jetNorm δ p (mul p N N) :=
          hAddN _ _ hOneNeg hNN
      _ ≤ (jetNorm δ p (one I) + jetNorm δ p (smul (-1) N)) + jetNorm δ p N * jetNorm δ p N :=
          add_le_add (hAddN _ _ hOne hNeg) (hNormMul N N hN hN)
      _ ≤ (1 + jetNorm δ p N) + jetNorm δ p N * jetNorm δ p N :=
          add_le_add (add_le_add hOneN hNegNorm) le_rfl
      _ ≤ (1 + jetNorm δ p N) + jetNorm δ p N * jetNorm δ p N + jetNorm δ p N := le_self_add
      _ = (1 + jetNorm δ p N) ^ 2 := by ring
  have hBound : jetNorm δ p (mul p Q A) ≤
      jetNorm δ p A * (1 + jetNorm δ p A * jetNorm δ p T) ^ 2 := by
    calc jetNorm δ p (mul p Q A)
        ≤ jetNorm δ p Q * jetNorm δ p A := hNormMul Q A hQ hA
      _ ≤ (1 + jetNorm δ p A * jetNorm δ p T) ^ 2 * jetNorm δ p A := by
          gcongr
          exact hQn.trans (by gcongr)
      _ = _ := mul_comm _ _
  have hSup : jetNorm δ p A = ⨆ κ ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (T.f00 κ)) := by
    have h0 : ∀ S : Set (Fin 4 → ℂ),
        (⨆ κ ∈ S, quotHomNorm ((0 : (Fin 4 → ℂ) → QuotHom I I) κ)) = 0 := fun S => by
      simp [hZero]
    change (⨆ κ ∈ imStrip (2 * δ), quotHomNorm (quotHomInverse (T.f00 κ))) +
      (⨆ κ ∈ stripAddShift δ p, quotHomNorm ((0 : (Fin 4 → ℂ) → QuotHom I I) κ)) +
      (⨆ κ ∈ stripSubShift δ p, quotHomNorm ((0 : (Fin 4 → ℂ) → QuotHom I I) κ)) +
      (⨆ κ ∈ realDualPoints, quotHomNorm ((0 : (Fin 4 → ℂ) → QuotHom I I) κ)) = _
    rw [h0, h0, h0]
    simp
  exact ⟨hInvJet, hLeft, hRight, hBound, hSup⟩
end YangMills.Construction.PeriodicOperators.JetInverse
end
