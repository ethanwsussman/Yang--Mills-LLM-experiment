import YangMills.Construction.PeriodicOperators.JetTripleOfALocalOperatorFunction
import YangMills.Construction.PeriodicOperators.KernelsOfALocalOperatorFunctionProof
import YangMills.Construction.PeriodicOperators.ProductsOfJetsProof
import YangMills.Construction.PeriodicOperators.QuasiPeriodicityOfTheJetOfAFunction
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicOperators.JetQuasiPeriodic
open YangMills.Construction.TorusMetric (euclidNormVec)
variable {I I' : PeriodicData}
theorem symbolHom_apply (hI : IsPeriodic I) (Z : I'.Carrier → I.Carrier → ℂ) (k : Fin 4 → ℂ)
    (f : I.UnitQuot → ℂ) : symbolHom I I' Z k f = applyKernel (quotSymbol I I' Z k) f := by apply _root_.YangMills.Construction.Tower.PlaneWaveSmoothingSymbols.symbolHom_eq_applyKernel <;> assumption
theorem blochWave_injective (I : PeriodicData) (k : Fin 4 → ℂ) {f g : I.UnitQuot → ℂ}
    (h : ∀ i, blochWave I k f i = blochWave I k g i) : f = g := by apply _root_.YangMills.Construction.PeriodicOperators.OpFunKernels.blochWave_injective <;> assumption
def expPhaseAt (n : Fin 4 → ℤ) (y : InfiniteLattice.AmbientSpace) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * bilinDot (toComplexVec (castVec n)) (toComplexVec y))
theorem bilinDot_addTwoPiInt (k y : Fin 4 → ℂ) (n : Fin 4 → ℤ) :
    bilinDot (addTwoPiInt k n) y =
      bilinDot k y + 2 * Real.pi * bilinDot (toComplexVec (castVec n)) y := by apply _root_.YangMills.Construction.PeriodicOperators.SymbolTranslation.bilinDot_addTwoPiInt <;> assumption
theorem phaseOn_mkQuot (n : Fin 4 → ℤ)
    (hp : ∀ i₁ i₂, I.mkQuot 1 i₁ = I.mkQuot 1 i₂ →
      expPhaseAt n (I.pos i₁) = expPhaseAt n (I.pos i₂)) (i : I.Carrier) :
    phaseOn I n (I.mkQuot 1 i) = expPhaseAt n (I.pos i) := by
  have hex : ∃ w, ∀ b, I.mkQuot 1 b = I.mkQuot 1 i →
      Complex.exp (2 * Real.pi * Complex.I *
        bilinDot (toComplexVec (castVec n)) (toComplexVec (I.pos b))) = w :=
    ⟨expPhaseAt n (I.pos i), fun b h => hp b i h⟩
  exact (Classical.epsilon_spec hex i rfl).symm
theorem blochWave_addTwoPiInt (n : Fin 4 → ℤ)
    (hp : ∀ i₁ i₂, I.mkQuot 1 i₁ = I.mkQuot 1 i₂ →
      expPhaseAt n (I.pos i₁) = expPhaseAt n (I.pos i₂))
    (k : Fin 4 → ℂ) (f : I.UnitQuot → ℂ) (i : I.Carrier) :
    blochWave I (addTwoPiInt k n) f i = blochWave I k (phaseMul I n f) i := by
  have hE : phaseMul I n f (I.mkQuot 1 i) =
      expPhaseAt n (I.pos i) * f (I.mkQuot 1 i) := by
    rw [← phaseOn_mkQuot n hp i]
    rfl
  have hx : Complex.I * bilinDot (addTwoPiInt k n) (toComplexVec (I.pos i)) =
      Complex.I * bilinDot k (toComplexVec (I.pos i)) +
        2 * Real.pi * Complex.I *
          bilinDot (toComplexVec (castVec n)) (toComplexVec (I.pos i)) := by
    rw [bilinDot_addTwoPiInt]
    ring
  simp only [blochWave]
  rw [hE, hx, Complex.exp_add, expPhaseAt, mul_assoc]
theorem addTwoPiInt_add (k q : Fin 4 → ℂ) (n : Fin 4 → ℤ) :
    addTwoPiInt k n + q = addTwoPiInt (k + q) n := by apply _root_.YangMills.Construction.PeriodicOperators.JetProducts.addTwoPiInt_add <;> assumption
theorem eq_conj_of_blochWave_relation (W : I'.Carrier → I.Carrier → ℂ) (q : Fin 4 → ℂ)
    (A : (Fin 4 → ℂ) → QuotHom I I')
    (hA : ∀ (k : Fin 4 → ℂ) (f : I.UnitQuot → ℂ) (i' : I'.Carrier),
      applyKernel W (blochWave I k f) i' = blochWave I' (k + q) (A k f) i')
    (n : Fin 4 → ℤ)
    (hp : ∀ i₁ i₂, I.mkQuot 1 i₁ = I.mkQuot 1 i₂ →
      expPhaseAt n (I.pos i₁) = expPhaseAt n (I.pos i₂))
    (hp' : ∀ i₁ i₂, I'.mkQuot 1 i₁ = I'.mkQuot 1 i₂ →
      expPhaseAt n (I'.pos i₁) = expPhaseAt n (I'.pos i₂))
    (hU : IsUnit (phaseMul I' n : Module.End ℂ (I'.UnitQuot → ℂ)))
    (k : Fin 4 → ℂ) :
    A (addTwoPiInt k n) =
      (quotHomInverse (phaseMul I' n)).comp ((A k).comp (phaseMul I n)) := by
  refine LinearMap.ext fun f => ?_
  have hwave : blochWave I (addTwoPiInt k n) f =
      blochWave I k (phaseMul I n f) :=
    funext (blochWave_addTwoPiInt n hp k f)
  have key : phaseMul I' n (A (addTwoPiInt k n) f) =
      A k (phaseMul I n f) := by
    refine blochWave_injective I' (k + q) fun i' => ?_
    rw [← blochWave_addTwoPiInt n hp', ← addTwoPiInt_add, ← hA, hwave, hA]
  have hinv := Ring.inverse_mul_cancel (phaseMul I' n : Module.End ℂ (I'.UnitQuot → ℂ)) hU
  have h1 := LinearMap.congr_fun hinv (A (addTwoPiInt k n) f)
  simp only [Module.End.mul_apply, Module.End.one_apply] at h1
  rw [key] at h1
  exact h1.symm
theorem claim_holds (hJ : LocalOpFunTriple.Claim)
    (hD : CovariantFiniteRange.Claim) (hT : SymbolTranslation.Claim) :
    Claim := by
  intro F I I' _ hI hI' T hLoc p sPlus sMinus
  have hphase : ∀ J : PeriodicData, IsPeriodic J → ∀ (n : Fin 4 → ℤ) (i₁ i₂ : J.Carrier),
      J.mkQuot 1 i₁ = J.mkQuot 1 i₂ →
        expPhaseAt n (J.pos i₁) = expPhaseAt n (J.pos i₂) := fun J hJ' n =>
    (hT.1 J J hJ' hJ' _ (hD.1 J hJ').2.1).exp_phase_eq_of_mkQuot_eq n
  obtain ⟨r, R, hM⟩ := hLoc
  have hzero : IsSupBelow F (0 : F.Carrier → ℂ) r := ⟨0, hM.radius_pos, fun k => by simp⟩
  have hcov : IsPhaseCovariant I I' 0 (coeffZero F I I' T) := by
    intro n i' i
    have h := hM.shift_covariant 0 hzero n i' i
    have hdot : bilinDot 0 (toComplexVec (castVec n)) = 0 := by simp [bilinDot]
    rw [hdot, mul_zero, Complex.exp_zero, one_mul]
    exact h
  have hvan : VanishesOutsideRadius I I' R (coeffZero F I I' T) := by
    intro i' i h
    refine hM.vanish_far 0 hzero i' i fun h' => h ?_
    have hs : euclidNormVec (I'.pos i' - I.pos i) =
        euclidNormVec (I.pos i - I'.pos i') := by
      simp only [euclidNormVec, Pi.sub_apply]
      congr 1
      exact Finset.sum_congr rfl fun m _ => by ring
    rwa [hs]
  have hrem : dephasedKernel I I' 0 (coeffZero F I I' T) =
      coeffZero F I I' T := by
    funext i' i
    simp [dephasedKernel, bilinDot]
  have hop := (hD.2 I I' hI hI' 0 R _ hcov hvan).1
  rw [hrem] at hop
  have hfacts := hT.1 I I' hI hI' _ hop.periodic
  have hsum : ∀ k, SymbolSummableAt I I' (coeffZero F I I' T) k :=
    fun k => hop.summable k (mem_univ k)
  have hU : ∀ n : Fin 4 → ℤ,
      IsUnit (phaseMul I' n : Module.End ℂ (I'.UnitQuot → ℂ)) := fun n =>
    (hfacts.quotSymbol_addTwoPiInt 0 n (hsum 0)).2.1
  have hspec : IsActionTriple F I I' T p sPlus sMinus
      (Classical.epsilon (IsActionTriple F I I' T p sPlus sMinus)) :=
    Classical.epsilon_spec
      ((hJ F I I' ‹_› hI hI' T ⟨r, R, hM⟩).1 p sPlus sMinus).exists
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n k _
    refine LinearMap.ext fun f => ?_
    change symbolHom I I' (coeffZero F I I' T) (addTwoPiInt k n) f =
      quotHomInverse (phaseMul I' n)
        (symbolHom I I' (coeffZero F I I' T) k (phaseMul I n f))
    rw [symbolHom_apply hI, symbolHom_apply hI,
      (hfacts.quotSymbol_addTwoPiInt k n (hsum k)).2.2 f]
    rfl
  · intro n k _
    exact eq_conj_of_blochWave_relation (coeffOne F I I' T (blochWave F p sPlus)) p _
      (fun k f i' => (hspec k f i').1) n (hphase I hI n) (hphase I' hI' n) (hU n) k
  · intro n k _
    exact eq_conj_of_blochWave_relation (coeffOne F I I' T (blochWave F (-p) sMinus)) (-p) _
      (fun k f i' => by rw [← sub_eq_add_neg]; exact (hspec k f i').2.1) n
      (hphase I hI n) (hphase I' hI' n) (hU n) k
  · intro n k _
    exact eq_conj_of_blochWave_relation
      (coeffTwo F I I' T (blochWave F p sPlus) (blochWave F (-p) sMinus)) 0 _
      (fun k f i' => by rw [add_zero]; exact (hspec k f i').2.2) n
      (hphase I hI n) (hphase I' hI' n) (hU n) k
end YangMills.Construction.PeriodicOperators.JetQuasiPeriodic
end
