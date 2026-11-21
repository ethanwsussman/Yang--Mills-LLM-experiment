import YangMills.Construction.Towers.FourierSumsOnTheSitesOfTheFinestLattice
import YangMills.Construction.Towers.PlaneWaveCoefficientsOnTheSites
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.VertexWaveCoefficients
open PeriodicOperators (descendFn_mkQuot colourVertices wNorm wInner IsQuotInvariant intShift)
open PlaneWaves (VertexClass freqBox vertexFourierCoeff vertexFieldOfClasses)
open PlaneWaveCalculus (VertexCoeffFacts integerWave expWave waveOnQuot)
open FinestFourierSums (FourierFacts IsIntPeriodic)
variable {L k : ℕ}
def vertexClassOf (L k : ℕ) (a : Fin 3) (x : FullSpace.Vertex L k 0) : (colourVertices L k 0).UnitQuot :=
  (colourVertices L k 0).mkQuot 1 ((a, x) : Fin 3 × FullSpace.Vertex L k 0)
theorem vertexClassOf_intShift (a : Fin 3) (v : Fin 4 → ℤ) (x : FullSpace.Vertex L k 0) :
    vertexClassOf L k a (FullSpace.vertexImage (intShift v) x) = vertexClassOf L k a x :=
  (Quot.sound ⟨v, by
    show ((a, FullSpace.vertexImage (intShift v) x) : Fin 3 × FullSpace.Vertex L k 0) =
      (a, FullSpace.vertexImage (intShift ((1 : ℕ) • v)) x)
    rw [one_smul]⟩).symm
def quotEquivColourClass (L k : ℕ) : (colourVertices L k 0).UnitQuot ≃ Fin 3 × VertexClass L k where
  toFun := Quot.lift (fun p : Fin 3 × FullSpace.Vertex L k 0 => (p.1, Quot.mk _ p.2)) (by
    rintro p _ ⟨v, rfl⟩
    exact Prod.ext rfl (Quot.sound ⟨(1 : ℕ) • v, rfl⟩))
  invFun q := Quot.lift (vertexClassOf L k q.1) (by
    rintro x _ ⟨v, rfl⟩
    exact (vertexClassOf_intShift q.1 v x).symm) q.2
  left_inv c := by
    obtain ⟨p, rfl⟩ := Quot.exists_rep c
    rfl
  right_inv q := by
    obtain ⟨a, d⟩ := q
    obtain ⟨x, rfl⟩ := Quot.exists_rep d
    rfl
theorem quotEquivColourClass_symm_apply (a : Fin 3) (d : VertexClass L k) :
    (quotEquivColourClass L k).symm (a, d) = vertexClassOf L k a (Quot.out d) := by
  have e : (quotEquivColourClass L k).symm (a, Quot.mk _ (Quot.out d)) =
      vertexClassOf L k a (Quot.out d) := rfl
  rwa [Quot.out_eq] at e
theorem exists_eq_vertexClassOf (c : (colourVertices L k 0).UnitQuot) :
    ∃ a x, c = vertexClassOf L k a x := by
  obtain ⟨p, rfl⟩ := Quot.exists_rep c
  exact ⟨p.1, p.2, rfl⟩
theorem tsum_quot_eq_sum_finsum {A : Type} [AddCommMonoid A] [TopologicalSpace A] (hF : FourierFacts L k)
    (F : (colourVertices L k 0).UnitQuot → A) :
    ∑' c, F c = ∑ a, ∑ᶠ d : VertexClass L k, F (vertexClassOf L k a (Quot.out d)) := by
  have := hF.finite_vertexClass
  let := Fintype.ofFinite (VertexClass L k)
  rw [← (quotEquivColourClass L k).symm.tsum_eq F, tsum_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun d _ => by rw [quotEquivColourClass_symm_apply]
theorem quotWeight_eq_finestMesh_pow (c : (colourVertices L k 0).UnitQuot) :
    (colourVertices L k 0).quotWeight 1 c = finestMesh L k ^ 4 := by
  have h := Classical.epsilon_spec
    (p := fun w => ∀ p, (colourVertices L k 0).mkQuot 1 p = c →
      (colourVertices L k 0).weightOf p = w) ⟨finestMesh L k ^ 4, fun _ _ => rfl⟩
  obtain ⟨p, rfl⟩ := Quot.exists_rep c
  exact (h p rfl).symm
theorem eq_of_vertexClassOf_eq {φ : FullSpace.Vertex L k 0 → ℂ} (hφ : IsIntPeriodic L k φ)
    {a b : Fin 3} {x y : FullSpace.Vertex L k 0} (e : vertexClassOf L k a x = vertexClassOf L k b y) :
    a = b ∧ φ x = φ y := by
  have h := congrArg (quotEquivColourClass L k) e
  have h₁ : (a, (Quot.mk _ x : VertexClass L k)) = (b, Quot.mk _ y) := h
  refine ⟨(Prod.ext_iff.mp h₁).1, ?_⟩
  exact congrArg (Quot.lift φ (by
    rintro x _ ⟨v, rfl⟩
    exact (hφ v x).symm)) (Prod.ext_iff.mp h₁).2
open Classical in
theorem waveOnQuot_vertexClassOf (hF : FourierFacts L k) (c a : Fin 3) (m : Fin 4 → ℤ)
    (x : FullSpace.Vertex L k 0) :
    waveOnQuot (colourVertices L k 0) (fun p => p.1 = c) m (vertexClassOf L k a x) =
      if a = c then integerWave m (x : InfiniteLattice.AmbientSpace) else 0 := by
  unfold waveOnQuot
  refine (descendFn_mkQuot (P := colourVertices L k 0) ?_
    ((a, x) : Fin 3 × FullSpace.Vertex L k 0)).trans ?_
  · rintro ⟨b, y⟩ ⟨b', y'⟩ e
    obtain ⟨e₁, e₂⟩ :=
      eq_of_vertexClassOf_eq (hF.integerWave_periodic m) (a := b) (b := b') (x := y) (y := y') e
    subst e₁
    have e₃ : integerWave m (y : InfiniteLattice.AmbientSpace) =
      integerWave m (y' : InfiniteLattice.AmbientSpace) := e₂
    by_cases hb : b = c
    · exact (if_pos hb).trans (e₃.trans (if_pos hb).symm)
    · exact (if_neg hb).trans (if_neg hb).symm
  · by_cases h : a = c
    · exact (if_pos h).trans (if_pos h).symm
    · exact (if_neg h).trans (if_neg h).symm
theorem vertexFieldOfClasses_isIntPeriodic (l : (colourVertices L k 0).UnitQuot → ℂ) :
    IsIntPeriodic L k (vertexFieldOfClasses L k l) := fun v x => by
  show ∑ a, l (vertexClassOf L k a (FullSpace.vertexImage (intShift v) x)) •
      Matrices.ComplexMatrix2.pauliFamily a =
    ∑ a, l (vertexClassOf L k a x) • Matrices.ComplexMatrix2.pauliFamily a
  simp only [vertexClassOf_intShift]
theorem colourComponent_isIntPeriodic (l : (colourVertices L k 0).UnitQuot → ℂ) (a : Fin 3) :
    IsIntPeriodic L k fun x => l (vertexClassOf L k a x) := fun v x => by
  show l (vertexClassOf L k a (FullSpace.vertexImage (intShift v) x)) = l (vertexClassOf L k a x)
  rw [vertexClassOf_intShift]
theorem vertexCoeffFacts_of_fourierFacts (hF : FourierFacts L k) : VertexCoeffFacts L k := by
  refine
    { basis := ⟨?_, ?_⟩
      expansion := fun l x => hF.expansion _ (vertexFieldOfClasses_isIntPeriodic l) x
      exp_expansion := ?_
      norm_sq := ?_
      pairing_eq := ?_ }
  · intro c c' m hm m' hm'
    have g : ∀ a x, conj (waveOnQuot (colourVertices L k 0) (fun p => p.1 = c) m (vertexClassOf L k a x)) *
        waveOnQuot (colourVertices L k 0) (fun p => p.1 = c') m' (vertexClassOf L k a x) =
        if a = c ∧ a = c' then conj (integerWave m (x : InfiniteLattice.AmbientSpace)) *
          integerWave m' (x : InfiniteLattice.AmbientSpace) else 0 := fun a x => by
      rw [waveOnQuot_vertexClassOf hF, waveOnQuot_vertexClassOf hF]
      by_cases h₁ : a = c
      · by_cases h₂ : a = c'
        · rw [if_pos h₁, if_pos h₂, if_pos ⟨h₁, h₂⟩]
        · rw [if_neg h₂, mul_zero, if_neg (show ¬(a = c ∧ a = c') from fun h => h₂ h.2)]
      · rw [if_neg h₁, map_zero, zero_mul, if_neg (show ¬(a = c ∧ a = c') from fun h => h₁ h.1)]
    show ∑' c₀, (((colourVertices L k 0).quotWeight 1 c₀ : ℝ) : ℂ) *
      (conj (waveOnQuot (colourVertices L k 0) (fun p => p.1 = c) m c₀) *
        waveOnQuot (colourVertices L k 0) (fun p => p.1 = c') m' c₀) = _
    simp only [quotWeight_eq_finestMesh_pow]
    rw [tsum_mul_left, tsum_quot_eq_sum_finsum hF]
    simp only [g]
    by_cases hc : c = c'
    · subst hc
      rw [Finset.sum_eq_single c (fun a _ ha => by simp [ha]) (by simp)]
      simp only [and_self, if_true, true_and]
      rw [hF.orthonormal m hm m' hm']
    · rw [Finset.sum_eq_zero fun a _ => by
        have hn : ¬(a = c ∧ a = c') := fun h => hc (h.1.symm.trans h.2)
        simp [hn]]
      simp [hc]
  · rw [eq_top_iff]
    intro f _
    choose z hz using fun a => hF.span _ (colourComponent_isIntPeriodic f a)
    have e : f = ∑ a, ∑ m ∈ freqBox L k, z a m •
        waveOnQuot (colourVertices L k 0) (fun p => p.1 = a) m := by
      funext c
      obtain ⟨a, x, rfl⟩ := exists_eq_vertexClassOf c
      rw [hz a x]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, waveOnQuot_vertexClassOf hF]
      rw [Finset.sum_eq_single a]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp
    rw [e]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun m hm =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, m, hm, rfl⟩)
  · intro κ l x
    have e := hF.expansion _ (vertexFieldOfClasses_isIntPeriodic l) x
    rw [e, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, hF.expWave_mul_integerWave]
    rfl
  · intro l
    have hnn : 0 ≤ ∑' c, (colourVertices L k 0).quotWeight 1 c * ‖l c‖ ^ 2 :=
      tsum_nonneg fun c => by
        rw [quotWeight_eq_finestMesh_pow]
        positivity
    rw [wNorm, Real.sq_sqrt hnn]
    simp only [quotWeight_eq_finestMesh_pow]
    rw [tsum_mul_left, tsum_quot_eq_sum_finsum hF]
    exact hF.norm_sq (fun p => l (vertexClassOf L k p.1 p.2)) (colourComponent_isIntPeriodic l)
  · intro l l'
    show ∑' c, (((colourVertices L k 0).quotWeight 1 c : ℝ) : ℂ) * (l c * l' c) = _
    simp only [quotWeight_eq_finestMesh_pow]
    rw [tsum_mul_left, tsum_quot_eq_sum_finsum hF]
    exact hF.pairing_eq (fun p => l (vertexClassOf L k p.1 p.2)) (fun p => l' (vertexClassOf L k p.1 p.2))
      (colourComponent_isIntPeriodic l) (colourComponent_isIntPeriodic l')
theorem vertexCoeffsHold_of_claim (hF : FinestFourierSums.Claim) : PlaneWaveCalculus.VertexCoeffsHold :=
  fun L hL k hk => vertexCoeffFacts_of_fourierFacts (hF L hL k hk)
end YangMills.Construction.Tower.VertexWaveCoefficients
end
