import YangMills.Construction.Towers.FourierSumsOnTheSitesOfTheFinestLattice
import YangMills.Construction.Towers.PlaneWaveCoefficientsOnThePlaquettes
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.Tower.FaceCoeffProof
open PeriodicOperators (PeriodicData IsQuotInvariant descendFn descendFn_mkQuot colourFaces wNorm
  wInner shiftFace intShift)
open PlaneWaves (VertexClass fourierCoeff freqBox faceFourierCoeff faceFieldOfClasses shiftedFreq)
open PlaneWaveCalculus (FaceCoeffFacts AxisPair WavesOrthonormalBasis integerWave tracelessPairing
  expWave waveOnQuot)
open FinestFourierSums (FourierFacts IsIntPeriodic)
variable {L j : ℕ}
def faceAt (p : AxisPair) (x : FullSpace.Vertex L j 0) : FullSpace.Face L j 0 :=
  ⟨x, p.1.1, p.1.2, p.2⟩
def labelQuot (a : Fin 3) (p : AxisPair) (x : FullSpace.Vertex L j 0) :
    (colourFaces L j 0).UnitQuot :=
  (colourFaces L j 0).mkQuot 1 (a, faceAt p x)
theorem labelQuot_vertexImage (a : Fin 3) (p : AxisPair) (v : Fin 4 → ℤ)
    (x : FullSpace.Vertex L j 0) :
    labelQuot a p (FullSpace.vertexImage (intShift v) x) = labelQuot a p x := by
  refine (Quot.sound ⟨v, ?_⟩).symm
  rw [one_smul]
  rfl
def quotOfTriple (t : Fin 3 × AxisPair × VertexClass L j) :
    (colourFaces L j 0).UnitQuot :=
  Quot.lift (labelQuot t.1 t.2.1)
    (by
      rintro x _ ⟨v, rfl⟩
      exact (labelQuot_vertexImage t.1 t.2.1 v x).symm) t.2.2
def tripleOfQuot (c : (colourFaces L j 0).UnitQuot) :
    Fin 3 × AxisPair × VertexClass L j :=
  Quot.lift
    (fun ι : (colourFaces L j 0).Carrier =>
      (ι.1, (⟨(ι.2.lowAxis, ι.2.highAxis), ι.2.lowAxis_lt_highAxis⟩ : AxisPair),
        (Quot.mk _ ι.2.corner : VertexClass L j)))
    (by
      rintro ι _ ⟨v, rfl⟩
      rw [one_smul]
      have e : (Quot.mk _ ι.2.corner : VertexClass L j) =
          Quot.mk _ (FullSpace.vertexImage (intShift v) ι.2.corner) := Quot.sound ⟨v, rfl⟩
      simp only [Prod.mk.injEq]
      exact ⟨rfl, rfl, e⟩) c
def tripleEquivQuot : Fin 3 × AxisPair × VertexClass L j ≃ (colourFaces L j 0).UnitQuot where
  toFun := quotOfTriple
  invFun := tripleOfQuot
  left_inv := by
    rintro ⟨a, p, d⟩
    induction d using Quot.ind
    rfl
  right_inv := by
    intro c
    induction c using Quot.ind
    rfl
theorem tripleEquivQuot_apply (a : Fin 3) (p : AxisPair) (d : VertexClass L j) :
    tripleEquivQuot (a, p, d) = labelQuot a p (Quot.out d : FullSpace.Vertex L j 0) := by
  have e : ∀ x : FullSpace.Vertex L j 0, (Quot.mk _ x : VertexClass L j) = d →
      tripleEquivQuot (a, p, d) = labelQuot a p x := by
    rintro x rfl
    rfl
  exact e _ (Quot.out_eq d)
theorem tsum_unitQuot {E : Type} [AddCommMonoid E] [TopologicalSpace E] [T2Space E]
    (hfin : Finite (VertexClass L j)) (h : (colourFaces L j 0).UnitQuot → E) :
    ∑' c, h c =
      ∑ a, ∑ p : AxisPair, ∑ᶠ d : VertexClass L j,
        h (labelQuot a p (Quot.out d : FullSpace.Vertex L j 0)) := by
  classical
  have := Fintype.ofFinite (VertexClass L j)
  rw [← tripleEquivQuot.tsum_eq h, tsum_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun d _ => by rw [tripleEquivQuot_apply]
theorem quotWeight_eq (c : (colourFaces L j 0).UnitQuot) :
    (colourFaces L j 0).quotWeight 1 c = finestMesh L j ^ 4 := by
  have hz : ∃ w, ∀ ι, (colourFaces L j 0).mkQuot 1 ι = c →
      (colourFaces L j 0).weightOf ι = w := ⟨finestMesh L j ^ 4, fun _ _ => rfl⟩
  induction c using Quot.ind with
  | mk ι => exact (Classical.epsilon_spec hz ι rfl).symm
def pauliFamily (f : (colourFaces L j 0).UnitQuot → ℂ) (p : AxisPair) :
    Fin 3 × FullSpace.Vertex L j 0 → ℂ :=
  fun ι => f (labelQuot ι.1 p ι.2)
theorem pauliFamily_periodic (f : (colourFaces L j 0).UnitQuot → ℂ) (p : AxisPair)
    (a : Fin 3) : IsIntPeriodic L j fun x => pauliFamily f p (a, x) :=
  fun v x => by simp only [pauliFamily, labelQuot_vertexImage]
theorem ofPauliCoeffs_periodic (f : (colourFaces L j 0).UnitQuot → ℂ) (p : AxisPair) :
    IsIntPeriodic L j (ofPauliCoeffs (pauliFamily f p)) :=
  fun v x => by simp only [ofPauliCoeffs, pauliFamily, labelQuot_vertexImage]
def HasLabel (c : Fin 3 × AxisPair) (ι : (colourFaces L j 0).Carrier) : Prop :=
  ι.1 = c.1 ∧ ι.2.lowAxis = c.2.1.1 ∧ ι.2.highAxis = c.2.1.2
theorem hasLabel_faceAt_iff (c : Fin 3 × AxisPair) (a : Fin 3) (p : AxisPair)
    (x : FullSpace.Vertex L j 0) : HasLabel c (a, faceAt p x) ↔ (a, p) = c := by
  obtain ⟨a', ⟨⟨μ', ν'⟩, h'⟩⟩ := c
  obtain ⟨⟨μ, ν⟩, h⟩ := p
  simp [HasLabel, faceAt]
open Classical in
theorem waveOnQuot_labelQuot (hF : FourierFacts L j) (c : Fin 3 × AxisPair) (m : Fin 4 → ℤ)
    (a : Fin 3) (p : AxisPair) (x : FullSpace.Vertex L j 0) :
    waveOnQuot (colourFaces L j 0) (HasLabel c) m (labelQuot a p x) =
      if (a, p) = c then integerWave m (x : InfiniteLattice.AmbientSpace) else 0 := by
  have hone : IsQuotInvariant (colourFaces L j 0) fun ι =>
      if HasLabel c ι then integerWave m ((colourFaces L j 0).pos ι) else 0 := by
    intro ι ι' e
    let φ : (colourFaces L j 0).UnitQuot → ℂ :=
      Quot.lift (fun ι => if HasLabel c ι then integerWave m ((colourFaces L j 0).pos ι)
        else 0)
        (by
          rintro ⟨a, P⟩ _ ⟨v, rfl⟩
          have hw : integerWave m ((FullSpace.vertexImage (intShift (1 • v)) P.corner :
              FullSpace.Vertex L j 0) : InfiniteLattice.AmbientSpace) =
              integerWave m (P.corner : InfiniteLattice.AmbientSpace) :=
            hF.integerWave_periodic m (1 • v) P.corner
          show (if HasLabel c (a, P) then integerWave m (P.corner : InfiniteLattice.AmbientSpace)
              else 0) =
            if HasLabel c (a, shiftFace (1 • v) P) then
              integerWave m ((FullSpace.vertexImage (intShift (1 • v)) P.corner :
                FullSpace.Vertex L j 0) : InfiniteLattice.AmbientSpace) else 0
          rw [hw]
          rfl)
    exact congrArg φ e
  have e := descendFn_mkQuot hone
    (show (colourFaces L j 0).Carrier from (a, faceAt p x))
  by_cases h : (a, p) = c
  · rw [if_pos h]
    exact e.trans (if_pos ((hasLabel_faceAt_iff c a p x).2 h))
  · rw [if_neg h]
    exact e.trans (if_neg fun h' => h ((hasLabel_faceAt_iff c a p x).1 h'))
open Classical in
theorem waveOnQuot_orthonormal (hF : FourierFacts L j) (c c' : Fin 3 × AxisPair) (m : Fin 4 → ℤ)
    (hm : m ∈ freqBox L j) (m' : Fin 4 → ℤ) (hm' : m' ∈ freqBox L j) :
    wInner ((colourFaces L j 0).quotWeight 1)
        (waveOnQuot (colourFaces L j 0) (HasLabel c) m)
        (waveOnQuot (colourFaces L j 0) (HasLabel c') m') =
      if c = c' ∧ m = m' then 1 else 0 := by
  have hsum : wInner ((colourFaces L j 0).quotWeight 1)
        (waveOnQuot (colourFaces L j 0) (HasLabel c) m)
        (waveOnQuot (colourFaces L j 0) (HasLabel c') m') =
      ((finestMesh L j ^ 4 : ℝ) : ℂ) * ∑ t : Fin 3 × AxisPair, ∑ᶠ d : VertexClass L j,
        conj (if t = c then integerWave m (Quot.out d : FullSpace.Vertex L j 0) else 0) *
          (if t = c' then integerWave m' (Quot.out d : FullSpace.Vertex L j 0) else 0) := by
    simp only [wInner, PeriodicOperators.wPairing, quotWeight_eq]
    rw [tsum_mul_left, tsum_unitQuot hF.finite_vertexClass, Fintype.sum_prod_type]
    simp only [waveOnQuot_labelQuot hF]
  rw [hsum, Finset.sum_eq_single c]
  · by_cases hc : c = c'
    · subst hc
      simp only [if_true, true_and]
      exact hF.orthonormal m hm m' hm'
    · simp [hc]
  · intro t _ ht
    simp [ht]
  · intro h
    exact absurd (Finset.mem_univ c) h
theorem waveOnQuot_span (hF : FourierFacts L j) :
    Submodule.span ℂ {f | ∃ c : Fin 3 × AxisPair, ∃ m ∈ freqBox L j,
      f = waveOnQuot (colourFaces L j 0) (HasLabel c) m} = ⊤ := by
  classical
  rw [Submodule.eq_top_iff']
  intro f
  choose z hz using fun t : Fin 3 × AxisPair =>
    hF.span (fun x => pauliFamily f t.2 (t.1, x)) (pauliFamily_periodic f t.2 t.1)
  have key : f = ∑ t : Fin 3 × AxisPair, ∑ m ∈ freqBox L j,
      z t m • waveOnQuot (colourFaces L j 0) (HasLabel t) m := by
    funext c
    have hc : ∃ (a : Fin 3) (p : AxisPair) (x : FullSpace.Vertex L j 0), c = labelQuot a p x := by
      induction c using Quot.ind with
      | mk ι => exact ⟨ι.1, ⟨(ι.2.lowAxis, ι.2.highAxis), ι.2.lowAxis_lt_highAxis⟩, ι.2.corner, rfl⟩
    obtain ⟨a, p, x, rfl⟩ := hc
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, waveOnQuot_labelQuot hF]
    rw [Finset.sum_eq_single (a, p)]
    · simpa [pauliFamily] using hz (a, p) x
    · intro t _ ht
      have : (a, p) ≠ t := fun e => ht e.symm
      simp [this]
    · intro h
      exact absurd (Finset.mem_univ _) h
  rw [key]
  exact Submodule.sum_mem _ fun t _ => Submodule.sum_mem _ fun m hm =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, m, hm, rfl⟩)
theorem wNorm_sq_eq (hF : FourierFacts L j) (f : (colourFaces L j 0).UnitQuot → ℂ) :
    wNorm ((colourFaces L j 0).quotWeight 1) f ^ 2 =
      finestMesh L j ^ 4 * ∑ a, ∑ p : AxisPair, ∑ᶠ d : VertexClass L j,
        ‖pauliFamily f p (a, (Quot.out d : FullSpace.Vertex L j 0))‖ ^ 2 := by
  rw [wNorm, Real.sq_sqrt (tsum_nonneg fun c => by
    rw [quotWeight_eq]
    positivity)]
  simp only [quotWeight_eq]
  rw [tsum_mul_left, tsum_unitQuot hF.finite_vertexClass]
  rfl
theorem faceCoeffFacts (hF : FourierFacts L j) : FaceCoeffFacts L j where
  basis := ⟨fun c c' m hm m' hm' =>
    (waveOnQuot_orthonormal hF c c' m hm m' hm').trans (by split_ifs <;> rfl), waveOnQuot_span hF⟩
  expansion := fun f μ ν h x => hF.expansion _ (ofPauliCoeffs_periodic f ⟨(μ, ν), h⟩) x
  exp_expansion := by
    intro κ f μ ν h x
    have e := hF.expansion _ (ofPauliCoeffs_periodic f ⟨(μ, ν), h⟩) x
    show expWave κ x • ofPauliCoeffs (pauliFamily f ⟨(μ, ν), h⟩) x =
      ∑ m ∈ freqBox L j, expWave (shiftedFreq κ m) x •
        fourierCoeff L j (ofPauliCoeffs (pauliFamily f ⟨(μ, ν), h⟩)) m
    conv_lhs => rw [e]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, hF.expWave_mul_integerWave]
  norm_sq := by
    intro f
    rw [wNorm_sq_eq hF, Finset.sum_comm, Finset.mul_sum, Finset.sum_comm (s := freqBox L j)]
    refine Finset.sum_congr rfl fun p _ => ?_
    exact hF.norm_sq (pauliFamily f p) (pauliFamily_periodic f p)
  pairing_eq := by
    intro f f'
    have hsum : PeriodicOperators.wPairing ((colourFaces L j 0).quotWeight 1) f f' =
        ((finestMesh L j ^ 4 : ℝ) : ℂ) * ∑ a, ∑ p : AxisPair, ∑ᶠ d : VertexClass L j,
          pauliFamily f p (a, (Quot.out d : FullSpace.Vertex L j 0)) *
            pauliFamily f' p (a, (Quot.out d : FullSpace.Vertex L j 0)) := by
      simp only [PeriodicOperators.wPairing, quotWeight_eq]
      rw [tsum_mul_left, tsum_unitQuot hF.finite_vertexClass]
      rfl
    rw [hsum, Finset.sum_comm, Finset.mul_sum, Finset.sum_comm (s := freqBox L j)]
    refine Finset.sum_congr rfl fun p _ => ?_
    exact hF.pairing_eq (pauliFamily f p) (pauliFamily f' p) (pauliFamily_periodic f p)
      (pauliFamily_periodic f' p)
theorem faceCoeffsHold_of_fourier (hFourier : FinestFourierSums.Claim) :
    PlaneWaveCalculus.FaceCoeffsHold :=
  fun L hL j hj => faceCoeffFacts (hFourier L hL j hj)
end YangMills.Construction.Tower.FaceCoeffProof
end
