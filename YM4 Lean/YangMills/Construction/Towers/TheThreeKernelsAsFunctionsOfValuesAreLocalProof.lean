import YangMills.Construction.Towers.KernelsOfPeriodicLocalBilinearMapsProof
import YangMills.Construction.Towers.TheGaugeTermOfTheKernelIsLocalProof
import YangMills.Construction.InfiniteLattice.TorusStatesAsPeriodicMeasuresProof
import YangMills.Construction.PassageToTheLimit.PartitionOfUnityOfClassC1WithSmallPiecesProof
import YangMills.Construction.PeriodicOperators.NumbersOfALocalOperatorFunctionProof
import YangMills.Construction.Towers.TheActionAndCurrentTermsOfTheKernelAreLocalProof
import YangMills.Construction.Towers.TheThreeKernelsAsFunctionsOfValuesAreLocal
import YangMills.Construction.Towers.TranslationRelationsOfTheTwoOperatorFunctions
import YangMills.Construction.Towers.TransposesOfTheIteratedAveragesOfTheScaledPictureOnTheWholeProof
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Tower.FullSpace.LocalKernelFunctions
section EvaluationMaps
variable {F : PeriodicOperators.PeriodicData}
theorem isSupBelow_mono {ζ : F.Carrier → ℂ} {ρ ρ' : ℝ} (h : PeriodicOperators.IsSupBelow F ζ ρ')
    (hle : ρ' ≤ ρ) : PeriodicOperators.IsSupBelow F ζ ρ := by apply _root_.YangMills.Construction.PeriodicOperators.ParameterIndependence.isSupBelow_mono <;> assumption
theorem isOpen_openPolydisk (l : ℕ) (r : ℝ) :
    IsOpen (Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk
      (0 : Coordinates.ComplexCoordinates l) r) := by apply _root_.YangMills.Construction.PeriodicOperators.TorusMatrixCoordinates.isOpen_openPolydisk_zero <;> assumption
theorem holomorphicIn_superset
    (hAffine : Matrices.GroupLieProduct.ExpChartHolomorphy.AffineHolomorphy)
    (hHolo : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {A S : Set F.Carrier} (hA : A.Finite) (hS : S ⊆ A) {ρ ρ' : ℝ} (hρ : ρ' ≤ ρ)
    {g : (F.Carrier → ℂ) → ℂ} (hg : PeriodicOperators.HolomorphicInValuesBelow F ρ S g) :
    ∃ (l : ℕ) (e : Fin l ≃ A) (h : Coordinates.ComplexCoordinates l → ℂ),
      Coordinates.ComplexCoordinates.IsHolomorphicIn (N' := 1)
        (Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk 0 ρ') (fun z _ => h z) ∧
      ∀ ζ, PeriodicOperators.IsSupBelow F ζ ρ' → g ζ = h (PeriodicOperators.fieldValues e ζ) := by
  obtain ⟨l, e, h, hol, hh⟩ := hg
  have := hA.to_subtype
  obtain ⟨m, ⟨e'⟩⟩ := Finite.exists_equiv_fin A
  let res : Coordinates.ComplexCoordinates m → Coordinates.ComplexCoordinates l :=
    fun z j => z (e' ⟨e j, hS (e j).2⟩)
  have hRes : Coordinates.ComplexCoordinates.IsHolomorphicIn
      (Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk
        (0 : Coordinates.ComplexCoordinates m) ρ') res := by
    have haff := hAffine m l (fun j => MvPolynomial.X (e' ⟨e j, hS (e j).2⟩))
      fun j => (MvPolynomial.totalDegree_X _).le
    have hfun : (fun (z : Coordinates.ComplexCoordinates m) (j : Fin l) =>
        MvPolynomial.eval z (MvPolynomial.X (e' ⟨e j, hS (e j).2⟩))) = res := by
      funext z j
      simp only [MvPolynomial.eval_X]
      rfl
    rw [hfun] at haff
    exact ⟨isOpen_openPolydisk _ _, haff.2.1.mono (subset_univ _),
      fun a _ j => haff.2.2 a (mem_univ a) j⟩
  have hmaps : MapsTo res
      (Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk
        (0 : Coordinates.ComplexCoordinates m) ρ')
      (Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.openPolydisk
        (0 : Coordinates.ComplexCoordinates l) ρ) := by
    intro z hz j
    have h1 : ‖z (e' ⟨e j, hS (e j).2⟩) - (0 : Coordinates.ComplexCoordinates m) _‖ < ρ' := hz _
    show ‖z (e' ⟨e j, hS (e j).2⟩) - (0 : Coordinates.ComplexCoordinates l) j‖ < ρ
    simp only [Pi.zero_apply, sub_zero] at h1 ⊢
    exact h1.trans_le hρ
  refine ⟨m, e'.symm, fun z => h (res z), ?_, ?_⟩
  · exact ((hHolo.1 l _ hol.1).1 1 _ hol).2.2.2.1 m _ _ hRes hmaps
  · intro ζ hζ
    rw [hh ζ (isSupBelow_mono hζ hρ)]
    refine congrArg h (funext fun j => ?_)
    show ζ (e j) = ζ (e'.symm (e' ⟨e j, hS (e j).2⟩) : A)
    rw [Equiv.symm_apply_apply]
end EvaluationMaps
section Distances
variable {L k : ℕ}
theorem euclidNormVec_le_two_mul {v : Fin 4 → ℝ} {r : ℝ} (hr : 0 ≤ r) (h : ∀ μ, |v μ| ≤ r) :
    TorusMetric.euclidNormVec v ≤ 2 * r := by apply _root_.YangMills.Construction.LimitSpaces.FinePartitionOfUnity.euclidNormVec_le <;> assumption
theorem meshAt_mul_pow (hL : 0 < L) : Tower.meshAt L k 0 * (L : ℝ) ^ k = 1 := by
  have hne : (L : ℝ) ≠ 0 := (Nat.cast_pos.2 hL).ne'
  unfold Tower.meshAt
  rw [← zpow_natCast, ← zpow_add₀ hne]
  simp
theorem meshAt_pos (hL : 0 < L) : 0 < Tower.meshAt L k 0 :=
  zpow_pos (Nat.cast_pos.2 hL) _
theorem meshAt_le_one (hL : 0 < L) : Tower.meshAt L k 0 ≤ 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.KernelTermsLocality.meshAt_le_one <;> assumption
theorem meshAt_self : Tower.meshAt L k k = 1 := by apply _root_.YangMills.Construction.Tower.FullSpace.IterTransposesOnFullSpace.meshAt_self <;> assumption
theorem link_abs_sub_le {a : ℝ} (ha : 0 ≤ a) (b : InfiniteLattice.Link a) (μ : Fin 4) :
    |(b.terminal : InfiniteLattice.AmbientSpace) μ - (b.initial : InfiniteLattice.AmbientSpace) μ|
      ≤ a := by apply _root_.YangMills.Construction.InfiniteLattice.PeriodicStates.abs_terminal_sub_initial_le <;> assumption
theorem cubeOfOrder_abs_sub_le (hL : 0 < L) {a : ℝ} (y : InfiniteLattice.LatticePoint a)
    {x : InfiniteLattice.AmbientSpace}
    (hx : x ∈ Tower.FullSpace.cubeOfOrder L (Tower.meshAt L k 0) k y) (μ : Fin 4) :
    |x μ - (y : InfiniteLattice.AmbientSpace) μ| ≤ 1 / 2 := by
  obtain ⟨ν, hν, rfl⟩ := hx
  have e : ((y : InfiniteLattice.AmbientSpace) +
      ∑ ρ, Pi.single ρ ((ν ρ : ℝ) * Tower.meshAt L k 0)) μ - (y : InfiniteLattice.AmbientSpace) μ =
      (ν μ : ℝ) * Tower.meshAt L k 0 := by
    simp [Finset.sum_apply, Pi.single_apply]
  rw [e, abs_mul, abs_of_pos (meshAt_pos hL)]
  have h1 : 2 * |(ν μ : ℝ)| ≤ (L : ℝ) ^ k - 1 := by exact_mod_cast hν μ
  have h2 := meshAt_mul_pow (k := k) hL
  have h3 := meshAt_pos (k := k) hL
  nlinarith
end Distances
section Difference
variable {L k : ℕ}
def basisVec {N : Type} (ι : N) : N → ℂ :=
  open Classical in fun ι₀ => if ι₀ = ι then 1 else 0
theorem applyKernel_basisVec {N N' : Type} (T : PeriodicOperators.KernelMatrix N N') (ι : N)
    (ι' : N') : PeriodicOperators.applyKernel T (basisVec ι) ι' = T ι' ι := by apply _root_.YangMills.Construction.LocalKernels.LocalBilinearKernels.applyKernel_pointIndicator <;> assumption
theorem kernel_apply_eq_coeffs (r r' : Tower.PauliComponentsOfSymmetricKernel)
    (m : (r.space.index → Matrices.ComplexMatrix2) → r'.space.index → Matrices.ComplexMatrix2)
    {T : PeriodicOperators.KernelMatrix r.Index r'.Index}
    (hT : PeriodicOperators.Represents T (Tower.PauliComponentsOfSymmetricKernel.mapOnCoeffs r r' m))
    (ι : r.Index) (ι' : r'.Index) :
    T ι' ι = r'.coeffs (m (r.ofCoeffs (basisVec ι))) ι' := by
  rw [← applyKernel_basisVec T ι ι', (hT _).2]
  rfl
theorem ofPauliCoeffs_basisVec (a : Fin 3) (x : Tower.FullSpace.Vertex L k 0) :
    (Tower.ofPauliCoeffs (basisVec ((a, x) : Fin 3 × Tower.FullSpace.Vertex L k 0)) :
      Tower.FullSpace.Vertex L k 0 → Matrices.ComplexMatrix2) =
      Tower.FullSpace.vertexBasisFunction a x := by apply _root_.YangMills.Construction.Tower.FullSpace.GaugeTermLocality.ofPauliCoeffs_unitVec <;> assumption
theorem covDiffFn_eq_covDiffEntry (hL : 0 < L) (hK : Tower.ThreeMapKernels.OnFullSpace L k)
    {f : (Tower.FullSpace.fieldPeriodicData L k hL).Carrier → ℂ}
    (hU : Tower.FullSpace.FieldValueFunctions.gaugeFieldOfCoeffs hL f ∈
      Tower.FullSpace.fieldsValuedIn L k 0 PeriodicLattice.complexGaugeGroup)
    (a' a : Fin 3) (b' : Tower.FullSpace.PositiveEdge (Tower.meshAt L k 0))
    (x : Tower.FullSpace.Vertex L k 0) :
    Tower.FullSpace.FieldValueFunctions.covDiffFn L k hL f (a', b') (a, x) =
      Tower.FullSpace.FieldValueFunctions.LocalComponents.covDiffEntry L k hL a' b' a x f := by
  have h := kernel_apply_eq_coeffs (Tower.vertexCoordinate (Tower.FullSpace.Vertex L k 0))
    (Tower.FullSpace.edgePauliCoordinates L k 0)
    (Tower.FullSpace.covDiff (Tower.FullSpace.FieldValueFunctions.gaugeFieldOfCoeffs hL f))
    (hK.2.1 _ hU).represents (a, x) (a', b')
  have e : (Tower.vertexCoordinate (Tower.FullSpace.Vertex L k 0)).ofCoeffs (basisVec (a, x)) =
      Tower.FullSpace.vertexBasisFunction a x := ofPauliCoeffs_basisVec a x
  rw [e] at h
  exact h
end Difference
theorem threeKernelsLocal_holds
    (hAction : Tower.FullSpace.FieldValueFunctions.LocalComponents.EntriesAreLocalAndEntire)
    (hIterated : Tower.FullSpace.IteratedKernelEntries.Claim)
    (hTranslation : Tower.FullSpace.ShiftCovariance.Claim)
    (hKernels : Tower.ThreeMapKernels.Claim)
    (hFinite : PeriodicOperators.CovariantFiniteRange.Claim)
    (hTower : LocalKernels.IndexSetPeriodicity.Statement)
    (hCharts : Matrices.GroupLieProduct.ExpChartHolomorphy.ExpChartTheory)
    (hHolo : Coordinates.ComplexCoordinates.PowerSeriesHolomorphy.Properties) :
    ThreeKernelsLocal := by
  intro L hL hS k hk
  obtain ⟨ρ₁, hρ₁, hSites, hBonds⟩ := hIterated L hL hS k hk
  obtain ⟨ρ₂, hρ₂, hT⟩ := hTranslation L hL hS k hk
  obtain ⟨-, hDiff, -⟩ := hAction L hL hS k
  have hK := (hKernels L hS k hk).2
  have hF : PeriodicOperators.IsPeriodic (Tower.FullSpace.fieldPeriodicData L k hL) :=
    ((hTower L hS k).2 (LocalKernels.fieldIndices L k hL)).1
  have hfin := (hFinite.1 _ hF).1
  have hρ : 0 < min ρ₁ ρ₂ := lt_min hρ₁ hρ₂
  have hb₁ : ∀ {f}, PeriodicOperators.IsSupBelow (Tower.FullSpace.fieldPeriodicData L k hL) f
      (min ρ₁ ρ₂) → PeriodicOperators.IsSupBelow (Tower.FullSpace.fieldPeriodicData L k hL) f ρ₁ :=
    fun h => isSupBelow_mono h (min_le_left _ _)
  have hb₂ : ∀ {f}, PeriodicOperators.IsSupBelow (Tower.FullSpace.fieldPeriodicData L k hL) f
      (min ρ₁ ρ₂) → PeriodicOperators.IsSupBelow (Tower.FullSpace.fieldPeriodicData L k hL) f ρ₂ :=
    fun h => isSupBelow_mono h (min_le_right _ _)
  have hsub : ∀ (T : Set (Tower.FullSpace.Edge L k 0)) (y : InfiniteLattice.AmbientSpace),
      (∀ b : Tower.FullSpace.PositiveEdge (Tower.meshAt L k 0), b.1 ∈ T →
        TorusMetric.euclidNormVec ((b.1.initial : InfiniteLattice.AmbientSpace) - y) ≤ 19) →
      Tower.FullSpace.FieldValueFunctions.backgroundCoords L k hL T ⊆
        PeriodicOperators.nearIndices (Tower.FullSpace.fieldPeriodicData L k hL) y 19 := by
    rintro T y h κ ⟨a, b, hb, rfl⟩
    exact h b hb
  have hnear : ∀ (y : InfiniteLattice.AmbientSpace) (r : ℝ), 0 ≤ r → r ≤ 3 →
      ∀ b : Tower.FullSpace.Edge L k 0,
        (∀ i, |(b.initial : InfiniteLattice.AmbientSpace) i - y i| < r ∨
          |(b.initial : InfiniteLattice.AmbientSpace) i - y i| ≤ r) →
      TorusMetric.euclidNormVec ((b.initial : InfiniteLattice.AmbientSpace) - y) ≤ 19 := by
    intro y r h0 h3 b h
    refine (euclidNormVec_le_two_mul h0 fun μ => ?_).trans (by linarith)
    rcases h μ with h | h
    · exact h.le
    · exact h
  refine ⟨min ρ₁ ρ₂, ⟨hρ, ?_, ?_, ?_⟩, ⟨hρ, ?_, ?_, ?_⟩, ⟨hρ, ?_, ?_, ?_⟩⟩
  · rintro ζ hζ ⟨a', b'⟩ ⟨a, x⟩ hn
    have hU := ((hT ζ (hb₂ hζ) 0).1).1
    rw [covDiffFn_eq_covDiffEntry hL hK hU]
    refine (hDiff a' a b' x).1 ?_ ?_ ζ
    · intro hx
      refine hn ?_
      show TorusMetric.euclidNormVec
        ((x : InfiniteLattice.AmbientSpace) - (b'.1.initial : InfiniteLattice.AmbientSpace)) ≤ 19
      rw [hx]
      exact (euclidNormVec_le_two_mul le_rfl (by simp)).trans (by norm_num)
    · intro hx
      refine hn ?_
      show TorusMetric.euclidNormVec
        ((x : InfiniteLattice.AmbientSpace) - (b'.1.initial : InfiniteLattice.AmbientSpace)) ≤ 19
      rw [hx]
      refine (euclidNormVec_le_two_mul (meshAt_pos hL).le
        (link_abs_sub_le (meshAt_pos hL).le b'.1)).trans ?_
      linarith [meshAt_le_one (k := k) hL]
  · rintro ⟨a', b'⟩ ⟨a, x⟩
    have hread := (hDiff a' a b' x).2 ρ₁ hρ₁
    obtain ⟨l, e, h, hol, hh⟩ := holomorphicIn_superset hCharts.1 hHolo
      (hfin (b'.1.initial : InfiniteLattice.AmbientSpace) 19)
      (hsub {b'.1} _ (by
        intro b hb
        rw [Set.mem_singleton_iff] at hb
        rw [hb]
        exact (euclidNormVec_le_two_mul le_rfl (by simp)).trans (by norm_num)))
      (min_le_left ρ₁ ρ₂) hread
    refine ⟨l, e, h, hol, fun ζ hζ => ?_⟩
    rw [covDiffFn_eq_covDiffEntry hL hK ((hT ζ (hb₂ hζ) 0).1).1]
    exact hh ζ hζ
  · intro ζ hζ n ι' ι
    exact (hT ζ (hb₂ hζ) n).2.2.2.2.2.covDiff ι' ι
  · rintro ζ hζ ⟨a', y⟩ ⟨a, x⟩ hn
    refine (hSites y a').2.2 a x (fun hx => hn ?_) ζ (hb₁ hζ)
    exact (euclidNormVec_le_two_mul (by norm_num) (cubeOfOrder_abs_sub_le hL y hx)).trans
      (by norm_num)
  · rintro ⟨a', y⟩ ι
    obtain ⟨l, e, h, hol, hh⟩ := holomorphicIn_superset hCharts.1 hHolo
      (hfin (y : InfiniteLattice.AmbientSpace) 19)
      (hsub (Tower.FullSpace.IteratedKernelEntries.edgesNear L k y 2) _ (fun b hb =>
        hnear _ 2 (by norm_num) (by norm_num) b.1 fun i => Or.inl (hb i).1))
      (min_le_left ρ₁ ρ₂) ((hSites y a').2.1 ι)
    exact ⟨l, e, h, hol, hh⟩
  · intro ζ hζ n ι' ι
    exact (hT ζ (hb₂ hζ) n).2.2.2.2.2.average ι' ι
  · rintro ζ hζ ⟨a', c⟩ ⟨a, b⟩ hn
    refine (hBonds c a').2 a b (fun hb => hn ?_) ζ (hb₁ hζ)
    refine (euclidNormVec_le_two_mul (r := 3 / 2) (by norm_num) fun μ => ?_).trans (by norm_num)
    show |(b.1.initial : InfiniteLattice.AmbientSpace) μ -
      (c.1.initial : InfiniteLattice.AmbientSpace) μ| ≤ 3 / 2
    have hc : |(c.1.terminal : InfiniteLattice.AmbientSpace) μ -
        (c.1.initial : InfiniteLattice.AmbientSpace) μ| ≤ 1 :=
      (link_abs_sub_le (a := Tower.meshAt L k k) (by rw [meshAt_self]; norm_num) c.1 μ).trans_eq
        meshAt_self
    rcases hb.2.1 with h | h
    · have := cubeOfOrder_abs_sub_le hL c.1.initial h μ
      linarith
    · have h₁ := abs_le.1 (cubeOfOrder_abs_sub_le hL c.1.terminal h μ)
      have h₂ := abs_le.1 hc
      exact abs_le.2 ⟨by linarith [h₁.1, h₂.1], by linarith [h₁.2, h₂.2]⟩
  · rintro ⟨a', c⟩ ι
    obtain ⟨l, e, h, hol, hh⟩ := holomorphicIn_superset hCharts.1 hHolo
      (hfin (c.1.initial : InfiniteLattice.AmbientSpace) 19)
      (hsub (Tower.FullSpace.IteratedKernelEntries.edgesNear L k c.1.initial 3) _ (fun b hb =>
        hnear _ 3 (by norm_num) le_rfl b.1 fun i => Or.inl (hb i).1))
      (min_le_left ρ₁ ρ₂) ((hBonds c a').1 ι)
    exact ⟨l, e, h, hol, hh⟩
  · intro ζ hζ n ι' ι
    exact (hT ζ (hb₂ hζ) n).2.2.2.2.2.covariantAverage ι' ι
end YangMills.Construction.Tower.FullSpace.LocalKernelFunctions
end
