import YangMills.Construction.Matrices.CalculusOfHolomorphicMapsProof
import YangMills.Construction.ComplexAnalysis.ConjugationAndInnerProducts
import YangMills.Construction.EuclideanFunctionals.VectorsOfPlatesAndTheProductFormula
import YangMills.Construction.ForwardTube.ArgumentsOfTheGramKernelInTheShiftedTubes
import YangMills.Construction.ForwardTube.ShiftedTubesInLightConeCoordinatesProof
import YangMills.Construction.RotationInvariance.OneFunctionOnAllTubesProof
import YangMills.Construction.RotationInvariance.ScalarProductsOfBumpVectorsAtComplexPoints
import Mathlib
set_option autoImplicit false
open YangMills.Construction.RealPlane YangMills.Construction.ForwardTube YangMills.Construction.Coordinates Set
open scoped InnerProductSpace ComplexConjugate
noncomputable section
namespace YangMills.Construction.EuclideanFunctionals.MollifierInnerAtComplexPoints
open YangMills.Construction.Matrices.GroupLieProduct.Subspaces.AnalyticCalculus (scalarEquiv)
theorem scalarEquiv_apply_eq (x : ℂ) (k : Fin 1) : scalarEquiv x k = x := by apply _root_.YangMills.DeltaSharedProofs.p23888 <;> assumption
theorem differentiable_pairTupleEquiv (p : ℕ) : Differentiable ℂ (pairTupleEquiv p) := by
  rw [differentiable_pi]
  intro l
  obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective l
  have h : ∀ c : Fin 2,
      Differentiable ℂ fun v : Fin p → ℂ × ℂ => pairTupleEquiv p v (finProdFinEquiv (i, c)) :=
    Fin.forall_fin_two.2
      ⟨by
        simp only [pairTupleEquiv_apply_fst]
        exact differentiable_fst.comp (differentiable_apply i),
       by
        simp only [pairTupleEquiv_apply_snd]
        exact differentiable_snd.comp (differentiable_apply i)⟩
  exact h c
theorem pairTupleEquiv_symm_apply (p : ℕ) (z : ComplexCoordinates (p * 2)) (i : Fin p) :
    (pairTupleEquiv p).symm z i =
      (z (finProdFinEquiv (i, 0)), z (finProdFinEquiv (i, 1))) := by
  have h₀ := pairTupleEquiv_apply_fst ((pairTupleEquiv p).symm z) i
  have h₁ := pairTupleEquiv_apply_snd ((pairTupleEquiv p).symm z) i
  rw [Equiv.apply_symm_apply] at h₀ h₁
  rw [h₀, h₁]
theorem differentiable_pairTupleEquiv_symm (p : ℕ) :
    Differentiable ℂ (pairTupleEquiv p).symm := by
  rw [differentiable_pi]
  intro i
  simp only [pairTupleEquiv_symm_apply]
  exact (differentiable_apply _).prodMk (differentiable_apply _)
theorem isOpen_pairTupleEquiv_image {p : ℕ} {D : Set (Fin p → ℂ × ℂ)} (hD : IsOpen D) :
    IsOpen (pairTupleEquiv p '' D) := by apply _root_.YangMills.Construction.EuclideanFunctionals.TubeUnionHarmonicsProof.isOpen_image_pairTupleEquiv <;> assumption
theorem isHolomorphicIn_of_differentiable {N N' : ℕ} {O : Set (ComplexCoordinates N)}
    (hO : IsOpen O) {f : ComplexCoordinates N → ComplexCoordinates N'} (hf : Differentiable ℂ f) :
    ComplexCoordinates.IsHolomorphicIn O f := ⟨hO, hf.continuous.continuousOn, fun a _ j => Filter.Eventually.of_forall fun t =>
      (hf.comp (by fun_prop :
        Differentiable ℂ fun t : ℂ => a + t • ComplexCoordinates.stdBasisVector j)) t⟩
theorem holomorphicOnTuples_sub {p : ℕ} {D : Set (Fin p → ℂ × ℂ)} {f g : (Fin p → ℂ × ℂ) → ℂ}
    (hf : HolomorphicOnTuples D f) (hg : HolomorphicOnTuples D g) :
    HolomorphicOnTuples D fun w => f w - g w := by apply _root_.YangMills.Construction.EuclideanFunctionals.UnionKernel.holomorphicOnTuples_sub <;> assumption
theorem holomorphicOnTuples_const {p : ℕ} {D : Set (Fin p → ℂ × ℂ)}
    (hD : IsOpen (pairTupleEquiv p '' D)) (c : ℂ) : HolomorphicOnTuples D fun _ => c :=
  isHolomorphicIn_of_differentiable hD (differentiable_const (scalarEquiv c))
theorem holomorphicOnTuples_comp (hHolo : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    {p q : ℕ} {D : Set (Fin p → ℂ × ℂ)} {T : Set (Fin q → ℂ × ℂ)}
    (hD : IsOpen (pairTupleEquiv p '' D)) {K : (Fin q → ℂ × ℂ) → ℂ}
    (hK : HolomorphicOnTuples T K) {F : (Fin p → ℂ × ℂ) → Fin q → ℂ × ℂ}
    (hF : Differentiable ℂ F) (hmaps : MapsTo F D T) :
    HolomorphicOnTuples D fun w => K (F w) := by
  have hg : ComplexCoordinates.IsHolomorphicIn (pairTupleEquiv p '' D)
      (pairTupleEquiv q ∘ F ∘ (pairTupleEquiv p).symm) :=
    isHolomorphicIn_of_differentiable hD
      ((differentiable_pairTupleEquiv q).comp
        (hF.comp (differentiable_pairTupleEquiv_symm p)))
  have hmaps' : MapsTo (pairTupleEquiv q ∘ F ∘ (pairTupleEquiv p).symm)
      (pairTupleEquiv p '' D) (pairTupleEquiv q '' T) := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨F w, hmaps hw, by simp⟩
  have hc := (((hHolo.1 (q * 2) _ hK.1).1 1 _ hK).2.2.2.1) (p * 2) _ _ hg hmaps'
  have heq : (scalarEquiv ∘ K ∘ (pairTupleEquiv q).symm) ∘
        (pairTupleEquiv q ∘ F ∘ (pairTupleEquiv p).symm) =
      scalarEquiv ∘ (fun w => K (F w)) ∘ (pairTupleEquiv p).symm := by
    funext z
    simp
  rw [heq] at hc
  exact hc
theorem pairTupleEquiv_conjTuple {p : ℕ} (x : Fin p → ℂ × ℂ) :
    pairTupleEquiv p (conjTuple x) =
      YangMills.Construction.BanachValued.ConjugationInner.conjPoint (pairTupleEquiv p x) := by
  funext l
  obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective l
  have h : ∀ c : Fin 2, pairTupleEquiv p (conjTuple x) (finProdFinEquiv (i, c)) =
      conj (pairTupleEquiv p x (finProdFinEquiv (i, c))) :=
    Fin.forall_fin_two.2
      ⟨by rw [pairTupleEquiv_apply_fst, pairTupleEquiv_apply_fst]; rfl,
       by rw [pairTupleEquiv_apply_snd, pairTupleEquiv_apply_snd]; rfl⟩
  exact h c
theorem conjTuple_conjTuple {p : ℕ} (x : Fin p → ℂ × ℂ) :
    conjTuple (conjTuple x) = x := by apply _root_.YangMills.Construction.ForwardTube.ShiftedTubeCoords.conjTuple_conjTuple <;> assumption
theorem conjTuple_realTuple {p : ℕ} (a : Fin p → RealPlane) :
    conjTuple (realTuple a) = realTuple a := by
  funext i
  simp [conjTuple, conjPair, realTuple, embedPlane]
theorem conjSet_pairTupleEquiv_image {p : ℕ} {D : Set (Fin p → ℂ × ℂ)}
    (hconj : conjTuple '' D = D) :
    YangMills.Construction.BanachValued.ConjugationInner.conjSet
      (pairTupleEquiv p '' D) = pairTupleEquiv p '' D := by
  have hmem : ∀ x, conjTuple x ∈ D ↔ x ∈ D := by
    intro x
    constructor
    · intro h
      rw [← hconj]
      exact ⟨_, h, conjTuple_conjTuple x⟩
    · intro h
      rw [← hconj] at h
      obtain ⟨w, hw, rfl⟩ := h
      rwa [conjTuple_conjTuple]
  ext z
  obtain ⟨x, rfl⟩ := (pairTupleEquiv p).surjective z
  simp only [YangMills.Construction.BanachValued.ConjugationInner.conjSet, mem_ofPred_eq,
    ← pairTupleEquiv_conjTuple, (pairTupleEquiv p).injective.mem_set_image, hmem]
theorem eq_zero_of_eq_zero_on_realTuples
    (hTubes : YangMills.Construction.ForwardTube.ShiftedTubeCoords.Holds)
    (hIdent : YangMills.Construction.ComplexAnalysis.IdentityTheoremOnRealLocus)
    {p : ℕ} (hp : 1 ≤ p) {η : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hconv : Convex ℝ (shiftedForwardTube p η)) {g : (Fin p → ℂ × ℂ) → ℂ}
    (hg : HolomorphicOnTuples (shiftedForwardTube p η) g)
    (h0 : ∀ a ∈ orderedTimeTuples p η, g (realTuple a) = 0) :
    ∀ x ∈ shiftedForwardTube p η, g x = 0 := by
  obtain ⟨-, -, hreal, hne, -⟩ := (hTubes 1 le_rfl η hη0 hη1).2.2.2 p hp
  set D := pairTupleEquiv p '' shiftedForwardTube p η with hDdef
  have hDopen : IsOpen D := hg.1
  have hmemReal : ∀ a ∈ orderedTimeTuples p η, realTuple a ∈ shiftedForwardTube p η := by
    intro a ha
    have : realTuple a ∈ YangMills.Construction.ForwardTube.realLocus (shiftedForwardTube p η) := by
      rw [hreal]
      exact ⟨a, ha, rfl⟩
    exact this.1
  obtain ⟨a₀, ha₀⟩ := hne
  have hDconn : IsConnected D := by
    refine ⟨⟨_, _, hmemReal a₀ ha₀, rfl⟩, ?_⟩
    exact hconv.isPreconnected.image _ (differentiable_pairTupleEquiv p).continuous.continuousOn
  have hholo : ComplexCoordinates.IsHolomorphicIn (N' := 1) D
      (fun z _ => g ((pairTupleEquiv p).symm z)) := by
    have heq : (fun (z : ComplexCoordinates (p * 2)) (_ : Fin 1) => g ((pairTupleEquiv p).symm z)) =
        scalarEquiv ∘ g ∘ (pairTupleEquiv p).symm := by
      funext z k
      simp [scalarEquiv_apply_eq]
    rw [heq]
    exact hg
  have hrealCoord : ∀ a : Fin p → RealPlane,
      pairTupleEquiv p (realTuple a) ∈ ComplexCoordinates.realLocus (p * 2) := by
    intro a l
    obtain ⟨⟨i, c⟩, rfl⟩ := finProdFinEquiv.surjective l
    have h : ∀ c : Fin 2,
        (pairTupleEquiv p (realTuple a) (finProdFinEquiv (i, c))).im = 0 :=
      Fin.forall_fin_two.2
        ⟨by rw [pairTupleEquiv_apply_fst]; simp [realTuple, embedPlane],
         by rw [pairTupleEquiv_apply_snd]; simp [realTuple, embedPlane]⟩
    exact h c
  have hvan : ∀ z ∈ D ∩ ComplexCoordinates.realLocus (p * 2),
      g ((pairTupleEquiv p).symm z) = 0 := by
    rintro _ ⟨⟨x, hx, rfl⟩, hz⟩
    rw [Equiv.symm_apply_apply]
    have hxreal : x ∈ YangMills.Construction.ForwardTube.realLocus (shiftedForwardTube p η) := by
      refine ⟨hx, fun i => !₂[(x i).1.re, (x i).2.re], fun i => ?_⟩
      have h₀ := hz (finProdFinEquiv (i, 0))
      have h₁ := hz (finProdFinEquiv (i, 1))
      rw [pairTupleEquiv_apply_fst] at h₀
      rw [pairTupleEquiv_apply_snd] at h₁
      refine Prod.ext (Complex.ext ?_ ?_) (Complex.ext ?_ ?_) <;> simp [embedPlane, h₀, h₁]
    rw [hreal] at hxreal
    obtain ⟨a, ha, rfl⟩ := hxreal
    exact h0 a ha
  intro x hx
  have := hIdent.1 (p * 2) (by omega) D (fun z => g ((pairTupleEquiv p).symm z)) hDopen hDconn
    hholo (D ∩ ComplexCoordinates.realLocus (p * 2))
    ⟨_, ⟨_, hmemReal a₀ ha₀, rfl⟩, hrealCoord a₀⟩ (fun z hz => hz)
    ⟨D, hDopen, rfl⟩ hvan (pairTupleEquiv p x) ⟨x, hx, rfl⟩
  simpa using this
theorem differentiable_gramKernelArgs_right {n n' : ℕ} (x : Fin n → ℂ × ℂ) :
    Differentiable ℂ fun y : Fin n' → ℂ × ℂ => gramKernelArgs x y := by
  rw [differentiable_pi]
  intro k
  unfold gramKernelArgs
  by_cases h : (k : ℕ) + 1 < n
  · simp only [dif_pos h]
    exact differentiable_const _
  · by_cases h' : (k : ℕ) + 1 = n
    · simp only [dif_neg h, dif_pos h']
      exact (differentiable_const _).add (differentiable_apply _)
    · simp only [dif_neg h, dif_neg h']
      exact (differentiable_apply _).sub (differentiable_apply _)
theorem differentiable_gramKernelArgs_conj_left {n n' : ℕ} (y : Fin n' → ℂ × ℂ) :
    Differentiable ℂ fun x : Fin n → ℂ × ℂ => gramKernelArgs (conjTuple x) y := by
  have hstar : ∀ i : Fin n, Differentiable ℂ fun x : Fin n → ℂ × ℂ =>
      tubeStar (conjPair (x i)) := by
    intro i
    have heq : (fun x : Fin n → ℂ × ℂ => tubeStar (conjPair (x i))) =
        fun x => ((x i).1, -(x i).2) := by
      funext x
      simp [tubeStar, conjPair]
    rw [heq]
    exact (differentiable_fst.comp (differentiable_apply i)).prodMk
      (differentiable_snd.comp (differentiable_apply i)).neg
  rw [differentiable_pi]
  intro k
  unfold gramKernelArgs
  by_cases h : (k : ℕ) + 1 < n
  · simp only [dif_pos h]
    have heq : (fun x : Fin n → ℂ × ℂ => tubeStar (conjTuple x ⟨n - 1 - k, by omega⟩ -
          conjTuple x ⟨n - 2 - k, by omega⟩)) =
        fun x => tubeStar (conjPair (x ⟨n - 1 - k, by omega⟩)) -
          tubeStar (conjPair (x ⟨n - 2 - k, by omega⟩)) := by
      funext x
      simp [tubeStar, conjPair, conjTuple]
      ring_nf
    rw [heq]
    exact (hstar _).sub (hstar _)
  · by_cases h' : (k : ℕ) + 1 = n
    · simp only [dif_neg h, dif_pos h']
      exact (hstar _).add (differentiable_const _)
    · simp only [dif_neg h, dif_neg h']
      exact differentiable_const _
section Setting
variable {m : SharpScale} {S : ConnFamily} (d : PlaneDataWithAperture m S)
def labelConstExt (ψ : RealPlane → ℝ) : ℝ :=
  open Classical in if hψ : ψ ∈ realLabels then d.base.labelConst ⟨ψ, hψ⟩ else 0
theorem productBoundWith_labelConstExt (ψ : RealPlane → ℝ) (hψ : ψ ∈ realLabels) :
    ProductBoundWith d.base.sigma d.base.expo_pos d.base.frac_mem ψ
      (labelConstExt d ψ) := by
  simp only [labelConstExt, dif_pos hψ]
  exact d.base.boundWith_labelConst ⟨ψ, hψ⟩
variable {d}
theorem vectorBounds_mollifier (hProd : PlateVectorsProduct.Holds) {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) {δ : ℕ+ → RealPlane → ℝ}
    (hδ : d.IsRadialMollifier η δ) (j : ℕ+) {n : ℕ} (φ : Fin n → realLabels) :
    PlateVectorsProduct.VectorBounds d.base.sigma d.base.expo η
      (labelConstExt d) (fun _ : Fin n => ofRealFun (δ j))
      (fun i => (φ i : RealPlane → ℝ)) :=
  (hProd m S d.base.sigma d.base.expo d.base.frac
    d.base.expo_pos d.base.frac_mem (labelConstExt d)
    d.base.productBoundWithExponent (productBoundWith_labelConstExt d) d.base.cone η hη0 hη1).1 n
    _ _ fun a => ⟨(φ a).2, (hδ.ofRealFun_mem hη0 j).1, (hδ.ofRealFun_mem hη0 j).2⟩
theorem mollifiedKernel_holomorphic (hProd : PlateVectorsProduct.Holds) {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) {δ : ℕ+ → RealPlane → ℝ}
    (hδ : d.IsRadialMollifier η δ) (j : ℕ+) {q : ℕ}
    (φ : Fin (q + 1) → RealPlane → ℝ) (hφ : ∀ k, φ k ∈ realLabels) :
    HolomorphicOnTuples (shiftedForwardTubePow q η) (d.mollifiedKernel η δ φ j) :=
  ((hProd m S d.base.sigma d.base.expo d.base.frac
    d.base.expo_pos d.base.frac_mem (labelConstExt d)
    d.base.productBoundWithExponent (productBoundWith_labelConstExt d) d.base.cone η hη0
    hη1).2 q _ φ fun a => ⟨hφ a, (hδ.ofRealFun_mem hη0 j).1, (hδ.ofRealFun_mem hη0 j).2⟩).1
theorem mollifierGramValue_holomorphic
    (hHolo : ComplexCoordinates.PowerSeriesHolomorphy.Properties)
    (hArgs : YangMills.Construction.ForwardTube.GramArgsInShiftedTubes.Holds)
    (hProd : PlateVectorsProduct.Holds) {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) {δ : ℕ+ → RealPlane → ℝ}
    (hδ : d.IsRadialMollifier η δ) (j : ℕ+) {n n' : ℕ} (φ : Fin n → realLabels)
    (φ' : Fin n' → realLabels) {p : ℕ} {D : Set (Fin p → ℂ × ℂ)}
    (hD : IsOpen (pairTupleEquiv p '' D)) {X : (Fin p → ℂ × ℂ) → Fin n → ℂ × ℂ}
    {Y : (Fin p → ℂ × ℂ) → Fin n' → ℂ × ℂ}
    (hdiff : Differentiable ℂ fun w => gramKernelArgs (X w) (Y w))
    (hX : MapsTo X D (shiftedForwardTube n η)) (hY : MapsTo Y D (shiftedForwardTube n' η)) :
    HolomorphicOnTuples D fun w => d.mollifierGramValue η δ j φ φ' (X w) (Y w) := by
  by_cases h : 2 ≤ n + n'
  · simp only [PlaneDataWithAperture.mollifierGramValue, dif_pos h]
    refine holomorphicOnTuples_comp hHolo hD
      (mollifiedKernel_holomorphic hProd hη0 hη1 hδ j _ fun k => Subtype.property _) hdiff ?_
    intro w hw
    exact hArgs n n' η hη0 hη1 h _ (hX hw) _ (hY hw)
  · simp only [PlaneDataWithAperture.mollifierGramValue, dif_neg h]
    exact holomorphicOnTuples_const hD _
end Setting
theorem holomorphicOnTuples_inner_right
    (hNotions : YangMills.Construction.BanachValued.ConjugationInner.Properties) {p : ℕ}
    (hp : 1 ≤ p) {D : Set (Fin p → ℂ × ℂ)} {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {Φ : (Fin p → ℂ × ℂ) → K}
    (hΦ : HolomorphicVectorOnTuples D Φ) (ψ : K) :
    HolomorphicOnTuples D fun w => inner ℂ ψ (Φ w) :=
  ((hNotions (p * 2) (by omega) _ hΦ.1).2.2 K (Φ ∘ (pairTupleEquiv p).symm) ψ hΦ).1
theorem holomorphicOnTuples_inner_conj_left
    (hNotions : YangMills.Construction.BanachValued.ConjugationInner.Properties) {p : ℕ}
    (hp : 1 ≤ p) {D : Set (Fin p → ℂ × ℂ)} (hconj : conjTuple '' D = D)
    {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] {Φ : (Fin p → ℂ × ℂ) → K}
    (hΦ : HolomorphicVectorOnTuples D Φ) (ψ : K) :
    HolomorphicOnTuples D fun w => inner ℂ (Φ (conjTuple w)) ψ := by
  have h := ((hNotions (p * 2) (by omega) _ hΦ.1).2.2 K (Φ ∘ (pairTupleEquiv p).symm) ψ hΦ).2
  rw [conjSet_pairTupleEquiv_image hconj] at h
  have heq : ∀ z : ComplexCoordinates (p * 2), (pairTupleEquiv p).symm
      (YangMills.Construction.BanachValued.ConjugationInner.conjPoint z) =
        conjTuple ((pairTupleEquiv p).symm z) := by
    intro z
    rw [Equiv.symm_apply_eq, pairTupleEquiv_conjTuple, Equiv.apply_symm_apply]
  simp only [Function.comp_apply, heq] at h
  exact h
theorem realTuple_mem_shiftedForwardTube
    (hTubes : YangMills.Construction.ForwardTube.ShiftedTubeCoords.Holds) {p : ℕ} {η : ℝ}
    (hη0 : 0 < η) (hη1 : η ≤ 1) {a : Fin p → RealPlane} (ha : a ∈ orderedTimeTuples p η) :
    realTuple a ∈ shiftedForwardTube p η := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · show realTuple a ∈ shiftedTuples forwardTube 0 η
    rw [shiftedTuples_zero forwardTube η (realTuple a)]
    rfl
  · have hreal := ((hTubes 1 le_rfl η hη0 hη1).2.2.2 p hp).2.2.1
    have : realTuple a ∈ YangMills.Construction.ForwardTube.realLocus (shiftedForwardTube p η) := by
      rw [hreal]
      exact ⟨a, ha, rfl⟩
    exact this.1
theorem exists_realTuple_eq_of_zero (η : ℝ) (x : Fin 0 → ℂ × ℂ) :
    ∃ a ∈ orderedTimeTuples 0 η, realTuple a = x :=
  ⟨fun i => i.elim0, ⟨fun h => absurd h (lt_irrefl 0), fun i h => absurd h (by omega)⟩,
    Subsingleton.elim _ _⟩
theorem holds (hReal : MollifierInnerAtRealPoints.Holds)
    (hArgs : YangMills.Construction.ForwardTube.GramArgsInShiftedTubes.Holds)
    (hProd : PlateVectorsProduct.Holds)
    (hTubes : YangMills.Construction.ForwardTube.ShiftedTubeCoords.Holds)
    (hNotions : YangMills.Construction.BanachValued.ConjugationInner.Properties)
    (hIdent : YangMills.Construction.ComplexAnalysis.IdentityTheoremOnRealLocus)
    (hHolo : ComplexCoordinates.PowerSeriesHolomorphy.Properties) : Holds := by
  intro m S d η hη δ hδ j n n' φ φ'
  obtain ⟨hη0, hη1⟩ := hη
  have hV := vectorBounds_mollifier hProd hη0 hη1 hδ j φ
  have hV' := vectorBounds_mollifier hProd hη0 hη1 hδ j φ'
  have hopen : IsOpen (pairTupleEquiv n '' shiftedForwardTube n η) :=
    isOpen_pairTupleEquiv_image hV.2.1
  have hopen' : IsOpen (pairTupleEquiv n' '' shiftedForwardTube n' η) :=
    isOpen_pairTupleEquiv_image hV'.2.1
  have hstep : ∀ a ∈ orderedTimeTuples n η, ∀ y ∈ shiftedForwardTube n' η,
      ⟪d.mollifierVector η δ j φ (realTuple a), d.mollifierVector η δ j φ' y⟫_ℂ -
        d.mollifierGramValue η δ j φ φ' (realTuple a) y = 0 := by
    intro a ha y hy
    have hreal : ∀ b ∈ orderedTimeTuples n' η,
        ⟪d.mollifierVector η δ j φ (realTuple a), d.mollifierVector η δ j φ' (realTuple b)⟫_ℂ -
          d.mollifierGramValue η δ j φ φ' (realTuple a) (realTuple b) = 0 := fun b hb =>
      sub_eq_zero.2 (hReal m S d η ⟨hη0, hη1⟩ δ hδ j n n' φ φ' a ha b hb)
    rcases Nat.eq_zero_or_pos n' with rfl | hn'
    · obtain ⟨b, hb, rfl⟩ := exists_realTuple_eq_of_zero η y
      exact hreal b hb
    · refine eq_zero_of_eq_zero_on_realTuples hTubes hIdent hn' hη0 hη1 hV'.2.2.1
        (g := fun y => ⟪d.mollifierVector η δ j φ (realTuple a), d.mollifierVector η δ j φ' y⟫_ℂ -
          d.mollifierGramValue η δ j φ φ' (realTuple a) y) ?_ hreal y hy
      refine holomorphicOnTuples_sub (holomorphicOnTuples_inner_right hNotions hn' hV'.2.2.2.1 _) ?_
      exact mollifierGramValue_holomorphic hHolo hArgs hProd hη0 hη1 hδ j φ φ' hopen'
        (X := fun _ => realTuple a) (Y := id) (differentiable_gramKernelArgs_right _)
        (fun _ _ => realTuple_mem_shiftedForwardTube hTubes hη0 hη1 ha) (fun _ h => h)
  intro x hx y hy
  rw [← sub_eq_zero]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · obtain ⟨a, ha, rfl⟩ := exists_realTuple_eq_of_zero η x
    exact hstep a ha y hy
  · have hconj := ((hTubes 1 le_rfl η hη0 hη1).2.2.2 n hn).2.1
    have hconjMaps : MapsTo conjTuple (shiftedForwardTube n η) (shiftedForwardTube n η) := by
      intro w hw
      rw [← hconj]
      exact ⟨w, hw, rfl⟩
    have hzero := eq_zero_of_eq_zero_on_realTuples hTubes hIdent hn hη0 hη1 hV.2.2.1
      (g := fun x => ⟪d.mollifierVector η δ j φ (conjTuple x), d.mollifierVector η δ j φ' y⟫_ℂ -
        d.mollifierGramValue η δ j φ φ' (conjTuple x) y)
      (holomorphicOnTuples_sub (holomorphicOnTuples_inner_conj_left hNotions hn hconj hV.2.2.2.1 _)
        (mollifierGramValue_holomorphic hHolo hArgs hProd hη0 hη1 hδ j φ φ' hopen
          (X := conjTuple) (Y := fun _ => y) (differentiable_gramKernelArgs_conj_left _)
          hconjMaps (fun _ _ => hy)))
      (fun a ha => by
        simp only [conjTuple_realTuple]
        exact hstep a ha y hy)
      (conjTuple x) (hconjMaps hx)
    simpa only [conjTuple_conjTuple] using hzero
end YangMills.Construction.EuclideanFunctionals.MollifierInnerAtComplexPoints
end
