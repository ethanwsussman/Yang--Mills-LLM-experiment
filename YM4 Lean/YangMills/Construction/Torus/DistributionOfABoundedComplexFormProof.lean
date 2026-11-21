import YangMills.Construction.Torus.CutOffsEqualToOneOnProjections
import YangMills.Construction.Torus.DistributionOfABoundedComplexForm
import YangMills.Construction.Torus.FormOfACutOffAtTensors
import YangMills.Construction.Torus.FormOfACutOffDoesNotDependOnTheCutOff
import YangMills.Construction.Torus.FormOfACutOffIsABoundedLinearForm
import YangMills.Construction.Torus.GradientNormLipschitzConstantAndSharpNorm
import YangMills.Construction.Torus.GradientNormOfACutOffTimesAMode
import YangMills.Construction.Torus.PartialSumsInsideACutOffConverge
import YangMills.Construction.Torus.RestrictionsSumsProductsAndTensorsOfTestFunctions
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.AmbientPoints.BoundedComplexFormDistributionProof
variable {s : Conventions.StandingParameters} {n : ℕ}
theorem subset_fundamentalBox {ρ : ℝ} {O : Fin n → Set (Pt s .euclidean)}
    (hO : IsOpenTupleInBall ρ O) (i : Fin n) : O i ⊆ Torus.FourierBox.fundamentalBox s (4 * ρ) := by
  intro u hu μ
  have hb : TorusMetric.euclidNormVec u ≤ ρ := (hO.2.2 i).2 hu
  have hc : |Torus.FourierBox.coord s μ u| ≤ TorusMetric.euclidNormVec u := by
    refine Real.abs_le_sqrt ?_
    exact Finset.single_le_sum (f := fun ν => (Torus.FourierBox.coord s ν u) ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
  have hρ := hO.2.1
  have hab := abs_le.mp (hc.trans hb)
  constructor <;> linarith [hab.1, hab.2]
theorem isOpen_singletonTuples {A : Set (Pt s .euclidean)} (hA : IsOpen A) :
    IsOpen (singletonTuples A) :=
  hA.preimage (continuous_apply (0 : Fin 1))
theorem form_eq_zero_of_finset_sum {p : ℕ} {Ω : Set (Tuple s .euclidean p)} {ι : Type*}
    (hcomb : LinearCombFacts Ω) {D : testFns Ω → ℂ} (hD : IsComplexLinearForm D)
    (F₀ : testFns Ω) (S : Finset ι) (c : ι → ℂ) (G : ι → Tuple s .euclidean p → ℂ)
    (hG : ∀ k, G k ∈ testFns Ω) (h0 : ∀ k, D ⟨G k, hG k⟩ = 0) :
    ∃ h : (fun y => ∑ k ∈ S, c k * G k y) ∈ testFns Ω, D ⟨_, h⟩ = 0 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have he : (fun _ : Tuple s .euclidean p => (0 : ℂ)) = (0 : ℂ) • F₀.1 + (0 : ℂ) • F₀.1 := by
      funext y
      simp
    have hm : (fun y => ∑ k ∈ (∅ : Finset ι), c k * G k y) ∈ testFns Ω := by
      simp only [Finset.sum_empty]
      rw [he]
      exact (hcomb F₀.1 F₀.2 F₀.1 F₀.2 0 0).1
    refine ⟨hm, ?_⟩
    have := hD.2 0 F₀ ⟨_, hm⟩ (by funext y; simp)
    simpa using this
  | insert a S ha ih =>
    obtain ⟨hm, hz⟩ := ih
    have hsm : c a • G a ∈ testFns Ω := by
      simpa using (hcomb _ (hG a) _ (hG a) (c a) 0).1
    have hza : D ⟨_, hsm⟩ = 0 := by
      rw [hD.2 (c a) ⟨_, hG a⟩ ⟨_, hsm⟩ rfl, h0 a, mul_zero]
    have he : (fun y => ∑ k ∈ insert a S, c k * G k y) =
        (1 : ℂ) • (c a • G a) + (1 : ℂ) • fun y => ∑ k ∈ S, c k * G k y := by
      funext y
      simp [Finset.sum_insert ha]
    have hm' : (fun y => ∑ k ∈ insert a S, c k * G k y) ∈ testFns Ω := by
      rw [he]
      exact (hcomb _ hsm _ hm 1 1).1
    refine ⟨hm', ?_⟩
    rw [hD.1 ⟨_, hsm⟩ ⟨_, hm⟩ ⟨_, hm'⟩ (by funext y; simp [Finset.sum_insert ha]), hza, hz, add_zero]
theorem tensorProd_update (h : Fin n → Pt s .euclidean → ℂ) (j : Fin n)
    (g : Pt s .euclidean → ℂ) (x : Tuple s .euclidean n) :
    tensorProd (Function.update h j g) x = g (x j) * ∏ i ∈ Finset.univ.erase j, h i (x i) := by
  unfold tensorProd
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
theorem form_eq_zero_of_complex_tensors
    (hR : TestFnOperations)
    {ρ : ℝ} {O : Fin n → Set (Pt s .euclidean)} (hO : IsOpenTupleInBall ρ O)
    {D : testFns (boxSet O) → ℂ} (hD : IsComplexLinearForm D)
    (hzero : ∀ φ : Fin n → Pt s .euclidean → ℝ,
      (∀ i, asFunctionOnOnePoint (φ i) ∈ testFns (singletonTuples (O i))) →
      ∀ hF : tensorProd (fun i y => (φ i y : ℂ)) ∈ testFns (boxSet O), D ⟨_, hF⟩ = 0)
    (S : Finset (Fin n)) :
    ∀ h : Fin n → Pt s .euclidean → ℂ,
      (∀ i, ofSinglePoint (h i) ∈ testFns (singletonTuples (O i))) →
      (∀ i, i ∉ S → ∀ y, (h i y).im = 0) →
      ∀ hF : tensorProd h ∈ testFns (boxSet O), D ⟨_, hF⟩ = 0 := by
  classical
  have hopen : IsOpen (boxSet O) :=
    isOpen_set_pi Set.finite_univ fun i _ => (hO.2.2 i).1
  obtain ⟨-, hΩ, -, htens⟩ := hR s .euclidean n hO.1
  obtain ⟨-, hcomb, -, -⟩ := hΩ _ hopen
  obtain ⟨-, hΩ₁, -, -⟩ := hR s .euclidean 1 le_rfl
  induction S using Finset.induction_on with
  | empty =>
    intro h hh him hF
    have heq : (fun i y => (((h i y).re : ℝ) : ℂ)) = h := by
      funext i y
      exact Complex.ext rfl (by simp [him i (Finset.notMem_empty i) y])
    have hφ : ∀ i, asFunctionOnOnePoint (fun y => (h i y).re) ∈ testFns (singletonTuples (O i)) := by
      intro i
      have he : asFunctionOnOnePoint (fun y => (h i y).re) = ofSinglePoint (h i) := by
        funext y
        exact congrFun (congrFun heq i) (y 0)
      rw [he]
      exact hh i
    have hF' : tensorProd (fun i y => (((h i y).re : ℝ) : ℂ)) ∈ testFns (boxSet O) := by
      rw [heq]
      exact hF
    have e : (⟨tensorProd h, hF⟩ : testFns (boxSet O)) = ⟨_, hF'⟩ :=
      Subtype.ext (by simp only [heq])
    rw [e]
    exact hzero (fun i y => (h i y).re) hφ hF'
  | insert j S hj ih =>
    intro h hh him hF
    have hopen₁ : IsOpen (singletonTuples (O j)) := isOpen_singletonTuples (hO.2.2 j).1
    obtain ⟨-, -, hparts, -⟩ := hΩ₁ _ hopen₁
    have hre := (hparts _ (hh j)).1.1
    have him' := (hparts _ (hh j)).2.1.1
    let a : Pt s .euclidean → ℂ := fun y => ((h j y).re : ℂ)
    let b : Pt s .euclidean → ℂ := fun y => ((h j y).im : ℂ)
    have ha : ofSinglePoint a ∈ testFns (singletonTuples (O j)) := hre
    have hb : ofSinglePoint b ∈ testFns (singletonTuples (O j)) := him'
    have hh₁ : ∀ g : Pt s .euclidean → ℂ,
        ofSinglePoint g ∈ testFns (singletonTuples (O j)) →
        ∀ i, ofSinglePoint (Function.update h j g i) ∈ testFns (singletonTuples (O i)) := by
      intro g hg i
      by_cases hij : i = j
      · subst hij
        simpa using hg
      · rw [Function.update_of_ne hij]
        exact hh i
    have him₁ : ∀ g : Pt s .euclidean → ℂ, (∀ y, (g y).im = 0) →
        ∀ i, i ∉ S → ∀ y, (Function.update h j g i y).im = 0 := by
      intro g hg i hi y
      by_cases hij : i = j
      · subst hij
        simpa using hg y
      · rw [Function.update_of_ne hij]
        exact him i (by simp [hij, hi]) y
    have hT : ∀ g : Pt s .euclidean → ℂ,
        ofSinglePoint g ∈ testFns (singletonTuples (O j)) →
        tensorProd (Function.update h j g) ∈ testFns (boxSet O) := fun g hg =>
      (htens O _ (fun i => (hO.2.2 i).1) (hh₁ g hg)).1
    have hza := ih _ (hh₁ a ha) (him₁ a fun y => by simp [a]) (hT a ha)
    have hzb := ih _ (hh₁ b hb) (him₁ b fun y => by simp [b]) (hT b hb)
    have hsm : Complex.I • tensorProd (Function.update h j b) ∈ testFns (boxSet O) := by
      simpa using (hcomb _ (hT b hb) _ (hT b hb) Complex.I 0).1
    have hzi : D ⟨_, hsm⟩ = 0 := by
      rw [hD.2 Complex.I ⟨_, hT b hb⟩ ⟨_, hsm⟩ rfl, hzb, mul_zero]
    have hsum : tensorProd h = tensorProd (Function.update h j a) +
        Complex.I • tensorProd (Function.update h j b) := by
      funext x
      have hx : tensorProd h x = h j (x j) * ∏ i ∈ Finset.univ.erase j, h i (x i) := by
        have := tensorProd_update h j (h j) x
        rwa [Function.update_eq_self] at this
      have hab : h j (x j) = a (x j) + Complex.I * b (x j) := by
        simp only [a, b]
        rw [mul_comm]
        exact (Complex.re_add_im _).symm
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hx, tensorProd_update, tensorProd_update, hab]
      ring
    rw [hD.1 ⟨_, hT a ha⟩ ⟨_, hsm⟩ ⟨_, hF⟩ hsum, hza, hzi, add_zero]
theorem boundedComplexFormDistribution_holds (hB : CutoffSeriesBoundedLinear)
    (hT : CutoffSeriesAtTensors)
    (hC : CutoffsEqualOneOnProjections)
    (hP : CutoffPartialSumsTendsto)
    (hI : CutoffSeriesIndepOfCutoff)
    (hR : TestFnOperations)
    (hS : GradientC1Bounds.Statement)
    (hM : CutoffTimesModeGradNorm) : BoundedComplexFormDistribution := by
  intro s n ρ C O B hO hC0 hlin hbd
  have hn := hO.1
  have hopen : IsOpen (boxSet O) :=
    isOpen_set_pi Set.finite_univ fun i _ => (hO.2.2 i).1
  obtain ⟨-, hΩ, -, htens⟩ := hR s .euclidean n hn
  obtain ⟨hcont, hcomb, -, -⟩ := hΩ _ hopen
  have hbox : boxSet O ⊆ Torus.FourierBox.fundamentalBoxPow s n (4 * ρ) := fun y hy i =>
    subset_fundamentalBox hO i (hy i (Set.mem_univ i))
  have hsub : testFns (boxSet O) ⊆ testFns (Torus.FourierBox.fundamentalBoxPow s n (4 * ρ)) :=
    testFns_mono hbox
  have hcut := (hC s n ρ O hO).1
  have hfor : ∀ (K : Set (Tuple s .euclidean n)) (χ : Fin n → Pt s .euclidean → ℝ),
      IsCutoff O χ → (∀ i, ∀ y ∈ factorProjection i K, χ i y = 1) →
      ∀ F : testFns (boxSet O), closedSupport F.1 ⊆ K → IsCutoffFor χ F := by
    intro K χ hχ h1 F hF
    refine (hC s n ρ O hO).2 F χ hχ fun i y hy => h1 i y ?_
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hF hz, rfl⟩
  have hex : ∀ F : testFns (boxSet O), ∃ χ, IsCutoffFor χ F := by
    intro F
    obtain ⟨χ, hχ, h1⟩ := hcut (closedSupport F.1) F.2.2.1 F.2.2.2
    exact ⟨χ, hfor _ χ hχ h1 F subset_rfl⟩
  let T : testFns (boxSet O) → ℂ := fun F =>
    cutoffSeries (4 * ρ) B (hex F).choose F.1
  have hTχ : ∀ (F : testFns (boxSet O)) (χ : Fin n → Pt s .euclidean → ℝ),
      IsCutoffFor χ F → T F = cutoffSeries (4 * ρ) B χ F.1 := fun F χ h =>
    hI s n ρ C O B hO hC0 hlin hbd F _ χ (hex F).choose_spec h
  have hTlin : IsComplexLinearForm T := by
    constructor
    · intro F G H hH
      obtain ⟨χ, hχ, h1⟩ := hcut (closedSupport F.1 ∪ closedSupport G.1) (F.2.2.1.union G.2.2.1)
        (Set.union_subset F.2.2.2 G.2.2.2)
      have hHs : closedSupport H.1 ⊆ closedSupport F.1 ∪ closedSupport G.1 := by
        have := (hcomb F.1 F.2 G.1 G.2 1 1).2
        simpa [hH] using this
      rw [hTχ H χ (hfor _ χ hχ h1 H hHs), hTχ F χ (hfor _ χ hχ h1 F Set.subset_union_left),
        hTχ G χ (hfor _ χ hχ h1 G Set.subset_union_right)]
      exact (hB s n ρ C O B χ hO hC0 hbd hχ).2.1 ⟨F.1, hsub F.2⟩ ⟨G.1, hsub G.2⟩
        ⟨H.1, hsub H.2⟩ hH
    · intro c F H hH
      obtain ⟨χ, hχ, h1⟩ := hcut (closedSupport F.1) F.2.2.1 F.2.2.2
      have hHs : closedSupport H.1 ⊆ closedSupport F.1 := by
        have := (hcomb F.1 F.2 F.1 F.2 c 0).2
        simpa [hH] using this
      rw [hTχ H χ (hfor _ χ hχ h1 H hHs), hTχ F χ (hfor _ χ hχ h1 F subset_rfl)]
      exact (hB s n ρ C O B χ hO hC0 hbd hχ).2.2 c ⟨F.1, hsub F.2⟩ ⟨H.1, hsub H.2⟩ hH
  have hfin : ∀ χ : Fin n → Pt s .euclidean → ℝ, IsCutoff O χ →
      (∏ i, c1GradNorm fun x => (χ i x : ℂ)) ≠ ⊤ := by
    intro χ hχ
    refine (ENNReal.prod_lt_top fun i _ => ?_).ne
    have h := hχ i
    exact ((hS s .euclidean).2 ⟨1, Set.mem_Ici.2 le_rfl⟩ (χ i)
      ⟨h.1.1, fun m _ => h.1.2 m le_top⟩ h.2.1).1
  have hbd₂ : ∀ (F : testFns (boxSet O)) (χ : Fin n → Pt s .euclidean → ℝ),
      IsCutoffFor χ F → ENNReal.ofReal ‖T F‖ ≤
        ENNReal.ofReal (C * bumpNumber n ρ) *
          (∏ i, c1GradNorm fun x => (χ i x : ℂ)) * cnNorm (5 * n + 1) F.1 := by
    intro F χ h
    rw [hTχ F χ h]
    exact ((hB s n ρ C O B χ hO hC0 hbd h.1).1 F.1 (hsub F.2)).2
  have hord : ∀ K, IsCompact K → K ⊆ boxSet O → OrderBoundsOn T K (5 * n + 1) := by
    intro K hK hKO
    obtain ⟨χ, hχ, h1⟩ := hcut K hK hKO
    refine ⟨(ENNReal.ofReal (C * bumpNumber n ρ) *
      ∏ i, c1GradNorm fun x => (χ i x : ℂ)).toNNReal, fun F hF => ?_⟩
    rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hfin χ hχ))]
    exact hbd₂ F χ (hfor K χ hχ h1 F hF)
  have hdist : IsDistrib T := ⟨hTlin, fun K hK hKO => ⟨_, hord K hK hKO⟩⟩
  have hvals : AgreesWithFormOnRealTensors B T := by
    intro φ hφ
    have hF : tensorProd (fun i y => (φ i y : ℂ)) ∈ testFns (boxSet O) :=
      (htens O (fun i y => (φ i y : ℂ)) (fun i => (hO.2.2 i).1) hφ).1
    refine ⟨hF, ?_⟩
    have hχ₁ : ∀ i, ∃ c : Pt s .euclidean → ℝ,
        asFunctionOnOnePoint c ∈ testFns (singletonTuples (O i)) ∧ ∀ y, φ i y ≠ 0 → c y = 1 := by
      intro i
      have hO₁ : IsOpenTupleInBall ρ (fun _ : Fin 1 => O i) :=
        ⟨le_rfl, hO.2.1, fun _ => hO.2.2 i⟩
      have hK : closedSupport (asFunctionOnOnePoint (φ i)) ⊆ boxSet fun _ : Fin 1 => O i := by
        intro y hy j _
        obtain rfl : j = 0 := Subsingleton.elim _ _
        exact (hφ i).2.2 hy
      obtain ⟨χ, hχ, h1⟩ := (hC s 1 ρ _ hO₁).1 _ (hφ i).2.1 hK
      refine ⟨χ 0, hχ 0, fun y hy => h1 0 y ⟨fun _ => y, subset_closure ?_, rfl⟩⟩
      simpa [asFunctionOnOnePoint] using hy
    choose χ hχ hχ1 using hχ₁
    have hmul : ∀ i y, (χ i y : ℂ) * (φ i y : ℂ) = (φ i y : ℂ) := by
      intro i y
      by_cases h : φ i y = 0
      · simp [h]
      · simp [hχ1 i y h]
    have hfor' : IsCutoffFor χ ⟨_, hF⟩ := by
      refine ⟨hχ, ?_⟩
      funext y
      simp only [cutoffTensor, tensorProd, Pi.mul_apply]
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => hmul i (y i)
    rw [hTχ _ χ hfor']
    have hQ : ∀ i, singletonTuples (O i) ⊆ Torus.FourierBox.fundamentalBoxPow s 1 (4 * ρ) := by
      intro i y hy j
      obtain rfl : j = 0 := Subsingleton.elim _ _
      exact subset_fundamentalBox hO i hy
    have hval := hT s n ρ C O B χ hO hC0 hlin hbd hχ (fun i y => (φ i y : ℂ))
      (fun i => testFns_mono (hQ i) (hφ i))
    refine hval.trans ?_
    congr 1
    funext i x
    exact hmul i x
  refine ⟨T, ⟨hdist, hord⟩, hvals, fun F χ h => ⟨hTχ F χ h, hbd₂ F χ h⟩, ?_⟩
  intro T' hT' hval'
  funext F
  let Dd : testFns (boxSet O) → ℂ := fun G => T G - T' G
  have hDlin : IsComplexLinearForm Dd := by
    constructor
    · intro F G H h
      simp only [Dd]
      rw [hTlin.1 F G H h, hT'.1.1 F G H h]
      ring
    · intro c F H h
      simp only [Dd]
      rw [hTlin.2 c F H h, hT'.1.2 c F H h]
      ring
  have hzero : ∀ φ : Fin n → Pt s .euclidean → ℝ,
      (∀ i, asFunctionOnOnePoint (φ i) ∈ testFns (singletonTuples (O i))) →
      ∀ hF : tensorProd (fun i y => (φ i y : ℂ)) ∈ testFns (boxSet O),
        Dd ⟨_, hF⟩ = 0 := by
    intro φ hφ hF
    obtain ⟨h1, e1⟩ := hvals φ hφ
    obtain ⟨h2, e2⟩ := hval' φ hφ
    change T ⟨_, h1⟩ - T' ⟨_, h2⟩ = 0
    rw [e1, e2, sub_self]
  obtain ⟨χ, hχ⟩ := hex F
  have hconv := hP s n ρ O hO F χ hχ
  have htest : ∀ k : Fin (4 * n) → ℤ, ∀ i,
      ofSinglePoint (cutoffModeTuple (4 * ρ) χ k i) ∈ testFns (singletonTuples (O i)) :=
    fun k i => (hM s ρ hO.2.1 (O i) (χ i) (Torus.FourierBox.blockOf k i) (hO.2.2 i).1 (hχ.1 i)).1
  have hmem : ∀ k : Fin (4 * n) → ℤ,
      tensorProd (cutoffModeTuple (4 * ρ) χ k) ∈ testFns (boxSet O) := fun k =>
    (htens O _ (fun i => (hO.2.2 i).1) (htest k)).1
  have hmodes : ∀ k : Fin (4 * n) → ℤ, Dd ⟨_, hmem k⟩ = 0 := fun k =>
    form_eq_zero_of_complex_tensors hR hO hDlin hzero Finset.univ _ (htest k)
      (fun i hi => absurd (Finset.mem_univ i) hi) (hmem k)
  have hFs : ∀ t, T ⟨_, hconv.1 t⟩ = T' ⟨_, hconv.1 t⟩ := by
    intro t
    obtain ⟨hm, hz⟩ := form_eq_zero_of_finset_sum hcomb hDlin F
      (Torus.FourierBox.modesWithin (t : ℕ))
      (Torus.FourierBox.fourierCoeff (4 * ρ) F.1)
      (fun k => tensorProd (cutoffModeTuple (4 * ρ) χ k)) hmem hmodes
    exact sub_eq_zero.mp hz
  have l1 := hcont T hdist _ _ hconv
  have l2 := hcont T' hT' _ _ hconv
  have l3 : Filter.Tendsto (fun t => T ⟨_, hconv.1 t⟩) Filter.atTop
      (nhds (T' ⟨F.1, hconv.2.1⟩)) := by
    simpa only [hFs] using l2
  exact (tendsto_nhds_unique l1 l3).symm ▸ rfl
end YangMills.Construction.AmbientPoints.BoundedComplexFormDistributionProof
