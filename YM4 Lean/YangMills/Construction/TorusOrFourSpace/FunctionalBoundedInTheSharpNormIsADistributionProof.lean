import YangMills.Construction.TorusOrFourSpace.CentredMomentsOfBoundedFormsProof
import YangMills.Construction.TorusOrFourSpace.ComplexClassesOfOnePointProof
import YangMills.Construction.TorusOrFourSpace.DistinctPointsAndProductsOfAdmissibleFamilies
import YangMills.Construction.TorusOrFourSpace.FiniteSumsOfTensorsAreDenseOnAProduct
import YangMills.Construction.TorusOrFourSpace.FunctionalBoundedInTheSharpNormIsADistribution
import YangMills.Construction.TorusOrFourSpace.GluingOfDistributions
import YangMills.Construction.TorusOrFourSpace.MapsOfFourKindsOnTuplesTestFunctionsAndDistributions
import YangMills.Construction.TorusOrFourSpace.MultilinearFunctionalsOnProductsOfC1Classes
import YangMills.Construction.TorusOrFourSpace.PartitionsOfUnityOnCompactSubsetsOfPowers
import YangMills.Construction.TorusOrFourSpace.SmoothRealFunctionsInTheTwoSenses
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
namespace SharpBoundedParts
open Tuple AdmissibleCharts
variable {D : Params} {E : Kind}
def pullReal (z : Fin 4 → ℝ) (A : Set (E.Pt D)) (φ : E.Pt D → ℝ) :
    euclidean.Pt D → ℝ :=
  fun u => (singlePullback D E z A (fun y => (φ y : ℂ)) u).re
def pushReal (z : Fin 4 → ℝ) (A : Set (E.Pt D)) (g : euclidean.Pt D → ℝ) :
    E.Pt D → ℝ :=
  fun y => (singlePushforward D E z A (fun u => (g u : ℂ)) y).re
def pushRealTuple {n : ℕ} (z : Fin n → Fin 4 → ℝ) (G : Fin n → Set (E.Pt D))
    (g : Fin n → euclidean.Pt D → ℝ) : FnTuple D E n :=
  fun i => pushReal (z i) (G i) (g i)
theorem fin_one_eq (a b : Fin ((1 : ℕ+) : ℕ)) : a = b :=
  Fin.ext (by have := a.2; have := b.2; simp only [PNat.one_coe] at *; omega)
theorem const_apply_zero {Z : Type*} (y : Fin ((1 : ℕ+) : ℕ) → Z) :
    (fun _ => y ⟨0, (1 : ℕ+).pos⟩) = y :=
  funext fun _ => congrArg y (fin_one_eq _ _)
theorem boxSet_one (A : Set (E.Pt D)) :
    boxSet (n := 1) D E (fun _ => A) = singleSet D E A := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.AdmissibleCharts.boxSet_one <;> assumption
theorem admissibleWith_single {n : ℕ+} {R d : ℝ} {G : Fin (n : ℕ) → Set (E.Pt D)}
    (hG : AdmissibleWith D E R d G) (i : Fin (n : ℕ)) :
    AdmissibleWith (n := 1) D E R d (fun _ => G i) where
  radius_pos := hG.radius_pos
  sep_pos := hG.sep_pos
  isOpen_mem := fun _ => hG.isOpen_mem i
  diam_le := fun _ => hG.diam_le i
  diam_lt_quarter_of_torus := fun h _ => hG.diam_lt_quarter_of_torus h i
  sep_le_setInfDist := fun a b hab => absurd (fin_one_eq a b) hab
theorem singlePushforward_singlePullback (hChart : AdmissibleCharts.Claim) {n : ℕ+} {R d : ℝ}
    {G : Fin (n : ℕ) → Set (E.Pt D)} (hG : AdmissibleWith D E R d G) (i : Fin (n : ℕ))
    {z : Fin 4 → ℝ} (hz : E.quotMap D z ∈ G i) {φ : E.Pt D → ℂ}
    (hφ : φ ∈ singleTestFns D E (G i)) :
    singlePushforward D E z (G i) (singlePullback D E z (G i) φ) = φ := by
  obtain ⟨-, -, hinv, -⟩ := hChart D E 1 R d (fun _ => G i) (fun _ => z) (admissibleWith_single hG i)
    (fun _ => ⟨_, hz⟩) (fun _ => hz)
  have hcs : HasCompactSupportWithin D E (boxSet (n := 1) D E fun _ => G i)
      (ofSingle D E φ) := by
    rw [_root_.YangMills.Construction.PeriodicSpace.Kind.SharpBoundedParts.boxSet_one]
    exact ⟨hφ.2.1, hφ.2.2⟩
  have h := (hinv.2.2.1 _ hcs).2.1
  have h' : ofSingle D euclidean (singlePullback D E z (G i) φ) =
      pullback D E (n := 1) (fun _ => z) (fun _ => G i) (ofSingle D E φ) := by
    funext w
    show pullback D E (n := 1) (fun _ => z) (fun _ => G i) (ofSingle D E φ)
      (fun _ => w ⟨0, (1 : ℕ+).pos⟩) = _
    rw [const_apply_zero]
  funext y
  show pushforward D E (n := 1) (fun _ => z) (fun _ => G i)
    (ofSingle D euclidean (singlePullback D E z (G i) φ)) (fun _ => y) = φ y
  rw [h', h]
  rfl
theorem singlePullback_of_mem {z : Fin 4 → ℝ} {A : Set (E.Pt D)} {u : euclidean.Pt D}
    (hu : u ∈ chartSource D E z A) (φ : E.Pt D → ℂ) :
    singlePullback D E z A φ u = φ (translateChart D E z u) := by
  have hm : (fun _ => u : euclidean.Tuple D 1) ∈
      chartSources D E (n := 1) (fun _ => z) (fun _ => A) := fun _ => hu
  show (chartSources D E (n := 1) (fun _ => z) (fun _ => A)).indicator _ _ = _
  rw [Set.indicator_of_mem hm]
  rfl
theorem setInfDist_anti {A A' B B' : Set (E.Pt D)} (hA : A ⊆ A') (hB : B ⊆ B') :
    setInfDist D E A' B' ≤ setInfDist D E A B := by apply _root_.YangMills.Construction.PeriodicSpace.Kind.CentredMoments.setInfDist_anti <;> assumption
theorem toReal_mem_allowedRadii {r : ℝ≥0∞} (h0 : 0 < r) (hq : r < periodQuarter D E)
    (htop : r ≠ ∞) : r.toReal ∈ allowedRadii D E := by
  have hpos : 0 < r.toReal := ENNReal.toReal_pos h0.ne' htop
  cases E with
  | euclidean => exact hpos
  | torus => exact ⟨hpos, ENNReal.toReal_lt_of_lt_ofReal hq⟩
theorem composePullback_eq {n : ℕ+} {z : Fin (n : ℕ) → Fin 4 → ℝ}
    {G : Fin (n : ℕ) → Set (E.Pt D)}
    (T : testFns D euclidean (chartSources D E z G) → ℂ)
    (F : testFns D E (boxSet D E G))
    (H : testFns D euclidean (chartSources D E z G))
    (hH : H.1 = pullback D E z G F.1) : composePullback D E z G T F = T H := by
  have h : pullback D E z G F.1 ∈ testFns D euclidean (chartSources D E z G) :=
    hH ▸ H.2
  rw [composePullback, dif_pos h]
  exact congrArg T (Subtype.ext hH.symm)
section Factors
variable {n : ℕ+} {G : Fin (n : ℕ) → Set (E.Pt D)} {z : Fin (n : ℕ) → Fin 4 → ℝ}
theorem coe_pullReal (hc : SingleMapsOnClasses D E z G) (i : Fin (n : ℕ)) {φ : E.Pt D → ℝ}
    (hφ : (fun y => (φ y : ℂ)) ∈ singleTestFns D E (G i)) :
    (fun u => (pullReal (z i) (G i) φ u : ℂ)) =
      singlePullback D E (z i) (G i) fun y => (φ y : ℂ) := by
  funext u
  apply Complex.ext
  · rw [Complex.ofReal_re]
    rfl
  · rw [Complex.ofReal_im]
    exact ((hc.1 i).2 _ hφ (fun y => Complex.ofReal_im _) u).symm
theorem pullReal_mem (hc : SingleMapsOnClasses D E z G) (i : Fin (n : ℕ)) {φ : E.Pt D → ℝ}
    (hφ : (fun y => (φ y : ℂ)) ∈ singleTestFns D E (G i)) :
    (fun u => (pullReal (z i) (G i) φ u : ℂ)) ∈
      singleTestFns D euclidean (chartSource D E (z i) (G i)) := by
  rw [coe_pullReal hc i hφ, ← (hc.1 i).1]
  exact ⟨_, hφ, rfl⟩
theorem pushReal_mem (hc : SingleMapsOnClasses D E z G) (i : Fin (n : ℕ))
    {g : euclidean.Pt D → ℝ} (hg : g ∈ c1SupportedIn D euclidean (chartSource D E (z i) (G i))) :
    pushReal (z i) (G i) g ∈ c1SupportedIn D E (G i) ∧
      (fun y => (pushReal (z i) (G i) g y : ℂ)) =
        singlePushforward D E (z i) (G i) fun u => (g u : ℂ) := by
  have h : (singlePushforward D E (z i) (G i) fun u => (g u : ℂ)) ∈
      (fun (h : E.Pt D → ℝ) (y : E.Pt D) => (h y : ℂ)) '' c1SupportedIn D E (G i) := by
    rw [← (hc.2.2 i).1]
    exact ⟨g, hg, rfl⟩
  obtain ⟨h, hh, e⟩ := h
  have e2 : pushReal (z i) (G i) g = h := by
    funext y
    show (singlePushforward D E (z i) (G i) (fun u => (g u : ℂ)) y).re = h y
    rw [← e]
    exact Complex.ofReal_re _
  rw [e2]
  exact ⟨hh, e⟩
theorem pushReal_pullReal (hc : SingleMapsOnClasses D E z G)
    (hpp : ∀ i, ∀ φ ∈ singleTestFns D E (G i),
      singlePushforward D E (z i) (G i) (singlePullback D E (z i) (G i) φ) = φ)
    (i : Fin (n : ℕ)) {φ : E.Pt D → ℝ}
    (hφ : (fun y => (φ y : ℂ)) ∈ singleTestFns D E (G i)) :
    pushReal (z i) (G i) (pullReal (z i) (G i) φ) = φ := by
  funext y
  show (singlePushforward D E (z i) (G i)
    (fun u => (pullReal (z i) (G i) φ u : ℂ)) y).re = φ y
  rw [coe_pullReal hc i hφ, hpp i _ hφ]
  exact Complex.ofReal_re _
theorem exists_pullReal_eq (hc : SingleMapsOnClasses D E z G)
    (hpp : ∀ i, ∀ φ ∈ singleTestFns D E (G i),
      singlePushforward D E (z i) (G i) (singlePullback D E (z i) (G i) φ) = φ)
    (i : Fin (n : ℕ)) {g : euclidean.Pt D → ℝ}
    (hg : (fun u => (g u : ℂ)) ∈
      singleTestFns D euclidean (chartSource D E (z i) (G i)))
    (hg1 : g ∈ c1SupportedIn D euclidean (chartSource D E (z i) (G i))) :
    ∃ φ : E.Pt D → ℝ, (fun y => (φ y : ℂ)) ∈ singleTestFns D E (G i) ∧
      pullReal (z i) (G i) φ = g := by
  have h : (fun u => (g u : ℂ)) ∈
      singlePullback D E (z i) (G i) '' singleTestFns D E (G i) := by
    rw [(hc.1 i).1]
    exact hg
  obtain ⟨ψ, hψ, e⟩ := h
  have e1 : (singlePushforward D E (z i) (G i) fun u => (g u : ℂ)) = ψ := by
    rw [← e]
    exact hpp i ψ hψ
  have e3 : (fun y => (pushReal (z i) (G i) g y : ℂ)) = ψ := (pushReal_mem hc i hg1).2.trans e1
  refine ⟨pushReal (z i) (G i) g, e3 ▸ hψ, ?_⟩
  funext u
  show (singlePullback D E (z i) (G i)
    (fun y => (pushReal (z i) (G i) g y : ℂ)) u).re = g u
  rw [e3, e]
  exact Complex.ofReal_re _
end Factors
theorem spec_of_nonempty (hChart : AdmissibleCharts.Claim)
    (hForm : C1BoundedFormDistribution)
    (hDense : TensorSpanDenseOnBoxes)
    (hFacts : PeriodicSpace.LiftsProductsDistributions.Statement)
    (hProd : DisjointProducts.Claim)
    (hPts : TupleFacts.AllFacts) {n : ℕ+}
    {Ψ : sepC1Tuples D E (n : ℕ) → ℝ} {c : ℝ → ℝ → ℝ}
    (hΨ : IsMultilinearOn D E (sepC1Tuples D E (n : ℕ)) Ψ)
    (hc : ∀ d R : ℝ, 0 < d → R ∈ allowedRadii D E → 0 ≤ c d R)
    (hbound : SharpNormBounded c Ψ) {R d : ℝ} {G : Fin (n : ℕ) → Set (E.Pt D)}
    (hG : AdmissibleWith D E R d G) (hne : ∀ i, (G i).Nonempty) :
    SeparatedFamilyDistribSpec c Ψ R d G := by
  have hn1 : 1 ≤ (n : ℕ) := n.pos
  have hd : 0 < d := hG.sep_pos
  obtain ⟨hCov, hLift, -, -, hLip, -, -⟩ := hFacts D E
  have hlift : ∀ y : E.Pt D, ∃ x, E.quotMap D x = y := fun y => by
    obtain ⟨x, hx, -⟩ := hLift 0 y
    exact ⟨x, hx⟩
  have hzex : ∀ i, ∃ x, E.quotMap D x ∈ G i := fun i => by
    obtain ⟨y, hy⟩ := hne i
    obtain ⟨x, rfl⟩ := hlift y
    exact ⟨x, hy⟩
  choose z hz using hzex
  obtain ⟨⟨hr0, hr2, hrq, hfac⟩, -, hinv, -, hiso, hconv, hcls⟩ :=
    hChart D E n R d G z hG hne hz
  have hpp : ∀ i, ∀ φ ∈ singleTestFns D E (G i),
      singlePushforward D E (z i) (G i) (singlePullback D E (z i) (G i) φ) = φ :=
    fun i φ hφ => singlePushforward_singlePullback hChart hG i (hz i) hφ
  have hdist0 : ∀ y : E.Pt D, ENNReal.ofReal (quotDist D E y y) = 0 := fun y => by
    obtain ⟨x, rfl⟩ := hlift y
    refine ENNReal.ofReal_eq_zero.mpr ((hCov x x).1.trans (le_of_eq ?_))
    simp [TorusMetric.euclidNormVec]
  have hdisj : ∀ l l', l ≠ l' → Disjoint (G l) (G l') := fun l l' hll =>
    Set.disjoint_left.mpr fun y h1 h2 => by
      have h3 : setInfDist D E (G l) (G l') ≤ 0 := by
        rw [← hdist0 y]
        exact iInf₂_le_of_le y h1 (iInf₂_le_of_le y h2 le_rfl)
      have h4 : ENNReal.ofReal d ≤ 0 := (hG.sep_le_setInfDist l l' hll).trans h3
      have h5 : 0 < ENNReal.ofReal d := ENNReal.ofReal_pos.mpr hd
      exact absurd h4 (not_le.mpr h5)
  obtain ⟨hVec, hSepP, hLinP, -, -⟩ := hProd D E n hn1
  have hVec4 := (hProd D euclidean n hn1).1
  have hTen : TupleFacts.TensorTestFns D E n :=
    (hPts D E n).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmemP : ∀ g : C1Components D euclidean (fun i => chartSource D E (z i) (G i)),
      pushRealTuple z G (fun j => (g j).1) ∈
        productSet D E (fun l => c1SupportedIn D E (G l)) :=
    fun g i _ => (pushReal_mem hcls i (g i).2).1
  have hsep : ∀ g : C1Components D euclidean (fun i => chartSource D E (z i) (G i)),
      pushRealTuple z G (fun j => (g j).1) ∈ sepC1Tuples D E (n : ℕ) :=
    fun g => hSepP G hdisj (hmemP g)
  obtain ⟨B, hB⟩ : ∃ B : C1Components D euclidean (fun i => chartSource D E (z i) (G i)) → ℝ,
      ∀ g, B g = Ψ ⟨_, hsep g⟩ := ⟨_, fun _ => rfl⟩
  have hrtop : maxMemberDiam D E G ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hr2
  have hrpos : 0 < (maxMemberDiam D E G).toReal := ENNReal.toReal_pos hr0.ne' hrtop
  have hradm := toReal_mem_allowedRadii hr0 hrq hrtop
  have h80 : 0 ≤ 80 * D.M := by linarith [D.one_le_M]
  have hCv : 0 ≤ c d (maxMemberDiam D E G).toReal :=
    hc d _ hd hradm
  have hc0 : 0 ≤ (80 * D.M) ^ (n : ℕ) * c d (maxMemberDiam D E G).toReal :=
    mul_nonneg (pow_nonneg h80 _) hCv
  have hlin : IsMultilinearReal B := by
    intro g i u v w a b hw
    have hN := hLinP (Ψ) hΨ G hdisj
    have hupd : ∀ x : c1SupportedIn D euclidean (chartSource D E (z i) (G i)),
        pushRealTuple z G (fun j => (Function.update g i x j).1) =
          Function.update (pushRealTuple z G fun j => (g j).1) i
            (pushReal (z i) (G i) x.1) := by
      intro x
      funext j
      by_cases h : j = i
      · subst h
        simp [pushRealTuple]
      · simp [pushRealTuple, Function.update_of_ne h]
    have hpw : pushReal (z i) (G i) w.1 =
        a • pushReal (z i) (G i) u.1 + b • pushReal (z i) (G i) v.1 := by
      have e := (hcls.2.2 i).2.1 a b u.1 u.2 v.1 v.2
      have hw' : (fun x => ((w.1 x : ℝ) : ℂ)) = fun x => ((a * u.1 x + b * v.1 x : ℝ) : ℂ) := by
        funext x
        rw [hw]
        rfl
      funext y
      show (singlePushforward D E (z i) (G i) (fun x => ((w.1 x : ℝ) : ℂ)) y).re =
        a * (singlePushforward D E (z i) (G i) (fun x => ((u.1 x : ℝ) : ℂ)) y).re +
          b * (singlePushforward D E (z i) (G i) (fun x => ((v.1 x : ℝ) : ℂ)) y).re
      rw [hw', e]
      simp
    have hm : ∀ x : c1SupportedIn D euclidean (chartSource D E (z i) (G i)),
        Function.update (pushRealTuple z G fun j => (g j).1) i (pushReal (z i) (G i) x.1) ∈
          sepC1Tuples D E (n : ℕ) :=
      fun x => hupd x ▸ hsep (Function.update g i x)
    have hww : Function.update (pushRealTuple z G fun j => (g j).1) i
        (a • pushReal (z i) (G i) u.1 + b • pushReal (z i) (G i) v.1) ∈
          sepC1Tuples D E (n : ℕ) := by
      rw [← hpw]
      exact hm w
    have key := hN.2 _ (hmemP g) i _ (pushReal_mem hcls i u.2).1 _ (pushReal_mem hcls i v.2).1 a b
      (hm u) (hm v) hww
    have eu : ∀ x : c1SupportedIn D euclidean (chartSource D E (z i) (G i)),
        Ψ ⟨_, hm x⟩ = B (Function.update g i x) := fun x => by
      rw [hB]
      exact congrArg _ (Subtype.ext (hupd x).symm)
    rw [← eu u, ← eu v, ← key, hB]
    exact congrArg _ (Subtype.ext ((hupd w).trans (by rw [hpw])))
  have hbd : C1Bounded
      ((80 * D.M) ^ (n : ℕ) * c d (maxMemberDiam D E G).toReal) B := by
    intro g
    have hmem := hmemP g
    have hl : pushRealTuple z G (fun j => (g j).1) ∈ lipTuplesSpacedInBalls D E (n : ℕ) d
        (maxMemberDiam D E G).toReal := by
      refine ⟨fun i => ?_, fun i => ?_, fun i k hik => ?_⟩
      · exact (hLip _ ⟨(hmem i trivial).1, (hmem i trivial).2.1, Set.subset_univ _⟩).1
      · exact ⟨closedBallAbout D E (E.quotMap D (z i)) (maxMemberDiam D E G).toReal,
          ⟨hrpos, _, rfl⟩, (hmem i trivial).2.2.trans (hfac i).2.2.2.2.2.2⟩
      · exact (hG.sep_le_setInfDist i k hik).trans
          (setInfDist_anti (hmem i trivial).2.2 (hmem k trivial).2.2)
    have h1 := hbound d _ hd hradm ⟨_, hsep g⟩ hl
    have hsh : ∀ i, sharpNormQ D E (pushRealTuple z G (fun j => (g j).1) i) ≤
        ENNReal.ofReal (80 * D.M) * c1NormSingleReal D euclidean (g i).1 := fun i => by
      have h2 := (hLip _ ⟨(hmem i trivial).1, (hmem i trivial).2.1, Set.subset_univ _⟩).2.2
      have h3 := (hcls.2.2 i).2.2 (g i).1 (g i).2
      have h4 : c1NormSingleReal D E (pushRealTuple z G (fun j => (g j).1) i) =
          c1NormSingleReal D euclidean (g i).1 := by
        rw [← h3, ← (pushReal_mem hcls i (g i).2).2]
        rfl
      rw [← h4]
      exact h2
    rw [hB g]
    calc ENNReal.ofReal |Ψ ⟨_, hsep g⟩|
        ≤ ENNReal.ofReal (c d (maxMemberDiam D E G).toReal) *
            ∏ i, sharpNormQ D E (pushRealTuple z G (fun j => (g j).1) i) := h1
      _ ≤ ENNReal.ofReal (c d (maxMemberDiam D E G).toReal) *
            ∏ i, (ENNReal.ofReal (80 * D.M) * c1NormSingleReal D euclidean (g i).1) := by
          gcongr with i _
          exact hsh i
      _ = _ := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            ENNReal.ofReal_mul (pow_nonneg h80 _), ENNReal.ofReal_pow h80, ← mul_assoc,
            mul_comm (ENNReal.ofReal (c _ _))]
  obtain ⟨hF1, ⟨T0, hT0, hT0u⟩, hT0b⟩ := hForm D n (2 * R) _
    (by have := hG.radius_pos; positivity) hc0 (fun i => chartSource D E (z i) (G i))
    (fun i => (hfac i).1) (fun i u hu => (hfac i).2.2.2.2.2.1 ((hfac i).2.2.2.2.1 hu)) B hlin hbd
  have hcut : ∀ φ, IsCutoffFamily D E G φ →
      φ ∈ sepC1Tuples D E (n : ℕ) ∧
        cutoffTensor D E φ ∈ testFns D E (boxSet D E G) ∧
        tensorProd D euclidean (fun i u => ((pullReal (z i) (G i) (φ i) u : ℝ) : ℂ)) =
          pullback D E z G (cutoffTensor D E φ) ∧
        ∀ i, (fun u => ((pullReal (z i) (G i) (φ i) u : ℝ) : ℂ)) ∈
          singleTestFns D euclidean (chartSource D E (z i) (G i)) := by
    intro φ hφ
    refine ⟨hSepP G hdisj fun i _ => hVec.2 (G i) (hG.isOpen_mem i) _ (hφ i),
      hTen G _ hG.isOpen_mem hφ, ?_, fun i => pullReal_mem hcls i (hφ i)⟩
    exact (congrArg _ (funext fun i => coe_pullReal hcls i (hφ i))).trans
      (hcls.2.1 (fun i y => (φ i y : ℂ)) hφ).symm
  have hBp : ∀ φ, IsCutoffFamily D E G φ →
      ∀ (h : ∀ i, pullReal (z i) (G i) (φ i) ∈
          c1SupportedIn D euclidean (chartSource D E (z i) (G i)))
        (hs : φ ∈ sepC1Tuples D E (n : ℕ)),
        B (fun i => ⟨_, h i⟩) = Ψ ⟨φ, hs⟩ := by
    intro φ hφ h hs
    rw [hB]
    exact congrArg _ (Subtype.ext (funext fun i => pushReal_pullReal hcls hpp i (hφ i)))
  have hexist : IsFamilyDistrib Ψ G (composePullback D E z G T0) := by
    refine ⟨hconv.2.1.mapsTo hT0.1, fun φ hφ => ?_⟩
    obtain ⟨hs, hF, hpb, hm⟩ := hcut φ hφ
    obtain ⟨h1, hF', e⟩ := hT0.2 (fun i => pullReal (z i) (G i) (φ i)) hm
    refine ⟨hs, hF, ?_⟩
    exact (composePullback_eq T0 ⟨_, hF⟩ ⟨_, hF'⟩ hpb).trans
      (e.trans (congrArg _ (hBp φ hφ h1 hs)))
  have hu : ∀ T', IsFamilyDistrib Ψ G T' → T' = composePullback D E z G T0 := by
    intro T' hT'
    obtain ⟨T, hTd, rfl⟩ := hconv.2.1.surjOn hT'.1
    have hform : IsDistribExtending B T := by
      refine ⟨hTd, fun ψ hψ => ?_⟩
      obtain ⟨h1, hF', -⟩ := hT0.2 ψ hψ
      choose φ hφ hpl using fun i => exists_pullReal_eq hcls hpp i (hψ i) (h1 i)
      obtain ⟨hs, hF, hpb, hm⟩ := hcut φ hφ
      obtain ⟨hs', hF2, e⟩ := hT'.2 φ hφ
      have hψe : ψ = fun i => pullReal (z i) (G i) (φ i) := funext fun i => (hpl i).symm
      subst hψe
      refine ⟨h1, hF', ?_⟩
      exact (composePullback_eq T ⟨_, hF2⟩ ⟨_, hF'⟩ hpb).symm.trans
        (e.trans (congrArg _ (hBp φ hφ h1 hs').symm))
    exact congrArg _ (hT0u T hform)
  refine ⟨⟨_, hexist, hu⟩, fun F => hDense D E n R d G hG hne F, fun _ => ⟨hrtop, hradm⟩,
    fun ⟨i, hi⟩ => absurd hi (hne i).ne_empty, fun T hT => ?_⟩
  have hTe := hu T hT
  subst hTe
  refine ⟨(hconv.2.2.2 T0 hT0.1 _).mpr (hT0b T0 hT0).2, fun _ χ hχ F hFχ => ?_,
    fun ⟨i, hi⟩ => absurd hi (hne i).ne_empty⟩
  have hcs : HasCompactSupportWithin D E (boxSet D E G) F.1 := ⟨F.2.2.1, F.2.2.2⟩
  have hpF := hiso.1.mapsTo F.2
  have hχ' : IsCutoffFamily D euclidean (fun i => chartSource D E (z i) (G i))
      (fun i => pullReal (z i) (G i) (χ i)) := fun i => pullReal_mem hcls i (hχ i)
  have hone : OneOnCoordProjs D euclidean (pullback D E z G F.1)
      (fun i => pullReal (z i) (G i) (χ i)) := by
    rintro i _ ⟨u, hu', rfl⟩
    rw [(hinv.2.2.1 F.1 hcs).2.2] at hu'
    obtain ⟨huO, huF⟩ := hu'
    obtain ⟨U, -, hsub, h1⟩ := hFχ i
    have h2 : χ i (translateChart D E (z i) (u i)) = 1 := h1 _ (hsub ⟨_, huF, rfl⟩)
    show (singlePullback D E (z i) (G i) (fun y => (χ i y : ℂ)) (u i)).re = 1
    rw [singlePullback_of_mem (huO i), h2]
    simp
  have hcf := (hF1 ⟨_, hpF⟩).1 _ hχ' hone
  have hb := (hT0b T0 hT0).1 ⟨_, hpF⟩ _ hcf
  have hTF : composePullback D E z G T0 F = T0 ⟨_, hpF⟩ :=
    composePullback_eq T0 F ⟨_, hpF⟩ rfl
  have hnorm : ∀ i, c1NormSingleReal D euclidean (pullReal (z i) (G i) (χ i)) =
      c1NormSingleReal D E (χ i) := fun i => by
    have h1 := hVec4.2 _ (hfac i).1 _ (pullReal_mem hcls i (hχ i))
    have h3 := (hcls.2.2 i).2.2 _ h1
    rw [← h3, coe_pullReal hcls i (hχ i), hpp i _ (hχ i)]
    rfl
  rw [hTF]
  refine hb.trans (le_of_eq ?_)
  have hconst : 2 ^ (n : ℕ) * ((80 * D.M) ^ (n : ℕ) *
      c d (maxMemberDiam D E G).toReal) * cutoffBound n (2 * R) =
      (160 * D.M) ^ (n : ℕ) * c d (maxMemberDiam D E G).toReal *
        cutoffBound n (2 * R) := by
    have : 160 * D.M = 2 * (80 * D.M) := by ring
    rw [this, mul_pow 2 (80 * D.M)]
    ring
  rw [hconst, Finset.prod_congr rfl fun i _ => hnorm i, hiso.2.2 F.1 F.2]
theorem spec_of_empty_member
    (points : TupleFacts.AllFacts)
    (products : DisjointProducts.Claim) {n : ℕ+}
    {Ψ : sepC1Tuples D E (n : ℕ) → ℝ} (c : ℝ → ℝ → ℝ)
    (hΨ : IsMultilinearOn D E (sepC1Tuples D E (n : ℕ)) Ψ) {R d : ℝ}
    {G : Fin (n : ℕ) → Set (E.Pt D)} (hG : AdmissibleWith D E R d G)
    (hE : ∃ i, G i = ∅) : SeparatedFamilyDistribSpec c Ψ R d G := by
  obtain ⟨i₀, hi₀⟩ := hE
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hprod, -, -, -, -, -, -, -, hstable, hemp, -, htens, -⟩ :=
    points D E n
  obtain ⟨-, -, hmetric₁, -, -, -, -, -, -, -, -, -, hproj₁, -, -, -, -, -, -, -, hemp₁, -, -, -⟩ :=
    points D E 1
  obtain ⟨hcl, hsep, -, hvan, -⟩ := products D E (n : ℕ) n.pos
  have hEmptyProduct : Tuple.boxSet D E G = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun y hy => ?_
    have h : y i₀ ∈ G i₀ := hy i₀
    rw [hi₀] at h
    exact h
  have hD : Tuple.testFns D E (Tuple.boxSet D E G) = {0} := by
    rw [hEmptyProduct]
    exact hemp
  have hzero : ∀ F : Tuple.testFns D E (Tuple.boxSet D E G),
      F.1 = 0 := fun F => Set.mem_singleton_iff.mp ((Set.ext_iff.mp hD F.1).mp F.2)
  have hmem0 : (0 : E.Tuple D n → ℂ) ∈
      Tuple.testFns D E (Tuple.boxSet D E G) :=
    (Set.ext_iff.mp hD 0).mpr rfl
  have hopen : Tuple.IsOpenT D E (Tuple.boxSet D E G) :=
    (hprod G).1 hG.isOpen_mem
  have hder : ∀ α, Tuple.partialDeriv D E α (0 : E.Tuple D n → ℂ) = 0 := fun α =>
    Set.mem_singleton_iff.mp ((Set.ext_iff.mp hD _).mp (((hstable _ hopen).2 0 hmem0).2.2.1 α))
  have hnorm : ∀ ν, Tuple.cNorm D E ν (0 : E.Tuple D n → ℂ) = 0 := by
    intro ν
    simp only [Tuple.cNorm, ENNReal.iSup_eq_zero]
    intro α _ y
    rw [hder α]
    simp
  have hlin : ∀ T : Tuple.testFns D E (Tuple.boxSet D E G) → ℂ,
      Tuple.IsComplexLinearForm T → ∀ F, T F = 0 := by
    intro T hT F
    have h := hT.2 0 F F (by rw [hzero F]; simp)
    simpa using h
  have hserve : ∀ T : Tuple.testFns D E (Tuple.boxSet D E G) → ℂ,
      Tuple.IsComplexLinearForm T → ∀ K ν, Tuple.HasOrderBoundOn T K ν := by
    intro T hT K ν
    refine ⟨0, fun F _ => ?_⟩
    rw [hlin T hT F]
    simp
  have hself : ∀ z : E.Pt D, quotDist D E z z ≤ 0 := by
    intro z
    have h := (hproj₁ ⟨0, (1 : ℕ+).pos⟩).1 (fun _ => z) (fun _ => z)
    rw [(hmetric₁.2.1 _ _).mpr rfl] at h
    exact h
  have hdisj : ∀ l l', l ≠ l' → Disjoint (G l) (G l') := by
    intro l l' hll
    rw [Set.disjoint_left]
    intro z hz hz'
    have h₁ := hG.sep_le_setInfDist l l' hll
    have h₂ : setInfDist D E (G l) (G l') ≤ ENNReal.ofReal (quotDist D E z z) :=
      (iInf₂_le z hz).trans (iInf₂_le z hz')
    rw [ENNReal.ofReal_of_nonpos (hself z)] at h₂
    have h₃ : ENNReal.ofReal d = 0 := le_antisymm (h₁.trans h₂) bot_le
    exact absurd hG.sep_pos (not_lt.mpr (ENNReal.ofReal_eq_zero.mp h₃))
  have hone : ∀ φ : E.Pt D → ℂ,
      φ ∈ Tuple.singleTestFns D E (G i₀) → φ = 0 := by
    intro φ hφ
    have hs : Tuple.singleSet D E (G i₀) = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun y hy => ?_
      have h : y ⟨0, (1 : ℕ+).pos⟩ ∈ G i₀ := hy
      rw [hi₀] at h
      exact h
    have h : Tuple.ofSingle D E φ ∈
        Tuple.testFns D E (Tuple.singleSet D E (G i₀)) := hφ
    rw [hs, hemp₁] at h
    funext y
    exact congrFun (Set.mem_singleton_iff.mp h) (fun _ => y)
  have hT₀ : Tuple.IsComplexLinearForm
      (fun _ : Tuple.testFns D E (Tuple.boxSet D E G) => (0 : ℂ)) :=
    ⟨fun _ _ _ _ => by simp, fun _ _ _ _ => by simp⟩
  have hvalue : ∀ φ : Fin (n : ℕ) → E.Pt D → ℝ,
      (∀ i, (fun y => (φ i y : ℂ)) ∈ Tuple.singleTestFns D E (G i)) →
      ∃ (hφ : φ ∈ sepC1Tuples D E (n : ℕ))
        (hF : Tuple.tensorProd D E (fun i y => (φ i y : ℂ)) ∈
          Tuple.testFns D E (Tuple.boxSet D E G)),
        (0 : ℂ) = ((Ψ ⟨φ, hφ⟩ : ℝ) : ℂ) := by
    intro φ hφ
    have hclass : φ ∈ productSet D E (fun l => c1SupportedIn D E (G l)) :=
      fun l _ => hcl.2 (G l) (hG.isOpen_mem l) (φ l) (hφ l)
    have hsepφ : φ ∈ sepC1Tuples D E (n : ℕ) := hsep G hdisj hclass
    have hF : Tuple.cutoffTensor D E φ ∈
        Tuple.testFns D E (Tuple.boxSet D E G) :=
      htens G (fun i y => (φ i y : ℂ)) hG.isOpen_mem hφ
    have hentry : φ i₀ = 0 := by
      funext y
      have h := congrFun (hone _ (hφ i₀)) y
      simpa using h
    refine ⟨hsepφ, hF, ?_⟩
    have h := hvan Ψ hΨ ⟨φ, hsepφ⟩ i₀ hentry
    rw [h]
    simp
  refine ⟨⟨fun _ => 0, ⟨⟨hT₀, fun K _ _ => ⟨0, hserve _ hT₀ K 0⟩⟩, hvalue⟩,
      fun T hT => funext fun F => hlin T hT.1.1 F⟩, ?_,
    fun hne => absurd (hne i₀) (by rw [hi₀]; exact Set.not_nonempty_empty), fun _ => hD,
    fun T hT => ⟨⟨hT.1, fun K _ _ => hserve T hT.1.1 K _⟩,
      fun hne => absurd (hne i₀) (by rw [hi₀]; exact Set.not_nonempty_empty),
      fun _ F => hlin T hT.1.1 F⟩⟩
  intro F
  refine ⟨fun _ => F, fun _ => ⟨0, fun k => k.elim0, fun k => k.elim0, ?_⟩,
    ⟨Tuple.supportT D E F.1, F.2.2.1, F.2.2.2, subset_rfl, fun _ => subset_rfl⟩, fun ν => ?_⟩
  · simpa using hzero F
  · simp only [sub_self, hnorm]
    exact tendsto_const_nhds
theorem isCutoffFamily_mono {n : ℕ+} {G H : Fin (n : ℕ) → Set (E.Pt D)} (hGH : ∀ i, H i ⊆ G i)
    {χ : Fin (n : ℕ) → E.Pt D → ℝ} (h : IsCutoffFamily D E H χ) : IsCutoffFamily D E G χ := by
  intro i
  obtain ⟨h1, h2, h3⟩ := h i
  exact ⟨h1, h2, h3.trans fun y hy => hGH i hy⟩
theorem restrictDistrib_isFamilyDistrib
    (hF : PeriodicSpace.LiftsProductsDistributions.Statement) {n : ℕ+}
    (Ψ : sepC1Tuples D E (n : ℕ) → ℝ) {G H : Fin (n : ℕ) → Set (E.Pt D)}
    (hG : Tuple.IsOpenT D E (boxSet D E G))
    (hH : Tuple.IsOpenT D E (boxSet D E H))
    (hGH : ∀ i, H i ⊆ G i) (hsub : boxSet D E H ⊆ boxSet D E G)
    {T₀ : testFns D E (boxSet D E H) → ℂ} (hT₀ : IsFamilyDistrib Ψ H T₀)
    {T : testFns D E (boxSet D E G) → ℂ} (hT : IsFamilyDistrib Ψ G T) :
    IsFamilyDistrib Ψ H (restrictDistrib hsub T) := by
  refine ⟨((hF D E).2.2.2.2.2.1 n _ _ hH hG hsub T hT.1).2.1, fun φ hφ => ?_⟩
  obtain ⟨h1, h2, -⟩ := hT₀.2 φ hφ
  obtain ⟨h3, h4, h5⟩ := hT.2 φ (isCutoffFamily_mono (χ := φ) hGH hφ)
  exact ⟨h1, h2, h5⟩
theorem glue_family_distribs (hF : PeriodicSpace.LiftsProductsDistributions.Statement)
    (hO : AdmissibleProductFacts)
    (hGl : Tuple.DistribGluing.Statement) {n : ℕ+} (hn : 2 ≤ (n : ℕ))
    (Ψ : sepC1Tuples D E (n : ℕ) → ℝ)
    (exU : ∀ G : Fin (n : ℕ) → Set (E.Pt D), Admissible D E G →
      ∃! T, IsFamilyDistrib Ψ G T)
    (ord : ∀ G : Fin (n : ℕ) → Set (E.Pt D), Admissible D E G →
      ∀ T, IsFamilyDistrib Ψ G T →
        IsDistribOfOrderLE (5 * (n : ℕ) + 1) T) :
    (∃! T, RestrictsToFamilyDistribs Ψ T) ∧
      ∀ T, RestrictsToFamilyDistribs Ψ T → IsDistribOfOrderLE (5 * (n : ℕ) + 1) T := by
  obtain ⟨hOpenΩ, hProd, -, hCover, hInter⟩ := hO D E n
  let Γ : Type := {G : Fin (n : ℕ) → Set (E.Pt D) // Admissible D E G}
  let O : Γ → Set (E.Tuple D n) := fun γ => boxSet D E γ.1
  have hΩ : ⋃ γ, O γ = pairwiseDistinct D E n := by
    apply Set.Subset.antisymm
    · exact Set.iUnion_subset fun γ => (hProd γ.1 γ.2).2
    · intro y hy
      obtain ⟨G, hG, hyG⟩ := hCover y hy
      exact Set.mem_iUnion.2 ⟨⟨G, hG⟩, hyG⟩
  have hOopen : ∀ γ, Tuple.IsOpenT D E (O γ) := fun γ => (hProd γ.1 γ.2).1
  choose T hT using fun γ : Γ => (exU γ.1 γ.2).exists
  have hAgree : ∀ (γ γ' : Γ) (F : testFns D E (O γ ∩ O γ')),
      restrictDistrib Set.inter_subset_left (T γ) F =
        restrictDistrib Set.inter_subset_right (T γ') F := by
    intro γ γ' F
    obtain ⟨R, d, hRd⟩ := γ.2
    obtain ⟨hH, hHeq⟩ := hInter R d γ.1 γ'.1 hRd γ'.2
    have hHadm : Admissible D E (memberInter D E γ.1 γ'.1) := ⟨R, d, hH⟩
    have s1 : boxSet D E (memberInter D E γ.1 γ'.1) ⊆
        boxSet D E γ.1 := hHeq.subset.trans Set.inter_subset_left
    have s2 : boxSet D E (memberInter D E γ.1 γ'.1) ⊆
        boxSet D E γ'.1 := hHeq.subset.trans Set.inter_subset_right
    obtain ⟨T₀, hT₀, -⟩ := exU _ hHadm
    have e1 := restrictDistrib_isFamilyDistrib hF Ψ (hOopen γ) (hProd _ hHadm).1
      (fun i => Set.inter_subset_left) s1 hT₀ (hT γ)
    have e2 := restrictDistrib_isFamilyDistrib hF Ψ (hOopen γ') (hProd _ hHadm).1
      (fun i => Set.inter_subset_right) s2 hT₀ (hT γ')
    have key : restrictDistrib s1 (T γ) = restrictDistrib s2 (T γ') := (exU _ hHadm).unique e1 e2
    have hFH : F.1 ∈ testFns D E
        (boxSet D E (memberInter D E γ.1 γ'.1)) :=
      ⟨F.2.1, F.2.2.1, F.2.2.2.trans hHeq.superset⟩
    exact congrFun key ⟨F.1, hFH⟩
  obtain ⟨⟨T₁, ⟨hT₁d, hT₁r⟩, hT₁u⟩, hOrd⟩ :=
    hGl D E n (5 * (n : ℕ) + 1) Γ (pairwiseDistinct D E n) O hΩ hOpenΩ hOopen T
      (fun γ => (hT γ).1) hAgree
  have member : ∀ T' : testFns D E (pairwiseDistinct D E n) → ℂ,
      RestrictsToFamilyDistribs Ψ T' → IsDistrib T' ∧
        ∀ γ, restrictDistrib ((Set.subset_iUnion O γ).trans hΩ.subset) T' = T γ := by
    rintro T' ⟨hd, hr⟩
    refine ⟨hd, fun γ => ?_⟩
    obtain ⟨R, d, hRd⟩ := γ.2
    obtain ⟨h, hf⟩ := hr γ.1 ⟨R, d, hn, hRd⟩
    exact (exU γ.1 γ.2).unique hf (hT γ)
  have hT₁ : RestrictsToFamilyDistribs Ψ T₁ := by
    refine ⟨hT₁d, fun G hG => ?_⟩
    obtain ⟨R, d, -, hRd⟩ := hG
    have hA : Admissible D E G := ⟨R, d, hRd⟩
    refine ⟨(hProd G hA).2, ?_⟩
    have h := hT ⟨G, hA⟩
    rw [← hT₁r ⟨G, hA⟩] at h
    exact h
  exact ⟨⟨T₁, hT₁, fun T' hT' => hT₁u T' (member T' hT')⟩, fun T' hT' =>
    hOrd (fun γ => ord γ.1 γ.2 _ (hT γ)) T' (member T' hT').1 (member T' hT').2⟩
theorem prop_of_finite_sums {X : Type*} [AddCommMonoid X] {n : ℕ} (W P : Fin n → Set X)
    (Good : (Fin n → X) → Prop) (hP : ∀ l, P l ⊆ W l)
    (hzeroW : ∀ l, (0 : X) ∈ W l) (haddW : ∀ l u v, u ∈ W l → v ∈ W l → u + v ∈ W l)
    (hzero : ∀ h : Fin n → X, (∀ l, h l ∈ W l) → ∀ i, Good (Function.update h i 0))
    (hadd : ∀ h : Fin n → X, (∀ l, h l ∈ W l) → ∀ i u v, u ∈ W i → v ∈ W i →
      Good (Function.update h i u) → Good (Function.update h i v) →
        Good (Function.update h i (u + v)))
    (hbase : ∀ h : Fin n → X, (∀ l, h l ∈ P l) → Good h)
    (f : Fin n → X) (r : Fin n → ℕ) (g : ∀ l, Fin (r l) → X)
    (hg : ∀ l a, g l a ∈ P l) (hf : ∀ l, f l = ∑ a, g l a) : Good f := by
  classical
  have hfW : ∀ l, ∀ s : Finset (Fin (r l)), (∑ a ∈ s, g l a) ∈ W l := by
    intro l s
    induction s using Finset.induction_on with
    | empty => simpa using hzeroW l
    | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact haddW l _ _ (hP l (hg l a)) ih
  have key : ∀ J : Finset (Fin n), ∀ h : Fin n → X, (∀ l, h l ∈ W l) →
      (∀ l, l ∉ J → h l ∈ P l) → (∀ l, l ∈ J → h l = f l) → Good h := by
    intro J
    induction J using Finset.induction_on with
    | empty =>
      intro h _ hp _
      exact hbase h fun l => hp l (by simp)
    | insert i J hi ih =>
      intro h hW hp hJ
      have sums : ∀ s : Finset (Fin (r i)), Good (Function.update h i (∑ a ∈ s, g i a)) := by
        intro s
        induction s using Finset.induction_on with
        | empty => simpa using hzero h hW i
        | insert a s ha ihs =>
          rw [Finset.sum_insert ha]
          refine hadd h hW i _ _ (hP i (hg i a)) (hfW i s) ?_ ihs
          refine ih _ ?_ ?_ ?_
          · intro l
            by_cases e : l = i
            · subst e
              simpa using hP l (hg l a)
            · simpa [Function.update_of_ne e] using hW l
          · intro l hl
            by_cases e : l = i
            · subst e
              simpa using hg l a
            · simpa [Function.update_of_ne e] using hp l (by simp [e, hl])
          · intro l hl
            have e : l ≠ i := fun e => hi (e ▸ hl)
            simpa [Function.update_of_ne e] using hJ l (by simp [hl])
      have h1 := sums Finset.univ
      rw [← hf i, ← hJ i (by simp), Function.update_eq_self] at h1
      exact h1
  exact key Finset.univ f (fun l => by rw [hf l]; exact hfW l _) (by simp) fun _ _ => rfl
theorem isCompactWrt_closureWrt {X : Type*} {d : X → X → ℝ}
    (tri : ∀ a b c, d a c ≤ d a b + d b c) {K Z : Set X}
    (hK : MetricNotions.IsCompactWrt d K) (hZ : MetricNotions.closureWrt d Z ⊆ K) :
    MetricNotions.IsCompactWrt d (MetricNotions.closureWrt d Z) := by
  intro U hU hcov
  have hCo : MetricNotions.IsOpenWrt d (MetricNotions.closureWrt d Z)ᶜ := by
    intro x hx
    have h0 : ∃ r : ℝ, 0 < r ∧ ∀ y ∈ Z, ¬ d x y < r := by
      by_contra hcon
      push Not at hcon
      exact hx fun r hr => hcon r hr
    obtain ⟨r, hr, h⟩ := h0
    refine ⟨r / 2, by positivity, fun z hz hzC => ?_⟩
    obtain ⟨y, hy, hzy⟩ := hzC (r / 2) (by positivity)
    exact h y hy (by have := tri x z y; linarith)
  obtain ⟨V, hV, hfin, hcovV⟩ := hK (insert (MetricNotions.closureWrt d Z)ᶜ U)
    (by
      rintro W (rfl | hW)
      · exact hCo
      · exact hU W hW)
    (fun x _ => by
      by_cases hxC : x ∈ MetricNotions.closureWrt d Z
      · obtain ⟨W, hW, hxW⟩ := hcov hxC
        exact ⟨W, Or.inr hW, hxW⟩
      · exact ⟨_, Or.inl rfl, hxC⟩)
  refine ⟨V \ {(MetricNotions.closureWrt d Z)ᶜ}, ?_, hfin.subset Set.sdiff_subset, ?_⟩
  · rintro W ⟨hW, hne⟩
    exact (hV hW).resolve_left hne
  · intro x hx
    obtain ⟨W, hW, hxW⟩ := hcovV (hZ hx)
    refine ⟨W, ⟨hW, ?_⟩, hxW⟩
    rintro rfl
    exact hxW hx
theorem const_fin_one (y : E.Tuple D 1) :
    (fun _ => y ⟨0, (1 : ℕ+).pos⟩) = y := by
  funext i
  have : i = ⟨0, (1 : ℕ+).pos⟩ := Fin.ext (by have := i.2; simp at this ⊢; omega)
  rw [this]
theorem singleSet_eq_boxSet (A : Set (E.Pt D)) :
    Tuple.singleSet D E A =
      Tuple.boxSet D E (n := 1) fun _ => A := by
  ext y
  constructor
  · intro h i
    have : i = ⟨0, (1 : ℕ+).pos⟩ := Fin.ext (by have := i.2; simp at this ⊢; omega)
    rw [this]
    exact h
  · intro h
    exact h _
theorem supportQ_ofReal (u : E.Pt D → ℝ) :
    supportQ D E (fun y => (u y : ℂ)) = supportQ D E u := by apply _root_.YangMills.SharedProofs.p40645 <;> assumption
theorem quotDist_self_nonpos (H3 : TupleFacts.AllFacts)
    (y : E.Pt D) : quotDist D E y y ≤ 0 := by
  obtain ⟨-, -, hmet, -, -, -, -, -, -, -, -, -, hproj, -⟩ := H3 D E 1
  have h := (hproj ⟨0, (1 : ℕ+).pos⟩).1 (fun _ => y) (fun _ => y)
  have h0 := (hmet.2.1 (fun _ => y) (fun _ => y)).2 rfl
  rw [h0] at h
  exact h
theorem mem_supportQ_of_ne (H3 : TupleFacts.AllFacts)
    {u : E.Pt D → ℝ} {y : E.Pt D} (hy : u y ≠ 0) : y ∈ supportQ D E u :=
  fun _ hr => ⟨y, hy, lt_of_le_of_lt (quotDist_self_nonpos H3 y) hr⟩
theorem isC1Fn_of_isSmoothFn {u : E.Pt D → ℝ} (hu : IsSmoothFn D E u) :
    IsC1Fn D E u :=
  show ContDiff ℝ 1 (u ∘ E.quotMap D) from
    ContDiff.of_le hu (mod_cast le_top)
theorem cutoffTensor_mem (H2 : SmoothIffSmoothAsTuple)
    (H3 : TupleFacts.AllFacts) {n : ℕ+}
    {f : FnTuple D E (n : ℕ)} (hf : f ∈ sepC1Tuples D E (n : ℕ))
    (hs : ∀ i, IsSmoothFn D E (f i)) :
    Tuple.cutoffTensor D E f ∈ Tuple.testFns D E (pairwiseDistinct D E n) := by
  obtain ⟨-, -, hmet, -, -, -, -, -, -, -, -, hprod, -, -, -, -, -, -, -, -, -, htens, -, -⟩ :=
    H3 D E n
  have hcl : ∀ ν i, TupleFacts.IsClassCSingle D E ν
      (fun y => (f i y : ℂ)) := fun ν i => (H2 D E (f i)).1 (hs i) ν
  have hsup : Tuple.supportT D E (Tuple.cutoffTensor D E f) ⊆
      Tuple.boxSet D E fun i => supportQ D E (f i) := by
    have h := (htens 0 (fun i y => (f i y : ℂ)) fun i => hcl 0 i).2.2
    simp only [supportQ_ofReal] at h
    exact h
  have hK := (hprod fun i => supportQ D E (f i)).2.2 hf.2.1
  refine ⟨fun ν => (htens ν (fun i y => (f i y : ℂ)) fun i => hcl ν i).1,
    isCompactWrt_closureWrt hmet.2.2.2 hK hsup, ?_⟩
  intro y hy
  have hy' := hsup hy
  show Function.Injective y
  intro i k hik
  by_contra hne
  exact Set.disjoint_left.mp (hf.2.2 i k hne) (hy' i) (hik ▸ hy' k)
def TakesValueAt {n : ℕ+} (Ψ : sepC1Tuples D E (n : ℕ) → ℝ)
    (T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ)
    (h : FnTuple D E (n : ℕ)) : Prop :=
  ∀ (hφ : h ∈ sepC1Tuples D E (n : ℕ))
    (hF : Tuple.cutoffTensor D E h ∈
      Tuple.testFns D E (pairwiseDistinct D E n)),
    T ⟨_, hF⟩ = ((Ψ ⟨h, hφ⟩ : ℝ) : ℂ)
def smoothSupportedIn (A : Set (E.Pt D)) : Set (E.Pt D → ℝ) :=
  {u | IsSmoothFn D E u ∧ u ∈ c1SupportedIn D E A}
def ballPieces (K : Set (E.Pt D)) (η : ℝ) : Set (E.Pt D → ℝ) :=
  {g | g ∈ smoothSupportedIn K ∧ ∃ y ∈ K,
    (fun z => (g z : ℂ)) ∈ Tuple.singleTestFns D E (openBallAt D E y η)}
theorem cutoffTensor_update {n : ℕ+} (h : FnTuple D E (n : ℕ)) (i : Fin (n : ℕ))
    (w : E.Pt D → ℝ) (y : E.Tuple D n) :
    Tuple.cutoffTensor D E (Function.update h i w) y =
      (w (y i) : ℂ) * ∏ j ∈ Finset.univ.erase i, (h j (y j) : ℂ) := by
  classical
  unfold Tuple.cutoffTensor Tuple.tensorProd
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun j hj => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
theorem update_mem_smoothSupportedIn {n : ℕ+} {A : Fin (n : ℕ) → Set (E.Pt D)}
    {h : FnTuple D E (n : ℕ)}
    (hh : ∀ l, h l ∈ smoothSupportedIn (A l)) (i : Fin (n : ℕ)) {w : E.Pt D → ℝ}
    (hw : w ∈ smoothSupportedIn (A i)) (l : Fin (n : ℕ)) :
    Function.update h i w l ∈ smoothSupportedIn (A l) := by
  by_cases e : l = i
  · subst e
    simpa using hw
  · simpa [Function.update_of_ne e] using hh l
theorem mem_sepC1Tuples_of_smooth
    (H4 : DisjointProducts.Claim) {n : ℕ+}
    {A : Fin (n : ℕ) → Set (E.Pt D)} (hA : ∀ l l', l ≠ l' → Disjoint (A l) (A l'))
    {h : FnTuple D E (n : ℕ)} (hh : ∀ l, h l ∈ smoothSupportedIn (A l)) :
    h ∈ sepC1Tuples D E (n : ℕ) :=
  (H4 D E (n : ℕ) n.pos).2.1 A hA fun l _ => (hh l).2
theorem takesValueAt_update_zero (H4 : DisjointProducts.Claim) {n : ℕ+}
    (Ψ : sepC1Tuples D E (n : ℕ) → ℝ)
    (hΨ : IsMultilinearOn D E (sepC1Tuples D E (n : ℕ)) Ψ)
    {T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ}
    (hT : Tuple.IsDistrib T) (h : FnTuple D E (n : ℕ)) (i : Fin (n : ℕ)) :
    TakesValueAt Ψ T (Function.update h i 0) := by
  intro hφ hF
  have hS := (H4 D E (n : ℕ) n.pos).2.2.2.1 Ψ hΨ ⟨_, hφ⟩ i (by simp)
  have h0 : T ⟨_, hF⟩ = 0 := by
    have := hT.1.2 0 ⟨_, hF⟩ ⟨_, hF⟩ (by
      funext y
      simp [cutoffTensor_update])
    simpa using this
  rw [h0, hS]
  simp
theorem takesValueAt_update_add (H2 : SmoothIffSmoothAsTuple)
    (H3 : TupleFacts.AllFacts)
    (H4 : DisjointProducts.Claim) {n : ℕ+}
    (Ψ : sepC1Tuples D E (n : ℕ) → ℝ)
    (hΨ : IsMultilinearOn D E (sepC1Tuples D E (n : ℕ)) Ψ)
    {T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ}
    (hT : Tuple.IsDistrib T)
    {A : Fin (n : ℕ) → Set (E.Pt D)} (hA : ∀ l l', l ≠ l' → Disjoint (A l) (A l'))
    {h : FnTuple D E (n : ℕ)} (hh : ∀ l, h l ∈ smoothSupportedIn (A l)) (i : Fin (n : ℕ))
    {u v : E.Pt D → ℝ} (hu : u ∈ smoothSupportedIn (A i)) (hv : v ∈ smoothSupportedIn (A i))
    (gu : TakesValueAt Ψ T (Function.update h i u))
    (gv : TakesValueAt Ψ T (Function.update h i v)) :
    TakesValueAt Ψ T (Function.update h i (u + v)) := by
  intro hφ hF
  have sepU := mem_sepC1Tuples_of_smooth H4 hA (update_mem_smoothSupportedIn hh i hu)
  have sepV := mem_sepC1Tuples_of_smooth H4 hA (update_mem_smoothSupportedIn hh i hv)
  have FU := cutoffTensor_mem H2 H3 sepU fun l => (update_mem_smoothSupportedIn hh i hu l).1
  have FV := cutoffTensor_mem H2 H3 sepV fun l => (update_mem_smoothSupportedIn hh i hv l).1
  have lin := hT.1.1 ⟨_, FU⟩ ⟨_, FV⟩ ⟨_, hF⟩ (by
    funext y
    simp only [Pi.add_apply, cutoffTensor_update]
    push_cast
    ring)
  have e : (1 : ℝ) • u + (1 : ℝ) • v = u + v := by simp
  have hw : Function.update h i ((1 : ℝ) • u + (1 : ℝ) • v) ∈ sepC1Tuples D E (n : ℕ) := by
    rw [e]
    exact hφ
  have nl := ((H4 D E (n : ℕ) n.pos).2.2.1 Ψ hΨ A hA).2
    h (fun l _ => (hh l).2) i u hu.2 v hv.2 1 1 sepU sepV hw
  have e2 : Ψ ⟨_, hφ⟩ = Ψ ⟨_, hw⟩ :=
    congrArg _ (Subtype.ext (by simp only [e]))
  rw [lin, gu sepU FU, gv sepV FV, e2, nl]
  push_cast
  ring
theorem takesValueAt_of_balls {n : ℕ+} (Ψ : sepC1Tuples D E (n : ℕ) → ℝ) (hn : 2 ≤ (n : ℕ))
    {T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ}
    (hT : RestrictsToFamilyDistribs Ψ T) {η d : ℝ} {c : E.Tuple D n}
    (hadm : AdmissibleWith D E η d fun i => openBallAt D E (c i) η)
    {h : FnTuple D E (n : ℕ)}
    (hm : ∀ l, (fun z => (h l z : ℂ)) ∈
      Tuple.singleTestFns D E (openBallAt D E (c l) η)) :
    TakesValueAt Ψ T h := by
  intro _ _
  obtain ⟨hsub, -, hval⟩ := hT.2 _ ⟨η, d, hn, hadm⟩
  obtain ⟨_, _, e⟩ := hval h hm
  exact e
theorem exists_ball_pieces (H2 : SmoothIffSmoothAsTuple)
    (H3 : TupleFacts.AllFacts)
    (H5 : PeriodicSpace.PartitionsOfUnity.Statement)
    {K : Set (E.Pt D)} (hK : IsCompactQ D E K) (hne : K.Nonempty) {η : ℝ} (hη : 0 < η)
    (hopen : ∀ y ∈ K, IsOpenQ D E (openBallAt D E y η))
    {u : E.Pt D → ℝ} (hu : IsSmoothFn D E u) (hsupp : supportQ D E u ⊆ K) :
    ∃ (r : ℕ) (g : Fin r → E.Pt D → ℝ), (∀ a, g a ∈ ballPieces K η) ∧ u = ∑ a, g a := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, hprod, hproj, -, -, -, htwo, -, -, hstable, -⟩ :=
    H3 D E 1
  have hself : ∀ y : E.Pt D, y ∈ openBallAt D E y η := fun y =>
    lt_of_le_of_lt (quotDist_self_nonpos H3 y) hη
  obtain ⟨V, hV, hfin, hcov⟩ := hK {B | ∃ y ∈ K, B = openBallAt D E y η}
    (by
      rintro _ ⟨y, hy, rfl⟩
      exact hopen y hy)
    (fun y hy => ⟨_, ⟨y, hy, rfl⟩, hself y⟩)
  have : Finite V := hfin
  obtain ⟨m, ⟨e⟩⟩ := Finite.exists_equiv_fin V
  have hm : 0 < m := by
    obtain ⟨y, hy⟩ := hne
    obtain ⟨B, hB, -⟩ := hcov hy
    exact (e ⟨B, hB⟩).pos
  obtain ⟨r, rfl⟩ : ∃ r : ℕ+, (r : ℕ) = m := ⟨⟨m, hm⟩, rfl⟩
  have hc : ∀ a : Fin (r : ℕ), ∃ y ∈ K, (e.symm a).1 = openBallAt D E y η :=
    fun a => hV (e.symm a).2
  choose c hcK hcB using hc
  have hW : ∀ a, Tuple.IsOpenT D E
      (Tuple.singleSet D E (openBallAt D E (c a) η)) := fun a => by
    rw [singleSet_eq_boxSet]
    exact (hprod _).1 fun _ => hopen _ (hcK a)
  have hK1 : Tuple.IsCompactT D E (Tuple.singleSet D E K) := by
    rw [singleSet_eq_boxSet]
    exact (hprod _).2.2 fun _ => hK
  have hcov1 : Tuple.singleSet D E K ⊆
      ⋃ a, Tuple.singleSet D E (openBallAt D E (c a) η) := by
    intro y hy
    obtain ⟨B, hB, hyB⟩ := hcov hy
    refine Set.mem_iUnion.2 ⟨e ⟨B, hB⟩, ?_⟩
    show y ⟨0, (1 : ℕ+).pos⟩ ∈ openBallAt D E (c (e ⟨B, hB⟩)) η
    rw [← hcB]
    simpa using hyB
  obtain ⟨φ, hφ, hvals, N, -, hKN, hsum⟩ := (H5 D E 1).1 r _ _ hK1 hW hcov1
  have hρ : ∀ a y, (((φ a fun _ => y).re : ℝ) : ℂ) = φ a fun _ => y := fun a y => by
    obtain ⟨t, -, ht⟩ := hvals a fun _ => y
    rw [ht]
    simp
  have hρ1 : ∀ a, Tuple.ofSingle D E (fun y => (((φ a fun _ => y).re : ℝ) : ℂ)) = φ a :=
    fun a => by
      funext y
      show (((φ a fun _ => y ⟨0, (1 : ℕ+).pos⟩).re : ℝ) : ℂ) = φ a y
      rw [hρ, const_fin_one]
  have hρs : ∀ a, IsSmoothFn D E fun y => (φ a fun _ => y).re := fun a =>
    (H2 D E _).2 (by
      rw [hρ1]
      exact (hφ a).1)
  have hus := (H2 D E u).1 hu
  have hgs : ∀ a, IsSmoothFn D E fun y => (φ a fun _ => y).re * u y := fun a =>
    ContDiff.mul (hρs a) hu
  have hgm : ∀ a, Tuple.ofSingle D E
      (fun y => (((φ a fun _ => y).re * u y : ℝ) : ℂ)) ∈
        Tuple.testFns D E
          (Tuple.singleSet D E (openBallAt D E (c a) η)) := fun a => by
    have h1 := ((hstable _ (hW a)).2 (φ a) (hφ a)).2.2.2.1 _ hus
    have h2 : Tuple.ofSingle D E
        (fun y => (((φ a fun _ => y).re * u y : ℝ) : ℂ)) =
          Tuple.ofSingle D E (fun y => (u y : ℂ)) * φ a := by
      funext y
      have h3 := congrFun (hρ1 a) y
      rw [Pi.mul_apply, ← h3]
      simp only [Tuple.ofSingle]
      push_cast
      ring
    rw [h2]
    exact h1
  refine ⟨r, fun a y => (φ a fun _ => y).re * u y, fun a => ⟨⟨hgs a, ?_, ?_, ?_⟩, c a, hcK a, hgm a⟩,
    ?_⟩
  · exact isC1Fn_of_isSmoothFn (hgs a)
  · have h1 := (hgm a).2.1
    have hC1 := isC1Fn_of_isSmoothFn (hgs a)
    rw [((htwo _).2 hC1).2] at h1
    have h2 := (hproj ⟨0, (1 : ℕ+).pos⟩).2 _ h1
    have h3 : (fun y : E.Tuple D 1 => y ⟨0, (1 : ℕ+).pos⟩) ''
        Tuple.singleSet D E (supportQ D E fun y => (φ a fun _ => y).re * u y) =
          supportQ D E fun y => (φ a fun _ => y).re * u y := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact hz
      · intro hy
        exact ⟨fun _ => y, hy, rfl⟩
    rw [h3] at h2
    exact h2
  · refine Set.Subset.trans ?_ hsupp
    intro y hy r hr
    obtain ⟨z, hz, hd⟩ := hy r hr
    exact ⟨z, fun h0 => hz (by simp [h0]), hd⟩
  · funext y
    rw [Finset.sum_apply]
    by_cases hy : u y = 0
    · simp [hy]
    · have hyK := hsupp (mem_supportQ_of_ne H3 hy)
      have h1 := hsum (fun _ => y) (hKN hyK)
      have h2 : ∑ a, (φ a fun _ => y).re = 1 := by
        have h3 : ((∑ a, (φ a fun _ => y).re : ℝ) : ℂ) = 1 := by
          rw [Complex.ofReal_sum]
          exact (Finset.sum_congr rfl fun a _ => hρ a y).trans h1
        exact_mod_cast h3
      rw [← Finset.sum_mul, h2, one_mul]
theorem exists_uniform_sep (H4 : DisjointProducts.Claim) {n : ℕ+}
    {A : Fin (n : ℕ) → Set (E.Pt D)} (hK : ∀ l, IsCompactQ D E (A l))
    (hA : ∀ l l', l ≠ l' → Disjoint (A l) (A l')) (hne : ∀ l, (A l).Nonempty) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i k, i ≠ k → ∀ y ∈ A i, ∀ y' ∈ A k, δ ≤ quotDist D E y y' := by
  classical
  have hd := (H4 D E (n : ℕ) n.pos).2.2.2.2
  have pair : ∀ i k, ∃ δ : ℝ, 0 < δ ∧
      (i ≠ k → ∀ y ∈ A i, ∀ y' ∈ A k, δ ≤ quotDist D E y y') := by
    intro i k
    by_cases e : i = k
    · exact ⟨1, one_pos, fun h => absurd e h⟩
    · obtain ⟨h0, h1⟩ := hd _ _ (hK i) (hK k) (hA i k e) (hne i) (hne k)
      refine ⟨(setInfDist D E (A i) (A k)).toReal, ENNReal.toReal_pos h0.ne' h1.ne,
        fun _ y hy y' hy' => ?_⟩
      have h2 : setInfDist D E (A i) (A k) ≤ ENNReal.ofReal (quotDist D E y y') :=
        iInf₂_le_of_le y hy (iInf₂_le y' hy')
      have h3 : 0 < quotDist D E y y' := ENNReal.ofReal_pos.1 (lt_of_lt_of_le h0 h2)
      exact ENNReal.toReal_le_of_le_ofReal h3.le h2
  choose δ hδ hsep using pair
  have hP : (Finset.univ : Finset (Fin (n : ℕ) × Fin (n : ℕ))).Nonempty :=
    ⟨(⟨0, n.pos⟩, ⟨0, n.pos⟩), Finset.mem_univ _⟩
  refine ⟨Finset.univ.inf' hP fun p => δ p.1 p.2,
    (Finset.lt_inf'_iff hP).2 fun p _ => hδ _ _, fun i k e y hy y' hy' => ?_⟩
  exact le_trans (Finset.inf'_le (fun p : Fin (n : ℕ) × Fin (n : ℕ) => δ p.1 p.2)
    (Finset.mem_univ (i, k))) (hsep i k e y hy y' hy')
theorem agreesOnSmoothTensors (H1 : AdmissibleProductFacts)
    (H2 : SmoothIffSmoothAsTuple)
    (H3 : TupleFacts.AllFacts)
    (H4 : DisjointProducts.Claim)
    (H5 : PeriodicSpace.PartitionsOfUnity.Statement) {n : ℕ+} (hn : 2 ≤ (n : ℕ))
    (Ψ : sepC1Tuples D E (n : ℕ) → ℝ)
    (hΨ : IsMultilinearOn D E (sepC1Tuples D E (n : ℕ)) Ψ)
    {T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ}
    (hT : RestrictsToFamilyDistribs Ψ T) : AgreesOnSmoothTensors Ψ T := by
  intro f hf hs
  have hF := cutoffTensor_mem H2 H3 hf hs
  refine ⟨hF, ?_⟩
  suffices hg : TakesValueAt Ψ T f from hg hf hF
  have hdisj : ∀ l l', l ≠ l' → Disjoint (supportQ D E (f l)) (supportQ D E (f l')) := hf.2.2
  by_cases hz : ∃ i, f i = 0
  · obtain ⟨i, hi⟩ := hz
    have e : Function.update f i 0 = f := by
      rw [← hi]
      exact Function.update_eq_self _ _
    have h1 := takesValueAt_update_zero H4 Ψ hΨ hT.1 f i
    rwa [e] at h1
  have hne : ∀ l, (supportQ D E (f l)).Nonempty := fun l => by
    have h0 : f l ≠ 0 := fun h => hz ⟨l, h⟩
    obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
    exact ⟨y, mem_supportQ_of_ne H3 hy⟩
  obtain ⟨δ, hδ, hsep⟩ := exists_uniform_sep H4 hf.2.1 hdisj hne
  obtain ⟨η, hη, hadm⟩ := (H1 D E n).2.2.1 δ hδ
  have hadm' : ∀ c : E.Tuple D n, (∀ i, c i ∈ supportQ D E (f i)) →
      AdmissibleWith D E η (δ / 3) fun i => openBallAt D E (c i) η := fun c hc =>
    hadm c fun i k e => hsep i k e _ (hc i) _ (hc k)
  choose c₀ hc₀ using hne
  have hopen : ∀ l, ∀ y ∈ supportQ D E (f l), IsOpenQ D E (openBallAt D E y η) := by
    classical
    intro l y hy
    have h1 := (hadm' (Function.update c₀ l y) fun i => by
      by_cases e : i = l
      · subst e
        simpa using hy
      · simpa [Function.update_of_ne e] using hc₀ i).isOpen_mem l
    simpa using h1
  have hpieces := fun l => exists_ball_pieces H2 H3 H5 (hf.2.1 l) ⟨_, hc₀ l⟩ hη (hopen l) (hs l)
    subset_rfl
  choose r g hg hsum using hpieces
  refine prop_of_finite_sums (fun l => smoothSupportedIn (supportQ D E (f l)))
    (fun l => ballPieces (supportQ D E (f l)) η) (TakesValueAt Ψ T) (fun l _ hp => hp.1)
    ?_ ?_ (fun h _ i => takesValueAt_update_zero H4 Ψ hΨ hT.1 h i)
    (fun h hh i u v hu hv gu gv =>
      takesValueAt_update_add H2 H3 H4 Ψ hΨ hT.1 hdisj hh i hu hv gu gv)
    ?_ f r g hg hsum
  · intro l
    obtain ⟨Wl, hWl⟩ := (H4 D E (n : ℕ) n.pos).1.1 (supportQ D E (f l))
    refine ⟨contDiff_const, ?_⟩
    rw [← hWl]
    exact Wl.zero_mem
  · intro l u v hu hv
    obtain ⟨Wl, hWl⟩ := (H4 D E (n : ℕ) n.pos).1.1 (supportQ D E (f l))
    refine ⟨ContDiff.add hu.1 hv.1, ?_⟩
    have hu2 := hu.2
    have hv2 := hv.2
    rw [← hWl] at hu2 hv2 ⊢
    exact Wl.add_mem hu2 hv2
  · intro h hh
    have hc : ∀ l, ∃ y ∈ supportQ D E (f l),
        (fun z => (h l z : ℂ)) ∈ Tuple.singleTestFns D E (openBallAt D E y η) :=
      fun l => (hh l).2
    choose c hcA hcm using hc
    exact takesValueAt_of_balls Ψ hn hT (hadm' c hcA) hcm
theorem restricts_of_agrees (points : AdmissibleProductFacts)
    (facts : PeriodicSpace.LiftsProductsDistributions.Statement)
    (two : SmoothIffSmoothAsTuple) {n : ℕ+}
    {Ψ : sepC1Tuples D E (n : ℕ) → ℝ}
    {T T' : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ}
    (hT : RestrictsToFamilyDistribs Ψ T) (hT' : Tuple.IsDistrib T')
    (hval : AgreesOnSmoothTensors Ψ T') : RestrictsToFamilyDistribs Ψ T' := by
  refine ⟨hT', fun G hG => ?_⟩
  obtain ⟨h, hfam⟩ := hT.2 G hG
  obtain ⟨hopenAll, hprod, -, -, -⟩ := points D E n
  obtain ⟨R, d, -, hRd⟩ := hG
  refine ⟨h, ?_, fun φ hφ => ?_⟩
  · exact ((facts D E).2.2.2.2.2.1 n _ _ (hprod G ⟨R, d, hRd⟩).1 hopenAll h T' hT').2.1
  · obtain ⟨hsep, hF, -⟩ := hfam.2 φ hφ
    have hsmooth : ∀ i, IsSmoothFn D E (φ i) := fun i => (two D E (φ i)).2 (hφ i).1
    obtain ⟨hF', hval'⟩ := hval φ hsep hsmooth
    exact ⟨hsep, hF, hval'⟩
theorem actFns_comp {n : ℕ+} {Z Z' : Type*} (c : Z → Z') (ψ : ExtendedTupleMap D E n)
    (f : Fin (n : ℕ) → E.Pt D → Z) :
    ψ.actFns (fun i y => c (f i y)) = fun i y => c (ψ.actFns f i y) := by
  cases ψ with
  | ofTupleMap ψ₀ => cases ψ₀ <;> rfl
  | ofIsometry s hs => rfl
theorem invariantDistrib
    (maps : ExtendedTupleMapFacts.MainProperties) {n : ℕ+}
    (hn : 2 ≤ (n : ℕ)) {Ψ : sepC1Tuples D E (n : ℕ) → ℝ}
    {T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ}
    (hT : Tuple.IsDistrib T) (values : AgreesOnSmoothTensors Ψ T)
    (only : ∀ T', Tuple.IsDistrib T' → AgreesOnSmoothTensors Ψ T' → T' = T)
    (ψ : ExtendedTupleMap D E n) (hψ : ψ.InvariantFunctional Ψ) : ψ.InvariantDistrib T := by
  obtain ⟨-, hall⟩ := maps D E n hn
  obtain ⟨-, ⟨-, hl, -⟩, -, ⟨-, hinv⟩, -, -, -, -, ⟨hsepψ, -⟩, ⟨ht, -, -, hform⟩, -⟩ := hall ψ
  obtain ⟨-, ⟨-, hl', -⟩, -, ⟨htens', hinv'⟩, -, -, -, -, ⟨hsep', hsm'⟩, -, -⟩ :=
    hall ψ.sameKindInv
  have hpts : ψ.sameKindInv.sameKindInv.actPts = ψ.actPts := by
    funext y
    have h := hl' (ψ.actPts y)
    rwa [hl y] at h
  have hback : ∀ h : FnTuple D E (n : ℕ), ψ.actFns (ψ.sameKindInv.actFns h) = h := by
    intro h
    have h1 := hinv ℝ (ψ.sameKindInv.actFns h)
    have h2 := hinv' ℝ (ψ.actFns (ψ.sameKindInv.actFns h))
    rw [h1] at h2
    rw [← h2, hinv' ℝ h]
  have hdist := (hform T).1 hT
  have hval : AgreesOnSmoothTensors Ψ fun F => T ⟨_, ht F⟩ := by
    intro h hh hsm
    obtain ⟨hFh, -⟩ := values h hh hsm
    have hf := hsep' h hh
    obtain ⟨hFf, hv⟩ := values _ hf (hsm' h hsm)
    refine ⟨hFh, ?_⟩
    have htensor : Tuple.tensorProd D E
        (fun i y => ((ψ.sameKindInv.actFns h i y : ℝ) : ℂ)) =
        Tuple.tensorProd D E (fun i y => ((h i y : ℝ) : ℂ)) ∘ ψ.actPts := by
      have h1 := (htens' fun i y => ((h i y : ℝ) : ℂ))
      rw [hpts, actFns_comp (fun x : ℝ => (x : ℂ)) ψ.sameKindInv h] at h1
      exact h1
    have hkeep := hψ ⟨_, hf⟩ (hsepψ _ hf)
    have hT1 : T ⟨_, ht ⟨_, hFh⟩⟩ = T ⟨_, hFf⟩ :=
      congrArg T (Subtype.ext htensor.symm)
    refine hT1.trans (hv.trans ?_)
    rw [← hkeep]
    exact congrArg _ (congrArg Ψ (Subtype.ext (hback h)))
  have he := only _ hdist hval
  intro F hF
  exact congrFun he F
end SharpBoundedParts
open SharpBoundedParts in
theorem Tuple.SharpBoundedIsDistrib.proof
    (hChart : AdmissibleCharts.Claim)
    (hForm : Tuple.C1BoundedFormDistribution)
    (hDense : TensorSpanDenseOnBoxes)
    (hFacts : PeriodicSpace.LiftsProductsDistributions.Statement)
    (hProd : DisjointProducts.Claim)
    (hPts : TupleFacts.AllFacts)
    (hOpen : AdmissibleProductFacts)
    (hGlue : Tuple.DistribGluing.Statement)
    (hTwo : SmoothIffSmoothAsTuple)
    (hUnity : PeriodicSpace.PartitionsOfUnity.Statement)
    (hMaps : ExtendedTupleMapFacts.MainProperties) :
    Tuple.SharpBoundedIsDistrib.Statement := by
  intro D E n hn Ψ c hΨ hc hbound
  have parts : ∀ (R d : ℝ) (G : Fin (n : ℕ) → Set (E.Pt D)),
      AdmissibleWith D E R d G → Tuple.SeparatedFamilyDistribSpec c Ψ R d G := by
    intro R d G hG
    by_cases h : ∃ i, G i = ∅
    · exact spec_of_empty_member hPts hProd c hΨ hG h
    · exact spec_of_nonempty hChart hForm hDense hFacts hProd hPts hΨ hc hbound hG fun i =>
        Set.nonempty_iff_ne_empty.2 fun hi => h ⟨i, hi⟩
  have exU : ∀ G : Fin (n : ℕ) → Set (E.Pt D), Admissible D E G →
      ∃! T, Tuple.IsFamilyDistrib Ψ G T := by
    rintro G ⟨R, d, hG⟩
    exact (parts R d G hG).1
  have ord : ∀ G : Fin (n : ℕ) → Set (E.Pt D), Admissible D E G →
      ∀ T, Tuple.IsFamilyDistrib Ψ G T →
        Tuple.IsDistribOfOrderLE (5 * (n : ℕ) + 1) T := by
    rintro G ⟨R, d, hG⟩ T hT
    exact ((parts R d G hG).2.2.2.2 T hT).1
  obtain ⟨hDistinct, hProducts, -⟩ := hOpen D E n
  obtain ⟨hExists, hOrder⟩ := glue_family_distribs hFacts hOpen hGlue hn Ψ exU ord
  refine ⟨fun R d G hG => parts R d G hG.2, hDistinct, ?_, hExists, fun T hT => ?_⟩
  · rintro G ⟨R, d, -, hG⟩
    exact hProducts G ⟨R, d, hG⟩
  · have hvals := agreesOnSmoothTensors hOpen hTwo hPts hProd hUnity hn Ψ hΨ hT
    have honly : ∀ T', Tuple.IsDistrib T' →
        Tuple.AgreesOnSmoothTensors Ψ T' → T' = T := fun T' hT' hv =>
      hExists.unique (restricts_of_agrees hOpen hFacts hTwo hT hT' hv) hT
    exact ⟨hOrder T hT, hvals, honly, fun ψ hψ => invariantDistrib hMaps hn hT.1 hvals honly ψ hψ⟩
end YangMills.Construction.PeriodicSpace.Kind
