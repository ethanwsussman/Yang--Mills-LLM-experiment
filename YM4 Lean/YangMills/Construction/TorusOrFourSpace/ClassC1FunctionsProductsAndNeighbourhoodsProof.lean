import YangMills.Construction.TorusOrFourSpace.ClassC1FunctionsProductsAndNeighbourhoods
import YangMills.Construction.TorusOrFourSpace.ClassesAreVectorSpacesWithTheSharpNormProof
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace
open Kind
namespace C1ProductsAndThickenings
theorem closureWrt_isClosedWrt {X : Type*} {d : X → X → ℝ}
    (tri : ∀ x y z, d x z ≤ d x y + d y z) (Z : Set X) :
    MetricNotions.IsClosedWrt d (MetricNotions.closureWrt d Z) := by apply _root_.YangMills.SharedProofs.p11892 <;> assumption
theorem isCompactWrt_of_isClosedWrt_subset {X : Type*} {d : X → X → ℝ} {K T : Set X}
    (hK : MetricNotions.IsCompactWrt d K) (hT : MetricNotions.IsClosedWrt d T)
    (hTK : T ⊆ K) : MetricNotions.IsCompactWrt d T := by apply _root_.YangMills.SharedProofs.p5019 <;> assumption
theorem bestLipschitzConstant_spec {X : Type*} {d : X → X → ℝ} (hd0 : ∀ x y, 0 ≤ d x y)
    (hd : ∀ x y, d x y = 0 → x = y) {u : X → ℝ} (hu : TestFunctions.IsLipschitzFor d u) :
    0 ≤ TestFunctions.bestLipschitzConstant d u ∧
      ∀ x y, |u x - u y| ≤ TestFunctions.bestLipschitzConstant d u * d x y := by
  have h0 : 0 ≤ TestFunctions.bestLipschitzConstant d u := Real.sInf_nonneg fun C hC => hC.1
  refine ⟨h0, fun x y => ?_⟩
  rcases (hd0 x y).eq_or_lt with h | h
  · rw [hd x y h.symm, sub_self, abs_zero]
    exact mul_nonneg h0 (hd0 _ _)
  · have hle : |u x - u y| / d x y ≤ TestFunctions.bestLipschitzConstant d u := by
      obtain ⟨C₀, hC₀⟩ := hu
      refine le_csInf ⟨C₀, hC₀⟩ fun C hC => ?_
      rw [div_le_iff₀ h]
      simpa [Real.norm_eq_abs] using hC.2 x y
    exact (div_le_iff₀ h).1 hle
variable (D : Params) (E : Kind)
variable {D E} in
theorem infDistPt_lt_iff {y : E.Pt D} {S : Set (E.Pt D)} {a : ℝ≥0∞} :
    infDistPt D E y S < a ↔ ∃ z ∈ S, ENNReal.ofReal (quotDist D E y z) < a := by
  simp [infDistPt, setInfDist, iInf_lt_iff]
variable {D E} in
theorem infDistPt_le_of_mem {y z : E.Pt D} {S : Set (E.Pt D)} (hz : z ∈ S) :
    infDistPt D E y S ≤ ENNReal.ofReal (quotDist D E y z) :=
  iInf₂_le_of_le y (Set.mem_singleton y) (iInf₂_le z hz)
variable {D E} in
theorem exists_mem_quotDist_lt_add {y : E.Pt D} {S : Set (E.Pt D)} {η ε : ℝ} (hη : 0 < η)
    (h : infDistPt D E y S ≤ ENNReal.ofReal η) (hε : 0 < ε) :
    ∃ z ∈ S, quotDist D E y z < η + ε := by
  have hpos : 0 < η + ε := by linarith
  have h1 : ENNReal.ofReal η < ENNReal.ofReal (η + ε) :=
    (ENNReal.ofReal_lt_ofReal_iff hpos).2 (by linarith)
  obtain ⟨z, hz, hlt⟩ := infDistPt_lt_iff.1 (lt_of_le_of_lt h h1)
  exact ⟨z, hz, (ENNReal.ofReal_lt_ofReal_iff hpos).1 hlt⟩
theorem c1CompactSupportLipschitz_holds
    (hC : QuotientCompactC1.CompactSupportC1Facts D E) :
    C1CompactSupportLipschitz D E := by
  have main : ∀ g ∈ c1Set D E, IsCompactQ D E (supportQ D E g) → IsLipschitzQ D E g :=
    fun g hg hs => (hC g hg hs).2.2.2.2.1
  refine ⟨fun g hg hs => ?_, fun A h hh => ⟨main h hh.1 hh.2.1, hh.2.1, hh.2.2⟩,
    fun n _ f hf => ⟨fun i => main (f i) (hf.1 i) (hf.2.1 i), hf.2⟩⟩
  obtain ⟨-, -, hfin, hlip, hL, hconst, -, hsharp⟩ := hC g hg hs
  have hV : vecSupNormQ D E (gradVec D E g) < ∞ :=
    lt_of_le_of_lt (show vecSupNormQ D E (gradVec D E g) ≤ euclidC1Norm D E g from
      le_max_right _ _) hfin
  refine ⟨fun x y => ?_, hL, hconst.le, hV, hsharp⟩
  calc ENNReal.ofReal |g x - g y|
      ≤ ENNReal.ofReal ((vecSupNormQ D E (gradVec D E g)).toReal * quotDist D E x y) :=
        ENNReal.ofReal_le_ofReal (hlip x y)
    _ = vecSupNormQ D E (gradVec D E g) * ENNReal.ofReal (quotDist D E x y) := by
        rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hV.ne]
theorem lipschitzCutoffProductMem_holds
    (hM : QuotientCompactC1.QuotDistIsMetricWithLifts D E)
    (hB : VectorClasses.BoundedAndSharpNorm D E) :
    LipschitzCutoffProductMem D E := by
  intro χ hχ hχL A h hh
  obtain ⟨hd0, hd, -, htri, -, -⟩ := hM
  obtain ⟨hhL, hhK, hhA⟩ := hh
  have hV : h ∈ lipschitzSupportedIn D E Set.univ := ⟨hhL, hhK, Set.subset_univ _⟩
  have hfin : sharpNormQ D E h < ∞ := hB.2.lt_top h hV
  obtain ⟨s, hs⟩ : ∃ s, s = (sharpNormQ D E h).toReal := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := hs ▸ ENNReal.toReal_nonneg
  have hsup : ∀ y, |h y| ≤ s := fun y => by
    have h1 : ENNReal.ofReal |h y| ≤ sharpNormQ D E h :=
      le_trans (le_iSup (fun y => ENNReal.ofReal |h y|) y) (le_max_left _ _)
    rw [hs]
    exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 h1
  have hbound : ∀ {u : E.Pt D → ℝ}, IsLipschitzQ D E u → 0 ≤ lipConstQ D E u ∧
      ∀ x y, |u x - u y| ≤ lipConstQ D E u * quotDist D E x y :=
    fun hu => bestLipschitzConstant_spec hd0 (fun x y e => (hd x y).1 e) hu
  obtain ⟨ha0, ha⟩ := hbound hhL
  obtain ⟨hb0, hb⟩ := hbound hχL
  obtain ⟨a, hadef⟩ : ∃ a, a = lipConstQ D E h := ⟨_, rfl⟩
  obtain ⟨b, hbdef⟩ : ∃ b, b = lipConstQ D E χ := ⟨_, rfl⟩
  rw [← hadef] at ha0 ha
  rw [← hbdef] at hb0 hb
  have hsa : 40 * D.M * a ≤ s := by
    have h1 : ENNReal.ofReal (40 * D.M * lipConstQ D E h) ≤ sharpNormQ D E h :=
      le_max_right _ _
    rw [hs, hadef]
    exact (ENNReal.ofReal_le_iff_le_toReal hfin.ne).1 h1
  have hM0 : 0 ≤ 40 * D.M := by
    have := D.one_le_M
    linarith
  have hprod : ∀ x y, ‖(χ * h) x - (χ * h) y‖ ≤ (a + s * b) * quotDist D E x y := by
    intro x y
    have hdxy := hd0 x y
    have e : (χ * h) x - (χ * h) y = χ x * (h x - h y) + (χ x - χ y) * h y := by
      simp only [Pi.mul_apply]
      ring
    have hχx : |χ x| ≤ 1 := by
      rw [abs_of_nonneg (hχ x).1]
      exact (hχ x).2
    have t1 : |χ x * (h x - h y)| ≤ a * quotDist D E x y := by
      rw [abs_mul]
      calc |χ x| * |h x - h y| ≤ 1 * |h x - h y| :=
            mul_le_mul_of_nonneg_right hχx (abs_nonneg _)
        _ ≤ a * quotDist D E x y := by
            rw [one_mul]
            exact ha x y
    have t2 : |(χ x - χ y) * h y| ≤ s * b * quotDist D E x y := by
      rw [abs_mul]
      calc |χ x - χ y| * |h y| ≤ (b * quotDist D E x y) * s :=
            mul_le_mul (hb x y) (hsup y) (abs_nonneg _) (mul_nonneg hb0 hdxy)
        _ = s * b * quotDist D E x y := by ring
    rw [Real.norm_eq_abs, e]
    calc |χ x * (h x - h y) + (χ x - χ y) * h y|
        ≤ |χ x * (h x - h y)| + |(χ x - χ y) * h y| := abs_add_le _ _
      _ ≤ a * quotDist D E x y + s * b * quotDist D E x y := add_le_add t1 t2
      _ = (a + s * b) * quotDist D E x y := by ring
  have hC0 : 0 ≤ a + s * b := add_nonneg ha0 (mul_nonneg hs0 hb0)
  have hLip : IsLipschitzQ D E (χ * h) := ⟨a + s * b, hC0, hprod⟩
  have hconst : lipConstQ D E (χ * h) ≤ a + s * b :=
    csInf_le ⟨0, fun C hC => hC.1⟩ ⟨hC0, hprod⟩
  have hsub : supportQ D E (χ * h) ⊆ supportQ D E χ ∩ supportQ D E h := by
    intro x hx
    refine ⟨fun r hr => ?_, fun r hr => ?_⟩
    · obtain ⟨y, hy, hxy⟩ := hx r hr
      exact ⟨y, fun e => hy (by simp [e]), hxy⟩
    · obtain ⟨y, hy, hxy⟩ := hx r hr
      exact ⟨y, fun e => hy (by simp [e]), hxy⟩
  have hclosed : IsClosedQ D E (supportQ D E (χ * h)) := closureWrt_isClosedWrt htri _
  have hcomp : IsCompactQ D E (supportQ D E (χ * h)) :=
    isCompactWrt_of_isClosedWrt_subset hhK hclosed fun x hx => (hsub hx).2
  have hsubA : supportQ D E (χ * h) ⊆ A ∩ supportQ D E χ :=
    fun x hx => ⟨hhA (hsub hx).2, (hsub hx).1⟩
  refine ⟨⟨hLip, hcomp, hsubA⟩, ?_, fun hc1 hh1 => ⟨?_, hcomp, hsubA⟩⟩
  · have hnn : 0 ≤ 1 + 40 * D.M * lipConstQ D E χ := by
      rw [← hbdef]
      have := mul_nonneg hM0 hb0
      linarith
    have hR : ENNReal.ofReal (1 + 40 * D.M * lipConstQ D E χ) * sharpNormQ D E h =
        ENNReal.ofReal ((1 + 40 * D.M * b) * s) := by
      rw [hs, hbdef, ENNReal.ofReal_mul hnn, ENNReal.ofReal_toReal hfin.ne]
    have hcoef : s ≤ (1 + 40 * D.M * b) * s := by
      have := mul_nonneg (mul_nonneg hM0 hb0) hs0
      nlinarith
    rw [hR]
    refine max_le (iSup_le fun y => ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_le_ofReal ?_)
    · rw [Pi.mul_apply, abs_mul, abs_of_nonneg (hχ y).1]
      calc χ y * |h y| ≤ 1 * |h y| := mul_le_mul_of_nonneg_right (hχ y).2 (abs_nonneg _)
        _ ≤ s := by
            rw [one_mul]
            exact hsup y
        _ ≤ (1 + 40 * D.M * b) * s := hcoef
    · calc 40 * D.M * lipConstQ D E (χ * h) ≤ 40 * D.M * (a + s * b) :=
            mul_le_mul_of_nonneg_left hconst hM0
        _ = 40 * D.M * a + 40 * D.M * b * s := by ring
        _ ≤ s + 40 * D.M * b * s := by linarith
        _ = (1 + 40 * D.M * b) * s := by ring
  · exact ContDiff.mul (show ContDiff ℝ 1 (χ ∘ quotMap D E) from hc1)
      (show ContDiff ℝ 1 (h ∘ quotMap D E) from hh1.1)
variable {D E} in
theorem closedThickening_isClosedQ
    (hM : QuotientCompactC1.QuotDistIsMetricWithLifts D E)
    (S : Set (E.Pt D)) (hS : IsCompactQ D E S) (η : ℝ) (hη : 0 < η) :
    IsClosedQ D E (closedThickening D E S hS η hη) := by
  obtain ⟨-, -, -, htri, -, -⟩ := hM
  intro y hy
  have hy' : ENNReal.ofReal η < infDistPt D E y S := not_le.1 hy
  obtain ⟨c, hc0, hc1, hc2⟩ := ENNReal.lt_iff_exists_real_btwn.1 hy'
  have hηc : η < c := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hη.le).1 hc1
  refine ⟨c - η, by linarith, fun y' hyy' hmem => ?_⟩
  have hε : 0 < c - η - quotDist D E y y' := by linarith
  obtain ⟨z, hz, hzd⟩ := exists_mem_quotDist_lt_add hη hmem hε
  have h1 := htri y y' z
  have h2 : infDistPt D E y S ≤ ENNReal.ofReal c :=
    (infDistPt_le_of_mem hz).trans (ENNReal.ofReal_le_ofReal (by linarith))
  exact absurd (lt_of_le_of_lt h2 hc2) (lt_irrefl _)
variable {D E} in
theorem closedThickening_subset_closedBallAbout
    (hM : QuotientCompactC1.QuotDistIsMetricWithLifts D E)
    (S : Set (E.Pt D)) (hS : IsCompactQ D E S) (η : ℝ) (hη : 0 < η) (ρ : ℝ≥0∞)
    (hρ : ρ < ∞) (hSρ : S ⊆ centredBall D E ρ) :
    closedThickening D E S hS η hη ⊆ closedBallAbout D E (origin D E) (ρ.toReal + η) := by
  obtain ⟨-, -, -, htri, -, -⟩ := hM
  intro y hy
  show quotDist D E y (origin D E) ≤ ρ.toReal + η
  refine le_of_forall_pos_le_add fun ε hε => ?_
  obtain ⟨z, hz, hzd⟩ := exists_mem_quotDist_lt_add hη hy hε
  have hzρ : z ∈ centredBall D E ρ := hSρ hz
  rw [centredBall, if_neg hρ.ne] at hzρ
  have hzρ' : quotDist D E z (origin D E) < ρ.toReal := hzρ
  have h1 := htri y z (origin D E)
  linarith
theorem thickeningsOpenCompactSeparated_holds
    (hM : QuotientCompactC1.QuotDistIsMetricWithLifts D E)
    (hN : QuotientCompactC1.CompactSetsThickenings D E)
    (hbc : ∀ (x : E.Pt D) (R : ℝ), 0 < R → IsCompactQ D E (closedBallAbout D E x R))
    (hex : ∀ S : Set (E.Pt D), IsCompactQ D E S →
      ∃ ρ : ℝ≥0∞, 0 < ρ ∧ ρ < ∞ ∧ S ⊆ centredBall D E ρ) :
    ThickeningsOpenCompactSeparated D E := by
  refine ⟨?_, ?_, ?_, fun S hS η hη ρ _ hρ hSρ =>
    closedThickening_subset_closedBallAbout hM S hS η hη ρ hρ hSρ⟩
  · obtain ⟨h₀, hempty⟩ := hN.2.2.1
    refine ⟨h₀, fun η hη => ⟨hempty η hη, Set.subset_empty_iff.1 fun y hy => ?_⟩⟩
    obtain ⟨z, hz, -⟩ := exists_mem_quotDist_lt_add hη hy one_pos
    exact hz
  · intro S hS η hη
    obtain ⟨hopen, hmem⟩ := hN.2.1 S hS η hη
    refine ⟨hopen, ?_, hmem, fun y (hy : infDistPt D E y S < ENNReal.ofReal η) =>
      show infDistPt D E y S ≤ ENNReal.ofReal η from hy.le⟩
    obtain ⟨ρ, -, hρ, hSρ⟩ := hex S hS
    exact isCompactWrt_of_isClosedWrt_subset
      (hbc (origin D E) (ρ.toReal + η) (add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg hη))
      (closedThickening_isClosedQ hM S hS η hη)
      (closedThickening_subset_closedBallAbout hM S hS η hη ρ hρ hSρ)
  · intro S S' hS hS' d _ hdist η η' hη hη'
    obtain ⟨hd0, -, hsymm, htri, -, -⟩ := hM
    unfold setInfDist
    refine le_iInf₂ fun y hy => le_iInf₂ fun y' hy' => ENNReal.ofReal_le_ofReal ?_
    refine le_of_forall_pos_le_add fun ε hε => ?_
    obtain ⟨x, hx, hyx⟩ := exists_mem_quotDist_lt_add hη hy (half_pos hε)
    obtain ⟨x', hx', hyx'⟩ := exists_mem_quotDist_lt_add hη' hy' (half_pos hε)
    have h1 : ENNReal.ofReal d ≤ ENNReal.ofReal (quotDist D E x x') :=
      hdist.trans (iInf₂_le_of_le x hx (iInf₂_le x' hx'))
    have h2 : d ≤ quotDist D E x x' := (ENNReal.ofReal_le_ofReal_iff (hd0 x x')).1 h1
    have h3 := htri x y x'
    have h4 := htri y y' x'
    have h5 := hsymm x y
    linarith
theorem compactSubsetClosedBallOfDiam_holds : CompactSubsetClosedBallOfDiam D E := by
  intro S _ R hR hdiam
  rcases S.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact ⟨closedBallAbout D E (origin D E) R, ⟨hR, _, rfl⟩, Set.empty_subset _⟩
  · refine ⟨closedBallAbout D E x R, ⟨hR, _, rfl⟩, fun y hy => ?_⟩
    have h1 : ENNReal.ofReal (quotDist D E y x) ≤ setDiam D E S :=
      le_iSup₂_of_le y hy (le_iSup₂ (f := fun z' _ => ENNReal.ofReal (quotDist D E y z')) x hx)
    exact (ENNReal.ofReal_le_ofReal_iff hR.le).1 (h1.trans hdiam)
theorem statement_holds (hF : Kind.QuotientCompactC1.Claim)
    (hB : BallCompactnessAndTorusLifts)
    (hV : VectorClasses.Claim) : Statement := by
  intro D E
  obtain ⟨hM, -, -, hN, hC⟩ := hF D E
  have hb := hB D
  exact ⟨c1CompactSupportLipschitz_holds D E hC, lipschitzCutoffProductMem_holds D E hM (hV D E).2.1,
    thickeningsOpenCompactSeparated_holds D E hM hN (hb.1 E) (hb.2.2.2.2.2.2.1 E),
    compactSubsetClosedBallOfDiam_holds D E⟩
end C1ProductsAndThickenings
end YangMills.Construction.PeriodicSpace
