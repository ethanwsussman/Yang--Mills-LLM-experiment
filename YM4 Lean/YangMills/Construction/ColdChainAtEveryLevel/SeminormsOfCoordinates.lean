import YangMills.Construction.ColdChainAtEveryLevel.CriticalForAllVariationsProof
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace CoordinateSeminorms
open YangMills.Construction.BlockAverages YangMills.Construction.GaugeMap YangMills.Construction.LatticeFractionalIntegration
section Minkowski
variable {ι : Type}
theorem sqrt_sum_sq_le_add (s : Finset ι) (f g h : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hfgh : ∀ i ∈ s, f i ≤ g i + h i) :
    Real.sqrt (∑ i ∈ s, f i ^ 2) ≤ Real.sqrt (∑ i ∈ s, g i ^ 2) + Real.sqrt (∑ i ∈ s, h i ^ 2) := by
  have hg0 : 0 ≤ ∑ i ∈ s, g i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hh0 : 0 ≤ ∑ i ∈ s, h i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : ∑ i ∈ s, f i ^ 2 ≤ ∑ i ∈ s, (g i + h i) ^ 2 :=
    Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (hf i hi) (hfgh i hi) 2
  have h2 : ∑ i ∈ s, (g i + h i) ^ 2 =
      ∑ i ∈ s, g i ^ 2 + 2 * ∑ i ∈ s, g i * h i + ∑ i ∈ s, h i ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : ∑ i ∈ s, g i * h i ≤ Real.sqrt (∑ i ∈ s, g i ^ 2) * Real.sqrt (∑ i ∈ s, h i ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt s g h
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have e1 := Real.sq_sqrt hg0
  have e2 := Real.sq_sqrt hh0
  nlinarith
theorem sqrt_sqrt_sum_pow_four_le_add (s : Finset ι) (f g h : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    (hg : ∀ i ∈ s, 0 ≤ g i) (hh : ∀ i ∈ s, 0 ≤ h i) (hfgh : ∀ i ∈ s, f i ≤ g i + h i) :
    Real.sqrt (Real.sqrt (∑ i ∈ s, f i ^ 4)) ≤
      Real.sqrt (Real.sqrt (∑ i ∈ s, g i ^ 4)) + Real.sqrt (Real.sqrt (∑ i ∈ s, h i ^ 4)) := by
  set A := Real.sqrt (Real.sqrt (∑ i ∈ s, g i ^ 4)) with hA
  set Bv := Real.sqrt (Real.sqrt (∑ i ∈ s, h i ^ 4)) with hB
  have eA : A ^ 2 = Real.sqrt (∑ i ∈ s, g i ^ 4) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have eB : Bv ^ 2 = Real.sqrt (∑ i ∈ s, h i ^ 4) := Real.sq_sqrt (Real.sqrt_nonneg _)
  have t1 : Real.sqrt (∑ i ∈ s, (f i ^ 2) ^ 2) ≤ Real.sqrt (∑ i ∈ s, (g i ^ 2) ^ 2) +
      Real.sqrt (∑ i ∈ s, (h i ^ 2 + 2 * (g i * h i)) ^ 2) :=
    sqrt_sum_sq_le_add s (fun i => f i ^ 2) (fun i => g i ^ 2) (fun i => h i ^ 2 + 2 * (g i * h i))
      (fun i _ => sq_nonneg _) (fun i hi => by
        have := pow_le_pow_left₀ (hf i hi) (hfgh i hi) 2
        nlinarith)
  have t2 : Real.sqrt (∑ i ∈ s, (h i ^ 2 + 2 * (g i * h i)) ^ 2) ≤ Real.sqrt (∑ i ∈ s, (h i ^ 2) ^ 2) +
      Real.sqrt (∑ i ∈ s, (2 * (g i * h i)) ^ 2) :=
    sqrt_sum_sq_le_add s (fun i => h i ^ 2 + 2 * (g i * h i)) (fun i => h i ^ 2) (fun i => 2 * (g i * h i))
      (fun i hi => by have := mul_nonneg (hg i hi) (hh i hi); positivity) (fun i _ => le_rfl)
  have t3 : Real.sqrt (∑ i ∈ s, (2 * (g i * h i)) ^ 2) ≤ 2 * (A * Bv) := by
    have e : ∑ i ∈ s, (2 * (g i * h i)) ^ 2 = 4 * ∑ i ∈ s, g i ^ 2 * h i ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have cs : ∑ i ∈ s, g i ^ 2 * h i ^ 2 ≤
        Real.sqrt (∑ i ∈ s, (g i ^ 2) ^ 2) * Real.sqrt (∑ i ∈ s, (h i ^ 2) ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt s _ _
    have p1 : ∀ u : ι → ℝ, ∑ i ∈ s, (u i ^ 2) ^ 2 = ∑ i ∈ s, u i ^ 4 :=
      fun u => Finset.sum_congr rfl fun i _ => by ring
    rw [p1, p1, ← eA, ← eB] at cs
    rw [e]
    apply Real.sqrt_le_iff.2
    refine ⟨by positivity, ?_⟩
    nlinarith
  have p1 : ∀ u : ι → ℝ, ∑ i ∈ s, (u i ^ 2) ^ 2 = ∑ i ∈ s, u i ^ 4 :=
    fun u => Finset.sum_congr rfl fun i _ => by ring
  rw [p1] at t1
  rw [p1] at t1 t2
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  nlinarith
theorem sqrt_sq_add_sq_le_add (a a₁ a₂ b b₁ b₂ : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (h1 : a ≤ a₁ + a₂)
    (h2 : b ≤ b₁ + b₂) :
    Real.sqrt (a ^ 2 + b ^ 2) ≤ Real.sqrt (a₁ ^ 2 + b₁ ^ 2) + Real.sqrt (a₂ ^ 2 + b₂ ^ 2) := by
  have := sqrt_sum_sq_le_add (Finset.univ : Finset Bool) (fun i => if i then a else b)
    (fun i => if i then a₁ else b₁) (fun i => if i then a₂ else b₂)
    (fun i _ => by cases i <;> simp [ha, hb]) (fun i _ => by cases i <;> simp [h1, h2])
  simpa [Fintype.sum_bool] using this
end Minkowski
variable {F : BlockFrame}
theorem adjointAction_add (g : UnitQuaternion) (x y : ℍ[ℝ]) :
    adjointAction g (x + y) = adjointAction g x + adjointAction g y := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_add <;> assumption
theorem adjointAction_smul (g : UnitQuaternion) (t : ℝ) (x : ℍ[ℝ]) :
    adjointAction g (t • x) = t • adjointAction g x := by apply _root_.YangMills.Construction.BlockAverages.adjointAction_smul <;> assumption
theorem linearizedCurl_add_smul (R : F.GaugeField 0) (u v : F.Site 0 → Fin 4 → imaginaryQuaternions) (t : ℝ)
    (p : F.Site 0 × Fin 4 × Fin 4) :
    linearizedCurl R (fun x i => u x i + t • v x i) p = linearizedCurl R u p + t • linearizedCurl R v p := by
  simp only [linearizedCurl, Submodule.coe_add, Submodule.coe_smul, adjointAction_add, adjointAction_smul,
    smul_add, smul_sub]
  abel
def quarticPart (S B : Finset F.Cell) (U : ChainChart F) (w : F.SiteWeights) : ℝ :=
  Real.sqrt (Real.sqrt (∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4))
def curlPart (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) : ℝ :=
  Real.sqrt (∑ p ∈ plaquettesOver S B 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2)
def coarsePartAt (S B : Finset F.Cell) (U : ChainChart F) (w : F.SiteWeights) (j : ℕ) : ℝ :=
  Real.sqrt (∑ c ∈ bondsOver S B (j + 1), (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2)
def coarsePart (S B : Finset F.Cell) (U : ChainChart F) (w : F.SiteWeights) : ℝ :=
  Real.sqrt (∑ j ∈ Finset.range (F.top - 1), coarsePartAt S B U w j ^ 2)
theorem localNormSq_eq_parts (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    localNormSq S B R U w =
      quarticPart S B U w ^ 2 + curlPart S B R U w ^ 2 + coarsePart S B U w ^ 2 := by
  have h1 : quarticPart S B U w ^ 2 = Real.sqrt (∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4) :=
    Real.sq_sqrt (Real.sqrt_nonneg _)
  have h2 : curlPart S B R U w ^ 2 =
      ∑ p ∈ plaquettesOver S B 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 :=
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h3 : coarsePart S B U w ^ 2 = ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    unfold coarsePart
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  rw [h1, h2, h3]
  rfl
theorem localNormSq_nonneg (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    0 ≤ localNormSq S B R U w := by
  rw [localNormSq_eq_parts]
  positivity
theorem localNorm_eq_parts (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights)
    (z : F.Cell) :
    localNorm S R U w z = Real.sqrt (
      (Real.sqrt (quarticPart S (cellBall S z 3) U w ^ 2 + curlPart S (cellBall S z 3) R U w ^ 2)) ^ 2 +
        coarsePart S (cellBall S z 3) U w ^ 2) := by
  unfold localNorm
  rw [localNormSq_eq_parts, Real.sq_sqrt (by positivity)]
theorem sqrt_sum_mul_sq {ι : Type} (s : Finset ι) (c : ℝ) (hc : 0 ≤ c) (g : ι → ℝ) :
    Real.sqrt (∑ i ∈ s, (c * g i) ^ 2) = c * Real.sqrt (∑ i ∈ s, g i ^ 2) := by
  have : ∑ i ∈ s, (c * g i) ^ 2 = c ^ 2 * ∑ i ∈ s, g i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
theorem sqrt_sqrt_sum_mul_pow_four {ι : Type} (s : Finset ι) (c : ℝ) (hc : 0 ≤ c) (g : ι → ℝ) :
    Real.sqrt (Real.sqrt (∑ i ∈ s, (c * g i) ^ 4)) = c * Real.sqrt (Real.sqrt (∑ i ∈ s, g i ^ 4)) := by
  have : ∑ i ∈ s, (c * g i) ^ 4 = (c ^ 2) ^ 2 * ∑ i ∈ s, g i ^ 4 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity),
    Real.sqrt_mul (by positivity), Real.sqrt_sq hc]
theorem quarticPart_chartMove_le (S B : Finset F.Cell) (U A : ChainChart F) (t : ℝ)
    (w : F.SiteWeights) (hw : ∀ j x, 0 ≤ w j x) :
    quarticPart S B (chartMove U A t) w ≤ quarticPart S B U w + |t| * quarticPart S B A w := by
  unfold quarticPart
  rw [← sqrt_sqrt_sum_mul_pow_four _ _ (abs_nonneg t)]
  refine sqrt_sqrt_sum_pow_four_le_add _ _ _ _ (fun i _ => mul_nonneg (hw _ _) (norm_nonneg _))
    (fun i _ => mul_nonneg (hw _ _) (norm_nonneg _))
    (fun i _ => mul_nonneg (abs_nonneg _) (mul_nonneg (hw _ _) (norm_nonneg _))) ?_
  intro b _
  have h1 : ‖(chartMove U A t).fine b.1 b.2‖ ≤ ‖U.fine b.1 b.2‖ + |t| * ‖A.fine b.1 b.2‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
  have := mul_le_mul_of_nonneg_left h1 (hw 0 b.1)
  nlinarith
theorem curlPart_chartMove_le (S B : Finset F.Cell) (R : F.FieldChain) (U A : ChainChart F) (t : ℝ)
    (w : F.SiteWeights) (hw : ∀ j x, 0 ≤ w j x) :
    curlPart S B R (chartMove U A t) w ≤ curlPart S B R U w + |t| * curlPart S B R A w := by
  unfold curlPart
  rw [← sqrt_sum_mul_sq _ _ (abs_nonneg t)]
  refine sqrt_sum_sq_le_add _ _ _ _ (fun i _ => mul_nonneg (hw _ _) (norm_nonneg _)) ?_
  intro p _
  have h1 : ‖linearizedCurl (R 0) (chartMove U A t).fine p‖ ≤
      ‖linearizedCurl (R 0) U.fine p‖ + |t| * ‖linearizedCurl (R 0) A.fine p‖ := by
    have : (chartMove U A t).fine = fun x i => U.fine x i + t • A.fine x i := rfl
    rw [this, linearizedCurl_add_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
  have := mul_le_mul_of_nonneg_left h1 (hw 0 p.1)
  nlinarith
theorem coarsePartAt_chartMove_le (S B : Finset F.Cell) (U A : ChainChart F) (t : ℝ)
    (w : F.SiteWeights) (hw : ∀ j x, 0 ≤ w j x) (j : ℕ) :
    coarsePartAt S B (chartMove U A t) w j ≤ coarsePartAt S B U w j + |t| * coarsePartAt S B A w j := by
  unfold coarsePartAt
  rw [← sqrt_sum_mul_sq _ _ (abs_nonneg t)]
  refine sqrt_sum_sq_le_add _ _ _ _ (fun i _ => mul_nonneg (hw _ _) (norm_nonneg _)) ?_
  intro c _
  have h1 : ‖(chartMove U A t).coarse j c.1 c.2‖ ≤ ‖U.coarse j c.1 c.2‖ + |t| * ‖A.coarse j c.1 c.2‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
  have := mul_le_mul_of_nonneg_left h1 (hw (j + 1) c.1)
  nlinarith
theorem coarsePart_chartMove_le (S B : Finset F.Cell) (U A : ChainChart F) (t : ℝ)
    (w : F.SiteWeights) (hw : ∀ j x, 0 ≤ w j x) :
    coarsePart S B (chartMove U A t) w ≤ coarsePart S B U w + |t| * coarsePart S B A w := by
  unfold coarsePart
  rw [← sqrt_sum_mul_sq _ _ (abs_nonneg t)]
  exact sqrt_sum_sq_le_add _ _ _ _ (fun i _ => Real.sqrt_nonneg _)
    (fun j _ => coarsePartAt_chartMove_le S B U A t w hw j)
theorem sqrt_mul_sq_add_mul_sq (c a b : ℝ) (hc : 0 ≤ c) :
    Real.sqrt ((c * a) ^ 2 + (c * b) ^ 2) = c * Real.sqrt (a ^ 2 + b ^ 2) := by
  have : (c * a) ^ 2 + (c * b) ^ 2 = c ^ 2 * (a ^ 2 + b ^ 2) := by ring
  rw [this, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
theorem localNorm_chartMove_le (S : Finset F.Cell) (R : F.FieldChain) (U A : ChainChart F) (t : ℝ)
    (w : F.SiteWeights) (hw : ∀ j x, 0 ≤ w j x) (z : F.Cell) :
    localNorm S R (chartMove U A t) w z ≤ localNorm S R U w z + |t| * localNorm S R A w z := by
  rw [localNorm_eq_parts, localNorm_eq_parts, localNorm_eq_parts]
  set B := cellBall S z 3
  have hc := abs_nonneg t
  have h1 := sqrt_sq_add_sq_le_add _ _ _ _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (quarticPart_chartMove_le S B U A t w hw) (curlPart_chartMove_le S B R U A t w hw)
  rw [sqrt_mul_sq_add_mul_sq _ _ _ hc] at h1
  have h2 := sqrt_sq_add_sq_le_add _ _ _ _ _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) h1
    (coarsePart_chartMove_le S B U A t w hw)
  rwa [sqrt_mul_sq_add_mul_sq _ _ _ hc] at h2
theorem weightedNorm_chartMove_le (S : Finset F.Cell) (R : F.FieldChain) (U A : ChainChart F) (t : ℝ)
    (w : F.SiteWeights) (hw : ∀ j x, 0 ≤ w j x) :
    weightedNorm S R (chartMove U A t) w ≤ weightedNorm S R U w + |t| * weightedNorm S R A w := by
  unfold weightedNorm
  rw [← sqrt_sum_mul_sq _ _ (abs_nonneg t)]
  exact sqrt_sum_sq_le_add _ _ _ _ (fun i _ => Real.sqrt_nonneg _)
    (fun z _ => localNorm_chartMove_le S R U A t w hw z)
theorem weightedNorm_nonneg (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    0 ≤ weightedNorm S R U w := Real.sqrt_nonneg _
theorem weightedNorm_sq (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights) :
    weightedNorm S R U w ^ 2 = ∑ z ∈ S, localNormSq S (cellBall S z 3) R U w := by
  unfold weightedNorm localNorm
  rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun z _ => Real.sq_sqrt (localNormSq_nonneg _ _ _ _ _)
theorem localNormSq_mono_weights (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w w' : F.SiteWeights) (h0 : ∀ j x, 0 ≤ w j x) (h1 : ∀ j x, w j x ≤ w' j x) :
    localNormSq S B R U w ≤ localNormSq S B R U w' := by
  unfold localNormSq
  have term : ∀ (e : ℕ) (j : ℕ) (x : F.Site j) (c : ℝ), 0 ≤ c → (w j x * c) ^ e ≤ (w' j x * c) ^ e :=
    fun e j x c hc => pow_le_pow_left₀ (mul_nonneg (h0 _ _) hc) (mul_le_mul_of_nonneg_right (h1 _ _) hc) e
  refine add_le_add (add_le_add (Real.sqrt_le_sqrt ?_) ?_) ?_
  · exact Finset.sum_le_sum fun b _ => term 4 0 b.1 _ (norm_nonneg _)
  · exact Finset.sum_le_sum fun b _ => term 2 0 b.1 _ (norm_nonneg _)
  · exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun b _ => term 2 (j + 1) b.1 _ (norm_nonneg _)
theorem weightedNorm_mono_weights (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w w' : F.SiteWeights) (h0 : ∀ j x, 0 ≤ w j x) (h1 : ∀ j x, w j x ≤ w' j x) :
    weightedNorm S R U w ≤ weightedNorm S R U w' := by
  unfold weightedNorm localNorm
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun z _ => ?_)
  rw [Real.sq_sqrt (localNormSq_nonneg _ _ _ _ _), Real.sq_sqrt (localNormSq_nonneg _ _ _ _ _)]
  exact localNormSq_mono_weights _ _ _ _ _ _ h0 h1
theorem mem_innerBonds_of_mem_bondsOver {S B : Finset F.Cell} {j : ℕ} {b : F.Site j × Fin 4}
    (h : b ∈ bondsOver S B j) : b ∈ innerBonds S j := by
  unfold bondsOver at h
  exact (Finset.mem_filter.1 h).1
theorem linearizedCurl_congr (S : Finset F.Cell) (R : F.GaugeField 0) (u u' : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (h : ∀ b ∈ innerBonds S 0, u b.1 b.2 = u' b.1 b.2) (p : F.Site 0 × Fin 4 × Fin 4)
    (hp : p ∈ innerPlaquettes S 0) : linearizedCurl R u p = linearizedCurl R u' p := by
  obtain ⟨x, μ, ν⟩ := p
  have hc := (Finset.mem_filter.1 hp).2.2
  have c0 : x ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c1 : x + unitStep 0 μ ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c2 : x + unitStep 0 ν ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have c3 : x + unitStep 0 μ + unitStep 0 ν ∈ sitesOfCells S 0 := hc (by simp [plaquetteCorners])
  have mk : ∀ (y : F.Site 0) (i : Fin 4), y ∈ sitesOfCells S 0 → y + unitStep 0 i ∈ sitesOfCells S 0 →
      (y, i) ∈ innerBonds S 0 := fun y i h1 h2 => by
    simp [innerBonds, h1, h2]
  have e1 := h _ (mk x μ c0 c1)
  have e2 := h _ (mk (x + unitStep 0 μ) ν c1 c3)
  have e3 := h _ (mk (x + unitStep 0 ν) μ c2 (by rw [add_right_comm]; exact c3))
  have e4 := h _ (mk x ν c0 c2)
  simp only [] at e1 e2 e3 e4
  simp only [linearizedCurl, e1, e2, e3, e4]
theorem localNormSq_congr (S B : Finset F.Cell) (R : F.FieldChain) (U U' : ChainChart F)
    (w : F.SiteWeights) (h : ChartEqOnBonds S U U') :
    localNormSq S B R U w = localNormSq S B R U' w := by
  unfold localNormSq
  congr 1
  · congr 1
    · congr 1
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [h.1 b (mem_innerBonds_of_mem_bondsOver hb)]
    · refine Finset.sum_congr rfl fun p hp => ?_
      have hp' : p ∈ innerPlaquettes S 0 := by
        unfold plaquettesOver at hp
        exact (Finset.mem_filter.1 hp).1
      rw [linearizedCurl_congr S (R 0) U.fine U'.fine h.1 p hp']
  · refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun c hc => ?_
    have hj' : j + 1 < F.top := by
      have := Finset.mem_range.1 hj
      omega
    rw [h.2 j hj' c (mem_innerBonds_of_mem_bondsOver hc)]
theorem weightedNorm_congr (S : Finset F.Cell) (R : F.FieldChain) (U U' : ChainChart F)
    (w : F.SiteWeights) (h : ChartEqOnBonds S U U') : weightedNorm S R U w = weightedNorm S R U' w := by
  unfold weightedNorm localNorm
  congr 1
  exact Finset.sum_congr rfl fun z _ => by rw [localNormSq_congr S _ R U U' w h]
theorem chainChart_ext {U U' : ChainChart F} (h1 : U.fine = U'.fine) (h2 : U.coarse = U'.coarse) : U = U' := by
  cases U
  cases U'
  simp_all
theorem weightedNorm_eq_zero_of_chartEq (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w : F.SiteWeights) (h : ChartEqOnBonds S U (zeroChart F)) : weightedNorm S R U w = 0 := by
  rw [weightedNorm_congr S R U _ w h]
  have h0 : ∀ B, localNormSq S B R (zeroChart F) w = 0 := by
    intro B
    simp [localNormSq, zeroChart, linearizedCurl, adjointAction]
  have := weightedNorm_sq S R (zeroChart F) w
  simp only [h0, Finset.sum_const_zero] at this
  exact pow_eq_zero_iff (two_ne_zero) |>.1 this
theorem weightedNorm_smul (S : Finset F.Cell) (R : F.FieldChain) (A : ChainChart F) (t : ℝ)
    (w : F.SiteWeights) (hw : ∀ j x, 0 ≤ w j x) :
    weightedNorm S R (chartMove (zeroChart F) A t) w = |t| * weightedNorm S R A w := by
  have hz : weightedNorm S R (zeroChart F) w = 0 :=
    weightedNorm_eq_zero_of_chartEq S R _ w ⟨fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  by_cases ht : t = 0
  · subst ht
    simp only [abs_zero, zero_mul]
    refine weightedNorm_eq_zero_of_chartEq S R _ w ⟨fun b _ => ?_, fun j _ c _ => ?_⟩ <;>
      simp [chartMove, zeroChart]
  · apply le_antisymm
    · have := weightedNorm_chartMove_le S R (zeroChart F) A t w hw
      rw [hz, zero_add] at this
      exact this
    · have h1 := weightedNorm_chartMove_le S R (zeroChart F) (chartMove (zeroChart F) A t) t⁻¹ w hw
      rw [hz, zero_add] at h1
      have h2 : chartMove (zeroChart F) (chartMove (zeroChart F) A t) t⁻¹ = A := by
        apply chainChart_ext
        · funext x i
          simp [chartMove, zeroChart, smul_smul, inv_mul_cancel₀ ht]
        · funext j x i
          simp [chartMove, zeroChart, smul_smul, inv_mul_cancel₀ ht]
      rw [h2, abs_inv] at h1
      have hpos : 0 < |t| := abs_pos.2 ht
      rw [inv_mul_eq_div, le_div_iff₀ hpos] at h1
      linarith
theorem enclosingCell_cellCentre_add (hL : Odd F.blockSide) {j : ℕ} (z : F.Cell) (h : Fin 4 → ℤ)
    (hh : h ∈ centredCube (F.blockSide ^ (F.top - j))) :
    enclosingCell (cellCentre j z + siteOfCoords j h : F.Site j) = z := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_cellCentre_add <;> assumption
theorem enclosingCell_mem {S : Finset F.Cell} (hL : Odd F.blockSide) {j : ℕ} {x : F.Site j}
    (hx : x ∈ sitesOfCells S j) : enclosingCell x ∈ S := by apply _root_.YangMills.Construction.BlockLines.enclosingCell_mem <;> assumption
theorem mem_sitesOfCells_of_mem_innerBonds {S : Finset F.Cell} {j : ℕ} {b : F.Site j × Fin 4}
    (hb : b ∈ innerBonds S j) : b.1 ∈ sitesOfCells S j := by
  have := (Finset.mem_filter.1 hb).1
  exact (Finset.mem_product.1 this).1
theorem cellSupDist_self (z : F.Cell) : cellSupDist z z = 0 := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_self <;> assumption
theorem mem_cellBall_self {S : Finset F.Cell} {z : F.Cell} (hz : z ∈ S) : z ∈ cellBall S z 3 := by apply _root_.YangMills.Construction.GaugedCriticality.mem_cellBall_self <;> assumption
theorem chartEq_zero_of_weightedNorm_eq_zero (S : Finset F.Cell) (hL : Odd F.blockSide) (R : F.FieldChain)
    (U : ChainChart F) (w : F.SiteWeights) (hw : ∀ j x, 0 < w j x) (h : weightedNorm S R U w = 0) :
    ChartEqOnBonds S U (zeroChart F) := by
  have h2 := weightedNorm_sq S R U w
  rw [h] at h2
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => localNormSq_nonneg S _ R U w)).1
    (by rw [← h2]; norm_num)
  have parts : ∀ z ∈ S, quarticPart S (cellBall S z 3) U w = 0 ∧ coarsePart S (cellBall S z 3) U w = 0 := by
    intro z hz
    have h3 := hall z hz
    rw [localNormSq_eq_parts] at h3
    have q1 := sq_nonneg (quarticPart S (cellBall S z 3) U w)
    have q2 := sq_nonneg (curlPart S (cellBall S z 3) R U w)
    have q3 := sq_nonneg (coarsePart S (cellBall S z 3) U w)
    constructor
    · exact pow_eq_zero_iff two_ne_zero |>.1 (by linarith)
    · exact pow_eq_zero_iff two_ne_zero |>.1 (by linarith)
  constructor
  · intro b hb
    have hz := enclosingCell_mem hL (mem_sitesOfCells_of_mem_innerBonds hb)
    have h3 := (parts _ hz).1
    unfold quarticPart at h3
    have h4 := Real.sqrt_eq_zero'.1 h3
    have h5 := Real.sqrt_eq_zero'.1 (le_antisymm h4 (Real.sqrt_nonneg _))
    have h6 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => by positivity)).1
      (le_antisymm h5 (Finset.sum_nonneg fun c _ => by positivity))
    have hmem : b ∈ bondsOver S (cellBall S (enclosingCell b.1) 3) 0 := by
      unfold bondsOver
      exact Finset.mem_filter.2 ⟨hb, mem_cellBall_self hz⟩
    have h7 := h6 b hmem
    have h8 : w 0 b.1 * ‖U.fine b.1 b.2‖ = 0 := pow_eq_zero_iff (by norm_num) |>.1 h7
    have h9 : ‖U.fine b.1 b.2‖ = 0 := by
      rcases mul_eq_zero.1 h8 with h | h
      · exact absurd h (hw _ _).ne'
      · exact h
    simpa [zeroChart] using h9
  · intro j hj c hc
    have hz := enclosingCell_mem hL (mem_sitesOfCells_of_mem_innerBonds hc)
    have h3 := (parts _ hz).2
    unfold coarsePart at h3
    have h4 := Real.sqrt_eq_zero'.1 h3
    have h6 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => by positivity)).1
      (le_antisymm h4 (Finset.sum_nonneg fun c _ => by positivity))
    have h7 := h6 j (Finset.mem_range.2 (by omega))
    have h8 : coarsePartAt S (cellBall S (enclosingCell c.1) 3) U w j = 0 :=
      pow_eq_zero_iff two_ne_zero |>.1 h7
    unfold coarsePartAt at h8
    have h9 := Real.sqrt_eq_zero'.1 h8
    have h10 := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => by positivity)).1
      (le_antisymm h9 (Finset.sum_nonneg fun c _ => by positivity))
    have hmem : c ∈ bondsOver S (cellBall S (enclosingCell c.1) 3) (j + 1) := by
      unfold bondsOver
      exact Finset.mem_filter.2 ⟨hc, mem_cellBall_self hz⟩
    have h11 := h10 c hmem
    have h12 : w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖ = 0 := pow_eq_zero_iff two_ne_zero |>.1 h11
    have h13 : ‖U.coarse j c.1 c.2‖ = 0 := by
      rcases mul_eq_zero.1 h12 with h | h
      · exact absurd h (hw _ _).ne'
      · exact h
    simpa [zeroChart] using h13
section Localization
theorem sum_le_sum_add_sum_of_subset_union {α : Type} [DecidableEq α] {s t u : Finset α} (h : s ⊆ t ∪ u)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s, f x ≤ ∑ x ∈ t, f x + ∑ x ∈ u, f x := by
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg h (f := f) fun x _ _ => hf x
  have h2 := Finset.sum_union_inter (s₁ := t) (s₂ := u) (f := f)
  have h3 : 0 ≤ ∑ x ∈ t ∩ u, f x := Finset.sum_nonneg fun x _ => hf x
  linarith
theorem sqrt_add_le_add_sqrt (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  apply Real.sqrt_le_iff.2
  refine ⟨by positivity, ?_⟩
  have e1 := Real.sq_sqrt ha
  have e2 := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)]
theorem mem_bondsOver {S B : Finset F.Cell} {j : ℕ} {b : F.Site j × Fin 4} :
    b ∈ bondsOver S B j ↔ b ∈ innerBonds S j ∧ enclosingCell b.1 ∈ B := by
  unfold bondsOver
  simp
theorem mem_plaquettesOver {S B : Finset F.Cell} {j : ℕ} {p : F.Site j × Fin 4 × Fin 4} :
    p ∈ plaquettesOver S B j ↔ p ∈ innerPlaquettes S j ∧ enclosingCell p.1 ∈ B := by
  unfold plaquettesOver
  simp
theorem localNormSq_insert_le (S B : Finset F.Cell) (y : F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w : F.SiteWeights) :
    localNormSq S (insert y B) R U w ≤ localNormSq S {y} R U w + localNormSq S B R U w := by
  unfold localNormSq
  have h1 : ∑ b ∈ bondsOver S (insert y B) 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤
      ∑ b ∈ bondsOver S {y} 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 +
        ∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 := by
    refine sum_le_sum_add_sum_of_subset_union (fun b hb => ?_) _ fun b => by positivity
    rw [mem_bondsOver, Finset.mem_insert] at hb
    rw [Finset.mem_union, mem_bondsOver, mem_bondsOver, Finset.mem_singleton]
    tauto
  have h2 : ∑ p ∈ plaquettesOver S (insert y B) 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 ≤
      ∑ p ∈ plaquettesOver S {y} 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 +
        ∑ p ∈ plaquettesOver S B 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 := by
    refine sum_le_sum_add_sum_of_subset_union (fun b hb => ?_) _ fun b => by positivity
    rw [mem_plaquettesOver, Finset.mem_insert] at hb
    rw [Finset.mem_union, mem_plaquettesOver, mem_plaquettesOver, Finset.mem_singleton]
    tauto
  have h3 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S (insert y B) (j + 1),
        (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S {y} (j + 1),
          (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 +
        ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
          (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun j _ => ?_
    refine sum_le_sum_add_sum_of_subset_union (fun b hb => ?_) _ fun b => by positivity
    rw [mem_bondsOver, Finset.mem_insert] at hb
    rw [Finset.mem_union, mem_bondsOver, mem_bondsOver, Finset.mem_singleton]
    tauto
  have h4 := (Real.sqrt_le_sqrt h1).trans (sqrt_add_le_add_sqrt _ _
    (Finset.sum_nonneg fun b _ => by positivity) (Finset.sum_nonneg fun b _ => by positivity))
  linarith
theorem localNormSq_mono_cells (S : Finset F.Cell) {B B' : Finset F.Cell} (h : B ⊆ B') (R : F.FieldChain)
    (U : ChainChart F) (w : F.SiteWeights) : localNormSq S B R U w ≤ localNormSq S B' R U w := by
  unfold localNormSq
  have h1 : ∑ b ∈ bondsOver S B 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 ≤
      ∑ b ∈ bondsOver S B' 0, (w 0 b.1 * ‖U.fine b.1 b.2‖) ^ 4 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => ?_) fun b _ _ => by positivity
    rw [mem_bondsOver] at hb ⊢
    exact ⟨hb.1, h hb.2⟩
  have h2 : ∑ p ∈ plaquettesOver S B 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 ≤
      ∑ p ∈ plaquettesOver S B' 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => ?_) fun b _ _ => by positivity
    rw [mem_plaquettesOver] at hb ⊢
    exact ⟨hb.1, h hb.2⟩
  have h3 : ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B (j + 1),
        (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 ≤
      ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S B' (j + 1),
        (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 := by
    refine Finset.sum_le_sum fun j _ =>
      Finset.sum_le_sum_of_subset_of_nonneg (fun b hb => ?_) fun b _ _ => by positivity
    rw [mem_bondsOver] at hb ⊢
    exact ⟨hb.1, h hb.2⟩
  have h4 := Real.sqrt_le_sqrt h1
  linarith
theorem localNormSq_le_sum_singletons (S B : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F)
    (w : F.SiteWeights) : localNormSq S B R U w ≤ ∑ y ∈ B, localNormSq S {y} R U w := by
  classical
  induction B using Finset.induction_on with
  | empty =>
    have : localNormSq S ∅ R U w = 0 := by
      unfold localNormSq
      simp [bondsOver, plaquettesOver]
    simp [this]
  | insert y B hy ih =>
    rw [Finset.sum_insert hy]
    exact (localNormSq_insert_le S B y R U w).trans (by linarith)
theorem localNorm_le_weightedNorm (S : Finset F.Cell) (R : F.FieldChain) (U : ChainChart F) (w : F.SiteWeights)
    (z : F.Cell) : localNorm S R U w z ≤ weightedNorm S R U w := by
  have h0 := weightedNorm_sq S R U w
  have h1 : localNormSq S (cellBall S z 3) R U w ≤ weightedNorm S R U w ^ 2 := by
    rw [h0]
    refine (localNormSq_le_sum_singletons S _ R U w).trans ?_
    have hsub : cellBall S z 3 ⊆ S := by
      unfold cellBall
      exact Finset.filter_subset _ _
    refine (Finset.sum_le_sum fun y hy => localNormSq_mono_cells S (B' := cellBall S y 3)
      (fun x hx => ?_) R U w).trans ?_
    · rw [Finset.mem_singleton] at hx
      subst hx
      exact mem_cellBall_self (hsub hy)
    · exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun y _ _ => localNormSq_nonneg S _ R U w
  unfold localNorm
  exact Real.sqrt_le_iff.2 ⟨weightedNorm_nonneg S R U w, h1⟩
end Localization
theorem scaleRadius_pos (hL : 0 < F.blockSide) (j : ℕ) (p : F.Site 0) (x : F.Site j) :
    0 < scaleRadius F j p x := by
  unfold scaleRadius
  refine lt_min (by positivity) (lt_max_of_lt_left (by positivity))
theorem decayWeights_pos (hL : 0 < F.blockSide) (del θ : ℝ) (p : F.Site 0) (y0 : F.Cell) (j : ℕ)
    (x : F.Site j) : 0 < decayWeights F del θ p y0 j x := by
  unfold decayWeights
  have h2 := scaleRadius_pos hL j p x
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)
theorem decayWeights_le_one (del : ℝ) (hdel : 0 ≤ del) (p : F.Site 0) (y0 : F.Cell) (j : ℕ) (x : F.Site j) :
    decayWeights F del 0 p y0 j x ≤ 1 := by
  unfold decayWeights
  simp only [neg_zero, Real.rpow_zero, mul_one]
  rw [Real.exp_le_one_iff]
  have : (0 : ℝ) ≤ cellSupDist (enclosingCell x) y0 := by positivity
  nlinarith
theorem weightedNorm_decay_le_one (S : Finset F.Cell) (hL : 0 < F.blockSide) (R : F.FieldChain)
    (U : ChainChart F) (del : ℝ) (hdel : 0 ≤ del) (p : F.Site 0) (y0 : F.Cell) :
    weightedNorm S R U (decayWeights F del 0 p y0) ≤ weightedNorm S R U (oneSiteWeights F) :=
  weightedNorm_mono_weights S R U _ _ (fun j x => (decayWeights_pos hL del 0 p y0 j x).le)
    (fun j x => decayWeights_le_one del hdel p y0 j x)
theorem bddAbove_weightedNorm_decay (S : Finset F.Cell) (hL : 0 < F.blockSide) (R : F.FieldChain)
    (U : ChainChart F) (del : ℝ) (hdel : 0 ≤ del) :
    BddAbove (Set.range fun y0 : F.Cell => weightedNorm S R U (decayWeights F del 0 0 y0)) :=
  ⟨weightedNorm S R U (oneSiteWeights F), by
    rintro _ ⟨y0, rfl⟩
    exact weightedNorm_decay_le_one S hL R U del hdel 0 y0⟩
instance cell_nonempty : Nonempty F.Cell := ⟨0⟩
theorem supWeightedNorm_nonneg (S : Finset F.Cell) (del : ℝ) (R : F.FieldChain) (U : ChainChart F) :
    0 ≤ supWeightedNorm S del R U :=
  Real.iSup_nonneg fun _ => weightedNorm_nonneg _ _ _ _
theorem weightedNorm_decay_le_supWeightedNorm (S : Finset F.Cell) (hL : 0 < F.blockSide) (del : ℝ)
    (hdel : 0 ≤ del) (R : F.FieldChain) (U : ChainChart F) (y0 : F.Cell) :
    weightedNorm S R U (decayWeights F del 0 0 y0) ≤ supWeightedNorm S del R U :=
  le_ciSup (bddAbove_weightedNorm_decay S hL R U del hdel) y0
theorem supWeightedNorm_le (S : Finset F.Cell) (del : ℝ) (R : F.FieldChain) (U : ChainChart F) (β : ℝ)
    (h : ∀ y0, weightedNorm S R U (decayWeights F del 0 0 y0) ≤ β) : supWeightedNorm S del R U ≤ β :=
  ciSup_le h
theorem supWeightedNorm_chartMove_le (S : Finset F.Cell) (hL : 0 < F.blockSide) (del : ℝ) (hdel : 0 ≤ del)
    (R : F.FieldChain) (U A : ChainChart F) (t : ℝ) :
    supWeightedNorm S del R (chartMove U A t) ≤ supWeightedNorm S del R U + |t| * supWeightedNorm S del R A := by
  refine supWeightedNorm_le _ _ _ _ _ fun y0 => ?_
  refine (weightedNorm_chartMove_le S R U A t _ fun j x => (decayWeights_pos hL del 0 0 y0 j x).le).trans ?_
  exact add_le_add (weightedNorm_decay_le_supWeightedNorm S hL del hdel R U y0)
    (mul_le_mul_of_nonneg_left (weightedNorm_decay_le_supWeightedNorm S hL del hdel R A y0) (abs_nonneg t))
theorem supWeightedNorm_smul (S : Finset F.Cell) (hL : 0 < F.blockSide) (del : ℝ) (R : F.FieldChain)
    (A : ChainChart F) (t : ℝ) :
    supWeightedNorm S del R (chartMove (zeroChart F) A t) = |t| * supWeightedNorm S del R A := by
  unfold supWeightedNorm
  rw [Real.mul_iSup_of_nonneg (abs_nonneg t)]
  congr 1
  funext y0
  exact weightedNorm_smul S R A t _ fun j x => (decayWeights_pos hL del 0 0 y0 j x).le
theorem adjointAction_neg (g : UnitQuaternion) (x : ℍ[ℝ]) : adjointAction g (-x) = - adjointAction g x := by
  simp [adjointAction]
section Linearity
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem lineSum_add_smul (w w' : Lattice4 → Fin 4 → E) (t : ℝ) (y : Lattice4) (i : Fin 4) (n : ℤ) :
    lineSum (fun x k => w x k + t • w' x k) y i n = lineSum w y i n + t • lineSum w' y i n := by
  simp only [lineSum, Finset.sum_add_distrib, smul_sub, Finset.smul_sum]
  abel
theorem staircaseSum_add_smul (w w' : Lattice4 → Fin 4 → E) (t : ℝ) (u v : Lattice4) :
    staircaseSum (fun x k => w x k + t • w' x k) u v = staircaseSum w u v + t • staircaseSum w' u v := by
  simp only [staircaseSum, lineSum_add_smul, Finset.sum_add_distrib, Finset.smul_sum]
theorem dyadicPathSum_add_smul (K : ℕ) (w w' : Lattice4 → Fin 4 → E) (t : ℝ) (x : Lattice4)
    (ω : StaircaseSample) :
    dyadicPathSum K (fun x k => w x k + t • w' x k) x ω = dyadicPathSum K w x ω + t • dyadicPathSum K w' x ω := by
  simp only [dyadicPathSum, staircaseSum_add_smul, Finset.sum_add_distrib, Finset.smul_sum]
theorem randomPathMean_add_smul (l : ℕ) (c : Lattice4) (w w' : Lattice4 → Fin 4 → E) (t : ℝ) (x : Lattice4) :
    randomPathMean l c (fun x k => w x k + t • w' x k) x = randomPathMean l c w x + t • randomPathMean l c w' x := by
  simp only [randomPathMean, dyadicPathSum_add_smul, Finset.sum_add_distrib, smul_add, ← Finset.smul_sum]
  rw [smul_comm t]
end Linearity
theorem localForm_add_smul (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0) (z : F.Cell)
    (u v : F.Site 0 → Fin 4 → ℍ[ℝ]) (t : ℝ) :
    localForm S V R z (fun x k => u x k + t • v x k) =
      fun x k => localForm S V R z u x k + t • localForm S V R z v x k := by
  funext x k
  unfold localForm
  simp only []
  split_ifs
  · rw [adjointAction_add, adjointAction_smul]
  · simp only [adjointAction_add, adjointAction_smul, adjointAction_neg, neg_add, smul_neg]
theorem localPotential_add_smul (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0) (z : F.Cell)
    (u v : F.Site 0 → Fin 4 → ℍ[ℝ]) (t : ℝ) (x : Lattice4) :
    localPotential S V R z (fun x k => u x k + t • v x k) x =
      localPotential S V R z u x + t • localPotential S V R z v x := by
  unfold localPotential
  rw [localForm_add_smul, randomPathMean_add_smul]
theorem localPotentialMean_add_smul (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0)
    (z : F.Cell) (u v : F.Site 0 → Fin 4 → ℍ[ℝ]) (t : ℝ) :
    localPotentialMean S V R z (fun x k => u x k + t • v x k) =
      localPotentialMean S V R z u + t • localPotentialMean S V R z v := by
  simp only [localPotentialMean, localPotential_add_smul, Finset.sum_add_distrib, smul_add, ← Finset.smul_sum]
  rw [smul_comm t]
theorem gluedPotential_add_smul (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0)
    (u v : F.Site 0 → Fin 4 → ℍ[ℝ]) (t : ℝ) (s : F.Site 0) :
    gluedPotential S V R (fun x k => u x k + t • v x k) s =
      gluedPotential S V R u s + t • gluedPotential S V R v s := by
  unfold gluedPotential
  rw [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [localPotential_add_smul, localPotentialMean_add_smul]
  have : localPotential S V R z u (patchChart S z s) + t • localPotential S V R z v (patchChart S z s) -
      (localPotentialMean S V R z u + t • localPotentialMean S V R z v) =
      (localPotential S V R z u (patchChart S z s) - localPotentialMean S V R z u) +
        t • (localPotential S V R z v (patchChart S z s) - localPotentialMean S V R z v) := by
    rw [smul_sub]
    abel
  rw [this, adjointAction_add, adjointAction_smul, smul_add, smul_comm t]
theorem frameCellMean_add_smul (S : Finset F.Cell) (V : F.GaugeField F.top) (y : F.Cell)
    (ξ ξ' : F.Site 0 → ℍ[ℝ]) (t : ℝ) :
    frameCellMean S V y (fun x => ξ x + t • ξ' x) = frameCellMean S V y ξ + t • frameCellMean S V y ξ' := by
  simp only [frameCellMean, adjointAction_add, adjointAction_smul, Finset.sum_add_distrib, smul_add,
    ← Finset.smul_sum]
  rw [smul_comm t]
theorem gaugeMap_add_smul (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0)
    (u v : F.Site 0 → Fin 4 → ℍ[ℝ]) (t : ℝ) (s : F.Site 0) :
    gaugeMap S V R (fun x k => u x k + t • v x k) s =
      gaugeMap S V R u s + t • gaugeMap S V R v s := by
  unfold gaugeMap
  have h1 : gluedPotential S V R (fun x k => u x k + t • v x k) =
      fun x => gluedPotential S V R u x + t • gluedPotential S V R v x :=
    funext fun x => gluedPotential_add_smul S V R u v t x
  have h2 : ∑ y ∈ S, normalizedBump S s y • adjointAction (frameChange S V y s)
        (frameCellMean S V y fun x => gluedPotential S V R u x + t • gluedPotential S V R v x) =
      ∑ y ∈ S, normalizedBump S s y • adjointAction (frameChange S V y s)
          (frameCellMean S V y (gluedPotential S V R u)) +
        t • ∑ y ∈ S, normalizedBump S s y • adjointAction (frameChange S V y s)
          (frameCellMean S V y (gluedPotential S V R v)) := by
    rw [Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [frameCellMean_add_smul, adjointAction_add, adjointAction_smul, smul_add, smul_comm t]
  rw [h1]
  simp only []
  rw [h2, smul_sub]
  abel
abbrev ChartVector (F : BlockFrame) : Type :=
  (F.Site 0 → Fin 4 → imaginaryQuaternions) × ((j : ℕ) → F.Site (j + 1) → Fin 4 → imaginaryQuaternions)
def toChart (x : ChartVector F) : ChainChart F := ⟨x.1, x.2⟩
def ofChart (U : ChainChart F) : ChartVector F := (U.fine, U.coarse)
theorem toChart_add (x y : ChartVector F) : toChart (x + y) = chartSum (toChart x) (toChart y) := by
  apply chainChart_ext
  · funext a i
    simp [toChart, chartSum, chartMove]
  · funext j a i
    simp [toChart, chartSum, chartMove]
theorem toChart_smul (t : ℝ) (x : ChartVector F) : toChart (t • x) = chartMove (zeroChart F) (toChart x) t := by
  apply chainChart_ext
  · funext a i
    simp [toChart, chartMove, zeroChart]
  · funext j a i
    simp [toChart, chartMove, zeroChart]
theorem toChart_zero : toChart (0 : ChartVector F) = zeroChart F := rfl
abbrev BondValues (S : Finset F.Cell) : Type :=
  (↥(innerBonds S 0) → imaginaryQuaternions) × ((j : Fin (F.top - 1)) → ↥(innerBonds S (j.1 + 1)) → imaginaryQuaternions)
def bondValues (S : Finset F.Cell) : ChartVector F →ₗ[ℝ] BondValues S where
  toFun x := (fun b => x.1 b.1.1 b.1.2, fun j c => x.2 j.1 c.1.1 c.1.2)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
theorem bondValues_eq_iff (S : Finset F.Cell) (x y : ChartVector F) :
    bondValues S x = bondValues S y ↔ ChartEqOnBonds S (toChart x) (toChart y) := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    refine ⟨fun b hb => congrFun h1 ⟨b, hb⟩, fun j hj c hc => ?_⟩
    exact congrFun (congrFun h2 ⟨j, by omega⟩) ⟨c, hc⟩
  · intro h
    refine Prod.ext ?_ ?_
    · funext b
      exact h.1 b.1 b.2
    · funext j c
      exact h.2 j.1 (by have := j.2; omega) c.1 c.2
theorem gaugeMap_zero (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0) (s : F.Site 0) :
    gaugeMap S V R (fun _ _ => 0) s = 0 := by
  have := gaugeMap_add_smul S V R (fun _ _ => 0) (fun _ _ => 0) (-1) s
  simpa using this
def gaugeSliceSubmodule (S : Finset F.Cell) (V : F.GaugeField F.top) (R : F.GaugeField 0) :
    Submodule ℝ (ChartVector F) where
  carrier := {x | InGaugeSlice S V R x.1}
  add_mem' := by
    intro x y hx hy s hs
    have h := gaugeMap_add_smul S V R (fun a i => (x.1 a i : ℍ[ℝ])) (fun a i => (y.1 a i : ℍ[ℝ])) 1 s
    have e : (fun a i => (((x + y).1 a i : imaginaryQuaternions) : ℍ[ℝ])) =
        fun a i => (x.1 a i : ℍ[ℝ]) + (1 : ℝ) • (y.1 a i : ℍ[ℝ]) := by
      funext a i
      simp
    rw [e, h, hx s hs, hy s hs]
    simp
  zero_mem' := by
    intro s _
    exact gaugeMap_zero S V R s
  smul_mem' := by
    intro t x hx s hs
    have h := gaugeMap_add_smul S V R (fun _ _ => 0) (fun a i => (x.1 a i : ℍ[ℝ])) t s
    have e : (fun a i => (((t • x).1 a i : imaginaryQuaternions) : ℍ[ℝ])) =
        fun a i => (0 : ℍ[ℝ]) + t • (x.1 a i : ℍ[ℝ]) := by
      funext a i
      simp
    rw [e, h, hx s hs, gaugeMap_zero]
    simp
theorem mem_gaugeSliceSubmodule {S : Finset F.Cell} {V : F.GaugeField F.top} {R : F.GaugeField 0}
    {x : ChartVector F} : x ∈ gaugeSliceSubmodule S V R ↔ InGaugeSlice S V R (toChart x).fine := Iff.rfl
theorem cellSupDist_comm (a b : F.Cell) : cellSupDist a b = cellSupDist b a := by apply _root_.YangMills.Construction.BlockLines.cellSupDist_comm <;> assumption
theorem cellSupDist_triangle (a b c : F.Cell) : cellSupDist a c ≤ cellSupDist a b + cellSupDist b c := by apply _root_.YangMills.Construction.BlockAverages.PatchLocality.cellSupDist_triangle <;> assumption
theorem classWeight_zero (p : F.Site 0) : classWeight F (fun _ => 0) 0 p = oneSiteWeights F := by
  funext j x
  simp [classWeight, oneSiteWeights]
theorem quadraticFormNormSq_nonneg (a : ℝ) (ha : 0 ≤ a) (S : Finset F.Cell) (R : F.FieldChain)
    (U : ChainChart F) (w : F.SiteWeights) : 0 ≤ quadraticFormNormSq a S R U w := by
  unfold quadraticFormNormSq
  have h1 : 0 ≤ ∑ p ∈ plaquettesOver S S 0, (w 0 p.1 * ‖linearizedCurl (R 0) U.fine p‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∑ j ∈ Finset.range (F.top - 1), ∑ c ∈ bondsOver S S (j + 1),
      (w (j + 1) c.1 * ‖U.coarse j c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 : 0 ≤ ∑ c ∈ bondsOver S S F.top, (w F.top c.1 * ‖linearPart R U F.top c.1 c.2‖) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have := mul_nonneg ha h2
  have := mul_nonneg ha h3
  linarith
end CoordinateSeminorms
end YangMills.Construction
end
