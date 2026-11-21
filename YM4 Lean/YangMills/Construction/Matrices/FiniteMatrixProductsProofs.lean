import YangMills.Construction.Matrices.FiniteMatrixProducts
import Mathlib
open Set
open scoped ContDiff Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Matrices.FamilyProducts
private theorem familyNbhd_eq_ball {σ : Type} [Fintype σ] (w₀ : σ → ComplexMatrix2) {ε : ℝ}
    (hε : 0 < ε) : familyNbhd w₀ ε = Metric.ball w₀ ε := by
  ext w
  rw [Metric.mem_ball, dist_pi_lt_iff hε]
  exact forall_congr' fun i => by rw [dist_eq_norm]
private def quaternionSplitting : ComplexMatrix2 ≃ₗ[ℝ] (Fin 4 → ℝ) × (Fin 4 → ℝ) where
  toFun X :=
    (![((X 0 0).re + (X 1 1).re) / 2, ((X 0 0).im - (X 1 1).im) / 2,
       ((X 0 1).re - (X 1 0).re) / 2, ((X 0 1).im + (X 1 0).im) / 2],
     ![((X 0 0).re - (X 1 1).re) / 2, ((X 0 0).im + (X 1 1).im) / 2,
       ((X 0 1).re + (X 1 0).re) / 2, ((X 0 1).im - (X 1 0).im) / 2])
  invFun p :=
    !![⟨p.1 0 + p.2 0, p.1 1 + p.2 1⟩, ⟨p.1 2 + p.2 2, p.1 3 + p.2 3⟩;
       ⟨p.2 2 - p.1 2, p.1 3 - p.2 3⟩, ⟨p.1 0 - p.2 0, p.2 1 - p.1 1⟩]
  map_add' X Y := by
    ext i <;> fin_cases i <;> simp <;> ring
  map_smul' r X := by
    ext i <;> fin_cases i <;> simp <;> ring
  left_inv X := by
    ext i j
    fin_cases i <;> fin_cases j <;> apply Complex.ext <;> simp <;> ring
  right_inv p := by
    ext i <;> fin_cases i <;> simp <;> ring
private theorem mem_specialUnitary_iff_splitting (X : ComplexMatrix2) :
    X ∈ ComplexMatrix2.specialUnitary ↔ (quaternionSplitting X).2 = 0 ∧
      (quaternionSplitting X).1 0 ^ 2 + (quaternionSplitting X).1 1 ^ 2
        + (quaternionSplitting X).1 2 ^ 2 + (quaternionSplitting X).1 3 ^ 2 = 1 := by
  have hc0 : ∀ Y : ComplexMatrix2, (quaternionSplitting Y).1 0 = ((Y 0 0).re + (Y 1 1).re) / 2 :=
    fun _ => rfl
  have hc1 : ∀ Y : ComplexMatrix2, (quaternionSplitting Y).1 1 = ((Y 0 0).im - (Y 1 1).im) / 2 :=
    fun _ => rfl
  have hc2 : ∀ Y : ComplexMatrix2, (quaternionSplitting Y).1 2 = ((Y 0 1).re - (Y 1 0).re) / 2 :=
    fun _ => rfl
  have hc3 : ∀ Y : ComplexMatrix2, (quaternionSplitting Y).1 3 = ((Y 0 1).im + (Y 1 0).im) / 2 :=
    fun _ => rfl
  have hd0 : ∀ Y : ComplexMatrix2, (quaternionSplitting Y).2 0 = ((Y 0 0).re - (Y 1 1).re) / 2 :=
    fun _ => rfl
  have hd1 : ∀ Y : ComplexMatrix2, (quaternionSplitting Y).2 1 = ((Y 0 0).im + (Y 1 1).im) / 2 :=
    fun _ => rfl
  have hd2 : ∀ Y : ComplexMatrix2, (quaternionSplitting Y).2 2 = ((Y 0 1).re + (Y 1 0).re) / 2 :=
    fun _ => rfl
  have hd3 : ∀ Y : ComplexMatrix2, (quaternionSplitting Y).2 3 = ((Y 0 1).im - (Y 1 0).im) / 2 :=
    fun _ => rfl
  rw [hc0, hc1, hc2, hc3]
  constructor
  · intro h
    obtain ⟨hu, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.1 h
    have h1 : star X * X = 1 := Unitary.star_mul_self_of_mem hu
    have h2 : X * X.adjugate = 1 := by rw [Matrix.mul_adjugate, hdet, one_smul]
    have hstar : star X = X.adjugate := by
      calc star X = star X * (X * X.adjugate) := by rw [h2, mul_one]
        _ = X.adjugate := by rw [← mul_assoc, h1, one_mul]
    have e00 := congrFun (congrFun hstar 0) 0
    have e01 := congrFun (congrFun hstar 0) 1
    simp only [Matrix.adjugate_fin_two, Matrix.star_apply, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at e00 e01
    have r00 := congrArg Complex.re e00
    have i00 := congrArg Complex.im e00
    have r01 := congrArg Complex.re e01
    have i01 := congrArg Complex.im e01
    rw [Matrix.det_fin_two] at hdet
    have rdet := congrArg Complex.re hdet
    simp only [Complex.star_def, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
      Complex.sub_re, Complex.mul_re, Complex.one_re] at r00 i00 r01 i01 rdet
    refine ⟨?_, ?_⟩
    · ext i
      fin_cases i
      · show (quaternionSplitting X).2 0 = 0
        rw [hd0]; linarith
      · show (quaternionSplitting X).2 1 = 0
        rw [hd1]; linarith
      · show (quaternionSplitting X).2 2 = 0
        rw [hd2]; linarith
      · show (quaternionSplitting X).2 3 = 0
        rw [hd3]; linarith
    · have a1 : (X 1 1).re = (X 0 0).re := by linarith
      have a2 : (X 1 1).im = -(X 0 0).im := by linarith
      have a3 : (X 1 0).re = -(X 0 1).re := by linarith
      have a4 : (X 1 0).im = (X 0 1).im := by linarith
      rw [a1, a2, a3, a4] at rdet ⊢
      nlinarith
  · rintro ⟨hw, hs⟩
    have w0 := congrFun hw 0
    have w1 := congrFun hw 1
    have w2 := congrFun hw 2
    have w3 := congrFun hw 3
    rw [hd0] at w0
    rw [hd1] at w1
    rw [hd2] at w2
    rw [hd3] at w3
    simp only [Pi.zero_apply] at w0 w1 w2 w3
    have a1 : (X 1 1).re = (X 0 0).re := by linarith
    have a2 : (X 1 1).im = -(X 0 0).im := by linarith
    have a3 : (X 1 0).re = -(X 0 1).re := by linarith
    have a4 : (X 1 0).im = (X 0 1).im := by linarith
    rw [a1, a2, a3, a4] at hs
    have hs' : (X 0 0).re ^ 2 + (X 0 0).im ^ 2 + (X 0 1).re ^ 2 + (X 0 1).im ^ 2 = 1 := by
      nlinarith
    refine Matrix.mem_specialUnitaryGroup_iff.2 ⟨Matrix.mem_unitaryGroup_iff.2 ?_, ?_⟩
    · have key : ∀ i j : Fin 2,
          X i 0 * star (X j 0) + X i 1 * star (X j 1) = (1 : ComplexMatrix2) i j := by
        simp only [Fin.forall_fin_two]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> apply Complex.ext <;>
          simp [a1, a2, a3, a4] <;> nlinarith
      refine Matrix.ext fun i j => ?_
      rw [← key i j, Matrix.mul_apply, Fin.sum_univ_two]
      rfl
    · rw [Matrix.det_fin_two]
      apply Complex.ext
      · simp [a1, a2, a3, a4]
        linear_combination hs'
      · simp [a1, a2, a3, a4]
        ring
private def sphereGraph (p : (Fin 4 → ℝ) × (Fin 4 → ℝ)) : (Fin 3 → ℝ) × (Fin 5 → ℝ) :=
  (![p.1 1, p.1 2, p.1 3],
   ![p.1 0 ^ 2 + p.1 1 ^ 2 + p.1 2 ^ 2 + p.1 3 ^ 2 - 1, p.2 0, p.2 1, p.2 2, p.2 3])
private def sphereRadicand (z : (Fin 3 → ℝ) × (Fin 5 → ℝ)) : ℝ :=
  1 + z.2 0 - z.1 0 ^ 2 - z.1 1 ^ 2 - z.1 2 ^ 2
private def sphereGraphInv (z : (Fin 3 → ℝ) × (Fin 5 → ℝ)) : (Fin 4 → ℝ) × (Fin 4 → ℝ) :=
  (![Real.sqrt (sphereRadicand z), z.1 0, z.1 1, z.1 2], ![z.2 1, z.2 2, z.2 3, z.2 4])
private theorem contDiff_fst_coord {n : ℕ} {m : ℕ} (i : Fin n) :
    ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × (Fin m → ℝ) => p.1 i) :=
  (contDiff_apply ℝ ℝ i).comp contDiff_fst
private theorem contDiff_snd_coord {n : ℕ} {m : ℕ} (i : Fin m) :
    ContDiff ℝ ∞ (fun p : (Fin n → ℝ) × (Fin m → ℝ) => p.2 i) :=
  (contDiff_apply ℝ ℝ i).comp contDiff_snd
private theorem contDiff_sphereGraph : ContDiff ℝ ∞ sphereGraph := by
  have h (i : Fin 4) := contDiff_fst_coord (n := 4) (m := 4) i
  have h' (i : Fin 4) := contDiff_snd_coord (n := 4) (m := 4) i
  refine ContDiff.prodMk (contDiff_pi.2 fun i => ?_) (contDiff_pi.2 fun i => ?_)
  · fin_cases i
    · exact h 1
    · exact h 2
    · exact h 3
  · fin_cases i
    · exact ((((h 0).pow 2).add ((h 1).pow 2)).add ((h 2).pow 2)).add ((h 3).pow 2) |>.sub
        contDiff_const
    · exact h' 0
    · exact h' 1
    · exact h' 2
    · exact h' 3
private theorem contDiff_sphereRadicand : ContDiff ℝ ∞ sphereRadicand := by
  have h (i : Fin 3) := contDiff_fst_coord (n := 3) (m := 5) i
  have h' (i : Fin 5) := contDiff_snd_coord (n := 3) (m := 5) i
  exact (((contDiff_const.add (h' 0)).sub ((h 0).pow 2)).sub ((h 1).pow 2)).sub ((h 2).pow 2)
private theorem contDiffOn_sphereGraphInv :
    ContDiffOn ℝ ∞ sphereGraphInv {z | 0 < sphereRadicand z} := by
  have h (i : Fin 3) := (contDiff_fst_coord (n := 3) (m := 5) i).contDiffOn
    (s := {z | 0 < sphereRadicand z})
  have h' (i : Fin 5) := (contDiff_snd_coord (n := 3) (m := 5) i).contDiffOn
    (s := {z | 0 < sphereRadicand z})
  refine ContDiffOn.prodMk (contDiffOn_pi.2 fun i => ?_) (contDiffOn_pi.2 fun i => ?_)
  · fin_cases i
    · exact contDiff_sphereRadicand.contDiffOn.sqrt fun z hz => ne_of_gt hz
    · exact h 0
    · exact h 1
    · exact h 2
  · fin_cases i
    · exact h' 1
    · exact h' 2
    · exact h' 3
    · exact h' 4
private def sphereChart :
    OpenPartialHomeomorph ((Fin 4 → ℝ) × (Fin 4 → ℝ)) ((Fin 3 → ℝ) × (Fin 5 → ℝ)) where
  toFun := sphereGraph
  invFun := sphereGraphInv
  source := {p | 0 < p.1 0}
  target := {z | 0 < sphereRadicand z}
  map_source' p hp := by
    have hp' : 0 < p.1 0 := hp
    have e : sphereRadicand (sphereGraph p) = p.1 0 ^ 2 := by
      simp [sphereRadicand, sphereGraph]
      ring
    show 0 < sphereRadicand (sphereGraph p)
    rw [e]
    positivity
  map_target' z hz := Real.sqrt_pos.2 hz
  left_inv' p hp := by
    have hp' : 0 < p.1 0 := hp
    have e : sphereRadicand (sphereGraph p) = p.1 0 ^ 2 := by
      simp [sphereRadicand, sphereGraph]
      ring
    have e' : Real.sqrt (sphereRadicand (sphereGraph p)) = p.1 0 := by
      rw [e, Real.sqrt_sq hp'.le]
    ext i
    · fin_cases i
      · exact e'
      · rfl
      · rfl
      · rfl
    · fin_cases i <;> rfl
  right_inv' z hz := by
    have hz' : 0 < sphereRadicand z := hz
    have e : Real.sqrt (sphereRadicand z) ^ 2 = sphereRadicand z := Real.sq_sqrt hz'.le
    ext i
    · fin_cases i <;> rfl
    · fin_cases i
      · show Real.sqrt (sphereRadicand z) ^ 2 + z.1 0 ^ 2 + z.1 1 ^ 2 + z.1 2 ^ 2 - 1 = z.2 0
        rw [e, sphereRadicand]
        ring
      · rfl
      · rfl
      · rfl
      · rfl
  open_source := isOpen_lt continuous_const (contDiff_fst_coord (n := 4) (m := 4) 0).continuous
  open_target := isOpen_lt continuous_const contDiff_sphereRadicand.continuous
  continuousOn_toFun := contDiff_sphereGraph.continuous.continuousOn
  continuousOn_invFun := contDiffOn_sphereGraphInv.continuousOn
private def rightMulEquiv (u v : ComplexMatrix2) (h : u * v = 1) (h' : v * u = 1) :
    ComplexMatrix2 ≃ₗ[ℝ] ComplexMatrix2 where
  toFun X := X * v
  invFun X := X * u
  map_add' X Y := Matrix.add_mul X Y v
  map_smul' r X := Matrix.smul_mul r X v
  left_inv X := by
    show X * v * u = X
    rw [mul_assoc, h', mul_one]
  right_inv X := by
    show X * u * v = X
    rw [mul_assoc, h, mul_one]
private theorem star_mem_specialUnitary {p : ComplexMatrix2}
    (hp : p ∈ ComplexMatrix2.specialUnitary) : star p ∈ ComplexMatrix2.specialUnitary := by
  obtain ⟨hu, hd⟩ := Matrix.mem_specialUnitaryGroup_iff.1 hp
  refine Matrix.mem_specialUnitaryGroup_iff.2 ⟨Unitary.star_mem hu, ?_⟩
  rw [Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose, hd, star_one]
private theorem exists_specialUnitary_chart {p : ComplexMatrix2}
    (hp : p ∈ ComplexMatrix2.specialUnitary) :
    ∃ q : OpenPartialHomeomorph ComplexMatrix2 ((Fin 3 → ℝ) × (Fin 5 → ℝ)),
      p ∈ q.source ∧ ContDiffOn ℝ ∞ q q.source ∧ ContDiffOn ℝ ∞ q.symm q.target ∧
        ∀ x ∈ q.source, (x ∈ ComplexMatrix2.specialUnitary ↔ (q x).2 = 0) := by
  obtain ⟨hu, -⟩ := Matrix.mem_specialUnitaryGroup_iff.1 hp
  have h1 : p * star p = 1 := Unitary.mul_star_self_of_mem hu
  have h2 : star p * p = 1 := Unitary.star_mul_self_of_mem hu
  let A : ComplexMatrix2 ≃L[ℝ] (Fin 4 → ℝ) × (Fin 4 → ℝ) :=
    ((rightMulEquiv p (star p) h1 h2).trans quaternionSplitting).toContinuousLinearEquiv
  have hA : ∀ x, A x = quaternionSplitting (x * star p) := fun _ => rfl
  refine ⟨A.toHomeomorph.transOpenPartialHomeomorph sphereChart, ?_, ?_, ?_, ?_⟩
  · show 0 < (A p).1 0
    rw [hA, h1]
    show 0 < (((1 : ComplexMatrix2) 0 0).re + ((1 : ComplexMatrix2) 1 1).re) / 2
    simp
  · exact contDiff_sphereGraph.contDiffOn.comp A.contDiff.contDiffOn (fun _ _ => mem_univ _)
  · exact A.symm.contDiff.comp_contDiffOn contDiffOn_sphereGraphInv
  · intro x _
    have hmem : x ∈ ComplexMatrix2.specialUnitary ↔
        x * star p ∈ ComplexMatrix2.specialUnitary := by
      refine ⟨fun hx => mul_mem hx (star_mem_specialUnitary hp), fun hx => ?_⟩
      have := mul_mem hx hp
      rwa [mul_assoc, h2, mul_one] at this
    rw [hmem, mem_specialUnitary_iff_splitting]
    show _ ↔ (sphereGraph (A x)).2 = 0
    rw [hA]
    generalize quaternionSplitting (x * star p) = c
    constructor
    · rintro ⟨hw, hs⟩
      ext i
      fin_cases i
      · show c.1 0 ^ 2 + c.1 1 ^ 2 + c.1 2 ^ 2 + c.1 3 ^ 2 - 1 = 0
        rw [hs, sub_self]
      · exact congrFun hw 0
      · exact congrFun hw 1
      · exact congrFun hw 2
      · exact congrFun hw 3
    · intro h
      have e (k : Fin 5) := congrFun h k
      refine ⟨?_, sub_eq_zero.1 (e 0)⟩
      ext i
      fin_cases i
      · exact e 1
      · exact e 2
      · exact e 3
      · exact e 4
private def flattenFamily {σ l l' : Type} {m m' : Type} (e : σ × m ≃ l) (e' : σ × m' ≃ l') :
    (σ → (m → ℝ) × (m' → ℝ)) ≃ₗ[ℝ] (l → ℝ) × (l' → ℝ) where
  toFun t := (fun k => (t (e.symm k).1).1 (e.symm k).2, fun k => (t (e'.symm k).1).2 (e'.symm k).2)
  invFun z i := (fun c => z.1 (e (i, c)), fun c => z.2 (e' (i, c)))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv t := by
    ext i c <;> simp
  right_inv z := by
    ext k <;> simp
private theorem image_source_inter_eq {E F F' : Type} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace F'] [Zero F'] (q : OpenPartialHomeomorph E (F × F')) (M : Set E)
    (h : ∀ x ∈ q.source, (x ∈ M ↔ (q x).2 = 0)) :
    q '' (q.source ∩ M) = q.target ∩ {z | z.2 = 0} := by
  ext z
  constructor
  · rintro ⟨x, ⟨hx, hM⟩, rfl⟩
    exact ⟨q.map_source hx, (h x hx).1 hM⟩
  · rintro ⟨hz, hz0⟩
    refine ⟨q.symm z, ⟨q.map_target hz, (h _ (q.map_target hz)).2 ?_⟩, q.right_inv hz⟩
    rw [q.right_inv hz]
    exact hz0
private theorem isSmoothSubmanifold_pi_specialUnitary (σ : Type) [Fintype σ] :
    Submanifolds.IsSmoothSubmanifold
      (ComplexMatrix2.compactProduct fun _ : σ => ComplexMatrix2.FactorKind.group) := by
  classical
  intro p hp
  have hp' : ∀ i, p i ∈ ComplexMatrix2.specialUnitary := hp
  choose q hq₁ hq₂ hq₃ hq₄ using fun i => exists_specialUnitary_chart (hp' i)
  let e := Fintype.equivFin (σ × Fin 3)
  let e' := Fintype.equivFin (σ × Fin 5)
  let L := (flattenFamily e e').toContinuousLinearEquiv
  let Q := (OpenPartialHomeomorph.pi q).transHomeomorph L.toHomeomorph
  have hsrc : ∀ x, x ∈ Q.source ↔ ∀ i, x i ∈ (q i).source := by
    intro x
    show x ∈ Set.pi univ (fun i => (q i).source) ↔ _
    simp
  refine ⟨_, _, Q, (hsrc p).2 hq₁, ?_, ?_, ?_⟩
  · have h : ContDiffOn ℝ ∞ (fun (x : σ → ComplexMatrix2) i => q i (x i)) Q.source :=
      contDiffOn_pi.2 fun i => (hq₂ i).comp (contDiff_apply ℝ ComplexMatrix2 i).contDiffOn
        fun x hx => (hsrc x).1 hx i
    exact L.contDiff.comp_contDiffOn h
  · have h : ContDiffOn ℝ ∞ (fun z i => (q i).symm (L.symm z i)) Q.target :=
      contDiffOn_pi.2 fun i => (hq₃ i).comp
        ((contDiff_apply ℝ ((Fin 3 → ℝ) × (Fin 5 → ℝ)) i).comp L.symm.contDiff).contDiffOn
        fun z hz => (show L.symm z ∈ Set.pi univ fun i => (q i).target from hz) i (mem_univ i)
    exact h
  · refine image_source_inter_eq Q _ fun x hx => ?_
    have hx' := (hsrc x).1 hx
    show (∀ i, x i ∈ ComplexMatrix2.specialUnitary) ↔ _
    rw [forall_congr' fun i => hq₄ i (x i) (hx' i)]
    constructor
    · intro h
      ext k
      exact congrFun (h _) _
    · intro h i
      ext c
      have := congrFun h (e' (i, c))
      simpa [Q, L, flattenFamily] using this
theorem familyProductsStatement_holds : FamilyProductsStatement := by
  intro σ _ _
  refine ⟨fun w₀ => ⟨fun ε hε => ?_, fun N hN => ?_⟩, fun Y O hO => ⟨?_, ?_⟩,
    isSmoothSubmanifold_pi_specialUnitary σ⟩
  · rw [familyNbhd_eq_ball w₀ hε]
    exact Metric.isOpen_ball
  · obtain ⟨ε, hε, h⟩ := Metric.mem_nhds_iff.1 hN
    exact ⟨ε, hε, by rwa [familyNbhd_eq_ball w₀ hε]⟩
  · rintro ⟨U, hU, rfl⟩ w₀ ⟨hw, _⟩
    obtain ⟨ε, hε, h⟩ := Metric.isOpen_iff.1 hU w₀ hw
    refine ⟨ε, hε, fun w hY hb => ⟨h ?_, hY⟩⟩
    rwa [← familyNbhd_eq_ball w₀ hε]
  · intro h
    choose! ε hε hε' using h
    refine ⟨⋃ w₀ ∈ O, Metric.ball w₀ (ε w₀), isOpen_biUnion fun _ _ => Metric.isOpen_ball, ?_⟩
    ext w
    constructor
    · intro hw
      refine ⟨mem_biUnion hw (Metric.mem_ball_self (hε w hw)), hO hw⟩
    · rintro ⟨hw, hY⟩
      obtain ⟨w₀, h₀, hb⟩ := mem_iUnion₂.1 hw
      exact hε' w₀ h₀ w hY (by rwa [familyNbhd_eq_ball w₀ (hε w₀ h₀)])
end YangMills.Construction.Matrices.FamilyProducts
