import YangMills.Construction.ToriAtArbitraryCouplings.SupportsAreCompactAndCarryTheirClasses
import YangMills.Construction.ToriAtArbitraryCouplings.TheNormOfClassC1OnASupport
import YangMills.Construction.TorusOrFourSpace.QuotientMapCompactSetsAndFunctionsOfClassC1
import YangMills.Construction.TorusOrFourSpace.SpaceAndItsFunctionsAreWellDefined
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ToriAtArbitraryCouplings
open ReflectionPositivity.AxisMirror (Ambient)
namespace C1NormOnSupport
open TestFunctions (IsBoundedFun uniformNorm partialDerivR4)
open MetricNotions (IsCompactWrt closureWrt)
section UniformBounds
variable {X : Type}
private theorem norm_le_uniformNorm' {w : X → ℝ} (hw : IsBoundedFun w) (x : X) :
    ‖w x‖ ≤ uniformNorm w := by
  obtain ⟨K, hK⟩ := hw
  exact le_ciSup (f := fun x => ‖w x‖) ⟨K, by rintro _ ⟨y, rfl⟩; exact hK y⟩ x
private theorem uniformNorm_add_le' [Nonempty X] {w w' : X → ℝ} (hw : IsBoundedFun w)
    (hw' : IsBoundedFun w') : uniformNorm (w + w') ≤ uniformNorm w + uniformNorm w' :=
  ciSup_le fun x => (norm_add_le (w x) (w' x)).trans
    (add_le_add (norm_le_uniformNorm' hw x) (norm_le_uniformNorm' hw' x))
private theorem uniformNorm_smul' (a : ℝ) (w : X → ℝ) :
    uniformNorm (a • w) = |a| * uniformNorm w := by
  show (⨆ x, ‖a • w x‖) = |a| * ⨆ x, ‖w x‖
  rw [Real.mul_iSup_of_nonneg (abs_nonneg a)]
  exact iSup_congr fun x => by rw [norm_smul, Real.norm_eq_abs]
end UniformBounds
section CoordinateLines
variable {w w' : (Fin 4 → ℝ) → ℝ}
private theorem differentiableAt_coordLine (hw : ContDiff ℝ 1 w) (i : Fin 4) (x : Fin 4 → ℝ) :
    DifferentiableAt ℝ (fun t : ℝ => w (x + t • Pi.single i (1 : ℝ))) 0 :=
  DifferentiableAt.comp (0 : ℝ) ((hw.differentiable (by norm_num)) _) (by fun_prop)
private theorem partialDerivR4_add' (hw : ContDiff ℝ 1 w) (hw' : ContDiff ℝ 1 w') (i : Fin 4) :
    partialDerivR4 i (w + w') = partialDerivR4 i w + partialDerivR4 i w' := by
  funext x
  exact ((differentiableAt_coordLine hw i x).hasDerivAt.add
    (differentiableAt_coordLine hw' i x).hasDerivAt).deriv
private theorem partialDerivR4_smul' (hw : ContDiff ℝ 1 w) (a : ℝ) (i : Fin 4) :
    partialDerivR4 i (a • w) = a • partialDerivR4 i w := by
  funext x
  exact ((differentiableAt_coordLine hw i x).hasDerivAt.const_mul a).deriv
end CoordinateLines
section Pullbacks
variable (s : TorusSide) {A : Ambient}
private theorem mem_c1Set_iff' {f : s.Point A → ℝ} :
    f ∈ s.c1Set A ↔ ContDiff ℝ 1 (s.pullback f) := by
  cases A <;> exact Iff.rfl
private theorem pullback_add' (f g : s.Point A → ℝ) :
    s.pullback (f + g) = s.pullback f + s.pullback g :=
  rfl
private theorem pullback_smul' (a : ℝ) (f : s.Point A → ℝ) :
    s.pullback (a • f) = a • s.pullback f :=
  rfl
private theorem partialD_add' {f g : s.Point A → ℝ} (hf : f ∈ s.c1Set A)
    (hg : g ∈ s.c1Set A) (i : Fin 4) :
    s.partialD i A (f + g) = s.partialD i A f + s.partialD i A g := by
  symm
  apply s.eq_partialD_of_pullback
  rw [pullback_add', pullback_add', s.pullback_partialD, s.pullback_partialD,
    partialDerivR4_add' ((mem_c1Set_iff' s).1 hf) ((mem_c1Set_iff' s).1 hg)]
private theorem partialD_smul' {f : s.Point A → ℝ} (hf : f ∈ s.c1Set A) (a : ℝ)
    (i : Fin 4) : s.partialD i A (a • f) = a • s.partialD i A f := by
  symm
  apply s.eq_partialD_of_pullback
  rw [pullback_smul', pullback_smul', s.pullback_partialD,
    partialDerivR4_smul' ((mem_c1Set_iff' s).1 hf)]
private theorem zero_mem_c1Set' : (0 : s.Point A → ℝ) ∈ s.c1Set A :=
  (mem_c1Set_iff' s).2 (contDiff_const (c := (0 : ℝ)))
private theorem partialD_zero' (i : Fin 4) :
    s.partialD i A (0 : s.Point A → ℝ) = 0 := by
  have h := partialD_smul' s (zero_mem_c1Set' s (A := A)) 0 i
  simpa using h
end Pullbacks
section Boundedness
private theorem abs_le_euclidNormVec' (v : Fin 4 → ℝ) (i : Fin 4) :
    |v i| ≤ TorusMetric.euclidNormVec v := by apply _root_.YangMills.Construction.Parametrix.UnitKernelSupport.abs_apply_le_euclidNormVec <;> assumption
private theorem bounded_of_compact_closure_support
    (hF : PeriodicSpace.Kind.QuotientCompactC1.Claim)
    (P : PeriodicSpace.Params) (K : PeriodicSpace.Kind)
    {d : K.Pt P → K.Pt P → ℝ} (hd : PeriodicSpace.Kind.quotDist P K = d)
    {w : K.Pt P → ℝ} (hw : w ∈ PeriodicSpace.Kind.c1Set P K)
    (hc : IsCompactWrt d (closureWrt d {y | w y ≠ 0})) :
    IsBoundedFun w ∧ ∀ i, IsBoundedFun (PeriodicSpace.Kind.partialDeriv P K i w) := by
  subst hd
  obtain ⟨-, -, hfin, -⟩ := (hF P K).2.2.2.2 w hw hc
  have h1 : PeriodicSpace.Kind.supNormQ P K w < ∞ := lt_of_le_of_lt (le_max_left _ _) hfin
  have h2 : PeriodicSpace.Kind.vecSupNormQ P K (PeriodicSpace.Kind.gradVec P K w) < ∞ :=
    lt_of_le_of_lt (le_max_right _ _) hfin
  refine ⟨⟨(PeriodicSpace.Kind.supNormQ P K w).toReal, fun y => ?_⟩, fun i =>
    ⟨(PeriodicSpace.Kind.vecSupNormQ P K (PeriodicSpace.Kind.gradVec P K w)).toReal,
      fun y => ?_⟩⟩
  · rw [Real.norm_eq_abs]
    exact (ENNReal.ofReal_le_iff_le_toReal h1.ne).1
      (le_iSup (fun y => ENNReal.ofReal |w y|) y)
  · rw [Real.norm_eq_abs]
    exact (abs_le_euclidNormVec' (PeriodicSpace.Kind.gradVec P K w y) i).trans
      ((ENNReal.ofReal_le_iff_le_toReal h2.ne).1
        (le_iSup (fun y => ENNReal.ofReal
          (TorusMetric.euclidNormVec (PeriodicSpace.Kind.gradVec P K w y))) y))
private def asParams (s : TorusSide) : PeriodicSpace.Params :=
  ⟨s.L, s.admissible, s.m, 1, le_rfl⟩
private theorem epsilon_eq_of_unique {X : Type} (q : (Fin 4 → ℝ) → X) (F : (Fin 4 → ℝ) → ℝ)
    (G : X → ℝ) (hG : G ∘ q = F) (huniq : ∀ g : X → ℝ, g ∘ q = F → g = G) :
    Classical.epsilon (fun v : X → ℝ => v ∘ q = F) = G :=
  huniq _ (Classical.epsilon_spec (p := fun v : X → ℝ => v ∘ q = F) ⟨G, hG⟩)
private theorem bounded_of_mem_c1CompactSet
    (hW : PeriodicSpace.WellPosedness.WellPosed)
    (hF : PeriodicSpace.Kind.QuotientCompactC1.Claim)
    (s : TorusSide) (A : Ambient) {f : s.Point A → ℝ} (hf : f ∈ s.c1CompactSet A) :
    IsBoundedFun f ∧ ∀ i, IsBoundedFun (s.partialD i A f) := by
  cases A
  · have hd : PeriodicSpace.Kind.quotDist (asParams s) .torus = s.pointDist .torus := by
      funext y y'
      exact ((hW (asParams s) .torus).2.2.2.2.2.2.2.2.1 y y').1
    have h := bounded_of_compact_closure_support hF (asParams s) .torus hd (w := f) hf.1 hf.2
    refine ⟨h.1, fun i => ?_⟩
    have e : PeriodicSpace.Kind.partialDeriv (asParams s) .torus i f =
        s.partialD i .torus f :=
      epsilon_eq_of_unique _ _ _ (s.pullback_partialD i .torus f)
        (fun g hg => s.eq_partialD_of_pullback i .torus f g hg)
    exact e ▸ h.2 i
  · have hd : PeriodicSpace.Kind.quotDist (asParams s) .euclidean = s.pointDist .euclidean := by
      funext y y'
      exact (hW (asParams s) .torus).2.2.2.2.2.2.2.1 y y'
    have h := bounded_of_compact_closure_support hF (asParams s) .euclidean hd (w := f) hf.1 hf.2
    refine ⟨h.1, fun i => ?_⟩
    have e : PeriodicSpace.Kind.partialDeriv (asParams s) .euclidean i f =
        s.partialD i .euclidean f :=
      epsilon_eq_of_unique _ _ _ (s.pullback_partialD i .euclidean f)
        (fun g hg => s.eq_partialD_of_pullback i .euclidean f g hg)
    exact e ▸ h.2 i
end Boundedness
section NormAxioms
variable (s : TorusSide) (A : Ambient)
private theorem le_iSup_partialD' (f : s.Point A → ℝ) (i : Fin 4) :
    uniformNorm (s.partialD i A f) ≤ ⨆ j : Fin 4, uniformNorm (s.partialD j A f) :=
  le_ciSup (f := fun j => uniformNorm (s.partialD j A f)) (Set.finite_range _).bddAbove i
private theorem c1NormOn_zero' : s.c1NormOn A (0 : s.Point A → ℝ) = 0 := by
  have h0 : uniformNorm (0 : s.Point A → ℝ) = 0 := by simp [uniformNorm]
  rw [s.c1NormOn_eq_max]
  simp only [partialD_zero', h0, ciSup_const, max_self]
private theorem eq_zero_of_c1NormOn' {f : s.Point A → ℝ} (hb : IsBoundedFun f)
    (h : s.c1NormOn A f = 0) : f = 0 := by
  funext x
  have h1 : uniformNorm f ≤ 0 := by
    rw [← h, s.c1NormOn_eq_max]
    exact le_max_left _ _
  have h2 := (norm_le_uniformNorm' hb x).trans h1
  simpa using h2
private theorem c1NormOn_add_le' {f g : s.Point A → ℝ} (hf : f ∈ s.c1Set A) (hg : g ∈ s.c1Set A)
    (hfb : IsBoundedFun f) (hgb : IsBoundedFun g)
    (hfp : ∀ i, IsBoundedFun (s.partialD i A f))
    (hgp : ∀ i, IsBoundedFun (s.partialD i A g)) :
    s.c1NormOn A (f + g) ≤ s.c1NormOn A f + s.c1NormOn A g := by
  have : Nonempty (s.Point A) := ⟨s.ambientProj A 0⟩
  rw [s.c1NormOn_eq_max, s.c1NormOn_eq_max, s.c1NormOn_eq_max]
  refine max_le ((uniformNorm_add_le' hfb hgb).trans
    (add_le_add (le_max_left _ _) (le_max_left _ _))) (ciSup_le fun i => ?_)
  rw [partialD_add' s hf hg]
  exact (uniformNorm_add_le' (hfp i) (hgp i)).trans
    (add_le_add ((le_iSup_partialD' s A f i).trans (le_max_right _ _))
      ((le_iSup_partialD' s A g i).trans (le_max_right _ _)))
private theorem c1NormOn_smul' {f : s.Point A → ℝ} (hf : f ∈ s.c1Set A) (a : ℝ) :
    s.c1NormOn A (a • f) = |a| * s.c1NormOn A f := by
  rw [s.c1NormOn_eq_max, s.c1NormOn_eq_max, uniformNorm_smul',
    mul_max_of_nonneg _ _ (abs_nonneg a), Real.mul_iSup_of_nonneg (abs_nonneg a)]
  congr 1
  exact iSup_congr fun i => by rw [partialD_smul' s hf, uniformNorm_smul']
end NormAxioms
theorem holds (hS : CompactSupports.Statement)
    (hW : PeriodicSpace.WellPosedness.WellPosed)
    (hF : PeriodicSpace.Kind.QuotientCompactC1.Claim) :
    Statement := by
  intro s A Q hQ
  have hb : ∀ f ∈ s.c1VanishingOutside A Q,
      IsBoundedFun f ∧ ∀ i, IsBoundedFun (s.partialD i A f) := by
    intro f hf
    have h : f ∈ s.c1SuppIn A Q := by
      rw [← (hS s A Q hQ).2]
      exact hf
    exact bounded_of_mem_c1CompactSet hW hF s A ⟨h.1, h.2.1⟩
  refine ⟨⟨zero_mem_c1Set' s, fun _ _ => rfl⟩, fun f hf g hg => ⟨?_, fun x hx => ?_⟩,
    fun a f hf => ⟨?_, fun x hx => ?_⟩, fun f hf => ⟨eq_zero_of_c1NormOn' s A (hb f hf).1, ?_⟩,
    fun f hf g hg => c1NormOn_add_le' s A hf.1 hg.1 (hb f hf).1 (hb g hg).1 (hb f hf).2 (hb g hg).2,
    fun a f hf => c1NormOn_smul' s A hf.1 a⟩
  · rw [mem_c1Set_iff', pullback_add']
    exact ((mem_c1Set_iff' s).1 hf.1).add ((mem_c1Set_iff' s).1 hg.1)
  · simp [hf.2 x hx, hg.2 x hx]
  · rw [mem_c1Set_iff', pullback_smul']
    exact ((mem_c1Set_iff' s).1 hf.1).const_smul a
  · simp [hf.2 x hx]
  · rintro rfl
    exact c1NormOn_zero' s A
end C1NormOnSupport
end YangMills.Construction.ToriAtArbitraryCouplings
end
