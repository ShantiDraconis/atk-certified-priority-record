import ATK.ZeroClasses.BDPisoExato
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.Complex.Convex

/-!
# A taxa de Báez-Duarte no monoide das funções `L` (rodada 110, proposta R110)

Generaliza o teto da rodada 109 (`BDPisoExato.taxa_le_Teta`) de `ζ` para uma classe abstrata `𝓛` de funções `L`
fechada por produtos, e prova a **junção**: uma única taxa do produto certifica a região sem zeros de todos os fatores.

**A classe** (`ClasseL`): `L` holomorfa em `Re s > 0` fora de `s = 1`; `M = 1/L` holomorfa onde `L ≠ 0` e em `s = 1`;
`1/L = Σ μ(n) n^{−s}` absolutamente em `Re s > 1`. **Reta boa** (`RetaBoa 𝓛 σ A`): `0 < σ < 1`, `L ≠ 0` em `Re s ≥ σ`,
`‖1/L‖ ≪ (1 + |Im s|)^η` para todo `η > 0` em `Re s ≥ σ`, e `‖L(σ + iτ)‖ ≪ (1 + |τ|)^A` com `A < 3/2`.

**A distância** (`DNF`): `D_N^𝓛(σ) = inf_{c ∈ ℂ^N} (1/2π) ∫ |1 − L(s) Σ_{k<N} c_k (k+1)^{−s}|² (1 + τ²)^{−2} dτ`,
`s = σ + iτ`; `TaxaDNF σ κ`: `D_N^𝓛(σ) ≪ N^{−δ}` para todo `δ < κ`.

Resultados:
* `piso_DNF`: `(2π)² ‖G(x)‖² ≤ 2π B x^{2σ} D_N^𝓛(σ)` para `N ≤ x`, com a Mertens suavizada
  `G(x) = (1/2π) ∫ x^s K(s)/L(s) dτ = Σ μ(n) ψ(n/x)` (`GF_desloca`, `GF_serie`).
* `mellin_gUF`: `∫₀^∞ u^{s−1} G(1/u) du = K(s)/L(s)` em `1 < Re s < 2`.
* `semZeros_de_extensao`, `semZeros_de_cota`: `‖G(x)‖ ≪ x^θ ⟹ L ≠ 0` em `Re s > θ` (teorema da identidade em duas
  meias-faixas convexas, sem usar simetria de `L`).
* **`teto`** (R110, item 1): numa reta boa, `TaxaDNF σ κ ⟹ L(s) ≠ 0` em `Re s > σ − κ/2`.
* **`juncao`, `juncao_lista`** (R110, item 3, direção do teto): `TaxaDNF (𝓛₁ ⋯ 𝓛_k) σ κ ⟹` todos os `L_i ≠ 0` em
  `Re s > σ − κ/2`. `ClasseL.mul` e `RetaBoa.mul` fecham a classe e as retas boas por produto.
* Instâncias: `classeZeta` (incondicional) com `retaBoa_zeta` em todo `σ ∈ (Θ, 1)`, e `taxaF_zeta_le`
  (`κ ≤ 2(σ − Θ)` também para a nova distância); `classeDirichlet χ` (`χ ≠ 1`, da Mathlib); `juncao_zeta_dirichlet`:
  uma taxa de `D_N^{ζ·L_χ}` certifica `ζ ≠ 0` e `L(·, χ) ≠ 0` juntas, **sob a hipótese** de reta boa para `L(s, χ)`
  (a Mathlib ainda não tem cotas de `L(s, χ)` em faixas).

O que **não** está aqui (fica para a parte 2 da proposta): o piso `TaxaDNF σ (2(σ − Θ_𝓛))` para `𝓛` geral (que
daria `κ_𝓛 = 2(σ − Θ_𝓛)` e `κ_{𝓛₁𝓛₂} = min(κ_{𝓛₁}, κ_{𝓛₂})` com igualdade). Classificação: **novo** (proposta R110,
issue #188). Nada aqui decide RH ou GRH; só os axiomas padrão.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace ATK.ZeroClasses.BDMonoide

open ATK.ZeroClasses.BDPisoExato (K ψ mK mK_pos norm_K_sq_le norm_K_mul_le continuous_K_linha
  integrable_K_linha inv_K_zero inv_K' integrable_K_cpow cpow_quociente norm_cpow_real K_ne_zero
  differentiableAt_K rpow_le_soma hasMellin_psi_n norm_integral_ofReal_nonneg psi_nonneg psi_eq_zero)

/-! ## 1. A classe `𝓛` e a reta boa -/

/-- **A classe `𝓛`**: `L` holomorfa em `Re s > 0` fora de `s = 1`; `M` é a inversa `1/L`, holomorfa onde
`L ≠ 0` e em `s = 1`; `1/L = Σ μ(n) n^{−s}` com convergência absoluta em `Re s > 1`. -/
structure ClasseL where
  L : ℂ → ℂ
  M : ℂ → ℂ
  μ : ℕ → ℂ
  somavel : ∀ s : ℂ, 1 < s.re → LSeriesSummable μ s
  serie : ∀ s : ℂ, 1 < s.re → LSeries μ s = M s
  inversa : ∀ s : ℂ, 0 < s.re → s ≠ 1 → L s ≠ 0 → M s * L s = 1
  semZeros_um : ∀ s : ℂ, 1 < s.re → L s ≠ 0
  holoL : ∀ s : ℂ, 0 < s.re → s ≠ 1 → DifferentiableAt ℂ L s
  holoM : ∀ s : ℂ, 0 < s.re → (s = 1 ∨ L s ≠ 0) → DifferentiableAt ℂ M s

/-- **Reta boa** `Re s = σ ∈ (0, 1)`: `L ≠ 0` em `Re s ≥ σ` (fora de `1`), `‖M(s)‖ ≪ (1 + |Im s|)^η` para todo
`η > 0` em `Re s ≥ σ`, e `‖L(σ + iτ)‖ ≪ (1 + |τ|)^A` com `A < 3/2`. -/
structure RetaBoa (𝓛 : ClasseL) (σ A : ℝ) : Prop where
  pos : 0 < σ
  lt_um : σ < 1
  A_lt : A < 3 / 2
  semZeros : ∀ s : ℂ, σ ≤ s.re → s ≠ 1 → 𝓛.L s ≠ 0
  cotaM : ∀ η : ℝ, 0 < η → ∃ C, 0 < C ∧ ∀ s : ℂ, σ ≤ s.re → ‖𝓛.M s‖ ≤ C * (1 + |s.im|) ^ η
  cotaL : ∃ C, 0 < C ∧ ∀ τ : ℝ, ‖𝓛.L (σ + τ * I)‖ ≤ C * (1 + |τ|) ^ A

namespace ClasseL

variable (𝓛 : ClasseL)

theorem somavel_real {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => ‖𝓛.μ n‖ * ((n : ℝ) ^ σ)⁻¹) := by
  have h := (𝓛.somavel (σ : ℂ) (by simpa using hσ)).norm
  refine h.congr fun n => ?_
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow (by linarith : σ ≠ 0)]
  · simp [hn, div_eq_mul_inv]

/-- O polinômio de Dirichlet `P_c(s) = Σ_{k<N} c_k (k + 1)^{−s}`. -/
noncomputable def P {N : ℕ} (c : Fin N → ℂ) (s : ℂ) : ℂ :=
  ∑ k : Fin N, c k * ((k.val + 1 : ℕ) : ℂ) ^ (-s)

/-- O peso `(1 + τ²)^{−2}` na reta. -/
noncomputable def peso (τ : ℝ) : ℝ := ((1 + τ ^ 2) ^ 2)⁻¹

/-- `W_σ^𝓛(c) = (1/2π) ∫ |1 − L(s) P_c(s)|² (1 + τ²)^{−2} dτ`, `s = σ + iτ`. -/
noncomputable def WF (σ : ℝ) {N : ℕ} (c : Fin N → ℂ) : ℝ :=
  (1 / (2 * π)) * ∫ τ : ℝ, ‖1 - 𝓛.L (σ + τ * I) * P c (σ + τ * I)‖ ^ 2 * peso τ

/-- **A distância ponderada** `D_N^𝓛(σ) = inf_c W_σ^𝓛(c)`. -/
noncomputable def DNF (σ : ℝ) (N : ℕ) : ℝ := ⨅ c : Fin N → ℂ, 𝓛.WF σ c

/-- `TaxaDNF σ κ`: `D_N^𝓛(σ) ≪ N^{−δ}` para todo `δ < κ`. -/
def TaxaDNF (σ κ : ℝ) : Prop :=
  ∀ δ < κ, ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N → 𝓛.DNF σ N ≤ C * (N : ℝ) ^ (-δ)

/-- A função de Mertens suavizada de `𝓛`: `G(x) = (1/2π) ∫ x^s K(s) M(s) dτ`. -/
noncomputable def GF (σ x : ℝ) : ℂ :=
  (1 / (2 * π)) * ∫ τ : ℝ, (x : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I) * 𝓛.M (σ + τ * I)

/-- `B = ∫ ‖K(s) M(s)‖² (1 + τ²)² dτ`. -/
noncomputable def BF (σ : ℝ) : ℝ := ∫ τ : ℝ, ‖K (σ + τ * I) * 𝓛.M (σ + τ * I)‖ ^ 2 * (1 + τ ^ 2) ^ 2

theorem WF_nonneg (σ : ℝ) {N : ℕ} (c : Fin N → ℂ) : 0 ≤ 𝓛.WF σ c := by
  unfold WF peso
  have : 0 ≤ ∫ τ : ℝ, ‖1 - 𝓛.L (σ + τ * I) * P c (σ + τ * I)‖ ^ 2 * ((1 + τ ^ 2) ^ 2)⁻¹ :=
    integral_nonneg fun τ => by positivity
  positivity

end ClasseL

open ClasseL

theorem RetaBoa.holoM' {𝓛 : ClasseL} {σ A : ℝ} (h : RetaBoa 𝓛 σ A) {s : ℂ} (hs : σ ≤ s.re) :
    DifferentiableAt ℂ 𝓛.M s := by
  refine 𝓛.holoM s (by linarith [h.pos]) ?_
  by_cases h1 : s = 1
  · exact Or.inl h1
  · exact Or.inr (h.semZeros s hs h1)

/-! ## 2. Ferramentas na reta -/

theorem continuous_linha {f : ℂ → ℂ} {σ : ℝ} (hf : ∀ τ : ℝ, DifferentiableAt ℂ f (σ + τ * I)) :
    Continuous (fun τ : ℝ => f (σ + τ * I)) :=
  continuous_iff_continuousAt.mpr fun τ =>
    (hf τ).continuousAt.comp (f := fun τ : ℝ => (σ : ℂ) + τ * I) (Continuous.continuousAt (by fun_prop))

theorem integrable_pot {r : ℝ} (hr : 1 < r) : Integrable (fun τ : ℝ => (1 + |τ|) ^ (-r)) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := r) (by simpa using hr)
  simpa [Real.norm_eq_abs] using this

theorem um_mais_sq_ge (τ : ℝ) : (1 + |τ|) ^ 2 ≤ 2 * (1 + τ ^ 2) := by
  have := sq_abs τ
  nlinarith [abs_nonneg τ, sq_nonneg (|τ| - 1)]

theorem inv_um_mais_sq_le (τ : ℝ) : (1 + τ ^ 2)⁻¹ ≤ 2 * (1 + |τ|) ^ (-2 : ℝ) := by
  have h1 : (0 : ℝ) < 1 + |τ| := by positivity
  rw [show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg h1.le, Real.rpow_natCast]
  rw [inv_le_iff_one_le_mul₀ (by positivity)]
  have := um_mais_sq_ge τ
  have h2 : 0 < (1 + |τ|) ^ 2 := by positivity
  calc (1 : ℝ) = (1 + |τ|) ^ 2 * ((1 + |τ|) ^ 2)⁻¹ := by field_simp
    _ ≤ (2 * (1 + τ ^ 2)) * ((1 + |τ|) ^ 2)⁻¹ := by gcongr
    _ = 2 * ((1 + |τ|) ^ 2)⁻¹ * (1 + τ ^ 2) := by ring

theorem peso_le (τ : ℝ) : ClasseL.peso τ ≤ 4 * (1 + |τ|) ^ (-4 : ℝ) := by
  have h1 : (0 : ℝ) < 1 + |τ| := by positivity
  have h := inv_um_mais_sq_le τ
  have h0 : 0 ≤ (1 + τ ^ 2)⁻¹ := by positivity
  unfold ClasseL.peso
  rw [show ((1 + τ ^ 2) ^ 2)⁻¹ = (1 + τ ^ 2)⁻¹ ^ 2 by rw [inv_pow]]
  calc (1 + τ ^ 2)⁻¹ ^ 2 ≤ (2 * (1 + |τ|) ^ (-2 : ℝ)) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = 4 * (1 + |τ|) ^ (-4 : ℝ) := by
        rw [mul_pow, ← Real.rpow_natCast ((1 + |τ|) ^ (-2 : ℝ)), ← Real.rpow_mul h1.le]
        norm_num

variable {𝓛 : ClasseL}

/-- `x^s K(s) M(s)` é integrável na reta `Re s = c ∈ [σ, 2)`. -/
theorem integrable_KM {σ A : ℝ} (h : RetaBoa 𝓛 σ A) {c : ℝ} (hc : σ ≤ c) (hc2 : c < 2) {x : ℝ}
    (hx : 0 < x) :
    Integrable (fun τ : ℝ => (x : ℂ) ^ ((c : ℂ) + τ * I) * K (c + τ * I) * 𝓛.M (c + τ * I)) := by
  obtain ⟨C, hC, hM⟩ := h.cotaM 1 one_pos
  have hm := mK_pos hc2
  have hcont : Continuous (fun τ : ℝ => (x : ℂ) ^ ((c : ℂ) + τ * I) * K (c + τ * I) *
      𝓛.M (c + τ * I)) := by
    refine ((Continuous.const_cpow (by fun_prop) (Or.inl ?_)).mul
      (continuous_K_linha hc2)).mul (continuous_linha fun τ => h.holoM' (by simpa using hc))
    exact_mod_cast hx.ne'
  refine Integrable.mono' ((integrable_inv_one_add_sq).const_mul (x ^ c * C * (2 / mK c)))
    hcont.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
  have hKb := norm_K_mul_le (σ₀ := c) hc2 (s := c + τ * I) (by simp)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add] at hKb
  have hMb := hM (c + τ * I) (by simpa using hc)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add, Real.rpow_one] at hMb
  rw [norm_mul, norm_mul, norm_cpow_real hx]
  have hxσ : 0 ≤ x ^ c := Real.rpow_nonneg hx.le c
  calc x ^ c * ‖K (c + τ * I)‖ * ‖𝓛.M (c + τ * I)‖ ≤ x ^ c * ‖K (c + τ * I)‖ * (C * (1 + |τ|)) :=
        mul_le_mul_of_nonneg_left hMb (by positivity)
    _ = x ^ c * C * (‖K (c + τ * I)‖ * (1 + |τ|)) := by ring
    _ ≤ x ^ c * C * (2 / (mK c * (1 + τ ^ 2))) := mul_le_mul_of_nonneg_left hKb (by positivity)
    _ = x ^ c * C * (2 / mK c) * (1 + τ ^ 2)⁻¹ := by field_simp

/-! ## 3. O pareamento: `(2π)² ‖G(x)‖² ≤ x^{2σ} (2π W(c)) B` para todo `c` -/

theorem norm_P_le {N : ℕ} (c : Fin N → ℂ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖ClasseL.P c s‖ ≤ ∑ k : Fin N, ‖c k‖ := by
  unfold ClasseL.P
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [norm_mul]
  have hk : (0 : ℝ) < ((k.val + 1 : ℕ) : ℝ) := by positivity
  have h1 : ‖((k.val + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [show ((k.val + 1 : ℕ) : ℂ) = (((k.val + 1 : ℕ) : ℝ) : ℂ) from (Complex.ofReal_natCast _).symm,
      Complex.norm_cpow_eq_rpow_re_of_pos hk, neg_re]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.le_add_left 1 k.val)
      (by linarith)
  calc ‖c k‖ * ‖((k.val + 1 : ℕ) : ℂ) ^ (-s)‖ ≤ ‖c k‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = ‖c k‖ := mul_one _

theorem continuous_P {N : ℕ} (c : Fin N → ℂ) (σ : ℝ) :
    Continuous (fun τ : ℝ => ClasseL.P c (σ + τ * I)) := by
  unfold ClasseL.P
  refine continuous_finsetSum _ fun k _ => continuous_const.mul ?_
  exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast Nat.succ_ne_zero k.val))

/-- `∫ ‖1 − L P‖² peso < ∞`. -/
theorem integrable_resto {σ A : ℝ} (h : RetaBoa 𝓛 σ A) {N : ℕ} (c : Fin N → ℂ) :
    Integrable (fun τ : ℝ => ‖1 - 𝓛.L (σ + τ * I) * ClasseL.P c (σ + τ * I)‖ ^ 2 * ClasseL.peso τ) := by
  obtain ⟨C, hC, hL⟩ := h.cotaL
  set S := ∑ k : Fin N, ‖c k‖ with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun k _ => norm_nonneg _
  have hcontL : Continuous (fun τ : ℝ => 𝓛.L (σ + τ * I)) :=
    continuous_linha fun τ => 𝓛.holoL _ (by simpa using h.pos) (fun h1 => by
      have := congrArg Complex.re h1; simp at this; linarith [h.lt_um])
  have hcont : Continuous (fun τ : ℝ =>
      ‖1 - 𝓛.L (σ + τ * I) * ClasseL.P c (σ + τ * I)‖ ^ 2 * ClasseL.peso τ) := by
    unfold ClasseL.peso
    exact ((continuous_const.sub (hcontL.mul (continuous_P c σ))).norm.pow 2).mul
      (Continuous.inv₀ (by fun_prop) fun τ => by positivity)
  have i1 := (integrable_pot (r := 4) (by norm_num)).const_mul 8
  have i2 := (integrable_pot (r := 4 - 2 * A) (by linarith [h.A_lt])).const_mul (8 * S ^ 2 * C ^ 2)
  refine Integrable.mono' (i1.add i2) hcont.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
  have h1 : (0 : ℝ) < 1 + |τ| := by positivity
  have hLτ := hL τ
  have hPτ := norm_P_le c (s := σ + τ * I) (by simp; linarith [h.pos])
  have hp := peso_le τ
  have hp0 : 0 ≤ ClasseL.peso τ := by unfold ClasseL.peso; positivity
  rw [Real.norm_of_nonneg (by positivity)]
  have hn : ‖1 - 𝓛.L (σ + τ * I) * ClasseL.P c (σ + τ * I)‖ ≤ 1 + C * (1 + |τ|) ^ A * S := by
    calc _ ≤ ‖(1 : ℂ)‖ + ‖𝓛.L (σ + τ * I) * ClasseL.P c (σ + τ * I)‖ := norm_sub_le _ _
      _ = 1 + ‖𝓛.L (σ + τ * I)‖ * ‖ClasseL.P c (σ + τ * I)‖ := by rw [norm_one, norm_mul]
      _ ≤ 1 + C * (1 + |τ|) ^ A * S := by gcongr
  have hA : 0 ≤ C * (1 + |τ|) ^ A * S := by positivity
  have hsq : ‖1 - 𝓛.L (σ + τ * I) * ClasseL.P c (σ + τ * I)‖ ^ 2 ≤
      2 + 2 * (C * (1 + |τ|) ^ A * S) ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hn 2
    nlinarith [sq_nonneg (1 - C * (1 + |τ|) ^ A * S)]
  have p1 : ((1 + |τ|) ^ A) ^ 2 * (1 + |τ|) ^ (-4 : ℝ) = (1 + |τ|) ^ (-(4 - 2 * A)) := by
    rw [← Real.rpow_natCast ((1 + |τ|) ^ A) 2, ← Real.rpow_mul h1.le, ← Real.rpow_add h1]
    congr 1
    simp only [Nat.cast_ofNat]
    ring
  have e1 : (C * (1 + |τ|) ^ A * S) ^ 2 * (1 + |τ|) ^ (-4 : ℝ) =
      S ^ 2 * C ^ 2 * (1 + |τ|) ^ (-(4 - 2 * A)) := by
    rw [show (C * (1 + |τ|) ^ A * S) ^ 2 * (1 + |τ|) ^ (-4 : ℝ) =
      S ^ 2 * C ^ 2 * (((1 + |τ|) ^ A) ^ 2 * (1 + |τ|) ^ (-4 : ℝ)) by ring, p1]
  calc ‖1 - 𝓛.L (σ + τ * I) * ClasseL.P c (σ + τ * I)‖ ^ 2 * ClasseL.peso τ
      ≤ (2 + 2 * (C * (1 + |τ|) ^ A * S) ^ 2) * (4 * (1 + |τ|) ^ (-4 : ℝ)) :=
        mul_le_mul hsq hp hp0 (by positivity)
    _ = 8 * (1 + |τ|) ^ (-4 : ℝ) + 8 * ((C * (1 + |τ|) ^ A * S) ^ 2 * (1 + |τ|) ^ (-4 : ℝ)) := by ring
    _ = 8 * (1 + |τ|) ^ (-4 : ℝ) + 8 * S ^ 2 * C ^ 2 * (1 + |τ|) ^ (-(4 - 2 * A)) := by rw [e1]; ring

/-- `B = ∫ ‖K M‖² (1 + τ²)² < ∞`. -/
theorem integrable_B {σ A : ℝ} (h : RetaBoa 𝓛 σ A) :
    Integrable (fun τ : ℝ => ‖K (σ + τ * I) * 𝓛.M (σ + τ * I)‖ ^ 2 * (1 + τ ^ 2) ^ 2) := by
  obtain ⟨C, hC, hM⟩ := h.cotaM (1 / 4) (by norm_num)
  have hσ2 : σ < 2 := by linarith [h.lt_um]
  have hm := mK_pos hσ2
  have hcont : Continuous (fun τ : ℝ => ‖K (σ + τ * I) * 𝓛.M (σ + τ * I)‖ ^ 2 * (1 + τ ^ 2) ^ 2) :=
    (((continuous_K_linha hσ2).mul (continuous_linha fun τ => h.holoM' (by simp))).norm.pow 2).mul
      (by fun_prop)
  refine Integrable.mono' ((integrable_pot (r := 3 / 2) (by norm_num)).const_mul (2 * C ^ 2 / mK σ ^ 3))
    hcont.aestronglyMeasurable (Eventually.of_forall fun τ => ?_)
  have h1 : (0 : ℝ) < 1 + |τ| := by positivity
  have hKs := norm_K_sq_le (σ₀ := σ) hσ2 (s := σ + τ * I) (by simp)
  have hMb := hM (σ + τ * I) (by simp)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero,
    zero_add] at hKs hMb
  have hinv := inv_um_mais_sq_le τ
  have hq : (0 : ℝ) < 1 + τ ^ 2 := by positivity
  rw [Real.norm_of_nonneg (by positivity), norm_mul, mul_pow]
  have hM2 : ‖𝓛.M (σ + τ * I)‖ ^ 2 ≤ C ^ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
    calc ‖𝓛.M (σ + τ * I)‖ ^ 2 ≤ (C * (1 + |τ|) ^ (1 / 4 : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hMb 2
      _ = C ^ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
          rw [mul_pow, ← Real.rpow_natCast ((1 + |τ|) ^ (1 / 4 : ℝ)), ← Real.rpow_mul h1.le]
          norm_num
  have hK2 : ‖K (σ + τ * I)‖ ^ 2 * (1 + τ ^ 2) ^ 2 ≤ (1 + τ ^ 2)⁻¹ / mK σ ^ 3 := by
    calc ‖K (σ + τ * I)‖ ^ 2 * (1 + τ ^ 2) ^ 2 ≤ 1 / (mK σ ^ 3 * (1 + τ ^ 2) ^ 3) * (1 + τ ^ 2) ^ 2 :=
          mul_le_mul_of_nonneg_right hKs (by positivity)
      _ = (1 + τ ^ 2)⁻¹ / mK σ ^ 3 := by field_simp
  calc ‖K (σ + τ * I)‖ ^ 2 * ‖𝓛.M (σ + τ * I)‖ ^ 2 * (1 + τ ^ 2) ^ 2
      = (‖K (σ + τ * I)‖ ^ 2 * (1 + τ ^ 2) ^ 2) * ‖𝓛.M (σ + τ * I)‖ ^ 2 := by ring
    _ ≤ ((1 + τ ^ 2)⁻¹ / mK σ ^ 3) * (C ^ 2 * (1 + |τ|) ^ (1 / 2 : ℝ)) :=
        mul_le_mul hK2 hM2 (by positivity) (by positivity)
    _ ≤ ((2 * (1 + |τ|) ^ (-2 : ℝ)) / mK σ ^ 3) * (C ^ 2 * (1 + |τ|) ^ (1 / 2 : ℝ)) := by gcongr
    _ = 2 * C ^ 2 / mK σ ^ 3 * ((1 + |τ|) ^ (-2 : ℝ) * (1 + |τ|) ^ (1 / 2 : ℝ)) := by ring
    _ = 2 * C ^ 2 / mK σ ^ 3 * (1 + |τ|) ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add h1]; norm_num

/-- **O pareamento**: para `N ≥ 1`, `x ≥ N` e todo `c : Fin N → ℂ`,
`(2π)² ‖G(x)‖² ≤ x^{2σ} (2π W(c)) B`. Os termos de `P` somem porque `ψ((k + 1)/x) = 0`. -/
theorem piso_GF {σ A : ℝ} (h : RetaBoa 𝓛 σ A) {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : (N : ℝ) ≤ x)
    (c : Fin N → ℂ) :
    (2 * π) ^ 2 * ‖𝓛.GF σ x‖ ^ 2 ≤ x ^ (2 * σ) * ((2 * π) * 𝓛.WF σ c) * 𝓛.BF σ := by
  have hσ0 := h.pos
  have hσ1 := h.lt_um
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hx0 : 0 < x := lt_of_lt_of_le hN0 hx
  have hs1 : ∀ τ : ℝ, ((σ : ℂ) + τ * I) ≠ 1 := fun τ h1 => by
    have := congrArg Complex.re h1; simp at this; linarith
  have hML : ∀ τ : ℝ, 𝓛.M (σ + τ * I) * 𝓛.L (σ + τ * I) = 1 := fun τ =>
    𝓛.inversa _ (by simpa using hσ0) (hs1 τ) (h.semZeros _ (by simp) (hs1 τ))
  set Lt : ℝ → ℂ := fun τ => (1 - 𝓛.L (σ + τ * I) * ClasseL.P c (σ + τ * I)) *
    ((x : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I) * 𝓛.M (σ + τ * I)) with hLt
  have hid : ∀ τ : ℝ, Lt τ = (x : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I) * 𝓛.M (σ + τ * I) -
      ∑ k : Fin N, c k * ((((x / (k.val + 1 : ℕ) : ℝ)) : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I)) := by
    intro τ
    have e2 : ClasseL.P c ((σ : ℂ) + τ * I) * (x : ℂ) ^ ((σ : ℂ) + τ * I) =
        ∑ k : Fin N, c k * (((x / (k.val + 1 : ℕ) : ℝ)) : ℂ) ^ ((σ : ℂ) + τ * I) := by
      unfold ClasseL.P
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc, cpow_quociente hx0]
    calc Lt τ = (x : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I) * 𝓛.M (σ + τ * I) -
          (ClasseL.P c ((σ : ℂ) + τ * I) * (x : ℂ) ^ ((σ : ℂ) + τ * I)) * K (σ + τ * I) *
            (𝓛.M (σ + τ * I) * 𝓛.L (σ + τ * I)) := by rw [hLt]; ring
      _ = _ := by rw [hML τ, mul_one, e2, Finset.sum_mul]; congr 1
                  refine Finset.sum_congr rfl fun k _ => ?_; ring
  have hint0 := integrable_KM h le_rfl (by linarith) hx0
  have hintk : ∀ k : Fin N, Integrable (fun τ : ℝ => c k * ((((x / (k.val + 1 : ℕ) : ℝ)) : ℂ) ^
      ((σ : ℂ) + τ * I) * K (σ + τ * I))) := fun k =>
    (integrable_K_cpow (by linarith) (by positivity)).const_mul _
  have hzero : ∀ k : Fin N, ∫ τ : ℝ, c k * ((((x / (k.val + 1 : ℕ) : ℝ)) : ℂ) ^
      ((σ : ℂ) + τ * I) * K (σ + τ * I)) = 0 := by
    intro k
    rw [integral_const_mul, inv_K_zero (by linarith), mul_zero]
    rw [le_div_iff₀ (by positivity), one_mul]
    exact le_trans (by exact_mod_cast k.isLt) hx
  have hIL : ∫ τ, Lt τ = 2 * π * 𝓛.GF σ x := by
    simp_rw [hid]
    rw [integral_sub hint0 (integrable_finsetSum _ fun k _ => hintk k),
      integral_finsetSum _ fun k _ => hintk k]
    simp_rw [hzero]
    rw [Finset.sum_const_zero, sub_zero, ClasseL.GF]
    have : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)
    rw [← mul_assoc, mul_one_div_cancel this, one_mul]
  -- as duas metades
  set a : ℝ → ℝ := fun τ => ‖1 - 𝓛.L (σ + τ * I) * ClasseL.P c (σ + τ * I)‖ * (1 + τ ^ 2)⁻¹ with ha
  set b : ℝ → ℝ := fun τ => x ^ σ * (‖K (σ + τ * I) * 𝓛.M (σ + τ * I)‖ * (1 + τ ^ 2)) with hb
  have hnormL : ∀ τ : ℝ, ‖Lt τ‖ = a τ * b τ := by
    intro τ
    have hq : (1 + τ ^ 2) ≠ 0 := by positivity
    simp only [hLt, ha, hb]
    rw [norm_mul, show (x : ℂ) ^ ((σ : ℂ) + τ * I) * K (σ + τ * I) * 𝓛.M (σ + τ * I) =
      (x : ℂ) ^ ((σ : ℂ) + τ * I) * (K (σ + τ * I) * 𝓛.M (σ + τ * I)) by ring, norm_mul,
      norm_cpow_real hx0]
    field_simp
  have ha0 : ∀ τ, 0 ≤ a τ := fun τ => by simp only [ha]; positivity
  have hb0 : ∀ τ, 0 ≤ b τ := fun τ => by simp only [hb]; positivity
  have hIa : Integrable (fun τ => a τ ^ 2) := by
    refine (integrable_resto h c).congr (ae_of_all _ fun τ => ?_)
    simp only [ha, ClasseL.peso]
    rw [mul_pow, inv_pow]
  have hIb : Integrable (fun τ => b τ ^ 2) := by
    refine ((integrable_B h).const_mul (x ^ (2 * σ))).congr (ae_of_all _ fun τ => ?_)
    simp only [hb]
    rw [mul_pow, mul_pow, ← Real.rpow_natCast (x ^ σ), ← Real.rpow_mul hx0.le]
    push_cast
    ring_nf
  have hcontL : Continuous (fun τ : ℝ => 𝓛.L (σ + τ * I)) :=
    continuous_linha fun τ => 𝓛.holoL _ (by simpa using hσ0) (hs1 τ)
  have hma : AEStronglyMeasurable a :=
    (((continuous_const.sub (hcontL.mul (continuous_P c σ))).norm).mul
      (Continuous.inv₀ (by fun_prop) fun τ => by positivity)).aestronglyMeasurable
  have hmb : AEStronglyMeasurable b :=
    (continuous_const.mul (((continuous_K_linha (by linarith)).mul
      (continuous_linha fun τ => h.holoM' (by simp))).norm.mul (by fun_prop))).aestronglyMeasurable
  have hfa : MemLp a (ENNReal.ofReal 2) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq_norm hma).mpr (hIa.congr (ae_of_all _ fun τ => ?_))
    simp [Real.norm_eq_abs, sq_abs]
  have hfb : MemLp b (ENNReal.ofReal 2) := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num]
    refine (memLp_two_iff_integrable_sq_norm hmb).mpr (hIb.congr (ae_of_all _ fun τ => ?_))
    simp [Real.norm_eq_abs, sq_abs]
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ ha0) (ae_of_all _ hb0) hfa hfb
  simp only [Real.rpow_two] at hCS
  have ea : ∫ τ, a τ ^ 2 = 2 * π * 𝓛.WF σ c := by
    rw [ClasseL.WF]
    have : (2 * π) * (1 / (2 * π)) = (1 : ℝ) := by field_simp
    rw [← mul_assoc, this, one_mul]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only [ha, ClasseL.peso]
    rw [mul_pow, inv_pow]
  have eb : ∫ τ, b τ ^ 2 = x ^ (2 * σ) * 𝓛.BF σ := by
    rw [ClasseL.BF, ← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only [hb]
    rw [mul_pow, mul_pow, ← Real.rpow_natCast (x ^ σ), ← Real.rpow_mul hx0.le]
    push_cast
    ring_nf
  rw [ea, eb] at hCS
  have hW0 : 0 ≤ 2 * π * 𝓛.WF σ c := by have := 𝓛.WF_nonneg σ c; positivity
  have hB0 : 0 ≤ x ^ (2 * σ) * 𝓛.BF σ := by
    rw [← eb]; exact integral_nonneg fun τ => sq_nonneg _
  have hle : ‖2 * π * 𝓛.GF σ x‖ ≤
      (2 * π * 𝓛.WF σ c) ^ (1 / 2 : ℝ) * (x ^ (2 * σ) * 𝓛.BF σ) ^ (1 / 2 : ℝ) := by
    rw [← hIL]
    calc ‖∫ τ, Lt τ‖ ≤ ∫ τ, ‖Lt τ‖ := norm_integral_le_integral_norm _
      _ = ∫ τ, a τ * b τ := by simp_rw [hnormL]
      _ ≤ _ := hCS
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
  rw [mul_pow, ← Real.rpow_natCast ((2 * π * 𝓛.WF σ c) ^ (1 / 2 : ℝ)),
    ← Real.rpow_natCast ((x ^ (2 * σ) * 𝓛.BF σ) ^ (1 / 2 : ℝ)), ← Real.rpow_mul hW0,
    ← Real.rpow_mul hB0] at hsq
  norm_num at hsq
  calc (2 * π) ^ 2 * ‖𝓛.GF σ x‖ ^ 2 = (2 * π * ‖𝓛.GF σ x‖) ^ 2 := by ring
    _ ≤ _ := hsq
    _ = _ := by ring

/-- **O piso em `D_N^𝓛(σ)`**: `(2π)² ‖G(x)‖² ≤ 2π B x^{2σ} D_N^𝓛(σ)` para `N ≤ x`. -/
theorem piso_DNF {σ A : ℝ} (h : RetaBoa 𝓛 σ A) {N : ℕ} (hN : 1 ≤ N) {x : ℝ} (hx : (N : ℝ) ≤ x) :
    (2 * π) ^ 2 * ‖𝓛.GF σ x‖ ^ 2 ≤ x ^ (2 * σ) * (2 * π) * 𝓛.BF σ * 𝓛.DNF σ N := by
  have hx0 : 0 < x := lt_of_lt_of_le (by exact_mod_cast hN) hx
  have hB0 : 0 ≤ 𝓛.BF σ := integral_nonneg fun τ => by positivity
  have hk : 0 ≤ x ^ (2 * σ) * (2 * π) * 𝓛.BF σ := by positivity
  rw [ClasseL.DNF, Real.mul_iInf_of_nonneg hk]
  refine le_ciInf fun c => ?_
  have := piso_GF h hN hx c
  linarith

/-! ## 4. Deslocamento até `Re s = 3/2` e a série `G(x) = Σ μ(n) ψ(n/x)` -/

theorem differentiableAt_fM {σ A : ℝ} (h : RetaBoa 𝓛 σ A) {x : ℝ} (hx : 0 < x) {z : ℂ}
    (h1 : σ ≤ z.re) (h2 : z.re < 2) :
    DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s * K s * 𝓛.M s) z := by
  have hx' : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hc : DifferentiableAt ℂ (fun s : ℂ => (x : ℂ) ^ s) z :=
    differentiableAt_id.const_cpow (Or.inl hx')
  exact (hc.mul (differentiableAt_K h2)).mul (h.holoM' h1)

/-- **Deslocamento**: `G_σ(x) = G_{3/2}(x)`. -/
theorem GF_desloca {σ A : ℝ} (h : RetaBoa 𝓛 σ A) {x : ℝ} (hx : 0 < x) :
    𝓛.GF σ x = 𝓛.GF (3 / 2) x := by
  have hσ1 := h.lt_um
  obtain ⟨C, hC, hF⟩ := h.cotaM 1 one_pos
  have hm := mK_pos (σ₀ := 3 / 2) (by norm_num)
  set f : ℂ → ℂ := fun s => (x : ℂ) ^ s * K s * 𝓛.M s with hf
  have hdiff : ∀ z : ℂ, z.re ∈ Icc σ (3 / 2) → DifferentiableAt ℂ f z := fun z hz =>
    differentiableAt_fM h hx hz.1 (by linarith [hz.2])
  have hdecay : ∀ η > 0, ∀ᶠ T : ℝ in atTop, ∀ u ∈ Icc σ (3 / 2 : ℝ),
      ‖f (u + T * I)‖ ≤ η ∧ ‖f (u + ((-T : ℝ) : ℂ) * I)‖ ≤ η := by
    intro η hη
    set Q := (x ^ σ + x ^ (3 / 2 : ℝ)) * C * (2 / mK (3 / 2)) with hQ
    have hQ0 : 0 ≤ Q := by positivity
    filter_upwards [eventually_ge_atTop (Q / η + 1)] with T hT
    have hQη : 0 ≤ Q / η := by positivity
    have hT1 : 1 ≤ T := by linarith
    have hbound : ∀ u ∈ Icc σ (3 / 2 : ℝ), ∀ t : ℝ, |t| = T → ‖f (u + t * I)‖ ≤ η := by
      intro u hu t ht
      have hre : ((u : ℂ) + t * I).re = u := by simp
      have him : ((u : ℂ) + t * I).im = t := by simp
      have hKb := norm_K_mul_le (σ₀ := 3 / 2) (by norm_num) (s := u + t * I) (by rw [hre]; exact hu.2)
      rw [him] at hKb
      have hFb := hF (u + t * I) (by rw [hre]; exact hu.1)
      rw [him, Real.rpow_one] at hFb
      have hxu := rpow_le_soma hx hu
      have ht2 : t ^ 2 = T ^ 2 := by rw [← sq_abs, ht]
      have hxs : 0 ≤ x ^ σ + x ^ (3 / 2 : ℝ) := by positivity
      simp only [hf]
      rw [norm_mul, norm_mul, norm_cpow_real hx]
      calc x ^ u * ‖K (u + t * I)‖ * ‖𝓛.M (u + t * I)‖
          ≤ (x ^ σ + x ^ (3 / 2 : ℝ)) * ‖K (u + t * I)‖ * (C * (1 + |t|)) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hxu (norm_nonneg _)) hFb (norm_nonneg _)
              (by positivity)
        _ = (x ^ σ + x ^ (3 / 2 : ℝ)) * C * (‖K (u + t * I)‖ * (1 + |t|)) := by ring
        _ ≤ (x ^ σ + x ^ (3 / 2 : ℝ)) * C * (2 / (mK (3 / 2) * (1 + t ^ 2))) :=
            mul_le_mul_of_nonneg_left hKb (by positivity)
        _ = Q / (1 + T ^ 2) := by rw [hQ, ht2]; field_simp
        _ ≤ η := by
            rw [div_le_iff₀ (by positivity)]
            have hQT : Q ≤ T * η := (div_le_iff₀ hη).mp (by linarith)
            have hTT : T ≤ T ^ 2 := by nlinarith
            nlinarith [mul_le_mul_of_nonneg_right hTT hη.le]
    intro u hu
    exact ⟨hbound u hu T (abs_of_pos (by linarith)),
      hbound u hu (-T) (by rw [abs_neg, abs_of_pos (by linarith)])⟩
  have key := ATK.PerronSuave.desloca (f := f) (a := σ) (b := 3 / 2) (by linarith) (s := ∅)
    countable_empty (fun z hz => (hdiff z hz).continuousAt.continuousWithinAt)
    (fun z hz => hdiff z (Ioo_subset_Icc_self hz.1))
    (integrable_KM h le_rfl (by linarith) hx)
    (integrable_KM h (by linarith) (by norm_num) hx) hdecay
  show (1 / (2 * π) : ℂ) * ∫ τ : ℝ, f (σ + τ * I) = (1 / (2 * π) : ℂ) * ∫ τ : ℝ, f ((3 / 2 : ℝ) + τ * I)
  rw [key]

/-- **A série**: `G_{3/2}(x) = Σ_n μ(n) ψ(n/x)`. -/
theorem GF_serie {x : ℝ} (hx : 0 < x) :
    𝓛.GF (3 / 2) x = ∑' n : ℕ, 𝓛.μ n * (ψ (n / x) : ℂ) := by
  have hs0 : ∀ τ : ℝ, (((3 / 2 : ℝ) : ℂ) + τ * I) ≠ 0 := fun τ h0 => by
    have := congrArg Complex.re h0; norm_num at this
  set T : ℕ → ℝ → ℂ := fun n τ =>
    𝓛.μ n * ((((x / n : ℝ)) : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + τ * I) * K (((3 / 2 : ℝ) : ℂ) + τ * I)) with hT
  have hre : ∀ τ : ℝ, 1 < (((3 / 2 : ℝ) : ℂ) + τ * I).re := fun τ => by simp; norm_num
  have hpt : ∀ τ : ℝ, (x : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + τ * I) * K (((3 / 2 : ℝ) : ℂ) + τ * I) *
      𝓛.M (((3 / 2 : ℝ) : ℂ) + τ * I) = ∑' n : ℕ, T n τ := by
    intro τ
    rw [← 𝓛.serie _ (hre τ), LSeries, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [hT, LSeries.term_zero, mul_zero, Nat.cast_zero, div_zero, ofReal_zero,
        Complex.zero_cpow (hs0 τ), zero_mul]
    · rw [LSeries.term_of_ne_zero hn.ne']
      simp only [hT]
      have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_eq_mul_inv x, ofReal_mul, Complex.mul_cpow_ofReal_nonneg hx.le (inv_nonneg.mpr hn'.le),
        ofReal_inv, Complex.inv_cpow _ _ (by
          rw [Complex.arg_ofReal_of_nonneg hn'.le]; exact Real.pi_pos.ne)]
      push_cast
      ring
  have hT0 : T 0 = fun _ => 0 := by
    funext τ
    simp only [hT, Nat.cast_zero, div_zero, ofReal_zero, Complex.zero_cpow (hs0 τ), zero_mul, mul_zero]
  have hTint : ∀ n : ℕ, Integrable (T n) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hT0]; exact integrable_zero _ _ _
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      exact (integrable_K_cpow (σ := 3 / 2) (by norm_num) (div_pos hx hn')).const_mul (𝓛.μ n)
  have hnorm : ∀ n : ℕ, ∫ τ, ‖T n τ‖ ≤
      x ^ (3 / 2 : ℝ) * (∫ τ : ℝ, ‖K (((3 / 2 : ℝ) : ℂ) + τ * I)‖) *
        (‖𝓛.μ n‖ * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hT0]
      simp only [norm_zero, integral_zero]
      rw [Nat.cast_zero, Real.zero_rpow (by norm_num), inv_zero, mul_zero, mul_zero]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have heq : ∀ τ : ℝ, ‖T n τ‖ = ‖𝓛.μ n‖ * (x / n) ^ (3 / 2 : ℝ) *
          ‖K (((3 / 2 : ℝ) : ℂ) + τ * I)‖ := by
        intro τ
        simp only [hT]
        rw [norm_mul, norm_mul, norm_cpow_real (div_pos hx hn')]
        ring
      simp_rw [heq]
      rw [integral_const_mul, Real.div_rpow hx.le hn'.le]
      apply le_of_eq
      ring
  have hsum : Summable (fun n : ℕ => ∫ τ, ‖T n τ‖) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hnorm
      ((𝓛.somavel_real (by norm_num : (1 : ℝ) < 3 / 2)).mul_left _)
  have hint : ∀ n : ℕ, ∫ τ, T n τ = 𝓛.μ n * (2 * π * (ψ (n / x) : ℂ)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hT0, integral_zero, Nat.cast_zero, zero_div, psi_eq_zero (t := 0) zero_le_one]
      simp
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      simp only [hT]
      rw [integral_const_mul, inv_K' (σ := 3 / 2) (by norm_num) (div_pos hx hn'), inv_div]
  show (1 / (2 * π) : ℂ) * ∫ τ : ℝ, (x : ℂ) ^ (((3 / 2 : ℝ) : ℂ) + τ * I) *
      K (((3 / 2 : ℝ) : ℂ) + τ * I) * 𝓛.M (((3 / 2 : ℝ) : ℂ) + τ * I) = _
  rw [integral_congr_ae (ae_of_all _ hpt), ← integral_tsum_of_summable_integral_norm hTint hsum]
  simp_rw [hint]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  have : (2 * π : ℂ) ≠ 0 := by exact_mod_cast (show (2 * π : ℝ) ≠ 0 by positivity)
  rw [show (1 / (2 * π) : ℂ) * (𝓛.μ n * (2 * π * (ψ (n / x) : ℂ))) =
    𝓛.μ n * (ψ (n / x) : ℂ) * ((2 * π : ℂ) * (1 / (2 * π))) by ring, mul_one_div_cancel this, mul_one]

theorem norm_GF_le (c : ℝ) {x : ℝ} (hx : 0 < x) :
    ‖𝓛.GF c x‖ ≤ 1 / (2 * π) * x ^ c * ∫ τ : ℝ, ‖K (c + τ * I) * 𝓛.M (c + τ * I)‖ := by
  unfold ClasseL.GF
  rw [norm_mul]
  have h1 : ‖(1 / (2 * π) : ℂ)‖ = 1 / (2 * π) := by simp [abs_of_pos Real.pi_pos]
  rw [h1]
  have h2 : ‖∫ τ : ℝ, (x : ℂ) ^ ((c : ℂ) + τ * I) * K (c + τ * I) * 𝓛.M (c + τ * I)‖ ≤
      x ^ c * ∫ τ : ℝ, ‖K (c + τ * I) * 𝓛.M (c + τ * I)‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun τ => ?_)
    simp only
    rw [mul_assoc, norm_mul, norm_cpow_real hx]
  have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ 1 / (2 * π) by positivity)
  linarith

theorem continuousAt_GF {σ A : ℝ} (h : RetaBoa 𝓛 σ A) {c : ℝ} (hc : σ ≤ c) (hc2 : c < 2)
    {x₀ : ℝ} (hx₀ : 0 < x₀) : ContinuousAt (𝓛.GF c) x₀ := by
  have hc0 : 0 ≤ c := by linarith [h.pos]
  have hint := (integrable_KM h hc hc2 (x := 1) one_pos).norm
  show ContinuousAt (fun x : ℝ => (1 / (2 * π) : ℂ) *
    ∫ τ : ℝ, (x : ℂ) ^ ((c : ℂ) + τ * I) * K (c + τ * I) * 𝓛.M (c + τ * I)) x₀
  refine ContinuousAt.mul continuousAt_const ?_
  refine continuousAt_of_dominated
    (bound := fun τ => (2 * x₀) ^ c * ‖K (c + τ * I) * 𝓛.M (c + τ * I)‖) ?_ ?_ ?_ ?_
  · filter_upwards [lt_mem_nhds hx₀] with x hx
    exact (integrable_KM h hc hc2 hx).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhds (half_lt_self hx₀) (by linarith : x₀ < 2 * x₀)] with x hx
    refine ae_of_all _ fun τ => ?_
    have hxpos : 0 < x := lt_trans (half_pos hx₀) hx.1
    rw [mul_assoc, norm_mul, norm_cpow_real hxpos]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hxpos.le hx.2.le hc0) (norm_nonneg _)
  · refine (hint.const_mul ((2 * x₀) ^ c)).congr (ae_of_all _ fun τ => ?_)
    simp only
    rw [mul_assoc, norm_mul (((1 : ℝ) : ℂ) ^ _), ofReal_one, one_cpow, norm_one, one_mul]
  · refine ae_of_all _ fun τ => ?_
    exact ((continuousAt_ofReal_cpow_const x₀ _ (Or.inr hx₀.ne')).mul continuousAt_const).mul
      continuousAt_const

/-! ## 5. A transformada de Mellin de `u ↦ G(1/u)` é `K(s) M(s)` -/

/-- `g(u) = G_{3/2}(1/u)`. -/
noncomputable def gUF (𝓛 : ClasseL) (u : ℝ) : ℂ := 𝓛.GF (3 / 2) u⁻¹

theorem mellin_gUF {s : ℂ} (hs1 : 1 < s.re) (hs2 : s.re < 2) :
    mellin (gUF 𝓛) s = K s * 𝓛.M s := by
  set Fn : ℕ → ℝ → ℂ := fun n u => (u : ℂ) ^ (s - 1) * (𝓛.μ n * (ψ (n * u) : ℂ)) with hFn
  have e1 : mellin (gUF 𝓛) s = ∫ u in Ioi (0 : ℝ), ∑' n : ℕ, Fn n u := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    simp only [hFn, smul_eq_mul, gUF]
    rw [GF_serie (inv_pos.mpr hu), ← tsum_mul_left]
    simp_rw [div_inv_eq_mul]
  have hF0 : Fn 0 = fun _ => 0 := by
    funext u; simp [hFn, psi_eq_zero (show (0 : ℝ) ≤ 1 by norm_num)]
  have hint : ∀ n : ℕ, Integrable (Fn n) (volume.restrict (Ioi 0)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hF0]; exact integrable_zero _ _ _
    · have hh := (hasMellin_psi_n hs2 hn).1
      refine (Integrable.const_mul hh (𝓛.μ n)).congr (ae_of_all _ fun u => ?_)
      simp only [hFn, smul_eq_mul]
      ring
  have hnorm : ∀ n : ℕ, ∫ u, ‖Fn n u‖ ∂(volume.restrict (Ioi 0)) ≤
      ‖K (s.re : ℂ)‖ * (‖𝓛.μ n‖ * ((n : ℝ) ^ s.re)⁻¹) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hF0]
      simp only [norm_zero, integral_zero]
      rw [Nat.cast_zero, Real.zero_rpow (by linarith), inv_zero, mul_zero, mul_zero]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hσ2 : ((s.re : ℂ)).re < 2 := by simpa using hs2
      have hM := hasMellin_psi_n hσ2 hn
      set r : ℝ → ℝ := fun u => u ^ (s.re - 1) * ψ (n * u) with hr
      have hr0 : ∀ u ∈ Ioi (0 : ℝ), 0 ≤ r u := fun u hu =>
        mul_nonneg (Real.rpow_nonneg (le_of_lt hu) _) (psi_nonneg _)
      have hg : ∀ u ∈ Ioi (0 : ℝ), (u : ℂ) ^ ((s.re : ℂ) - 1) • (ψ (n * u) : ℂ) = (r u : ℂ) := by
        intro u hu
        simp only [hr, smul_eq_mul, Complex.ofReal_mul]
        rw [Complex.ofReal_cpow (le_of_lt hu)]
        push_cast
        try ring
      have step1 : ∫ u in Ioi (0 : ℝ), ‖Fn n u‖ = ∫ u in Ioi (0 : ℝ), ‖𝓛.μ n‖ * ‖(r u : ℂ)‖ := by
        refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
        have hu' : (0 : ℝ) < u := hu
        simp only [hFn]
        rw [← hg u hu, smul_eq_mul]
        simp only [norm_mul]
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hu', Complex.norm_cpow_eq_rpow_re_of_pos hu']
        simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
        ring
      have e3 : ∫ u in Ioi (0 : ℝ), (r u : ℂ) = ((n : ℝ) : ℂ) ^ (-(s.re : ℂ)) * K (s.re : ℂ) := by
        rw [← hM.2, mellin]
        exact (setIntegral_congr_fun measurableSet_Ioi hg).symm
      rw [step1, integral_const_mul, norm_integral_ofReal_nonneg measurableSet_Ioi hr0, e3, norm_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos hn']
      simp only [neg_re, ofReal_re]
      rw [Real.rpow_neg hn'.le]
      apply le_of_eq
      ring
  have hsum : Summable (fun n : ℕ => ∫ u, ‖Fn n u‖ ∂(volume.restrict (Ioi 0))) :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hnorm
      ((𝓛.somavel_real hs1).mul_left _)
  have hval : ∀ n : ℕ, ∫ u in Ioi (0 : ℝ), Fn n u = K s * LSeries.term 𝓛.μ s n := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hF0, integral_zero]; simp
    · have hM := hasMellin_psi_n hs2 hn
      rw [LSeries.term_of_ne_zero hn.ne']
      have e : ∫ u in Ioi (0 : ℝ), Fn n u = 𝓛.μ n * mellin (fun u : ℝ => (ψ (n * u) : ℂ)) s := by
        rw [mellin, ← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
        simp only [hFn, smul_eq_mul]
        ring
      rw [e, hM.2, Complex.cpow_neg]
      push_cast
      ring
  rw [e1, ← integral_tsum_of_summable_integral_norm hint hsum]
  simp_rw [hval]
  rw [tsum_mul_left]
  show K s * LSeries 𝓛.μ s = K s * 𝓛.M s
  rw [𝓛.serie s hs1]

theorem gUF_top :
    gUF 𝓛 =O[atTop] (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) := by
  refine Asymptotics.IsBigO.of_bound
    (1 / (2 * π) * ∫ τ : ℝ, ‖K (((3 / 2 : ℝ) : ℂ) + τ * I) * 𝓛.M (((3 / 2 : ℝ) : ℂ) + τ * I)‖) ?_
  filter_upwards [eventually_gt_atTop 0] with u hu
  rw [gUF, Real.norm_of_nonneg (Real.rpow_nonneg hu.le _)]
  have hh := norm_GF_le (𝓛 := 𝓛) (3 / 2) (inv_pos.mpr hu)
  rw [Real.inv_rpow hu.le, ← Real.rpow_neg hu.le] at hh
  linarith

theorem gUF_bot {σ A θ C : ℝ} (h : RetaBoa 𝓛 σ A)
    (hG : ∀ x : ℝ, 1 ≤ x → ‖𝓛.GF σ x‖ ≤ C * x ^ θ) : gUF 𝓛 =O[𝓝[>] 0] (fun u : ℝ => u ^ (-θ)) := by
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with u hu
  rw [gUF, ← GF_desloca h (inv_pos.mpr hu.1), Real.norm_of_nonneg (Real.rpow_nonneg hu.1.le _),
    Real.rpow_neg hu.1.le, ← Real.inv_rpow hu.1.le]
  exact hG u⁻¹ ((one_le_inv₀ hu.1).mpr hu.2.le)

/-! ## 6. Continuação: `‖G(x)‖ ≪ x^θ` dá `L ≠ 0` em `Re s > θ` -/

/-- Identidade num aberto convexo: uma função holomorfa que se anula perto de `z₀` anula em todo o aberto. -/
theorem anula_convexo {U : Set ℂ} (hU : IsOpen U) (hc : Convex ℝ U) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) (h0 : Φ =ᶠ[𝓝 z₀] 0) : EqOn Φ 0 U :=
  (hΦ.analyticOnNhd hU).eqOn_zero_of_preconnected_of_eventuallyEq_zero hc.isPreconnected hz₀ h0

/-- Valor no fecho por continuidade ao longo de `s₀ + i·t/(n + 1)`. -/
theorem anula_limite {Φ : ℂ → ℂ} {s₀ : ℂ} (hΦ : ContinuousAt Φ s₀) (t : ℝ)
    (hz : ∀ n : ℕ, Φ (s₀ + ((t / (n + 1) : ℝ) : ℂ) * I) = 0) : Φ s₀ = 0 := by
  have hu : Tendsto (fun n : ℕ => s₀ + ((t / (n + 1) : ℝ) : ℂ) * I) atTop (𝓝 s₀) := by
    have h1 : Tendsto (fun n : ℕ => t / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul t
      simp only [mul_zero] at this
      exact Tendsto.congr (fun n => by ring) this
    have h2 := ((continuous_ofReal.tendsto 0).comp h1).mul_const I
    simpa using (tendsto_const_nhds (x := s₀)).add h2
  have := hΦ.tendsto.comp hu
  have hc : Tendsto (Φ ∘ fun n : ℕ => s₀ + ((t / (n + 1) : ℝ) : ℂ) * I) atTop (𝓝 0) := by
    simp only [Function.comp_def, hz]; exact tendsto_const_nhds
  exact tendsto_nhds_unique this hc

/-- **Continuação abstrata.** Se `H` é holomorfa em `θ < Re s < 3/2` e coincide com `K M` em `1 < Re s < 3/2`,
então `L(s) ≠ 0` em `max(θ, 0) < Re s < 3/2`, `s ≠ 1`. -/
theorem semZeros_de_extensao {θ : ℝ} {H : ℂ → ℂ}
    (hH : ∀ s : ℂ, θ < s.re → s.re < 3 / 2 → DifferentiableAt ℂ H s)
    (hHM : ∀ s : ℂ, 1 < s.re → s.re < 3 / 2 → H s = K s * 𝓛.M s) :
    ∀ s : ℂ, θ < s.re → 0 < s.re → s.re < 3 / 2 → s ≠ 1 → 𝓛.L s ≠ 0 := by
  intro s₀ hθ h0 h32 hs1 hL
  set θ' := max θ 0 with hθ'
  set Φ : ℂ → ℂ := fun z => H z * 𝓛.L z - K z with hΦdef
  have hΦd : ∀ z : ℂ, θ' < z.re → z.re < 3 / 2 → z ≠ 1 → DifferentiableAt ℂ Φ z := fun z h1 h2 hz1 =>
    ((hH z (lt_of_le_of_lt (le_max_left _ _) h1) h2).mul
      (𝓛.holoL z (lt_of_le_of_lt (le_max_right _ _) h1) hz1)).sub (differentiableAt_K (by linarith))
  -- `Φ = 0` perto de `5/4 ± i`
  have hloc : ∀ z₀ : ℂ, 1 < z₀.re → z₀.re < 3 / 2 → Φ =ᶠ[𝓝 z₀] 0 := by
    intro z₀ hz1 hz2
    have hopen : IsOpen {z : ℂ | 1 < z.re ∧ z.re < 3 / 2} :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_re continuous_const)
    filter_upwards [hopen.mem_nhds (show z₀ ∈ {z : ℂ | 1 < z.re ∧ z.re < 3 / 2} from
      ⟨hz1, hz2⟩)] with z hz
    obtain ⟨h1, h2⟩ := hz
    simp only [hΦdef, Pi.zero_apply]
    rw [hHM z h1 h2, mul_assoc, 𝓛.inversa z (by linarith) (fun h => by
      rw [h] at h1; simp at h1) (𝓛.semZeros_um z h1), mul_one, sub_self]
  have hK0 := K_ne_zero (s := s₀) (by linarith)
  set r₀ : ℝ := (max θ' 1 + 3 / 2) / 2 with hr₀
  have hm1 : θ' < 3 / 2 := lt_trans (max_lt hθ h0) h32
  have hr1 : 1 < r₀ := by have := le_max_right θ' 1; rw [hr₀]; linarith [max_lt hm1 (by norm_num : (1:ℝ) < 3 / 2)]
  have hr2 : r₀ < 3 / 2 := by rw [hr₀]; linarith [max_lt hm1 (by norm_num : (1:ℝ) < 3 / 2)]
  have hrθ : θ' < r₀ := by have := le_max_left θ' 1; rw [hr₀]; linarith [max_lt hm1 (by norm_num : (1:ℝ) < 3 / 2)]
  have hval : Φ s₀ = 0 := by
    have hcont : ContinuousAt Φ s₀ := (hΦd s₀ (max_lt hθ h0) h32 hs1).continuousAt
    rcases le_or_gt 0 s₀.im with him | him
    · -- metade de cima
      set U := {z : ℂ | θ' < z.re} ∩ {z : ℂ | z.re < 3 / 2} ∩ {z : ℂ | 0 < z.im} with hU
      have hUo : IsOpen U := ((isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_re continuous_const)).inter (isOpen_lt continuous_const continuous_im)
      have hUc : Convex ℝ U :=
        ((convex_halfSpace_re_gt θ').inter (convex_halfSpace_re_lt (3 / 2))).inter
          (convex_halfSpace_im_gt 0)
      have hz₀ : ((r₀ : ℂ) + I) ∈ U := by
        refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [hrθ, hr2]
      have hEq := anula_convexo hUo hUc (fun z hz => (hΦd z hz.1.1 hz.1.2 (fun h1 => by
        have := hz.2; rw [h1] at this; simp at this)).differentiableWithinAt) hz₀
        (hloc _ (by simpa using hr1) (by simpa using hr2))
      refine anula_limite hcont 1 fun n => hEq ?_
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simp only [hU, mem_inter_iff, Set.mem_ofPred_eq, add_re, add_im, ofReal_re, ofReal_im, mul_re,
        mul_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero]
      exact ⟨⟨max_lt hθ h0, h32⟩, by linarith⟩
    · -- metade de baixo
      set U := {z : ℂ | θ' < z.re} ∩ {z : ℂ | z.re < 3 / 2} ∩ {z : ℂ | z.im < 0} with hU
      have hUo : IsOpen U := ((isOpen_lt continuous_const continuous_re).inter
        (isOpen_lt continuous_re continuous_const)).inter (isOpen_lt continuous_im continuous_const)
      have hUc : Convex ℝ U :=
        ((convex_halfSpace_re_gt θ').inter (convex_halfSpace_re_lt (3 / 2))).inter
          (convex_halfSpace_im_lt 0)
      have hz₀ : ((r₀ : ℂ) - I) ∈ U := by
        refine ⟨⟨?_, ?_⟩, ?_⟩ <;> simp [hrθ, hr2]
      have hEq := anula_convexo hUo hUc (fun z hz => (hΦd z hz.1.1 hz.1.2 (fun h1 => by
        have := hz.2; rw [h1] at this; simp at this)).differentiableWithinAt) hz₀
        (hloc _ (by simpa using hr1) (by simpa using hr2))
      refine anula_limite hcont (-1) fun n => hEq ?_
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      simp only [hU, mem_inter_iff, Set.mem_ofPred_eq, add_re, add_im, ofReal_re, ofReal_im, mul_re,
        mul_im, I_re, I_im, mul_zero, mul_one, sub_zero, add_zero]
      refine ⟨⟨max_lt hθ h0, h32⟩, ?_⟩
      have : -1 / ((n : ℝ) + 1) < 0 := by
        rw [neg_div]; exact neg_neg_of_pos hpos
      linarith
  simp only [hΦdef, hL, mul_zero, zero_sub, neg_eq_zero] at hval
  exact hK0 hval

/-- **A cota dá a região sem zeros**: se `‖G_σ(x)‖ ≤ C x^θ` para `x ≥ 1`, então `L ≠ 0` em `Re s > θ`
(`Re s > 0`, `s ≠ 1`). -/
theorem semZeros_de_cota {σ A θ C : ℝ} (h : RetaBoa 𝓛 σ A)
    (hG : ∀ x : ℝ, 1 ≤ x → ‖𝓛.GF σ x‖ ≤ C * x ^ θ) :
    ∀ s : ℂ, θ < s.re → 0 < s.re → s ≠ 1 → 𝓛.L s ≠ 0 := by
  intro s hθ h0 hs1
  rcases le_or_gt σ s.re with hσs | hσs
  · exact h.semZeros s hσs hs1
  have hloc : LocallyIntegrableOn (gUF 𝓛) (Ioi 0) := by
    refine ContinuousOn.locallyIntegrableOn (fun u hu => ?_) measurableSet_Ioi
    have hu' : (0 : ℝ) < u := hu
    exact ((continuousAt_GF h (c := 3 / 2) (by linarith [h.lt_um]) (by norm_num)
      (inv_pos.mpr hu')).comp (continuousAt_inv₀ hu'.ne')).continuousWithinAt
  have htop := gUF_top (𝓛 := 𝓛)
  have hbot := gUF_bot h hG
  refine semZeros_de_extensao (θ := θ) (H := mellin (gUF 𝓛)) (fun z h1 h2 =>
    mellin_differentiableAt_of_isBigO_rpow hloc htop h2 hbot h1)
    (fun z h1 h2 => mellin_gUF h1 (by linarith)) s hθ h0 (by linarith [h.lt_um]) hs1

/-! ## 7. O teto: `TaxaDNF σ κ ⟹ L ≠ 0` em `Re s > σ − κ/2` -/

/-- **O teto** (proposta R110, item 1): numa reta boa `σ`, a taxa `κ` de `D_N^𝓛(σ)` certifica que `L` não tem
zeros em `Re s > σ − κ/2`. -/
theorem teto {σ A κ : ℝ} (h : RetaBoa 𝓛 σ A) (ht : 𝓛.TaxaDNF σ κ) :
    ∀ s : ℂ, σ - κ / 2 < s.re → 0 < s.re → s ≠ 1 → 𝓛.L s ≠ 0 := by
  intro s hs h0 hs1
  rcases le_or_gt σ s.re with hσs | hσs
  · exact h.semZeros s hσs hs1
  set δ := (2 * (σ - s.re) + κ) / 2 with hδ
  have hδκ : δ < κ := by linarith
  have hδ0 : 0 < δ := by linarith
  obtain ⟨K₀, hK₀⟩ := ht δ hδκ
  set K₁ := max K₀ 0 with hK₁
  have hK₁0 : 0 ≤ K₁ := le_max_right _ _
  set B := 𝓛.BF σ with hB
  have hB0 : 0 ≤ B := integral_nonneg fun τ => by positivity
  set Q := 2 * π * B * K₁ * 2 ^ δ with hQ
  have hQ0 : 0 ≤ Q := by positivity
  set θ := σ - δ / 2 with hθ
  have hθs : θ < s.re := by linarith
  have hcota : ∀ x : ℝ, 1 ≤ x → ‖𝓛.GF σ x‖ ≤ Real.sqrt Q / (2 * π) * x ^ θ := by
    intro x hx
    have hx0 : 0 < x := by linarith
    have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast hx)
    have hNx : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
    have hxN : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    have hN1' : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast hN1
    have hpiso := piso_DNF h hN1 hNx
    have hD' : 𝓛.DNF σ ⌊x⌋₊ ≤ K₁ * (⌊x⌋₊ : ℝ) ^ (-δ) :=
      (hK₀ _ hN1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    have hNd : (⌊x⌋₊ : ℝ) ^ (-δ) ≤ 2 ^ δ * x ^ (-δ) := by
      have h1 : (⌊x⌋₊ : ℝ) ^ (-δ) ≤ (x / 2) ^ (-δ) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
      rw [Real.div_rpow hx0.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
        div_inv_eq_mul] at h1
      linarith
    have hsq : (2 * π) ^ 2 * ‖𝓛.GF σ x‖ ^ 2 ≤ Q * x ^ (2 * θ) := by
      have e : x ^ (2 * θ) = x ^ (2 * σ) * x ^ (-δ) := by
        rw [← Real.rpow_add hx0]; congr 1; rw [hθ]; ring
      rw [e]
      calc (2 * π) ^ 2 * ‖𝓛.GF σ x‖ ^ 2 ≤ x ^ (2 * σ) * (2 * π) * B * 𝓛.DNF σ ⌊x⌋₊ := hpiso
        _ ≤ x ^ (2 * σ) * (2 * π) * B * (K₁ * (2 ^ δ * x ^ (-δ))) := by
            gcongr
            exact hD'.trans (mul_le_mul_of_nonneg_left hNd hK₁0)
        _ = Q * (x ^ (2 * σ) * x ^ (-δ)) := by rw [hQ]; ring
    have hR : 0 ≤ Real.sqrt Q / (2 * π) * x ^ θ := by positivity
    rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero]
    have hxθ : (x ^ θ) ^ 2 = x ^ (2 * θ) := by
      rw [mul_comm (2 : ℝ) θ, Real.rpow_mul hx0.le, Real.rpow_two]
    have e2 : (Real.sqrt Q / (2 * π) * x ^ θ) ^ 2 = Q * x ^ (2 * θ) / (2 * π) ^ 2 := by
      rw [mul_pow, div_pow, Real.sq_sqrt hQ0, hxθ]; ring
    rw [e2, le_div_iff₀ (by positivity)]
    linarith
  exact semZeros_de_cota h hcota s hθs h0 hs1

/-! ## 8. O produto e a junção -/

/-- **O produto** `𝓛₁ · 𝓛₂`: `L = L₁ L₂`, `M = M₁ M₂`, `μ = μ₁ ⍟ μ₂`. -/
noncomputable def ClasseL.mul (𝓛₁ 𝓛₂ : ClasseL) : ClasseL where
  L s := 𝓛₁.L s * 𝓛₂.L s
  M s := 𝓛₁.M s * 𝓛₂.M s
  μ := LSeries.convolution 𝓛₁.μ 𝓛₂.μ
  somavel s hs := (𝓛₁.somavel s hs).convolution (𝓛₂.somavel s hs)
  serie s hs := by
    rw [LSeries_convolution' (𝓛₁.somavel s hs) (𝓛₂.somavel s hs), 𝓛₁.serie s hs, 𝓛₂.serie s hs]
  inversa s hs hs1 hL := by
    have h1 : 𝓛₁.L s ≠ 0 := left_ne_zero_of_mul hL
    have h2 : 𝓛₂.L s ≠ 0 := right_ne_zero_of_mul hL
    calc 𝓛₁.M s * 𝓛₂.M s * (𝓛₁.L s * 𝓛₂.L s) = (𝓛₁.M s * 𝓛₁.L s) * (𝓛₂.M s * 𝓛₂.L s) := by ring
      _ = 1 := by rw [𝓛₁.inversa s hs hs1 h1, 𝓛₂.inversa s hs hs1 h2, one_mul]
  semZeros_um s hs := mul_ne_zero (𝓛₁.semZeros_um s hs) (𝓛₂.semZeros_um s hs)
  holoL s hs hs1 := (𝓛₁.holoL s hs hs1).mul (𝓛₂.holoL s hs hs1)
  holoM s hs h := by
    rcases h with h | h
    · exact (𝓛₁.holoM s hs (Or.inl h)).mul (𝓛₂.holoM s hs (Or.inl h))
    · exact (𝓛₁.holoM s hs (Or.inr (left_ne_zero_of_mul h))).mul
        (𝓛₂.holoM s hs (Or.inr (right_ne_zero_of_mul h)))

theorem rpow_metade {t η : ℝ} (ht : 0 < t) : t ^ (η / 2) * t ^ (η / 2) = t ^ η := by
  rw [← Real.rpow_add ht]; ring_nf

/-- **Retas boas se multiplicam**, com os expoentes de `L` somados. -/
theorem RetaBoa.mul {𝓛₁ 𝓛₂ : ClasseL} {σ A B : ℝ} (h₁ : RetaBoa 𝓛₁ σ A) (h₂ : RetaBoa 𝓛₂ σ B)
    (hAB : A + B < 3 / 2) : RetaBoa (𝓛₁.mul 𝓛₂) σ (A + B) where
  pos := h₁.pos
  lt_um := h₁.lt_um
  A_lt := hAB
  semZeros s hs hs1 := mul_ne_zero (h₁.semZeros s hs hs1) (h₂.semZeros s hs hs1)
  cotaM η hη := by
    obtain ⟨C₁, hC₁, k₁⟩ := h₁.cotaM (η / 2) (by linarith)
    obtain ⟨C₂, hC₂, k₂⟩ := h₂.cotaM (η / 2) (by linarith)
    refine ⟨C₁ * C₂, by positivity, fun s hs => ?_⟩
    show ‖𝓛₁.M s * 𝓛₂.M s‖ ≤ _
    have ht : (0 : ℝ) < 1 + |s.im| := by positivity
    rw [norm_mul, ← rpow_metade ht]
    calc ‖𝓛₁.M s‖ * ‖𝓛₂.M s‖ ≤ (C₁ * (1 + |s.im|) ^ (η / 2)) * (C₂ * (1 + |s.im|) ^ (η / 2)) :=
          mul_le_mul (k₁ s hs) (k₂ s hs) (norm_nonneg _) (by positivity)
      _ = _ := by ring
  cotaL := by
    obtain ⟨C₁, hC₁, k₁⟩ := h₁.cotaL
    obtain ⟨C₂, hC₂, k₂⟩ := h₂.cotaL
    refine ⟨C₁ * C₂, by positivity, fun τ => ?_⟩
    show ‖𝓛₁.L (σ + τ * I) * 𝓛₂.L (σ + τ * I)‖ ≤ _
    have ht : (0 : ℝ) < 1 + |τ| := by positivity
    rw [norm_mul, Real.rpow_add ht]
    calc ‖𝓛₁.L (σ + τ * I)‖ * ‖𝓛₂.L (σ + τ * I)‖ ≤ (C₁ * (1 + |τ|) ^ A) * (C₂ * (1 + |τ|) ^ B) :=
          mul_le_mul (k₁ τ) (k₂ τ) (norm_nonneg _) (by positivity)
      _ = _ := by ring

/-- **A junção** (proposta R110, item 3, direção do teto): uma única taxa do produto certifica a região sem
zeros dos dois fatores: `TaxaDNF (𝓛₁·𝓛₂) σ κ ⟹ L₁ ≠ 0 e L₂ ≠ 0` em `Re s > σ − κ/2`. -/
theorem juncao {𝓛₁ 𝓛₂ : ClasseL} {σ A κ : ℝ} (h : RetaBoa (𝓛₁.mul 𝓛₂) σ A)
    (ht : (𝓛₁.mul 𝓛₂).TaxaDNF σ κ) :
    ∀ s : ℂ, σ - κ / 2 < s.re → 0 < s.re → s ≠ 1 → 𝓛₁.L s ≠ 0 ∧ 𝓛₂.L s ≠ 0 := by
  intro s hs h0 hs1
  have := teto h ht s hs h0 hs1
  exact ⟨left_ne_zero_of_mul this, right_ne_zero_of_mul this⟩

/-- Se o produto de uma lista não se anula em `s`, nenhum fator se anula. -/
theorem foldr_L_ne_zero (𝓛s : List ClasseL) (𝓛₀ : ClasseL) {s : ℂ}
    (hP : (𝓛s.foldr ClasseL.mul 𝓛₀).L s ≠ 0) : ∀ 𝓛 ∈ 𝓛s, 𝓛.L s ≠ 0 := by
  induction 𝓛s with
  | nil => intro 𝓛 h; simp at h
  | cons a t ih =>
    intro 𝓛 h𝓛
    have hP' : a.L s * (t.foldr ClasseL.mul 𝓛₀).L s ≠ 0 := hP
    rcases List.mem_cons.mp h𝓛 with rfl | hm
    · exact left_ne_zero_of_mul hP'
    · exact ih (right_ne_zero_of_mul hP') 𝓛 hm

/-- **Junção para uma família finita**: a taxa do produto `𝓛₁ ⋯ 𝓛_k · 𝓛₀` certifica todos os fatores. -/
theorem juncao_lista (𝓛s : List ClasseL) (𝓛₀ : ClasseL) {σ A κ : ℝ}
    (h : RetaBoa (𝓛s.foldr ClasseL.mul 𝓛₀) σ A) (ht : (𝓛s.foldr ClasseL.mul 𝓛₀).TaxaDNF σ κ) :
    ∀ 𝓛 ∈ 𝓛s, ∀ s : ℂ, σ - κ / 2 < s.re → 0 < s.re → s ≠ 1 → 𝓛.L s ≠ 0 :=
  fun 𝓛 h𝓛 s hs h0 hs1 => foldr_L_ne_zero 𝓛s 𝓛₀ (teto h ht s hs h0 hs1) 𝓛 h𝓛

/-! ## 9. Instâncias: `ζ` (incondicional em `Θ < σ < 1`) e `L(s, χ)` -/

open ATK.ZeroClasses.BDTheta (Teta semZeros_Teta meio_le_Teta)

/-- `ζ` na classe `𝓛`: `M = F = (s − 1)/ζ₁(s)`, `μ` = Möbius. -/
noncomputable def classeZeta : ClasseL where
  L := riemannZeta
  M := ATK.RHLogZeta.F
  μ := ATK.ZeroClasses.LittlewoodMu.mu
  somavel s hs := ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  serie s hs := ATK.ZeroClasses.LittlewoodMu.LSeries_mu hs
  inversa s _ hs1 hL := by rw [ATK.RHLogZeta.F_eq hs1, inv_mul_cancel₀ hL]
  semZeros_um s hs := riemannZeta_ne_zero_of_one_lt_re hs
  holoL s _ hs1 := differentiableAt_riemannZeta hs1
  holoM s _ h := by
    have hz : riemannZeta₁ s ≠ 0 := by
      by_cases hs1 : s = 1
      · subst hs1; rw [riemannZeta₁_one]; exact one_ne_zero
      · rcases h with h | h
        · exact absurd h hs1
        · rw [ATK.RHLogZeta.zeta₁_eq hs1]; exact mul_ne_zero (sub_ne_zero.mpr hs1) h
    exact ((differentiableAt_id.sub (differentiableAt_const _))).div
      (differentiable_riemannZeta₁ s) hz

/-- **`ζ` tem reta boa** em todo `σ ∈ (Θ, 1)`, com qualquer expoente `η ∈ (0, 3/2)` para `ζ` na reta. -/
theorem retaBoa_zeta {σ η : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) (hη : 0 < η) (hη2 : η < 3 / 2) :
    RetaBoa classeZeta σ η where
  pos := by linarith [meio_le_Teta]
  lt_um := hσ1
  A_lt := hη2
  semZeros s hs _ := semZeros_Teta s (by linarith)
  cotaM η' hη' := by
    have hT := meio_le_Teta
    obtain ⟨C, hC, hF⟩ := ATK.ZeroClasses.QuasiRH.norm_F_le semZeros_Teta hT (by linarith)
      (δ := σ - Teta) (η := η') (by linarith) (by linarith) hη'
    exact ⟨C, hC, fun s hs => hF s (by linarith)⟩
  cotaL := ATK.ZeroClasses.BDTaxa.norm_zeta_linha semZeros_Teta meio_le_Teta (by linarith) hσ hσ1 hη

/-- **Para `ζ`**: a taxa da nova distância `D_N^ζ(σ)` também satisfaz `κ ≤ 2(σ − Θ)`. -/
theorem taxaF_zeta_le {σ κ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) (ht : classeZeta.TaxaDNF σ κ) :
    κ ≤ 2 * (σ - Teta) := by
  by_contra hlt
  push Not at hlt
  have h := retaBoa_zeta hσ hσ1 (η := 1) one_pos (by norm_num)
  have hT := meio_le_Teta
  set θ := max (σ - κ / 2) (1 / 4) with hθ
  have hθT : θ < Teta := max_lt (by linarith) (by linarith)
  apply ATK.ZeroClasses.Unilateral.nao_semZeros hθT
  intro s hs
  by_cases hs1 : s = 1
  · subst hs1; exact semZeros_Teta 1 (by simp; linarith)
  · exact teto h ht s (lt_of_le_of_lt (le_max_left _ _) hs)
      (by linarith [le_max_right (σ - κ / 2) (1 / 4)]) hs1

/-- `L(s, χ)`, `χ ≠ 1`, na classe `𝓛`: `M = 1/L`, `μ = χ·μ`. -/
noncomputable def classeDirichlet {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ClasseL where
  L := DirichletCharacter.LFunction χ
  M s := (DirichletCharacter.LFunction χ s)⁻¹
  μ := (fun n : ℕ => χ n) * fun n => ((ArithmeticFunction.moebius n : ℤ) : ℂ)
  somavel s hs := DirichletCharacter.LSeriesSummable_mul χ
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs)
  serie s hs := by
    have h1 := DirichletCharacter.LSeries.mul_mu_eq_one χ hs
    rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
    exact eq_inv_of_mul_eq_one_right h1
  inversa s _ _ hL := inv_mul_cancel₀ hL
  semZeros_um s hs := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
  holoL s _ _ := DirichletCharacter.differentiableAt_LFunction χ s (Or.inr hχ)
  holoM s _ h := by
    have hL : DirichletCharacter.LFunction χ s ≠ 0 := by
      rcases h with rfl | h
      · exact DirichletCharacter.LFunction_apply_one_ne_zero hχ
      · exact h
    exact (DirichletCharacter.differentiableAt_LFunction χ s (Or.inr hχ)).inv hL

/-- **RH e GRH(χ) certificadas por uma taxa só**: se `L(s, χ)` tem reta boa em `σ ∈ (Θ, 1)` com expoente `A`
(hipótese: a Mathlib ainda não tem cotas de `L(s, χ)` em faixas), então a taxa `κ` de `D_N^{ζ·L_χ}(σ)` dá
`ζ(s) ≠ 0` e `L(s, χ) ≠ 0` em `Re s > σ − κ/2`. -/
theorem juncao_zeta_dirichlet {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    {σ A η κ : ℝ} (hσ : Teta < σ) (hσ1 : σ < 1) (hη : 0 < η) (hη2 : η < 3 / 2)
    (hD : RetaBoa (classeDirichlet χ hχ) σ A)
    (hA : η + A < 3 / 2) (ht : (classeZeta.mul (classeDirichlet χ hχ)).TaxaDNF σ κ) :
    ∀ s : ℂ, σ - κ / 2 < s.re → 0 < s.re → s ≠ 1 →
      riemannZeta s ≠ 0 ∧ DirichletCharacter.LFunction χ s ≠ 0 :=
  juncao (𝓛₁ := classeZeta) (𝓛₂ := classeDirichlet χ hχ) ((retaBoa_zeta hσ hσ1 hη hη2).mul hD hA) ht

end ATK.ZeroClasses.BDMonoide

#print axioms ATK.ZeroClasses.BDMonoide.ClasseL.somavel_real
#print axioms ATK.ZeroClasses.BDMonoide.ClasseL.WF_nonneg
#print axioms ATK.ZeroClasses.BDMonoide.RetaBoa.holoM'
#print axioms ATK.ZeroClasses.BDMonoide.continuous_linha
#print axioms ATK.ZeroClasses.BDMonoide.integrable_pot
#print axioms ATK.ZeroClasses.BDMonoide.um_mais_sq_ge
#print axioms ATK.ZeroClasses.BDMonoide.inv_um_mais_sq_le
#print axioms ATK.ZeroClasses.BDMonoide.peso_le
#print axioms ATK.ZeroClasses.BDMonoide.integrable_KM
#print axioms ATK.ZeroClasses.BDMonoide.norm_P_le
#print axioms ATK.ZeroClasses.BDMonoide.continuous_P
#print axioms ATK.ZeroClasses.BDMonoide.integrable_resto
#print axioms ATK.ZeroClasses.BDMonoide.integrable_B
#print axioms ATK.ZeroClasses.BDMonoide.piso_GF
#print axioms ATK.ZeroClasses.BDMonoide.piso_DNF
#print axioms ATK.ZeroClasses.BDMonoide.differentiableAt_fM
#print axioms ATK.ZeroClasses.BDMonoide.GF_desloca
#print axioms ATK.ZeroClasses.BDMonoide.GF_serie
#print axioms ATK.ZeroClasses.BDMonoide.norm_GF_le
#print axioms ATK.ZeroClasses.BDMonoide.continuousAt_GF
#print axioms ATK.ZeroClasses.BDMonoide.mellin_gUF
#print axioms ATK.ZeroClasses.BDMonoide.gUF_top
#print axioms ATK.ZeroClasses.BDMonoide.gUF_bot
#print axioms ATK.ZeroClasses.BDMonoide.anula_convexo
#print axioms ATK.ZeroClasses.BDMonoide.anula_limite
#print axioms ATK.ZeroClasses.BDMonoide.semZeros_de_extensao
#print axioms ATK.ZeroClasses.BDMonoide.semZeros_de_cota
#print axioms ATK.ZeroClasses.BDMonoide.teto
#print axioms ATK.ZeroClasses.BDMonoide.rpow_metade
#print axioms ATK.ZeroClasses.BDMonoide.RetaBoa.mul
#print axioms ATK.ZeroClasses.BDMonoide.juncao
#print axioms ATK.ZeroClasses.BDMonoide.foldr_L_ne_zero
#print axioms ATK.ZeroClasses.BDMonoide.juncao_lista
#print axioms ATK.ZeroClasses.BDMonoide.retaBoa_zeta
#print axioms ATK.ZeroClasses.BDMonoide.taxaF_zeta_le
#print axioms ATK.ZeroClasses.BDMonoide.juncao_zeta_dirichlet
