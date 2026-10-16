# SnPres —— Lean 4 形式化

本仓库在 Lean 4 + Mathlib 中形式化了论文

> 《对称群在标准生成元上的有界表现：比特长度 O(log n)》（2026 年 10 月）

主定理所依赖的论文中的全部论证都在 Lean 中给出了证明，没有 `sorry`。论文引用的四个经典结果以弱化形式作为公理（见下文）。

## 版本与编译

* Lean `v4.24.0`（见 `lean-toolchain`）
* Mathlib `v4.24.0`，commit `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`（见 `lakefile.toml`）

```
lake exe cache get      # 可选：下载 Mathlib 的编译结果
lake build              # 编译库 SnPres
lake env lean Check.lean
```

`Check.lean` 打印主要定理的陈述及其依赖的公理。`#print axioms SnPres.main_theorem` 的结果是 `propext`、`Classical.choice`、`Quot.sound` 以及四条公理 `SnPres.Classical.{sunday_bound, carmichael_bound, moore_bound, nagura}`，此外没有任何假设。

## 主要结果（命名空间 `SnPres`）

* `main_theorem`：存在常数 `r₀`、`c₀`，使得对每个 `n ≥ 2`，存在 `{x, y}` 上幂表达式的有限集 `R`，满足 `IsPresentation (xyv n _) R`，其中每个元素都是真正的幂表达式（`PE.WF`），且 `R.card ≤ r₀`、`presLength R ≤ c₀ * Nat.log 2 n`。
* `main_theorem_62`：当 `n ≥ 245` 时可取 `R.card ≤ 62`。证明给出 `c₀ = cLarge = 269991154`，且每个关系子的长度不超过 `486816 + 773576 (⌊log₂ n⌋ + 4)`（`main_large`）。
* `main_theorem_mathlib`、`main_theorem_mathlib_62`：对 Mathlib 自身的 `Equiv.Perm (Fin n)`（乘法 `σ * τ = σ ∘ τ`）、生成元 `Equiv.swap 0 1` 与 `finRotate n` 的相同陈述；关系子反向读取（`PE.rev`），长度不变。

`IsPresentation φ R` 的含义：每个关系子取值为 `1`，并且诱导同态 `PresentedGroup (toFreeGroup '' R) → G` 是双射（定义 2.4）。`presLength R = |{x,y}| + ∑_{E ∈ R} ℓ(E)`，其中 `ℓ` 是定义 2.1 的长度（`PE.length`，指数用二进制计）。

## 约定

与论文一致，置换右作用：`Sym n := (Equiv.Perm (Fin n))ᵐᵒᵖ`，`g * h` 表示"先 `g` 后 `h`"。生成元 `x = (0,1)`（`xs`）、`y = (0,1,…,n-1)`（`ys`，`i ↦ i+1 mod n`）；经 `i ↦ i+1` 即为 `(1,2)` 与 `(1,2,…,n)`。点的像用 `nv g i : ℕ` 表示（`i ≥ n` 时取 `i` 本身）。行向量与仿射映射的约定同论文：`α_{M,w} α_{M',w'} = α_{MM', wM'+w'}`。

## 公理（`SnPres/Axioms.lean`）

每条公理都弱于所引用的定理，只假设证明中实际用到的部分。

| 公理 | 引用的结果 | 实际假设的内容 |
|---|---|---|
| `sunday_bound p`（`p` 为素数，`p ≥ 5`） | Sunday 1972；BCLO 命题 3.3：`⟨a,c ∣ a^p, acacac⁻¹, (a^h c a^4 c)²⟩ ≅ PSL(2,p)` | 该群有限且阶 `≤ p(p²−1)/2` |
| `carmichael_bound M`（`M ≥ 1`） | Carmichael 1923：`⟨x₁…x_M ∣ x_i³, (x_i x_j)²⟩ ≅ A_{M+2}` | 有限且阶 `≤ (M+2)!/2` |
| `moore_bound n`（`n ≥ 2`） | Moore 1897：`S_n` 的 Coxeter 表现 | 有限且阶 `≤ n!` |
| `nagura m`（`m ≥ 25`） | Nagura 1952：实数 `ξ ≥ 25` 时 `(ξ, 6ξ/5)` 中有素数 | 只用整数 `ξ = m` 的情形 |

`check_axioms.py` 对这些关系子集合做数值检验（陪集枚举：Sunday 取 `p ≤ 17`，Carmichael 取 `M ≤ 5`，Moore 取 `n ≤ 7`；Nagura 检验到 `m ≤ 2·10⁵`）。这只是防止公理写错的核对，不属于证明。

## 与论文的对应

见英文版 `README.md` 中的对照表（文件名与定理名一一列出）。

## 证明路线与论文的不同之处

所有陈述都是论文的陈述；少数地方证明路线不同。

1. **引理 5.5**（`ASL(2,p)` 全部正规子群的分类，其证明用到 `PSL(2,p)` 的单性）没有形式化。定理 6.3 的 Step 5 只需要："`ASL(2,p)` 中含 `α_{M_L,e₁}` 的正规子群就是全群"。这就是 `normal_eq_top_of_mem`，对一切素数 `p` 直接证明。
2. **推论 5.4** 直接由命题 5.3 推出（十个关系子给出的群是 `ASL(2,p)` 的商），而不是用 Tietze 变换加引理 2.5。
3. **引理 6.2(b)** 在各循环 `C_i` 等长 `ℓ` 的情形下证明（论文只用到这一情形）：此时 `gπ` 把每个点映到两个显式的、长为 `1 + ℓr/2` 的循环之一中的下一个点，从而 `(gπ)^{1+ℓr/2} = 1`。
4. **定理 6.3 的 Steps 6–7**：阶的上界 `|Γ| ≤ 2|K| ≤ N!` 与论文相同；`L, U, T, X₀, X₁, Q` 生成 `S_N` 改由命题 6.4 得到（它们能写出 `(0,1)` 和 `(0,1,…,N−1)`），而不是用 `(ω,⋆,∞)` 型 3-循环。Step 6 中"`θ(α)` 是偶置换、因而 `Γ_A ≅ A_N`"这一附带结论不需要，未形式化。
5. **一致性**（定义 2.3，命题 4.3、6.4，定理 7.3）通过对 `occ`、`pw`、`ex` 的显式上界证明（`Bounds.lean`）。这些常数是粗略的上界；论文第 8 节数值计算得到的长度不属于证明，未形式化。
6. **小的 `n`**（`n < 245`）：论文中"每个 `S_n` 在 `x, y` 上都有某个有限表现"由 Mathlib 的 Schreier 引理证明（`exists_finite_presentation`）。
7. 原根 `λ` 与 `μ = λ⁻¹ mod p` 取在 `[1, p−1]` 中，用到 `(ℤ/p)ˣ` 是循环群。

形式化过程中没有发现论文的数学错误。
