import Mathlib.Data.Real.Basic  --实数基础理论
import Mathlib.Data.Matrix.Basic --矩阵的基本操作和符号法
import Mathlib.Data.Matrix.Notation
import Mathlib.Analysis.Calculus.FDeriv.Basic --提供导数的定义和基本性质
import Mathlib.Analysis.Calculus.ContDiff.Basic  --定义连续可微性及其高阶形式
import Mathlib.Analysis.Calculus.Gradient.Basic  --梯度相关
import Mathlib.Analysis.InnerProductSpace.Basic --内积相关
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic  --自然数 ℕ 的基础定义与定理
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.InnerProductSpace.EuclideanDist  --欧几里得空间的内积结构
import Mathlib.Analysis.InnerProductSpace.PiL2  --内积空间的结构和相关定理
import Mathlib.LinearAlgebra.Matrix.Symmetric --对称矩阵
import Mathlib.LinearAlgebra.Matrix.PosDef  --正定矩阵的定义和性质
import Mathlib.LinearAlgebra.Matrix.DotProduct --向量与矩阵相关的点积定义
import Mathlib.Data.Matrix.Mul  --矩阵乘法的定义与基本性质
import Mathlib.Algebra.Ring.CharZero
import Init.Data.Int.Lemmas  --整数 ℤ 的基础引理
import Mathlib.Algebra.Group.Defs  --群、加法群等代数结构的基础定义
import Mathlib.Algebra.Star.Basic  --Star 运算（*）的基础定义
import Mathlib.Algebra.BigOperators.Ring.Finset


open Matrix
open Real
open scoped BigOperators
open Fin
open CharZero
open scoped ComplexConjugate
open Matrix BigOperators

namespace PH --自定义命名空间

-- 向量场定义(定义一个别名来表示)
abbrev VectorField (n : ℕ) := (Fin n → ℝ) → (Fin n → ℝ)

-- 光滑实值函数定义
abbrev SmoothFunction (n : ℕ) := (Fin n → ℝ) → ℝ

-- 判断函数是否 C^∞
def IsSmooth {n : ℕ} (f : SmoothFunction n) : Prop :=
  ContDiff ℝ ⊤ f

-- 梯度定义：将 fderiv 映射为向量
noncomputable def grad {n : ℕ} (f : SmoothFunction n) (x : Fin n → ℝ) : Fin n → ℝ :=
  let df : (Fin n → ℝ) →L[ℝ] ℝ := fderiv ℝ f x
  fun i ↦ df (Pi.single i 1)

-- 反对称矩阵定义
def IsSkewSymmetric {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Mᵀ = -M

lemma neg_nonpos_of_nonneg {a : ℝ} (h : 0 ≤ a) : (-a) ≤ 0 := by linarith

-- star 在实数上恒等
lemma star_eq_id_real (v : Fin n → ℝ) : star v = v := by
  ext i
  simp [star]

lemma neg_dot_product (a b : Fin n → ℝ) : (-a) ⬝ᵥ b = - (a ⬝ᵥ b) := by
  simp [dotProduct, Fin.sum_univ_succ, mul_neg, neg_mul, mul_comm]

-- 反对称矩阵内积为0，若矩阵 J 是反对称的，即 J = -J，则任意向量 v 满足 vᵀ J v = 0
lemma dotProduct_skew_zero {n : ℕ} (J : Matrix (Fin n) (Fin n) ℝ)
  (v : Fin n → ℝ) (hJ : Jᵀ = -J) : v ⬝ᵥ (J *ᵥ v ) = 0 := by
  have h1 : v ⬝ᵥ (J *ᵥ v) = - (v ⬝ᵥ (J *ᵥ v)) :=
    calc
      v ⬝ᵥ ( J *ᵥ v )
          = (v ᵥ* J) ⬝ᵥ v := by rw [dotProduct_mulVec]
        _ = (Jᵀ *ᵥ v )⬝ᵥ v := by rw [← mulVec_transpose]
        _ = (-J *ᵥ v) ⬝ᵥ v := by rw [hJ]
        _ = -(J *ᵥ v) ⬝ᵥ v := by rw [neg_mulVec]
        _ = -(J *ᵥ v ⬝ᵥ v) := by rw [neg_dot_product]
        _ = - (v ⬝ᵥ (J *ᵥ v)) := by rw [dotProduct_comm]
  exact CharZero.eq_neg_self_iff.mp h1

lemma dotProduct_star_eq_real_symm {m : ℕ} (R : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) :
  R *ᵥ x ⬝ᵥ star x = R *ᵥ x ⬝ᵥ x := by
  rw [star_eq_id_real]

lemma Nat.sub_lt_of_le_of_lt {m n k : ℕ} (h₁ : n ≤ m) (h₂ : m < n + k) : m - n < k := by
  have : m = n + (m - n) := (Nat.add_sub_cancel' h₁).symm
  rw [this] at h₂
  exact Nat.lt_of_add_lt_add_left h₂

--构造Fin (n1+n2)块对角矩阵
def blockDiagFin {n1 n2 m1 m2 : ℕ} (A : Matrix (Fin n1) (Fin m1) ℝ)
  (B : Matrix (Fin n2) (Fin m2) ℝ) : Matrix (Fin (n1+n2)) (Fin (m1+m2)) ℝ :=
fun i j =>
  if hi : (i : ℕ) < n1 then
    if hj : (j : ℕ) < m1 then
      A ⟨i.val, hi⟩ ⟨j.val, hj⟩
    else 0
  else
    if hj : (j : ℕ) < m1 then
      0
    else
      B ⟨i.val - n1, Nat.sub_lt_of_le_of_lt (Nat.le_of_not_lt hi) i.isLt⟩
        ⟨j.val - m1, Nat.sub_lt_of_le_of_lt (Nat.le_of_not_lt hj) j.isLt⟩

-- 左投影：从 x : Fin (n1 + n2) → ℝ 提取左侧 Fin n1 → ℝ -/
def proj_left {n1 n2 : ℕ} (x : Fin (n1 + n2) → ℝ) : Fin n1 → ℝ :=
  fun i => x ⟨i.val, by
    -- i.isLt : i.val < n1
    -- 需证明 i.val < n1 + n2，这里使用 n1 ≤ n1 + n2
    exact (Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n1 n2))⟩

-- 右投影：从 x : Fin (n1 + n2) → ℝ 提取右侧 Fin n2 → ℝ -/
def proj_right {n1 n2 : ℕ} (x : Fin (n1 + n2) → ℝ) : Fin n2 → ℝ :=
  fun j => x ⟨j.val + n1, by
    have h := Nat.add_lt_add_right j.isLt n1
    rwa [Nat.add_comm n2 n1] at h⟩

-- 块对角矩阵转置等于各块转置
lemma blockDiagFin_transpose {n1 n2 : ℕ}
  (A : Matrix (Fin n1) (Fin n1) ℝ) (B : Matrix (Fin n2) (Fin n2) ℝ) :
  (blockDiagFin A B)ᵀ = blockDiagFin (Aᵀ) (Bᵀ) := by
  -- 用 matrix.ext 逐元素展开
  ext i j
  -- 分两种情况：i,j 在左块或者右块
  by_cases hi : i.val < n1
  · by_cases hj : j.val < n1
    · -- 左上角块
      simp [blockDiagFin, hi, hj]
    · -- 左下角块为0
      simp [blockDiagFin, hi, hj]
  · by_cases hj : j.val < n1
    · -- 右上角块为0
      simp [blockDiagFin, hi, hj]
    · -- 右下角块
      simp [blockDiagFin, hi, hj]

-- 块对角矩阵乘-1等于各块乘-1
lemma blockDiagFin_neg {n1 n2 : ℕ}
  (A : Matrix (Fin n1) (Fin n1) ℝ) (B : Matrix (Fin n2) (Fin n2) ℝ) :
  - blockDiagFin A B = blockDiagFin (-A) (-B) := by
  ext i j
  by_cases hi : i.val < n1
  · by_cases hj : j.val < n1
    · simp [blockDiagFin, hi, hj]
    · simp [blockDiagFin, hi, hj]
  · by_cases hj : j.val < n1
    · simp [blockDiagFin, hi, hj]
    · simp [blockDiagFin, hi, hj]

lemma blockDiagFin_conjTranspose {n1 n2 : ℕ}
  (A : Matrix (Fin n1) (Fin n1) ℝ) (B : Matrix (Fin n2) (Fin n2) ℝ) :
  (blockDiagFin A B)ᴴ = blockDiagFin Aᴴ Bᴴ := by
  ext i j
  simp [blockDiagFin, Matrix.conjTranspose, transpose, conjTranspose]
  split_ifs <;> simp

-- 分块向量辅助定义
def proj_left_vec {n1 n2 : ℕ} (v : Fin (n1 + n2) → ℝ) : Fin n1 → ℝ :=
  fun i => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n1 n2)⟩

def proj_right_vec {n1 n2 : ℕ} (v : Fin (n1 + n2) → ℝ) : Fin n2 → ℝ :=
  fun j => v ⟨j.val + n1, by
    have h := Nat.add_lt_add_right j.isLt n1
    rwa [Nat.add_comm n2 n1] at h⟩

-- 左半部分投影
def proj_left_index {n1 n2 : ℕ} (i : Fin n1) : Fin (n1 + n2) :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n1 n2)⟩

-- 右半部分投影
def proj_right_index {n1 n2 : ℕ} (j : Fin n2) : Fin (n1 + n2) :=
  ⟨j.val + n1, by
    rw [Nat.add_comm]
    exact Nat.add_lt_add_left j.isLt n1⟩

--证明:块对角矩阵的二次型能够分解成左右两个部分
lemma blockDiagFin_mulVec_split {n1 n2 : ℕ}
  (A : Matrix (Fin n1) (Fin n1) ℝ) (B : Matrix (Fin n2) (Fin n2) ℝ)
  (v : Fin (n1 + n2) → ℝ) :
  star v ⬝ᵥ (blockDiagFin A B *ᵥ v) =
    star (proj_left_vec v) ⬝ᵥ A *ᵥ proj_left_vec v +
    star (proj_right_vec v) ⬝ᵥ B *ᵥ proj_right_vec v := by
  simp [dotProduct, Matrix.mulVec]
  -- 将对Fin (n1 + n2)的和拆成左右两块
  -- dotProduct会产生两个求和（分别对应castAdd/natAdd），所以用Fin.sum_univ_add
  rw [Fin.sum_univ_add]
  -- 处理左块：把内层对(Fin(n1 + n2))的和，拆成左右两块，再消去右块的零项
  have left_eq :
    (∑ i : Fin n1,
      v (Fin.castAdd n2 i) *
        ∑ k, blockDiagFin A B (Fin.castAdd n2 i) k * v k)
    = (∑ i : Fin n1,
        proj_left_vec v i * (A *ᵥ proj_left_vec v) i) := by
    -- 先把内层的和拆成对左索引和右索引的和
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_add]
    simp [blockDiagFin, proj_left_vec, Matrix.mulVec, dotProduct]
    congr
  -- 处理右块：与左块对称
  have right_eq :
    (∑ i : Fin n2,
      v (Fin.natAdd n1 i) *
        ∑ k, blockDiagFin A B (Fin.natAdd n1 i) k * v k)
    = (∑ i : Fin n2,
        proj_right_vec v i * (B *ᵥ proj_right_vec v) i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_add]
    simp [blockDiagFin, proj_right_vec, Matrix.mulVec, dotProduct, Fin.natAdd]
    simp [Nat.add_comm]
  rw [left_eq, right_eq]
  rfl

-- 块对角半正定
lemma blockDiagFin_posSemidef {n1 n2 : ℕ}
  {A : Matrix (Fin n1) (Fin n1) ℝ} {B : Matrix (Fin n2) (Fin n2) ℝ}
  (hA : A.PosSemidef) (hB : B.PosSemidef) :
  (blockDiagFin A B).PosSemidef := by
  unfold Matrix.PosSemidef
  constructor
  · -- Hermitian 性
    unfold Matrix.IsHermitian
    rw [blockDiagFin_conjTranspose]
    rw [hA.left.eq, hB.left.eq]
  · -- 半正定性
    intro v
    let v1 : Fin n1 → ℝ := fun i => v ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n1 n2)⟩
    let v2 : Fin n2 → ℝ := fun j => v ⟨j.val + n1, by
      have h := Nat.add_lt_add_right j.isLt n1
      rwa [Nat.add_comm n2 n1] at h⟩
    have h1 := hA.right v1
    have h2 := hB.right v2
    let v1 := proj_left_vec v
    let v2 := proj_right_vec v
    have h1 := hA.right v1
    have h2 := hB.right v2
    have h_sum := blockDiagFin_mulVec_split A B v
    rw [h_sum]
    exact add_nonneg h1 h2

-- 哈密顿系统结构体
structure HamiltonianSystem (n : Nat) where
  H : SmoothFunction n  -- 哈密顿量
  J : Matrix (Fin n) (Fin n) ℝ  -- 结构矩阵
  skew : IsSkewSymmetric J  -- 反对称性

-- 哈密顿系统动力学方程
noncomputable def HamiltonianSystem.dynamics {n : ℕ} (sys : HamiltonianSystem n)
  (x : Fin n → ℝ) : Fin n → ℝ :=
  let gradH := grad sys.H x
  sys.J *ᵥ gradH

-- 哈密顿能量变化率
noncomputable def HamiltonianSystem.energyRate {n : ℕ} (sys : HamiltonianSystem n)
  (x : Fin n → ℝ) : ℝ :=
  (grad sys.H x) ⬝ᵥ (sys.dynamics x)

-- 能量守恒定理
theorem energy_conservation (sys : HamiltonianSystem n) (x : Fin n → ℝ) :
  sys.energyRate x = 0 := by
  simp [HamiltonianSystem.energyRate, HamiltonianSystem.dynamics]
  apply dotProduct_skew_zero sys.J (grad sys.H x)
  exact sys.skew

-- 在此基础上，扩展为 Port-Hamiltonian 系统
-- Port-Hamiltonian 系统结构体
structure PHSystem (n m : ℕ) where
  H : SmoothFunction n  -- 哈密顿函数 H
  J : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ   -- 结构矩阵 J(x)
  R : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ   -- 耗散矩阵 R(x)
  G : (Fin n → ℝ) → Matrix (Fin n) (Fin m) ℝ   -- 输入矩阵 G(x)
  J_skew : ∀ x, IsSkewSymmetric (J x)
  R_symmetric : ∀ x, IsSymm (R x)
  R_psd : ∀ x, PosSemidef (R x)

--定义输出变量y
noncomputable def PHSystem.output {n m : ℕ}
 (sys : PHSystem n m) (x : Fin n → ℝ) : Fin m → ℝ :=
  let gradH := grad sys.H x
  (sys.G x)ᵀ *ᵥ gradH

-- PH 系统的动力学方程
noncomputable def PHSystem.dynamics {n m : ℕ}
 (sys : PHSystem n m) (x : Fin n → ℝ) (u : Fin m → ℝ) : Fin n → ℝ :=
  let gradH := grad sys.H x
  (sys.J x - sys.R x) *ᵥ gradH + sys.G x *ᵥ u

-- PH 系统能量变化率
noncomputable def PHSystem.energyRate {n m : ℕ}
 (sys : PHSystem n m) (x : Fin n → ℝ) (u : Fin m → ℝ) : ℝ :=
  let gradH := grad sys.H x
  gradH ⬝ᵥ sys.dynamics x u

-- 构造一个从HamiltonianSystem到Port-Hamiltonian System的嵌入
noncomputable def HamiltonianSystem.toPHSystem {n : ℕ}
 (sys : HamiltonianSystem n) : PHSystem n 0 :=
  {
    H := sys.H  --保留哈密顿函数
    J := fun _ ↦ sys.J  -- 结构矩阵J与状态无关，变为常值函数
    R := fun _ ↦ (0 : Matrix (Fin n) (Fin n) ℝ) -- 没有耗散，R(x)恒为0矩阵
    G := fun _ ↦ (0 : Matrix (Fin n) (Fin 0) ℝ) -- 没有输入，G(x)恒为0矩阵
    J_skew := fun x ↦ by
      exact sys.skew
    R_symmetric := fun x ↦ by
      exact Matrix.isSymm_zero
    R_psd := fun x ↦ by
      exact Matrix.PosSemidef.zero
  }

--动力学方程一致性定理
theorem HamiltonianSystem.toPHSystem_dynamics_eq {n : ℕ}
 (sys : HamiltonianSystem n) (x : Fin n → ℝ) :
    (sys.toPHSystem).dynamics x 0 = sys.dynamics x := by
    simp [HamiltonianSystem.dynamics, PHSystem.dynamics, HamiltonianSystem.toPHSystem]

--能量变化率一致性定理
theorem HamiltonianSystem.toPHSystem_energyRate_eq {n : ℕ}
  (sys : HamiltonianSystem n) (x : Fin n → ℝ) :
    (sys.toPHSystem).energyRate x 0 = sys.energyRate x := by
  simp [HamiltonianSystem.energyRate, PHSystem.energyRate,
       HamiltonianSystem.dynamics, PHSystem.dynamics,HamiltonianSystem.toPHSystem]

-- 能量守恒定理：当 R = 0 且 u = 0 时，能量变化率为 0
theorem PHSystem.energy_conservation (sys : PHSystem n m) (x : Fin n → ℝ) (u : Fin m → ℝ)
    (hR_zero : sys.R x = 0) (hu_zero : u = 0) : sys.energyRate x u = 0 := by
     let gradH := grad sys.H x
     let d := sys.dynamics x u
     --展开定义
     calc
      sys.energyRate x u = gradH ⬝ᵥ d := by rfl
      _ = gradH ⬝ᵥ (sys.dynamics x u) := by simp [d]
      _ = gradH ⬝ᵥ ((sys.J x - sys.R x) *ᵥ gradH + sys.G x *ᵥ u) := by
          rw [PHSystem.dynamics]
      _ = gradH ⬝ᵥ ((sys.J x - sys.R x) *ᵥ gradH) + gradH ⬝ᵥ (sys.G x *ᵥ u) := by
          rw [dotProduct_add]
      _ = gradH ⬝ᵥ ((sys.J x - sys.R x) *ᵥ gradH ) := by
          simp [hu_zero]
      _ = gradH ⬝ᵥ (sys.J x  *ᵥ gradH ) := by
          simp [hR_zero]
      _ = 0 := by
          apply dotProduct_skew_zero
          exact sys.J_skew x

--能量守恒一致性
theorem HamiltonianSystem.toPHSystem_preserves_energy {n : ℕ}
  (sys : HamiltonianSystem n) (x : Fin n → ℝ) :
    (sys.toPHSystem).energyRate x 0 = 0 := by
  -- 把 PHSystem 的能量变化率归约为 HamiltonianSystem 的能量变化率
  have h_reduc : (sys.toPHSystem).energyRate x 0 = sys.energyRate x :=
    HamiltonianSystem.toPHSystem_energyRate_eq sys x
  -- 目标变为证明 sys.energyRate x = 0
  rw [h_reduc]
  -- 展开HamiltonianSystem.energyRate/dynamics的定义并计算
  simp [HamiltonianSystem.energyRate, HamiltonianSystem.dynamics]
  -- 设gradH，并用 J 的反对称性证明点积为 0
  let gradH := grad sys.H x
  have h_zero : gradH ⬝ᵥ (sys.J *ᵥ gradH) = 0 := by
    apply dotProduct_skew_zero
    exact sys.skew
  -- 用上面等式完成证明
  simpa using h_zero

--能量耗散定理
theorem PHSystem.energy_dissipation
  (sys : PHSystem n m) (x : Fin n → ℝ) (u : Fin m → ℝ)
    (hu_zero : u = 0) : sys.energyRate x u ≤ 0 := by
    let gradH := grad sys.H x
    have hJ : gradH ⬝ᵥ (sys.J x *ᵥ gradH) = 0 := dotProduct_skew_zero (sys.J x) gradH (sys.J_skew x)
    calc
      sys.energyRate x u = gradH ⬝ᵥ (sys.dynamics x u) := by rfl
      _ = gradH ⬝ᵥ ((sys.J x - sys.R x) *ᵥ gradH + sys.G x *ᵥ u) := by
          rw [PHSystem.dynamics]
      _ = gradH ⬝ᵥ ((sys.J x - sys.R x) *ᵥ gradH ) := by
          simp [hu_zero]
      _ = gradH ⬝ᵥ (sys.J x *ᵥ gradH) - gradH ⬝ᵥ (sys.R x *ᵥ gradH) := by
          rw [sub_mulVec, dotProduct_sub]
      _ = 0 - gradH ⬝ᵥ (sys.R x *ᵥ gradH) := by
          rw[hJ]
      _ = - gradH ⬝ᵥ (sys.R x *ᵥ gradH) := by
          simp
      _ ≤ 0 := by
          let ⟨_, h_psd⟩ := sys.R_psd x
          let a := gradH ⬝ᵥ (sys.R x *ᵥ gradH)
          have h_eq : -gradH ⬝ᵥ (sys.R x *ᵥ gradH) = -a := by simp [a]
          rw [h_eq]
          exact neg_nonpos_of_nonneg (h_psd gradH)

--功率平衡
theorem PHSystem.power_balance
  (sys : PHSystem n m) (x : Fin n → ℝ) (u : Fin m → ℝ) :
    sys.energyRate x u =
    - (grad sys.H x ⬝ᵥ sys.R x *ᵥ grad sys.H x) + (sys.output x ⬝ᵥ u) := by
    let gradH := grad sys.H x
    let h := - (gradH ⬝ᵥ sys.R x *ᵥ gradH )
    have hJ : gradH ⬝ᵥ (sys.J x *ᵥ gradH) = 0 := dotProduct_skew_zero (sys.J x) gradH (sys.J_skew x)
    calc
        sys.energyRate x u  = gradH ⬝ᵥ (sys.dynamics x u) := by rfl
        _ = gradH ⬝ᵥ ((sys.J x - sys.R x) *ᵥ gradH + sys.G x *ᵥ u) := by
          rw [PHSystem.dynamics]
        _ = gradH ⬝ᵥ sys.J x *ᵥ gradH - gradH ⬝ᵥ sys.R x *ᵥ gradH + gradH ⬝ᵥ sys.G x *ᵥ u := by
          rw [sub_mulVec, dotProduct_add ,dotProduct_sub]
        _ = 0 - gradH ⬝ᵥ sys.R x *ᵥ gradH + gradH ⬝ᵥ sys.G x *ᵥ u := by
          rw [hJ]
        _ = - (gradH ⬝ᵥ sys.R x *ᵥ gradH ) + gradH ⬝ᵥ sys.G x *ᵥ u := by
          simp
        _ = h + gradH ⬝ᵥ sys.G x *ᵥ u := by
          rfl
        _ = h + (sys.G x)ᵀ *ᵥ gradH ⬝ᵥ u := by
          rw [dotProduct_mulVec , mulVec_transpose]
        _ = - (gradH ⬝ᵥ sys.R x *ᵥ gradH ) + (sys.G x)ᵀ *ᵥ gradH ⬝ᵥ u := by
          rfl
        _ = - (gradH ⬝ᵥ sys.R x *ᵥ gradH ) + (sys.output x ⬝ᵥ u):= by
          rw [PHSystem.output]

--被动性
theorem PHSystem.passivity
  (sys : PHSystem n m) (x : Fin n → ℝ) (u : Fin m → ℝ) :
    sys.energyRate x u ≤ sys.output x ⬝ᵥ u := by
    let gradH := grad sys.H x
    -- 从 psd 得到二次型非负
    rcases sys.R_psd x with ⟨_, h_psd⟩
    have h_nonneg : 0 ≤ gradH ⬝ᵥ (sys.R x *ᵥ gradH) := by
      simpa using h_psd gradH
    have h_le_zero : -(gradH ⬝ᵥ (sys.R x *ᵥ gradH)) ≤ 0 :=
      neg_nonpos.mpr h_nonneg
    -- 用功率平衡把energyRate改写成-(...) + (output ⋅ u)的形式
    have hb : sys.energyRate x u
            = - (gradH ⬝ᵥ sys.R x *ᵥ gradH) + (sys.output x ⬝ᵥ u) := by
      simpa [gradH] using (sys.power_balance x u)
    -- 由-(...) ≤ 0 推出：-(...) + (output⋅u) ≤ 0 + (output⋅u) = (output⋅u)
    have h_bound :
      - (gradH ⬝ᵥ sys.R x *ᵥ gradH) + (sys.output x ⬝ᵥ u)
      ≤ (sys.output x ⬝ᵥ u) := by
      simpa using add_le_add_right h_le_zero (sys.output x ⬝ᵥ u)
    -- 代回
    simpa [hb] using h_bound

def vstack {n1 n2 m : ℕ}
  (A : Matrix (Fin n1) (Fin m) ℝ)
  (B : Matrix (Fin n2) (Fin m) ℝ) :
  Matrix (Fin (n1 + n2)) (Fin m) ℝ :=
fun i j =>
  Fin.addCases
    (fun i1 => A i1 j)
    (fun i2 => B i2 j)
    i

noncomputable def PHSystem.interconnect_powerconserving
  {n1 n2 m : ℕ} (s1 : PHSystem n1 m) (s2 : PHSystem n2 m) : PHSystem (n1 + n2) m :=
{
  -- Hamiltonian: 子系统能量相加
  H := fun x => s1.H (proj_left x) + s2.H (proj_right x),
  -- 块对角矩阵 J
  J := fun x => blockDiagFin (s1.J (proj_left x)) (s2.J (proj_right x)),
  -- 块对角矩阵 R
  R := fun x => blockDiagFin (s1.R (proj_left x)) (s2.R (proj_right x)),
  -- 合并输入矩阵 G
  G := fun x => vstack (s1.G (proj_left x)) (s2.G (proj_right x))
  -- 块对角 J 反对称
  J_skew := by
    intro x
    unfold IsSkewSymmetric
    rw [blockDiagFin_transpose]
    rw [s1.J_skew (proj_left x), s2.J_skew (proj_right x)]
    rw [blockDiagFin_neg],
  -- 块对角 R 对称
  R_symmetric := by
    intro x
    unfold Matrix.IsSymm
    rw [blockDiagFin_transpose]
    rw [s1.R_symmetric (proj_left x), s2.R_symmetric (proj_right x)],
  -- 块对角 R 半正定
  R_psd := by
    intro x
    exact blockDiagFin_posSemidef (s1.R_psd (proj_left x)) (s2.R_psd (proj_right x))
}

noncomputable def interconnect_output {n1 n2 m : ℕ}
  (s1 : PHSystem n1 m) (s2 : PHSystem n2 m) (x : Fin (n1 + n2) → ℝ) : Fin m → ℝ :=
  PHSystem.output s1 (proj_left x) + PHSystem.output s2 (proj_right x)

--互联继承定理
theorem interconnect_preserves_validity
  {n1 n2 m : ℕ} (s1 : PHSystem n1 m) (s2 : PHSystem n2 m) :
  (∀ x, IsSkewSymmetric ((s1.interconnect_powerconserving s2).J x)) ∧
  (∀ x, IsSymm ((s1.interconnect_powerconserving s2).R x)) ∧
  (∀ x, PosSemidef ((s1.interconnect_powerconserving s2).R x)) := by
  constructor
  · intro x
    exact (s1.interconnect_powerconserving s2).J_skew x
  constructor
  · intro x
    exact (s1.interconnect_powerconserving s2).R_symmetric x
  · intro x
    exact (s1.interconnect_powerconserving s2).R_psd x

--互联系统被动性
theorem interconnect_powerconserving_passive {n1 n2 : ℕ}
  (s1 : PHSystem n1 0) (s2 : PHSystem n2 0) :
  ∀ x, (s1.interconnect_powerconserving s2).energyRate x 0 ≤ 0 := by
  intro x
  let s := s1.interconnect_powerconserving s2
  let gradH := grad s.H x
  -- 能量率展开
  have h := s.power_balance x 0
  rw [PHSystem.output] at h
  -- 输出为空，G *ᵥ 0 = 0
  simp at h
  -- 得到 s.energyRate x 0 = - gradH ⬝ᵥ s.R x *ᵥ gradH
  have h1 : s.energyRate x 0 = - (gradH ⬝ᵥ s.R x *ᵥ gradH) := by
    simpa using h
  have h2 : 0 ≤ gradH ⬝ᵥ s.R x *ᵥ gradH :=
    let ⟨_, h_psd⟩ := s.R_psd x
    h_psd gradH
  rw [h1]
  exact neg_nonpos_of_nonneg h2

end PH

open PH

--应用：单连杆机械臂
noncomputable def singleLinkArm
  (I α d : ℝ) (hd : 0 ≤ d): PHSystem 2 1 :=
{
  -- 哈密顿量 H
  H := fun x =>
    let q := x 0
    let p := x 1
    (p^2) / (2 * I) + α * (1 - Real.cos q),
  -- 结构矩阵 J
  J := fun _ => !![0, 1; -1, 0],
  -- 耗散矩阵 R
  R := fun _ => !![0, 0; 0, d],
  -- 输入矩阵 G
  G := fun _ => !![0; 1],
  -- 结构矩阵与耗散矩阵的性质证明
  J_skew := by
    intro x
    ext i j <;> fin_cases i <;> fin_cases j <;> simp,
  R_symmetric := by
    intro x
    ext i j <;> fin_cases i <;> fin_cases j <;> simp,
  R_psd := by
    intro x
    constructor
    ·  -- Hermitian
      ext i j <;> fin_cases i <;> fin_cases j <;> simp
    ·  -- 半正定性
      intro v
      set a := vecHead (vecTail v)
      have h2 : 0 ≤ a^2 := pow_two_nonneg a
      -- d ≥ 0 & a^2 ≥ 0 ⇒ d * a^2 ≥ 0
      have hmul : 0 ≤ d * a^2 := mul_nonneg hd h2
      -- 目标是：0 ≤ d * (a * a)
      simpa [a, pow_two, mul_comm, mul_left_comm, mul_assoc] using hmul
}

-- 性质验证
-- d = 0 时，系统成为Hamiltonian系统，满足能量平衡。
theorem singleLink_energy_conservation (I α : ℝ) :
  ∀ x u,
    (singleLinkArm I α 0 (by simp)).energyRate x u =
    (singleLinkArm I α 0 (by simp)).output x ⬝ᵥ u :=
by
  intro x u
  let s := singleLinkArm I α 0 (by simp)
  -- 把目标显式改写成用s的版本：s.energyRate = s.output ⬝ᵥ u
  change s.energyRate x u = s.output x ⬝ᵥ u
  have hpb := PHSystem.power_balance s x u
  -- s.R 的二次型为 0
  have hR_zero : ∀ v : Fin 2 → ℝ, v ⬝ᵥ (s.R x *ᵥ v) = 0 := by
    intro v
    have : s.R x = !![0,0;0,0] := rfl
    rw [this]
    simp [Matrix.mulVec, dotProduct]
  -- 目标现在是：s.energyRate x u = s.output x ⬝ᵥ u
  rw [hpb]
  simp [hR_zero]


-- 对单连杆机械臂：当 u = 0 且 d ≥ 0 时，能量单调不增。
theorem singleLink_energy_dissipation
  (I α d : ℝ) (hd : 0 ≤ d) :
  ∀ x, (singleLinkArm I α d hd).energyRate x 0 ≤ 0 :=
by
  intro x
  let s := singleLinkArm I α d hd
  apply PHSystem.energy_dissipation s x 0
  rfl


--单连杆机械臂满足Port-Hamiltonian功率平衡恒等式。
theorem singleLink_power_balance
  (I α d : ℝ) (hd : 0 ≤ d) :
  ∀ x u,
    (singleLinkArm I α d hd).energyRate x u =
      (-(grad (singleLinkArm I α d hd).H x ⬝ᵥ
         ((singleLinkArm I α d hd).R x *ᵥ grad (singleLinkArm I α d hd).H x)))
      + (singleLinkArm I α d hd).output x ⬝ᵥ u :=
by
  intro x u
  simpa using PHSystem.power_balance (singleLinkArm I α d hd) x u

--单连杆机械臂是被动系统
theorem singleLink_passive
  (I α d : ℝ) (hd : 0 ≤ d) :
  ∀ x u,
    (singleLinkArm I α d hd).energyRate x u ≤
    (singleLinkArm I α d hd).output x ⬝ᵥ u :=
by
  intro x u
  apply PHSystem.passivity

--应用：双质量弹簧阻尼器（互联验证）
-- 子系统 1：mass1
noncomputable def mass1 (m1 k b : ℝ) (hk : 0 ≤ k) (hb : 0 ≤ b) : PHSystem 2 1 :=
{
  H := fun x =>
    let q1 := x 0
    let p1 := x 1
    p1^2 / (2 * m1) + (k / 2) * q1^2,
  J := fun _ => !![0, 1; -1, 0],
  R := fun _ => !![0, 0; 0, b],
  G := fun _ => !![0;1],  -- 弹簧力输入
  J_skew := by intro x; ext i j; fin_cases i <;> fin_cases j <;> simp,
  R_symmetric := by intro x; ext i j; fin_cases i <;> fin_cases j <;> simp,
  R_psd := by
    intro x
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp
    · intro v
      have h1 : star v ⬝ᵥ (!![0,0;0,b] *ᵥ v) = b * (v 1)^2 := by
        simp [dotProduct, Matrix.mulVec, star_eq_id_real]
        ring
      rw [h1]
      exact mul_nonneg hb (pow_two_nonneg (v 1))
}
-- 子系统 2：mass2
noncomputable def mass2 (m2 k b : ℝ) (hk : 0 ≤ k) (hb : 0 ≤ b) : PHSystem 2 1 :=
{
  H := fun x =>
    let q2 := x 0
    let p2 := x 1
    p2^2 / (2 * m2) + (k / 2) * q2^2,
  J := fun _ => !![0, 1; -1, 0],
  R := fun _ => !![0, 0; 0, b],
  G := fun _ => !![0;1],  -- 弹簧力输入
  J_skew := by intro x; ext i j; fin_cases i <;> fin_cases j <;> simp,
  R_symmetric := by intro x; ext i j; fin_cases i <;> fin_cases j <;> simp,
  R_psd := by
    intro x
    constructor
    · ext i j; fin_cases i <;> fin_cases j <;> simp
    · intro v
      have h1 : star v ⬝ᵥ (!![0,0;0,b] *ᵥ v) = b * (v 1)^2 := by
        simp [dotProduct, Matrix.mulVec, star_eq_id_real]
        ring
      rw [h1]
      exact mul_nonneg hb (pow_two_nonneg (v 1))
}

-- 互联:连接mass1和mass2
noncomputable def twoMassSpringDamping (m1 m2 k b : ℝ) (hk : 0 ≤ k) (hb : 0 ≤ b) :
  PHSystem 4 1 :=
  let s1 := mass1 m1 k b hk hb
  let s2 := mass2 m2 k b hk hb
  s1.interconnect_powerconserving s2

-- 验证互联系统的Port-Hamiltonian性质
theorem twoMass_interconnect_valid {m1 m2 k b : ℝ} (hk : 0 ≤ k) (hb : 0 ≤ b) :
  ∀ x,
    IsSkewSymmetric ((twoMassSpringDamping m1 m2 k b hk hb).J x) ∧
    IsSymm ((twoMassSpringDamping m1 m2 k b hk hb).R x) ∧
    PosSemidef ((twoMassSpringDamping m1 m2 k b hk hb).R x) := by
  intro x
  let h := interconnect_preserves_validity (mass1 m1 k b hk hb) (mass2 m2 k b hk hb)
  constructor
  · exact h.1 x
  constructor
  · exact h.2.1 x
  · exact h.2.2 x
