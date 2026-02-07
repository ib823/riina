# RIINA

**形式化验证编程语言。**

安全属性不是测试的，不是假设的——而是在编译时*数学证明*的。

---

## 什么是 RIINA？

RIINA 是一种编程语言，其中**每一个安全保证都有机器检查的数学证明**。如果你的程序能编译通过，它就是安全的——不是靠惯例，不是靠最佳实践，而是靠证明。

| RIINA 在编译时证明什么 | 如何实现 |
|---|---|
| 安全级别间无信息泄露 | 非干扰定理 (Coq) |
| 无未授权副作用执行 | 效果门代数 (Coq) |
| 类型安全（无运行时类型错误） | 进展 + 保持定理 (Coq) |
| 公开输出中无秘密数据 | 解密策略证明 (Coq) |
| 所有纯计算终止 | 强归一化证明 (Coq) |
| 无垃圾回收的内存安全 | 分离逻辑证明 (Coq) |

---

## 快速开始

### 安装

```bash
git clone https://github.com/ib823/riina.git
cd riina/03_PROTO
cargo build --release
```

编译器二进制文件为 `riinac`。零外部依赖。

### Hello World

创建 `hello.rii`：

```riina
fungsi utama() -> Teks kesan IO {
    biar mesej = "Selamat datang ke RIINA!";
    cetakln(mesej);
    pulang mesej;
}
```

```bash
riinac check hello.rii    # 类型检查和验证
riinac run hello.rii      # 直接运行
riinac build hello.rii    # 通过 C 编译为本地二进制文件
```

### 安全示例

```riina
// RIINA 在编译时防止信息泄露

fungsi proses_pembayaran(kad: Rahsia<Teks>, jumlah: Nombor) -> Teks kesan Kripto {
    // 'kad' 是 Rahsia（秘密）——编译器证明它永远不会到达公开输出

    biar hash = sha256(kad);           // 正确：对秘密数据进行加密操作
    biar resit = "Jumlah: " + ke_teks(jumlah);  // 正确：金额是公开的

    // cetakln(kad);                   // 编译错误：秘密数据在 IO 效果中
    // pulang kad;                     // 编译错误：秘密在公开返回值中

    pulang resit;                      // 正确：只返回公开数据
}
```

---

## 关键字参考

RIINA 使用**马来语**关键字。以下是对照表：

| RIINA (马来语) | 中文 | 英文 | 示例 |
|-------|------|------|------|
| `fungsi` | 函数 | fn | `fungsi tambah(x: Nombor) -> Nombor` |
| `biar` | 让 | let | `biar nama = "Ahmad";` |
| `kalau` | 如果 | if | `kalau x > 0 { ... }` |
| `lain` | 否则 | else | `lain { ... }` |
| `untuk` | 循环 | for | `untuk x dalam senarai { ... }` |
| `pulang` | 返回 | return | `pulang hasil;` |
| `padan` | 匹配 | match | `padan nilai { ... }` |
| `rahsia` | 秘密 | secret | `biar kunci: Rahsia<Teks>` |
| `dedah` | 解密 | declassify | `dedah(nilai)` |
| `kesan` | 效果 | effect | `kesan IO` |
| `bersih` | 纯 | pure | `kesan Bersih` |
| `betul` / `salah` | 真 / 假 | true / false | 布尔值 |

---

## 贡献

参见 [CONTRIBUTING.md](../../CONTRIBUTING.md) 了解贡献指南。

## 许可证

[RIINA Proprietary License](../../LICENSE)

---

*RIINA — Rigorous Immutable Invariant, No Assumptions*

*Q.E.D. Aeternum.*
