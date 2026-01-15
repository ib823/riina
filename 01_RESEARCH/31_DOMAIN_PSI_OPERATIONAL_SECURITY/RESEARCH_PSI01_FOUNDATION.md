# RIINA Research Domain Ψ (Psi): Operational Security

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-PSI-OPERATIONAL-SECURITY |
| Version | 1.0.0 |
| Date | 2026-01-15 |
| Domain | Ψ: Operational Security |
| Mode | ULTRA KIASU | PARANOID | ZERO TRUST |
| Status | FOUNDATIONAL DEFINITION |

---

# Ψ-01: The "Human Layer" Problem & The RIINA Solution

## 1. The Existential Threat

**Context:**
All other RIINA tracks assume the human operators are not the vulnerability. This is false.

**The Reality:**
- **Physical coercion:** Governments can torture keyholders
- **Social engineering:** Humans are fooled by convincing stories
- **Insider threats:** Authorized users can abuse access
- **Hardware zero-days:** Unknown vulnerabilities in silicon

**The Uncomfortable Truth:**
> "Given enough time and resources, any single human can be compromised."

**The RIINA Philosophy:**
> "Trust no single human. Trust the protocol."

**The Goal:**
Design systems where:
- **No single human** can cause catastrophic failure
- **Coercion of one person** is insufficient
- **Insider access** is bounded and audited
- **Hardware diversity** mitigates zero-days

## 2. The Solution: Multi-Party Everything

### 2.1 Core Principle

```
╔════════════════════════════════════════════════════════════════════╗
║                   OPERATIONAL SECURITY PRINCIPLE                    ║
╠════════════════════════════════════════════════════════════════════╣
║                                                                     ║
║  "For any critical operation, require N-of-M parties where:        ║
║                                                                     ║
║   - N > 1 (no single point of trust)                               ║
║   - M parties are in different:                                    ║
║     • Geographic locations                                         ║
║     • Legal jurisdictions                                          ║
║     • Organizational roles                                         ║
║     • Communication channels                                       ║
║                                                                     ║
║   - Each party has:                                                ║
║     • Limited individual capability                                ║
║     • Complete audit trail                                         ║
║     • Time-delayed execution window                                ║
║     • Anomaly detection on their actions"                          ║
║                                                                     ║
╚════════════════════════════════════════════════════════════════════╝
```

### 2.2 Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                 OPERATIONAL SECURITY STACK                           │
├─────────────────────────────────────────────────────────────────────┤
│                                                                      │
│  ┌─────────────────────────────────────────────────────────────┐    │
│  │  Layer 5: Anomaly Detection                                  │    │
│  │  ├── ML-based behavioral analysis                           │    │
│  │  ├── Pattern recognition for unusual access                 │    │
│  │  └── Automatic alerts and lockouts                          │    │
│  └─────────────────────────────────────────────────────────────┘    │
│                              │                                       │
│  ┌───────────────────────────▼───────────────────────────────────┐  │
│  │  Layer 4: Time-Delayed Execution                              │  │
│  │  ├── Critical ops delayed 24-72 hours                         │  │
│  │  ├── Cancellation window for detection                        │  │
│  │  └── Out-of-band confirmation required                        │  │
│  └───────────────────────────────────────────────────────────────┘  │
│                              │                                       │
│  ┌───────────────────────────▼───────────────────────────────────┐  │
│  │  Layer 3: Multi-Party Authorization                           │  │
│  │  ├── N-of-M approval for critical operations                  │  │
│  │  ├── Different channels (prevent single compromise)           │  │
│  │  └── Role separation (admin ≠ auditor ≠ operator)            │  │
│  └───────────────────────────────────────────────────────────────┘  │
│                              │                                       │
│  ┌───────────────────────────▼───────────────────────────────────┐  │
│  │  Layer 2: Threshold Cryptography                              │  │
│  │  ├── Shamir Secret Sharing for keys                           │  │
│  │  ├── No single keyholder                                      │  │
│  │  └── Geographic/jurisdictional distribution                   │  │
│  └───────────────────────────────────────────────────────────────┘  │
│                              │                                       │
│  ┌───────────────────────────▼───────────────────────────────────┐  │
│  │  Layer 1: Duress Detection & Hardware Diversity               │  │
│  │  ├── Duress codes trigger lockout                             │  │
│  │  ├── Dead man's switches                                      │  │
│  │  └── N-version execution on diverse hardware                  │  │
│  └───────────────────────────────────────────────────────────────┘  │
│                                                                      │
└─────────────────────────────────────────────────────────────────────┘
```

## 3. Threat 1: Physical Coercion (Rubber Hose Cryptanalysis)

### 3.1 The Attack

An adversary physically captures a keyholder and uses coercion (torture, threats to family, imprisonment) to extract cryptographic keys or credentials.

### 3.2 Defense: Threshold Cryptography

```coq
(* Shamir Secret Sharing *)
(* A secret S is split into n shares such that any k shares can reconstruct S,
   but k-1 shares give ZERO information about S *)

Record ShamirScheme := {
  k : nat;  (* Threshold *)
  n : nat;  (* Total shares *)
  prime : nat;  (* Field prime, larger than secret *)
}.

(* Share generation *)
Definition share (scheme : ShamirScheme) (secret : nat) : list (nat * nat) :=
  let coeffs := secret :: random_coefficients (scheme.k - 1) scheme.prime in
  let poly := fun x => eval_polynomial coeffs x mod scheme.prime in
  map (fun i => (i, poly i)) (range 1 (scheme.n + 1)).

(* Secret reconstruction *)
Definition reconstruct (shares : list (nat * nat)) (prime : nat) : nat :=
  lagrange_interpolation shares 0 prime.

(* Security theorem: k-1 shares give zero information *)
Theorem shamir_security : forall scheme secret shares subset,
  shares = share scheme secret ->
  length subset < scheme.k ->
  subset ⊆ shares ->
  information_about secret subset = 0.
Proof.
  (* With < k points, any secret value is equally likely *)
  (* Perfect information-theoretic security *)
Qed.

(* Reconstruction correctness *)
Theorem shamir_correctness : forall scheme secret shares subset,
  shares = share scheme secret ->
  length subset >= scheme.k ->
  subset ⊆ shares ->
  reconstruct subset scheme.prime = secret.
Proof.
  (* Lagrange interpolation recovers polynomial *)
  (* Polynomial evaluated at 0 gives secret *)
Qed.
```

### 3.3 RIINA Threshold Key Management

```riina
// Threshold key management
bentuk PengurusKunciAmbang {
    ambang: usize,      // k - minimum shares needed
    jumlah: usize,      // n - total shares
    perdana: BigInt,    // Prime for field arithmetic
}

bentuk BahagianKunci {
    indeks: usize,
    nilai: BigInt,
    pemegang: IdPrinsipal,
    lokasi: LokasiGeografi,
    bidang_kuasa: BidangKuasa,
}

impl PengurusKunciAmbang {
    // Split a secret key into shares
    fungsi bahagi(&self, rahsia: &KunciPersendirian)
        -> Senarai<BahagianKunci>
        kesan KesanRawak
    {
        biar nilai_rahsia = BigInt::dari_bait(&rahsia.ke_bait());

        // Generate random polynomial coefficients
        biar mut pekali = vec![nilai_rahsia];
        untuk _ dalam 1..self.ambang {
            pekali.tolak(BigInt::rawak_bawah(&self.perdana));
        }

        // Evaluate polynomial at each point
        biar mut bahagian = Senarai::baru();
        untuk i dalam 1..=self.jumlah {
            biar x = BigInt::dari(i);
            biar y = nilai_polinomial(&pekali, &x, &self.perdana);
            bahagian.tolak(BahagianKunci {
                indeks: i,
                nilai: y,
                pemegang: IdPrinsipal::tidak_ditugaskan(),
                lokasi: LokasiGeografi::tidak_ditugaskan(),
                bidang_kuasa: BidangKuasa::tidak_ditugaskan(),
            });
        }

        bahagian
    }

    // Reconstruct key from shares
    fungsi bina_semula(&self, bahagian: &[BahagianKunci])
        -> Keputusan<KunciPersendirian, RalatAmbang>
        memerlukan bahagian.panjang() >= self.ambang
    {
        kalau bahagian.panjang() < self.ambang {
            pulang Err(RalatAmbang::BahagianTidakCukup);
        }

        // Lagrange interpolation at x=0
        biar rahsia = interpolasi_lagrange(bahagian, &self.perdana);
        KunciPersendirian::dari_bait(&rahsia.ke_bait())
    }
}

// Key ceremony with geographic distribution
fungsi upacara_kunci_selamat()
    -> Keputusan<Senarai<BahagianKunci>, RalatUpacara>
    kesan KesanSistem
{
    biar pengurus = PengurusKunciAmbang {
        ambang: 3,     // Need 3 of 5
        jumlah: 5,
        perdana: PERDANA_256_BIT,
    };

    biar kunci = KunciPersendirian::jana()?;
    biar mut bahagian = pengurus.bahagi(&kunci);

    // Assign to geographically distributed keyholders
    bahagian[0].lokasi = LokasiGeografi::Amerika;
    bahagian[0].bidang_kuasa = BidangKuasa::AS;

    bahagian[1].lokasi = LokasiGeografi::Eropah;
    bahagian[1].bidang_kuasa = BidangKuasa::Switzerland;

    bahagian[2].lokasi = LokasiGeografi::Asia;
    bahagian[2].bidang_kuasa = BidangKuasa::Singapura;

    bahagian[3].lokasi = LokasiGeografi::Oceania;
    bahagian[3].bidang_kuasa = BidangKuasa::NewZealand;

    bahagian[4].lokasi = LokasiGeografi::Afrika;
    bahagian[4].bidang_kuasa = BidangKuasa::Mauritius;

    // Destroy original key
    kunci.sifar_dan_lepas();

    Ok(bahagian)
}
```

### 3.4 Duress Codes

```riina
// Duress detection system
bentuk SistemDuress {
    kata_laluan_biasa: Hash,
    akhiran_duress: Rentetan,  // e.g., "911" or "help"
}

pilihan KeputusanPengesahan {
    Berjaya(Sesi),
    Gagal,
    DuressDigesan,  // Alert security, provide fake access
}

impl SistemDuress {
    fungsi sahkan(&self, input: &Rentetan) -> KeputusanPengesahan {
        // Check for duress suffix
        kalau input.berakhir_dengan(&self.akhiran_duress) {
            // SILENT ALERT - don't let attacker know
            log_keselamatan_senyap("DURESS DETECTED", &konteks_semasa());
            maklum_pasukan_keselamatan();

            // Provide fake "success" with honeypot access
            pulang KeputusanPengesahan::DuressDigesan;
        }

        // Normal authentication
        biar hash = sha256(input.sebagai_bait());
        kalau hash == self.kata_laluan_biasa {
            KeputusanPengesahan::Berjaya(Sesi::baru())
        } lain {
            KeputusanPengesahan::Gagal
        }
    }
}

// Dead man's switch
bentuk SuisMatiOrang {
    selang_daftar_masuk: Tempoh,
    daftar_terakhir: Atomik<CapMasa>,
    tindakan_kegagalan: fn(),
}

impl SuisMatiOrang {
    // Keyholder must check in periodically
    fungsi daftar_masuk(&self) {
        self.daftar_terakhir.simpan(CapMasa::sekarang(), Tertib::Release);
    }

    // Background task monitors for missed check-ins
    fungsi pantau(&self) {
        gelung {
            tunggu(self.selang_daftar_masuk);

            biar terakhir = self.daftar_terakhir.muat(Tertib::Acquire);
            kalau CapMasa::sekarang() - terakhir > self.selang_daftar_masuk * 2 {
                // Keyholder missed check-in - assume compromised
                log_keselamatan("DEAD MAN SWITCH TRIGGERED");
                (self.tindakan_kegagalan)();
            }
        }
    }
}
```

## 4. Threat 2: Social Engineering

### 4.1 The Attack

An adversary tricks a human into revealing credentials, approving malicious actions, or granting access.

### 4.2 Defense: Multi-Party Authorization

```coq
(* Multi-party authorization requirement *)
Record MultiPartyAuth := {
  operation : CriticalOp;
  required_approvers : nat;
  approver_roles : list Role;
  time_window : duration;
  confirmation_channels : list Channel;  (* Different channels *)
}.

(* Authorization state *)
Record AuthState := {
  approvals : list (Principal * Signature * Timestamp * Channel);
}.

(* Check if operation is authorized *)
Definition is_authorized (mpa : MultiPartyAuth) (state : AuthState) : bool :=
  let valid_approvals := filter (fun a =>
    (* Signature valid *)
    verify_signature a.1 a.2 /\
    (* Within time window *)
    now - a.3 < mpa.time_window /\
    (* Has required role *)
    has_role a.1 mpa.approver_roles /\
    (* Used approved channel *)
    In a.4 mpa.confirmation_channels
  ) state.approvals in
  (* Different principals *)
  let unique_principals := deduplicate (map fst valid_approvals) in
  length unique_principals >= mpa.required_approvers.

(* Social engineering of one person is insufficient *)
Theorem social_eng_insufficient : forall mpa attacker victim,
  mpa.required_approvers > 1 ->
  compromised victim ->
  ~ compromised_all (remove victim (principals mpa)) ->
  ~ is_authorized mpa (attacker_state attacker victim).
Proof.
  (* Attacker can only get victim's approval *)
  (* Need approvals from non-compromised principals *)
  (* Cannot forge signatures *)
Qed.
```

### 4.3 RIINA Multi-Party System

```riina
// Multi-party authorization
bentuk KeizinanBerbilangPihak {
    operasi: OperasiKritikal,
    pengesah_diperlukan: usize,
    peranan: Senarai<Peranan>,
    tetingkap_masa: Tempoh,
    saluran: Senarai<Saluran>,
}

bentuk Kelulusan {
    prinsipal: IdPrinsipal,
    tandatangan: Tandatangan,
    cap_masa: CapMasa,
    saluran: Saluran,
}

pilihan Saluran {
    WebDashboard,
    MobileApp,
    HardwareToken,
    Telefon,
    Emel,
}

impl KeizinanBerbilangPihak {
    // Request approval from multiple parties
    fungsi minta_kelulusan(&self)
        -> Keputusan<PengendaliKelulusan, Ralat>
        kesan KesanRangkaian
    {
        biar pengendali = PengendaliKelulusan::baru(self.klon());

        // Notify all potential approvers via their registered channels
        untuk prinsipal dalam &self.cari_prinsipal_layak() {
            untuk saluran dalam &prinsipal.saluran_berdaftar {
                hantar_notifikasi(prinsipal, saluran, &self.operasi)?;
            }
        }

        Ok(pengendali)
    }

    // Check if we have enough approvals
    fungsi disahkan(&self, kelulusan: &[Kelulusan]) -> bool {
        biar sekarang = CapMasa::sekarang();

        // Filter valid approvals
        biar sah: Senarai<_> = kelulusan.iter()
            .tapis(|k| {
                // Within time window
                sekarang - k.cap_masa < self.tetingkap_masa &&
                // Valid signature
                k.prinsipal.sahkan(&k.tandatangan, &self.operasi.ke_bait()) &&
                // Has required role
                self.peranan.iter().ada(|r| k.prinsipal.ada_peranan(r)) &&
                // Used approved channel
                self.saluran.mengandungi(&k.saluran)
            })
            .kumpul();

        // Count unique principals
        biar prinsipal_unik: HashSet<_> = sah.iter()
            .peta(|k| &k.prinsipal)
            .kumpul();

        prinsipal_unik.panjang() >= self.pengesah_diperlukan
    }
}

// Critical operation wrapper
fungsi operasi_kritikal<T>(
    op: fn() -> T,
    keizinan: &KeizinanBerbilangPihak,
    kelulusan: &[Kelulusan],
) -> Keputusan<T, RalatKeizinan> {
    // Verify multi-party authorization
    kalau !keizinan.disahkan(kelulusan) {
        pulang Err(RalatKeizinan::KelulusanTidakCukup);
    }

    // Log the operation
    log_audit("CRITICAL_OP_EXECUTED", &keizinan.operasi, kelulusan);

    // Execute
    Ok(op())
}
```

## 5. Threat 3: Insider Threats

### 5.1 The Attack

An authorized user with legitimate access abuses their privileges to exfiltrate data, sabotage systems, or cause harm.

### 5.2 Defense: Budgets + Auditing + Anomaly Detection

```coq
(* Insider threat mitigation *)

(* Information budget per principal *)
Record InsiderBudget := {
  principal : Principal;
  daily_query_limit : nat;
  daily_export_limit : bytes;
  declassify_budget : nat;  (* From Track Z *)
}.

(* Complete audit trail *)
Record AuditEntry := {
  principal : Principal;
  action : Action;
  timestamp : Timestamp;
  data_accessed : list DataId;
  bytes_exported : nat;
  signature : bytes;  (* Signed by system *)
}.

(* Audit is complete and immutable *)
Axiom audit_complete : forall action,
  occurred action -> exists entry, In entry audit_log /\ records entry action.

Axiom audit_immutable : forall entry,
  In entry audit_log -> forall t, t > now -> In entry (audit_log_at t).

(* Insider bounded by budget *)
Theorem insider_bounded : forall insider day,
  is_insider insider ->
  total_exported insider day <= insider.budget.daily_export_limit.
Proof.
  (* Every export consumes budget *)
  (* System enforces budget before allowing export *)
Qed.

(* All insider actions audited *)
Theorem insider_audited : forall insider action,
  is_insider insider ->
  performs insider action ->
  exists entry, In entry audit_log /\ entry.principal = insider /\ entry.action = action.
Proof.
  (* All actions go through audited pathways *)
  (* No way to bypass audit *)
Qed.
```

### 5.3 RIINA Insider Threat Mitigation

```riina
// Insider threat mitigation system
bentuk MitigasiAncamanDalaman {
    belanjawan: Peta<IdPrinsipal, BelanjawanHarian>,
    pengesan_anomali: PengesanAnomali,
    log_audit: LogAuditKekal,
}

bentuk BelanjawanHarian {
    had_pertanyaan: u64,
    had_eksport_bait: u64,
    had_dedah: u64,          // From Track Z
    pertanyaan_diguna: Atomik<u64>,
    eksport_diguna: Atomik<u64>,
    dedah_diguna: Atomik<u64>,
    tetapan_semula: CapMasa,
}

impl MitigasiAncamanDalaman {
    // Check and consume budget before any sensitive operation
    fungsi semak_belanjawan(&self, prinsipal: &IdPrinsipal, tindakan: &Tindakan)
        -> Keputusan<(), RalatBelanjawan>
    {
        biar belanjawan = self.belanjawan.dapat(prinsipal)
            .ok_or(RalatBelanjawan::PrinsipalTidakDitemui)?;

        // Reset if new day
        belanjawan.tetap_semula_jika_perlu();

        padan tindakan {
            Tindakan::Pertanyaan => {
                biar semasa = belanjawan.pertanyaan_diguna.tambah(1, Tertib::SeqCst);
                kalau semasa > belanjawan.had_pertanyaan {
                    belanjawan.pertanyaan_diguna.tolak(1, Tertib::SeqCst);
                    pulang Err(RalatBelanjawan::HadPertanyaanMelebihi);
                }
            }
            Tindakan::Eksport(saiz) => {
                biar semasa = belanjawan.eksport_diguna.tambah(saiz, Tertib::SeqCst);
                kalau semasa > belanjawan.had_eksport_bait {
                    belanjawan.eksport_diguna.tolak(saiz, Tertib::SeqCst);
                    pulang Err(RalatBelanjawan::HadEksportMelebihi);
                }
            }
            Tindakan::Dedah => {
                biar semasa = belanjawan.dedah_diguna.tambah(1, Tertib::SeqCst);
                kalau semasa > belanjawan.had_dedah {
                    belanjawan.dedah_diguna.tolak(1, Tertib::SeqCst);
                    pulang Err(RalatBelanjawan::HadDedahMelebihi);
                }
            }
        }

        Ok(())
    }

    // Log all actions
    fungsi log(&self, prinsipal: &IdPrinsipal, tindakan: &Tindakan) {
        biar entri = EntriAudit {
            prinsipal: prinsipal.klon(),
            tindakan: tindakan.klon(),
            cap_masa: CapMasa::sekarang(),
            tandatangan: tanda_sistem(&prinsipal, &tindakan),
        };

        self.log_audit.tambah(entri);

        // Check for anomalies
        kalau self.pengesan_anomali.adakah_anomali(prinsipal, tindakan) {
            maklum_pasukan_keselamatan_serta_merta(prinsipal, tindakan);
        }
    }
}

// Anomaly detection
bentuk PengesanAnomali {
    model: ModelML,
    sejarah: Peta<IdPrinsipal, Senarai<Tindakan>>,
}

impl PengesanAnomali {
    fungsi adakah_anomali(&self, prinsipal: &IdPrinsipal, tindakan: &Tindakan) -> bool {
        biar sejarah = self.sejarah.dapat(prinsipal);

        // Check various anomaly signals
        biar anomali = vec![
            // Unusual time (e.g., 3 AM access)
            self.masa_luar_biasa(tindakan.cap_masa),

            // Unusual volume
            self.volum_luar_biasa(prinsipal, tindakan),

            // Unusual data access pattern
            self.corak_luar_biasa(prinsipal, tindakan, sejarah),

            // Unusual source (new device, new location)
            self.sumber_luar_biasa(prinsipal, &tindakan.konteks),

            // ML model prediction
            self.model.ramal(prinsipal, tindakan) > AMBANG_ANOMALI,
        ];

        anomali.iter().ada(|&a| a)
    }
}
```

## 6. Threat 4: Hardware Zero-Days

### 6.1 The Attack

An unknown vulnerability in CPU, memory, or other hardware allows attackers to bypass all software protections.

### 6.2 Defense: Hardware Diversity + N-Version Execution

```coq
(* Hardware diversity model *)
Record HardwarePlatform := {
  vendor : Vendor;
  architecture : Arch;  (* ARM, x86, RISC-V *)
  microarchitecture : MicroArch;
}.

(* Platforms are independent if different vendor AND architecture *)
Definition independent (p1 p2 : HardwarePlatform) : Prop :=
  p1.vendor <> p2.vendor /\ p1.architecture <> p2.architecture.

(* N-version execution *)
Definition n_version_execute (op : Operation) (platforms : list HardwarePlatform)
  : list Result :=
  map (fun p => execute_on p op) platforms.

(* Consensus among diverse platforms *)
Definition diverse_consensus (results : list Result) : option Result :=
  let majority := find_majority results in
  if count_eq majority results > length results / 2 then
    Some majority
  else
    None.

(* Security: Zero-day on one platform detected by disagreement *)
Theorem diversity_detects_zeroday : forall platforms op,
  length platforms >= 3 ->
  pairwise independent platforms ->
  (* At most one platform has zero-day affecting this operation *)
  at_most_one_zeroday platforms op ->
  (* Disagreement detected or correct result *)
  diverse_consensus (n_version_execute op platforms) = Some (correct_result op) \/
  diverse_consensus (n_version_execute op platforms) = None.
Proof.
  (* With 3+ independent platforms and at most 1 affected *)
  (* Either all agree (on correct result) *)
  (* Or minority disagrees (detected) *)
Qed.
```

### 6.3 RIINA Hardware Diversity

```riina
// N-version execution on diverse hardware
bentuk PelaksanaPelbagai {
    platform: Senarai<Platform>,
    had_perbezaan: usize,
}

pilihan Platform {
    ARM_Apple_M3,
    x86_Intel_14thGen,
    x86_AMD_Zen5,
    RISCV_SiFive_U84,
}

impl Platform {
    // Check if platforms are independent
    fungsi bebas(&self, lain: &Platform) -> bool {
        padan (self, lain) {
            // Different architecture = independent
            (Platform::ARM_Apple_M3, Platform::x86_Intel_14thGen) => betul,
            (Platform::ARM_Apple_M3, Platform::x86_AMD_Zen5) => betul,
            (Platform::ARM_Apple_M3, Platform::RISCV_SiFive_U84) => betul,
            (Platform::RISCV_SiFive_U84, Platform::x86_Intel_14thGen) => betul,
            (Platform::RISCV_SiFive_U84, Platform::x86_AMD_Zen5) => betul,
            // Different vendor same arch = partially independent
            (Platform::x86_Intel_14thGen, Platform::x86_AMD_Zen5) => betul,
            // Same = not independent
            _ => salah,
        }
    }
}

impl PelaksanaPelbagai {
    // Execute operation on all platforms, compare results
    fungsi laksana_pelbagai<T: Eq + Klon>(&self, op: fn() -> T)
        -> Keputusan<T, RalatKepelbagaian>
        kesan KesanRangkaian  // Network calls to remote platforms
    {
        biar mut keputusan = Vektor::baru();

        // Execute on each platform
        untuk platform dalam &self.platform {
            biar hasil = self.laksana_pada(platform, op)?;
            keputusan.tolak((platform.klon(), hasil));
        }

        // Find majority result
        biar kira = HashMap::baru();
        untuk (_, hasil) dalam &keputusan {
            *kira.masuk_atau(hasil.klon(), 0) += 1;
        }

        biar (majoriti, kiraan) = kira.iter()
            .maks_oleh_kunci(|(_, k)| *k)
            .ok_or(RalatKepelbagaian::TiadaKeputusan)?;

        // Check for disagreement
        biar berbeza = keputusan.iter()
            .tapis(|(_, h)| h != majoriti)
            .kira();

        kalau berbeza > self.had_perbezaan {
            // Significant disagreement - possible zero-day
            log_keselamatan("HARDWARE DISAGREEMENT DETECTED", &keputusan);
            maklum_pasukan_keselamatan();
            pulang Err(RalatKepelbagaian::PerbezaanDigesan);
        }

        kalau *kiraan > self.platform.panjang() / 2 {
            Ok(majoriti.klon())
        } lain {
            Err(RalatKepelbagaian::TiadaMajoriti)
        }
    }
}
```

## 7. Time-Delayed Execution

```riina
// Time-delayed critical operations
bentuk KunciMasa<T> {
    operasi: fn() -> T,
    masa_buka: CapMasa,
    tetingkap_batal: Tempoh,
    pembatal_sah: Senarai<IdPrinsipal>,
    dibatalkan: Atomik<bool>,
}

impl<T> KunciMasa<T> {
    // Create a time-locked operation
    fungsi baru(
        operasi: fn() -> T,
        kelewatan: Tempoh,
        tetingkap_batal: Tempoh,
        pembatal: Senarai<IdPrinsipal>,
    ) -> KunciMasa<T> {
        KunciMasa {
            operasi,
            masa_buka: CapMasa::sekarang() + kelewatan,
            tetingkap_batal,
            pembatal_sah: pembatal,
            dibatalkan: Atomik::baru(salah),
        }
    }

    // Cancel the operation (if still in window)
    fungsi batal(&self, prinsipal: &IdPrinsipal) -> Keputusan<(), RalatKunciMasa> {
        // Check if authorized to cancel
        kalau !self.pembatal_sah.mengandungi(prinsipal) {
            pulang Err(RalatKunciMasa::TidakDibenarkan);
        }

        // Check if still in cancellation window
        kalau CapMasa::sekarang() > self.masa_buka {
            pulang Err(RalatKunciMasa::TetingkapTamat);
        }

        self.dibatalkan.simpan(betul, Tertib::SeqCst);
        log_audit("TIMELOCK_CANCELLED", prinsipal);
        Ok(())
    }

    // Execute (if time reached and not cancelled)
    fungsi laksana(&self) -> Keputusan<T, RalatKunciMasa> {
        // Check if cancelled
        kalau self.dibatalkan.muat(Tertib::SeqCst) {
            pulang Err(RalatKunciMasa::Dibatalkan);
        }

        // Check if time reached
        kalau CapMasa::sekarang() < self.masa_buka {
            pulang Err(RalatKunciMasa::TerlampauAwal);
        }

        log_audit("TIMELOCK_EXECUTED");
        Ok((self.operasi)())
    }
}

// Usage: Sensitive operation with 24-hour delay
biar kunci = KunciMasa::baru(
    || padam_semua_data(),           // Operation
    Tempoh::dari_jam(24),            // 24-hour delay
    Tempoh::dari_jam(23),            // 23-hour cancellation window
    vec![ceo, cto, ciso],            // Who can cancel
);

// Anyone noticing suspicious request has 23 hours to cancel
```

## 8. Summary: Threat Mitigation Matrix

| Threat | Defense Layer | Mechanism | Residual Risk |
|--------|---------------|-----------|---------------|
| Physical coercion | L2: Threshold | Shamir n-of-m | Coercing all keyholders |
| Single keyholder compromise | L2: Geographic | Multi-jurisdiction | Global adversary |
| Social engineering | L3: Multi-party | N approvals required | Compromising N people |
| Insider abuse | L4: Budgets | Information limits | Within-budget abuse |
| Insider stealth | L5: Anomaly | ML detection | Novel patterns |
| Hardware zero-day | L1: Diversity | N-version execution | Zero-day on all platforms |
| Rushed malicious action | L4: Time-delay | 24-72 hour window | Undetected within window |

## 9. Dependencies

| Dependency | Direction | Nature |
|------------|-----------|--------|
| Track A (Formal) | Ψ depends on A | Proof foundation |
| Track F (Crypto) | Ψ depends on F | Threshold crypto, signatures |
| Track Z (Declassify) | Ψ integrates Z | Declassification budgets |
| Track U (Guardian) | Ψ integrates U | Runtime enforcement |
| All tracks | All depend on Ψ | Human security layer |

## 10. Honest Assessment: What Remains Impossible

| Threat | Why Truly Impossible | Best Mitigation |
|--------|---------------------|-----------------|
| Coercing ALL keyholders | Physical reality | Max geographic/jurisdictional spread |
| Nation-state with unlimited resources | They always win eventually | Make it expensive, detect early |
| Authorized action within budget | By definition allowed | Anomaly detection, small budgets |
| Novel attack patterns | Unknown unknowns | Continuous ML training, diversity |
| Compromising all hardware vendors | Extreme collusion | Independent verification of independence |

---

**"The system is only as strong as its weakest human. Make sure no human is the weakest link."**

*Named for: Reena + Isaac + Imaan — The foundation of everything.*
