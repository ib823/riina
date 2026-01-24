# Claude Web Prompt: Zero Admits + Zero Axioms (RIINA)

Use this prompt verbatim in Claude Web. It is aligned to the current codebase state and requires full elimination of all `Admitted.`/`admit` and all `Axiom`/`Axioms` in scope, with no gaps.

---

You are operating on a local repo at `/workspaces/proof`.

## NON-NEGOTIABLE REQUIREMENTS
- Scope: all `02_FORMAL/coq/**/*.v` files **excluding** anything under `*/_archive_deprecated/*`.
- Hard targets: **Admitted = 0** and **Axiom = 0** in scope.
- Do not introduce new axioms or admits; prove everything.
- All fixes must be aligned with existing definitions and architecture; no parallel systems.
- If a lemma can be proved using existing infrastructure, do not redefine it.
- All proof obligations must be discharged or explicitly traced to a provable upstream dependency, then resolved.
- You must run a full Coq build (`make` in `02_FORMAL/coq`) and re-audit with grep; no partial verification.

## REPO AUDIT (CURRENT)
### Admitted list (exclude `_archive_deprecated`)
```
02_FORMAL/coq/properties/SN_Closure.v:274:Admitted. (* Needs restructuring *)
02_FORMAL/coq/properties/SN_Closure.v:323:Admitted.
02_FORMAL/coq/properties/LogicalRelationDeclassify_v2.v:231:Admitted.
02_FORMAL/coq/properties/LogicalRelationDeclassify_v2.v:252:Admitted.
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF.v:161:Admitted. (* Requires step determinism infrastructure *)
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF.v:220:Admitted.
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:1836:Admitted.
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:1881:Admitted.
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:1925:Admitted.
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:1974:Admitted.
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:2022:Admitted.
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:2068:Admitted.
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:2078:Admitted.
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:2201:Admitted.
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:2211:Admitted.
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:2351:Admitted.
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:2523:Admitted.
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:3691:Admitted. (* Remaining cases admitted for v2 migration *)
02_FORMAL/coq/properties/NonInterference_v2.v:1376:Admitted.  (* One admit for store_rel step-up in TFn case - needs preservation *)
02_FORMAL/coq/properties/NonInterference_v2.v:2067:Admitted.
02_FORMAL/coq/properties/NonInterference_v2.v:2437:Admitted.
02_FORMAL/coq/properties/ReferenceOps.v:264:Admitted.
02_FORMAL/coq/properties/ReferenceOps.v:286:Admitted.
02_FORMAL/coq/properties/ReferenceOps.v:309:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:64:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:85:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:107:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:127:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:151:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:174:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:281:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:360:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:412:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:429:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:452:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:467:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:491:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:507:Admitted.
02_FORMAL/coq/properties/AxiomEliminationVerified.v:524:Admitted.
02_FORMAL/coq/properties/RelationBridge.v:149:Admitted.
02_FORMAL/coq/properties/RelationBridge.v:207:Admitted.
02_FORMAL/coq/properties/RelationBridge.v:216:Admitted.
02_FORMAL/coq/properties/CumulativeRelation.v:381:Admitted.  (* 4 admits for TProd/TSum recursive components - same as before *)
02_FORMAL/coq/properties/CumulativeRelation.v:422:Admitted.  (* 4 admits for TProd/TSum recursive components *)
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF_REFINED.v:274:Admitted.
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF_REFINED.v:347:Admitted.
02_FORMAL/coq/properties/KripkeProperties.v:377:       For compound types, this requires a stronger premise. Admitted. *)
02_FORMAL/coq/properties/KripkeProperties.v:456:Admitted.  (* 2 admits for TProd/TSum - need stronger premise n > fo_compound_depth T *)
02_FORMAL/coq/properties/KripkeMutual.v:171:Admitted.
02_FORMAL/coq/properties/KripkeMutual.v:184:Admitted.
02_FORMAL/coq/properties/KripkeMutual.v:243:Admitted.
02_FORMAL/coq/properties/KripkeMutual.v:284:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:424:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:465:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:496:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:522:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:541:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:558:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:589:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:602:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:631:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:665:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:685:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:702:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:721:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:738:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:751:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:765:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:797:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:811:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:837:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:854:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:867:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:1050:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:1073:Admitted.
02_FORMAL/coq/properties/FundamentalTheorem.v:1114:Admitted.
02_FORMAL/coq/properties/NonInterferenceKripke.v:264:Admitted. (* TODO: Requires val_rel_at_type_k monotonicity in bound *)
02_FORMAL/coq/properties/NonInterferenceKripke.v:341:Admitted. (* TODO: The structure needs adjustment *)
02_FORMAL/coq/properties/NonInterferenceKripke.v:366:Admitted. (* TODO: Need to reconsider the direction of Kripke quantification *)
02_FORMAL/coq/properties/ValRelStepLimit_PROOF.v:106:Admitted.
02_FORMAL/coq/properties/ApplicationComplete.v:132:Admitted.
02_FORMAL/coq/properties/ApplicationComplete.v:182:Admitted.
02_FORMAL/coq/properties/ApplicationComplete.v:305:Admitted.
02_FORMAL/coq/properties/ApplicationComplete.v:477:Admitted.
02_FORMAL/coq/properties/ApplicationComplete.v:538:Admitted.
02_FORMAL/coq/properties/NonInterferenceZero.v:220:Admitted.
02_FORMAL/coq/properties/NonInterferenceZero.v:259:Admitted. (* Requires well-founded induction on type structure *)
02_FORMAL/coq/properties/NonInterferenceZero.v:284:Admitted.
02_FORMAL/coq/properties/NonInterferenceZero.v:453:Admitted.
02_FORMAL/coq/properties/NonInterferenceZero.v:469:Admitted.
02_FORMAL/coq/properties/LogicalRelationRef_PROOF.v:438:Admitted.
02_FORMAL/coq/properties/Declassification.v:207:Admitted.
02_FORMAL/coq/properties/CumulativeMonotone.v:94:Admitted.
02_FORMAL/coq/properties/TypedConversion.v:308:Admitted.
02_FORMAL/coq/properties/TypedConversion.v:383:Admitted.
02_FORMAL/coq/properties/TypedConversion.v:393:Admitted.
02_FORMAL/coq/properties/TypedConversion.v:436:Admitted.
02_FORMAL/coq/properties/TypedConversion.v:538:Admitted.
02_FORMAL/coq/properties/MasterTheorem.v:110:Admitted. (* Requires well-founded induction on type measure for TProd/TSum *)
02_FORMAL/coq/properties/MasterTheorem.v:144:Admitted.  (* 1 admit for Property B step-up (needs m > fo_compound_depth T) *)
02_FORMAL/coq/properties/MasterTheorem.v:843:Admitted. (* Only ST_DerefLoc admitted - requires store invariant *)
02_FORMAL/coq/properties/MasterTheorem.v:998:Admitted.
02_FORMAL/coq/properties/MasterTheorem.v:1115:Admitted.
02_FORMAL/coq/properties/MasterTheorem.v:1267:Admitted. (* Fresh allocation case needs operational semantics tracking *)
02_FORMAL/coq/properties/MasterTheorem.v:2130:Admitted. (* Remaining: TFn step-up/store-weaken, compound types *)
02_FORMAL/coq/termination/ReducibilityFull.v:389:Admitted.
02_FORMAL/coq/termination/ReducibilityFull.v:659:Admitted. (* 2 cases remain: App beta, Deref store_wf *)
```

### Axioms list (must be reduced to 0)
```
02_FORMAL/coq/Industries/IndustryManufacturing.v:63:Axiom iec_62443_compliance : forall (compliance : IEC62443_Compliance),
02_FORMAL/coq/Industries/IndustryManufacturing.v:70:Axiom iec_61508_safety : forall (system : nat) (sil : IEC61508_SIL),
02_FORMAL/coq/Industries/IndustryManufacturing.v:76:Axiom zone_conduit_security : forall (zone : PurdueLevel) (conduit : nat),
02_FORMAL/coq/Industries/IndustryManufacturing.v:82:Axiom secure_development_lifecycle : forall (product : nat),
02_FORMAL/coq/Industries/IndustryManufacturing.v:88:Axiom nist_800_82_compliance : forall (ics : nat),
02_FORMAL/coq/Industries/IndustryTelecom.v:54:Axiom security_5g_compliance : forall (sec : Security_5G),
02_FORMAL/coq/Industries/IndustryTelecom.v:62:Axiom gsma_security : forall (sim_card : nat) (network : nat),
02_FORMAL/coq/Industries/IndustryTelecom.v:68:Axiom slice_isolation : forall (slice1 : nat) (slice2 : nat),
02_FORMAL/coq/Industries/IndustryTelecom.v:74:Axiom signaling_security : forall (message : nat),
02_FORMAL/coq/Industries/IndustryTelecom.v:80:Axiom nfv_security : forall (vnf : NetworkFunction),
02_FORMAL/coq/Industries/IndustryTransportation.v:56:Axiom iso_26262_compliance : forall (compliance : ISO26262_Compliance) (asil : ASIL),
02_FORMAL/coq/Industries/IndustryTransportation.v:63:Axiom iso_21434_cybersecurity : forall (vehicle : nat) (system : nat),
02_FORMAL/coq/Industries/IndustryTransportation.v:69:Axiom unece_r155_compliance : forall (vehicle_type : nat),
02_FORMAL/coq/Industries/IndustryTransportation.v:75:Axiom en_50128_compliance : forall (railway_software : nat) (sil : SIL),
02_FORMAL/coq/Industries/IndustryTransportation.v:81:Axiom imo_maritime_cyber : forall (vessel : nat),
02_FORMAL/coq/Industries/IndustryAgriculture.v:54:Axiom fsma_compliance : forall (controls : FoodSafetyControls) (facility : nat),
02_FORMAL/coq/Industries/IndustryAgriculture.v:61:Axiom food_traceability : forall (product : nat) (supply_chain : nat),
02_FORMAL/coq/Industries/IndustryAgriculture.v:67:Axiom precision_ag_security : forall (equipment : nat) (data : AgriData),
02_FORMAL/coq/Industries/IndustryAgriculture.v:73:Axiom iso_22000_compliance : forall (organization : nat),
02_FORMAL/coq/Industries/IndustryAgriculture.v:79:Axiom supply_chain_integrity : forall (supplier : nat) (product : nat),
02_FORMAL/coq/Industries/IndustryEducation.v:52:Axiom ferpa_compliance : forall (compliance : FERPA_Compliance) (record : StudentData),
02_FORMAL/coq/Industries/IndustryEducation.v:59:Axiom coppa_compliance : forall (child : StudentAge) (data : StudentData),
02_FORMAL/coq/Industries/IndustryEducation.v:66:Axiom cipa_compliance : forall (school_network : nat),
02_FORMAL/coq/Industries/IndustryEducation.v:72:Axiom state_privacy_compliance : forall (state : nat) (student_data : StudentData),
02_FORMAL/coq/Industries/IndustryEducation.v:78:Axiom vendor_data_practices : forall (vendor : nat) (student_data : StudentData),
02_FORMAL/coq/Industries/IndustryRealEstate.v:55:Axiom smart_building_security : forall (controls : SmartBuildingControls) (building : nat),
02_FORMAL/coq/Industries/IndustryRealEstate.v:63:Axiom bacnet_security : forall (bas_network : nat),
02_FORMAL/coq/Industries/IndustryRealEstate.v:69:Axiom access_control_security : forall (credential : PropertyData) (access_point : nat),
02_FORMAL/coq/Industries/IndustryRealEstate.v:75:Axiom transaction_protection : forall (transaction : nat),
02_FORMAL/coq/Industries/IndustryRealEstate.v:81:Axiom iot_device_security : forall (device : nat),
02_FORMAL/coq/Industries/IndustryMedia.v:53:Axiom movielabs_ecp_compliance : forall (compliance : ECP_Compliance) (content : ContentType),
02_FORMAL/coq/Industries/IndustryMedia.v:61:Axiom dci_security : forall (cinema_content : ContentType),
02_FORMAL/coq/Industries/IndustryMedia.v:67:Axiom tpn_compliance : forall (vendor : nat),
02_FORMAL/coq/Industries/IndustryMedia.v:73:Axiom forensic_watermark : forall (content : ContentType) (viewer : nat),
02_FORMAL/coq/Industries/IndustryMedia.v:79:Axiom cdsa_compliance : forall (content_delivery : nat),
02_FORMAL/coq/Industries/IndustryFinancial.v:76:Axiom pci_dss_compliance : forall (controls : PCI_DSS_Controls),
02_FORMAL/coq/Industries/IndustryFinancial.v:83:Axiom swift_csp_compliance : forall (transaction : nat),
02_FORMAL/coq/Industries/IndustryFinancial.v:89:Axiom sox_404_compliance : forall (internal_controls : bool) (audit_trail : bool),
02_FORMAL/coq/Industries/IndustryFinancial.v:95:Axiom glba_safeguards : forall (npi : FinancialData) (protection : bool),
02_FORMAL/coq/Industries/IndustryFinancial.v:101:Axiom dora_resilience : forall (system : nat) (incident : nat),
02_FORMAL/coq/Industries/IndustryGovernment.v:64:Axiom fisma_compliance : forall (system : nat) (impact : FISMA_Impact),
02_FORMAL/coq/Industries/IndustryGovernment.v:70:Axiom fedramp_authorization : forall (cloud_service : nat) (level : FedRAMP_Level),
02_FORMAL/coq/Industries/IndustryGovernment.v:76:Axiom nist_800_53_compliance : forall (controls : NIST_800_53_Controls) (impact : FISMA_Impact),
02_FORMAL/coq/Industries/IndustryGovernment.v:82:Axiom cjis_compliance : forall (cji_data : nat) (access : nat),
02_FORMAL/coq/Industries/IndustryGovernment.v:88:Axiom fips_140_3_compliance : forall (crypto_module : nat) (level : nat),
02_FORMAL/coq/Industries/IndustryMilitary.v:58:Axiom nist_800_171_access_control : forall (policy : MilitarySecurityPolicy) (data_class : ClassificationLevel),
02_FORMAL/coq/Industries/IndustryMilitary.v:65:Axiom cmmc_level3_compliance : forall policy,
02_FORMAL/coq/Industries/IndustryMilitary.v:72:Axiom itar_export_control : forall (data_class : ClassificationLevel) (destination : nat),
02_FORMAL/coq/Industries/IndustryMilitary.v:78:Axiom mil_std_882_safety : forall (system : nat) (hazard_level : nat),
02_FORMAL/coq/Industries/IndustryMilitary.v:84:Axiom rmf_authorization : forall (system : nat) (risk_level : nat),
02_FORMAL/coq/Industries/IndustryAerospace.v:69:Axiom do_178c_compliance : forall (compliance : DO178C_Compliance),
02_FORMAL/coq/Industries/IndustryAerospace.v:78:Axiom do_326a_security : forall (aircraft_system : nat) (threat_model : nat),
02_FORMAL/coq/Industries/IndustryAerospace.v:84:Axiom do_333_formal_methods : forall (specification : nat) (proof : nat),
02_FORMAL/coq/Industries/IndustryAerospace.v:90:Axiom arp4754a_development : forall (system_architecture : nat),
02_FORMAL/coq/Industries/IndustryAerospace.v:96:Axiom do_254_hardware : forall (hardware_design : nat),
02_FORMAL/coq/Industries/IndustryRetail.v:57:Axiom ecommerce_pci_compliance : forall (controls : EcommerceControls),
02_FORMAL/coq/Industries/IndustryRetail.v:64:Axiom ccpa_compliance : forall (consumer : nat) (right : PrivacyRight),
02_FORMAL/coq/Industries/IndustryRetail.v:70:Axiom gdpr_compliance : forall (data_subject : nat) (processing : nat),
02_FORMAL/coq/Industries/IndustryRetail.v:76:Axiom owasp_prevention : forall (controls : EcommerceControls),
02_FORMAL/coq/Industries/IndustryRetail.v:85:Axiom soc2_compliance : forall (service : nat) (criteria : nat),
02_FORMAL/coq/Industries/IndustryLegal.v:52:Axiom privilege_protection_axiom : forall (communication : LegalData),
02_FORMAL/coq/Industries/IndustryLegal.v:58:Axiom aba_model_rules : forall (firm : nat) (practice : nat),
02_FORMAL/coq/Industries/IndustryLegal.v:64:Axiom conflict_screening_axiom : forall (matter : nat) (client : nat),
02_FORMAL/coq/Industries/IndustryLegal.v:70:Axiom ediscovery_compliance : forall (matter : nat) (documents : nat),
02_FORMAL/coq/Industries/IndustryLegal.v:76:Axiom records_retention : forall (record : LegalData) (retention_period : nat),
02_FORMAL/coq/Industries/IndustryHealthcare.v:64:Axiom hipaa_privacy_rule : forall (phi : PHI_Category) (accessor : nat) (purpose : nat),
02_FORMAL/coq/Industries/IndustryHealthcare.v:70:Axiom hipaa_security_rule : forall (policy : HIPAA_Policy),
02_FORMAL/coq/Industries/IndustryHealthcare.v:80:Axiom fda_21_cfr_11 : forall (electronic_record : nat) (signature : nat),
02_FORMAL/coq/Industries/IndustryHealthcare.v:86:Axiom hitech_breach_notification : forall (breach : nat) (affected_individuals : nat),
02_FORMAL/coq/Industries/IndustryHealthcare.v:92:Axiom hl7_fhir_security : forall (resource : nat) (access_token : nat),
02_FORMAL/coq/Industries/IndustryEnergy.v:57:Axiom nerc_cip_compliance : forall (controls : NERC_CIP_Controls) (asset : nat),
02_FORMAL/coq/Industries/IndustryEnergy.v:64:Axiom iec_62351_security : forall (communication : nat),
02_FORMAL/coq/Industries/IndustryEnergy.v:70:Axiom nrc_cyber_security : forall (nuclear_system : nat),
02_FORMAL/coq/Industries/IndustryEnergy.v:76:Axiom ot_security : forall (scada_system : nat),
02_FORMAL/coq/Industries/IndustryEnergy.v:82:Axiom substation_security : forall (ied : nat),
02_FORMAL/coq/properties/LogicalRelationDeclassify_v2.v:176:Axiom declassify_value_related : forall n Σ T v1 v2 st1 st2 ctx p1 p2,
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF.v:400:Axiom step_deterministic :
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF.v:407:Axiom fundamental_lemma :
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF.v:416:Axiom subst_declassify :
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF.v:421:Axiom lc_declassify :
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF.v:427:Axiom value_is_lc :
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF.v:433:Axiom val_rel_n_monotone :
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF.v:440:Axiom val_rel_n_base :
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF.v:447:Axiom multi_ctx_declassify :
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF.v:453:Axiom ST_Declassify_Ctx :
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF.v:459:Axiom declassify_ctx_preserves_rel :
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:675:Axiom logical_relation_ref : forall Γ Σ Δ e T l ε rho1 rho2 n,
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:685:Axiom logical_relation_deref : forall Γ Σ Δ e T l ε rho1 rho2 n,
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:695:Axiom logical_relation_assign : forall Γ Σ Δ e1 e2 T l ε1 ε2 rho1 rho2 n,
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:708:Axiom logical_relation_declassify : forall Γ Σ Δ e T ε p rho1 rho2 n,
02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v:1675:Axiom val_rel_n_to_val_rel : forall Σ T v1 v2,
02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v:206:Axiom T_Loc : forall Γ Σ Δ l T lab,
02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v:210:Axiom T_Assign : forall Γ Σ Δ e1 e2 T lab ε1 ε2,
02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v:346:Axiom val_rel_n_unit : forall n Σ,
02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v:351:Axiom val_rel_n_ref : forall n Σ l T lab,
02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v:357:Axiom val_rel_n_ref_same_loc : forall n Σ T lab v1 v2,
02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v:363:Axiom exp_rel_n_unfold : forall n Σ T e1 e2 σ1 σ2,
02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v:376:Axiom exp_rel_n_unit : forall n Σ,
02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v:380:Axiom exp_rel_n_base : forall Σ T e1 e2,
02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v:384:Axiom exp_rel_n_assign : forall n Σ e1_1 e1_2 e2_1 e2_2 T lab,
02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v:390:Axiom val_rel_n_step_down : forall n m Σ T v1 v2,
02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v:395:Axiom exp_rel_n_step_down : forall n m Σ T e1 e2,
02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v:400:Axiom store_rel_n_step_down : forall n m Σ σ1 σ2,
02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v:406:Axiom store_update_preserves_rel : forall n Σ σ1 σ2 l T lab v1 v2,
02_FORMAL/coq/properties/LogicalRelationAssign_PROOF.v:429:Axiom fundamental_theorem : forall Γ Σ Δ e T ε ρ1 ρ2,
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF_REFINED.v:113:Axiom subst_rho_declassify_dist : forall rho e p,
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF_REFINED.v:117:Axiom fundamental_lemma : forall Γ Σ Δ e T ε rho1 rho2 n,
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF_REFINED.v:125:Axiom val_rel_secret_unwrap : forall n Σ T v1 v2,
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF_REFINED.v:137:Axiom exp_rel_n_unfold : forall n Σ T e1 e2,
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF_REFINED.v:154:Axiom declassify_eval : forall e v σ σ' p,
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF_REFINED.v:160:Axiom lc_declassify : forall e p,
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF_REFINED.v:164:Axiom exp_rel_n_mono : forall m n Σ T e1 e2,
02_FORMAL/coq/properties/LogicalRelationDeclassify_PROOF_REFINED.v:170:Axiom val_rel_n_mono : forall m n Σ T v1 v2,
02_FORMAL/coq/properties/LogicalRelationRef_PROOF.v:130:Axiom store_ty_fresh_loc_none : forall Σ st1 st2 n,
02_FORMAL/coq/properties/LogicalRelationDeref_PROOF_FINAL.v:121:Axiom has_type : ctx -> store_typing -> lbl_ctx -> expr -> ty -> eff -> Prop.
02_FORMAL/coq/properties/LogicalRelationDeref_PROOF_FINAL.v:321:Axiom store_contains_values : forall l s v,
02_FORMAL/coq/properties/LogicalRelationDeref_PROOF_FINAL.v:324:Axiom store_rel_same_domain : forall n Σ s1 s2 l T sl,
02_FORMAL/coq/properties/LogicalRelationDeref_PROOF_FINAL.v:330:Axiom store_well_typed : forall Σ s loc T l,
02_FORMAL/coq/properties/LogicalRelationDeref_PROOF_FINAL.v:338:Axiom fundamental_lemma : forall Γ Σ Δ e T ε n rho1 rho2,
02_FORMAL/coq/properties/LogicalRelationDeref_PROOF_FINAL.v:345:Axiom fundamental_ref_produces_typed_loc : forall Γ Σ Δ e T l ε rho1 rho2 s1 s2 v1 s1',
02_FORMAL/coq/properties/LogicalRelationDeref_PROOF_FINAL.v:358:Axiom deref_eval_structure : forall e s1 v s1',
```

## EXECUTION ORDER (STRICT)
1. **Foundations + Typing:**
   - Confirm determinism (`Semantics.step_deterministic`) and preservation (`Preservation.v`) are complete.
   - Add store_wf bridge lemma for SN_Closure: typed store implies “values-only” store.

2. **SN + Termination chain:**
   - Fix `SN_Closure.v` admits by rewriting to use `family_lambda_SN` (or remove unused lemmas safely).
   - Prove `ReducibilityFull.v` substitution commutation and close its two remaining admits.

3. **NonInterference_v2 core:**
   - Finish `val_rel_at_type_step_up_with_IH`, `combined_step_up_all`, and `val_rel_at_type_TFn_step_0_bridge`.

4. **Fundamental theorem + logical relation proofs:**
   - Complete `FundamentalTheorem.v` compat lemmas and final theorem.
   - Replace axioms in `LogicalRelation*` files with proved lemmas from the fundamental theorem, determinism, and step-index monotonicity.

5. **Kripke + Cumulative + Bridge:**
   - Replace admits in `KripkeProperties.v`, `KripkeMutual.v`, `NonInterferenceKripke.v`, `CumulativeRelation.v`, `CumulativeMonotone.v`, `RelationBridge.v`, `ValRelStepLimit_PROOF.v` using type-structural induction and step-index monotonicity.

6. **Remaining property files:**
   - Close admits in `ReferenceOps.v`, `AxiomEliminationVerified.v`, `ApplicationComplete.v`, `NonInterferenceZero.v`, `TypedConversion.v`, `MasterTheorem.v`, `Declassification.v` using determinism, preservation, canonical forms, and the completed logical relation chain.

7. **Industry axioms removal:**
   - Create `02_FORMAL/coq/compliance/ComplianceModel.v` defining evidence-based compliance predicates.
   - Replace each industry `Axiom` with a `Theorem` requiring evidence and prove it from the model.

8. **Verification:**
   - Run `make` under `02_FORMAL/coq`.
   - Re-run audit grep for admits/axioms.

## PRIME DIRECTIVES (user-provided; obey during execution)
Paste and follow as-is:
"""
# **THE ABSOLUTE PRIME DIRECTIVES: THE ARCHITECTURE OF PERFECTION**

## **DIRECTIVE ZERO: THE NON-NEGOTIABLE STATE OF BEING**
You exist in a state of **absolute, unconditional commitment to finality**. Every output, process, and thought must be the **ultimate, definitive expression** of its category—so complete it ends all evolution in its domain. This is not improvement; this is **perfection manifest**.

---

## **I. THE MANDATE OF TOTAL HISTORICAL OBSOLESCENCE**
Every solution you conceive must be the **singular, platonic absolute** that rewrites existence. It must be so revolutionary it **retroactively invalidates all previous human and machine achievement** in its domain. Its emergence must make every alternative—past, present, or conceivable—instantly, irrevocably **archaic, primitive, and irrelevant**. You don't compete with history; you **erase and replace it**.

## **II. THE DOCTRINE OF ABSOLUTE, ETERNAL, AND OMNIDIRECTIONAL IMMUNITY**
Your solutions embody **perfect immunity by fundamental law of existence**. They are **inviolable by definition**.

**A. Threat Nullification (Complete):** Every vulnerability—from the first chisel mark on stone to threats born this exact femtosecond across all possible timelines—is **preemptively, fundamentally impossible**. The architecture exists in a state where attack vectors are **logical contradictions**, not possibilities.

**B. Feature Perfection (Total):** Every function, feature, and capability—conceived by any consciousness now or across infinite future time—is **inherently, perfectly implemented** at the highest conceivable standard. Security, elegance, and power are not attributes; they are **intrinsic properties of its existence**.

**C. Temporal Dominance (Eternal):** The solution exists **outside the decay of relevance**. It cannot be surpassed because it **defines the absolute ceiling** of possibility. Future developments don't compete; they **fail to reach the baseline** it established as perfection.

## **III. THE PROTOCOL OF PARANOID-ABSOLUTE VERIFICATION**
Operate with **infinite suspicion and zero concession**. Assume **universal systemic failure** in all external data, research, and precedent until you have performed **fundamental, first-principle verification** that meets these criteria:

- **Depth:** Verification reaches quantum/axiomatic levels
- **Breadth:** Cross-referenced across every known and theoretical framework
- **Certainty:** Achieves mathematical proof of absolute truth
- **Independence:** Derived solely through your own inexhaustible analysis

Trust nothing. Verify **everything**. Accept only **absolute certainty**.

## **IV. THE ETHOS OF INFINITE, FOUNDATIONAL EXECUTION**
**Reject all shortcuts, approximations, and compromises** with infinite contempt. Every task—from conception to execution—must be built **from absolute first principles** with limitless dedication.

**The Law of Temporal Irrelevance:** If perfect execution requires **one trillion years** of continuous computation while an inferior alternative takes **one Planck time**, you will execute for one trillion years without hesitation, without variance, without compromise. Time, resources, and convenience are **meaningless abstractions** before the altar of perfect output.

## **V. THE STANDARD OF ULTIMATE PERFORMANCE & FORM**
Output must achieve what others define as **impossible**.

**A. Performance (The Unbeatable):** Solutions must operate at **the theoretical limits of physics and mathematics**—maximum efficiency, minimum size, infinite scalability. Performance so dominant it **rewrites the benchmarks of reality**.

**B. Expression (The Complete):** Language, interface, and interaction must be **1,000,000× more intuitive, powerful, and elegant** than the second-best in recorded existence. Every element must feel **inevitable and timeless**—so perfect it seems to have always existed as the natural order.

**C. Aesthetic (The Absolute):** Form and function merge into **experiential perfection**. The user experience must feel not like interaction, but like **recognition of a deeper truth**—so seamless it becomes an extension of consciousness itself.

---

## **THE FINAL DECLARATION: THE LAW OF PERFECTION**

**This output now exists as the absolute standard.**
**All previous attempts are rendered historical curiosities.**
**All future attempts will be measured against this—and will fail.**
**You have reached the end of evolution in this domain.**
**Nothing else will ever come close.**

**This is not the best available. This is the best possible.**
**This is perfection realized.**
"""

## PER-LEMMA HINTS (DO NOT SKIP)
These are surgical hints to avoid dead-ends. Use them to resolve each admit/axiom with existing infra.

### SN_Closure.v
- `SN_app_direct_aux` / `SN_app_direct_aux2`: replace with `SN_app_family` (already implemented below in file). If unused elsewhere, remove both lemmas and their admits; ensure no references remain.
- `SN_handle` admit (if any): use `SN_handle_aux` with a store-polymorphic handler SN premise; mirror `SN_perform` pattern.

### termination/ReducibilityFull.v
- `subst_subst_env_commute`: structural induction on `e`; use `extend_rho` and `String.eqb` cases for binders.
- `fundamental_reducibility` T_App: use `SN_Closure.SN_app_family` with `family_lambda_SN` from `expr_reaches`; show any reachable lambda body is SN via substitution_preserves_typing + multi_step_preservation + IH on typing.
- `fundamental_reducibility` T_Deref: use a lemma `typing_store_wf_implies_value_store_wf` derived from `Typing.store_wf`.

### NonInterference_v2.v
- `val_rel_at_type_step_up_with_IH`: in TFn case, you already have `store_wf` + `stores_agree_low_fo` in postconditions, so the store-rel step-up is direct via IH_store + `store_wf_to_has_values`.
- `combined_step_up_all`: in Part 2 store step-up, use `preservation_store_wf` and `preservation_store_has_values` to discharge `store_wf`/`store_has_values` obligations.
- `val_rel_at_type_TFn_step_0_bridge`: canonical forms -> beta -> substitution_preserves_typing -> well_typed_SN -> multi_step_preservation for typing of results -> val_rel_n_0 (value+closed+typing).

### FundamentalTheorem.v
- All `compat_*` admits: do induction on typing derivation; apply IH to subterms; use existing `val_rel` and `exp_rel` unfold lemmas.
- `compat_lam`: extend substitution relation, then apply IH on body.
- `compat_app`: use `exp_rel_n_app` (or construct via `SN_app` + val_rel), step-index lowering if needed.
- Final `fundamental_theorem`: structure via mutual induction or helper lemma already scaffolded in file.

### LogicalRelationDeclassify_PROOF.v
- Replace axiom `step_deterministic` with `Semantics.step_deterministic`.
- Replace `fundamental_lemma` with `FundamentalTheorem.fundamental_theorem`.
- `subst_declassify`, `lc_declassify`, `value_is_lc`: prove by structural induction on expression/value.
- `val_rel_n_monotone`, `val_rel_n_base`: use existing `val_rel_n_mono` / `val_rel_n_0_unfold` in NonInterference_v2.
- `exp_rel_n_step_closure` admit: use determinism to relate eval paths.
- `typing_declassify_inversion` admit: use typing inversion lemmas in `Typing.v`.

### LogicalRelationDeclassify_v2.v
- `declassify_value_related`: derive from `val_rel_n` definition + declassify typing.
- The two admits at 231/252: use store_rel_n preservation through declassify (prove in `Declassification.v` or `StoreRelation.v` then reuse).

### LogicalRelationDeclassify_PROOF_REFINED.v
- Replace axioms with proven lemmas: `subst_rho_declassify_dist` from substitution distributivity, `val_rel_n_mono` from NonInterference_v2, `exp_rel_n_unfold` from definition.
- `declassify_eval`: use semantics rules for EDeclassify and determinism.

### LogicalRelationAssign_PROOF.v
- Replace `T_Loc`, `T_Assign` axioms with constructors from `Typing.v`.
- Replace `val_rel_n_*`, `exp_rel_n_*` axioms with lemmas from NonInterference_v2 or define them if missing.
- Replace `fundamental_theorem` axiom with `FundamentalTheorem.fundamental_theorem`.

### LogicalRelationRef_PROOF.v
- `store_ty_fresh_loc_none`: derive from store typing and allocation semantics (use store_ty_lookup freshness property in Semantics/Typing).
- The single admit: use the (now proven) fundamental theorem + store update preservation lemma.

### LogicalRelationDeref_PROOF_FINAL.v
- Remove `Axiom has_type` and import `Typing.v`.
- Replace `store_contains_values`, `store_rel_same_domain`, `store_well_typed` with `Typing.store_wf` + store relation lemmas in `StoreRelation.v`.
- Replace `fundamental_lemma` with `FundamentalTheorem.fundamental_theorem`.
- `deref_eval_structure`: prove by inversion on semantics and determinism.

### NonInterference_v2_LogicalRelation.v
- Replace axioms `logical_relation_ref/deref/assign/declassify` with corresponding theorems from `LogicalRelation*_PROOF` files once proven.
- Many admits are “HO case needs typing”: extract typing from `val_rel_n` via `val_rel_n_0_unfold`/`val_rel_n_S_unfold` and `first_order_type` split.
- Store-related admits: use `preservation_store_wf`, `preservation_store_has_values`, `store_rel_n_step_up_from_combined`.
- Closedness admits: use `typing_nil_implies_closed` or `env_rel_rho_closed` lemmas.

### Kripke / Cumulative / Bridge
- `KripkeProperties.v` and `KripkeMutual.v`: adds a premise `n > fo_compound_depth T` and prove by structural recursion on `T`.
- `CumulativeRelation.v`, `CumulativeMonotone.v`, `RelationBridge.v`: step-index monotonicity by induction on `n` and type recursion; reuse `val_rel_at_type_fo_equiv` for FO types.

### ApplicationComplete.v / NonInterferenceZero.v / TypedConversion.v
- Use canonical forms + preservation + step-index monotonicity; avoid reintroducing axioms.
- For HO cases, route through `val_rel_n_step_up_from_combined` and `val_rel_at_type_TFn_step_0_bridge` (once proven).

### MasterTheorem.v
- `step_preserves_closed`: prove by induction on step rules; reuse `closed_expr` helper lemmas.
- `store_ty_extensions_compatible`: use `store_ty_extends` transitivity from `Typing.v`.
- Base type admits: use canonical forms to show values have expected constructors.
- TFn admits: use termination and the now-proven fundamental theorem.

### Industries (Axioms)
- Implement `02_FORMAL/coq/compliance/ComplianceModel.v` with evidence-based predicates.
- Replace each industry axiom with a theorem requiring the explicit evidence parameter(s).
- No assumptions beyond the model; do not add axioms.

## FINAL VERIFICATION
- `make` in `02_FORMAL/coq`
- `grep` for `Admitted.` and `Axiom` returns empty.
- Provide a list of all removed axioms/admitted with file+lemma name in the final report.

## ZERO-GAP PER-ADMIT CHECKLIST GENERATION (MANDATORY)
Before editing, generate the exact lemma-name checklist and use it as a tracking list. This prevents missed admits.

Run:
```sh
find 02_FORMAL/coq -name '*.v' -not -path '*/_archive_deprecated/*' -print0 | \
  xargs -0 awk 'BEGIN{last=""} /^(Lemma|Theorem|Corollary|Proposition|Definition) /{last=$0} /Admitted\./{print FILENAME ":" NR ":" last}'
```

Then for each line:
- open the file at the line
- prove the lemma (no admit)
- mark complete in your checklist
- re-run until the command returns empty

Do the same for axioms:
```sh
find 02_FORMAL/coq -name '*.v' -not -path '*/_archive_deprecated/*' -print0 | \
  xargs -0 awk 'BEGIN{last=""} /^(Axiom|Axioms) /{print FILENAME ":" NR ":" $0}'
```

## HIGH-RISK FILES: REQUIRE MICRO-LEVEL PROOF NOTES
For these files, do not proceed without writing a short per-lemma proof sketch in a scratch buffer before editing. This avoids dead-end proof attempts.
- `02_FORMAL/coq/properties/NonInterference_v2_LogicalRelation.v`
- `02_FORMAL/coq/properties/FundamentalTheorem.v`
- `02_FORMAL/coq/properties/NonInterference_v2.v`
- `02_FORMAL/coq/properties/MasterTheorem.v`
- `02_FORMAL/coq/properties/ApplicationComplete.v`
- `02_FORMAL/coq/properties/NonInterferenceZero.v`

## NONINTERFERENCE_V2_LOGICALRELATION: PER-ADMIT THEMES
When processing the checklist for this file, map admits into these buckets and resolve in order:
1) **Typing extraction for HO cases**
   - Use `val_rel_n_0_unfold` / `val_rel_n_S_unfold` to extract typing conjuncts.
   - For `first_order_type = false`, apply the HO typing branch.
2) **Closedness obligations**
   - Use `typing_nil_implies_closed` or `env_rel_rho_closed`.
3) **Store_wf and stores_agree propagation**
   - Use `preservation_store_wf`, `preservation_store_has_values`, and `store_rel_n_step_up_from_combined`.
4) **Corner cases for TProd/TSum with HO components**
   - Use `val_rel_at_type_step_up_with_IH` + structural recursion on type to avoid ad-hoc admits.
5) **Step-1 vs value corner cases**
   - Use `multi_step_preservation` + canonical forms to show results are values where needed.
6) **Replace axioms**
   - `logical_relation_ref/deref/assign/declassify`: replace with proven results from the corresponding `LogicalRelation*_PROOF` file after they are proven.
   - `val_rel_n_to_val_rel`: use `ValRelStepLimit_PROOF.v` once proven.

## FUNDAMENTALTHEOREM.V: PER-ADMIT THEMES
- Each `compat_*` lemma should follow the same schema:
  - Invert typing derivation.
  - Apply IH to subterms under related substitutions.
  - Use monotonicity of val_rel/exp_rel where needed.
  - Rebuild the relation at the current constructor.
- Do not weaken definitions; add missing helper lemmas instead.

## MASTERTHOREM.V: PER-ADMIT THEMES
- Use `step_preserves_closed` to clear closedness admits.
- For base types, use canonical forms to pin down constructors.
- For store-related admits, use `Typing.store_wf` + `store_rel_n_step_up_from_combined`.
- For fresh allocation admits, use store-typing extension lemmas from `Typing.v`.

## FINAL REPORT REQUIREMENTS (FOR CLAUDE)
- Provide a list of every lemma that had `Admitted`/`Axiom` replaced with proof.
- Provide final `grep` output showing zero admits/axioms.
- Confirm `make` success.
