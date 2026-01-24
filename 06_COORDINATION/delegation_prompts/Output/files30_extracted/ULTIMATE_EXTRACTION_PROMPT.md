# ULTIMATE EXTRACTION PROMPT FOR RIINA NON-INTERFERENCE
# Copy this entire block and run with: claude --print "$(cat THIS_FILE)"

## OBJECTIVE
Extract COMPLETE information to eliminate ALL 13 remaining admits in NonInterference_v2.v.
The output must be SELF-CONTAINED for an external AI to generate exact Coq code.

---

## PART 1: STRUCTURAL ANALYSIS

### 1.1 The val_rel_at_type Definition (COMPLETE - ALL CASES)
```bash
# Extract the FULL val_rel_at_type definition
grep -n -A 150 'Fixpoint val_rel_at_type\|Section ValRelAtType' 02_FORMAL/coq/properties/NonInterference_v2.v | head -180
```

Show the EXACT lines where TFn case begins and ends. Include ALL parameters.

### 1.2 TFn Case Specifically
```bash
# Show just the TFn case with 20 lines before/after
grep -n -B 5 -A 40 '| TFn' 02_FORMAL/coq/properties/NonInterference_v2.v | head -60
```

### 1.3 val_rel_n and store_rel_n Mutual Fixpoint
```bash
grep -n -A 80 'Fixpoint val_rel_n\|with store_rel_n' 02_FORMAL/coq/properties/NonInterference_v2.v | head -100
```

---

## PART 2: THE 13 ADMIT LOCATIONS

### 2.1 List ALL admits with exact line numbers
```bash
grep -n 'admit\.' 02_FORMAL/coq/properties/NonInterference_v2.v
```

### 2.2 Admits 284, 286 - Full Context (50 lines around each)
```bash
echo "=== CONTEXT FOR LINE 284 ==="
sed -n '250,320p' 02_FORMAL/coq/properties/NonInterference_v2.v
```

What lemma is this in? What is the EXACT Goal? List ALL hypotheses.

### 2.3 Admit 1532 - Fundamental Theorem Context
```bash
echo "=== CONTEXT FOR LINE 1532 ==="
sed -n '1480,1580p' 02_FORMAL/coq/properties/NonInterference_v2.v
```

What is the Goal? What hypotheses are in scope? What case (TFn/TProd/TSum)?

### 2.4 Admits 1593-1601 - Preservation Group
```bash
echo "=== CONTEXT FOR LINES 1593-1601 ==="
sed -n '1550,1650p' 02_FORMAL/coq/properties/NonInterference_v2.v
```

### 2.5 Admits 1662, 1733, 1808, 1880 - Nested Cases
```bash
echo "=== NESTED ADMITS ==="
for line in 1662 1733 1808 1880; do
  echo "--- Line $line ---"
  sed -n "$((line-20)),$((line+10))p" 02_FORMAL/coq/properties/NonInterference_v2.v
done
```

### 2.6 Admit 1334 - Helper Lemma
```bash
echo "=== CONTEXT FOR LINE 1334 ==="
sed -n '1290,1380p' 02_FORMAL/coq/properties/NonInterference_v2.v
```

---

## PART 3: KEY DEFINITIONS

### 3.1 store_wf (EXACT current definition)
```bash
grep -n -B 2 -A 15 'Definition store_wf' 02_FORMAL/coq/properties/NonInterference_v2.v
```

### 3.2 store_has_values
```bash
grep -n -B 2 -A 8 'Definition store_has_values' 02_FORMAL/coq/properties/NonInterference_v2.v
```

### 3.3 stores_agree_low_fo
```bash
grep -n -B 2 -A 10 'Definition stores_agree_low_fo' 02_FORMAL/coq/properties/NonInterference_v2.v
```

### 3.4 first_order_type
```bash
grep -n -A 25 'Fixpoint first_order_type' 02_FORMAL/coq/properties/NonInterference_v2.v 02_FORMAL/coq/foundations/Syntax.v | head -35
```

### 3.5 val_rel_at_type_fo (for TSum case - admits 284,286)
```bash
grep -n -A 40 'val_rel_at_type_fo\|Fixpoint val_rel_at_type_fo' 02_FORMAL/coq/properties/NonInterference_v2.v | head -50
```

---

## PART 4: AVAILABLE LEMMAS

### 4.1 Canonical Forms (EXACT signatures)
```bash
grep -n -B 1 -A 10 'Lemma canonical_forms_fn\|Lemma canonical_forms_prod\|Lemma canonical_forms_sum' 02_FORMAL/coq/foundations/Typing.v
```

### 4.2 Preservation Theorem
```bash
grep -n -B 2 -A 15 'Theorem preservation\|Lemma preservation' 02_FORMAL/coq/type_system/Preservation.v | head -40
```

### 4.3 Substitution Preserves Typing
```bash
grep -n -B 2 -A 12 'Lemma substitution_preserves_typing' 02_FORMAL/coq/type_system/Preservation.v
```

### 4.4 Value Has Pure Effect
```bash
grep -n -B 2 -A 8 'Lemma value_has_pure_effect' 02_FORMAL/coq/type_system/Preservation.v
```

### 4.5 Store Type Extension Lemmas
```bash
grep -n -B 1 -A 6 'Lemma store_ty_extends' 02_FORMAL/coq/foundations/Typing.v 02_FORMAL/coq/type_system/Preservation.v | head -40
```

### 4.6 Typing Nil Implies Closed
```bash
grep -n -B 1 -A 6 'Lemma typing_nil_implies_closed\|typing.*closed' 02_FORMAL/coq/foundations/Typing.v 02_FORMAL/coq/type_system/Preservation.v | head -20
```

---

## PART 5: STEP RELATION

### 5.1 ST_AppAbs (Beta Reduction)
```bash
grep -n -B 3 -A 6 'ST_AppAbs' 02_FORMAL/coq/foundations/Semantics.v
```

### 5.2 Multi-step Relation
```bash
grep -n -A 20 'Inductive multi_step\|Reserved.*-->*' 02_FORMAL/coq/foundations/Semantics.v | head -30
```

---

## PART 6: SYNTAX

### 6.1 Expression Constructors
```bash
grep -n 'ELam\|EApp\|EPair\|EInl\|EInr\|EFn' 02_FORMAL/coq/foundations/Syntax.v | head -15
```

### 6.2 Value Inductive
```bash
grep -n -A 25 'Inductive value' 02_FORMAL/coq/foundations/Syntax.v
```

### 6.3 Type Constructors (especially TFn, TSum)
```bash
grep -n 'TFn\|TSum\|TProd' 02_FORMAL/coq/foundations/Syntax.v | head -10
```

---

## PART 7: combined_step_up_all STRUCTURE

### 7.1 The Main Theorem Statement
```bash
grep -n -B 5 -A 50 'Theorem combined_step_up_all\|Lemma combined_step_up_all' 02_FORMAL/coq/properties/NonInterference_v2.v | head -70
```

### 7.2 combined_step_up Definition
```bash
grep -n -B 2 -A 30 'Definition combined_step_up' 02_FORMAL/coq/properties/NonInterference_v2.v
```

### 7.3 val_rel_at_type_step_up_with_IH Lemma
```bash
grep -n -B 3 -A 60 'Lemma val_rel_at_type_step_up_with_IH\|val_rel_at_type_step_up' 02_FORMAL/coq/properties/NonInterference_v2.v | head -80
```

---

## PART 8: PROOF STATE AT EACH ADMIT

For EACH of the 13 admits, I need:
1. The enclosing lemma/theorem name
2. The EXACT Goal at that point
3. ALL hypotheses in scope (with types)
4. What case/branch we're in (n=0? TFn? TProd T1 where T1 is HO?)

Use `Print Ltac` or manual trace if needed.

---

## OUTPUT FORMAT REQUIREMENTS

Structure your response EXACTLY as follows:

```
=== SECTION 1: val_rel_at_type DEFINITION ===
[COMPLETE code from line X to line Y]
[Note which lines are TFn case]

=== SECTION 2: val_rel_n / store_rel_n ===
[COMPLETE mutual fixpoint]

=== SECTION 3: ADMIT CONTEXTS ===

--- ADMIT LINE 284 ---
Enclosing lemma: [name]
Goal: [exact goal]
Hypotheses:
  H1 : [type]
  H2 : [type]
  ...
Case: [what case are we in]

--- ADMIT LINE 286 ---
[same format]

[repeat for all 13]

=== SECTION 4: KEY DEFINITIONS ===
store_wf := [exact definition]
store_has_values := [exact definition]
stores_agree_low_fo := [exact definition]
first_order_type := [exact definition]
val_rel_at_type_fo := [exact definition for TSum case]

=== SECTION 5: AVAILABLE LEMMAS ===
canonical_forms_fn : [exact signature]
canonical_forms_prod : [exact signature]
canonical_forms_sum : [exact signature]
preservation : [exact signature]
substitution_preserves_typing : [exact signature]
value_has_pure_effect : [exact signature]
store_ty_extends_refl : [signature]
store_ty_extends_trans : [signature]
typing_nil_implies_closed : [signature]

=== SECTION 6: STEP RELATION ===
ST_AppAbs : [exact rule]
multi_step : [definition]

=== SECTION 7: SYNTAX ===
ELam signature: [from Inductive expr]
value cases: [from Inductive value]

=== SECTION 8: MAIN THEOREM STRUCTURE ===
combined_step_up : [definition]
combined_step_up_all : [theorem statement]
IH structure: [what induction, what IH available]
```

---

## CRITICAL REQUIREMENTS

1. **DO NOT SUMMARIZE** - Provide EXACT Coq code
2. **Include ALL type signatures** - Every argument, every return type
3. **Show EXACT Goal** at each admit - Copy from Coq's output
4. **Include line numbers** for everything
5. **Note any Unicode issues** - Σ vs Sigma, etc.
6. **If something doesn't exist**, say so explicitly

This output will be used to generate COMPILABLE Coq code to replace all admits.

---

## EXPECTED OUTPUT SIZE
Approximately 500-1000 lines of extracted code and context.
Do not truncate. Complete extraction is required.
