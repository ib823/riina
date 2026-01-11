# TERAS-LANG Research Domain H: Policy Languages

## Document Control

| Property | Value |
|----------|-------|
| Document ID | RESEARCH-H-POLICY-LANGUAGES |
| Version | 1.0.0 |
| Date | 2026-01-04 |
| Sessions | H-01 through H-10 |
| Domain | H: Policy Languages |
| Author | Claude (Anthropic) |
| Status | Complete |

---

# H-01: Access Control Models and Policy Foundations

## Executive Summary

Policy languages formalize security requirements into enforceable rules. This domain surveys all major access control models, policy specification languages, and their formal foundations relevant to TERAS security architecture.

## 1. Access Control Model Evolution

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Access Control Model Timeline                     │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  1960s-70s: DISCRETIONARY ACCESS CONTROL (DAC)                      │
│  ├── Owner controls access to resources                            │
│  ├── Access Control Lists (ACLs)                                   │
│  ├── Capability lists                                              │
│  └── Unix permissions (rwx), Windows ACLs                          │
│                                                                     │
│  1970s-80s: MANDATORY ACCESS CONTROL (MAC)                          │
│  ├── Bell-LaPadula (confidentiality)                               │
│  ├── Biba (integrity)                                              │
│  ├── System-enforced, users cannot change                          │
│  └── Military/government systems (MLS)                             │
│                                                                     │
│  1990s: ROLE-BASED ACCESS CONTROL (RBAC)                            │
│  ├── Users assigned to roles                                       │
│  ├── Roles have permissions                                        │
│  ├── Simplifies administration                                     │
│  └── NIST RBAC standard (2004)                                     │
│                                                                     │
│  2000s: ATTRIBUTE-BASED ACCESS CONTROL (ABAC)                       │
│  ├── Decisions based on attributes                                 │
│  ├── Subject, resource, environment attributes                     │
│  ├── Flexible, context-aware                                       │
│  └── XACML standard                                                │
│                                                                     │
│  2010s+: POLICY-BASED / INTENT-BASED                                │
│  ├── High-level policy specification                               │
│  ├── Automated enforcement                                         │
│  ├── Zero Trust architectures                                      │
│  └── Cloud-native policies (OPA, Cedar)                            │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## 2. Bell-LaPadula Model

### 2.1 Formal Definition

```
Bell-LaPadula Model (BLP):

Components:
├── S: Set of subjects (users, processes)
├── O: Set of objects (files, resources)
├── A: Set of access rights {read, write, append, execute}
├── L: Lattice of security levels (e.g., Unclassified < Secret < Top Secret)
├── fs: S → L (subject clearance function)
└── fo: O → L (object classification function)

Security Properties:

SIMPLE SECURITY (NO READ UP):
∀s ∈ S, o ∈ O: read(s, o) ⟹ fs(s) ≥ fo(o)
"A subject can only read objects at or below its clearance level"

*-PROPERTY (NO WRITE DOWN):
∀s ∈ S, o ∈ O: write(s, o) ⟹ fs(s) ≤ fo(o)
"A subject can only write to objects at or above its clearance level"

DISCRETIONARY SECURITY:
Access must also satisfy discretionary access control matrix

Basic Security Theorem:
If initial state is secure and all state transitions preserve
simple security and *-property, system remains secure.
```

### 2.2 BLP Limitations

```
Limitations:
├── Covert channels: Not addressed by model
├── Declassification: No mechanism for downgrading
├── Integrity: Not addressed (see Biba)
├── Trusted subjects: Must bypass for practical systems
└── Write-down problem: Can't edit lower-classified docs

Practical Adaptations:
├── Tranquility principle (levels don't change)
├── Trusted subjects (can violate for specific purposes)
├── Compartments (need-to-know within levels)
└── Categories (horizontal partitioning)
```

## 3. Biba Integrity Model

### 3.1 Formal Definition

```
Biba Model:

Dual of Bell-LaPadula for INTEGRITY:

Components:
├── Same structure as BLP
└── I: Lattice of integrity levels (Low < High)

Security Properties:

SIMPLE INTEGRITY (NO READ DOWN):
∀s ∈ S, o ∈ O: read(s, o) ⟹ fi(s) ≤ fi(o)
"A subject can only read objects at or above its integrity level"
(Don't trust data from less trustworthy sources)

*-INTEGRITY (NO WRITE UP):
∀s ∈ S, o ∈ O: write(s, o) ⟹ fi(s) ≥ fi(o)
"A subject can only write to objects at or below its integrity level"
(Don't corrupt more trustworthy data)

Variants:
├── Low-Water-Mark: Subject integrity drops on reading low data
├── Ring Policy: Subject can read any level
└── Strict Integrity: Both properties enforced
```

## 4. Clark-Wilson Integrity Model

### 4.1 Commercial Integrity

```
Clark-Wilson Model (1987):

Focus: Commercial/business integrity (not military)

Components:
├── CDI: Constrained Data Items (protected data)
├── UDI: Unconstrained Data Items (unvalidated input)
├── TP: Transformation Procedures (valid operations on CDI)
├── IVP: Integrity Verification Procedures (validate CDI)
└── Users: Authenticated principals

Rules:

CERTIFICATION RULES (CR):
CR1: IVPs must ensure all CDIs are valid
CR2: TPs must transform CDIs to valid states
CR3: CDI access must satisfy separation of duty
CR4: TPs must write to append-only log
CR5: TPs on UDIs must convert to CDIs or reject

ENFORCEMENT RULES (ER):
ER1: System must maintain certified TP-CDI relations
ER2: System must maintain User-TP-CDI triples
ER3: User identity must be authenticated
ER4: Only certifier can modify TP-CDI and User-TP-CDI

Key Concepts:
├── Well-formed transactions: Only valid transformations
├── Separation of duty: No user controls entire transaction
└── Auditing: All operations logged
```

## TERAS Decision H-01

**FOR TERAS:**
1. Implement multi-model support (MAC + RBAC + ABAC)
2. Clark-Wilson principles for data integrity
3. Bell-LaPadula for confidentiality labeling
4. Formal verification of policy properties

### Architecture Decision ID: `TERAS-ARCH-H01-MODELS-001`

---

# H-02: XACML (eXtensible Access Control Markup Language)

## 1. XACML Architecture

### 1.1 Component Model

```
┌─────────────────────────────────────────────────────────────────────┐
│                    XACML Architecture                                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────┐                                                   │
│  │    User     │                                                   │
│  └──────┬──────┘                                                   │
│         │ Request                                                   │
│         ▼                                                           │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │              Policy Enforcement Point (PEP)                  │   │
│  │              Intercepts access request                       │   │
│  └──────────────────────────┬──────────────────────────────────┘   │
│                             │ XACML Request                        │
│                             ▼                                       │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │              Policy Decision Point (PDP)                     │   │
│  │              Evaluates policies, returns decision            │   │
│  │                                                              │   │
│  │  ┌─────────────────┐  ┌─────────────────┐                   │   │
│  │  │ Policy Store    │  │ Attribute Store │                   │   │
│  │  │ (PAP output)    │  │ (PIP queries)   │                   │   │
│  │  └─────────────────┘  └─────────────────┘                   │   │
│  └──────────────────────────┬──────────────────────────────────┘   │
│                             │ Decision                             │
│                             ▼                                       │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                      PEP                                     │   │
│  │              Enforces decision (Permit/Deny)                 │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
│  Additional Components:                                             │
│  ├── PAP (Policy Administration Point): Create/manage policies     │
│  ├── PIP (Policy Information Point): Retrieve attributes           │
│  └── PRP (Policy Retrieval Point): Find applicable policies        │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 XACML Policy Structure

```xml
<!-- XACML 3.0 Policy Example -->
<Policy xmlns="urn:oasis:names:tc:xacml:3.0:core:schema:wd-17"
        PolicyId="medical-records-policy"
        RuleCombiningAlgId="urn:oasis:names:tc:xacml:3.0:rule-combining-algorithm:deny-unless-permit"
        Version="1.0">
  
  <Description>Medical records access control policy</Description>
  
  <Target>
    <AnyOf>
      <AllOf>
        <Match MatchId="urn:oasis:names:tc:xacml:1.0:function:string-equal">
          <AttributeValue DataType="http://www.w3.org/2001/XMLSchema#string">
            medical-record
          </AttributeValue>
          <AttributeDesignator 
            Category="urn:oasis:names:tc:xacml:3.0:attribute-category:resource"
            AttributeId="resource-type"
            DataType="http://www.w3.org/2001/XMLSchema#string"/>
        </Match>
      </AllOf>
    </AnyOf>
  </Target>
  
  <Rule RuleId="doctor-read-own-patients" Effect="Permit">
    <Description>Doctors can read their own patients' records</Description>
    <Target>
      <AnyOf>
        <AllOf>
          <Match MatchId="urn:oasis:names:tc:xacml:1.0:function:string-equal">
            <AttributeValue DataType="http://www.w3.org/2001/XMLSchema#string">
              read
            </AttributeValue>
            <AttributeDesignator 
              Category="urn:oasis:names:tc:xacml:3.0:attribute-category:action"
              AttributeId="action-id"
              DataType="http://www.w3.org/2001/XMLSchema#string"/>
          </Match>
        </AllOf>
      </AnyOf>
    </Target>
    <Condition>
      <Apply FunctionId="urn:oasis:names:tc:xacml:1.0:function:and">
        <Apply FunctionId="urn:oasis:names:tc:xacml:1.0:function:string-equal">
          <AttributeDesignator 
            Category="urn:oasis:names:tc:xacml:1.0:subject-category:access-subject"
            AttributeId="role"
            DataType="http://www.w3.org/2001/XMLSchema#string"/>
          <AttributeValue DataType="http://www.w3.org/2001/XMLSchema#string">
            doctor
          </AttributeValue>
        </Apply>
        <Apply FunctionId="urn:oasis:names:tc:xacml:1.0:function:string-equal">
          <AttributeDesignator 
            Category="urn:oasis:names:tc:xacml:1.0:subject-category:access-subject"
            AttributeId="treating-physician"
            DataType="http://www.w3.org/2001/XMLSchema#string"/>
          <AttributeDesignator 
            Category="urn:oasis:names:tc:xacml:3.0:attribute-category:resource"
            AttributeId="patient-physician"
            DataType="http://www.w3.org/2001/XMLSchema#string"/>
        </Apply>
      </Apply>
    </Condition>
  </Rule>
  
  <Rule RuleId="default-deny" Effect="Deny">
    <Description>Default deny rule</Description>
  </Rule>
  
</Policy>
```

### 1.3 XACML Combining Algorithms

```
Policy/Rule Combining Algorithms:

DENY-OVERRIDES:
├── Any Deny → Deny
├── All Permit → Permit
└── Use case: Conservative security

PERMIT-OVERRIDES:
├── Any Permit → Permit
├── All Deny → Deny
└── Use case: Allow-list scenarios

FIRST-APPLICABLE:
├── First matching rule's effect
└── Use case: Ordered rule evaluation

ONLY-ONE-APPLICABLE:
├── Exactly one policy must apply
├── Otherwise: Indeterminate
└── Use case: Strict policy separation

DENY-UNLESS-PERMIT:
├── Permit requires explicit Permit
├── Default is Deny
└── Use case: Whitelist approach

PERMIT-UNLESS-DENY:
├── Deny requires explicit Deny
├── Default is Permit
└── Use case: Blacklist approach
```

## 2. XACML Limitations and Alternatives

```
XACML Limitations:
├── Verbosity: XML syntax very verbose
├── Performance: Complex policy evaluation can be slow
├── Complexity: Steep learning curve
├── Testing: Difficult to test comprehensive scenarios
└── Real-time: Not suited for high-throughput decisions

Modern Alternatives:
├── OPA (Open Policy Agent): Rego language, cloud-native
├── Cedar: AWS, Rust-based, formally verified
├── Casbin: Multi-language, PERM model
└── Google Zanzibar / SpiceDB: Relationship-based
```

## TERAS Decision H-02

**FOR TERAS:**
1. Support XACML for enterprise integration
2. Prefer modern engines (OPA/Cedar) for new deployments
3. Provide policy translation tools
4. Implement efficient policy caching

### Architecture Decision ID: `TERAS-ARCH-H02-XACML-001`

---

# H-03: SELinux and Mandatory Access Control

## 1. SELinux Architecture

### 1.1 Security Context

```
┌─────────────────────────────────────────────────────────────────────┐
│                    SELinux Security Context                          │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Context Format: user:role:type:level                               │
│                                                                     │
│  Example: system_u:system_r:httpd_t:s0                             │
│           ────────  ────────  ──────  ──                           │
│              │         │        │      │                            │
│              │         │        │      └── MLS/MCS Level           │
│              │         │        └───────── Type (most important)   │
│              │         └────────────────── Role                    │
│              └──────────────────────────── User                    │
│                                                                     │
│  Type Enforcement (TE):                                             │
│  ├── Primary mechanism                                             │
│  ├── Types assigned to subjects and objects                        │
│  ├── Policy rules specify allowed interactions                     │
│  └── Default deny: unlisted interactions blocked                   │
│                                                                     │
│  Role-Based Access Control (RBAC):                                  │
│  ├── Roles group types                                             │
│  ├── Users assigned to roles                                       │
│  └── Restricts which types user can assume                         │
│                                                                     │
│  Multi-Level Security (MLS):                                        │
│  ├── Bell-LaPadula implementation                                  │
│  ├── Sensitivity levels (s0, s1, ...)                             │
│  ├── Categories (c0, c1, ...)                                     │
│  └── Range: s0-s15:c0.c1023                                        │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 SELinux Policy Language

```
# Type Enforcement Rules

# Type declaration
type httpd_t;
type httpd_config_t;
type httpd_log_t;
type httpd_sys_content_t;

# Role declaration
role system_r types httpd_t;

# Allow rule syntax:
# allow source_type target_type:class { permissions };

# Allow httpd to read config files
allow httpd_t httpd_config_t:file { read getattr open };

# Allow httpd to write log files
allow httpd_t httpd_log_t:file { write append create getattr open };

# Allow httpd to read web content
allow httpd_t httpd_sys_content_t:file { read getattr open };
allow httpd_t httpd_sys_content_t:dir { search getattr };

# Network access
allow httpd_t http_port_t:tcp_socket { name_bind name_connect };

# Type transition (process spawning)
type_transition init_t httpd_exec_t:process httpd_t;

# Domain transition rules
allow init_t httpd_t:process transition;
allow httpd_t httpd_exec_t:file { read getattr execute entrypoint };

# Constrain statement (MLS enforcement)
constrain file { write } 
    ( l1 dom l2 or t1 == mlsfilewrite );
```

### 1.3 SELinux Modes and Tools

```
Operation Modes:
├── Enforcing: Policy enforced, violations blocked
├── Permissive: Policy not enforced, violations logged
└── Disabled: SELinux not active

Management Tools:
├── semanage: Manage policy components
├── sestatus: Show SELinux status
├── seinfo: Query policy information
├── sesearch: Search policy rules
├── audit2allow: Generate rules from denials
├── audit2why: Explain denial reasons
└── restorecon: Restore file contexts

Common Operations:
# Check status
sestatus

# Set boolean (runtime policy tuning)
setsebool -P httpd_can_network_connect on

# Add file context
semanage fcontext -a -t httpd_sys_content_t "/web(/.*)?"
restorecon -Rv /web

# Generate policy module from denials
audit2allow -M mymodule < /var/log/audit/audit.log
semodule -i mymodule.pp
```

## 2. AppArmor

### 2.1 AppArmor Profiles

```
# AppArmor Profile Example: /etc/apparmor.d/usr.sbin.nginx

#include <tunables/global>

/usr/sbin/nginx {
  #include <abstractions/base>
  #include <abstractions/nameservice>
  
  # Capabilities
  capability net_bind_service,
  capability setuid,
  capability setgid,
  capability dac_override,
  
  # Network
  network inet stream,
  network inet6 stream,
  
  # Binary and libraries
  /usr/sbin/nginx mr,
  /lib/x86_64-linux-gnu/** mr,
  /usr/lib/** mr,
  
  # Configuration
  /etc/nginx/** r,
  /etc/ssl/** r,
  
  # Web content
  /var/www/** r,
  /srv/www/** r,
  
  # Logs
  /var/log/nginx/** w,
  
  # Runtime
  /run/nginx.pid rw,
  /var/lib/nginx/** rw,
  
  # Temporary files
  /tmp/** rw,
  
  # Deny everything else by default
}
```

### 2.2 SELinux vs AppArmor

```
Comparison:

                SELinux              AppArmor
────────────────────────────────────────────────────
Approach        Label-based          Path-based
Granularity     Very fine            Coarse
Complexity      High                 Medium
Learning curve  Steep                Moderate
Performance     Overhead moderate    Lower overhead
Default distro  RHEL/Fedora/CentOS   Ubuntu/SUSE
Policy mgmt     Difficult            Easier
MLS support     Yes                  No
```

## TERAS Decision H-03

**FOR TERAS:**
1. Provide SELinux policy modules for TERAS components
2. Provide AppArmor profiles for Ubuntu deployments
3. Document mandatory access control requirements
4. Test policy coverage for all operations

### Architecture Decision ID: `TERAS-ARCH-H03-MAC-001`

---

# H-04: Open Policy Agent (OPA) and Rego

## 1. OPA Architecture

### 1.1 Design Philosophy

```
┌─────────────────────────────────────────────────────────────────────┐
│                    OPA Architecture                                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Design Principles:                                                 │
│  ├── Policy as Code: Version, test, deploy like code               │
│  ├── Decoupled: Separate policy from application                   │
│  ├── Declarative: Describe what, not how                           │
│  └── Universal: Same engine for all policy decisions               │
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                      Application                             │   │
│  │  ┌──────────────────────────────────────────────────────┐   │   │
│  │  │  Decision Request                                     │   │   │
│  │  │  {                                                    │   │   │
│  │  │    "input": {                                         │   │   │
│  │  │      "user": "alice",                                 │   │   │
│  │  │      "action": "read",                                │   │   │
│  │  │      "resource": "/documents/secret.pdf"              │   │   │
│  │  │    }                                                  │   │   │
│  │  │  }                                                    │   │   │
│  │  └────────────────────────┬─────────────────────────────┘   │   │
│  └───────────────────────────┼─────────────────────────────────┘   │
│                              ▼                                      │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                         OPA                                  │   │
│  │  ┌──────────────────┐  ┌──────────────────┐                 │   │
│  │  │    Rego Policy   │  │      Data        │                 │   │
│  │  │   (rules)        │  │   (JSON facts)   │                 │   │
│  │  └──────────────────┘  └──────────────────┘                 │   │
│  │                              │                               │   │
│  │                              ▼                               │   │
│  │  ┌──────────────────────────────────────────────────────┐   │   │
│  │  │  Decision Response: {"allow": true}                   │   │   │
│  │  └──────────────────────────────────────────────────────┘   │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Rego Language

```rego
# Rego Policy Example

package authz

import future.keywords.if
import future.keywords.in

# Default deny
default allow := false

# Allow if user is admin
allow if {
    input.user == data.admins[_]
}

# Allow if user has required permission
allow if {
    # Get user's roles
    roles := data.user_roles[input.user]
    
    # Check if any role has the required permission
    some role in roles
    permissions := data.role_permissions[role]
    required := sprintf("%s:%s", [input.action, input.resource])
    required in permissions
}

# RBAC data structure
user_roles := {
    "alice": ["developer", "viewer"],
    "bob": ["admin"],
    "charlie": ["viewer"]
}

role_permissions := {
    "admin": ["read:*", "write:*", "delete:*"],
    "developer": ["read:code", "write:code", "read:docs"],
    "viewer": ["read:docs"]
}

admins := ["bob"]

# Complex conditions
allow if {
    input.action == "read"
    input.resource == "public"
}

# Time-based access
allow if {
    input.action == "access"
    input.resource == "maintenance-panel"
    time.now_ns() >= time.parse_rfc3339_ns(data.maintenance_window.start)
    time.now_ns() <= time.parse_rfc3339_ns(data.maintenance_window.end)
}

# Deny rules (explicit)
deny if {
    input.user in data.blacklist
}

# Final decision
result := {
    "allow": allow,
    "deny": deny,
    "reason": reason
}
```

### 1.3 OPA Use Cases

```
Kubernetes Admission Control:
├── Gatekeeper: OPA for Kubernetes
├── Validate pod specs
├── Enforce resource limits
├── Require labels/annotations
└── Network policy enforcement

API Authorization:
├── Envoy external authorization
├── Kong/NGINX plugins
├── Direct API integration
└── Microservice authorization

Infrastructure as Code:
├── Terraform plan validation
├── CloudFormation review
├── Kubernetes manifest checking
└── Compliance scanning

Data Access:
├── Database query filtering
├── GraphQL field authorization
├── Column-level security
└── Row-level filtering
```

## 2. OPA Performance and Deployment

### 2.1 Optimization

```
Performance Considerations:

Partial Evaluation:
├── Pre-compile policies with known data
├── Generate residual policy
├── Faster runtime evaluation
└── Use for Envoy integration

Caching:
├── Decision caching
├── Policy bundle caching
├── Data caching
└── Cache invalidation strategy

Benchmarks:
├── Simple rules: ~10μs
├── Complex RBAC: ~100μs
├── Large dataset joins: ~1ms
└── Target: <1ms for most decisions
```

## TERAS Decision H-04

**FOR TERAS:**
1. Use OPA/Rego as primary policy engine
2. Implement TERAS-specific Rego libraries
3. Provide policy templates for common patterns
4. Performance testing for real-time decisions

### Architecture Decision ID: `TERAS-ARCH-H04-OPA-001`

---

# H-05: AWS Cedar Policy Language

## 1. Cedar Architecture

### 1.1 Design

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Cedar Architecture                                │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Design Goals:                                                      │
│  ├── Expressive: Rich policy conditions                            │
│  ├── Fast: Efficient evaluation                                    │
│  ├── Analyzable: Formal verification possible                      │
│  └── Safe: No arbitrary code execution                             │
│                                                                     │
│  Components:                                                        │
│  ├── Policies: Authorization rules                                 │
│  ├── Entities: Principals, resources, actions                      │
│  ├── Schema: Type definitions                                      │
│  └── Authorizer: Evaluation engine                                 │
│                                                                     │
│  Formal Properties:                                                 │
│  ├── Decidable: Always terminates                                  │
│  ├── Sound: Proven correct                                         │
│  ├── Complete: All valid policies expressible                      │
│  └── Verified: Dafny proofs                                        │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Cedar Policy Syntax

```
// Cedar Policy Examples

// Basic permit
permit (
    principal == User::"alice",
    action == Action::"read",
    resource == Document::"report.pdf"
);

// Role-based with conditions
permit (
    principal in Group::"developers",
    action in [Action::"read", Action::"write"],
    resource in Folder::"projects"
) when {
    resource.classification != "confidential"
};

// Attribute-based
permit (
    principal,
    action == Action::"access",
    resource
) when {
    principal.department == resource.department &&
    principal.clearance >= resource.requiredClearance
};

// Time-based
permit (
    principal in Group::"contractors",
    action,
    resource
) when {
    context.time.hour >= 9 &&
    context.time.hour < 17 &&
    context.time.dayOfWeek in ["Monday", "Tuesday", "Wednesday", "Thursday", "Friday"]
};

// Forbid (explicit deny)
forbid (
    principal,
    action == Action::"delete",
    resource
) unless {
    principal in Group::"admins"
};

// Hierarchy traversal
permit (
    principal,
    action == Action::"read",
    resource
) when {
    principal in resource.owner.organization
};
```

### 1.3 Cedar Schema

```
// Cedar Schema Definition

namespace PhotoApp {
    entity User in [Group, Organization] {
        department: String,
        clearance: Long,
        email: String
    };
    
    entity Group in [Organization];
    
    entity Organization;
    
    entity Photo {
        owner: User,
        album: Album,
        classification: String,
        tags: Set<String>
    };
    
    entity Album in [Folder] {
        owner: User,
        shared_with: Set<User>
    };
    
    entity Folder {
        owner: User
    };
    
    action view appliesTo {
        principal: User,
        resource: Photo
    };
    
    action edit appliesTo {
        principal: User,
        resource: [Photo, Album]
    };
    
    action delete appliesTo {
        principal: User,
        resource: [Photo, Album, Folder]
    };
}
```

## 2. Cedar vs OPA

```
Comparison:

                Cedar                    OPA/Rego
────────────────────────────────────────────────────────
Language        Purpose-built DSL        General-purpose
Verification    Formally verified        No formal proofs
Expressiveness  Constrained (safe)       Turing-complete
Performance     Highly optimized         Good, varies
Learning curve  Lower                    Higher
Ecosystem       AWS-focused              Broad
Schema support  Built-in                 Optional
Analysis tools  Built-in                 External
```

## TERAS Decision H-05

**FOR TERAS:**
1. Evaluate Cedar for new policy requirements
2. Leverage formal verification properties
3. Consider Cedar for BENTENG access control
4. Compare performance with OPA for use case

### Architecture Decision ID: `TERAS-ARCH-H05-CEDAR-001`

---

# H-06: Google Zanzibar and Relationship-Based Access Control

## 1. Zanzibar Model

### 1.1 Architecture

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Zanzibar Architecture                             │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Core Concept: Relationship-Based Access Control (ReBAC)            │
│                                                                     │
│  Relationships:                                                     │
│  ├── <object>#<relation>@<user>                                    │
│  │   Example: document:readme#viewer@user:alice                    │
│  │            folder:root#parent@document:readme                   │
│  │                                                                  │
│  └── Relations can be:                                             │
│      ├── Direct: Explicit tuple                                    │
│      ├── Inherited: Through parent relations                       │
│      └── Computed: Via usersets                                    │
│                                                                     │
│  Data Model:                                                        │
│  ┌────────────────────────────────────────────────────────────┐    │
│  │  Relation Tuples:                                           │    │
│  │  ┌────────────────────────────────────────────────────┐    │    │
│  │  │ Object          │ Relation │ User/Userset          │    │    │
│  │  ├────────────────────────────────────────────────────┤    │    │
│  │  │ doc:readme      │ owner    │ user:alice            │    │    │
│  │  │ doc:readme      │ viewer   │ group:engineering#mem │    │    │
│  │  │ folder:root     │ parent   │ doc:readme            │    │    │
│  │  │ group:eng       │ member   │ user:bob              │    │    │
│  │  └────────────────────────────────────────────────────┘    │    │
│  └────────────────────────────────────────────────────────────┘    │
│                                                                     │
│  Scale: 10M+ QPS, global consistency                               │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 Namespace Configuration

```
// Zanzibar-style Configuration (SpiceDB syntax)

definition user {}

definition group {
    relation member: user | group#member
}

definition organization {
    relation admin: user
    relation member: user | group#member
}

definition folder {
    relation owner: user
    relation parent: folder
    relation viewer: user | group#member | folder#viewer
    
    permission view = viewer + owner + parent->view
    permission edit = owner + parent->edit
}

definition document {
    relation owner: user
    relation parent: folder
    relation viewer: user | group#member
    relation editor: user | group#member
    
    // Computed permissions
    permission view = viewer + editor + owner + parent->view
    permission edit = editor + owner + parent->edit
    permission delete = owner
}
```

### 1.3 Check Algorithm

```
Check Algorithm (simplified):

Input: object, relation, user
Output: boolean (has permission?)

function check(object, relation, user):
    // Direct check
    if tuple_exists(object, relation, user):
        return true
    
    // Userset expansion
    for userset in get_usersets(object, relation):
        if check(userset.object, userset.relation, user):
            return true
    
    // Computed relations (rewrite rules)
    for rewrite in get_rewrites(object.type, relation):
        if evaluate_rewrite(rewrite, object, user):
            return true
    
    return false

Optimizations:
├── Memoization: Cache intermediate results
├── Parallel evaluation: Check branches concurrently
├── Indexing: Efficient tuple lookup
└── Zookies: Consistency tokens for caching
```

## 2. Open Source Implementations

### 2.1 SpiceDB

```
SpiceDB (Open Source Zanzibar):

Features:
├── Zanzibar-compatible API
├── Schema language
├── gRPC and HTTP APIs
├── Multiple storage backends
├── Watch API for changes
└── Caveats (conditions)

Example Usage:
# Write relationships
spicedb write document:readme#viewer@user:alice
spicedb write folder:root#parent@document:readme

# Check permission
spicedb check document:readme viewer user:alice
# Result: true

# Expand permissions
spicedb expand document:readme viewer
# Returns all users with viewer permission
```

### 2.2 Other Implementations

```
OpenFGA (Auth0/Okta):
├── Zanzibar-inspired
├── JSON-based configuration
├── SDK for multiple languages
└── Cloud-hosted option

Ory Keto:
├── Zanzibar implementation
├── Part of Ory ecosystem
├── gRPC API
└── Kubernetes-native

Authzed (SpiceDB commercial):
├── Managed SpiceDB
├── Enterprise features
├── Global deployment
└── SLA guarantees
```

## TERAS Decision H-06

**FOR TERAS:**
1. Use ReBAC for BENTENG identity relationships
2. Consider SpiceDB for complex permission graphs
3. Integrate with OPA for combined policy evaluation
4. Design schema for TERAS resource relationships

### Architecture Decision ID: `TERAS-ARCH-H06-REBAC-001`

---

# H-07: Formal Policy Analysis and Verification

## 1. Policy Analysis Techniques

### 1.1 Property Checking

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Policy Analysis Properties                        │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  SAFETY PROPERTIES:                                                 │
│  ├── No unauthorized access possible                               │
│  ├── Separation of duty enforced                                   │
│  ├── Least privilege maintained                                    │
│  └── Information flow constraints satisfied                        │
│                                                                     │
│  COMPLETENESS PROPERTIES:                                           │
│  ├── All legitimate access permitted                               │
│  ├── No gaps in policy coverage                                    │
│  └── Business functions achievable                                 │
│                                                                     │
│  CONSISTENCY PROPERTIES:                                            │
│  ├── No conflicting rules                                          │
│  ├── Policy priorities well-defined                                │
│  └── Deterministic decisions                                       │
│                                                                     │
│  ANALYSIS QUESTIONS:                                                │
│  ├── Can user X ever access resource Y?                            │
│  ├── What can user X access?                                       │
│  ├── Who can access resource Y?                                    │
│  ├── Are policies P1 and P2 equivalent?                            │
│  ├── Is policy P more permissive than Q?                           │
│  └── Does adding rule R change any decision?                       │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 SMT-Based Verification

```
// Policy verification using Z3 SMT solver

from z3 import *

# Define sorts
User = DeclareSort('User')
Resource = DeclareSort('Resource')
Action = DeclareSort('Action')
Role = DeclareSort('Role')

# Define relations
has_role = Function('has_role', User, Role, BoolSort())
role_permits = Function('role_permits', Role, Action, Resource, BoolSort())
can_access = Function('can_access', User, Action, Resource, BoolSort())

# Define constants
alice = Const('alice', User)
bob = Const('bob', User)
admin = Const('admin', Role)
user = Const('user', Role)
read = Const('read', Action)
write = Const('write', Action)
secret = Const('secret', Resource)
public = Const('public', Resource)

# Policy rules
s = Solver()

# Rule 1: Users can access what their roles permit
u, a, r, ro = Consts('u a r ro', [User, Action, Resource, Role])
s.add(ForAll([u, a, r], 
    Implies(
        Exists([ro], And(has_role(u, ro), role_permits(ro, a, r))),
        can_access(u, a, r)
    )
))

# Rule 2: Admin can do everything
s.add(ForAll([a, r], role_permits(admin, a, r)))

# Rule 3: User can only read public
s.add(role_permits(user, read, public))
s.add(Not(role_permits(user, write, public)))
s.add(Not(role_permits(user, read, secret)))
s.add(Not(role_permits(user, write, secret)))

# Fact: Alice is admin, Bob is user
s.add(has_role(alice, admin))
s.add(has_role(bob, user))

# Query: Can Bob access secret?
s.push()
s.add(can_access(bob, read, secret))
result = s.check()  # UNSAT = Bob cannot access secret
s.pop()

# Query: Can Alice access secret?
s.push()
s.add(Not(can_access(alice, read, secret)))
result = s.check()  # UNSAT = Alice CAN access secret
```

## 2. Margrave Policy Analyzer

### 2.1 Analysis Capabilities

```
Margrave Features:

Policy Comparison:
├── Identify differences between policies
├── Show added/removed permissions
└── Verify backward compatibility

Change Impact Analysis:
├── What changes if we add rule X?
├── Who gains/loses access?
└── Regression testing for policies

Query Language:
EXPLORE policy1 
    INCLUDE (s, a, r) 
    WHERE permitted(s, a, r) 
    AND resource-type(r) = "database"

COMPARE policy1, policy2
    SHOW ADDED permissions
```

## TERAS Decision H-07

**FOR TERAS:**
1. Implement policy analysis tools
2. Verify safety properties before deployment
3. Automated policy testing in CI/CD
4. Change impact analysis for policy updates

### Architecture Decision ID: `TERAS-ARCH-H07-ANALYSIS-001`

---

# H-08: Information Flow Policies

## 1. Decentralized Information Flow Control (DIFC)

### 1.1 Label Model

```
┌─────────────────────────────────────────────────────────────────────┐
│                    DIFC Label Model                                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  Label Structure: L = (S, I)                                       │
│  ├── S: Secrecy component (who can read)                           │
│  └── I: Integrity component (who can write)                        │
│                                                                     │
│  Label Components (sets of principals):                             │
│  ├── {alice, bob}: Alice and Bob own this data                     │
│  ├── {}: Public data (anyone can access)                           │
│  └── {⊤}: Top/universal (no one can access)                        │
│                                                                     │
│  Flow Rules:                                                        │
│  L1 ⊑ L2 iff S1 ⊇ S2 ∧ I1 ⊆ I2                                    │
│  (More restrictive can flow to less restrictive for secrecy)        │
│  (Less trusted can flow to more trusted for integrity)              │
│                                                                     │
│  Operations:                                                        │
│  ├── Join (⊔): Most restrictive combination                        │
│  ├── Meet (⊓): Least restrictive combination                       │
│  └── Declassify/Endorse: Privilege-controlled label change         │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 DLM (Decentralized Label Model)

```
JIF (Java Information Flow) Label Syntax:

// Simple labels
{alice:}           // Alice owns, readable by alice
{alice: bob}       // Alice owns, readable by alice and bob
{alice: bob, charlie}  // Alice owns, readable by alice, bob, charlie
{alice:; bob:}     // Both alice and bob own (intersection of readers)

// Integrity labels
{*←alice}          // Integrity: endorsed by alice
{alice:; *←bob}    // Secrecy from alice, integrity from bob

// Declassification
// Principal alice can remove herself from secrecy label
// if (actsFor(currentPrincipal, alice)) {
//     declassify(data, {alice:} to {:})
// }

// Label inference
int{alice:} x = ...;
int{bob:} y = ...;
int{alice:; bob:} z = x + y;  // Join of labels
```

## 2. Policy DSLs for IFC

### 2.1 FlowSpec

```
// FlowSpec Policy Language

// Define security levels
level public;
level internal;
level confidential;
level secret;

// Define ordering
public < internal < confidential < secret;

// Define compartments
compartment hr;
compartment finance;
compartment engineering;

// Label definitions
label PublicData = public;
label InternalDoc = internal;
label HRData = confidential + hr;
label FinanceData = confidential + finance;
label TopSecret = secret + hr + finance;

// Flow policies
policy SeparationOfDuty {
    // HR data cannot flow to finance
    deny flow HRData -> finance;
    deny flow FinanceData -> hr;
}

policy NeedToKnow {
    // Compartmented data only flows within compartment
    deny flow (confidential + C) -> ~C for any compartment C;
}

// Declassification policies
declassify HRData -> InternalDoc
    when principal in Role("HR_Manager")
    audit "HR data declassified to internal";
```

## TERAS Decision H-08

**FOR TERAS:**
1. Implement IFC policy language for TERAS-LANG
2. Support decentralized labels (DLM-style)
3. Controlled declassification with audit
4. Integration with type system for enforcement

### Architecture Decision ID: `TERAS-ARCH-H08-IFC-001`

---

# H-09: Domain-Specific Security Policies

## 1. Database Security Policies

### 1.1 Row-Level Security (RLS)

```sql
-- PostgreSQL Row-Level Security Example

-- Enable RLS on table
ALTER TABLE medical_records ENABLE ROW LEVEL SECURITY;

-- Policy: Doctors can see their patients' records
CREATE POLICY doctor_view_policy ON medical_records
    FOR SELECT
    TO doctors
    USING (treating_physician_id = current_user_id());

-- Policy: Patients can see only their own records
CREATE POLICY patient_view_policy ON medical_records
    FOR SELECT
    TO patients
    USING (patient_id = current_user_id());

-- Policy: Admins can see all (audit purposes)
CREATE POLICY admin_view_policy ON medical_records
    FOR SELECT
    TO admins
    USING (true);

-- Policy: Only treating doctor can update
CREATE POLICY doctor_update_policy ON medical_records
    FOR UPDATE
    TO doctors
    USING (treating_physician_id = current_user_id())
    WITH CHECK (treating_physician_id = current_user_id());

-- Column-level encryption
CREATE POLICY ssn_view_policy ON patients
    FOR SELECT (ssn)
    TO authorized_viewers
    USING (has_clearance(current_user(), 'PII'));
```

### 1.2 Application-Level Policies

```python
# SQLAlchemy with policy enforcement

class PolicyEnforcedQuery:
    def __init__(self, user, model):
        self.user = user
        self.model = model
        
    def apply_policies(self, query):
        policies = get_policies_for_model(self.model)
        
        for policy in policies:
            if policy.type == 'row_filter':
                query = query.filter(
                    policy.condition(self.user)
                )
            elif policy.type == 'column_mask':
                query = query.options(
                    defer(policy.column) if not policy.allowed(self.user)
                    else identity()
                )
        
        return query

# Usage
@app.route('/records')
def get_records():
    user = get_current_user()
    query = PolicyEnforcedQuery(user, MedicalRecord)
    records = query.apply_policies(
        MedicalRecord.query
    ).all()
    return jsonify(records)
```

## 2. Network Security Policies

### 2.1 Network Policy (Kubernetes)

```yaml
# Kubernetes Network Policy

apiVersion: networking.k8s.io/v1
kind: NetworkPolicy
metadata:
  name: api-server-policy
  namespace: production
spec:
  podSelector:
    matchLabels:
      app: api-server
  policyTypes:
    - Ingress
    - Egress
  
  ingress:
    # Allow from frontend
    - from:
        - podSelector:
            matchLabels:
              app: frontend
        - namespaceSelector:
            matchLabels:
              name: production
      ports:
        - protocol: TCP
          port: 8080
    
    # Allow from monitoring
    - from:
        - namespaceSelector:
            matchLabels:
              name: monitoring
      ports:
        - protocol: TCP
          port: 9090
  
  egress:
    # Allow to database
    - to:
        - podSelector:
            matchLabels:
              app: database
      ports:
        - protocol: TCP
          port: 5432
    
    # Allow to external API
    - to:
        - ipBlock:
            cidr: 203.0.113.0/24
      ports:
        - protocol: TCP
          port: 443
```

## TERAS Decision H-09

**FOR TERAS:**
1. Provide policy templates for common domains
2. Database policy integration (RLS helpers)
3. Network policy generation from security model
4. Domain-specific policy languages where beneficial

### Architecture Decision ID: `TERAS-ARCH-H09-DOMAIN-001`

---

# H-10: TERAS Policy Framework Integration

## 1. Unified Policy Architecture

### 1.1 TERAS Policy Stack

```
┌─────────────────────────────────────────────────────────────────────┐
│                    TERAS Policy Architecture                         │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                    Policy Definition Layer                   │   │
│  │  ┌───────────────────────────────────────────────────────┐  │   │
│  │  │  TERAS Policy DSL (based on Cedar/Rego hybrid)        │  │   │
│  │  │  - Type-safe policy definitions                       │  │   │
│  │  │  - Formal verification support                        │  │   │
│  │  │  - Product-specific extensions                        │  │   │
│  │  └───────────────────────────────────────────────────────┘  │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              │                                      │
│                              ▼                                      │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                    Policy Compilation Layer                  │   │
│  │  - Parse and validate policies                              │   │
│  │  - Type check against schema                                │   │
│  │  - Verify formal properties                                 │   │
│  │  - Optimize for evaluation                                  │   │
│  │  - Generate enforcement code                                │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              │                                      │
│                              ▼                                      │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                    Policy Runtime Layer                      │   │
│  │  ┌─────────────┐ ┌─────────────┐ ┌─────────────┐           │   │
│  │  │ TERAS-Core  │ │    OPA      │ │   Cedar     │           │   │
│  │  │ (embedded)  │ │ (external)  │ │ (external)  │           │   │
│  │  └─────────────┘ └─────────────┘ └─────────────┘           │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                              │                                      │
│                              ▼                                      │
│  ┌─────────────────────────────────────────────────────────────┐   │
│  │                    Enforcement Points                        │   │
│  │  ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌─────────┐ ┌───────┐ │   │
│  │  │ MENARA  │ │ GAPURA  │ │  ZIRAH  │ │ BENTENG │ │ SANDI │ │   │
│  │  └─────────┘ └─────────┘ └─────────┘ └─────────┘ └───────┘ │   │
│  └─────────────────────────────────────────────────────────────┘   │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

### 1.2 TERAS Policy DSL

```
// TERAS Policy Language Example

namespace teras.security {
    
    // Import product schemas
    import menara.MobileDevice;
    import gapura.HttpRequest;
    import benteng.Identity;
    import sandi.SigningRequest;
    
    // Define security clearance levels
    enum Clearance {
        Public,
        Internal,
        Confidential,
        Secret,
        TopSecret
    }
    
    // Define policy for GAPURA WAF
    policy GapuraAccessControl {
        
        // Block requests from known bad IPs
        forbid request: HttpRequest
        when request.source_ip in ThreatIntel.blocked_ips {
            audit("Blocked request from threat IP", request);
        }
        
        // Rate limiting
        forbid request: HttpRequest
        when request.client.request_count > 100 
             in last(minutes(1)) {
            audit("Rate limit exceeded", request);
            response = RateLimitExceeded;
        }
        
        // Require authentication for sensitive endpoints
        forbid request: HttpRequest
        when request.path matches "/api/admin/**"
             and not request.authenticated {
            response = Unauthorized;
        }
        
        // Permit authenticated requests
        permit request: HttpRequest
        when request.authenticated
             and request.user.clearance >= request.resource.required_clearance;
    }
    
    // Policy for BENTENG eKYC
    policy BentengIdentityVerification {
        
        // Require multi-factor for high-risk operations
        forbid action: IdentityAction
        when action.risk_score > 0.7
             and not action.mfa_verified {
            require MfaChallenge;
        }
        
        // Geographic restrictions
        forbid action: IdentityAction
        when action.source_country in SanctionedCountries;
        
        // Permit verified actions
        permit action: IdentityAction
        when action.identity.verified
             and action.identity.not_expired
             and action.identity.trust_score >= action.required_trust;
    }
    
    // Cross-product policy
    policy TERASDataClassification {
        
        // IFC labels flow through all products
        label sensitive_data = Confidential + compartment(PII);
        
        // Prevent PII leakage
        forbid data_flow(source, dest)
        when source.label >= sensitive_data
             and dest.clearance < Confidential;
        
        // Audit all access to classified data
        on access(user, resource)
        when resource.classification >= Confidential {
            audit("Classified access", user, resource);
        }
    }
}
```

### 1.3 Product-Specific Integration

```
Product Policy Integration:

MENARA (Mobile):
├── Device trust policies
├── App permission policies
├── Network security policies
└── Offline access policies

GAPURA (WAF):
├── Request filtering policies
├── Rate limiting policies
├── Bot detection policies
└── API authorization policies

ZIRAH (EDR):
├── Process execution policies
├── File access policies
├── Network connection policies
└── Incident response policies

BENTENG (eKYC):
├── Identity verification policies
├── Document validation policies
├── Risk assessment policies
└── Compliance policies

SANDI (Signatures):
├── Signing authorization policies
├── Key usage policies
├── Timestamping policies
└── Audit policies
```

## 2. Policy Lifecycle Management

### 2.1 Policy Operations

```
┌─────────────────────────────────────────────────────────────────────┐
│                    Policy Lifecycle                                  │
├─────────────────────────────────────────────────────────────────────┤
│                                                                     │
│  1. AUTHOR                                                          │
│     ├── Write policy in TERAS DSL                                  │
│     ├── Use policy templates                                       │
│     └── IDE support with validation                                │
│                                                                     │
│  2. VALIDATE                                                        │
│     ├── Syntax checking                                            │
│     ├── Type checking against schema                               │
│     ├── Formal property verification                               │
│     └── Policy simulation/testing                                  │
│                                                                     │
│  3. REVIEW                                                          │
│     ├── Security team review                                       │
│     ├── Change impact analysis                                     │
│     └── Compliance verification                                    │
│                                                                     │
│  4. DEPLOY                                                          │
│     ├── Staged rollout (canary)                                    │
│     ├── A/B testing                                                │
│     └── Rollback capability                                        │
│                                                                     │
│  5. MONITOR                                                         │
│     ├── Decision logging                                           │
│     ├── Performance metrics                                        │
│     ├── Anomaly detection                                          │
│     └── Compliance reporting                                       │
│                                                                     │
│  6. ITERATE                                                         │
│     ├── Learn from decisions                                       │
│     ├── Refine policies                                            │
│     └── Version management                                         │
│                                                                     │
└─────────────────────────────────────────────────────────────────────┘
```

## TERAS Decision H-10

**FOR TERAS:**
1. Develop TERAS Policy DSL
2. Implement unified policy runtime
3. Product-specific policy schemas
4. Full lifecycle management tooling
5. Integration with TERAS audit system

### Architecture Decision ID: `TERAS-ARCH-H10-INTEGRATE-001`

---

# Domain H Summary: Policy Languages

| Session | Topic | Decision ID |
|---------|-------|-------------|
| H-01 | Access Control Models | TERAS-ARCH-H01-MODELS-001 |
| H-02 | XACML | TERAS-ARCH-H02-XACML-001 |
| H-03 | SELinux/MAC | TERAS-ARCH-H03-MAC-001 |
| H-04 | OPA/Rego | TERAS-ARCH-H04-OPA-001 |
| H-05 | Cedar | TERAS-ARCH-H05-CEDAR-001 |
| H-06 | Zanzibar/ReBAC | TERAS-ARCH-H06-REBAC-001 |
| H-07 | Formal Analysis | TERAS-ARCH-H07-ANALYSIS-001 |
| H-08 | IFC Policies | TERAS-ARCH-H08-IFC-001 |
| H-09 | Domain-Specific | TERAS-ARCH-H09-DOMAIN-001 |
| H-10 | Integration | TERAS-ARCH-H10-INTEGRATE-001 |

## Key Principles

1. **Policy as Code**: Version, test, deploy policies like software
2. **Defense in Depth**: Multiple policy layers (OS + App + Network)
3. **Formal Verification**: Prove policy properties mathematically
4. **Unified Framework**: Common policy language across TERAS products
5. **Continuous Monitoring**: Audit and learn from policy decisions

## DOMAIN H: COMPLETE

---

*Research Track Output — Domain H: Policy Languages*
*Mode: ULTRA KIASU | EXHAUSTIVE | COMPLETE*

---

**SHA-256**: To be computed
