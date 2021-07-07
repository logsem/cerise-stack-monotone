This directory contains the Coq mechanization accompanying the submission
"Le Temps des Cerises: Bringing Temporal Stack Safety to Capability Machines".

# Building the proofs

## Installing the dependencies

You need to have [opam](https://opam.ocaml.org/) >= 2.0 installed.

The development is known to compile with Coq 8.12.0 and Iris 3.3.0. To install
those, two options:

- **Option 1**: create a fresh *local* opam switch with everything needed:

```
   opam switch create -y --deps-only --repositories=default,coq-released=https://coq.inria.fr/opam/released .
   eval $(opam env)
```

- **Option 2 (manual installation)**: if you already have an opam switch with
  ocaml >= 4.02.3 and < 4.10:

```
    # Add the coq-released repo (skip if you already have it)
    opam repo add coq-released https://coq.inria.fr/opam/released
    # Install Coq 8.12.0 (skip if already installed)
    opam install coq.8.12.0
    opam update
    opam install coq-iris.3.3.0
```

### Troubleshooting

For Option 1, if the invocation fails at some point, either remove the `_opam`
directory and re-run the command (this will redo everything), or do `eval $(opam
env)` and then `opam install -y --deps-only .` (this will continue from where it
failed).

## Building

```
make -jN  # replace N with the number of CPU cores of your machine
```

We recommend that you have **32Gb of RAM+swap**. Please be aware that the
development takes around XXh to compile. In particular, the files
`theories/examples/awkward_example_u.v` and `theories/examples/stack_object.v` 
can each take up to 25 minutes to compile.

It is possible to run `make fundamental` to only build files up to the
Fundamental Theorem (and `make fundamental-binary` to build up until the binary FTLR). 
This usually takes up 20 minutes.

# Documentation

After building the development, documentation generated using Coqdoc can be
created using `make html`. 

Then, browse the `html/toc.html` file.

Note that we have included a copy of the generated html files as a supplemental material. 

# Organization

The organization of the `theories/` folder is as follows.

## Operational semantics

- `addr_reg.v`: Defines registers and the set of (finite) memory addresses.

- `machine_base.v`: Contains the syntax (permissions, capability, instructions,
  ...) of the capability machine.

- `machine_parameters.v`: Defines a number of "settings" for the machine, that
  parameterize the whole development (e.g. the specific encoding scheme for
  instructions, etc.).

- `cap_lang.v`: Defines the operational semantics of the machine, and the
  embedding of the capability machine language into Iris.

## Program logic (Unary)

- `region.v`: Auxiliary definitions to reason about consecutive range of
  addresses and memory words.

- `rules_base.v`: Contains some of the core resource algebras for the program
  logic, namely the definition for points to predicates with permissions.

- `rules.v`: Imports all the Hoare triple rules for each instruction. These
  rules are separated into separate files (located in the `rules/` folder).

## Logical relation (Unary)

- `multiple_updates.v`: Auxiliary definitions to reason about multiple updates
  to a world.

- `region_invariants_transitions.v`: 

- `region_invariants.v`: Definitions for standard resources, and the shared
  resources map *sharedResources*. Contains some lemmas for "opening" and
  "closing" the map, akin to opening and closing invariants.

- `region_invariants_revocation.v`: Lemmas for revoking standard resources
  (setting *Temporary* invariants to a *Revoked* state).

- `region_invariants_static.v`: Lemmas for manipulating frozen standard
  resources.

- `region_invariants_batch_uninitialized.v`: Lemmas for manipulating uninitialized standard
  resources.

- `region_invariants_allocation.v`:  

- `sts.v`: The definition of *stsCollection*, and associated lemmas.

- `logrel.v`: The definition of the logical relation.

- `monotone.v`: Proof of the monotonicity of the value relation with regards to
  public future worlds, and private future worlds for non local words.

- `fundamental.v`: Contains *Theorem 6.1: fundamental theorem of logical
  relations*. Each case (one for each instruction) is proved in a separate file
  (located in the `ftlr/` folder), which are all imported and applied in this
  file.

## Binary Model

## Case studies: Integrity

In the `examples` folder:

- `macros/*` : Specifications for some useful macros

- `macros/scall_u.v`: Specification of a safe calling convention for
  a URWLX Monotone stack. The specification is split up into two parts:
  the prologue is the specification for the code before the jump, the epilogue
  is the specification for the activation record.

- `macros/malloc.v`: A simple malloc implementation, and its specification.

- `downwards_lse{_preamble}{_adequacty}.v`:

- `stack_object{_preamble}{_adequacty}.v`:

- `awkward_example{_u}{_preamble}{_adequacty}.v`:

## Case studies: Confidentiality

In the `binary_model/examples_binary` folder:

- `macros_binary` : Exports all macro specifications for the "spec" side of the
  binary logical relation

- `confidentiality{_adequacy}{_adequacy_theorem}.v`: 

## Overlay semantics

## Full abstraction

# Differences with the paper

Some definitions have different names from the paper.

*name in paper => name in mechanization*

In the operational semantics:

| *name in paper*   | *name in mechanization*   |
|-------------------|---------------------------|
| SingleStep        | Instr Executable          |
| Done Standby      | Instr NextI               |
| Done Halted       | Instr Halted              |
| Done Failed       | Instr Failed              |
| Repeat _          | Seq _                     |

In the model:

| *name in paper* | *name in mechanization* |
|-----------------|-------------------------|
| Frozen          | Monostatic              |
| stsCollection   | full_sts_world          |
| sharedResources | region                  |
| Temporary       | Monotemporary           |

In `scall_u.v` : the scall macro is slightly unfolded, as it does not include the part of the calling convention which stores local state on the stack. That part is inlined into the examples. 