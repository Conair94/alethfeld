# Getting Started & Usage

## Prerequisites

1.  **OS**: Linux or macOS recommended.
2.  **Lean 4**: Install via [elan](https://github.com/leanprover/elan).
    ```bash
    curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
    ```
3.  **Claude CLI / LLM Context**: Currently, Alethfeld is designed as a prompt-driven system. You need a way to feed the `orchestrator-prompt-v4.md` and the project context to an LLM (like Claude 3.5 Sonnet or Opus).
    *   *Note: In the future, this will be a standalone Python/CLI tool.*

## Setup

1.  Clone the repository:
    ```bash
    git clone https://github.com/tobiasosborne/alethfeld.git
    cd alethfeld
    ```
2.  Initialize the Lean project (if not already done):
    ```bash
    cd lean
    lake build
    ```

## Running a Proof Session

### Manual / Interactive Mode (Current)

The current workflow relies on an interactive session with an LLM.

1.  **Prepare the Context**: Concatenate the orchestrator prompt and your target theorem.
2.  **Start the Session**:
    *   Load `orchestrator-prompt-v4.md`.
    *   Tell the model: "Initialize the graph for the following theorem: [Your Theorem Here]".
3.  **Iterate**:
    *   The model (acting as Orchestrator) will produce output describing the graph updates.
    *   It may ask for user input or simply proceed through the phases.
    *   **Tip**: Use the `save_memory` or file writing tools if you are running this in an agentic environment (like the Gemini CLI) to persist the EDN graph to disk.

### Example: Proving a Limit

**User**:
> Prove that the limit of 1/n as n approaches infinity is 0 using the epsilon-N definition.

**Alethfeld**:
1.  **Adviser** suggests using the Archimedean property.
2.  **Prover** sets up the structure: "For all $\epsilon > 0$, there exists $N \in \mathbb{N}$..."
3.  **Verifier** checks each logical step.
4.  **Output**: A semantic graph in EDN and a generated Lean file.

## Directory Structure

A typical project structure looks like this:

```text
.
├── lean/                   # The formal Verification target
│   ├── lakefile.toml
│   └── AlethfeldLean/      # Source files
├── examples/               # Completed proofs
│   └── my-proof/
│       ├── proof.edn       # The semantic graph (Source of Truth)
│       ├── proof.tex       # Readable LaTeX version
│       └── proof.lean      # Generated Lean skeleton
└── docs/                   # This documentation
```
