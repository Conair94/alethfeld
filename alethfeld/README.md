# Alethfeld CLI

A Clojure CLI tool for semantic proof graph operations.

## Quick Start

```bash
# Run with Clojure
clojure -M:run <command> [options]

# Show help
clojure -M:run --help
```

## Commands

| Command | Description |
|---------|-------------|
| `init` | Initialize a new semantic proof graph |
| `validate` | Validate graph against schema |
| `add-node` | Add a node to the graph |
| `update-status` | Update node verification status |
| `replace-node` | Replace a rejected node |
| `delete-node` | Archive a leaf node |
| `extract-lemma` | Extract subgraph as independent lemma |
| `external-ref` | Manage external references |
| `stats` | Display graph statistics |
| `recompute` | Recalculate taint propagation |
| `convert` | Convert legacy format to v4 schema |

## Common Workflows

### Initialize a proof

```bash
clojure -M:run init "For all continuous f,g: (g \\circ f) is continuous" \
  --mode strict-mathematics \
  --output proof.edn
```

### Add nodes

```bash
# From file
clojure -M:run add-node proof.edn node.edn

# From stdin
echo '{:id :1-abc :type :claim :statement "..." ...}' | \
  clojure -M:run add-node --stdin proof.edn
```

### Verification loop

```bash
# Verify a step
clojure -M:run update-status proof.edn :1-abc123 verified

# Reject a step
clojure -M:run update-status proof.edn :1-abc123 rejected

# Replace rejected with revision
clojure -M:run replace-node proof.edn :1-abc123 revised.edn
```

### Extract lemmas

```bash
clojure -M:run extract-lemma proof.edn \
  --name "Intermediate Value Theorem" \
  --root :2-ivt456 \
  --nodes :2-ivt456,:3-sub1,:3-sub2
```

### Validate

```bash
clojure -M:run validate proof.edn -v
```

## Development

### Run tests

```bash
clojure -M:test
```

### Build uberjar

```bash
clojure -T:build uber
java -jar target/alethfeld.jar --help
```

## Project Structure

```
alethfeld/
├── src/alethfeld/
│   ├── core.clj           # CLI entry point
│   ├── schema.clj         # Malli schemas
│   ├── validators.clj     # Validation logic
│   ├── graph.clj          # Graph query functions
│   ├── io.clj             # EDN I/O
│   ├── config.clj         # Constants
│   ├── ops/               # Graph operations
│   │   ├── add_node.clj
│   │   ├── update_status.clj
│   │   ├── delete_node.clj
│   │   ├── replace_node.clj
│   │   ├── extract_lemma.clj
│   │   ├── external_ref.clj
│   │   └── init.clj
│   └── commands/          # CLI commands
│       ├── validate.clj
│       ├── add_node.clj
│       ├── update_status.clj
│       └── ...
├── test/alethfeld/
│   ├── ops/               # Operation unit tests
│   └── integration/       # Integration tests
└── deps.edn
```

## Graph Schema

See [docs/proof-format.md](../docs/proof-format.md) for the full EDN schema.

Key concepts:
- **Nodes**: Claims, assumptions, definitions, lemma-refs
- **Dependencies**: DAG of what each node uses
- **Scope**: Active local assumptions
- **Taint**: Propagates from admitted steps
- **Status**: proposed, verified, admitted, rejected

## Full Documentation

- [CLI Reference](../docs/cli-reference.md) - Complete command documentation
- [Architecture](../docs/architecture.md) - System design
- [Proof Format](../docs/proof-format.md) - EDN schema details
